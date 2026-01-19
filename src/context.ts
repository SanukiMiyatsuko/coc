import { type Name } from "./ast";
import { type Result, succ, err, isErr } from "./result";
import { type CtxElement, type JudgContext } from "./core";
import { freeVar } from "./definition";

type DepKind = "type" | "def";

type CtxError =
  | { tag: "DuplicateGlobal"; name: Name }
  | { tag: "DuplicateLocal"; name: Name }
  | { tag: "SelfReference"; name: Name; kind: DepKind }
  | { tag: "GlobalDependsOnLocal"; from: Name; to: Name; kind: DepKind }
  | { tag: "ForwardDependency"; from: Name; to: Name; kind: DepKind }
  | { tag: "Undefined"; name: Name; in: Name; kind: DepKind }
  | { tag: "Cycle"; path: { from: Name; to: Name; kind: DepKind }[] };

type Dependency = { to: Name; kind: DepKind };

type DefInfo = { isGlobal: boolean; index: number };
type MapDefInfo = Map<Name, DefInfo>;

type DepGraph = Map<Name, Dependency[]>;

function depsOf(e: CtxElement): Dependency[] {
  const deps: Dependency[] = [];
  for (const v of freeVar(e.type)) {
    deps.push({ to: v, kind: "type" });
  }
  if (e.tag === "Def")
    for (const v of freeVar(e.def)) {
      deps.push({ to: v, kind: "def" });
    }
  return deps;
}

function buildDefInfo(ctx: JudgContext): Result<MapDefInfo, CtxError> {
  const info: MapDefInfo = new Map();
  let index = 0;
  for (const e of ctx.global) {
    if (info.has(e.name))
      return err({ tag: "DuplicateGlobal", name: e.name });
    info.set(e.name, { isGlobal: true, index: index++ });
  }
  for (const e of ctx.local) {
    const prev = info.get(e.name);
    if (prev && !prev.isGlobal)
      return err({ tag: "DuplicateLocal", name: e.name });
    info.set(e.name, { isGlobal: false, index: index++ });
  }
  return succ(info);
}

function checkDepPolicy(
  from: Name,
  dep: Dependency,
  info: MapDefInfo
): Result<null, CtxError> {
  if (dep.to === from)
    return err({ tag: "SelfReference", name: from, kind: dep.kind });
  const f = info.get(from)!;
  const t = info.get(dep.to)!;
  if (f.isGlobal && !t.isGlobal)
    return err({
      tag: "GlobalDependsOnLocal",
      from,
      to: dep.to,
      kind: dep.kind,
    });
  if (t.index >= f.index)
    return err({
      tag: "ForwardDependency",
      from,
      to: dep.to,
      kind: dep.kind,
    });
  return succ(null);
}

function buildDepGraph(
  ctx: JudgContext,
  info: MapDefInfo
): Result<DepGraph, CtxError> {
  const graph: DepGraph = new Map();
  const all = [...ctx.global, ...ctx.local];
  for (const e of all)
    graph.set(e.name, []);
  for (const e of all) {
    for (const dep of depsOf(e)) {
      if (!info.has(dep.to))
        return err({
          tag: "Undefined",
          name: dep.to,
          in: e.name,
          kind: dep.kind,
        });
      const r = checkDepPolicy(e.name, dep, info);
      if (isErr(r))
        return r;
      graph.get(e.name)!.push(dep);
    }
  }
  return succ(graph);
}

function checkAcyclic(graph: DepGraph): Result<null, CtxError> {
  const visited = new Set<Name>();
  const visiting = new Set<Name>();
  const stack: { from: Name; to: Name; kind: DepKind }[] = [];
  function dfs(n: Name): Result<null, CtxError> {
    if (visiting.has(n)) {
      const i = stack.findIndex(e => e.from === n);
      return err({
        tag: "Cycle",
        path: stack.slice(i),
      });
    }
    if (visited.has(n))
      return succ(null);
    visiting.add(n);
    for (const dep of graph.get(n)!) {
      stack.push({ from: n, to: dep.to, kind: dep.kind });
      const r = dfs(dep.to);
      if (isErr(r))
        return r;
      stack.pop();
    }
    visiting.delete(n);
    visited.add(n);
    return succ(null);
  }
  for (const n of graph.keys()) {
    const r = dfs(n);
    if (isErr(r))
      return r;
  }
  return succ(null);
}

export function checkJudgContext(ctx: JudgContext): Result<true, CtxError> {
  const infoR = buildDefInfo(ctx);
  if (isErr(infoR))
    return infoR;
  const graphR = buildDepGraph(ctx, infoR.value);
  if (isErr(graphR))
    return graphR;
  const acyclicR = checkAcyclic(graphR.value);
  if (isErr(acyclicR))
    return acyclicR;
  return succ(true);
}