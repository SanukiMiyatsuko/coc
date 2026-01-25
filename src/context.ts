import { pFreeVariables, type PLocalElement, type PGlobalContext, type Range, type Name, type PGlobal } from "./pdef";
import { type Result, succ, err, isErr } from "./result";

type DepKind = "type" | "def";

export type CtxError =
  | { tag: "DuplicateGlobal"; name: Name; range: Range }
  | { tag: "DuplicateLocal"; name: Name; range: Range }
  | { tag: "SelfReference"; name: Name; kind: DepKind; range: Range }
  | { tag: "Undefined"; name: Name; in: Name; kind: DepKind; range: Range }
  | { tag: "Cycle"; path: { from: Name; to: Name; kind: DepKind }[]; range: Range };

type Dependency = { to: Name; kind: DepKind };
type DepGraph = Map<string, Dependency[]>;
type GlobalInfos = Set<Name>;
type RangeMap = Map<string, Range>;

function globalDepsOf(ge: PGlobal): Dependency[] {
  const bound = new Set<Name>();
  for (const e of ge.local) {
    bound.add(e.name);
  };
  const deps: Dependency[] = [];
  for (const v of pFreeVariables(ge.elem.type)) {
    if (!bound.has(v))
      deps.push({ to: v, kind: "type" });
  }
  if (ge.elem.tag === "Def")
    for (const v of pFreeVariables(ge.elem.def)) {
      if (!bound.has(v))
        deps.push({ to: v, kind: "def" });
    }
  return deps;
}

function localDepsOf(e: PLocalElement): Dependency[] {
  const deps: Dependency[] = [];
  if (e.tag === "Var")
    for (const v of pFreeVariables(e.type)) {
      deps.push({ to: v, kind: "type" });
    }
  if (e.tag === "Def") {
    if (e.type)
      for (const v of pFreeVariables(e.type)) {
        deps.push({ to: v, kind: "type" });
      }
    for (const v of pFreeVariables(e.def)) {
      deps.push({ to: v, kind: "def" });
    }
  }
  return deps;
}

function buildDefInfo(ctx: PGlobalContext): Result<GlobalInfos, CtxError> {
  const globals: GlobalInfos = new Set();
  for (const ge of ctx) {
    const elem = ge.elem
    if (globals.has(elem.name))
      return err({ tag: "DuplicateGlobal", name: elem.name, range: elem.range });
    const local: Name[] = [];
    for (const e of ge.local) {
      if (local.find(x => x === e.name))
        return err({ tag: "DuplicateLocal", name: e.name, range: e.range });
      local.push(e.name);
    }
    globals.add(elem.name);
  }
  return succ(globals);
}

function buildDepGraph(ctx: PGlobalContext, info: GlobalInfos): Result<{ graph: DepGraph; rangeMap: RangeMap }, CtxError> {
  const graph: DepGraph = new Map();
  const rangeMap: RangeMap = new Map();
  for (const g of ctx) {
    const gNode = `global:${g.elem.name}`;
    const globalDeps = globalDepsOf(g);
    for (const dep of globalDeps) {
      if (dep.to === g.elem.name)
        return err({
          tag: "SelfReference",
          name: g.elem.name,
          kind: dep.kind,
          range: g.elem.range
        });
      if (!info.has(dep.to))
        return err({
          tag: "Undefined",
          name: dep.to,
          in: g.elem.name,
          kind: dep.kind,
          range: g.elem.range
        });
    }
    graph.set(gNode, globalDeps);
    rangeMap.set(gNode, g.elem.range);
    const seenLocals = new Set<Name>();
    for (const localElem of g.local) {
      const lNode = `local:${g.elem.name}:${localElem.name}`;
      const localDeps = localDepsOf(localElem);
      for (const dep of localDeps) {
        if (dep.to === localElem.name)
          return err({
            tag: "SelfReference",
            name: localElem.name,
            kind: dep.kind,
            range: localElem.range
          });
        const isDefinedLocal = seenLocals.has(dep.to);
        const isDefinedGlobal = info.has(dep.to);
        if (!isDefinedLocal && !isDefinedGlobal)
          return err({
            tag: "Undefined",
            name: dep.to,
            in: localElem.name,
            kind: dep.kind,
            range: localElem.range
          });
      }
      graph.set(lNode, localDeps);
      rangeMap.set(lNode, localElem.range);
      seenLocals.add(localElem.name);
    }
  }
  return succ({ graph, rangeMap });
}

function depToNode(fromNode: string, dep: Dependency): string {
  if (fromNode.startsWith("global:"))
    return `global:${dep.to}`;
  const li = fromNode.split(":");
  return `local:${li[1]}:${dep.to}`;
}

function detectCycle(
  graph: DepGraph,
  ranges: Map<string, Range>
): Result<true, CtxError> {
  const visited = new Set<string>();
  const stack: string[] = [];
  const onStack = new Set<string>();

  function dfs(v: string): Result<true, CtxError> {
    visited.add(v);
    stack.push(v);
    onStack.add(v);

    const deps = graph.get(v) ?? [];
    for (const dep of deps) {
      const to = depToNode(v, dep);
      if (!graph.has(to))
        continue;
      if (!visited.has(to)) {
        const r = dfs(to);
        if (isErr(r))
          return r;
      } else if (onStack.has(to)) {
        const idx = stack.indexOf(to);
        const cyclePath = stack.slice(idx).map((_, i) => ({
          from: stack[idx + i],
          to: stack[idx + i + 1] ?? to,
          kind: dep.kind
        }));
        return err({
          tag: "Cycle",
          path: cyclePath,
          range: ranges.get(to)!
        });
      }
    }
    stack.pop();
    onStack.delete(v);
    return succ(true);
  }
  for (const v of graph.keys()) {
    if (!visited.has(v)) {
      const r = dfs(v);
      if (isErr(r))
        return r;
    }
  }
  return succ(true);
}


export function checkGlobalContext(ctx: PGlobalContext): Result<true, CtxError> {
  const infoR = buildDefInfo(ctx);
  if (isErr(infoR))
    return infoR;
  const graphR = buildDepGraph(ctx, infoR.value);
  if (isErr(graphR))
    return graphR;
  const acyclicR = detectCycle(graphR.value.graph, graphR.value.rangeMap);
  if (isErr(acyclicR))
    return acyclicR;
  return succ(true);
}