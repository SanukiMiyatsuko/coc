import { type PGlobalContext, type Range, type Name, type Scope, newScope, pVarElem, Pi, Lambda, pDefElem, type PGlobalElement, type PTerm, type Binder, type Place } from "./pdef";
import { type Result, succ, err, isErr } from "./result";

type DepKind = "Type" | "Def";

export type ContextError =
  | { tag: "Undefined"; place: Place; kind: DepKind; name: Name; range: Range }
  | { tag: "Duplicate"; place: Place; name: Name; range: Range };

function lookup(scope: Scope | null, name: Name): boolean {
  let cur = scope;
  while (cur) {
    for (const e of cur.context) {
      if (e.name === name)
        return true;
    }
    cur = cur.parent;
  }
  return false;
}

function checkVariable(
  scope: Scope,
  name: Name,
  range: Range
): Result<true, ContextError> {
  if (!lookup(scope, name)) {
    return err({
      tag: "Undefined",
      place: scope.tag,
      kind: "Type",
      name,
      range,
    });
  }
  return succ(true);
}

function collect(t: PTerm, scope: Scope, dep: number): Result<true, ContextError> {
  switch (t.tag) {
    case "Sort":
      break;
    case "Variable": {
      const r = checkVariable(scope, t.name, t.range);
      if (isErr(r))
        return r;
      break;
    }
    case "Lambda":
    case "Pi":
    case "Sigma": {
      const result = collectBindersThenBody(t.binders, t.body, scope, dep);
      if (isErr(result))
        return result;
      break;
    }
    case "Arrow": {
      const result0 = collect(t.in, scope, dep);
      if (isErr(result0))
        return result0;
      const result1 = collect(t.out, scope, dep);
      if (isErr(result1))
        return result1;
      break;
    }
    case "Pair": {
      const result0 = collect(t.first, scope, dep);
      if (isErr(result0))
        return result0;
      const result1 = collect(t.second, scope, dep);
      if (isErr(result1))
        return result1;
      if (t.type) {
        const result2 = collect(t.type, scope, dep);
        if (isErr(result2))
          return result2;
      }
      break;
    }
    case "First":
    case "Second": {
      const result = collect(t.pair, scope, dep);
      if (isErr(result))
        return result;
      break;
    }
    case "Prod": {
      const result0 = collect(t.first, scope, dep);
      if (isErr(result0))
        return result0;
      const result1 = collect(t.second, scope, dep);
      if (isErr(result1))
        return result1;
      break;
    }
    case "Let": {
      const result = collectLet(t, scope, dep);
      if (isErr(result))
        return result;
      break;
    }
    case "Apply": {
      for (const e of t.apply) {
        const result = collect(e, scope, dep);
        if (isErr(result))
          return result;
      }
      break;
    }
  }
  return succ(true);
}

function checkDuplicate(scope: Scope, name: Name, range: Range): Result<true, ContextError> {
  if (scope.context.some(e => e.name === name))
    return err({
      tag: "Duplicate",
      place: scope.tag,
      name,
      range,
    });
  let cur = scope.parent;
  while (cur) {
    if (cur.context.some(e => e.name === name))
      return err({
        tag: "Duplicate",
        place: scope.tag,
        name,
        range,
      });
    cur = cur.parent;
  }
  return succ(true);
}

function collectBindersThenBody( binders: Binder[], body: PTerm, parent: Scope, dep: number): Result<true, ContextError> {
  const end = body.range.end;
  let currentScope = parent;
  let depth = dep;
  for (const b of binders) {
    if (b.tag === "Var") {
      const result = collect(b.type, currentScope, depth);
      if (isErr(result))
        return result;
    } else {
      if (b.type) {
        const result = collect(b.type, currentScope, depth);
        if (isErr(result))
          return result;
      }
      const result = collect(b.def, currentScope, depth);
      if (isErr(result))
        return result;
    }
    depth += 1;
    const nextScope = newScope("Local", currentScope, b.range.start, end, depth);
    currentScope.children.push(nextScope);
    if (b.tag === "Var")
      for (const n of b.names) {
        const dup = checkDuplicate(nextScope, n, b.range);
        if (isErr(dup))
          return dup;
        nextScope.context.push(
          pVarElem(n, b.type, b.range)
        );
      }
    else {
      const dup = checkDuplicate(nextScope, b.name, b.range);
      if (isErr(dup))
        return dup;
      nextScope.context.push(
        pDefElem(
          b.name,
          b.type ? b.type : undefined,
          b.def,
          b.range
        )
      );
    }
    currentScope = nextScope;
  }
  const result = collect(body, currentScope, depth);
  if (isErr(result))
    return result;
  return succ(true);
}

function collectLet(t: PTerm & { tag: "Let" }, parent: Scope, dep: number): Result<true, ContextError> {
  const end = t.body.range.end;
  let currentScope = parent;
  const scopes: Scope[] = [];
  let depth = dep;
  for (const b of t.binders) {
    if (b.tag === "Var") {
      const result = collect(b.type, currentScope, depth);
      if (isErr(result))
        return result;
    } else {
      if (b.type) {
        const result = collect(b.type, currentScope, depth);
        if (isErr(result))
          return result;
      }
      const result = collect(b.def, currentScope, depth);
      if (isErr(result))
        return result;
    }
    depth += 1;
    const nextScope = newScope("Local", currentScope, b.range.start, end, depth);
    currentScope.children.push(nextScope);
    scopes.push(nextScope);
    if (b.tag === "Var") {
      for (const n of b.names) {
        const dup = checkDuplicate(nextScope, n, b.range);
        if (isErr(dup))
          return dup;
        nextScope.context.push(
          pVarElem(n, b.type, b.range)
        );
      }
    } else {
      const dup = checkDuplicate(nextScope, b.name, b.range);
      if (isErr(dup))
        return dup;
      nextScope.context.push(
        pDefElem(
          b.name,
          b.type ? b.type : undefined,
          b.def,
          b.range
        )
      );
    }
    currentScope = nextScope;
  }
  if (t.type) {
    const result = collect(t.type, currentScope, depth);
    if (isErr(result))
      return result;
  }
  const result0 = collect(t.def, currentScope, depth);
  if (isErr(result0))
    return result0;
  depth += 1;
  const letScope = newScope("Local", currentScope, t.range.start, end, depth);
  currentScope.children.push(letScope);
  const dup = checkDuplicate(letScope, t.name, t.range);
  if (isErr(dup))
    return dup;
  letScope.context.push(
    pDefElem(
      t.name,
      t.type
        ? t.binders.length === 0
          ? t.type
          : Pi(t.binders, t.type, t.range)
        : undefined,
      t.binders.length === 0
        ? t.def
        : Lambda(t.binders, t.def, t.range),
      t.range
    )
  );
  const result1 = collect(t.body, letScope, depth);
  if (isErr(result1))
    return result1;
  return succ(true);
}

function collectGlobalElement(global: PGlobalElement, parent: Scope, dep: number): Result<true, ContextError> {
  const end = global.range.end;
  let currentScope = parent;
  const scopes: Scope[] = [];
  let depth = dep;
  for (const b of global.binders) {
    if (b.tag === "Var") {
      const result = collect(b.type, currentScope, depth);
      if (isErr(result))
        return result;
    } else {
      if (b.type) {
        const result = collect(b.type, currentScope, depth);
        if (isErr(result))
          return result;
      }
      const result = collect(b.def, currentScope, depth);
      if (isErr(result))
        return result;
    }
    depth += 1;
    const nextScope = newScope("Local", currentScope, b.range.start, end, depth);
    currentScope.children.push(nextScope);
    scopes.push(nextScope);
    if (b.tag === "Var")
      for (const n of b.names) {
        const dup = checkDuplicate(nextScope, n, b.range);
        if (isErr(dup))
          return dup;
        nextScope.context.push(
          pVarElem(n, b.type, b.range)
        );
      }
    else {
      const dup = checkDuplicate(nextScope, b.name, b.range);
      if (isErr(dup))
        return dup;
      nextScope.context.push(
        pDefElem(
          b.name,
          b.type ? b.type : undefined,
          b.def,
          b.range
        )
      );
    }
    currentScope = nextScope;
  }
  const result = collect(global.type, currentScope, depth);
  if (isErr(result))
    return result;
  if (global.tag === "Def") {
    const result0 = collect(global.def, currentScope, depth);
    if (isErr(result0))
      return result0;
  }
  return succ(true);
}

export function buildGlobalScope(globals: PGlobalContext): Result<Scope, ContextError> {
  const end = {
    line: Number.MAX_SAFE_INTEGER,
    character: Number.MAX_SAFE_INTEGER,
  };
  let depth = 0;
  const root = newScope("Global", null, { line: 0, character: 0 }, end, 0);
  let currentScope = root;
  for (const global of globals) {
    const result = collectGlobalElement(global, currentScope, depth);
    if (isErr(result))
      return result;
    depth += 1;
    const nextScope = newScope("Global", currentScope, global.range.start, end, depth);
    currentScope.children.push(nextScope);
    const dup = checkDuplicate(nextScope, global.name, global.range);
    if (isErr(dup))
      return dup;
    const type =
      global.binders.length === 0
        ? global.type
        : Pi(global.binders, global.type, global.range);
    if (global.tag === "Var") {
      nextScope.context.push(
        pVarElem(
          global.name,
          type,
          global.range
        )
      );
    } else {
      const def =
        global.binders.length === 0
          ? global.def
          : Lambda(global.binders, global.def, global.range);
      nextScope.context.push(
        pDefElem(
          global.name,
          type,
          def,
          global.range
        )
      );
    }
    currentScope = nextScope;
  }
  return succ(root);
}