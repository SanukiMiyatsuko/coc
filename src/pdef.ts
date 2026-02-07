export type Sort = "Prop" | "Type";
export type Name = string;
export type Position = { line: number; character: number };
export type Range = { start: Position; end: Position };
export type PType = PTerm;
export type Binder =
  | { tag: "Var"; names: Name[], type: PType; range: Range }
  | { tag: "Def"; name: Name; type?: PType; def: PType; range: Range };
export type PTerm =
  | { tag: "Sort"; name: Sort; range: Range }
  | { tag: "Variable"; name: Name; range: Range }
  | { tag: "Lambda"; binders: Binder[]; body: PTerm; range: Range }
  | { tag: "Pi"; binders: Binder[]; body: PType; range: Range }
  | { tag: "Arrow"; in: PType; out: PType; range: Range }
  | { tag: "Pair"; first: PTerm; second: PTerm; type?: PType; range: Range }
  | { tag: "First"; pair: PTerm; range: Range }
  | { tag: "Second"; pair: PTerm; range: Range }
  | { tag: "Sigma"; binders: Binder[]; body: PType; range: Range }
  | { tag: "Prod"; first: PType; second: PType; range: Range }
  | { tag: "Let"; name: Name; binders: Binder[]; type?: PType; def: PTerm; body: PTerm; range: Range }
  | { tag: "Apply"; apply: PTerm[]; range: Range };

export const varBinder = (names: string[], type: PType, range: Range): Binder => ({ tag: "Var", names, type, range });
export const defBinder = (name: string, type: PType | undefined, def: PType, range: Range): Binder => ({ tag: "Def", name, type, def, range });
export const Sort = (name: Sort, range: Range): PTerm => ({ tag: "Sort", name, range });
export const Variable = (name: string, range: Range): PTerm => ({ tag: "Variable", name, range });
export const Lambda = (binders: Binder[], body: PTerm, range: Range): PTerm => ({ tag: "Lambda", binders, body, range });
export const Pi = (binders: Binder[], body: PType, range: Range): PTerm => ({ tag: "Pi", binders, body, range });
export const Arrow = (input: PType, output: PType, range: Range): PTerm => ({ tag: "Arrow", in: input, out: output, range });
export const Pair = (first: PTerm, second: PTerm, type: PType | undefined, range: Range): PTerm => ({ tag: "Pair", first, second, type, range });
export const First = (pair: PTerm, range: Range): PTerm => ({ tag: "First", pair, range });
export const Second = (pair: PTerm, range: Range): PTerm => ({ tag: "Second", pair, range });
export const Sigma = (binders: Binder[], body: PType, range: Range): PTerm => ({ tag: "Sigma", binders, body, range });
export const Prod = (first: PType, second: PType, range: Range): PTerm => ({ tag: "Prod", first, second, range });
export const Let = (name: string, binders: Binder[], type: PType | undefined, def: PTerm, body: PTerm, range: Range): PTerm => ({ tag: "Let", name, binders, type, def, body, range });
export const Apply = (apply: PTerm[], range: Range): PTerm => ({ tag: "Apply", apply, range });

export type PLocalElement =
  | { tag: "Var"; name: Name; type: PTerm; range: Range }
  | { tag: "Def"; name: Name; type?: PTerm; def: PTerm; range: Range };
export type PLocalContext = PLocalElement[];

export const pVarElem = (name: Name, type: PTerm, range: Range): PLocalElement => ({ tag: "Var", name, type, range: range });
export const pDefElem = (name: Name, type: PTerm | undefined, def: PTerm, range: Range): PLocalElement => ({ tag: "Def", name, type, def, range: range });

export type Place = "Global" | "Local";
export type Scope = { tag: Place;  parent: Scope | null; context: PLocalContext; children: Scope[]; range: Range; depth: number };

export const newScope = (tag: Place, parent: Scope | null, start: Position, end: Position, depth: number): Scope =>
  ({ tag, parent, context: [], children: [], range: { start, end }, depth });

export type PGlobalElement =
  | { tag: "Var"; name: Name; binders: Binder[]; type: PTerm; range: Range }
  | { tag: "Def"; name: Name; binders: Binder[]; type: PTerm; def: PTerm; range: Range };

export const pGlobalElem = (name: Name, binders: Binder[], type: PTerm, def: PTerm | undefined, range: Range): PGlobalElement =>
  def ? { tag: "Def", name, binders, type, def, range } : { tag: "Var", name, binders, type, range };

export type PGlobalContext = PGlobalElement[];

export function pFreeVariables(t: PTerm): Set<Name> {
  const env = new Set<Name>();
  const acc = new Set<Name>();
  collect(t, env, acc);
  return acc;
}

function collect(t: PTerm, env: Set<Name>, acc: Set<Name>) {
  switch (t.tag) {
    case "Sort":
      return;
    case "Variable": {
      if (!env.has(t.name))
        acc.add(t.name);
      return;
    }
    case "Lambda":
    case "Pi":
    case "Sigma":
    case "Let":
      break;
    case "Arrow": {
      collect(t.in, env, acc);
      collect(t.out, env, acc);
      return;
    }
    case "Pair": {
      collect(t.first, env, acc);
      collect(t.second, env, acc);
      if (t.type)
        collect(t.type, env, acc);
      return;
    }
    case "First":
    case "Second": {
      collect(t.pair, env, acc);
      return;
    }
    case "Prod": {
      collect(t.first, env, acc);
      collect(t.second, env, acc);
      return;
    }
    case "Apply": {
      t.apply.forEach(e => collect(e, env, acc));
      return;
    }
  }
  for (const m of t.binders) {
    if (m.tag === "Var") {
      collect(m.type, env, acc);
      m.names.forEach(n => env.add(n));
    } else {
      if (m.type)
        collect(m.type, env, acc);
      collect(m.def, env, acc);
      env.add(m.name);
    }
  }
  if (t.tag === "Let") {
    if (t.type)
      collect(t.type, env, acc);
    collect(t.def, env, acc);
    env.add(t.name);
  }
  collect(t.body, env, acc);
  if (t.tag === "Let") env.delete(t.name);
  for (const m of t.binders) {
    if (m.tag === "Var")
      m.names.forEach(n => env.delete(n));
    else {
      env.delete(m.name);
    }
  }
  return;
}