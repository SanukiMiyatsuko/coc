import { type Name, type Sort } from "./pdef";

export type Term =
  | { tag: "Sort"; name: Sort }
  | { tag: "Var"; name: Name }
  | { tag: "Lam"; name: Name; type: Term; body: Term }
  | { tag: "Pi"; name: Name; type: Term; body: Term }
  | { tag: "Pair"; fst: Term; snd: Term; as?: Term }
  | { tag: "Fst"; pair: Term }
  | { tag: "Snd"; pair: Term }
  | { tag: "Sig"; name: Name; type: Term; body: Term }
  | { tag: "Let"; name: Name; type?: Term; def: Term; body: Term }
  | { tag: "App"; fun: Term; arg: Term };

export const sort = (name: Sort): Term => ({ tag: "Sort", name });
export const varia = (name: Name): Term => ({ tag: "Var", name });
export const lam = (name: Name, type: Term, body: Term): Term => ({ tag: "Lam", name, type, body });
export const pi = (name: Name, type: Term, body: Term): Term => ({ tag: "Pi", name, type, body });
export const pair = (fst: Term, snd: Term, as?: Term): Term => ({ tag: "Pair", fst, snd, as });
export const fst = (pair: Term): Term => ({ tag: "Fst", pair });
export const snd = (pair: Term): Term => ({ tag: "Snd", pair });
export const sig = (name: Name, type: Term, body: Term): Term => ({ tag: "Sig", name, type, body });
export const letIn = (name: Name, type: Term | undefined, def: Term, body: Term): Term => ({ tag: "Let", name, type, def, body });
export const app = (fun: Term, arg: Term): Term => ({ tag: "App", fun, arg });

export type CtxElement =
  | { tag: "Var"; name: Name; type: Term }
  | { tag: "Def"; name: Name; type: Term; def: Term };

export type Context = CtxElement[];

export const ctxElem = (name: Name, type: Term, def?: Term): CtxElement =>
  def ? { tag: "Def", name, type, def } : { tag: "Var", name, type };

export type JudgContext = { global: Context; local: Context };

export const judgCtx = (global: Context, local: Context): JudgContext => ({ global, local });

export type Judgment =
  | { tag: "nomal"; context: JudgContext; term: Term; type: Term }
  | { tag: "WF"; context: JudgContext };