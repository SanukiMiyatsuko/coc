import type { Name, Sort } from "./pdef";

export type Term =
  | { tag: "Sort"; name: Sort }
  | { tag: "Free"; name: Name }
  | { tag: "Bind"; index: number }
  | { tag: "Lam"; type: Term; body: Term }
  | { tag: "Pi"; type: Term; body: Term }
  | { tag: "Pair"; fst: Term; snd: Term; as?: Term }
  | { tag: "Fst"; pair: Term }
  | { tag: "Snd"; pair: Term }
  | { tag: "Sig"; type: Term; body: Term }
  | { tag: "Let"; type?: Term; def: Term; body: Term }
  | { tag: "App"; fun: Term; arg: Term };

export const sort = (name: Sort): Term => ({ tag: "Sort", name });
export const free = (name: Name): Term => ({ tag: "Free", name });
export const bind = (index: number): Term => ({ tag: "Bind", index });
export const lam = (type: Term, body: Term): Term => ({ tag: "Lam", type, body });
export const pi = (type: Term, body: Term): Term => ({ tag: "Pi", type, body });
export const pair = (fst: Term, snd: Term, as?: Term): Term => ({ tag: "Pair", fst, snd, as });
export const fst = (pair: Term): Term => ({ tag: "Fst", pair });
export const snd = (pair: Term): Term => ({ tag: "Snd", pair });
export const sig = (type: Term, body: Term): Term => ({ tag: "Sig", type, body });
export const letIn = (type: Term | undefined, def: Term, body: Term): Term => ({ tag: "Let", type, def, body });
export const app = (fun: Term, arg: Term): Term => ({ tag: "App", fun, arg });

export type GlobalElement =
  | { tag: "Var"; name: Name; type: Term }
  | { tag: "Def"; name: Name; type: Term; def: Term };

export type GlobalContext = GlobalElement[];

export const globalElem = (name: Name, type: Term, def?: Term): GlobalElement =>
  def ? { tag: "Def", name, type, def } : { tag: "Var", name, type };

export type LocalElement =
  | { tag: "Var"; type: Term }
  | { tag: "Def"; type: Term; def: Term };

export type LocalContext = LocalElement[];

export const localElem = (type: Term, def?: Term): LocalElement =>
  def ? { tag: "Def", type, def } : { tag: "Var", type };

export type JudgContext = { global: GlobalContext; local: LocalContext };

export const judgCtx = (global: GlobalContext, local: LocalContext): JudgContext => ({ global, local });