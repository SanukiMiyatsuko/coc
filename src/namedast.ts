import type { Name, Range, Sort } from "./pdef";

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

export type GlobalElement =
  | { tag: "Var"; name: Name; type: Term; range: Range }
  | { tag: "Def"; name: Name; type: Term; def: Term; range: Range };

export type GlobalContext = GlobalElement[];

export const globalElem = (name: Name, type: Term, def: Term | undefined, range: Range): GlobalElement =>
  def ? { tag: "Def", name, type, def, range } : { tag: "Var", name, type, range };