export type Sort = "Prop" | "Type";
export type Name = string;
export type Term = { tag: "Sort"; name: Sort }
  | { tag: "Var"; name: Name }
  | { tag: "Lam"; name: Name; type: Term; body: Term }
  | { tag: "Pi"; name: Name; type: Term; body: Term }
  | { tag: "Let"; name: Name; type: Term; def: Term; body: Term  }
  | { tag: "App"; fun: Term; arg: Term };

export const sort = (name: Sort): Term => ({ tag: "Sort", name });
export const varia = (name: Name): Term => ({ tag: "Var", name });
export const lam = (name: Name, type: Term, body: Term): Term => ({ tag: "Lam", name, type, body });
export const pi = (name: Name, type: Term, body: Term): Term => ({ tag: "Pi", name, type, body });
export const letIn = (name: Name, type: Term, def: Term, body: Term): Term => ({ tag: "Let", name, type, def, body });
export const app = (fun: Term, arg: Term): Term => ({ tag: "App", fun, arg });