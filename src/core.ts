import { type Name, type Term } from "./ast";

type CtxVariable = { tag: "Var"; name: Name; type: Term };
type CtxDefinition = { tag: "Def"; name: Name; type: Term; def: Term };
export type CtxElement = CtxVariable | CtxDefinition;

export type Context = CtxElement[];

export const ctxVar = (name: Name, type: Term): CtxVariable => ({ tag: "Var", name, type });
export const ctxDef = (name: Name, type: Term, def: Term): CtxDefinition => ({ tag: "Def", name, type, def });

export type JudgContext = { global: Context; local: Context };

export const judgCtx = (global: Context, local: Context): JudgContext => ({ global, local });

export type Judgment = { tag: "nomal"; context: JudgContext; term: Term; type: Term }
  | { tag: "WF"; context: JudgContext };