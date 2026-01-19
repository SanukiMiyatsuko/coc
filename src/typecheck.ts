import { type Name, type Term, sort, lam, pi, letIn, app } from "./ast";
import { type Result, succ, err, isErr } from "./result";
import { type CtxElement, type Context, ctxVar, ctxDef, type JudgContext, judgCtx } from "./core";
import { subst, alphaEq } from "./definition";

type TypeError =
  | { tag: "TypeHasNoType" }
  | { tag: "UnboundVariable"; name: Name }
  | { tag: "ExpectedSort"; actual: Term }
  | { tag: "ExpectedPi"; fun: Term; actual: Term }
  | { tag: "TypeMismatch"; expected: Term; actual: Term };

type WFError = { error: TypeError; at: CtxElement };

function zdnf(jc: JudgContext, t: Term): Term {
  switch (t.tag) {
    case "Sort":
      return t;
    case "Var": {
      const le = jc.local.slice().reverse().find(e => e.name === t.name);
      if (le && le.tag === "Def")
        return zdnf(jc, le.def);
      const ge = jc.global.slice().reverse().find(e => e.name === t.name);
      if (ge && ge.tag === "Def")
        return zdnf(jc, ge.def);
      return t;
    }
    case "Lam":
      return lam(t.name, zdnf(jc, t.type), zdnf(jc, t.body));
    case "Pi":
      return pi(t.name, zdnf(jc, t.type), zdnf(jc, t.body));
    case "Let":
      return zdnf(jc, subst(t.body, t.name, t.def));
    case "App":
      return app(zdnf(jc, t.fun), zdnf(jc, t.arg));
  }
}

function whnf(t: Term): Term {
  switch (t.tag) {
    case "Sort":
    case "Var":
    case "Lam":
      return t;
    case "Pi":
    return pi(t.name, whnf(t.type), whnf(t.body));
    case "Let":
      return letIn(t.name, whnf(t.type), whnf(t.def), whnf(t.body));
    case "App": {
      const fun = whnf(t.fun);
      if (fun.tag === "Lam")
        return whnf(subst(fun.body, fun.name, t.arg));
      return app(fun, t.arg);
    }
  }
}

function whnfEq(jc: JudgContext, t: Term, u: Term): boolean {
  return alphaEq(whnf(zdnf(jc, t)), whnf(zdnf(jc, u)));
}

export function wellFormed(jc: JudgContext): Result<true, WFError> {
  const g: Context = [];
  const l: Context = [];
  const check = (ctx: JudgContext, e: CtxElement): Result<void, WFError> => {
    if (e.tag === "Var") {
      const r = typeInfer(ctx, e.type);
      if (isErr(r))
        return err({ error: r.err, at: e });
      if (r.value.tag !== "Sort")
        return err({
          error: { tag: "ExpectedSort", actual: r.value },
          at: e,
        });
      return succ(undefined);
    } else {
      const r = typeInfer(ctx, e.def);
      if (isErr(r))
        return err({ error: r.err, at: e });
      if (!whnfEq(ctx, r.value, e.type))
        return err({
          error: {
            tag: "TypeMismatch",
            expected: e.type,
            actual: r.value,
          },
          at: e,
        });
      return succ(undefined);
    }
  };
  for (const e of jc.global) {
    const r = check(judgCtx(g, l), e);
    if (isErr(r))
      return r;
    g.push(e);
  }
  for (const e of jc.local) {
    const r = check(judgCtx(g, l), e);
    if (isErr(r))
      return r;
    l.push(e);
  }
  return succ(true);
}

function typeInfer(jc: JudgContext, t: Term): Result<Term, TypeError> {
  switch (t.tag) {
    case "Sort": {
      if (t.name === "Type")
        return err({ tag: "TypeHasNoType" });
      return succ(sort("Type"));
    }
    case "Var": {
      const le = jc.local.slice().reverse().find(e => e.name === t.name);
      if (le)
        return succ(le.type);
      const ge = jc.global.slice().reverse().find(e => e.name === t.name);
      if (ge)
        return succ(ge.type);
      return err({ tag: "UnboundVariable", name: t.name });
    }
    case "Lam": {
      const local = jc.local.slice();
      local.push(ctxVar(t.name, t.type));
      const bodyType = typeInfer(judgCtx(jc.global, local), t.body);
      if (isErr(bodyType))
        return bodyType;
      const termType = pi(t.name, t.type, bodyType.value);
      const s = typeInfer(jc, termType);
      if (isErr(s))
        return s;
      if (s.value.tag !== "Sort")
        return err({ tag: "ExpectedSort", actual: s.value });
      return succ(termType);
    }
    case "Pi": {
      const s0 = typeInfer(jc, t.type);
      if (isErr(s0))
        return s0;
      if (s0.value.tag !== "Sort")
        return err({ tag: "ExpectedSort", actual: s0.value });
      const local = jc.local.slice();
      local.push(ctxVar(t.name, t.type));
      const s1 = typeInfer(judgCtx(jc.global, local), t.body);
      if (isErr(s1))
        return s1;
      if (s1.value.tag !== "Sort")
        return err({ tag: "ExpectedSort", actual: s1.value });
      return s1;
    }
    case "Let": {
      const paramType = typeInfer(jc, t.def);
      if (isErr(paramType))
        return paramType;
      if (!whnfEq(jc, paramType.value, t.type))
        return err({ tag: "TypeMismatch", expected: t.type, actual: paramType.value });
      const local = jc.local.slice();
      local.push(ctxDef(t.name, t.type, t.def));
      const bodyType = typeInfer(judgCtx(jc.global, local), t.body);
      if (isErr(bodyType))
        return bodyType;
      return succ(subst(bodyType.value, t.name, t.def));
    }
    case "App": {
      const funType = typeInfer(jc, t.fun);
      if (isErr(funType))
        return funType;
      const funTypeWhnf = whnf(zdnf(jc, funType.value));
      if (funTypeWhnf.tag !== "Pi")
        return err({ tag: "ExpectedPi", fun: t.fun, actual: funTypeWhnf });
      const argType = typeInfer(jc, t.arg);
      if (isErr(argType))
        return argType;
      if (!whnfEq(jc, argType.value, funTypeWhnf.type))
        return err({ tag: "TypeMismatch", expected: funTypeWhnf.type, actual: argType.value });
      return succ(subst(funTypeWhnf.body, funTypeWhnf.name, t.arg));
    }
  }
}