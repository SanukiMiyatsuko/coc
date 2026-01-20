import { type Sort, type Name, type Term, sort, lam, pi, pair, fst, snd, sig, letIn, app } from "./ast";
import { type Result, succ, err, isErr } from "./result";
import { type CtxElement, type Context, ctxVar, ctxDef, type JudgContext, judgCtx } from "./core";
import { subst, alphaEq } from "./definition";

type TypeError =
  | { tag: "TypeHasNoType" }
  | { tag: "UnboundVariable"; name: Name }
  | { tag: "ExpectedSort"; actual: Term }
  | { tag: "ImpossibleCombination", sort0: Sort, sort1: Sort }
  | { tag: "ExpectedPi"; fun: Term; actual: Term }
  | { tag: "CannotInfer"; term: Term }
  | { tag: "ExpectedSigma"; pair: Term; actual: Term }
  | { tag: "TypeMismatch"; expected: Term; actual: Term };

type WFError = { error: TypeError; at: CtxElement };

function zdsnf(jc: JudgContext, t: Term): Term {
  switch (t.tag) {
    case "Sort":
      return t;
    case "Var": {
      const le = jc.local.slice().reverse().find(e => e.name === t.name);
      if (le && le.tag === "Def")
        return zdsnf(jc, le.def);
      const ge = jc.global.slice().reverse().find(e => e.name === t.name);
      if (ge && ge.tag === "Def")
        return zdsnf(jc, ge.def);
      return t;
    }
    case "Lam":
      return lam(t.name, zdsnf(jc, t.type), zdsnf(jc, t.body));
    case "Pi":
      return pi(t.name, zdsnf(jc, t.type), zdsnf(jc, t.body));
    case "Pair":
      return pair(zdsnf(jc, t.fst), zdsnf(jc, t.snd));
    case "Fst": {
      if (t.pair.tag === "Pair")
        return zdsnf(jc, t.pair.fst);
      return fst(zdsnf(jc, t.pair));
    }
    case "Snd": {
      if (t.pair.tag === "Pair")
        return zdsnf(jc, t.pair.snd);
      return snd(zdsnf(jc, t.pair));
    }
    case "Sig":
      return sig(t.name, zdsnf(jc, t.type), zdsnf(jc, t.body));
    case "Let":
      return zdsnf(jc, subst(t.body, t.name, t.def));
    case "App":
      return app(zdsnf(jc, t.fun), zdsnf(jc, t.arg));
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
    case "Pair":
      return pair(whnf(t.fst), whnf(t.snd));
    case "Fst":
      return fst(whnf(t.pair));
    case "Snd":
      return snd(whnf(t.pair));
    case "Sig":
      return sig(t.name, whnf(t.type), whnf(t.body));
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
  return alphaEq(whnf(zdsnf(jc, t)), whnf(zdsnf(jc, u)));
}

export function wellFormed(jc: JudgContext): Result<true, WFError> {
  const g: Context = [];
  const l: Context = [];
  const check = (ctx: JudgContext, e: CtxElement): Result<true, WFError> => {
    if (e.tag === "Var") {
      const r = typeInfer(ctx, e.type);
      if (isErr(r))
        return err({ error: r.err, at: e });
      if (r.value.tag !== "Sort")
        return err({
          error: { tag: "ExpectedSort", actual: r.value },
          at: e,
        });
      return succ(true);
    } else {
      const r = typeCheck(ctx, e.def, e.type);
      if (isErr(r))
        return err({ error: r.err, at: e });
      return succ(true);
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
      const sWhnf = whnf(zdsnf(jc, s.value));
      if (sWhnf.tag !== "Sort")
        return err({ tag: "ExpectedSort", actual: sWhnf });
      return succ(termType);
    }
    case "Pi": {
      const s0 = typeInfer(jc, t.type);
      if (isErr(s0))
        return s0;
      const s0Whnf = whnf(zdsnf(jc, s0.value));
      if (s0Whnf.tag !== "Sort")
        return err({ tag: "ExpectedSort", actual: s0Whnf });
      const local = jc.local.slice();
      local.push(ctxVar(t.name, t.type));
      const s1 = typeInfer(judgCtx(jc.global, local), t.body);
      if (isErr(s1))
        return s1;
      const s1Whnf = whnf(zdsnf(jc, s1.value));
      if (s1Whnf.tag !== "Sort")
        return err({ tag: "ExpectedSort", actual: s1Whnf });
      return succ(s1Whnf);
    }
    case "Pair":{
      return err({ tag: "CannotInfer", term: t });
    }
    case "Fst": {
      const pairType = typeInfer(jc, t.pair);
      if (isErr(pairType))
        return pairType;
      const pairTypeWhnf = whnf(zdsnf(jc, pairType.value));
      if (pairTypeWhnf.tag !== "Sig")
        return err({ tag: "ExpectedSigma", pair: t.pair, actual: pairTypeWhnf });
      return succ(pairTypeWhnf.type);
    }
    case "Snd": {
      const pairType = typeInfer(jc, t.pair);
      if (isErr(pairType))
        return pairType;
      const pairTypeWhnf = whnf(zdsnf(jc, pairType.value));
      if (pairTypeWhnf.tag !== "Sig")
        return err({ tag: "ExpectedSigma", pair: t.pair, actual: pairTypeWhnf });
      return succ(subst(pairTypeWhnf.body, pairTypeWhnf.name, fst(t.pair)));
    }
    case "Sig": {
      const s0 = typeInfer(jc, t.type);
      if (isErr(s0))
        return s0;
      const s0Whnf = whnf(zdsnf(jc, s0.value));
      if (s0Whnf.tag !== "Sort")
        return err({ tag: "ExpectedSort", actual: s0Whnf });
      const local = jc.local.slice();
      local.push(ctxVar(t.name, t.type));
      const s1 = typeInfer(judgCtx(jc.global, local), t.body);
      if (isErr(s1))
        return s1;
      const s1Whnf = whnf(zdsnf(jc, s1.value));
      if (s1Whnf.tag !== "Sort")
        return err({ tag: "ExpectedSort", actual: s1Whnf });
      if ((s0Whnf.name === "Prop" && s1Whnf.name === "Prop")
        || s1Whnf.name === "Type")
        return succ(s1Whnf);
      return err({
        tag: "ImpossibleCombination",
        sort0: s0Whnf.name,
        sort1: s1Whnf.name,
      });
    }
    case "Let": {
      const checkR = typeCheck(jc, t.def, t.type);
      if (isErr(checkR))
        return checkR;
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
      const funTypeWhnf = whnf(zdsnf(jc, funType.value));
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

function typeCheck(jc: JudgContext, t: Term, expected: Term): Result<true, TypeError> {
  switch (t.tag) {
    case "Lam": {
      const expectedWhnf = whnf(zdsnf(jc, expected));
      if (expectedWhnf.tag !== "Pi")
        return err({ tag: "ExpectedPi", fun: t, actual: expectedWhnf });
      if (!whnfEq(jc, t.type, expectedWhnf.type))
        return err({ tag: "TypeMismatch", expected: expectedWhnf.type, actual: t.type });
      const local = jc.local.slice();
      local.push(ctxVar(t.name, t.type));
      const bodyExpected = subst(expectedWhnf.body, expectedWhnf.name, { tag: "Var", name: t.name });
      return typeCheck(judgCtx(jc.global, local), t.body, bodyExpected);
    }
    case "Pair": {
      const expectedWhnf = whnf(zdsnf(jc, expected));
      if (expectedWhnf.tag !== "Sig")
        return err({ tag: "ExpectedSigma", pair: t, actual: expectedWhnf });
      const fstCheck = typeCheck(jc, t.fst, expectedWhnf.type);
      if (isErr(fstCheck))
        return fstCheck;
      const sndExpected = subst(expectedWhnf.body, expectedWhnf.name, t.fst);
      return typeCheck(jc, t.snd, sndExpected);
    }
    default: {
      const inferred = typeInfer(jc, t);
      if (isErr(inferred))
        return inferred;
      if (!whnfEq(jc, inferred.value, expected))
        return err({ tag: "TypeMismatch", expected, actual: inferred.value });
      return succ(true);
    }
  }
}