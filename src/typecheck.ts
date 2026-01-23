import { type Sort, type Name, type Term, sort, lam, pi, pair, fst, snd, sig, letIn, app, varia } from "./ast";
import { type Result, succ, err, isErr } from "./result";
import { type CtxElement, type Context, ctxVar, ctxDef, type JudgContext, judgCtx } from "./core";
import { subst, alphaEq } from "./definition";

type TypeError =
  | { tag: "TypeHasNoType" }
  | { tag: "UnboundVariable"; name: Name }
  | { tag: "ExpectedSort"; actual: Term }
  | { tag: "ImpossibleCombination", sort0: Sort, sort1: Sort }
  | { tag: "ExpectedPi"; fun: Term; actual: Term }
  | { tag: "ExpectedSigma"; pair: Term; actual: Term }
  | { tag: "TypeMismatch"; expected: Term; actual: Term };

type WFError = { error: TypeError; at: CtxElement };

function dszNF(jc: JudgContext, t: Term): Term {
  switch (t.tag) {
    case "Sort":
      return t;
    case "Var": {
      const le = jc.local.slice().reverse().find(e => e.name === t.name);
      if (le && le.tag === "Def")
        return dszNF(jc, le.def);
      const ge = jc.global.slice().reverse().find(e => e.name === t.name);
      if (ge && ge.tag === "Def")
        return dszNF(jc, ge.def);
      return t;
    }
    case "Lam":
      return lam(t.name, dszNF(jc, t.type), dszNF(jc, t.body));
    case "Pi":
      return pi(t.name, dszNF(jc, t.type), dszNF(jc, t.body));
    case "Pair":
      return pair(dszNF(jc, t.fst), dszNF(jc, t.snd), t.as ? dszNF(jc, t.as) : undefined);
    case "Fst": {
      if (t.pair.tag === "Pair")
        return dszNF(jc, t.pair.fst);
      return fst(dszNF(jc, t.pair));
    }
    case "Snd": {
      if (t.pair.tag === "Pair")
        return dszNF(jc, t.pair.snd);
      return snd(dszNF(jc, t.pair));
    }
    case "Sig":
      return sig(t.name, dszNF(jc, t.type), dszNF(jc, t.body));
    case "Let":
      return dszNF(jc, subst(t.body, t.name, t.def));
    case "App":
      return app(dszNF(jc, t.fun), dszNF(jc, t.arg));
  }
}

function headNF(t: Term): Term {
  switch (t.tag) {
    case "Sort":
    case "Var":
    case "Lam":
      return t;
    case "Pi":
      return pi(t.name, headNF(t.type), headNF(t.body));
    case "Pair":
      return pair(headNF(t.fst), headNF(t.snd), t.as ? headNF(t.as) : undefined);
    case "Fst":
      return fst(headNF(t.pair));
    case "Snd":
      return snd(headNF(t.pair));
    case "Sig":
      return sig(t.name, headNF(t.type), headNF(t.body));
    case "Let":
      return letIn(t.name, t.type ? headNF(t.type) : undefined, headNF(t.def), headNF(t.body));
    case "App": {
      const fun = headNF(t.fun);
      if (fun.tag === "Lam")
        return headNF(subst(fun.body, fun.name, t.arg));
      return app(fun, t.arg);
    }
  }
}

function ahEq(jc: JudgContext, t: Term, u: Term): boolean {
  const tWhnf = headNF(dszNF(jc, t));
  const uWhnf = headNF(dszNF(jc, u));
  if (tWhnf.tag === "Lam") {
    const tname = tWhnf.name;
    const tbody = tWhnf.body;
    const local = jc.local.slice();
    local.push(ctxVar(tname, tWhnf.type));
    return ahEq(judgCtx(jc.global, local), tbody, app(uWhnf, varia(tname)));
  }
  if (uWhnf.tag === "Lam") {
    const uname = uWhnf.name;
    const ubody = uWhnf.body;
    const local = jc.local.slice();
    local.push(ctxVar(uname, uWhnf.type));
    return ahEq(judgCtx(jc.global, local), app(tWhnf, varia(uname)), ubody);
  }
  return alphaEq(tWhnf, uWhnf);
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
      const sNF = headNF(dszNF(jc, s.value));
      if (sNF.tag !== "Sort")
        return err({ tag: "ExpectedSort", actual: sNF });
      return succ(termType);
    }
    case "Pi": {
      const s0 = typeInfer(jc, t.type);
      if (isErr(s0))
        return s0;
      const s0NF = headNF(dszNF(jc, s0.value));
      if (s0NF.tag !== "Sort")
        return err({ tag: "ExpectedSort", actual: s0NF });
      const local = jc.local.slice();
      local.push(ctxVar(t.name, t.type));
      const s1 = typeInfer(judgCtx(jc.global, local), t.body);
      if (isErr(s1))
        return s1;
      const s1NF = headNF(dszNF(jc, s1.value));
      if (s1NF.tag !== "Sort")
        return err({ tag: "ExpectedSort", actual: s1NF });
      return succ(s1NF);
    }
    case "Pair": {
      if (t.as) {
        const asCheck = typeCheck(jc, t, t.as);
        if (isErr(asCheck))
          return asCheck;
        return succ(t.as);
      } else {
        const firstType = typeInfer(jc, t.fst);
        if (isErr(firstType))
          return firstType;
        const secondType = typeInfer(jc, t.snd);
        if (isErr(secondType))
          return secondType;
        return succ(sig("_", firstType.value, secondType.value));
      }
    }
    case "Fst": {
      const pairType = typeInfer(jc, t.pair);
      if (isErr(pairType))
        return pairType;
      const pairTypeNF = headNF(dszNF(jc, pairType.value));
      if (pairTypeNF.tag !== "Sig")
        return err({ tag: "ExpectedSigma", pair: t.pair, actual: pairTypeNF });
      return succ(pairTypeNF.type);
    }
    case "Snd": {
      const pairType = typeInfer(jc, t.pair);
      if (isErr(pairType))
        return pairType;
      const pairTypeNF = headNF(dszNF(jc, pairType.value));
      if (pairTypeNF.tag !== "Sig")
        return err({ tag: "ExpectedSigma", pair: t.pair, actual: pairTypeNF });
      return succ(subst(pairTypeNF.body, pairTypeNF.name, fst(t.pair)));
    }
    case "Sig": {
      const s0 = typeInfer(jc, t.type);
      if (isErr(s0))
        return s0;
      const s0NF = headNF(dszNF(jc, s0.value));
      if (s0NF.tag !== "Sort")
        return err({ tag: "ExpectedSort", actual: s0NF });
      const local = jc.local.slice();
      local.push(ctxVar(t.name, t.type));
      const s1 = typeInfer(judgCtx(jc.global, local), t.body);
      if (isErr(s1))
        return s1;
      const s1NF = headNF(dszNF(jc, s1.value));
      if (s1NF.tag !== "Sort")
        return err({ tag: "ExpectedSort", actual: s1NF });
      if ((s0NF.name === "Prop" && s1NF.name === "Prop")
        || s1NF.name === "Type")
        return succ(s1NF);
      return err({
        tag: "ImpossibleCombination",
        sort0: s0NF.name,
        sort1: s1NF.name,
      });
    }
    case "Let": {
      let defType: Term;
      if (t.type) {
        const defCheck = typeCheck(jc, t.def, t.type);
        if (isErr(defCheck))
          return defCheck;
        defType = t.type;
      } else {
        const defInfer = typeInfer(jc, t.def);
        if (isErr(defInfer))
          return defInfer;
        defType = defInfer.value;
      }
      const local = jc.local.slice();
      local.push(ctxDef(t.name, defType, t.def));
      const bodyType = typeInfer(judgCtx(jc.global, local), t.body);
      if (isErr(bodyType))
        return bodyType;
      return succ(subst(bodyType.value, t.name, t.def));
    }
    case "App": {
      const funType = typeInfer(jc, t.fun);
      if (isErr(funType))
        return funType;
      const funTypeNF = headNF(dszNF(jc, funType.value));
      if (funTypeNF.tag !== "Pi")
        return err({ tag: "ExpectedPi", fun: t.fun, actual: funTypeNF });
      const argType = typeInfer(jc, t.arg);
      if (isErr(argType))
        return argType;
      if (!ahEq(jc, argType.value, funTypeNF.type))
        return err({ tag: "TypeMismatch", expected: funTypeNF.type, actual: argType.value });
      return succ(subst(funTypeNF.body, funTypeNF.name, t.arg));
    }
  }
}

function typeCheck(jc: JudgContext, t: Term, expected: Term): Result<true, TypeError> {
  switch (t.tag) {
    case "Pair": {
      const expectedNF = headNF(dszNF(jc, expected));
      if (expectedNF.tag !== "Sig")
        return err({ tag: "ExpectedSigma", pair: t, actual: expectedNF });
      const name = expectedNF.name;
      const fstExpected = expectedNF.type
      const fstCheck = typeCheck(jc, t.fst, fstExpected);
      if (isErr(fstCheck))
        return fstCheck;
      const sndExpected = subst(expectedNF.body, expectedNF.name, t.fst);
      const sndCheck = typeCheck(jc, t.snd, sndExpected);
      if (isErr(sndCheck))
        return sndCheck;
      const local = jc.local.slice();
      local.push(ctxVar(name, fstExpected));
      const extendedJc = judgCtx(jc.global, local);
      const s = typeInfer(extendedJc, sndExpected);
      if (isErr(s))
        return s;
      const sNF = headNF(dszNF(extendedJc, s.value));
      if (sNF.tag !== "Sort")
        return err({ tag: "ExpectedSort", actual: sNF });
      return succ(true);
    }
    default: {
      const inferred = typeInfer(jc, t);
      if (isErr(inferred))
        return inferred;
      if (!ahEq(jc, inferred.value, expected))
        return err({ tag: "TypeMismatch", expected, actual: inferred.value });
      return succ(true);
    }
  }
}