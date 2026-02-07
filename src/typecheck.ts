import { type Sort, type Name } from "./pdef";
import { type Term, sort, pi, fst, snd, sig, app, type GlobalElement, type GlobalContext, type JudgContext, judgCtx, bind, type LocalContext } from "./indexast";
import { type Result, succ, err, isErr } from "./result";
import { eq, shift, subst } from "./indexdef";

type TypeError =
  | { tag: "TypeHasNoType" }
  | { tag: "UnboundVariableName"; name: Name }
  | { tag: "UnboundVariableIndex"; index: number }
  | { tag: "ExpectedSort"; actual: Term }
  | { tag: "ImpossibleCombination", sort0: Sort, sort1: Sort }
  | { tag: "ExpectedPi"; fun: Term; actual: Term }
  | { tag: "ExpectedSigma"; pair: Term; actual: Term }
  | { tag: "TypeMismatch"; expected: Term; actual: Term };

type WFError = { error: TypeError; at: GlobalElement };

function pushLocal(jc: JudgContext, type: Term, def?: Term): JudgContext {
  if (def)
    return {
      ...jc,
      local: [{ tag: "Def", type, def }, ...jc.local]
    };
  return {
    ...jc,
    local: [{ tag: "Var", type }, ...jc.local]
  };
}

function whNF(jc: JudgContext, t: Term): Term {
  switch (t.tag) {
    case "Free": {
      const ge = jc.global.slice().reverse().find(e => e.name === t.name);
      if (ge && ge.tag === "Def")
        return whNF(jc, ge.def);
      return t;
    }
    case "Bind": {
      const le = jc.local[t.index];
      if (le && le.tag === "Def")
        return whNF(jc, shift(le.def, t.index + 1, 0));
      return t;
    }
    case "Fst": {
      const pair = whNF(jc, t.pair);
      if (pair.tag === "Pair")
        return whNF(jc, pair.fst);
      return fst(pair);
    }
    case "Snd": {
      const pair = whNF(jc, t.pair);
      if (pair.tag === "Pair")
        return whNF(jc, pair.snd);
      return snd(pair);
    }
    case "Let":
      return whNF(jc, shift(subst(t.body, 0, shift(t.def, 1, 0)), -1, 0));
    case "App": {
      const fun = whNF(jc, t.fun);
      if (fun.tag === "Lam")
        return whNF(jc, shift(subst(fun.body, 0, shift(t.arg, 1, 0)), -1, 0));
      return app(fun, t.arg);
    }
    default:
      return t;
  }
}

function convWhNF(jc: JudgContext, t0: Term, t1: Term): boolean {
  const w0 = whNF(jc, t0);
  const w1 = whNF(jc, t1);
  if (w0.tag === "Lam" && w1.tag !== "Lam")
    return conv(pushLocal(jc, w0.type), w0.body, app(shift(w1, 1, 0), bind(0)));
  if (w0.tag !== "Lam" && w1.tag === "Lam")
    return conv(pushLocal(jc, w1.type), app(shift(w0, 1, 0), bind(0)), w1.body);
  if (w0.tag === "Pair" && w1.tag !== "Pair")
    return conv(jc, w0.fst, fst(w1))
      && conv(jc, w0.snd, snd(w1));
  if (w0.tag !== "Pair" && w1.tag === "Pair")
    return conv(jc, fst(w0), w1.fst)
      && conv(jc, snd(w0), w1.snd);
  if (eq(w0, w1))
    return true;
  switch (w0.tag) {
    case "Lam":
    case "Pi":
    case "Sig": {
      return w0.tag === w1.tag
        && conv(jc, w0.type, w1.type)
        && conv(pushLocal(jc, w0.type), w0.body, w1.body);
    }
    case "Pair": {
      if (w0.tag !== w1.tag)
        return false;
      if (!conv(jc, w0.fst, w1.fst))
        return false;
      if (!conv(jc, w0.snd, w1.snd))
        return false;
      if (w0.as === undefined && w1.as === undefined)
        return true;
      if (w0.as === undefined || w1.as === undefined)
        return false;
      return conv(jc, w0.as, w1.as);
    }
    case "Fst":
    case "Snd": {
      return w0.tag === w1.tag
        && conv(jc, w0.pair, w1.pair);
    }
    case "App": {
      return w0.tag === w1.tag
        && conv(jc, w0.fun, w1.fun)
        && conv(jc, w0.arg, w1.arg);
    }
  }
  return false;
}

function conv(jc: JudgContext, t0: Term, t1: Term): boolean {
  if (eq(t0, t1))
    return true;
  return convWhNF(jc, t0, t1);
}

function wellFormedLocal(jc: JudgContext): Result<true, TypeError> {
  const l: LocalContext = [];
  for (let idx = jc.local.length - 1; idx >= 0; idx--) {
    const e = jc.local[idx];
    const ctx = judgCtx(jc.global, l);
    if (e.tag === "Var") {
      const r = typeInfer(ctx, e.type);
      if (isErr(r))
        return r;
      if (r.value.tag !== "Sort")
        return err({ tag: "ExpectedSort", actual: r.value });
    } else {
      const r = typeCheck(ctx, e.def, e.type);
      if (isErr(r))
        return r;
    }
    l.unshift(e);
  }
  return succ(true);
}

function typeInfer(jc: JudgContext, t: Term): Result<Term, TypeError> {
  switch (t.tag) {
    case "Sort": {
      const wf = wellFormedLocal(jc);
      if (isErr(wf))
        return wf;
      if (t.name === "Type")
        return err({ tag: "TypeHasNoType" });
      return succ(sort("Type"));
    }
    case "Free": {
      const ge = jc.global.slice().reverse().find(e => e.name === t.name);
      if (ge)
        return succ(ge.type);
      return err({ tag: "UnboundVariableName", name: t.name });
    }
    case "Bind": {
      const wf = wellFormedLocal(jc);
      if (isErr(wf))
        return wf;
      const le = jc.local[t.index];
      if (le)
        return succ(shift(le.type, t.index + 1, 0));
      return err({ tag: "UnboundVariableIndex", index: t.index });
    }
    case "Lam": {
      const newJc = pushLocal(jc, t.type);
      const bodyType = typeInfer(newJc, t.body);
      if (isErr(bodyType))
        return bodyType;
      const termType = pi(t.type, bodyType.value);
      const s = typeInfer(jc, termType);
      if (isErr(s))
        return s;
      const sWhNF = whNF(jc, s.value);
      if (sWhNF.tag !== "Sort")
        return err({ tag: "ExpectedSort", actual: sWhNF });
      return succ(termType);
    }
    case "Pi": {
      const s0 = typeInfer(jc, t.type);
      if (isErr(s0))
        return s0;
      const s0WhNF = whNF(jc, s0.value);
      if (s0WhNF.tag !== "Sort")
        return err({ tag: "ExpectedSort", actual: s0WhNF });
      const newJc = pushLocal(jc, t.type);
      const s1 = typeInfer(newJc, t.body);
      if (isErr(s1))
        return s1;
      const s1WhNF = whNF(jc, s1.value);
      if (s1WhNF.tag !== "Sort")
        return err({ tag: "ExpectedSort", actual: s1WhNF });
      return succ(s1WhNF);
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
        const sigma = sig(firstType.value, shift(secondType.value, 1, 0));
        const s = typeInfer(jc, sigma);
        if (isErr(s))
          return s;
        const sWhNF = whNF(jc, s.value);
        if (sWhNF.tag !== "Sort")
          return err({ tag: "ExpectedSort", actual: sWhNF });
        return succ(sigma);
      }
    }
    case "Fst": {
      const pairType = typeInfer(jc, t.pair);
      if (isErr(pairType))
        return pairType;
      const pairTypeWhNF = whNF(jc, pairType.value);
      if (pairTypeWhNF.tag !== "Sig")
        return err({ tag: "ExpectedSigma", pair: t.pair, actual: pairTypeWhNF });
      return succ(pairTypeWhNF.type);
    }
    case "Snd": {
      const pairType = typeInfer(jc, t.pair);
      if (isErr(pairType))
        return pairType;
      const pairTypeWhNF = whNF(jc, pairType.value);
      if (pairTypeWhNF.tag !== "Sig")
        return err({ tag: "ExpectedSigma", pair: t.pair, actual: pairTypeWhNF });
      return succ(shift(subst(pairTypeWhNF.body, 0, shift(fst(t.pair), 1, 0)), -1, 0));
    }
    case "Sig": {
      const s0 = typeInfer(jc, t.type);
      if (isErr(s0))
        return s0;
      const s0WhNF = whNF(jc, s0.value);
      if (s0WhNF.tag !== "Sort")
        return err({ tag: "ExpectedSort", actual: s0WhNF });
      const newJc = pushLocal(jc, t.type);
      const s1 = typeInfer(newJc, t.body);
      if (isErr(s1))
        return s1;
      const s1WhNF = whNF(jc, s1.value);
      if (s1WhNF.tag !== "Sort")
        return err({ tag: "ExpectedSort", actual: s1WhNF });
      if (s0WhNF.name === "Type" && s1WhNF.name === "Prop")
        return err({
          tag: "ImpossibleCombination",
          sort0: "Type",
          sort1: "Prop",
        });
      return succ(s1WhNF);
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
      const newJc = pushLocal(jc, defType, t.def);
      const bodyType = typeInfer(newJc, t.body);
      if (isErr(bodyType))
        return bodyType;
      return succ(shift(subst(bodyType.value, 0, shift(t.def, 1, 0)), -1, 0));
    }
    case "App": {
      const funType = typeInfer(jc, t.fun);
      if (isErr(funType))
        return funType;
      const funTypeWhNF = whNF(jc, funType.value);
      if (funTypeWhNF.tag !== "Pi")
        return err({ tag: "ExpectedPi", fun: t.fun, actual: funTypeWhNF });
      const argType = typeInfer(jc, t.arg);
      if (isErr(argType))
        return argType;
      if (!conv(jc, argType.value, funTypeWhNF.type))
        return err({ tag: "TypeMismatch", expected: argType.value, actual: funTypeWhNF.type });
      return succ(shift(subst(funTypeWhNF.body, 0, shift(t.arg, 1, 0)), -1, 0));
    }
  }
}

function typeCheck(jc: JudgContext, t: Term, expected: Term): Result<true, TypeError> {
  const expectedWhNF = whNF(jc, expected);
  switch (t.tag) {
    case "Pair": {
      if (expectedWhNF.tag !== "Sig")
        return err({ tag: "ExpectedSigma", pair: t, actual: expectedWhNF });
      const fstExpected = expectedWhNF.type
      const fstCheck = typeCheck(jc, t.fst, fstExpected);
      if (isErr(fstCheck))
        return fstCheck;
      const sndExpected = shift(subst(expectedWhNF.body, 0, shift(t.fst, 1, 0)), -1, 0);
      const sndCheck = typeCheck(jc, t.snd, sndExpected);
      if (isErr(sndCheck))
        return sndCheck;
      const newJc = pushLocal(jc, fstExpected);
      const s = typeInfer(newJc, shift(sndExpected, 1, 0));
      if (isErr(s))
        return s;
      const sWhNF = whNF(jc, s.value);
      if (sWhNF.tag !== "Sort")
        return err({ tag: "ExpectedSort", actual: sWhNF });
      return succ(true);
    }
    default: {
      const inferred = typeInfer(jc, t);
      if (isErr(inferred))
        return inferred;
      if (!conv(jc, inferred.value, expectedWhNF))
        return err({ tag: "TypeMismatch", expected: inferred.value, actual: expectedWhNF });
      return succ(true);
    }
  }
}

export function wellFormedGlobal(global: GlobalContext): Result<true, WFError> {
  const g: GlobalContext = [];
  for (const e of global) {
    if (e.tag === "Var") {
      const r = typeInfer(judgCtx(g, []), e.type);
      if (isErr(r))
        return err({ error: r.err, at: e });
      if (r.value.tag !== "Sort")
        return err({
          error: { tag: "ExpectedSort", actual: r.value },
          at: e
        });
    } else {
      const r = typeCheck(judgCtx(g, []), e.def, e.type);
      if (isErr(r))
        return err({ error: r.err, at: e });
    }
    g.push(e);
  }
  return succ(true);
}