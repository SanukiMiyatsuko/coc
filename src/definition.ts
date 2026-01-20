import { type Name, type Term, varia, lam, pi, pair, fst, snd, sig, letIn, app } from "./ast";

export function freeVar(t: Term, acc: Set<Name> = new Set()): Set<Name> {
  switch (t.tag) {
    case "Sort":
      return acc;
    case "Var": {
      acc.add(t.name);
      return acc;
    }
    case "Lam":
    case "Pi":
    case "Sig":
    case "Let":
      break;
    case "Pair": {
      freeVar(t.fst, acc);
      freeVar(t.snd, acc);
      return acc;
    }
    case "Fst":
    case "Snd":
      return freeVar(t.pair, acc);
    case "App": {
      freeVar(t.fun, acc);
      freeVar(t.arg, acc);
      return acc;
    }
  }
  freeVar(t.type, acc);
  if (t.tag === "Let")
    freeVar(t.def, acc);
  const bf = freeVar(t.body);
  bf.delete(t.name);
  bf.forEach(v => acc.add(v));
  return acc;
}

function freshName(base: Name, used: Set<Name> = new Set()): Name {
  if (!used.has(base)) return base;
  const match = base.match(/_(\d+)$/);
  let i = match ? Number(match[1]) + 1 : 0;
  const sliced = match ? base.slice(0, match.index) : base;
  let cand: Name;
  do {
    cand = `${sliced}_${i}`;
    i += 1;
  } while (used.has(cand));
  return cand;
}

function substInter(t: Term, v: Name, u: Term, fu: Set<Name>): Term {
  switch (t.tag) {
    case "Sort":
      return t;
    case "Var":
      return t.name === v ? u : t;
    case "Lam":
    case "Pi":
    case "Sig": {
      const x = t.name;
      const pt = substInter(t.type, v, u, fu);
      if (x === v)
        return t.tag === "Lam"
          ? lam(x, pt, t.body)
          : t.tag === "Pi"
            ? pi(x, pt, t.body)
            : sig(x, pt, t.body);
      if (!fu.has(x)) {
        const body = substInter(t.body, v, u, fu);
        return t.tag === "Lam"
          ? lam(x, pt, body)
          : t.tag === "Pi"
            ? pi(x, pt, body)
            : sig(x, pt, body);
      }
      const used = new Set(fu);
      used.add(v);
      freeVar(t, used);
      const y = freshName(x, used);
      const rename = substInter(t.body, x, varia(y), new Set([y]));
      const body = substInter(rename, v, u, fu);
      return t.tag === "Lam"
        ? lam(y, pt, body)
        : t.tag === "Pi"
          ? pi(y, pt, body)
          : sig(y, pt, body);
    }
    case "Pair": {
      const fun = substInter(t.fst, v, u, fu);
      const arg = substInter(t.snd, v, u, fu);
      return pair(fun, arg);
    }
    case "Fst":
      return fst(substInter(t.pair, v, u, fu));
    case "Snd":
      return snd(substInter(t.pair, v, u, fu));
    case "Let": {
      const x = t.name;
      const pt = substInter(t.type, v, u, fu);
      const def = substInter(t.def, v, u, fu);
      if (x === v)
        return letIn(x, pt, def!, t.body);
      if (!fu.has(x)) {
        const body = substInter(t.body, v, u, fu);
        return letIn(x, pt, def!, body);
      }
      const used = new Set(fu);
      used.add(v);
      freeVar(t, used);
      const y = freshName(x, used);
      const rename = substInter(t.body, x, varia(y), new Set([y]));
      const body = substInter(rename, v, u, fu);
      return letIn(y, pt, def!, body);
    }
    case "App": {
      const fun = substInter(t.fun, v, u, fu);
      const arg = substInter(t.arg, v, u, fu);
      return app(fun, arg);
    }
  }
}

export function subst(t: Term, v: Name, u: Term): Term {
  const ft = freeVar(t);
  if (!ft.has(v))
    return t;
  const fu = freeVar(u);
  return substInter(t, v, u, fu);
}

export function alphaEq(t: Term, u: Term): boolean {
  switch (t.tag) {
    case "Sort":
    case "Var":
      return t.tag === u.tag && t.name === u.name;
    case "Lam":
    case "Pi":
    case "Sig": {
      if (t.tag !== u.tag)
        return false;
      const used = new Set([t.name, u.name]);
      freeVar(t.body, used);
      freeVar(u.body, used);
      const fresh = freshName(t.name, used);
      const newVar = varia(fresh);
      return alphaEq(t.type, u.type)
        && alphaEq(
          subst(t.body, t.name, newVar),
          subst(u.body, u.name, newVar)
        );
    }
    case "Pair":
      return t.tag === u.tag
        && alphaEq(t.fst, u.fst)
        && alphaEq(t.snd, u.snd);
    case "Fst":
    case "Snd":
      return t.tag === u.tag
        && alphaEq(t.pair, u.pair);
    case "Let": {
      if (t.tag !== u.tag)
        return false;
      const used = new Set([t.name, u.name]);
      freeVar(t.body, used);
      freeVar(u.body, used);
      const fresh = freshName(t.name, used);
      const newVar = varia(fresh);
      return alphaEq(t.type, u.type)
        && alphaEq(t.def, u.def)
        && alphaEq(
          subst(t.body, t.name, newVar),
          subst(u.body, u.name, newVar)
        );
    }
    case "App":
      return t.tag === u.tag
        && alphaEq(t.fun, u.fun)
        && alphaEq(t.arg, u.arg);
  }
}