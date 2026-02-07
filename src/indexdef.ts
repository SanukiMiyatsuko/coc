import { app, bind, letIn, pair, type Term } from "./indexast";

export function shift(t: Term, d: number, c: number): Term {
  switch (t.tag) {
    case "Sort":
    case "Free":
      return t;
    case "Bind":
      return t.index >= c ? bind(t.index + d) : t;
    case "Lam":
    case "Pi":
    case "Sig":
      return {
        ...t,
        type: shift(t.type, d, c),
        body: shift(t.body, d, c + 1)
      };
    case "Let": {
      let type: Term | undefined = undefined;
      if (t.type) {
        type = shift(t.type, d, c);
      }
      return letIn(
        type,
        shift(t.def, d, c),
        shift(t.body, d, c + 1)
      );
    }
    case "Pair":
      return pair(
        shift(t.fst, d, c),
        shift(t.snd, d, c),
        t.as ? shift(t.as, d, c) : undefined
      );
    case "Fst":
    case "Snd":
      return {
        ...t,
        pair: shift(t.pair, d, c)
      };
    case "App":
      return app(
        shift(t.fun, d, c),
        shift(t.arg, d, c)
      );
  }
}

export function subst(t: Term, idx: number, u: Term): Term {
  switch (t.tag) {
    case "Sort":
    case "Free":
      return t;
    case "Bind":
      return t.index === idx ? u : t;
    case "Lam":
    case "Pi":
    case "Sig":
      return {
        ...t,
        type: subst(t.type, idx, u),
        body: subst(t.body, idx + 1, shift(u, 1, 0))
      };
    case "Let": {
      let type: Term | undefined = undefined;
      if (t.type) {
        type = subst(t.type, idx, u);
      }
      return letIn(
        type,
        subst(t.def, idx, u),
        subst(t.body, idx + 1, shift(u, 1, 0))
      );
    }
    case "Pair":
      return pair(
        subst(t.fst, idx, u),
        subst(t.snd, idx, u),
        t.as ? subst(t.as, idx, u) : undefined
      );
    case "Fst":
    case "Snd":
      return {
        ...t,
        pair: subst(t.pair, idx, u)
      };
    case "App":
      return app(
        subst(t.fun, idx, u),
        subst(t.arg, idx, u)
      );
  }
}

export function eq(t: Term, u: Term): boolean {
  switch (t.tag) {
    case "Sort":
    case "Free":
      return t.tag === u.tag && t.name === u.name;
    case "Bind":
      return t.tag === u.tag && t.index === u.index;
    case "Lam":
    case "Pi":
    case "Sig":
      return t.tag === u.tag
        && eq(t.type, u.type)
        && eq(t.body, u.body);
    case "Pair": {
      if (t.tag !== u.tag)
        return false;
      if (!eq(t.fst, u.fst))
        return false;
      if (!eq(t.snd, u.snd))
        return false;
      if (t.as === undefined && u.as === undefined)
        return true;
      if (t.as === undefined || u.as === undefined)
        return false;
      return eq(t.as, u.as);
    }
    case "Fst":
    case "Snd":
      return t.tag === u.tag
        && eq(t.pair, u.pair);
    case "Let": {
      if (t.tag !== u.tag)
        return false;
      if (!eq(t.def, u.def))
        return false;
      if (!eq(t.body, u.body))
        return false;
      if (t.type === undefined && u.type === undefined)
        return true;
      if (t.type === undefined || u.type === undefined)
        return false;
      return eq(t.type, u.type);
    }
    case "App":
      return t.tag === u.tag
        && eq(t.fun, u.fun)
        && eq(t.arg, u.arg);
  }
}