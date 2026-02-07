import * as N from "./namedast";
import * as I from "./indexast";
import { type Name } from "./pdef";

export function NamedtoIndex(term: N.Term, env: Name[]): I.Term {
  switch (term.tag) {
    case "Sort":
      return I.sort(term.name);
    case "Var": {
      const index = env.indexOf(term.name);
      return index === -1 ? I.free(term.name) : I.bind(index);
    }
    case "Lam":
      return I.lam(
        NamedtoIndex(term.type, env),
        NamedtoIndex(term.body, [term.name, ...env])
      );
    case "Pi":
      return I.pi(
        NamedtoIndex(term.type, env),
        NamedtoIndex(term.body, [term.name, ...env])
      );
    case "Pair":
      return I.pair(
        NamedtoIndex(term.fst, env),
        NamedtoIndex(term.snd, env),
        term.as ? NamedtoIndex(term.as, env) : undefined
      );
    case "Fst":
      return I.fst(NamedtoIndex(term.pair, env));
    case "Snd":
      return I.snd(NamedtoIndex(term.pair, env));
    case "Sig":
      return I.sig(
        NamedtoIndex(term.type, env),
        NamedtoIndex(term.body, [term.name, ...env])
      );
    case "Let":
      return I.letIn(
        term.type ? NamedtoIndex(term.type, env) : undefined,
        NamedtoIndex(term.def, env),
        NamedtoIndex(term.body, [term.name, ...env])
      );
    case "App":
      return I.app(
        NamedtoIndex(term.fun, env),
        NamedtoIndex(term.arg, env)
      );
  }
}

export const toGlobalContext = (ctx: N.GlobalContext): I.GlobalContext => {
  return ctx.map(elem => {
    const convert = (t: N.Term) => NamedtoIndex(t, []);
    if (elem.tag === "Var")
      return I.globalElem(elem.name, convert(elem.type));
    return I.globalElem(elem.name, convert(elem.type), convert(elem.def));
  });
}