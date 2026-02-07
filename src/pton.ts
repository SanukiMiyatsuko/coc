import * as P from "./pdef";
import * as N from "./namedast";

let counter = 0;
const anon = "@";

function elabBinders(
  bs: P.Binder[],
  body: N.Term,
  f: (name: P.Name, type: N.Term, body: N.Term) => N.Term
): N.Term {
  return bs.reduceRight((acc, b) => {
    if (b.tag === "Var")
      return b.names.reduceRight(
        (acc2, n) => f(n, elabTerm(b.type), acc2),
        acc
      );
    else
      return N.letIn(
        b.name,
        b.type ? elabTerm(b.type) : undefined,
        elabTerm(b.def),
        acc
      );
  }, body);
}

export function elabTerm(t: P.PTerm): N.Term {
  switch (t.tag) {
    case "Sort":
      return N.sort(t.name);
    case "Variable":
      return N.varia(t.name);
    case "Lambda":
      return elabBinders(
        t.binders,
        elabTerm(t.body),
        N.lam
      );
    case "Pi":
      return elabBinders(
        t.binders,
        elabTerm(t.body),
        N.pi
      );
    case "Arrow": {
      const index = counter++;
      return N.pi(
        `${anon}_${index}`,
        elabTerm(t.in),
        elabTerm(t.out)
      );
    }
    case "Pair":
      return N.pair(
        elabTerm(t.first),
        elabTerm(t.second),
        t.type ? elabTerm(t.type) : undefined
      );
    case "First":
      return N.fst(elabTerm(t.pair));
    case "Second":
      return N.snd(elabTerm(t.pair));
    case "Sigma":
      return elabBinders(
        t.binders,
        elabTerm(t.body),
        N.sig
      );
    case "Prod": {
      const index = counter++;
      return N.sig(
        `${anon}_${index}`,
        elabTerm(t.first),
        elabTerm(t.second)
      );
    }
    case "Let": {
      const defType = t.type
        ? elabBinders(
            t.binders,
            elabTerm(t.type),
            N.pi
          )
        : undefined;
      const defCore = elabBinders(
        t.binders,
        elabTerm(t.def),
        N.lam
      );
      return N.letIn(
        t.name,
        defType,
        defCore,
        elabTerm(t.body)
      );
    }
    case "Apply": {
      const [head, ...args] = t.apply.map(elabTerm);
      return args.reduce((f, a) => N.app(f, a), head);
    }
  }
}

export function elabGlobalContext(ctx: P.PGlobalContext): N.GlobalContext {
  return ctx.map(g => {
    const type = elabBinders(g.binders, elabTerm(g.type), N.pi);
    if (g.tag === "Var") {
      return N.globalElem(g.name, type, undefined, g.range);
    } else {
      const def = elabBinders(g.binders, elabTerm(g.def), N.lam);
      return N.globalElem(g.name, type, def, g.range);
    }
  });
}