import * as P from "./pdef";
import * as A from "./ast";

const anon = "_";

function elabBinders(
  bs: P.Binder[],
  body: A.Term,
  f: (name: P.Name, type: A.Term, body: A.Term) => A.Term
): A.Term {
  return bs.reduceRight((acc, b) => {
    if (b.tag === "Var")
      return b.names.reduceRight(
        (acc2, n) => f(n, elabTerm(b.type), acc2),
        acc
      );
    else
      return A.letIn(
        b.name,
        b.type ? elabTerm(b.type) : undefined,
        elabTerm(b.def),
        acc
      );
  }, body);
}

export function elabTerm(t: P.PTerm): A.Term {
  switch (t.tag) {
    case "Sort":
      return A.sort(t.name);
    case "Variable":
      return A.varia(t.name);
    case "Lambda":
      return elabBinders(
        t.binders,
        elabTerm(t.body),
        A.lam
      );
    case "Pi":
      return elabBinders(
        t.binders,
        elabTerm(t.body),
        A.pi
      );
    case "Arrow":
      return A.pi(
        anon,
        elabTerm(t.in),
        elabTerm(t.out)
      );
    case "Pair":
      return A.pair(
        elabTerm(t.first),
        elabTerm(t.second),
        t.type ? elabTerm(t.type) : undefined
      );
    case "First":
      return A.fst(elabTerm(t.pair));
    case "Second":
      return A.snd(elabTerm(t.pair));
    case "Sigma":
      return elabBinders(
        t.binders,
        elabTerm(t.body),
        A.sig
      );
    case "Prod":
      return A.sig(
        anon,
        elabTerm(t.first),
        elabTerm(t.second)
      );
    case "Let": {
      const defType = t.type
        ? elabBinders(
            t.binders,
            elabTerm(t.type),
            A.pi
          )
        : undefined;
      const defCore = elabBinders(
        t.binders,
        elabTerm(t.def),
        A.lam
      );
      return A.letIn(
        t.name,
        defType,
        defCore,
        elabTerm(t.body)
      );
    }
    case "Apply": {
      const [head, ...args] = t.apply.map(elabTerm);
      return args.reduce((f, a) => A.app(f, a), head);
    }
  }
}

export function elabGlobalContext(pgc: P.PGlobalContext): A.Context {
  const ctx: A.Context = [];
  for (const g of pgc) {
    let term = elabTerm(g.elem.type);
    for (let i = g.local.length - 1; i >= 0; i--) {
      const e = g.local[i];
      if (e.tag === "Var") {
        term = A.pi(e.name, elabTerm(e.type), term);
      } else {
        term = A.letIn(
          e.name,
          e.type ? elabTerm(e.type) : undefined,
          elabTerm(e.def),
          term
        );
      }
    }
    let defTerm = g.elem.tag === "Def" ? elabTerm(g.elem.def) : undefined;
    if (defTerm) {
      for (let i = g.local.length - 1; i >= 0; i--) {
        const e = g.local[i];
        if (e.tag === "Var") {
          defTerm = A.lam(e.name, elabTerm(e.type), defTerm);
        } else {
          defTerm = A.letIn(
            e.name,
            e.type ? elabTerm(e.type) : undefined,
            elabTerm(e.def),
            defTerm
          );
        }
      }
    }
    if (g.elem.tag === "Var") {
      ctx.push(A.ctxElem(g.elem.name, term));
    } else {
      ctx.push(
        A.ctxElem(
          g.elem.name,
          term,
          defTerm!
        )
      );
    }
  }
  return ctx;
}