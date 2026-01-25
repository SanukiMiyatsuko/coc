import { type CtxError, checkGlobalContext } from "./context";
import { type Name, type Range, type PType, type Binder, type PTerm, varBinder, Sort, Variable, Lambda, Pi, Arrow, Pair, First, Second, Sigma, Prod, Let, Apply, pVarElem, pDefElem, defBinder, type PGlobalContext, type PLocalContext, pGlobalElem, pGlobal, type VarBinder, type PGlobalElement } from "./pdef";
import { type Result, succ, err, isErr, isSucc } from "./result";
import { type TokenizerError, type Tokenizer, type TokenType, type Token } from "./tokenize";

type ParseError =
  | { tag: "Tokenizer"; error: TokenizerError }
  | { tag: "Context"; error: CtxError }
  | { tag: "UnexpectedToken"; expected: TokenType; actual: Token };

export type ParseNode = {
  id: number;
  label: string;
  children: ParseNode[];
  range?: Range;
  status: "enter" | "success" | "error";
  error?: ParseError;
};

export class Parser {
  private tokenizer: Tokenizer;
  private curr!: Token;
  private prev!: Token;
  private traceStack: ParseNode[] = [];
  private root: ParseNode | null = null;
  private nextNodeId = 0;

  constructor(tokenizer: Tokenizer) {
    this.tokenizer = tokenizer;
    this.advance();
  }

  getTrace(): ParseNode | null {
    return this.root;
  }

  private advance(): Result<void, ParseError> {
    const res = this.tokenizer.next();
    if (isErr(res)) {
      return err({ tag: "Tokenizer", error: res.err });
    }
    this.prev = this.curr;
    this.curr = res.value;
    return succ(undefined);
  }

  private withNode<T>(
    label: string,
    fn: () => Result<T, ParseError>
  ): Result<T, ParseError> {
    const startToken = this.curr;
    const node: ParseNode = {
      id: this.nextNodeId++,
      label,
      children: [],
      status: "enter",
    };
    if (this.traceStack.length === 0) {
      this.root = node;
    } else {
      this.traceStack[this.traceStack.length - 1].children.push(node);
    }
    this.traceStack.push(node);
    const result = fn();
    this.traceStack.pop();
    const maybeEndToken = this.prev ?? startToken;
    node.range = {
      start: startToken.range.start,
      end: maybeEndToken.range.end,
    };
    if (isErr(result)) {
      node.status = "error";
      node.error = result.err;
      return result;
    }
    node.status = "success";
    return result;
  }

  private expect(type: TokenType): Result<Token, ParseError> {
    const t = this.curr;
    if (t.type !== type)
      return err({
        tag: "UnexpectedToken",
        expected: type,
        actual: t,
      });
    const adv = this.advance();
    if (isErr(adv))
      return adv;
    return succ(t);
  }

  private parseOpenBinder(): Result<VarBinder, ParseError> {
    return this.withNode("parseOpenBinder", () => {
      const start = this.curr.range.start;
      const name = this.expect("IDENT");
      if (isErr(name))
        return name;
      const names = [name.value.value];
      let cur = this.curr;
      while (cur.type === "IDENT") {
        names.push(cur.value);
        const adv = this.advance();
        if (isErr(adv))
          return adv;
        cur = this.curr;
      }
      const colon = this.expect("COLON");
      if (isErr(colon))
        return colon;
      const type = this.parseTerm();
      if (isErr(type))
        return type;
      const end = this.prev.range.end;
      return succ(varBinder(names, type.value, { start, end }));
    });
  }

  private parseVariableBinder(): Result<VarBinder, ParseError> {
    return this.withNode("parseVariableBinder", () => {
      const start = this.curr.range.start;
      const lparen = this.expect("LPAREN");
      if (isErr(lparen))
        return lparen;
      const open_binder = this.parseOpenBinder();
      if (isErr(open_binder))
        return open_binder;
      const { names, type } = open_binder.value;
      const rparen = this.expect("RPAREN");
      if (isErr(rparen))
        return rparen;
      const end = this.prev.range.end;
      return succ(varBinder(names, type, { start, end }));
    });
  }

  private parseClosedBinder(): Result<Binder, ParseError> {
    return this.withNode("parseClosedBinder", () => {
      const start = this.curr.range.start;
      const lparen = this.expect("LPAREN");
      if (isErr(lparen))
        return lparen;
      const ident = this.expect("IDENT");
      if (isErr(ident))
        return ident;
      const name = ident.value.value;
      let cur = this.curr;
      if (cur.type === "IDENT") {
        const names = [name];
        while (cur.type === "IDENT") {
          names.push(cur.value);
          const adv = this.advance();
          if (isErr(adv))
            return adv;
          cur = this.curr;
        }
        const colon = this.expect("COLON");
        if (isErr(colon))
          return colon;
        const type = this.parseTerm();
        if (isErr(type))
          return type;
        const rparen = this.expect("RPAREN");
        if (isErr(rparen))
          return rparen;
        const end = this.prev.range.end;
        return succ(varBinder(names, type.value, { start, end }) as Binder);
      }
      if (isSucc(this.expect("ASSIGN"))) {
        const def = this.parseTerm();
        if (isErr(def))
          return def;
        const rparen = this.expect("RPAREN");
        if (isErr(rparen))
          return rparen;
        const end = this.prev.range.end;
        return succ(defBinder(name, undefined, def.value, { start, end }) as Binder);
      }
      const colon = this.expect("COLON");
      if (isErr(colon))
        return colon;
      const type = this.parseTerm();
      if (isErr(type))
        return type;
      if (isSucc(this.expect("RPAREN"))) {
        const end = this.prev.range.end;
        return succ(varBinder([name], type.value, { start, end }) as Binder);
      }
      const assign = this.expect("ASSIGN");
      if (isErr(assign))
        return assign;
      const def = this.parseTerm();
      if (isErr(def))
        return def;
      const rparen = this.expect("RPAREN");
      if (isErr(rparen))
        return rparen;
      const end = this.prev.range.end;
      return succ(defBinder(name, type.value, def.value, { start, end }) as Binder);
    });
  }

  private parseBinder(): Result<Binder[], ParseError> {
    return this.withNode("parseBinder", () => {
      const t = this.curr;
      if (t.type === "IDENT") {
        const open_binder = this.parseOpenBinder();
        if (isErr(open_binder))
          return open_binder;
        return succ([open_binder.value]);
      }
      const binder = this.parseVariableBinder();
      if (isErr(binder))
        return binder;
      const binders: Binder[] = [binder.value];
      let cur = this.curr;
      while (cur.type === "LPAREN") {
        const b = this.parseClosedBinder();
        if (isErr(b))
          return b;
        binders.push(b.value);
        cur = this.curr;
      }
      return succ(binders);
    });
  }

  private parseLam(): Result<PTerm, ParseError> {
    return this.withNode("parseLam", () => {
      const start = this.curr.range.start;
      const res_fun = this.expect("RES_FUN");
      if (isErr(res_fun))
        return res_fun;
      const binders = this.parseBinder();
      if (isErr(binders))
        return binders;
      const fat_arrow = this.expect("FAT_ARROW");
      if (isErr(fat_arrow))
        return fat_arrow;
      const body = this.parseTerm();
      if (isErr(body))
        return body;
      const end = this.prev.range.end;
      return succ(Lambda(binders.value, body.value, { start, end }));
    });
  }

  private parsePi(): Result<PTerm, ParseError> {
    return this.withNode("parsePi", () => {
      const start = this.curr.range.start;
      const res_forall = this.expect("RES_FORALL");
      if (isErr(res_forall))
        return res_forall;
      const binders = this.parseBinder();
      if (isErr(binders))
        return binders;
      const comma = this.expect("COMMA");
      if (isErr(comma))
        return comma;
      const body = this.parseTerm();
      if (isErr(body))
        return body;
      const end = this.prev.range.end;
      return succ(Pi(binders.value, body.value, { start, end }));
    });
  }

  private parsePair(): Result<PTerm, ParseError> {
    return this.withNode("parsePair", () => {
      const start = this.curr.range.start;
      const langle = this.expect("LANGLE");
      if (isErr(langle))
        return langle;
      const first = this.parseTerm();
      if (isErr(first))
        return first;
      const comma = this.expect("COMMA");
      if (isErr(comma))
        return comma;
      const second = this.parseTerm();
      if (isErr(second))
        return second;
      const rangle = this.expect("RANGLE");
      if (isErr(rangle))
        return rangle;
      let type: PType | undefined = undefined;
      if (this.curr.type === "COLON") {
        const adv = this.advance();
        if (isErr(adv))
          return adv;
        const assertion = this.parseTerm();
        if (isErr(assertion))
          return assertion;
        type = assertion.value;
      }
      const end = this.prev.range.end;
      return succ(Pair(first.value, second.value, type, { start, end }));
    });
  }

  private parseSigma(): Result<PTerm, ParseError> {
    return this.withNode("parseSigma", () => {
      const start = this.curr.range.start;
      const res_exist = this.expect("RES_EXIST");
      if (isErr(res_exist))
        return res_exist;
      const binders = this.parseBinder();
      if (isErr(binders))
        return binders;
      const comma = this.expect("COMMA");
      if (isErr(comma))
        return comma;
      const body = this.parseTerm();
      if (isErr(body))
        return body;
      const end = this.prev.range.end;
      return succ(Sigma(binders.value, body.value, { start, end }));
    });
  }

  private parseToEndOfBinder(): Result<{ name: Name; binders: Binder[] }, ParseError> {
    return this.withNode("parseToEndOfBinder", () => {
      const ident = this.expect("IDENT");
      if (isErr(ident))
        return ident;
      const name = ident.value.value;
      const binders = [];
      let cur = this.curr;
      while (cur.type === "LPAREN") {
        const b = this.parseClosedBinder();
        if (isErr(b))
          return b;
        binders.push(b.value);
        cur = this.curr;
      }
      return succ({ name, binders });
    });
  }

  private parseLet(): Result<PTerm, ParseError> {
    return this.withNode("parseLet", () => {
      const start = this.curr.range.start;
      const res_let = this.expect("RES_LET");
      if (isErr(res_let))
        return res_let;
      const nameBinders = this.parseToEndOfBinder();
      if (isErr(nameBinders))
        return nameBinders;
      const { name, binders } = nameBinders.value;
      let type: PTerm | undefined = undefined;
      if (this.curr.type === "COLON") {
        const adv = this.advance();
        if (isErr(adv))
          return adv;
        const resulttype = this.parseTerm();
        if (isErr(resulttype))
          return resulttype;
        type = resulttype.value;
      }
      const assign = this.expect("ASSIGN");
      if (isErr(assign))
        return assign;
      const def = this.parseTerm();
      if (isErr(def))
        return def;
      const res_in = this.expect("RES_IN");
      if (isErr(res_in))
        return res_in;
      const body = this.parseTerm();
      if (isErr(body))
        return body;
      const end = this.prev.range.end;
      return succ(Let(name, binders, type, def.value, body.value, { start, end }));
    });
  }

  private parseAtom(): Result<PTerm, ParseError> {
    return this.withNode("parseAtom", () => {
      const t = this.curr;
      if (t.type === "LANGLE")
        return this.parsePair();
      if (isSucc(this.expect("RES_PROP")))
        return succ(Sort("Prop", t.range));
      if (isSucc(this.expect("RES_TYPE")))
        return succ(Sort("Type", t.range));
      if (isSucc(this.expect("IDENT")))
        return succ(Variable(t.value, t.range));
      const lparen = this.expect("LPAREN");
      if (isErr(lparen))
        return lparen;
      const term = this.parseTerm();
      if (isErr(term))
        return term;
      const rparen = this.expect("RPAREN");
      if (isErr(rparen))
        return rparen;
      return term;
    });
  }

  private parseProj(): Result<PTerm, ParseError> {
    return this.withNode("parseProj", () => {
      const start = this.curr.range.start;
      const atom = this.parseAtom();
      if (isErr(atom))
        return atom;
      let cur = atom.value;
      let token = this.curr;
      while (token.type === "DOTONE"
        || token.type === "DOTTWO") {
        if (token.type === "DOTONE")
          cur = First(cur, { start, end: token.range.end });
        else
          cur = Second(cur, { start, end: token.range.end });
        const adv = this.advance();
        if (isErr(adv))
          return adv;
        token = this.curr;
      }
      return succ(cur);
    });
  }

  private isAppStart(token: Token): boolean {
    return token.type === "RES_PROP"
      || token.type === "RES_TYPE"
      || token.type === "IDENT"
      || token.type === "LPAREN"
      || token.type === "LANGLE";
  }

  private parseApp(): Result<PTerm, ParseError> {
    return this.withNode("parseApp", () => {
      const start = this.curr.range.start;
      const first = this.parseProj();
      if (isErr(first))
        return first;
      const cur = [first.value];
      while (this.isAppStart(this.curr)) {
        const arg = this.parseProj();
        if (isErr(arg))
          return arg;
        cur.push(arg.value);
      }
      const end = this.prev.range.end;
      if (cur.length === 1)
        return succ(first.value);
      return succ(Apply(cur, { start, end }));
    });
  }

  private parseProd(): Result<PTerm, ParseError> {
    return this.withNode("parseProd", () => {
      const start = this.curr.range.start;
      const first = this.parseApp();
      if (isErr(first))
        return first;
      let cur = first.value;
      while (this.curr.type === "AND") {
        const adv = this.advance();
        if (isErr(adv))
          return adv;
        const body = this.parseApp();
        if (isErr(body))
          return body;
        const end = this.prev.range.end;
        cur = Prod(cur, body.value, { start, end });
      }
      return succ(cur);
    });
  }

  private parseArrow(): Result<PTerm, ParseError> {
    return this.withNode("parseArrow", () => {
      const start = this.curr.range.start;
      const left = this.parseProd();
      if (isErr(left))
        return left;
      if (this.curr.type === "ARROW") {
        const adv = this.advance();
        if (isErr(adv))
          return adv;
        const right = this.parseTerm();
        if (isErr(right))
          return right;
        const end = this.prev.range.end;
        return succ(Arrow(left.value, right.value, { start, end }));
      }
      return left;
    });
  }

  private parseTerm(): Result<PTerm, ParseError> {
    return this.withNode("parseTerm", () => {
      const t = this.curr;
      if (t.type === "RES_FUN")
        return this.parseLam();
      if (t.type === "RES_FORALL")
        return this.parsePi();
      if (t.type === "RES_EXIST")
        return this.parseSigma();
      if (t.type === "RES_LET")
        return this.parseLet();
      return this.parseArrow();
    });
  }

  private parseDef(): Result<{ elem: PGlobalElement, binders: Binder[] }, ParseError> {
    return this.withNode("parseDef", () => {
      const start = this.curr.range.start;
      if (isSucc(this.expect("RES_DEF"))) {
        const nameBinders = this.parseToEndOfBinder();
        if (isErr(nameBinders))
          return nameBinders;
        const name = nameBinders.value.name;
        const binders = nameBinders.value.binders;
        const colon = this.expect("COLON");
        if (isErr(colon))
          return colon;
        const type = this.parseTerm();
        if (isErr(type))
          return type;
        const assign = this.expect("ASSIGN");
        if (isErr(assign))
          return assign;
        const def = this.parseTerm();
        if (isErr(def))
          return def;
        const semicolon = this.expect("SEMICOLON");
        if (isErr(semicolon))
          return semicolon;
        const end = this.prev.range.end;
        const elem = pGlobalElem(name, type.value, def.value, { start, end });
        return succ({ elem, binders });
      }
      const nameBinders = this.parseToEndOfBinder();
      if (isErr(nameBinders))
        return nameBinders;
      const name = nameBinders.value.name;
      const binders = nameBinders.value.binders;
      const colon = this.expect("COLON");
      if (isErr(colon))
        return colon;
      const type = this.parseTerm();
      if (isErr(type))
        return type;
      const semicolon = this.expect("SEMICOLON");
      if (isErr(semicolon))
        return semicolon;
      const end = this.prev.range.end;
      const elem = pGlobalElem(name, type.value, undefined, { start, end });
      return succ({ elem, binders });
    });
  }

  parseProgram(): Result<PGlobalContext, ParseError> {
    return this.withNode("parseProgram", () => {
      const defs: PGlobalContext = [];
      while (this.curr.type !== "EOF") {
        const def = this.parseDef();
        if (isErr(def))
          return def;
        const local: PLocalContext = [];
        for (const e of def.value.binders) {
          if (e.tag === "Var")
            for (const n of e.names) {
              local.push(pVarElem(n, e.type, e.range));
            }
          if (e.tag === "Def")
            local.push(pDefElem(e.name, e.type, e.def, e.range));
        }
        const global = pGlobal(def.value.elem, local);
        defs.push(global);
      }
      const cj = checkGlobalContext(defs);
      if (isErr(cj))
        return err({ tag: "Context", error: cj.err });
      return succ(defs);
    });
  }
}