import { type Name, type Term, sort, varia, lam, pi, pair, fst, snd, sig, letIn, app } from "./ast";
import { type Result, succ, err, isErr } from "./result";
import { type Context, ctxVar, ctxDef } from "./core";
import { type TokenizerError, type Tokenizer, type TokenType, type Token, type Position, type Range } from "./tokenize";

type ParseError =
  | { tag: "Tokenizer"; error: TokenizerError }
  | { tag: "UnexpectedToken"; expected: TokenType; actual: Token }
  | { tag: "ExpectedBinder"; token: Token }
  | { tag: "ExtraneousDef"; def: Term; range: Range }
  | { tag: "ExpectedAtom"; token: Token }
  | { tag: "ExpectedDef"; range: Range };

export type ParseNode = {
  id: number;
  label: string;
  children: ParseNode[];
  range?: Range;
  status: "enter" | "success" | "error";
  error?: ParseError;
};

export type BindersInfo = Map<Name, Range>;

type GlobalDef = {
  name: Name;
  type: Term;
  body?: {
    term: Term;
    range: Range;
  };
};

export class Parser {
  private tokenizer: Tokenizer;
  private curr!: Token;
  private prev!: Token;
  private traceStack: ParseNode[] = [];
  private root: ParseNode | null = null;
  private nextNodeId = 0;
  private binderInfos: BindersInfo = new Map();

  constructor(tokenizer: Tokenizer) {
    this.tokenizer = tokenizer;
    this.advance();
  }

  getTrace(): ParseNode | null {
    return this.root;
  }

  getAllBindersInfo(): BindersInfo {
    return this.binderInfos;
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

  private parseOpenBinder(): Result<{ names: string[]; type: Term; start: Position }, ParseError> {
    return this.withNode("parseOpenBinder", () => {
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
      return succ({ names, type: type.value, start: name.value.range.start });
    });
  }

  private parseClosedBinder(): Result<{ names: string[]; type: Term; start: Position }, ParseError> {
    return this.withNode("parseClosedBinder", () => {
      const lparen = this.expect("LPAREN");
      if (isErr(lparen))
        return lparen;
      const open_binder = this.parseOpenBinder();
      if (isErr(open_binder))
        return open_binder;
      const rparen = this.expect("RPAREN");
      if (isErr(rparen))
        return rparen;
      return succ(open_binder.value);
    });
  }

  private parseBinder(): Result<{ names: string[]; type: Term; start: Position }[], ParseError> {
    return this.withNode("parseBinder", () => {
      const t = this.curr;
      if (t.type === "IDENT") {
        const open_binder = this.parseOpenBinder();
        if (isErr(open_binder))
          return open_binder;
        return succ([open_binder.value]);
      }
      if (t.type === "LPAREN") {
        const binder = this.parseClosedBinder();
        if (isErr(binder))
          return binder;
        const binders = [binder.value];
        let cur = this.curr;
        while (cur.type === "LPAREN") {
          const b = this.parseClosedBinder();
          if (isErr(b))
            return b;
          binders.push(b.value);
          cur = this.curr;
        }
        return succ(binders);
      }
      return err({ tag: "ExpectedBinder", token: t });
    });
  }

  private parseLam(): Result<Term, ParseError> {
    return this.withNode("parseLam", () => {
      const res_fun = this.expect("RES_FUN");
      if (isErr(res_fun))
        return res_fun;
      const binder = this.parseBinder();
      if (isErr(binder))
        return binder;
      const fat_arrow = this.expect("FAT_ARROW");
      if (isErr(fat_arrow))
        return fat_arrow;
      const body = this.parseTerm();
      if (isErr(body))
        return body;
      const end = this.prev.range.end;
      for (const { names, start } of binder.value) {
        for (const name of names) {
          this.binderInfos.set(name, { start, end });
        }
      }
      return succ(binder.value.reduceRight(
        (acc, { names, type }) =>
          names.reduceRight(
            (acc2, name) => lam(name, type, acc2),
            acc
          ),
        body.value
      ));
    });
  }

  private parsePi(): Result<Term, ParseError> {
    return this.withNode("parsePi", () => {
      const res_forall = this.expect("RES_FORALL");
      if (isErr(res_forall))
        return res_forall;
      const binder = this.parseBinder();
      if (isErr(binder))
        return binder;
      const comma = this.expect("COMMA");
      if (isErr(comma))
        return comma;
      const body = this.parseTerm();
      if (isErr(body))
        return body;
      const end = this.prev.range.end;
      for (const { names, start } of binder.value) {
        for (const name of names) {
          this.binderInfos.set(name, { start, end });
        }
      }
      return succ(binder.value.reduceRight(
        (acc, { names, type }) =>
          names.reduceRight(
            (acc2, name) => pi(name, type, acc2),
            acc
          ),
        body.value
      ));
    });
  }

  private parsePair(): Result<Term, ParseError> {
    return this.withNode("parsePair", () => {
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
      let type: Term | undefined = undefined;
      if (this.curr.type === "COLON") {
        const adv = this.advance();
        if (isErr(adv))
          return adv;
        const assertion = this.parseTerm();
        if (isErr(assertion))
          return assertion;
        type = assertion.value;
      }
      return succ(pair(first.value, second.value, type));
    });
  }

  private parseSigma(): Result<Term, ParseError> {
    return this.withNode("parseSigma", () => {
      const res_exist = this.expect("RES_EXIST");
      if (isErr(res_exist))
        return res_exist;
      const binder = this.parseBinder();
      if (isErr(binder))
        return binder;
      const comma = this.expect("COMMA");
      if (isErr(comma))
        return comma;
      const body = this.parseTerm();
      if (isErr(body))
        return body;
      const end = this.prev.range.end;
      for (const { names, start } of binder.value) {
        for (const name of names) {
          this.binderInfos.set(name, { start, end });
        }
      }
      return succ(binder.value.reduceRight(
        (acc, { names, type }) =>
          names.reduceRight(
            (acc2, name) => sig(name, type, acc2),
            acc
          ),
        body.value
      ));
    });
  }

  private parseDef(): Result<GlobalDef, ParseError> {
    return this.withNode("parseDef", () => {
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
      const colon = this.expect("COLON");
      if (isErr(colon))
        return colon;
      const type = this.parseTerm();
      if (isErr(type))
        return type;
      const endPi = this.prev.range.end;
      for (const { names, start } of binders) {
        for (const name of names) {
          this.binderInfos.set(name, { start, end: endPi });
        }
      }
      const typePi = binders.reduceRight(
        (acc, { names, type }) =>
          names.reduceRight(
            (acc2, name) => pi(name, type, acc2),
            acc
          ),
        type.value
      );
      let bodyObject: { term: Term; range: Range } | undefined = undefined;
      if (this.curr.type === "ASSIGN") {
        const adv = this.advance();
        if (isErr(adv))
          return adv;
        const startLam = this.curr.range.start;
        const body = this.parseTerm();
        if (isErr(body))
          return body;
        const endLam = this.prev.range.end;
        for (const { names, start } of binders) {
          for (const name of names) {
            this.binderInfos.set(name, { start, end: endLam });
          }
        }
        const term = binders.reduceRight(
          (acc, { names, type }) =>
            names.reduceRight(
              (acc2, name) => lam(name, type, acc2),
              acc
            ),
          body.value
        );
        bodyObject = { term, range: { start: startLam, end: endLam } };
      }
      return succ({ name, type: typePi, body: bodyObject });
    });
  }

  private parseLet(): Result<Term, ParseError> {
    return this.withNode("parseLet", () => {
      const res_let = this.expect("RES_LET");
      if (isErr(res_let))
        return res_let;
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
      let typePi: Term | undefined = undefined;
      if (this.curr.type === "COLON") {
        const adv = this.advance();
        if (isErr(adv))
          return adv;
        const type = this.parseTerm();
        if (isErr(type))
          return type;
        const endPi = this.prev.range.end;
        for (const { names, start } of binders) {
          for (const name of names) {
            this.binderInfos.set(name, { start, end: endPi });
          }
        }
        typePi = binders.reduceRight(
          (acc, { names, type }) =>
            names.reduceRight(
              (acc2, name) => pi(name, type, acc2),
              acc
            ),
          type.value
        );
      }
      const assign = this.expect("ASSIGN");
      if (isErr(assign))
        return assign;
      const def = this.parseTerm();
      if (isErr(def))
        return def;
      const endLam = this.prev.range.end;
      for (const { names, start } of binders) {
        for (const name of names) {
          this.binderInfos.set(name, { start, end: endLam });
        }
      }
      const defLam = binders.reduceRight(
        (acc, { names, type }) =>
          names.reduceRight(
            (acc2, name) => lam(name, type, acc2),
            acc
          ),
        def.value
      );
      const res_in = this.expect("RES_IN");
      if (isErr(res_in))
        return res_in;
      const start = this.curr.range.start;
      const body = this.parseTerm();
      if (isErr(body))
        return body;
      const end = this.prev.range.end;
      this.binderInfos.set(name, { start, end });
      return succ(letIn(name, typePi, defLam, body.value));
    });
  }

  private parseAtom(): Result<Term, ParseError> {
    return this.withNode("parseAtom", () => {
      const t = this.curr;
      if (t.type === "LANGLE")
        return this.parsePair();
      const adv = this.advance();
      if (isErr(adv))
        return adv;
      if (t.type === "RES_PROP")
        return succ(sort("Prop"));
      if (t.type === "RES_TYPE")
        return succ(sort("Type"));
      if (t.type === "IDENT")
        return succ(varia(t.value));
      if (t.type === "LPAREN") {
        const term = this.parseTerm();
        if (isErr(term))
          return term;
        const rparen = this.expect("RPAREN");
        if (isErr(rparen))
          return rparen;
        return term;
      }
      return err({ tag: "ExpectedAtom", token: t });
    });
  }

  private parseProj(): Result<Term, ParseError> {
    return this.withNode("parseProj", () => {
      const atom = this.parseAtom();
      if (isErr(atom))
        return atom;
      let cur = atom.value;
      let token = this.curr;
      while (token.type === "DOTONE"
        || token.type === "DOTTWO") {
        if (token.type === "DOTONE")
          cur = fst(cur);
        else
          cur = snd(cur);
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

  private parseApp(): Result<Term, ParseError> {
    return this.withNode("parseApp", () => {
      const first = this.parseProj();
      if (isErr(first))
        return first;
      let cur = first.value;
      while (this.isAppStart(this.curr)) {
        const arg = this.parseProj();
        if (isErr(arg))
          return arg;
        cur = app(cur, arg.value);
      }
      return succ(cur);
    });
  }

  private parseProd(): Result<Term, ParseError> {
    return this.withNode("parseProd", () => {
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
        cur = sig("_", cur, body.value);
      }
      return succ(cur);
    });
  }

  private parseArrow(): Result<Term, ParseError> {
    return this.withNode("parseArrow", () => {
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
        return succ(pi("_", left.value, right.value));
      }
      return left;
    });
  }

  private parseTerm(): Result<Term, ParseError> {
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

  parseProgram(): Result<Context, ParseError> {
    return this.withNode("parseProgram", () => {
      const defs: Context = [];
      while (this.curr.type !== "EOF") {
        if (this.curr.type === "RES_DEF") {
          const adv = this.advance();
          if (isErr(adv))
            return adv;
          const global = this.parseDef();
          if (isErr(global))
            return global;
          const parsed = global.value;
          if (!parsed.body) {
            const t = this.prev;
            return err({ tag: "ExpectedDef", range: t.range });
          }
          defs.push(ctxDef(parsed.name, parsed.type, parsed.body.term));
        } else {
          const res_var = this.expect("RES_VAR");
          if (isErr(res_var))
            return res_var;
          const global = this.parseDef();
          if (isErr(global))
            return global;
          const parsed = global.value;
          if (parsed.body)
            return err({ tag: "ExtraneousDef", def: parsed.body.term, range: parsed.body.range });
          defs.push(ctxVar(parsed.name, parsed.type));
        }
        const semicolon = this.expect("SEMICOLON");
        if (isErr(semicolon))
          return semicolon;
      }
      return succ(defs);
    });
  }
}