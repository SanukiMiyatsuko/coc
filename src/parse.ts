import { type Term, sort, varia, lam, pi, letIn, app } from "./ast";
import { type Result, succ, err, isErr } from "./result";
import { type Context, ctxVar, ctxDef } from "./core";
import { type TokenType, type Token, type Range } from "./tokenize";

type ParseError =
  | { tag: "UnexpectedToken"; expected: TokenType; actual: Token }
  | { tag: "ExpectedBinder"; token: Token }
  | { tag: "ExpectedAtom"; token: Token }
  | { tag: "ExtraneousDef"; def: Term; range: Range }
  | { tag: "ExpectedDef"; range: Range };

export type ParseNode = {
  id: number;
  label: string;
  children: ParseNode[];
  range?: Range;
  status: "enter" | "success" | "error";
  error?: ParseError;
};

type GlobalDef = {
  name: string;
  type: Term;
  body?: {
    term: Term;
    range: Range;
  };
};

export class Parser {
  private tokens: Token[];
  private tokenPos = 0;
  private traceStack: ParseNode[] = [];
  private root: ParseNode | null = null;
  private nextNodeId = 0;

  constructor(tokens: Token[]) {
    this.tokens = tokens;
  }

  getTrace(): ParseNode | null {
    return this.root;
  }

  private peek(): Token {
    return this.tokens[this.tokenPos];
  }

  private withNode<T>(
    label: string,
    fn: () => Result<T, ParseError>
  ): Result<T, ParseError> {
    const startToken = this.peek();
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
  
    if (isErr(result)) {
      node.status = "error";
      node.error = result.err;
      return result;
    }
  
    const endToken = this.tokens[this.tokenPos - 1] ?? startToken;
    node.status = "success";
    node.range = {
      start: startToken.range.start,
      end: endToken.range.end,
    };
    return result;
  }

  private expect(type: TokenType): Result<Token, ParseError> {
    const t = this.peek();
    if (t.type !== type)
      return err({
        tag: "UnexpectedToken",
        expected: type,
        actual: t,
      });
    this.tokenPos += 1;
    return succ(t);
  }

  private consume(token: Token, type: TokenType): boolean {
    if (token.type !== type)
      return false;
    this.tokenPos += 1;
    return true;
  }

  private parseOpenBinder(): Result<{ names: string[]; type: Term }, ParseError> {
    return this.withNode("parseOpenBinder", () => {
      const name = this.expect("IDENT");
      if (isErr(name))
        return name;
      const names = [name.value.value];
      let cur = this.peek();
      while (this.consume(cur, "IDENT")) {
        names.push(cur.value);
        cur = this.peek();
      }
      const colon = this.expect("COLON");
      if (isErr(colon))
        return colon;
      const type = this.parseTerm();
      if (isErr(type))
        return type;
      return succ({ names, type: type.value });
    });
  }

  private parseClosedBinder(): Result<{ names: string[]; type: Term }, ParseError> {
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

  private parseBinder(): Result<{ names: string[]; type: Term }[], ParseError> {
    return this.withNode("parseBinder", () => {
      const t = this.peek();
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
        let cur = this.peek();
        while (cur.type === "LPAREN") {
          const b = this.parseClosedBinder();
          if (isErr(b))
            return b;
          binders.push(b.value);
          cur = this.peek();
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

  parseDef(): Result<GlobalDef, ParseError> {
    return this.withNode("parseDef", () => {
      const ident = this.expect("IDENT");
      if (isErr(ident))
        return ident;
      const name = ident.value.value;
      const binders = [];
      let cur = this.peek();
      while (cur.type === "LPAREN") {
        const b = this.parseClosedBinder();
        if (isErr(b))
          return b;
        binders.push(b.value);
        cur = this.peek();
      }
      this.expect("COLON");
      const type = this.parseTerm();
      if (isErr(type))
        return type;
      const typePi = binders.reduceRight(
        (acc, { names, type }) =>
          names.reduceRight(
            (acc2, name) => pi(name, type, acc2),
            acc
          ),
        type.value
      );
      const t = this.peek();
      let bodyObject = undefined;
      if (this.consume(t, "ASSIGN")) {
        const start = t.range.start;
        const body = this.parseTerm();
        if (isErr(body))
          return body;
        const end = this.peek().range.end;
        const term = binders.reduceRight(
          (acc, { names, type }) =>
            names.reduceRight(
              (acc2, name) => lam(name, type, acc2),
              acc
            ),
          body.value
        );
        bodyObject = { term, range: { start, end } };
      }
      return succ({ name, type: typePi, body: bodyObject });
    });
  }

  private parseLet(): Result<Term, ParseError> {
    return this.withNode("parseLet", () => {
      const res_let = this.expect("RES_LET");
      if (isErr(res_let))
        return res_let;
      const def = this.parseDef();
      if (isErr(def))
        return def;
      const parsed = def.value;
      if (!parsed.body) {
        const t = this.tokens[this.tokenPos - 1] ?? this.peek();
        return err({ tag: "ExpectedDef", range: t.range });
      }
      const res_in = this.expect("RES_IN");
      if (isErr(res_in))
        return res_in;
      const body = this.parseTerm();
      if (isErr(body))
        return body;
      return succ(letIn(parsed.name, parsed.type, parsed.body.term, body.value));
    });
  }

  private parseAtom(): Result<Term, ParseError> {
    return this.withNode("parseAtom", () => {
      const t = this.peek();
      if (this.consume(t, "RES_PROP"))
        return succ(sort("Prop"));
      if (this.consume(t, "RES_TYPE"))
        return succ(sort("Type"));
      if (this.consume(t, "IDENT"))
        return succ(varia(t.value));
      if (this.consume(t, "LPAREN")) {
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

  private isAppStart(token: Token): boolean {
    return token.type === "RES_PROP"
      || token.type === "RES_TYPE"
      || token.type === "LPAREN"
      || token.type === "IDENT";
  }

  private parseApp(): Result<Term, ParseError> {
    return this.withNode("parseApp", () => {
      const atom = this.parseAtom();
      if (isErr(atom))
        return atom;
      let cur = atom.value;
      while (this.isAppStart(this.peek())) {
        const arg = this.parseAtom();
        if (isErr(arg))
          return arg;
        cur = app(cur, arg.value);
      }
      return succ(cur);
    });
  }

  private parseArrow(): Result<Term, ParseError> {
    return this.withNode("parseArrow", () => {
      const left = this.parseApp();
      if (isErr(left))
        return left;
      if (this.consume(this.peek(), "ARROW")) {
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
      const t = this.peek();
      if (t.type === "RES_FUN") {
        return this.parseLam();
      }
      if (t.type === "RES_FORALL") {
        return this.parsePi();
      }
      if (t.type === "RES_LET") {
        return this.parseLet();
      }
      return this.parseArrow();
    });
  }

  parseProgram(): Result<Context, ParseError> {
    return this.withNode("parseProgram", () => {
      const defs: Context = [];
      while (this.peek().type !== "EOF") {
        if (this.consume(this.peek(), "RES_DEF")) {
          const global = this.parseDef();
          if (isErr(global))
            return global;
          const parsed = global.value;
          if (!parsed.body) {
            const t = this.tokens[this.tokenPos - 1] ?? this.peek();
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