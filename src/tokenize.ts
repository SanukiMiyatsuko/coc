import { type Position, type Range } from "./pdef";
import { type Result, succ, err, isErr } from "./result";

export type TokenizerError =
  | { tag: "UnexpectedChar"; char: string; pos: Position }
  | { tag: "UnclosedComment"; pos: Position };

export type TokenType =
  | "BLANKS"
  | "COMMENT"
  | "RES_DEF"
  | "RES_VAR"
  | "RES_PROP"
  | "RES_TYPE"
  | "RES_FUN"
  | "RES_FORALL"
  | "RES_EXIST"
  | "RES_LET"
  | "RES_IN"
  | "FAT_ARROW"
  | "ARROW"
  | "ASSIGN"
  | "LPAREN"
  | "RPAREN"
  | "COLON"
  | "COMMA"
  | "LANGLE"
  | "RANGLE"
  | "DOTONE"
  | "DOTTWO"
  | "AND"
  | "SEMICOLON"
  | "IDENT"
  | "EOF"

export type Token = {
  type: TokenType;
  value: string;
  range: Range;
};

type Pattern = { type: TokenType; re: RegExp };

const patterns: Pattern[] = [
  { type: "BLANKS", re: /^\s+/ },
  { type: "COMMENT", re: /^--[^\n]*(?:\n|$)/ },
  { type: "RES_DEF", re: /^(def)(?![\w'])/ },
  { type: "RES_VAR", re: /^(var)(?![\w'])/ },
  { type: "RES_PROP", re: /^(Prop)(?![\w'])/ },
  { type: "RES_TYPE", re: /^(Type)(?![\w'])/ },
  { type: "RES_FUN", re: /^(fun)(?![\w'])/ },
  { type: "RES_FORALL", re: /^(forall)(?![\w'])/ },
  { type: "RES_EXIST", re: /^(exist)(?![\w'])/ },
  { type: "RES_LET", re: /^(let)(?![\w'])/ },
  { type: "RES_IN", re: /^(in)(?![\w'])/ },
  { type: "FAT_ARROW", re: /^=>/ },
  { type: "ARROW", re: /^->/ },
  { type: "ASSIGN", re: /^:=/ },
  { type: "LPAREN", re: /^\(/ },
  { type: "RPAREN", re: /^\)/ },
  { type: "COLON", re: /^:/ },
  { type: "COMMA", re: /^,/ },
  { type: "LANGLE", re: /^</ },
  { type: "RANGLE", re: /^>/ },
  { type: "DOTONE", re: /^\.1/ },
  { type: "DOTTWO", re: /^\.2/ },
  { type: "AND", re: /^&/ },
  { type: "SEMICOLON", re: /^;/ },
  { type: "IDENT", re: /^[A-Za-z_][\w']*/ },
];

export class Tokenizer {
  private src: string;
  private pos = 0;
  private line = 0;
  private character = 0;

  constructor(src: string) {
    this.src = src.replace(/\r\n|\r/g, "\n");
  }

  private eof(): boolean {
    return this.pos >= this.src.length;
  }

  private advance(text: string) {
    for (const ch of text) {
      if (ch === "\n") {
        this.line++;
        this.character = 0;
      } else {
        this.character++;
      }
    }
    this.pos += text.length;
  }

  private currentPosition(): Position {
    return { line: this.line, character: this.character };
  }

  next(): Result<Token, TokenizerError> {
    if (this.eof()) {
      const p = this.currentPosition();
      return succ({
        type: "EOF",
        value: "",
        range: { start: p, end: p },
      });
    }
    const rest = this.src.slice(this.pos);
    if (rest.startsWith("{-")) {
      const close_index = rest.indexOf("-}", 2);
      if (close_index === -1)
        return err({
          tag: "UnclosedComment",
          pos: this.currentPosition(),
        });
      const value = rest.slice(0, close_index + 2);
      this.advance(value);
      return this.next();
    }
    const start = this.currentPosition();
    for (const { type, re } of patterns) {
      const m = re.exec(rest);
      if (!m)
        continue;
      const value = m[0];
      this.advance(value);
      if (type === "BLANKS" || type === "COMMENT")
        return this.next();
      const end = this.currentPosition();
      return succ({
        type,
        value,
        range: { start, end },
      });
    }
    return err({
      tag: "UnexpectedChar",
      char: this.src[this.pos],
      pos: this.currentPosition(),
    });
  }
}

export function tokenizeAll(src: string): Token[] {
  const t = new Tokenizer(src);
  const tokens: Token[] = [];
  while (true) {
    const r = t.next();
    if (isErr(r))
      break;
    tokens.push(r.value);
    if (r.value.type === "EOF")
      break;
  }
  return tokens;
}