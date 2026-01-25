import { useState, useEffect, useTransition, useRef } from "react";
import { CustomLanguageEditor } from "./editor"
import "./app.css";
import { type PGlobalContext } from "./pdef";
import { err, isErr, succ, type Result } from "./result";
import { type TokenType, Tokenizer } from "./tokenize";
import { Parser } from "./parse";
import { type Term, type CtxElement, judgCtx } from "./ast";
import { wellFormed } from "./typecheck";
import { elabGlobalContext } from "./trans";

type Phase = "tokenize" | "parse" | "context" | "typecheck";

type UIError = {
  phase: Phase;
  title: string;
  message: string;
  detail?: unknown;
};

function renderError(err: UIError) {
  const message =
    typeof err.message === "string"
      ? err.message
      : JSON.stringify(err.message, null, 2);
  return (
    <div className="error">
      <div className="error-title">
        [{err.phase.toUpperCase()}] {err.title}
      </div>
      <div className="error-message">{message}</div>
      {err.detail !== undefined && (
        <details>
          <summary>詳細</summary>
          <pre>
            {(() => {
              try {
                return JSON.stringify(err.detail, null, 2);
              } catch {
                return String(err.detail);
              }
            })()}
          </pre>
        </details>
      )}
    </div>
  );
}

function tokenDesc(t: TokenType): string {
  switch (t) {
    case "RES_DEF":
      return "def";
    case "RES_VAR":
      return "var";
    case "RES_PROP":
      return "Prop";
    case "RES_TYPE":
      return "Type";
    case "RES_FUN":
      return "fun";
    case "RES_FORALL":
      return "forall";
    case "RES_EXIST":
      return "exist";
    case "RES_LET":
      return "let";
    case "RES_IN":
      return "in";
    case "FAT_ARROW":
      return "=>";
    case "ARROW":
      return "->";
    case "ASSIGN":
      return ":=";
    case "LPAREN":
      return "(";
    case "RPAREN":
      return ")";
    case "COLON":
      return ":";
    case "COMMA":
      return ",";
    case "LANGLE":
      return "<";
    case "RANGLE":
      return ">";
    case "DOTONE":
      return ".1";
    case "DOTTWO":
      return ".2";
    case "AND":
      return "&";
    case "SEMICOLON":
      return ";";
    case "IDENT":
      return "識別子";
    default:
      return "";
  }
}

function showTerm(t: Term): string {
  switch (t.tag) {
    case "Sort":
      return t.name;
    case "Var":
      return t.name;
    case "Lam":
      return `(fun (${t.name} : ${showTerm(t.type)}) => ${showTerm(t.body)})`;
    case "Pi":
      return `(forall (${t.name} : ${showTerm(t.type)}), ${showTerm(t.body)})`;
    case "Pair":
      return `<${showTerm(t.fst)}, ${showTerm(t.snd)}>${t.as ? ` : ${showTerm(t.as)}` : ``}`;
    case "Fst":
      return `${showTerm(t.pair)}.1`;
    case "Snd":
      return `${showTerm(t.pair)}.2`;
    case "Sig":
      return `(exist (${t.name} : ${showTerm(t.type)}), ${showTerm(t.body)})`;
    case "Let":
      return `(let ${t.name}${t.type ? ` : ${showTerm(t.type)}` : ``} := ${showTerm(t.def)} in ${showTerm(t.body)})`;
    case "App":
      return `(${showTerm(t.fun)} ${showTerm(t.arg)})`;
  }
}

function showCtxElement(e: CtxElement): string {
  if (e.tag === "Def")
    return `def ${e.name} : ${showTerm(e.type)} := ${showTerm(e.def)}`;
  else
    return `var ${e.name} : ${showTerm(e.type)}`;
}

const init =
`def Nat: Prop := forall A: Prop, (A -> A) -> A -> A;

def zero: Nat :=
  fun (A: Prop) (f: A -> A) (x: A) => x;

def succ : Nat -> Nat :=
  fun (n : Nat) (A : Prop) (f : A -> A) (x : A) => f (n A f x);

def iter : Nat -> forall (A : Prop), (A -> A) -> A -> A :=
  fun (n : Nat) (A : Prop) (f : A -> A) (x : A) => n A f x;

def rec : Nat -> forall (A: Prop), A -> (Nat -> A -> A) -> A :=
  fun (n : Nat)
    (A : Prop)
    (a : A)
    (s : Nat -> A -> A) =>
      let step (p : Nat & A) :=
        <succ p.1, s p.1 p.2>
      in (n (Nat & A) step <zero, a>).2;


def Bool: Prop := forall (A: Prop), A -> A -> A;

def true: Bool := fun (A: Prop) (x y: A) => x;

def false: Bool := fun (A: Prop) (x y: A) => y;

def or: Bool -> Bool -> Bool :=
  fun a b: Bool => a Bool true b;

def and: Bool -> Bool -> Bool :=
  fun a b: Bool => a Bool b false;

def not: Bool -> Bool :=
  fun a: Bool => a Bool false true;


def List (A: Prop): Prop :=
  forall L: Prop, L -> (A -> L -> L) -> L;

def nil (A: Prop): List A :=
  fun (L: Prop) (x: L) (f: A -> L -> L) => x;

def cons (A: Prop): A -> List A -> List A :=
  fun (a: A)
    (s: List A)
    (L: Prop)
    (x: L)
    (f: A -> L -> L) =>
      f a (s L x f);


def Vec (A: Prop) (n: Nat): Prop :=
  forall V: Nat -> Prop,
    V zero -> (forall m: Nat, A -> V m -> V (succ m)) -> V n;

def nilv (A: Prop): Vec A zero :=
  fun (V: Nat -> Prop)
    (x: V zero)
    (f: forall m: Nat, A -> V m -> V (succ m))
      => x;

def consv (A: Prop) (n: Nat): A -> Vec A n -> Vec A (succ n) :=
  fun (a: A)
    (s: Vec A n)
    (V: Nat -> Prop)
    (x: V zero)
    (f: forall m: Nat, A -> V m -> V (succ m))
      => f n a (s V x f);


def and_intro (A B C: Prop) (im_a: C -> A) (im_b: C -> B): C -> A & B :=
  fun c: C => <im_a c, im_b c>;


def Union (A B: Prop): Prop :=
  forall C: Prop, (A -> C) -> (B -> C) -> C;

def in_l (A B: Prop): A -> Union A B :=
  fun (a: A) (C: Prop) (im_a: A -> C) (im_b: B -> C) => im_a a;

def in_r (A B: Prop): B -> Union A B :=
  fun (b: B) (C: Prop) (im_a: A -> C) (im_b: B -> C) => im_b b;

def or_elim (A B C: Prop) (im_a: A -> C) (im_b: B -> C): Union A B -> C :=
  fun union: Union A B => union C im_a im_b;


def Truth: Prop := forall A: Prop, A -> A;

def id (A : Prop) (x : A) : A := x;


def Contra: Prop := forall (A: Prop), A;

def Not (A: Prop): Prop := A -> Contra;

def Not_elim: forall A: Prop, Contra -> A :=
  fun (A: Prop) (co: Contra) => co A;


def EM: Prop := forall A: Prop, Union A (Not A);

def DNE: Prop := forall A: Prop, Not (Not A) -> A;

def EM_to_DNE: EM -> DNE :=
  fun (em: EM)
    (A: Prop)
    (nna: Not (Not A)) =>
      or_elim A (Not A) A (id A) (fun na: Not A => Not_elim A (nna na)) (em A);

def DNE_to_EM: DNE -> EM :=
  fun (dne: DNE) (A: Prop) =>
    let nnEM (p: Not (Union A (Not A))) :=
      let na := fun a: A => p (in_l A (Not A) a)
      in p (in_r A (Not A) na)
    in dne (Union A (Not A)) nnEM;


def Eq (A: Prop) (a b: A): Prop := forall P: A -> Prop, P a -> P b;

def ref (A: Prop) (a: A): Eq A a a := fun P: A -> Prop => id (P a);

def symm (A: Prop) (a b: A): Eq A a b -> Eq A b a :=
  fun (eqab: Eq A a b) (P: A -> Prop) =>
    let q := eqab (fun x : A => P x -> P a)
    in q (id (P a));

def trans (A: Prop) (a b c: A) : Eq A a b -> Eq A b c -> Eq A a c :=
  fun (eqab: Eq A a b)
    (eqbc: Eq A b c)
    (P: A -> Prop)
    (pa: P a) =>
      eqbc P (eqab P pa);


def funEq (A B: Prop) (f g: A -> B): Prop :=
  forall a: A, Eq B (f a) (g a);

def FunEq (A B: Prop) (f g: A -> B): Prop :=
  Eq (A -> B) f g;

def F_to_f (A B: Prop) (f g: A -> B): FunEq A B f g -> funEq A B f g :=
  fun (F: FunEq A B f g)
    (a: A)
    (R: B -> Prop) =>
      F (fun h: A -> B => R (h a));`

export default function App() {
  const [source, setSource] = useState(init);
  const [error, setError] = useState<UIError | null>(null);
  const [success, setSuccess] = useState<string>("");
  const [successDefs, setSuccessDefs] = useState<string[]>([]);
  const [pGlobalContext, setPGlobalContext] = useState<PGlobalContext>([]);
  const [isPending, startTransition] = useTransition();
  const runIdRef = useRef(0);

  const fail = (e: UIError) => {
    setSuccess("");
    setError(e);
  };

  const runUntilContext = (code: string): Result<true, UIError> => {
    setPGlobalContext([]);
    const tokenizer = new Tokenizer(code);
    const parser = new Parser(tokenizer);
    const ctxR = parser.parseProgram();
    if (isErr(ctxR)) {
      let msg: string;
      switch (ctxR.err.tag) {
        case "Tokenizer":
          return err({
            phase: "tokenize",
            title: "字句解析エラー",
            message:
              ctxR.err.error.tag === "UnexpectedChar"
                ? `不正な文字 ${ctxR.err.error.char} を検出しました。`
                : "コメントが閉じられていません。",
            detail: ctxR.err.error,
          });
        case "Context": {
          const e = ctxR.err.error;
          let msg = "";
          switch (e.tag) {
            case "DuplicateGlobal":
              msg = `グローバル定義 ${e.name} が重複しています。`;
              break;
            case "DuplicateLocal":
              msg = `ローカル定義 ${e.name} が重複しています。`;
              break;
            case "SelfReference":
              msg = `${e.kind} にて自分の名前 ${e.name} を参照しています。`;
              break;
            case "Undefined":
              msg = `定義 ${e.in} の中で未定義の名前 ${e.name} (${e.kind}) が使われています。`;
              break;
            case "Cycle":
              msg = "定義に循環依存があります:\n" +
                e.path.map(p => `${p.from} → ${p.to} (${p.kind})`).join("\n");
              break;
          }
          return err({
            phase: "context",
            title: "文脈エラー",
            message: msg,
            detail: e,
          });
        }
        case "UnexpectedToken":
          msg = `ここには ${tokenDesc(ctxR.err.expected)} が必要ですが、 ${tokenDesc(ctxR.err.actual.type)} が見つかりました。`;
          break;
      }
      return err({
        phase: "parse",
        title: "構文解析エラー",
        message: msg,
        detail: ctxR.err,
      });
    }
    const pctx = ctxR.value;
    setPGlobalContext(pctx);
    return succ(true);
  }

  useEffect(() => {
    const id = ++runIdRef.current;
    startTransition(() => {
      const result = runUntilContext(source);
      if (runIdRef.current !== id)
        return;
      if (isErr(result))
        fail(result.err);
      else setError(null);
    });
  }, [source]);

  const runTypeCheck = () => {
    setError(null);
    setSuccess("");
    setSuccessDefs([]);
    const jc = judgCtx(elabGlobalContext(pGlobalContext), []);
    const wf = wellFormed(jc);
    for (const c of jc.global) {
      console.log(c);
    }
    if (isErr(wf)) {
      let msg = "";
      switch (wf.err.error.tag) {
        case "TypeHasNoType":
          msg = `Type は型を持ちません。\n\n` +
            `参照元: ${showCtxElement(wf.err.at)}`;
          break;
        case "UnboundVariable":
          msg = `変数 ${wf.err.error.name} は定義されていません。\n` +
            `参照元: ${showCtxElement(wf.err.at)}`;
          break;
        case "ExpectedSort":
          msg = `Sort (Prop / Type) が期待されましたが、次の型でした: ${showTerm(wf.err.error.actual)}\n\n` +
            `参照元: ${showCtxElement(wf.err.at)}`;
          break;
        case "ImpossibleCombination":
          msg = `Sortの組み合わせが無効です:\nsort0 -> ${wf.err.error.sort0}\nsort1 -> ${wf.err.error.sort1}\n\n` +
            `参照元: ${showCtxElement(wf.err.at)}`;
          break;
        case "ExpectedPi":
          msg = `${showTerm(wf.err.error.fun)}の型として関数型 (forall) が期待されましたが、次の型でした: ${showTerm(wf.err.error.actual)}\n\n` +
            `参照元: ${showCtxElement(wf.err.at)}`;
          break;
        case "ExpectedSigma":
          msg = `${showTerm(wf.err.error.pair)}の型として直積型 (exist) が期待されましたが、次の型でした: ${showTerm(wf.err.error.actual)}\n\n` +
            `参照元: ${showCtxElement(wf.err.at)}`;
          break;
        case "TypeMismatch":
          msg = `型が一致しません。\n` +
            `期待された型: ${showTerm(wf.err.error.expected)}\n` +
            `実際の型: ${showTerm(wf.err.error.actual)}\n\n` +
            `参照元: ${showCtxElement(wf.err.at)}`;
          break;
      }
      fail({
        phase: "typecheck",
        title: `型エラー`,
        message: msg,
        detail: wf.err,
      });
      return;
    }
    setSuccess("✔ すべての定義は正しく型付けされました");
    setSuccessDefs(pGlobalContext.map(e => e.elem.name));
  };

  return (
    <div className="app">
      <header>
        CoC Playground
      </header>
      <CustomLanguageEditor
        source={source}
        replace={e => setSource(e)}
      />
      <footer>
        <div className="controls">
          <button onClick={runTypeCheck}>Check</button>
        </div>
        <div className="result">
          {isPending && <span>解析中…</span>}
          {error && renderError(error)}
          {success &&
            <div className="success">
              {success+" "}
              {successDefs.join(", ")}
            </div>
          }
        </div>
      </footer>
    </div>
  );
}