import { useState } from "react";
import "./app.css";
import { type Term } from "./ast";
import { Tokenizer } from "./tokenize";
import { Parser } from "./parse";
import { type CtxElement, judgCtx } from "./core";
import { wellFormed } from "./typecheck";
import { checkJudgContext } from "./context";
import { isErr } from "./result";

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
    case "Let":
      return `(let ${t.name} : ${showTerm(t.type)} := ${showTerm(t.def)} in ${showTerm(t.body)})`;
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

const init = `def id (A : Prop) (x : A) : A := x;

def Nat: Prop := forall (A: Prop), (A -> A) -> A -> A;

def zero: Nat :=
  fun (A: Prop) (f: A -> A) (x: A) => x;

def succ : Nat -> Nat :=
  fun (n : Nat) (A : Prop) (f : A -> A) (x : A) => f (n A f x);


def Bool: Prop := forall (A: Prop), A -> A -> A;

def true: Bool := fun (A: Prop) (x y: A) => x;

def false: Bool := fun (A: Prop) (x y: A) => y;

def or: Bool -> Bool -> Bool :=
  fun (a b: Bool) => a Bool true b;

def and: Bool -> Bool -> Bool :=
  fun (a b: Bool) => a Bool b false;

def not: Bool -> Bool :=
  fun (a: Bool) => a Bool false true;


def Prod (A B: Prop): Prop :=
  forall (C: Prop), (A -> B -> C) -> C;

def pair (A B: Prop): A -> B -> Prod A B :=
  fun (a: A) (b: B) (C: Prop) (f: A -> B -> C) => f a b;

def left (A B: Prop): Prod A B -> A :=
  fun (p: Prod A B) => p A (fun (a: A) (b: B) => a);

def right (A B: Prop): Prod A B -> B :=
  fun (p: Prod A B) => p B (fun (a: A) (b: B) => b);


def iter : Nat -> forall (A : Prop), (A -> A) -> A -> A :=
  fun (n : Nat) (A : Prop) (f : A -> A) (x : A) => n A f x;

def rec : Nat -> forall (A: Prop), A -> (Nat -> A -> A) -> A :=
  fun (n : Nat) (A : Prop) (a : A) (s : Nat -> A -> A) =>
    let step : Prod Nat A -> Prod Nat A :=
      fun (p : Prod Nat A) =>
        pair Nat A
          (succ (left Nat A p))
          (s (left Nat A p) (right Nat A p)) in
      right Nat A (n (Prod Nat A) step (pair Nat A zero a));

def List (A: Prop): Prop :=
  forall (L: Prop), L -> (A -> L -> L) -> L;`

export default function App() {
  const [source, setSource] = useState(init);
  const [error, setError] = useState<UIError | null>(null);
  const [success, setSuccess] = useState<string>("");
  const [successDefs, setSuccessDefs] = useState<string[]>([]);

  const fail = (e: UIError) => {
    setSuccess("");
    setError(e);
  };

  const run = () => {
    setError(null);
    setSuccess("");
    setSuccessDefs([]);
    const tokenizer = new Tokenizer(source);
    const tokensR = tokenizer.tokenize();
    if (isErr(tokensR)) {
      fail({
        phase: "tokenize",
        title: "字句解析エラー",
        message:
          tokensR.err.tag === "UnexpectedChar"
            ? `不正な文字 ${tokensR.err.char} を検出しました。`
            : "コメントが閉じられていません。",
        detail: tokensR.err,
      });
      return;
    }
    const parser = new Parser(tokensR.value);
    const ctxR = parser.parseProgram();
    if (isErr(ctxR)) {
      let msg: string;
      switch (ctxR.err.tag) {
        case "UnexpectedToken":
          msg = `トークン ${ctxR.err.actual.type} は ${ctxR.err.expected} ではありません。`;
          break;
        case "ExpectedAtom":
          msg = `Atomが必要な位置です。 (実際に検出されたもの: ${ctxR.err.token.type})`;
          break;
        case "ExtraneousDef":
          msg = `不要な定義 ${showTerm(ctxR.err.def)} が検出されました。`;
          break;
        case "ExpectedDef":
          msg = `定義が必要な位置です。`;
          break;
      }
      fail({
        phase: "parse",
        title: "構文解析エラー",
        message: msg,
        detail: ctxR.err,
      });
      return;
    }
    const ctx = ctxR.value;
    const jc = judgCtx(ctx, []);
    const ctxCheck = checkJudgContext(jc);
    if (isErr(ctxCheck)) {
      const e = ctxCheck.err;
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
        case "GlobalDependsOnLocal":
          msg = `ローカル定義 ${e.to} (${e.kind}) にグローバル定義 ${e.from} が依存しています。`;
          break;
        case "ForwardDependency":
          msg = `${e.from} は 現在未定義の${e.to} (${e.kind}) に依存しています。`;
          break;
        case "Undefined":
          msg = `定義 ${e.in} の中で未定義の名前 ${e.name} (${e.kind}) が使われています。`;
          break;
        case "Cycle":
          msg = "定義に循環依存があります:\n" +
            e.path.map(p => `${p.from} → ${p.to} (${p.kind})`).join("\n");
          break;
      }
      fail({
        phase: "context",
        title: "文脈エラー",
        message: msg,
        detail: e,
      });
      return;
    }
    const wf = wellFormed(jc);
    for (const c of jc.global) {
      console.log(showCtxElement(c));
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
        case "ExpectedPi":
          msg = `${showTerm(wf.err.error.fun)}の型として関数型が期待されましたが、次の型でした: ${showTerm(wf.err.error.actual)}\n\n` +
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
    setSuccessDefs(jc.global.map(e => e.name));
  };

  return (
    <div className="app">
      <header>Mini CoC Playground</header>
      <textarea
        value={source}
        onChange={e => setSource(e.target.value)}
        spellCheck={false}
      />
      <div className="controls">
        <button onClick={run}>Check</button>
      </div>
      <div className="result">
        {error && renderError(error)}
        {success &&
          <div className="success">
            {success+" "}
            {successDefs.join(", ")}
          </div>
        }
      </div>
    </div>
  );
}