export type Succ<A> = { tag: "succ"; value: A }
export type Err<B> = { tag: "err"; err: B };
export type Result<A, B> = Succ<A> | Err<B>

export const succ = <A>(value: A): Succ<A> => ({ tag: "succ", value });
export const err = <B>(err: B): Err<B> => ({ tag: "err", err });

export const isSucc = <A, B>(vali: Result<A, B>): vali is Succ<A> => vali.tag === "succ";
export const isErr = <A, B>(vali: Result<A, B>): vali is Err<B> => vali.tag === "err";