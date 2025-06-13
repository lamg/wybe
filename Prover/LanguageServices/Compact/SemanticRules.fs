module LanguageServices.Compact.SemanticRules

open AST

// import CompactStandardLibrary;
// enum State { unset, set }
//
// export ledger authority: Bytes<32>;
// export ledger value: Uint<64>;
// export ledger state: State;
// export ledger round: Counter;
//
// constructor(sk: Bytes<32>, v: Uint<64>) {
//   authority = publicKey(round, sk);
//   value = v;
//   state = State.set;
// }
//
// circuit publicKey(round: Field, sk: Bytes<32>): Bytes<32> {
//   return persistentHash<Vector<3, Bytes<32>>>(
//     [pad(32, "midnight:examples:lock:pk"),
//      round as Bytes<32>,
//      sk]);
// }
//
// export circuit get(): Uint<64> {
//   assert(state == State.set, "Attempted to get uninitialized value");
//   return value;
// }
//
// witness secretKey(): Bytes<32>;
//
// export circuit set(v: Uint<64>): [] {
//   assert(state == State.unset, "Attempted to set initialized value");
//   const sk = secretKey();
//   const pk = publicKey(round, sk);
//   authority = pk;
//   value = v;
//   state = State.set;
// }
//
// export circuit clear(): [] {
//   assert(state == State.set, "Attempted to clear uninitialized value");
//   const sk = secretKey();
//   const pk = publicKey(round, sk);
//   assert(authority == pk, "Attempted to clear without authorization");
//   state = State.unset;
//   round.increment(1);
// }

open Core

type Rule =
  | SameType of Expr * Expr
  | EqualType of Expr * CompactType

let assignmentTypeRule (target: Expr, e: Expr) = SameType(target, e)

let rec boolOp e x y =
  [ SameType(x, y); EqualType(e, compactBool) ]
  @ expressionTypeRule x
  @ expressionTypeRule y

and intIntOp e x y =
  [ EqualType(x, compactInt); EqualType(y, compactInt); EqualType(e, compactInt) ]
  @ expressionTypeRule x
  @ expressionTypeRule y

and expressionTypeRule =
  function
  | Binary(x, op, y) as e ->
    match op with
    | ">=" -> boolOp e x y
    | "<=" -> boolOp e x y
    | "<" -> boolOp e x y
    | ">" -> boolOp e x y
    | "==" -> boolOp e x y
    | "!=" -> boolOp e x y
    | "+" -> intIntOp e x y
    | "-" -> intIntOp e x y
    | "*" -> intIntOp e x y
    | _ -> failwith "not supported expression"
  | Call _ -> failwith "not supported expression"
  | _ -> failwith "not supported expression"
