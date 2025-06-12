module CompactTest

open Xunit
open LanguageServices.Compact.AST
open LanguageServices.Compact.Parser
open LanguageServices.Compact.TypeChecker

[<Fact>]
let ``parse counter`` () =
  let counter =
    """
pragma language_version 0.15;

import CompactStandardLibrary;

enum State { unset, set }
// public state
export ledger round: Counter;

// transition function changing public state
export circuit increment(): [] {
  round.increment(1);
}"""

  let topLevel = LanguageServices.Compact.Parser.parse counter

  let expected =
    [ Pragma([ "language_version" ], Version [ 0; 15 ])
      Import [ [ "CompactStandardLibrary" ] ]
      Enum(false, [ "State" ], [ [ "unset" ]; [ "set" ] ])
      Ledger(
        true,
        { paramName = [ "round" ]
          paramType = NamedType([ "Counter" ], []) }
      )
      Circuit(
        true,
        [ "increment" ],
        { args = []; returnType = Void },
        [ CallStatement(Call([ "round"; "increment" ], [], [ Lit(Int 1) ])) ]
      ) ]

  Assert.Equal<TopLevel list>(expected, topLevel)

[<Fact>]
let ``parse large example`` () =
  let example =
    """
import CompactStandardLibrary;
enum State { unset, set }

export ledger authority: Bytes<32>;
export ledger value: Uint<64>;
export ledger state: State;
export ledger round: Counter;

constructor(sk: Bytes<32>, v: Uint<64>) {
  authority = publicKey(round, sk);
  value = v;
  state = State.set;
}

circuit publicKey(round: Field, sk: Bytes<32>): Bytes<32> {
  return persistentHash<Vector<3, Bytes<32>>>(
    [pad(32, "midnight:examples:lock:pk"),
     round as Bytes<32>,
     sk]);
}

export circuit get(): Uint<64> {
  assert(state == State.set, "Attempted to get uninitialized value");
  return value;
}

witness secretKey(): Bytes<32>;

export circuit set(v: Uint<64>): [] {
  assert(state == State.unset, "Attempted to set initialized value");
  const sk = secretKey();
  const pk = publicKey(round, sk);
  authority = pk;
  value = v;
  state = State.set;
}

export circuit clear(): [] {
  assert(state == State.set, "Attempted to clear uninitialized value");
  const sk = secretKey();
  const pk = publicKey(round, sk);
  assert(authority == pk, "Attempted to clear without authorization");
  state = State.unset;
  round.increment(1);
}"""

  let topLevel = LanguageServices.Compact.Parser.parse example
  Assert.True(topLevel.Length > 0)

[<Fact>]
let ``typecheck simple arithmetic in constructor`` () =
  let src = """
constructor() {
  const x = 1 + 2;
}
"""
  let prog = parse src
  check prog

[<Fact>]
let ``typecheck assignment type mismatch`` () =
  let src = """
constructor() {
  const x = 1;
  x = true;
}
"""
  let prog = parse src
  Assert.Throws<TypeError>(fun () -> check prog) |> ignore

[<Fact>]
let ``typecheck return type mismatch`` () =
  let src = """
circuit foo(): int {
  return true;
}
"""
  let prog = parse src
  Assert.Throws<TypeError>(fun () -> check prog) |> ignore
