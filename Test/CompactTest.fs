module CompactTest

open Xunit
open FsUnitTyped
open LanguageServices.Compact
open AST
open Parser
open TypeChecker


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

let stateSetter =
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

let extractWithEmptyEnv code =
  let env =
    { enums = Map.empty
      functions = Map.empty
      variables = Map.empty }

  code |> SemanticRules.extractSemanticInfo env

[<Fact>]
let ``parse counter`` () =
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

  topLevel |> shouldEqual expected

[<Fact>]
let ``parse large example`` () =
  let topLevel = LanguageServices.Compact.Parser.parse stateSetter
  topLevel.Length |> shouldBeGreaterThan 0

[<Fact>]
let ``typecheck simple arithmetic in constructor`` () =
  let src =
    """
constructor() {
  const x = 1 + 2;
}
"""

  let prog = parse src
  check prog

[<Fact>]
let ``typecheck assignment type mismatch`` () =
  let src =
    """
constructor() {
  const x = 1;
  x = true;
}
"""

  let prog = parse src
  shouldFail<TypeError> (fun () -> check prog)

[<Fact>]
let ``typecheck return type mismatch`` () =
  let src =
    """
circuit foo(): int {
  return true;
}
"""

  let prog = parse src
  Assert.Throws<TypeError>(fun () -> check prog) |> ignore

[<Fact>]
let ``extract semantic info`` () =
  let mkParam name cType =
    { paramName = [ name ]
      paramType = cType }

  let bytes32 = NamedType([ "Bytes" ], [ TypeParamInt 32 ])

  let roundDotIncrement =
    [ "round"; "increment" ],
    { args = [ mkParam "n" compactInt ]
      returnType = Void }

  let persistentHash =
    [ "persistentHash" ],
    { args =
        [ { paramName = [ "xs" ]
            paramType = NamedType(compactVector, [ TypeParamInt 3; CompactTypeParam bytes32 ]) } ]
      returnType = bytes32 }

  let pad =
    [ "pad" ],
    { args = [ mkParam "n" compactInt; mkParam "s" compactString ]
      returnType = bytes32 }

  let compactAssert =
    [ "assert" ],
    { args = [ mkParam "cond" compactBool; mkParam "msg" compactString ]
      returnType = Void }

  let envFunctions =
    Map.ofList [ roundDotIncrement; persistentHash; pad; compactAssert ]

  let env =
    { enums = Map.empty
      functions = envFunctions
      variables = Map.empty }

  stateSetter
  |> SemanticRules.extractSemanticInfo env
  |> _.Count
  |> shouldBeGreaterThan 0

open Core
open GriesSchneider

[<Fact>]
let ``validCalc demo 0`` () =
  let validCalc =
    """
circuit validCalc(): Uint<64> {
  const a = 18;
  const b = 1;
  return a/b;
}
  """

  let obligations = extractWithEmptyEnv validCalc
  let a, b = mkIntVar "a", mkIntVar "b"

  obligations["validCalc"][0]
  |> shouldEqual (a = Integer 18 <&&> (b = Integer 1) ==> (b != zero))
