module CompactTest

open Xunit

[<Fact>]
let ``parse counter`` () =
  let counter =
    """
pragma language_version 0.15;

import CompactStandardLibrary;

// public state
export ledger round: Counter;

// transition function changing public state
export circuit increment(): [] {
  round.increment(1);
}"""

  let statements = Parsers.Compact.parse counter
  printfn $"STATEMENTS {statements}"
  Assert.True(statements.Length > 0)


[<Fact>]
let ``parse large example`` () =
  let example = """
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

  ()
