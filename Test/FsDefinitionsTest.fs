module FsDefinitionsTest

open Xunit
open FsDefinitions

// Use __SOURCE_DIRECTORY__ so that the test picks up the Prover.fsproj next door.
type TestProj = FromProjectTypeProvider<__SOURCE_DIRECTORY__ + "/../Prover/Prover.fsproj">

[<Fact>]
let ``module0 instance property is accessible`` () =
  let p = TestProj()
  let m = p.module0
  Assert.NotNull(m)

[<Fact>]
let ``insert instance property is accessible`` () =
  let p = TestProj()
  let fn = p.module0.insert
  Assert.NotNull(fn)

[<Fact>]
let ``branch0 instance property returns a proposition with expected content`` () =
  let pInst = TestProj()
  let p = pInst.module0.insert.branch0
  let s = p.ToString()
  Assert.Contains("Length xs = 0", s)
  Assert.Contains("insert", s)
