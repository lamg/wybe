module FsDefinitionsTest

open Xunit
open FsDefinitions

let projectFile = __SOURCE_DIRECTORY__ + "/../Prover/Prover.fsproj"

[<Fact>]
let ``module0 instance property is accessible`` () =
  let m = getModule projectFile "module0"
  Assert.NotNull(m)

[<Fact>]
let ``insert instance property is accessible`` () =
  let fn = getFunction projectFile "module0" "insert"
  Assert.NotNull(fn)

[<Fact>]
let ``branch0 instance property returns a proposition with expected content`` () =
  let prop = getBranch projectFile "module0" "insert" 0
  let s = prop.ToString()
  //Assert.Contains("Length xs = 0", s)
  Assert.Contains("insert", s)
