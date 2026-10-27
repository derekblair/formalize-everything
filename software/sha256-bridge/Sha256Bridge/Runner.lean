import LeanSha256
import Hash.Sha256

/-!
Compiled execution checks, separate from the kernel known-answer gates.
Run `lake exe sha256-bridge-vectors` from this package's directory. The CAVP
response files are read from the unchanged, commit-pinned LeanSha256 dependency;
this module embeds no copy of that corpus and imports no upstream test target.
These finite checks do not prove an equivalence theorem or discharge FFI axioms.
-/

namespace Sha256Bridge.Runner

/-- A byte-oriented CAVP input and its 32-byte published digest. -/
structure VectorCase where
  bitLength : Nat
  message : ByteArray
  expected : ByteArray

/-- Parse the pinned CAVP three-field record format strictly. In particular,
`Len = 0 / Msg = 00` denotes an empty input, not the byte `0x00`. -/
def parseCavp (text : String) : Except String (Array VectorCase) := do
  let mut cases := #[]
  let mut length : Option Nat := none
  let mut message : Option ByteArray := none
  let mut lineNo := 0
  for raw in text.splitOn "\n" do
    lineNo := lineNo + 1
    let line := String.ofList (raw.toList.filter (· != '\r'))
    if line.isEmpty || line.startsWith "#" || line == "[L = 32]" then
      continue
    if line.startsWith "Len = " then
      if length.isSome || message.isSome then
        throw s!"line {lineNo}: new Len before the previous record ended"
      let value := String.ofList (line.toList.drop 6)
      match value.toNat? with
      | none => throw s!"line {lineNo}: invalid Len"
      | some n =>
        if n % 8 != 0 then
          throw s!"line {lineNo}: non-byte-aligned Len {n}"
        length := some n
    else if line.startsWith "Msg = " then
      let some n := length | throw s!"line {lineNo}: Msg without Len"
      if message.isSome then
        throw s!"line {lineNo}: duplicate Msg"
      let hex := String.ofList (line.toList.drop 6)
      let some bytes := Hash.Sha256.Hex.decode? hex
        | throw s!"line {lineNo}: invalid Msg hexadecimal"
      if n == 0 then
        if hex != "00" then
          throw s!"line {lineNo}: unexpected empty-message placeholder"
        message := some ByteArray.empty
      else
        if bytes.size * 8 != n then
          throw s!"line {lineNo}: Msg size does not match Len {n}"
        message := some bytes
    else if line.startsWith "MD = " then
      let some n := length | throw s!"line {lineNo}: MD without Len"
      let some bytes := message | throw s!"line {lineNo}: MD without Msg"
      let hex := String.ofList (line.toList.drop 5)
      let some digest := Hash.Sha256.Hex.decode? hex
        | throw s!"line {lineNo}: invalid MD hexadecimal"
      if digest.size != 32 then
        throw s!"line {lineNo}: MD must contain 32 bytes"
      cases := cases.push ⟨n, bytes, digest⟩
      length := none
      message := none
    else
      throw s!"line {lineNo}: unrecognized content"
  if length.isSome || message.isSome then
    throw "incomplete final CAVP record"
  return cases

/-- Check both pure implementations against one independently supplied answer. -/
def checkAnswer (label : String) (message expected : ByteArray) : IO Unit := do
  let actual := LeanSha256.hash message
  let other := (Hash.Sha256.sha256 message).bytes
  unless actual == expected do
    throw <| IO.userError s!"{label}: LeanSha256 expected {Hash.Sha256.Hex.encode expected}, got {Hash.Sha256.Hex.encode actual}"
  unless other == expected do
    throw <| IO.userError s!"{label}: lean4-hash expected {Hash.Sha256.Hex.encode expected}, got {Hash.Sha256.Hex.encode other}"

/-- Require the exact pinned suite size, then execute every parsed record. -/
def checkCavpFile (path : System.FilePath) (expectedCount : Nat) : IO Nat := do
  let records ← match parseCavp (← IO.FS.readFile path) with
    | .ok records => pure records
    | .error e => throw <| IO.userError s!"{path}: {e}"
  unless records.size == expectedCount do
    throw <| IO.userError s!"{path}: expected {expectedCount} records, found {records.size}"
  let mut index := 0
  for record in records do
    index := index + 1
    checkAnswer s!"{path}, record {index}, Len = {record.bitLength}"
      record.message record.expected
  IO.println s!"PASS {path.fileName.getD path.toString}: {records.size} published CAVP vectors (both implementations)"
  return records.size

/-- The long FIPS vector is evaluated only by this executable, never as a theorem. -/
def checkMillionA : IO Unit := do
  let millionA : ByteArray := ⟨Array.replicate 1000000 0x61⟩
  let some expected := Hash.Sha256.Hex.decode?
      "cdc76e5c9914fb9281a1c7e284d73e67f1809a48a497200e046d39ccc7112cd0"
    | throw <| IO.userError "invalid embedded FIPS B.3 digest"
  checkAnswer "FIPS B.3, 1000000 ASCII a bytes" millionA expected
  IO.println "PASS FIPS B.3: 1000000 ASCII a bytes, 15626 padded compression blocks (both implementations)"

/-- All lengths 0 through 256, with a deterministic nonconstant byte pattern. -/
def checkBoundaries : IO Unit := do
  for n in [:257] do
    let message : ByteArray := ⟨(Array.range n).map fun i => UInt8.ofNat (17 * i + 3)⟩
    unless LeanSha256.hash message == (Hash.Sha256.sha256 message).bytes do
      throw <| IO.userError s!"boundary cross-check failed at {n} bytes"
  IO.println "PASS boundary cross-check: 257 messages, lengths 0 through 256"

def run : IO Unit := do
  checkMillionA
  let directory : System.FilePath := ".lake/packages/LeanSha256/cavp"
  let short ← checkCavpFile (directory / "SHA256ShortMsg.rsp") 65
  let long ← checkCavpFile (directory / "SHA256LongMsg.rsp") 64
  unless short + long == 129 do
    throw <| IO.userError "CAVP total is not 129"
  checkBoundaries
  IO.println "PASS sha256-bridge-vectors: FIPS B.3 + 129 CAVP vectors + 257 boundary comparisons"

end Sha256Bridge.Runner

def main : IO UInt32 := do
  try
    Sha256Bridge.Runner.run
    return 0
  catch e =>
    IO.eprintln s!"FAIL sha256-bridge-vectors: {e}"
    return 1
