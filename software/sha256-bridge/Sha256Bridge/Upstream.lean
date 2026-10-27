import Lean
import LeanSha256
import Hash.Sha256

/-!
Aliases for the pinned implementation's private helpers. The term elaborator
refers to the original declarations directly; it copies no upstream bodies.
Lean's kernel checks all uses of these aliases against those declarations.
-/

open Lean Elab Term in
elab "upstreamSha256%" ident:ident : term => do
  let name := Name.str (Name.str (Name.num (Name.str (Name.str (Name.str .anonymous
    "_private") "LeanSha256") "Core") 0) "LeanSha256") ident.getId.toString
  let info ← getConstInfo name
  unless info.levelParams.isEmpty do
    throwError "unexpected universe parameters in pinned SHA-256 helper"
  return mkConst name

namespace Sha256Bridge.Upstream

abbrev kConstants : Array UInt32 := upstreamSha256% kConstants
abbrev h0Constants : Array UInt32 := upstreamSha256% h0Constants
abbrev rotr : UInt32 → UInt32 → UInt32 := upstreamSha256% rotr
abbrev ch : UInt32 → UInt32 → UInt32 → UInt32 := upstreamSha256% ch
abbrev maj : UInt32 → UInt32 → UInt32 → UInt32 := upstreamSha256% maj
abbrev bigSigma0 : UInt32 → UInt32 := upstreamSha256% bigSigma0
abbrev bigSigma1 : UInt32 → UInt32 := upstreamSha256% bigSigma1
abbrev smallSigma0 : UInt32 → UInt32 := upstreamSha256% smallSigma0
abbrev smallSigma1 : UInt32 → UInt32 := upstreamSha256% smallSigma1
abbrev extendSchedule : Array UInt32 → Nat → Array UInt32 := upstreamSha256% extendSchedule
abbrev messageSchedule : Array UInt32 → Array UInt32 := upstreamSha256% messageSchedule
abbrev oneRound : Array UInt32 → UInt32 → UInt32 → Array UInt32 := upstreamSha256% oneRound
abbrev compressBlock : Array UInt32 → Array UInt32 → Array UInt32 := upstreamSha256% compressBlock
abbrev uint64ToBytesBE : Nat → ByteArray := upstreamSha256% uint64ToBytesBE
abbrev pad : ByteArray → ByteArray := upstreamSha256% pad
abbrev bytesToWordBE : UInt8 → UInt8 → UInt8 → UInt8 → UInt32 := upstreamSha256% bytesToWordBE
abbrev wordToBytesBE : UInt32 → ByteArray := upstreamSha256% wordToBytesBE
abbrev extractBlock : ByteArray → Nat → Array UInt32 := upstreamSha256% extractBlock
abbrev packState : Array UInt32 → ByteArray := upstreamSha256% packState

end Sha256Bridge.Upstream
