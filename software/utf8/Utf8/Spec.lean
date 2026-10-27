/-!
# UTF-8 well-formedness: the Table 3-7 specification

An independent inductive transcription of the well-formed UTF-8 byte
sequences of the Unicode Standard, Table 3-7 ("Well-Formed UTF-8 Byte
Sequences"), equivalently RFC 3629 §3. Nothing here is defined via any
decoder: `Seq` is the document's table, row by row, and `Valid` is a
finite concatenation of well-formed sequences.

The restricted second-byte ranges in the `E0`, `ED`, `F0`, and `F4` rows
are stated exactly as the table states them. They are what exclude
overlong (non-shortest) forms, the UTF-16 surrogate code points
U+D800–U+DFFF, and code points above U+10FFFF.
-/

namespace Utf8

/-- A continuation byte: the pattern `10xxxxxx`, that is `0x80 ≤ b ≤ 0xBF`. -/
def IsCont (b : UInt8) : Prop :=
  0x80 ≤ b.toNat ∧ b.toNat ≤ 0xBF

instance (b : UInt8) : Decidable (IsCont b) :=
  inferInstanceAs (Decidable (0x80 ≤ b.toNat ∧ b.toNat ≤ 0xBF))

/-- One well-formed UTF-8 byte sequence: exactly one row of Table 3-7.

Well-formed ranges, in hexadecimal. The first byte determines the row:

* `00–7F` — a single byte;
* `C2–DF`, then one continuation byte;
* `E0`, then `A0–BF`, then a continuation byte;
* `E1–EC`, then two continuation bytes;
* `ED`, then `80–9F`, then a continuation byte;
* `EE–EF`, then two continuation bytes;
* `F0`, then `90–BF`, then two continuation bytes;
* `F1–F3`, then three continuation bytes;
* `F4`, then `80–8F`, then two continuation bytes.

Bytes `80–C1` and `F5–FF` begin no row: `80–BF` are continuation bytes,
`C0–C1` could only start overlong two-byte forms, and `F5–FF` could only
start forms for code points above U+10FFFF. -/
inductive Seq : List UInt8 → Prop where
  | one {b : UInt8} (h : b.toNat ≤ 0x7F) : Seq [b]
  | two {b₀ b₁ : UInt8} (h₀ : 0xC2 ≤ b₀.toNat ∧ b₀.toNat ≤ 0xDF)
      (h₁ : IsCont b₁) : Seq [b₀, b₁]
  | threeE0 {b₀ b₁ b₂ : UInt8} (h₀ : b₀.toNat = 0xE0)
      (h₁ : 0xA0 ≤ b₁.toNat ∧ b₁.toNat ≤ 0xBF) (h₂ : IsCont b₂) :
      Seq [b₀, b₁, b₂]
  | three {b₀ b₁ b₂ : UInt8} (h₀ : 0xE1 ≤ b₀.toNat ∧ b₀.toNat ≤ 0xEC)
      (h₁ : IsCont b₁) (h₂ : IsCont b₂) : Seq [b₀, b₁, b₂]
  | threeED {b₀ b₁ b₂ : UInt8} (h₀ : b₀.toNat = 0xED)
      (h₁ : 0x80 ≤ b₁.toNat ∧ b₁.toNat ≤ 0x9F) (h₂ : IsCont b₂) :
      Seq [b₀, b₁, b₂]
  | threeEF {b₀ b₁ b₂ : UInt8} (h₀ : 0xEE ≤ b₀.toNat ∧ b₀.toNat ≤ 0xEF)
      (h₁ : IsCont b₁) (h₂ : IsCont b₂) : Seq [b₀, b₁, b₂]
  | fourF0 {b₀ b₁ b₂ b₃ : UInt8} (h₀ : b₀.toNat = 0xF0)
      (h₁ : 0x90 ≤ b₁.toNat ∧ b₁.toNat ≤ 0xBF)
      (h₂ : IsCont b₂) (h₃ : IsCont b₃) : Seq [b₀, b₁, b₂, b₃]
  | four {b₀ b₁ b₂ b₃ : UInt8} (h₀ : 0xF1 ≤ b₀.toNat ∧ b₀.toNat ≤ 0xF3)
      (h₁ : IsCont b₁) (h₂ : IsCont b₂) (h₃ : IsCont b₃) :
      Seq [b₀, b₁, b₂, b₃]
  | fourF4 {b₀ b₁ b₂ b₃ : UInt8} (h₀ : b₀.toNat = 0xF4)
      (h₁ : 0x80 ≤ b₁.toNat ∧ b₁.toNat ≤ 0x8F)
      (h₂ : IsCont b₂) (h₃ : IsCont b₃) : Seq [b₀, b₁, b₂, b₃]

/-- A byte sequence is well-formed UTF-8 when it is a finite concatenation
of well-formed sequences. The empty sequence is well-formed. -/
inductive Valid : List UInt8 → Prop where
  | nil : Valid []
  | cons {s rest : List UInt8} (hs : Seq s) (hr : Valid rest) :
      Valid (s ++ rest)

/-- A single well-formed sequence is a well-formed byte sequence. -/
theorem Valid.ofSeq {s : List UInt8} (hs : Seq s) : Valid s := by
  have h := Valid.cons hs Valid.nil
  simpa using h

/-- Well-formedness is closed under concatenation. -/
theorem Valid.append {l₁ l₂ : List UInt8} (h₁ : Valid l₁) (h₂ : Valid l₂) :
    Valid (l₁ ++ l₂) := by
  induction h₁ with
  | nil => simpa using h₂
  | cons hs _ ih =>
      rw [List.append_assoc]
      exact Valid.cons hs ih

/-- The canonical (shortest-form) UTF-8 encoding of a code point, written
with the division/modulo formulas that produce exactly the bit patterns
of Table 3-7. For a valid Unicode scalar value `n`, `encodeCodepoint n`
is the unique row of the table whose bit pattern carries `n`; for other
`n` the value of this function is not used. -/
def encodeCodepoint (n : Nat) : List UInt8 :=
  if n ≤ 0x7F then [UInt8.ofNat n]
  else if n ≤ 0x7FF then
    [UInt8.ofNat (n / 64 % 32 + 0xC0), UInt8.ofNat (n % 64 + 0x80)]
  else if n ≤ 0xFFFF then
    [UInt8.ofNat (n / 4096 % 16 + 0xE0), UInt8.ofNat (n / 64 % 64 + 0x80),
      UInt8.ofNat (n % 64 + 0x80)]
  else
    [UInt8.ofNat (n / 262144 % 8 + 0xF0), UInt8.ofNat (n / 4096 % 64 + 0x80),
      UInt8.ofNat (n / 64 % 64 + 0x80), UInt8.ofNat (n % 64 + 0x80)]

/-- Encode a list of characters, each by `encodeCodepoint` of its value. -/
def encodeAll (cs : List Char) : List UInt8 :=
  cs.flatMap (fun c => encodeCodepoint c.val.toNat)

end Utf8
