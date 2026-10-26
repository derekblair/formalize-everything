/-!
# Character classes (RFC 3986 §2, with the RFC 5234 core rules)

The character classes of the ABNF, as decidable predicates on `Char`.
The numeric ranges are Unicode code points and are exactly the `%x`
ranges of the ABNF definitions, so membership of any concrete character
is decidable and checkable by `decide`.
-/

/-- `ALPHA = %x41-5A / %x61-7A` -/
def IsAlpha (c : Char) : Prop :=
  (65 ≤ c.toNat ∧ c.toNat ≤ 90) ∨ (97 ≤ c.toNat ∧ c.toNat ≤ 122)

/-- `DIGIT = %x30-39` -/
def IsDigit (c : Char) : Prop :=
  48 ≤ c.toNat ∧ c.toNat ≤ 57

/-- `HEXDIG = DIGIT / %x41-46 / %x61-66` -/
def IsHexDig (c : Char) : Prop :=
  IsDigit c ∨ (65 ≤ c.toNat ∧ c.toNat ≤ 70) ∨ (97 ≤ c.toNat ∧ c.toNat ≤ 102)

/-- `unreserved = ALPHA / DIGIT / "-" / "." / "_" / "~"` -/
def IsUnreserved (c : Char) : Prop :=
  IsAlpha c ∨ IsDigit c ∨ c = '-' ∨ c = '.' ∨ c = '_' ∨ c = '~'

/-- `gen-delims = ":" / "/" / "?" / "#" / "[" / "]" / "@"` -/
def IsGenDelim (c : Char) : Prop :=
  c = ':' ∨ c = '/' ∨ c = '?' ∨ c = '#' ∨ c = '[' ∨ c = ']' ∨ c = '@'

/-- `sub-delims = "!" / "$" / "&" / "'" / "(" / ")" / "*" / "+" / "," / ";" / "="` -/
def IsSubDelim (c : Char) : Prop :=
  c = '!' ∨ c = '$' ∨ c = '&' ∨ c = '\'' ∨ c = '(' ∨ c = ')' ∨
  c = '*' ∨ c = '+' ∨ c = ',' ∨ c = ';' ∨ c = '='

/-- `reserved = gen-delims / sub-delims` -/
def IsReserved (c : Char) : Prop :=
  IsGenDelim c ∨ IsSubDelim c

instance (c : Char) : Decidable (IsAlpha c) := by
  unfold IsAlpha; infer_instance

instance (c : Char) : Decidable (IsDigit c) := by
  unfold IsDigit; infer_instance

instance (c : Char) : Decidable (IsHexDig c) := by
  unfold IsHexDig IsDigit; infer_instance

instance (c : Char) : Decidable (IsUnreserved c) := by
  unfold IsUnreserved IsAlpha IsDigit; infer_instance

instance (c : Char) : Decidable (IsGenDelim c) := by
  unfold IsGenDelim; infer_instance

instance (c : Char) : Decidable (IsSubDelim c) := by
  unfold IsSubDelim; infer_instance

instance (c : Char) : Decidable (IsReserved c) := by
  unfold IsReserved IsGenDelim IsSubDelim; infer_instance

/-- A character packaged with a proof that it is `ALPHA`. An `abbrev`, so
that the subtype is reducibly transparent wherever these are used. -/
abbrev AlphaChar := { c : Char // IsAlpha c }

/-- A character packaged with a proof that it is a `DIGIT`. -/
abbrev DigitChar := { c : Char // IsDigit c }

/-- A character packaged with a proof that it is a `HEXDIG`. -/
abbrev HexDigChar := { c : Char // IsHexDig c }
