/-
Copyright (c) 2026 Derek Blair. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import Cbor.Rfc8949.Parse

/-!
# The parser inverts the wire grammar exactly

Soundness (`decodeRaw_sound`): whatever the decoder returns is a `WF` tree
whose encoding is exactly the consumed prefix. Completeness
(`decodeRaw_complete`): every `WF` tree is decoded back from its encoding
followed by any bytes, given fuel above the encoding's length. Together:

* `parseRaw_eq_some_iff` — `parseRaw bs = some r ↔ r.WF ∧ r.encode = bs`;
* `parseWellFormed_eq_some_iff` — `parseWellFormed bs = some x` iff `bs` is
  the encoding of a well-formed tree whose item is `x`;
* `decodeRaw_of_length_lt` — any fuel above `bs.length` gives the same
  answer as the initial fuel `bs.length + 1`: the step fuel never truncates
  the grammar, including arbitrarily long indefinite-length loops (I5);
* the break-stop-code clauses of §3.2.1–§3.2.3 hold on every input: a break
  is never an item, chunks are definite strings of the parent's major type,
  and every indefinite item ends at its own break.
-/

namespace Cbor.Rfc8949

/-! ## Generic loops -/

section Loops

variable {α : Type} {dec : List UInt8 → Option (α × List UInt8)} {enc : α → List UInt8}

theorem decodeCount_sound {P : α → Prop}
    (hdec : ∀ bs x rest, dec bs = some (x, rest) → P x ∧ bs = enc x ++ rest) :
    ∀ n bs xs rest, decodeCount dec n bs = some (xs, rest) →
      xs.length = n ∧ (∀ x ∈ xs, P x) ∧ bs = (xs.map enc).flatten ++ rest := by
  intro n
  induction n with
  | zero =>
    intro bs xs rest h
    simp only [decodeCount, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp
  | succ n ih =>
    intro bs xs rest h
    simp only [decodeCount] at h
    split at h
    · simp at h
    · rename_i x r hx
      split at h
      · simp at h
      · rename_i ys r' hys
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨hPx, rfl⟩ := hdec _ _ _ hx
        obtain ⟨hlen, hP, rfl⟩ := ih _ _ _ hys
        refine ⟨by simp [hlen], ?_, by simp⟩
        intro y hy
        simp only [List.mem_cons] at hy
        rcases hy with rfl | hy
        · exact hPx
        · exact hP y hy

theorem decodeCount_complete (xs : List α)
    (hdec : ∀ x ∈ xs, ∀ rest, dec (enc x ++ rest) = some (x, rest)) (rest : List UInt8) :
    decodeCount dec xs.length ((xs.map enc).flatten ++ rest) = some (xs, rest) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hx := hdec x (by simp) ((xs.map enc).flatten ++ rest)
    have hxs := ih (fun y hy => hdec y (by simp [hy]))
    simp only [List.length_cons, List.map_cons, List.flatten_cons, List.append_assoc, decodeCount,
      hx, hxs]

theorem decodeUntilBreak_sound {P : α → Prop}
    (hdec : ∀ bs x rest, dec bs = some (x, rest) → P x ∧ bs = enc x ++ rest) :
    ∀ fuel bs xs rest, decodeUntilBreak dec fuel bs = some (xs, rest) →
      (∀ x ∈ xs, P x) ∧ bs = (xs.map enc).flatten ++ 0xff :: rest := by
  intro fuel
  induction fuel with
  | zero => intro bs xs rest h; simp [decodeUntilBreak] at h
  | succ fuel ih =>
    intro bs xs rest h
    match bs with
    | [] => simp [decodeUntilBreak] at h
    | b :: bs =>
      simp only [decodeUntilBreak] at h
      split at h
      · rename_i hb
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp [hb]
      · split at h
        · simp at h
        · rename_i x r hx
          split at h
          · simp at h
          · rename_i ys r' hys
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            obtain ⟨hPx, hbs⟩ := hdec _ _ _ hx
            obtain ⟨hP, rfl⟩ := ih _ _ _ hys
            refine ⟨?_, by rw [hbs]; simp⟩
            intro y hy
            simp only [List.mem_cons] at hy
            rcases hy with rfl | hy
            · exact hPx
            · exact hP y hy

theorem decodeUntilBreak_complete (xs : List α)
    (hdec : ∀ x ∈ xs, ∀ rest, dec (enc x ++ rest) = some (x, rest))
    (hfirst : ∀ x ∈ xs, ∃ b t, enc x = b :: t ∧ b ≠ 0xff) :
    ∀ fuel, xs.length < fuel → ∀ rest,
      decodeUntilBreak dec fuel ((xs.map enc).flatten ++ 0xff :: rest) = some (xs, rest) := by
  induction xs with
  | nil =>
    intro fuel hfuel rest
    match fuel with
    | 0 => simp at hfuel
    | fuel + 1 => simp [decodeUntilBreak]
  | cons x xs ih =>
    intro fuel hfuel rest
    match fuel with
    | 0 => simp at hfuel
    | fuel + 1 =>
      obtain ⟨b, t, hxe, hb⟩ := hfirst x (by simp)
      have hx := hdec x (by simp) ((xs.map enc).flatten ++ 0xff :: rest)
      have hxs := ih (fun y hy => hdec y (by simp [hy])) (fun y hy => hfirst y (by simp [hy]))
        fuel (by simp at hfuel; omega) rest
      rw [hxe] at hx
      simp only [List.map_cons, List.flatten_cons, hxe, List.cons_append, List.append_assoc,
        decodeUntilBreak, hb, ite_false]
      simp only [List.cons_append] at hx
      rw [hx]
      simp only [hxs]

theorem decodePair_sound {P : α → Prop}
    (hdec : ∀ bs x rest, dec bs = some (x, rest) → P x ∧ bs = enc x ++ rest)
    {bs : List UInt8} {kv : α × α} {rest : List UInt8}
    (h : decodePair dec bs = some (kv, rest)) :
    (P kv.1 ∧ P kv.2) ∧ bs = (enc kv.1 ++ enc kv.2) ++ rest := by
  unfold decodePair at h
  split at h
  · simp at h
  · rename_i k r hk
    split at h
    · simp at h
    · rename_i v r' hv
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨hPk, rfl⟩ := hdec _ _ _ hk
      obtain ⟨hPv, rfl⟩ := hdec _ _ _ hv
      exact ⟨⟨hPk, hPv⟩, by simp⟩

theorem decodePair_complete {k v : α}
    (hk : ∀ rest, dec (enc k ++ rest) = some (k, rest))
    (hv : ∀ rest, dec (enc v ++ rest) = some (v, rest)) (rest : List UInt8) :
    decodePair dec ((enc k ++ enc v) ++ rest) = some ((k, v), rest) := by
  simp only [decodePair, List.append_assoc, hk, hv]

end Loops

/-! ## Small list facts -/

theorem length_le_flatten_of_mem {β : Type} {f : β → List UInt8} {xs : List β} {x : β}
    (hx : x ∈ xs) : (f x).length ≤ ((xs.map f).flatten).length := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
    simp only [List.mem_cons] at hx
    simp only [List.map_cons, List.flatten_cons, List.length_append]
    rcases hx with rfl | hx
    · omega
    · have := ih hx; omega

theorem length_le_flatten {β : Type} {f : β → List UInt8} (xs : List β)
    (hne : ∀ x ∈ xs, f x ≠ []) : xs.length ≤ ((xs.map f).flatten).length := by
  induction xs with
  | nil => simp
  | cons y ys ih =>
    have hy := hne y (by simp)
    have := ih (fun x hx => hne x (by simp [hx]))
    have : (f y).length ≠ 0 := by simpa using hy
    simp only [List.map_cons, List.flatten_cons, List.length_append, List.length_cons]
    omega

theorem encodeHead_length (m : Nat) (w : Width) (n : Nat) :
    (encodeHead m w n).length = w.extra + 1 := by
  simp [encodeHead, beBytes_length]

/-! ## Chunks of indefinite-length strings -/

/-- The bytes of one chunk of major type `m` (§3.2.3). -/
def chunkEnc (m : Nat) (c : Width × List UInt8) : List UInt8 :=
  encodeHead m c.1 c.2.length ++ c.2

theorem encodeChunks_eq (m : Nat) (cs : List (Width × List UInt8)) :
    RawItem.encodeChunks m cs = (cs.map (chunkEnc m)).flatten := by
  induction cs with
  | nil => rfl
  | cons c cs ih => obtain ⟨w, p⟩ := c; simp [RawItem.encodeChunks, chunkEnc, ih]

theorem decodeChunk_sound {m : Nat} {bs : List UInt8} {c : Width × List UInt8}
    {rest : List UInt8} (h : decodeChunk m bs = some (c, rest)) :
    c.1.fits c.2.length = true ∧ bs = chunkEnc m c ++ rest := by
  unfold decodeChunk at h
  split at h
  · rename_i m' w n rest0 hd
    split at h
    · rename_i hc
      obtain ⟨rfl, hn⟩ := hc
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨⟨_, hfit⟩, hbs⟩ := decodeHead_sound hd
      have hlen : (rest0.take n).length = n := by simp; omega
      refine ⟨by rw [hlen]; exact hfit, ?_⟩
      rw [hbs]; simp [chunkEnc, Head.bytes, hlen]
    · simp at h
  · simp at h

theorem decodeChunk_complete {m : Nat} (hm : m ≤ 6) {c : Width × List UInt8}
    (hc : c.1.fits c.2.length = true) (rest : List UInt8) :
    decodeChunk m (chunkEnc m c ++ rest) = some (c, rest) := by
  obtain ⟨w, p⟩ := c
  have hd := decodeHead_bytes (h := .arg m w p.length) ⟨hm, hc⟩ (p ++ rest)
  simp only [Head.bytes] at hd
  simp only [chunkEnc, List.append_assoc, decodeChunk, hd]
  simp

theorem chunkEnc_first {m : Nat} (hm : m ≤ 6) {c : Width × List UInt8}
    (hc : c.1.fits c.2.length = true) : ∃ b t, chunkEnc m c = b :: t ∧ b ≠ 0xff := by
  have _ := hm
  refine ⟨UInt8.ofNat (m * 32 + c.1.ai c.2.length), beBytes c.1.extra c.2.length ++ c.2,
    by simp [chunkEnc, encodeHead], ?_⟩
  have := Width.ai_lt hc
  intro h
  have h2 := congrArg UInt8.toNat h
  rw [toNat_ofNat_byte] at h2
  simp at h2
  omega

/-! ## Soundness -/

theorem decodeBody_sound {item : List UInt8 → Option (RawItem × List UInt8)}
    (hitem : ∀ bs r rest, item bs = some (r, rest) → r.WF ∧ bs = r.encode ++ rest)
    {fuel : Nat} {h : Head} (hv : h.Valid) {bs : List UInt8} {r : RawItem} {rest : List UInt8}
    (hb : decodeBody item fuel h bs = some (r, rest)) :
    r.WF ∧ h.bytes ++ bs = r.encode ++ rest := by
  cases h with
  | arg m w n =>
    obtain ⟨hm, hfit⟩ := hv
    match m, hm with
    | 0, _ =>
      simp only [decodeBody, Option.some.injEq, Prod.mk.injEq] at hb
      obtain ⟨rfl, rfl⟩ := hb
      exact ⟨hfit, rfl⟩
    | 1, _ =>
      simp only [decodeBody, Option.some.injEq, Prod.mk.injEq] at hb
      obtain ⟨rfl, rfl⟩ := hb
      exact ⟨hfit, rfl⟩
    | 2, _ =>
      simp only [decodeBody] at hb
      split at hb
      · rename_i hn
        simp only [Option.some.injEq, Prod.mk.injEq] at hb
        obtain ⟨rfl, rfl⟩ := hb
        have hlen : (bs.take n).length = n := by simp; omega
        refine ⟨by simp only [RawItem.WF, hlen]; exact hfit, ?_⟩
        simp [RawItem.encode, Head.bytes, hlen]
      · simp at hb
    | 3, _ =>
      simp only [decodeBody] at hb
      split at hb
      · rename_i hn
        simp only [Option.some.injEq, Prod.mk.injEq] at hb
        obtain ⟨rfl, rfl⟩ := hb
        have hlen : (bs.take n).length = n := by simp; omega
        refine ⟨by simp only [RawItem.WF, hlen]; exact hfit, ?_⟩
        simp [RawItem.encode, Head.bytes, hlen]
      · simp at hb
    | 4, _ =>
      simp only [decodeBody] at hb
      split at hb
      · simp at hb
      · rename_i xs rest' hc
        simp only [Option.some.injEq, Prod.mk.injEq] at hb
        obtain ⟨rfl, rfl⟩ := hb
        obtain ⟨hlen, hwf, rfl⟩ := decodeCount_sound hitem _ _ _ _ hc
        refine ⟨⟨by rw [hlen]; exact hfit, (RawItem.WFList_iff xs).2 hwf⟩, ?_⟩
        simp [RawItem.encode, Head.bytes, hlen, RawItem.encodeList_eq]
    | 5, _ =>
      simp only [decodeBody] at hb
      split at hb
      · simp at hb
      · rename_i kvs rest' hc
        simp only [Option.some.injEq, Prod.mk.injEq] at hb
        obtain ⟨rfl, rfl⟩ := hb
        obtain ⟨hlen, hwf, rfl⟩ := decodeCount_sound
          (fun bs kv rest h => decodePair_sound hitem h) _ _ _ _ hc
        refine ⟨⟨by rw [hlen]; exact hfit, (RawItem.WFPairs_iff kvs).2 hwf⟩, ?_⟩
        simp [RawItem.encode, Head.bytes, hlen, RawItem.encodePairs_eq]
    | 6, _ =>
      simp only [decodeBody] at hb
      split at hb
      · simp at hb
      · rename_i x rest' hx
        simp only [Option.some.injEq, Prod.mk.injEq] at hb
        obtain ⟨rfl, rfl⟩ := hb
        obtain ⟨hwf, rfl⟩ := hitem _ _ _ hx
        exact ⟨⟨hfit, hwf⟩, by simp [RawItem.encode, Head.bytes]⟩
    | _ + 7, hm => omega
  | indef m =>
    obtain ⟨h2, h5⟩ := hv
    match m, h2, h5 with
    | 2, _, _ =>
      simp only [decodeBody] at hb
      split at hb
      · simp at hb
      · rename_i cs rest' hc
        simp only [Option.some.injEq, Prod.mk.injEq] at hb
        obtain ⟨rfl, rfl⟩ := hb
        obtain ⟨hwf, rfl⟩ := decodeUntilBreak_sound
          (fun bs c rest h => decodeChunk_sound h) _ _ _ _ hc
        exact ⟨hwf, by simp [RawItem.encode, Head.bytes, encodeChunks_eq]⟩
    | 3, _, _ =>
      simp only [decodeBody] at hb
      split at hb
      · simp at hb
      · rename_i cs rest' hc
        simp only [Option.some.injEq, Prod.mk.injEq] at hb
        obtain ⟨rfl, rfl⟩ := hb
        obtain ⟨hwf, rfl⟩ := decodeUntilBreak_sound
          (fun bs c rest h => decodeChunk_sound h) _ _ _ _ hc
        exact ⟨hwf, by simp [RawItem.encode, Head.bytes, encodeChunks_eq]⟩
    | 4, _, _ =>
      simp only [decodeBody] at hb
      split at hb
      · simp at hb
      · rename_i xs rest' hc
        simp only [Option.some.injEq, Prod.mk.injEq] at hb
        obtain ⟨rfl, rfl⟩ := hb
        obtain ⟨hwf, rfl⟩ := decodeUntilBreak_sound hitem _ _ _ _ hc
        exact ⟨(RawItem.WFList_iff xs).2 hwf,
          by simp [RawItem.encode, Head.bytes, RawItem.encodeList_eq]⟩
    | 5, _, _ =>
      simp only [decodeBody] at hb
      split at hb
      · simp at hb
      · rename_i kvs rest' hc
        simp only [Option.some.injEq, Prod.mk.injEq] at hb
        obtain ⟨rfl, rfl⟩ := hb
        obtain ⟨hwf, rfl⟩ := decodeUntilBreak_sound
          (fun bs kv rest h => decodePair_sound hitem h) _ _ _ _ hc
        exact ⟨(RawItem.WFPairs_iff kvs).2 hwf,
          by simp [RawItem.encode, Head.bytes, RawItem.encodePairs_eq]⟩
  | brk => simp [decodeBody] at hb
  | simple v =>
    simp only [decodeBody, Option.some.injEq, Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    exact ⟨hv, rfl⟩

/-- Soundness: the decoder returns only well-formed trees, and the consumed
prefix is exactly the tree's encoding. -/
theorem decodeRaw_sound : ∀ fuel bs r rest, decodeRaw fuel bs = some (r, rest) →
    r.WF ∧ bs = r.encode ++ rest := by
  intro fuel
  induction fuel with
  | zero => intro bs r rest h; simp [decodeRaw] at h
  | succ fuel ih =>
    intro bs r rest h
    simp only [decodeRaw] at h
    split at h
    · simp at h
    · rename_i hd0 rest0 hd
      obtain ⟨hv, rfl⟩ := decodeHead_sound hd
      exact decodeBody_sound ih hv h

/-! ## Completeness -/

theorem encodeHead_first {m : Nat} {w : Width} {n : Nat} (h : m * 32 + w.ai n < 255) :
    ∃ b t, encodeHead m w n = b :: t ∧ b ≠ 0xff := by
  refine ⟨_, _, rfl, ?_⟩
  intro hb
  have h2 := congrArg UInt8.toNat hb
  rw [toNat_ofNat_byte] at h2
  simp at h2
  omega

/-- No well-formed item starts with the break stop code (§3.2.1: "break" is
not itself a data item). -/
theorem RawItem.encode_first {r : RawItem} (hr : r.WF) :
    ∃ b t, r.encode = b :: t ∧ b ≠ 0xff := by
  cases r with
  | uint w n => exact encodeHead_first (by have := Width.ai_lt hr; omega)
  | nint w n => exact encodeHead_first (by have := Width.ai_lt hr; omega)
  | bytes w p =>
    obtain ⟨b, t, h, hb⟩ := encodeHead_first (m := 2) (w := w) (n := p.length)
      (by have := Width.ai_lt hr; omega)
    exact ⟨b, t ++ p, by simp [RawItem.encode, h], hb⟩
  | text w p =>
    obtain ⟨b, t, h, hb⟩ := encodeHead_first (m := 3) (w := w) (n := p.length)
      (by have := Width.ai_lt hr; omega)
    exact ⟨b, t ++ p, by simp [RawItem.encode, h], hb⟩
  | bytesIndef cs => exact ⟨_, _, rfl, by decide⟩
  | textIndef cs => exact ⟨_, _, rfl, by decide⟩
  | array w xs =>
    obtain ⟨b, t, h, hb⟩ := encodeHead_first (m := 4) (w := w) (n := xs.length)
      (by have := Width.ai_lt hr.1; omega)
    exact ⟨b, t ++ RawItem.encodeList xs, by simp [RawItem.encode, h], hb⟩
  | arrayIndef xs => exact ⟨_, _, rfl, by decide⟩
  | map w kvs =>
    obtain ⟨b, t, h, hb⟩ := encodeHead_first (m := 5) (w := w) (n := kvs.length)
      (by have := Width.ai_lt hr.1; omega)
    exact ⟨b, t ++ RawItem.encodePairs kvs, by simp [RawItem.encode, h], hb⟩
  | mapIndef kvs => exact ⟨_, _, rfl, by decide⟩
  | tag w t x =>
    obtain ⟨b, t', h, hb⟩ := encodeHead_first (m := 6) (w := w) (n := t)
      (by have := Width.ai_lt hr.1; omega)
    exact ⟨b, t' ++ x.encode, by simp [RawItem.encode, h], hb⟩
  | simple v =>
    apply encodeHead_first
    simp only [RawItem.WF] at hr
    simp only [simpleWidth]
    split <;> simp [Width.ai] <;> omega

theorem RawItem.encode_ne_nil {r : RawItem} (hr : r.WF) : r.encode ≠ [] := by
  obtain ⟨b, t, h, _⟩ := RawItem.encode_first hr
  simp [h]

theorem decodeRaw_of_head {fuel : Nat} {bs rest : List UInt8} {h : Head}
    (hd : decodeHead bs = some (h, rest)) :
    decodeRaw (fuel + 1) bs = decodeBody (decodeRaw fuel) fuel h rest := by
  simp [decodeRaw, hd]

theorem decodeRaw_arg {fuel m : Nat} {w : Width} {n : Nat} (hm : m ≤ 6) (hf : w.fits n = true)
    (rest : List UInt8) :
    decodeRaw (fuel + 1) (encodeHead m w n ++ rest) =
      decodeBody (decodeRaw fuel) fuel (.arg m w n) rest :=
  decodeRaw_of_head (decodeHead_bytes (h := .arg m w n) ⟨hm, hf⟩ rest)

/-- Completeness: every well-formed tree is decoded back from its encoding
followed by arbitrary bytes, whenever the fuel exceeds the encoding's length. -/
theorem decodeRaw_complete : ∀ fuel (r : RawItem) (rest : List UInt8), r.WF →
    r.encode.length < fuel → decodeRaw fuel (r.encode ++ rest) = some (r, rest) := by
  intro fuel
  induction fuel with
  | zero => intro r rest _ h; omega
  | succ fuel ih =>
    intro r rest hwf hlen
    cases r with
    | uint w n =>
      rw [RawItem.encode, decodeRaw_arg (by omega) hwf rest]
      rfl
    | nint w n =>
      rw [RawItem.encode, decodeRaw_arg (by omega) hwf rest]
      rfl
    | bytes w p =>
      rw [RawItem.encode, List.append_assoc, decodeRaw_arg (by omega) hwf (p ++ rest)]
      simp [decodeBody]
    | text w p =>
      rw [RawItem.encode, List.append_assoc, decodeRaw_arg (by omega) hwf (p ++ rest)]
      simp [decodeBody]
    | bytesIndef cs =>
      have hd := decodeHead_bytes (h := .indef 2) ⟨by omega, by omega⟩
        (RawItem.encodeChunks 2 cs ++ 0xff :: rest)
      have hb : (Head.indef 2).bytes = [0x5f] := rfl
      rw [hb] at hd
      simp only [RawItem.encode, List.cons_append, List.append_assoc, List.nil_append] at hlen ⊢
      rw [decodeRaw_of_head (by simpa using hd)]
      simp only [RawItem.WF] at hwf
      have hlen' : cs.length < fuel := by
        have := length_le_flatten cs (f := chunkEnc 2) (fun c hc => by
          obtain ⟨b, t, h, _⟩ := chunkEnc_first (m := 2) (by omega) (hwf c hc); simp [h])
        rw [encodeChunks_eq] at hlen
        simp only [List.length_cons, List.length_append] at hlen
        omega
      rw [encodeChunks_eq, decodeBody, decodeUntilBreak_complete cs
        (fun c hc rest => decodeChunk_complete (by omega) (hwf c hc) rest)
        (fun c hc => chunkEnc_first (by omega) (hwf c hc)) fuel hlen' rest]
    | textIndef cs =>
      have hd := decodeHead_bytes (h := .indef 3) ⟨by omega, by omega⟩
        (RawItem.encodeChunks 3 cs ++ 0xff :: rest)
      have hb : (Head.indef 3).bytes = [0x7f] := rfl
      rw [hb] at hd
      simp only [RawItem.encode, List.cons_append, List.append_assoc, List.nil_append] at hlen ⊢
      rw [decodeRaw_of_head (by simpa using hd)]
      simp only [RawItem.WF] at hwf
      have hlen' : cs.length < fuel := by
        have := length_le_flatten cs (f := chunkEnc 3) (fun c hc => by
          obtain ⟨b, t, h, _⟩ := chunkEnc_first (m := 3) (by omega) (hwf c hc); simp [h])
        rw [encodeChunks_eq] at hlen
        simp only [List.length_cons, List.length_append] at hlen
        omega
      rw [encodeChunks_eq, decodeBody, decodeUntilBreak_complete cs
        (fun c hc rest => decodeChunk_complete (by omega) (hwf c hc) rest)
        (fun c hc => chunkEnc_first (by omega) (hwf c hc)) fuel hlen' rest]
    | array w xs =>
      obtain ⟨hfit, hxs⟩ := hwf
      rw [RawItem.WFList_iff] at hxs
      rw [RawItem.encode, List.append_assoc, decodeRaw_arg (by omega) hfit]
      simp only [RawItem.encode, List.length_append, encodeHead_length, RawItem.encodeList_eq]
        at hlen
      rw [RawItem.encodeList_eq, decodeBody, decodeCount_complete xs (fun x hx rest' =>
        ih x rest' (hxs x hx) (by have := length_le_flatten_of_mem (f := RawItem.encode) hx; omega))
        rest]
    | arrayIndef xs =>
      rw [RawItem.WF, RawItem.WFList_iff] at hwf
      have hd := decodeHead_bytes (h := .indef 4) ⟨by omega, by omega⟩
        (RawItem.encodeList xs ++ 0xff :: rest)
      have hb : (Head.indef 4).bytes = [0x9f] := rfl
      rw [hb] at hd
      simp only [RawItem.encode, List.cons_append, List.append_assoc, List.nil_append] at hlen ⊢
      rw [decodeRaw_of_head (by simpa using hd)]
      simp only [RawItem.encodeList_eq, List.length_cons, List.length_append] at hlen
      have hlen' : xs.length < fuel := by
        have := length_le_flatten xs (f := RawItem.encode) (fun x hx => RawItem.encode_ne_nil (hwf x hx))
        omega
      rw [RawItem.encodeList_eq, decodeBody, decodeUntilBreak_complete xs
        (fun x hx rest' => ih x rest' (hwf x hx)
          (by have := length_le_flatten_of_mem (f := RawItem.encode) hx; omega))
        (fun x hx => RawItem.encode_first (hwf x hx)) fuel hlen' rest]
    | map w kvs =>
      obtain ⟨hfit, hkvs⟩ := hwf
      rw [RawItem.WFPairs_iff] at hkvs
      rw [RawItem.encode, List.append_assoc, decodeRaw_arg (by omega) hfit]
      simp only [RawItem.encode, List.length_append, encodeHead_length, RawItem.encodePairs_eq]
        at hlen
      rw [RawItem.encodePairs_eq, decodeBody, decodeCount_complete kvs (fun kv hkv rest' => by
        have hle := length_le_flatten_of_mem (f := fun kv => kv.1.encode ++ kv.2.encode) hkv
        simp only [List.length_append] at hle
        exact decodePair_complete (enc := RawItem.encode)
          (fun r => ih kv.1 r (hkvs kv hkv).1 (by omega))
          (fun r => ih kv.2 r (hkvs kv hkv).2 (by omega)) rest') rest]
    | mapIndef kvs =>
      rw [RawItem.WF, RawItem.WFPairs_iff] at hwf
      have hd := decodeHead_bytes (h := .indef 5) ⟨by omega, by omega⟩
        (RawItem.encodePairs kvs ++ 0xff :: rest)
      have hb : (Head.indef 5).bytes = [0xbf] := rfl
      rw [hb] at hd
      simp only [RawItem.encode, List.cons_append, List.append_assoc, List.nil_append] at hlen ⊢
      rw [decodeRaw_of_head (by simpa using hd)]
      simp only [RawItem.encodePairs_eq, List.length_cons, List.length_append] at hlen
      have hlen' : kvs.length < fuel := by
        have := length_le_flatten kvs (f := fun kv => kv.1.encode ++ kv.2.encode)
          (fun kv hkv => by simp [RawItem.encode_ne_nil (hwf kv hkv).1])
        omega
      rw [RawItem.encodePairs_eq, decodeBody, decodeUntilBreak_complete kvs
        (fun kv hkv rest' => by
          have hle := length_le_flatten_of_mem (f := fun kv => kv.1.encode ++ kv.2.encode) hkv
          simp only [List.length_append] at hle
          exact decodePair_complete (enc := RawItem.encode)
            (fun r => ih kv.1 r (hwf kv hkv).1 (by omega))
            (fun r => ih kv.2 r (hwf kv hkv).2 (by omega)) rest')
        (fun kv hkv => by
          obtain ⟨b, t, h, hb⟩ := RawItem.encode_first (hwf kv hkv).1
          exact ⟨b, t ++ kv.2.encode, by simp [h], hb⟩) fuel hlen' rest]
    | tag w t x =>
      obtain ⟨hfit, hx⟩ := hwf
      rw [RawItem.encode, List.append_assoc, decodeRaw_arg (by omega) hfit]
      simp only [RawItem.encode, List.length_append, encodeHead_length] at hlen
      simp [decodeBody, ih x rest hx (by omega)]
    | simple v =>
      have hd := decodeHead_bytes (h := .simple v) hwf rest
      simp only [Head.bytes] at hd
      rw [RawItem.encode, decodeRaw_of_head hd]
      rfl

/-! ## Exact characterizations -/

theorem decodeRaw_eq_some_iff {fuel : Nat} {bs : List UInt8} (hf : bs.length < fuel)
    {r : RawItem} {rest : List UInt8} :
    decodeRaw fuel bs = some (r, rest) ↔ r.WF ∧ bs = r.encode ++ rest := by
  constructor
  · exact decodeRaw_sound fuel bs r rest
  · rintro ⟨hwf, rfl⟩
    exact decodeRaw_complete fuel r rest hwf (by simp at hf; omega)

/-- `decodePrefixRaw` reads exactly one well-formed tree from the front. -/
theorem decodePrefixRaw_eq_some_iff {bs : List UInt8} {r : RawItem} {rest : List UInt8} :
    decodePrefixRaw bs = some (r, rest) ↔ r.WF ∧ bs = r.encode ++ rest :=
  decodeRaw_eq_some_iff (Nat.lt_succ_self _)

/-- **Grammar characterization.** `parseRaw bs = some r` exactly when `r` is a
well-formed tree whose encoding is the whole input. -/
theorem parseRaw_eq_some_iff {bs : List UInt8} {r : RawItem} :
    parseRaw bs = some r ↔ r.WF ∧ r.encode = bs := by
  unfold parseRaw
  constructor
  · intro h
    split at h
    · rename_i r' h'
      simp only [Option.some.injEq] at h
      subst h
      obtain ⟨hwf, hbs⟩ := decodePrefixRaw_eq_some_iff.1 h'
      exact ⟨hwf, by simpa using hbs.symm⟩
    · simp at h
  · rintro ⟨hwf, rfl⟩
    have := decodePrefixRaw_eq_some_iff (bs := r.encode) (r := r) (rest := []) |>.2 ⟨hwf, by simp⟩
    rw [this]

/-- Fuel irrelevance: any fuel above the input length gives exactly the
answer of the initial fuel `bs.length + 1` (I5); the fuel never truncates
the grammar. -/
theorem decodeRaw_of_length_lt {fuel : Nat} {bs : List UInt8} (hf : bs.length < fuel) :
    decodeRaw fuel bs = decodePrefixRaw bs := by
  cases h : decodeRaw fuel bs with
  | none =>
    cases h' : decodePrefixRaw bs with
    | none => rfl
    | some p =>
      obtain ⟨r, rest⟩ := p
      obtain ⟨hwf, hbs⟩ := decodePrefixRaw_eq_some_iff.1 h'
      rw [(decodeRaw_eq_some_iff hf).2 ⟨hwf, hbs⟩] at h
      simp at h
  | some p =>
    obtain ⟨r, rest⟩ := p
    obtain ⟨hwf, hbs⟩ := decodeRaw_sound _ _ _ _ h
    exact (decodePrefixRaw_eq_some_iff.2 ⟨hwf, hbs⟩).symm

/-- A run with any fuel that succeeds agrees with the canonical run: less
fuel can only fail, never disagree. -/
theorem decodePrefixRaw_of_decodeRaw {fuel : Nat} {bs : List UInt8} {p : RawItem × List UInt8}
    (h : decodeRaw fuel bs = some p) : decodePrefixRaw bs = some p := by
  obtain ⟨r, rest⟩ := p
  obtain ⟨hwf, hbs⟩ := decodeRaw_sound _ _ _ _ h
  exact decodePrefixRaw_eq_some_iff.2 ⟨hwf, hbs⟩

/-- Well-formed encodings are prefix-free (the self-delimiting property used by
the §4.2.1 implementation note): two well-formed trees whose encodings start
two equal byte strings are equal, and so are the remainders. -/
theorem RawItem.encode_prefix_unique {r₁ r₂ : RawItem} (h₁ : r₁.WF) (h₂ : r₂.WF)
    {rest₁ rest₂ : List UInt8} (h : r₁.encode ++ rest₁ = r₂.encode ++ rest₂) :
    r₁ = r₂ ∧ rest₁ = rest₂ := by
  have e₁ : decodePrefixRaw (r₁.encode ++ rest₁) = some (r₁, rest₁) :=
    decodePrefixRaw_eq_some_iff.2 ⟨h₁, rfl⟩
  have e₂ : decodePrefixRaw (r₁.encode ++ rest₁) = some (r₂, rest₂) :=
    decodePrefixRaw_eq_some_iff.2 ⟨h₂, h⟩
  rw [e₁] at e₂
  simp only [Option.some.injEq, Prod.mk.injEq] at e₂
  exact e₂

theorem RawItem.encode_injective {r₁ r₂ : RawItem} (h₁ : r₁.WF) (h₂ : r₂.WF)
    (h : r₁.encode = r₂.encode) : r₁ = r₂ :=
  (RawItem.encode_prefix_unique h₁ h₂ (rest₁ := []) (rest₂ := []) (by simp [h])).1

/-- **Well-formedness characterization.** `parseWellFormed bs = some x`
exactly when `bs` is the encoding of a well-formed float-free tree whose
item is `x`. -/
theorem parseWellFormed_eq_some_iff {bs : List UInt8} {x : Item} :
    parseWellFormed bs = some x ↔ ∃ r : RawItem, r.WF ∧ r.encode = bs ∧ r.toItem = x := by
  unfold parseWellFormed
  constructor
  · intro h
    split at h
    · rename_i r hr
      simp only [Option.some.injEq] at h
      obtain ⟨hwf, henc⟩ := parseRaw_eq_some_iff.1 hr
      exact ⟨r, hwf, henc, h⟩
    · simp at h
  · rintro ⟨r, hwf, rfl, rfl⟩
    rw [parseRaw_eq_some_iff.2 ⟨hwf, rfl⟩]

theorem parseWellFormed_eq_none_iff {bs : List UInt8} :
    parseWellFormed bs = none ↔ ¬ ∃ r : RawItem, r.WF ∧ r.encode = bs := by
  constructor
  · rintro h ⟨r, hwf, henc⟩
    have := parseWellFormed_eq_some_iff.2 ⟨r, hwf, henc, rfl⟩
    rw [h] at this
    simp at this
  · intro h
    cases hp : parseWellFormed bs with
    | none => rfl
    | some x =>
      obtain ⟨r, hwf, henc, _⟩ := parseWellFormed_eq_some_iff.1 hp
      exact absurd ⟨r, hwf, henc⟩ h

/-- `decodePrefix` reads one well-formed item and returns exactly the unread
bytes. -/
theorem decodePrefix_eq_some_iff {bs : List UInt8} {x : Item} {rest : List UInt8} :
    decodePrefix bs = some (x, rest) ↔
      ∃ r : RawItem, r.WF ∧ bs = r.encode ++ rest ∧ r.toItem = x := by
  unfold decodePrefix
  constructor
  · intro h
    split at h
    · rename_i r rest' hr
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨hwf, hbs⟩ := decodePrefixRaw_eq_some_iff.1 hr
      exact ⟨r, hwf, hbs, rfl⟩
    · simp at h
  · rintro ⟨r, hwf, rfl, rfl⟩
    rw [decodePrefixRaw_eq_some_iff.2 ⟨hwf, rfl⟩]

/-! ## The preferred encoder -/

theorem Width.preferred_fits {n : Nat} (h : n < 2 ^ 64) : (Width.preferred n).fits n = true := by
  unfold Width.preferred
  split
  · simp [Width.fits, *]
  · split
    · simp [Width.fits, *]
    · split
      · simp [Width.fits, *]
      · split
        · simp [Width.fits, *]
        · simp [Width.fits, h]

theorem Item.toRaw_toItem (x : Item) : x.toRaw.toItem = x := by
  induction x using Item.rec' with
  | uint n => rfl
  | nint n => rfl
  | bytes p => rfl
  | text p => rfl
  | bytesIndef cs => simp [Item.toRaw, RawItem.toItem, Function.comp_def]
  | textIndef cs => simp [Item.toRaw, RawItem.toItem, Function.comp_def]
  | array xs ih =>
    simp only [Item.toRaw, RawItem.toItem, RawItem.toItemList_eq, Item.toRawList_eq, List.map_map]
    congr 1
    exact (List.map_congr_left fun x hx => ih x hx).trans (List.map_id _)
  | arrayIndef xs ih =>
    simp only [Item.toRaw, RawItem.toItem, RawItem.toItemList_eq, Item.toRawList_eq, List.map_map]
    congr 1
    exact (List.map_congr_left fun x hx => ih x hx).trans (List.map_id _)
  | map kvs ih =>
    simp only [Item.toRaw, RawItem.toItem, RawItem.toItemPairs_eq, Item.toRawPairs_eq, List.map_map]
    congr 1
    refine (List.map_congr_left fun kv hkv => ?_).trans (List.map_id _)
    simp [(ih kv hkv).1, (ih kv hkv).2]
  | mapIndef kvs ih =>
    simp only [Item.toRaw, RawItem.toItem, RawItem.toItemPairs_eq, Item.toRawPairs_eq, List.map_map]
    congr 1
    refine (List.map_congr_left fun kv hkv => ?_).trans (List.map_id _)
    simp [(ih kv hkv).1, (ih kv hkv).2]
  | tag t x ih => simp [Item.toRaw, RawItem.toItem, ih]
  | simple v => rfl

theorem Item.WF_toRaw {x : Item} (hx : x.WF) : x.toRaw.WF := by
  induction x using Item.rec' with
  | uint n => exact Width.preferred_fits hx
  | nint n => exact Width.preferred_fits hx
  | bytes p => exact Width.preferred_fits hx
  | text p => exact Width.preferred_fits hx
  | bytesIndef cs =>
    simp only [Item.toRaw, RawItem.WF, List.mem_map]
    rintro _ ⟨c, hc, rfl⟩
    exact Width.preferred_fits (hx c hc)
  | textIndef cs =>
    simp only [Item.toRaw, RawItem.WF, List.mem_map]
    rintro _ ⟨c, hc, rfl⟩
    exact Width.preferred_fits (hx c hc)
  | array xs ih =>
    obtain ⟨hlen, hxs⟩ := hx
    rw [Item.WFList_iff] at hxs
    refine ⟨by rw [Item.toRawList_eq, List.length_map]; exact Width.preferred_fits hlen, ?_⟩
    rw [RawItem.WFList_iff, Item.toRawList_eq]
    simp only [List.mem_map]
    rintro _ ⟨x, hx, rfl⟩
    exact ih x hx (hxs x hx)
  | arrayIndef xs ih =>
    simp only [Item.WF, Item.WFList_iff] at hx
    show RawItem.WFList _
    rw [RawItem.WFList_iff, Item.toRawList_eq]
    simp only [List.mem_map]
    rintro _ ⟨x, hx', rfl⟩
    exact ih x hx' (hx x hx')
  | map kvs ih =>
    obtain ⟨hlen, hkvs⟩ := hx
    rw [Item.WFPairs_iff] at hkvs
    refine ⟨by rw [Item.toRawPairs_eq, List.length_map]; exact Width.preferred_fits hlen, ?_⟩
    rw [RawItem.WFPairs_iff, Item.toRawPairs_eq]
    simp only [List.mem_map]
    rintro _ ⟨kv, hkv, rfl⟩
    exact ⟨(ih kv hkv).1 (hkvs kv hkv).1, (ih kv hkv).2 (hkvs kv hkv).2⟩
  | mapIndef kvs ih =>
    simp only [Item.WF, Item.WFPairs_iff] at hx
    show RawItem.WFPairs _
    rw [RawItem.WFPairs_iff, Item.toRawPairs_eq]
    simp only [List.mem_map]
    rintro _ ⟨kv, hkv, rfl⟩
    exact ⟨(ih kv hkv).1 (hx kv hkv).1, (ih kv hkv).2 (hx kv hkv).2⟩
  | tag t x ih => exact ⟨Width.preferred_fits hx.1, ih hx.2⟩
  | simple v => exact hx

theorem Width.fits_lt_two_pow {w : Width} {n : Nat} (h : w.fits n = true) : n < 2 ^ 64 := by
  cases w <;> simp only [Width.fits, decide_eq_true_eq] at h <;> omega

theorem RawItem.WF_toItem {r : RawItem} (hr : r.WF) : r.toItem.WF := by
  induction r using RawItem.rec' with
  | uint w n => exact Width.fits_lt_two_pow hr
  | nint w n => exact Width.fits_lt_two_pow hr
  | bytes w p => exact Width.fits_lt_two_pow hr
  | text w p => exact Width.fits_lt_two_pow hr
  | bytesIndef cs =>
    simp only [RawItem.toItem, Item.WF, List.mem_map]
    rintro _ ⟨c, hc, rfl⟩
    exact Width.fits_lt_two_pow (hr c hc)
  | textIndef cs =>
    simp only [RawItem.toItem, Item.WF, List.mem_map]
    rintro _ ⟨c, hc, rfl⟩
    exact Width.fits_lt_two_pow (hr c hc)
  | array w xs ih =>
    obtain ⟨hlen, hxs⟩ := hr
    rw [RawItem.WFList_iff] at hxs
    refine ⟨by rw [RawItem.toItemList_eq, List.length_map]; exact Width.fits_lt_two_pow hlen, ?_⟩
    rw [Item.WFList_iff, RawItem.toItemList_eq]
    simp only [List.mem_map]
    rintro _ ⟨x, hx, rfl⟩
    exact ih x hx (hxs x hx)
  | arrayIndef xs ih =>
    simp only [RawItem.WF, RawItem.WFList_iff] at hr
    show Item.WFList _
    rw [Item.WFList_iff, RawItem.toItemList_eq]
    simp only [List.mem_map]
    rintro _ ⟨x, hx, rfl⟩
    exact ih x hx (hr x hx)
  | map w kvs ih =>
    obtain ⟨hlen, hkvs⟩ := hr
    rw [RawItem.WFPairs_iff] at hkvs
    refine ⟨by rw [RawItem.toItemPairs_eq, List.length_map]; exact Width.fits_lt_two_pow hlen, ?_⟩
    rw [Item.WFPairs_iff, RawItem.toItemPairs_eq]
    simp only [List.mem_map]
    rintro _ ⟨kv, hkv, rfl⟩
    exact ⟨(ih kv hkv).1 (hkvs kv hkv).1, (ih kv hkv).2 (hkvs kv hkv).2⟩
  | mapIndef kvs ih =>
    simp only [RawItem.WF, RawItem.WFPairs_iff] at hr
    show Item.WFPairs _
    rw [Item.WFPairs_iff, RawItem.toItemPairs_eq]
    simp only [List.mem_map]
    rintro _ ⟨kv, hkv, rfl⟩
    exact ⟨(ih kv hkv).1 (hr kv hkv).1, (ih kv hkv).2 (hr kv hkv).2⟩
  | tag w t x ih => exact ⟨Width.fits_lt_two_pow hr.1, ih hr.2⟩
  | simple v => exact hr

/-- Everything `parseWellFormed` returns is a well-formed item. -/
theorem parseWellFormed_WF {bs : List UInt8} {x : Item} (h : parseWellFormed bs = some x) :
    x.WF := by
  obtain ⟨r, hwf, _, rfl⟩ := parseWellFormed_eq_some_iff.1 h
  exact RawItem.WF_toItem hwf

/-- Round trip through the preferred encoder. -/
theorem parseWellFormed_encodePreferred {x : Item} (hx : x.WF) :
    parseWellFormed (encodePreferred x) = some x :=
  parseWellFormed_eq_some_iff.2 ⟨x.toRaw, Item.WF_toRaw hx, rfl, Item.toRaw_toItem x⟩

theorem decodePrefix_encodePreferred {x : Item} (hx : x.WF) (rest : List UInt8) :
    decodePrefix (encodePreferred x ++ rest) = some (x, rest) :=
  decodePrefix_eq_some_iff.2 ⟨x.toRaw, Item.WF_toRaw hx, rfl, Item.toRaw_toItem x⟩

/-- An item is well-formed exactly when it has an encoding. -/
theorem Item.WF_iff_exists_encoding {x : Item} :
    x.WF ↔ ∃ bs, parseWellFormed bs = some x :=
  ⟨fun hx => ⟨_, parseWellFormed_encodePreferred hx⟩, fun ⟨_, h⟩ => parseWellFormed_WF h⟩

end Cbor.Rfc8949
