import UriRfc3986.Components
import UriRfc3986.Examples

/-!
# RFC 3986 §5.2 reference resolution

The helpers below use `List Char`, retaining empty segments and every slash.
The two buffer representations follow §5.2.4's implementation note verbatim:
"Some applications may find it more efficient to implement the
remove_dot_segments algorithm by using two segment stacks rather than
strings." The input keeps its pending leading slash; the output records
whether its first emitted segment had one. In particular this representation
retains the RFC buffer behavior on rootless paths.
-/

deriving instance DecidableEq, Repr for Components

/-- RFC 3986 §5.2.4, rule E: "up to, but not including, the next "/"
character or the end of the input buffer." Split at those delimiters, keeping
both leading and trailing empty segments. -/
def splitSlash : List Char → List (List Char)
  | [] => [[]]
  | c :: cs =>
    if c = '/' then [] :: splitSlash cs
    else match splitSlash cs with
      | [] => [[c]]
      | s :: ss => (c :: s) :: ss

/-- RFC 3986 §5.2.4, rule E: "including the initial "/" character (if any)".
Restore exactly the delimiters retained by `splitSlash`. -/
def joinSlash : List (List Char) → List Char
  | [] => []
  | [s] => s
  | s :: t :: ss => s ++ '/' :: joinSlash (t :: ss)

/-- RFC 3986 §5.2.4: "a complete path segment"; even the empty path has one
empty segment under the delimiter-preserving convention. -/
theorem splitSlash_ne_nil (p : List Char) : splitSlash p ≠ [] := by
  cases p with
  | nil => simp [splitSlash]
  | cons c cs =>
    simp only [splitSlash]
    split
    · exact List.cons_ne_nil _ _
    · split <;> exact List.cons_ne_nil _ _

/-- RFC 3986 §5.2.4, rule E: "including the initial "/" character (if any)".
The delimiter-preserving representation is lossless. -/
theorem joinSlash_splitSlash (p : List Char) : joinSlash (splitSlash p) = p := by
  induction p with
  | nil => rfl
  | cons c cs ih =>
    simp only [splitSlash]
    split
    · rename_i h
      subst c
      cases hs : splitSlash cs with
      | nil => exact False.elim (splitSlash_ne_nil cs hs)
      | cons s ss => simpa [joinSlash, hs] using congrArg (List.cons '/') ih
    · cases hs : splitSlash cs with
      | nil => exact False.elim (splitSlash_ne_nil cs hs)
      | cons s ss =>
        cases ss <;> simp_all [joinSlash]

/-- RFC 3986 §5.2.4: "the next "/" character" is the segment delimiter. -/
@[simp] theorem splitSlash_slash (p : List Char) :
    splitSlash ('/' :: p) = [] :: splitSlash p := by simp [splitSlash]

/-- RFC 3986 §5.2.4: "the next "/" character" is the segment delimiter. -/
theorem splitSlash_cons (c : Char) (p : List Char) (h : c ≠ '/') :
    splitSlash (c :: p) = (c :: (splitSlash p).head!) :: (splitSlash p).tail := by
  cases hs : splitSlash p with
  | nil => exact False.elim (splitSlash_ne_nil p hs)
  | cons s ss => simp [splitSlash, h, hs, List.head!]

/-- RFC 3986 §5.2.4, rule E: "any subsequent characters up to, but not
including, the next "/" character" stay in the same segment. -/
theorem splitSlash_of_noSlash (p : List Char) (h : '/' ∉ p) :
    splitSlash p = [p] := by
  induction p with
  | nil => rfl
  | cons c cs ih =>
    have hc : c ≠ '/' := by intro he; subst c; exact h (by simp)
    have ht : '/' ∉ cs := by intro hm; exact h (by simp [hm])
    simp [splitSlash, hc, ih ht]

/-- RFC 3986 §5.2.4, rule E: "up to, but not including, the next "/"
character". A slash-free prefix is exactly the first complete segment. -/
theorem splitSlash_append_slash (p q : List Char) (h : '/' ∉ p) :
    splitSlash (p ++ '/' :: q) = p :: splitSlash q := by
  induction p with
  | nil => simp
  | cons c cs ih =>
    have hc : c ≠ '/' := by intro he; subst c; exact h (by simp)
    have ht : '/' ∉ cs := by intro hm; exact h (by simp [hm])
    simp [splitSlash, hc, ih ht]

/-- RFC 3986 §5.2.4, rule E: "up to, but not including, the next "/"
character". No individual segment contains its separator. -/
theorem noSlash_of_mem_splitSlash (p s : List Char) (h : s ∈ splitSlash p) :
    '/' ∉ s := by
  induction p generalizing s with
  | nil =>
    have he : s = [] := by simpa [splitSlash] using h
    subst s
    simp
  | cons c cs ih =>
    simp only [splitSlash] at h
    split at h
    · rcases List.mem_cons.mp h with rfl | hm
      · simp
      · exact ih s hm
    · rename_i hc
      cases hs : splitSlash cs with
      | nil => exact False.elim (splitSlash_ne_nil cs hs)
      | cons t ts =>
        simp only [hs] at h
        rcases List.mem_cons.mp h with rfl | hm
        · have ht := ih t (by simp [hs])
          simp only [List.mem_cons, not_or]
          exact ⟨Ne.symm hc, ht⟩
        · exact ih s (by simp [hs, hm])

/-- RFC 3986 §5.2.4, rule E: "including the initial "/" character (if any)".
Joining slash-free segments recovers the same segment list when nonempty. -/
theorem splitSlash_joinSlash (ss : List (List Char)) (hn : ss ≠ [])
    (h : ∀ s ∈ ss, '/' ∉ s) : splitSlash (joinSlash ss) = ss := by
  induction ss with
  | nil => contradiction
  | cons s ss ih =>
    cases ss with
    | nil => exact splitSlash_of_noSlash s (h s (by simp))
    | cons t ts =>
      simp only [joinSlash]
      rw [splitSlash_append_slash s _ (h s (by simp))]
      rw [ih (by simp) (by intro q hq; exact h q (by simp [hq]))]

/-- RFC 3986 §5.2.4: "The input buffer is initialized with the now-appended
path components and the output buffer is initialized to the empty string."
The input buffer stores its first segment and remaining slash-separated
segments; `absolute` records the first slash without consuming it. -/
inductive RdsInput where
  | empty
  | rootless (first : List Char) (rest : List (List Char))
  | absolute (first : List Char) (rest : List (List Char))
  deriving DecidableEq, Repr

/-- RFC 3986 §5.2.4: "including the initial "/" character (if any)". -/
def RdsInput.render : RdsInput → List Char
  | .empty => []
  | .rootless s ss => joinSlash (s :: ss)
  | .absolute s ss => '/' :: joinSlash (s :: ss)

/-- RFC 3986 §5.2.4: "The input buffer is initialized with the now-appended
path components". The delimiter-preserving split is only a representation
of that buffer, not a replacement segment-stack resolution algorithm. -/
def RdsInput.ofSegments : List (List Char) → RdsInput
  | [] => .empty
  | [] :: [] => .empty
  | [] :: s :: ss => .absolute s ss
  | s :: ss => .rootless s ss

/-- RFC 3986 §5.2.4, rule E: "up to, but not including, the next "/"
character". The remainder retains that slash. -/
def RdsInput.afterSlash : List (List Char) → RdsInput
  | [] => .empty
  | s :: ss => .absolute s ss

/-- RFC 3986 §5.2.4, rules B/C: "replace that prefix with "/" in the
input buffer". Even a terminal dot segment leaves one slash. -/
def RdsInput.replaceDot : List (List Char) → RdsInput
  | [] => .absolute [] []
  | s :: ss => .absolute s ss

/-- RFC 3986 §5.2.4: "the output buffer is initialized to the empty string."
Completed segments are stored in reverse order; `rooted` records the first
slash. An empty segment list renders the empty output buffer in either mode. -/
structure RdsOutput where
  rooted : Bool
  segments : List (List Char)
  deriving DecidableEq, Repr

/-- RFC 3986 §5.2.4: "Finally, the output buffer is returned". -/
def RdsOutput.render (o : RdsOutput) : List Char :=
  match o.segments with
  | [] => []
  | _ :: _ => if o.rooted then '/' :: joinSlash o.segments.reverse
              else joinSlash o.segments.reverse

/-- RFC 3986 §5.2.4, rule C: "remove the last segment and its preceding
"/" (if any) from the output buffer". -/
def RdsOutput.pop (o : RdsOutput) : RdsOutput :=
  { o with segments := o.segments.tail }

/-- RFC 3986 §5.2.4, rule E: "move the first path segment in the input
buffer to the end of the output buffer, including the initial "/"
character (if any)". -/
def RdsOutput.push (o : RdsOutput) (slash : Bool) (s : List Char) : RdsOutput :=
  if slash then
    { rooted := if o.segments.isEmpty then true else o.rooted
      segments := s :: o.segments }
  else
    match o.segments with
    | [] => { rooted := false, segments := [s] }
    | t :: ts => { o with segments := (t ++ s) :: ts }

/-- RFC 3986 §5.2.4 rules A–E, in order:

A. "If the input buffer begins with a prefix of "../" or "./", then
remove that prefix from the input buffer; otherwise,"
B. "if the input buffer begins with a prefix of "/./" or "/.", where
"." is a complete path segment, then replace that prefix with "/" in
the input buffer; otherwise,"
C. "if the input buffer begins with a prefix of "/../" or "/..", where
".." is a complete path segment, then replace that prefix with "/" in
the input buffer and remove the last segment and its preceding "/"
(if any) from the output buffer; otherwise,"
D. "if the input buffer consists only of "." or "..", then remove
that from the input buffer; otherwise,"
E. "move the first path segment in the input buffer to the end of the
output buffer, including the initial "/" character (if any) and any
subsequent characters up to, but not including, the next "/" character
or the end of the input buffer."

Segment boundaries encode the literal buffer; a transition consumes exactly
one RFC rule. A rootless dot segment uses A when `ss` is nonempty, or D
when `ss` is empty; B/C cannot match a rootless input. In particular, B/C
retain a final slash and C pops the entire last emitted segment, including
a rootless first segment. -/
def rdsNext (i : RdsInput) (o : RdsOutput) : RdsInput × RdsOutput :=
  match i with
  | .empty => (.empty, o)
  | .rootless s ss =>
    if s = ['.'] ∨ s = ['.', '.'] then
      (RdsInput.ofSegments ss, o)
    else (RdsInput.afterSlash ss, o.push false s)
  | .absolute s ss =>
    if s = ['.'] then (RdsInput.replaceDot ss, o)
    else if s = ['.', '.'] then (RdsInput.replaceDot ss, o.pop)
    else (RdsInput.afterSlash ss, o.push true s)

/-- RFC 3986 §5.2.4: "While the input buffer is not empty, loop as
follows". Fuel makes recursion structural; sufficiency is proved below. -/
def rdsStep : Nat → RdsInput → RdsOutput → RdsOutput
  | 0, _, o => o
  | n + 1, i, o =>
    match i with
    | .empty => o
    | _ => let next := rdsNext i o; rdsStep n next.1 next.2

/-- RFC 3986 §5.2.4: "The input buffer is initialized with the now-appended
path components and the output buffer is initialized to the empty string."
"Finally, the output buffer is returned as the result of remove_dot_segments."
The two buffers use a delimiter-preserving representation internally. -/
def removeDotSegments (p : List Char) : List Char :=
  (rdsStep (p.length + 2) (RdsInput.ofSegments (splitSlash p)) ⟨false, []⟩).render

/-- RFC 3986 §5.2.4: "While the input buffer is not empty, loop as follows".
Record the actual buffers before and after each RFC rule. -/
def rdsTraceStep : Nat → RdsInput → RdsOutput → List (List Char × List Char)
  | 0, i, o => [(o.render, i.render)]
  | n + 1, i, o =>
    match i with
    | .empty => [(o.render, [])]
    | _ => let next := rdsNext i o
           (o.render, i.render) :: rdsTraceStep n next.1 next.2

/-- RFC 3986 §5.2.4: "The following illustrates how the above steps are
applied for two examples of merged paths". -/
def rdsTrace (p : List Char) : List (List Char × List Char) :=
  rdsTraceStep (p.length + 2) (RdsInput.ofSegments (splitSlash p)) ⟨false, []⟩

/-- RFC 3986 §5.2.4 first official trace, verbatim:
```
      STEP   OUTPUT BUFFER         INPUT BUFFER

       1 :                         /a/b/c/./../../g
       2E:   /a                    /b/c/./../../g
       2E:   /a/b                  /c/./../../g
       2E:   /a/b/c                /./../../g
       2B:   /a/b/c                /../../g
       2C:   /a/b                  /../g
       2C:   /a                    /g
       2E:   /a/g
```
-/
theorem rds_trace_absolute : rdsTrace "/a/b/c/./../../g".toList =
    [("".toList, "/a/b/c/./../../g".toList),
     ("/a".toList, "/b/c/./../../g".toList),
     ("/a/b".toList, "/c/./../../g".toList),
     ("/a/b/c".toList, "/./../../g".toList),
     ("/a/b/c".toList, "/../../g".toList),
     ("/a/b".toList, "/../g".toList),
     ("/a".toList, "/g".toList), ("/a/g".toList, [])] := by decide

/-- RFC 3986 §5.2.4 second official trace, verbatim:
```
      STEP   OUTPUT BUFFER         INPUT BUFFER

       1 :                         mid/content=5/../6
       2E:   mid                   /content=5/../6
       2E:   mid/content=5         /../6
       2C:   mid                   /6
       2E:   mid/6
```
-/
theorem rds_trace_rootless : rdsTrace "mid/content=5/../6".toList =
    [("".toList, "mid/content=5/../6".toList),
     ("mid".toList, "/content=5/../6".toList),
     ("mid/content=5".toList, "/../6".toList),
     ("mid".toList, "/6".toList), ("mid/6".toList, [])] := by decide

/-- Beyond-RFC ground pin of §5.2.4 rule C: "remove the last segment and
its preceding "/" (if any) from the output buffer". -/
theorem rds_rootless_parent : removeDotSegments "a/../b".toList = "/b".toList := by decide

/-- Beyond-RFC ground pin of §5.2.4 rule C: "replace that prefix with
"/" in the input buffer". -/
theorem rds_rootless_parents : removeDotSegments "a/../..".toList = "/".toList := by decide

/-- Beyond-RFC ground pin of §5.2.4 rule A: "remove that prefix from the
input buffer". Repeated slashes survive literally. -/
theorem rds_rootless_doubleSlash : removeDotSegments ".///g".toList = "//g".toList := by decide

/-- RFC 3986 §5.2.4: "While the input buffer is not empty"; an empty
input therefore returns the initially empty output buffer. -/
@[simp] theorem removeDotSegments_nil : removeDotSegments [] = [] := by decide

/-- RFC 3986 §5.2.4: "any subsequent characters up to, but not including,
the next "/" character". Count those characters and separators. -/
def segmentSize : List (List Char) → Nat
  | [] => 0
  | s :: ss => s.length + 1 + segmentSize ss

/-- RFC 3986 §5.2.4: "While the input buffer is not empty". The measure
is precisely its character length, in its lossless buffer representation. -/
def RdsInput.size : RdsInput → Nat
  | .empty => 0
  | .rootless s ss => s.length + segmentSize ss
  | .absolute s ss => s.length + segmentSize ss + 1

/-- RFC 3986 §5.2.4, rule E: "including the initial "/" character (if
any)". A nonempty rootless buffer starts with a nonempty first segment. -/
def RdsInput.Valid : RdsInput → Prop
  | .rootless s _ => s ≠ []
  | _ => True

/-- RFC 3986 §5.2.4, rule E: "up to, but not including, the next "/"
character". This bookkeeping equality counts the preserved delimiters. -/
theorem joinSlash_cons_length (s : List Char) (ss : List (List Char)) :
    (joinSlash (s :: ss)).length = s.length + segmentSize ss := by
  induction ss generalizing s with
  | nil => simp [joinSlash, segmentSize]
  | cons t ts ih => simp [joinSlash, segmentSize, ih, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- RFC 3986 §5.2.4: "input buffer"; its measure is its literal length. -/
theorem RdsInput.size_eq_length (i : RdsInput) : i.size = i.render.length := by
  cases i <;> simp [size, render, joinSlash_cons_length, Nat.add_comm]

/-- RFC 3986 §5.2.4: "The input buffer is initialized with the now-appended
path components"; representation preserves those characters exactly. -/
theorem RdsInput.render_ofSegments (ss : List (List Char)) :
    (ofSegments ss).render = joinSlash ss := by
  cases ss with
  | nil => rfl
  | cons s ss =>
    cases s with
    | nil => cases ss <;> rfl
    | cons c cs => rfl

/-- RFC 3986 §5.2.4, rule E: "including the initial "/" character (if any)". -/
theorem RdsInput.valid_ofSegments (ss : List (List Char)) : (ofSegments ss).Valid := by
  cases ss with
  | nil => trivial
  | cons s ss => cases s with
    | nil => cases ss <;> trivial
    | cons c cs => exact List.cons_ne_nil _ _

/-- RFC 3986 §5.2.4, rule E: "up to, but not including, the next "/"
character". -/
theorem RdsInput.size_afterSlash (ss : List (List Char)) :
    (afterSlash ss).size = segmentSize ss := by
  cases ss <;> simp [afterSlash, size, segmentSize, Nat.add_assoc, Nat.add_comm]

/-- RFC 3986 §5.2.4, rules B/C: "replace that prefix with "/"". -/
theorem RdsInput.size_replaceDot_le (ss : List (List Char)) :
    (replaceDot ss).size ≤ segmentSize ss + 1 := by
  cases ss <;> simp [replaceDot, size, segmentSize, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- RFC 3986 §5.2.4, rule A: "remove that prefix from the input buffer". -/
theorem RdsInput.size_ofSegments_le (ss : List (List Char)) :
    (ofSegments ss).size ≤ segmentSize ss := by
  cases ss with
  | nil => simp [ofSegments, size, segmentSize]
  | cons s ss =>
    cases s with
    | nil => cases ss <;> simp [ofSegments, size, segmentSize, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    | cons c cs => simp [ofSegments, size, segmentSize]

/-- RFC 3986 §5.2.4 rules A–E: every next input still has the stated
"initial "/" character (if any)" representation. -/
theorem rdsNext_valid (i : RdsInput) (o : RdsOutput) : (rdsNext i o).1.Valid := by
  cases i with
  | empty => trivial
  | rootless s ss =>
    simp only [rdsNext]
    split
    · exact RdsInput.valid_ofSegments _
    · cases ss <;> trivial
  | absolute s ss =>
    simp only [rdsNext]
    split
    · cases ss <;> trivial
    · split <;> cases ss <;> trivial

/-- RFC 3986 §5.2.4 rules A–E respectively "remove", "replace", or
"move" at least one input character on each nonempty-buffer iteration. -/
theorem rdsNext_size_lt (i : RdsInput) (o : RdsOutput)
    (hv : i.Valid) (hn : i ≠ .empty) : (rdsNext i o).1.size < i.size := by
  cases i with
  | empty => contradiction
  | rootless s ss =>
    have hs : 0 < s.length := List.length_pos_iff.mpr hv
    simp only [rdsNext]
    split
    · have := RdsInput.size_ofSegments_le ss
      change (RdsInput.ofSegments ss).size < s.length + segmentSize ss
      omega
    · rw [RdsInput.size_afterSlash]
      simp only [RdsInput.size]
      omega
  | absolute s ss =>
    simp only [rdsNext]
    split
    · rename_i hs
      have := RdsInput.size_replaceDot_le ss
      change (RdsInput.replaceDot ss).size < s.length + segmentSize ss + 1
      simp only [hs, List.length_cons, List.length_nil]
      omega
    · split
      · rename_i hs
        have := RdsInput.size_replaceDot_le ss
        change (RdsInput.replaceDot ss).size < s.length + segmentSize ss + 1
        simp only [hs, List.length_cons, List.length_nil]
        omega
      · rw [RdsInput.size_afterSlash]
        simp only [RdsInput.size]
        omega

/-- RFC 3986 §5.2.4: "While the input buffer is not empty". The buffer
must be empty at measure zero in a valid representation. -/
theorem RdsInput.eq_empty_of_size_zero (i : RdsInput) (hv : i.Valid)
    (hz : i.size = 0) : i = .empty := by
  cases i with
  | empty => rfl
  | rootless s ss =>
    have hs : 0 < s.length := List.length_pos_iff.mpr hv
    simp only [size] at hz
    omega
  | absolute s ss => simp [size] at hz

/-- RFC 3986 §5.2.4: "While the input buffer is not empty". Any two fuel
budgets at least the input-buffer length produce the same output buffer. -/
theorem rdsStep_fuel_independent (n m : Nat) (i : RdsInput) (o : RdsOutput)
    (hv : i.Valid) (hn : i.size ≤ n) (hm : i.size ≤ m) :
    rdsStep n i o = rdsStep m i o := by
  induction n generalizing m i o with
  | zero =>
    have he : i = .empty := i.eq_empty_of_size_zero hv (by omega)
    subst i
    cases m <;> rfl
  | succ n ih =>
    by_cases he : i = .empty
    · subst i; cases m <;> rfl
    · have hl := rdsNext_size_lt i o hv he
      cases m with
      | zero => omega
      | succ m =>
        have hx := ih m (rdsNext i o).1 (rdsNext i o).2
          (rdsNext_valid i o) (by omega) (by omega)
        cases i <;> simp_all only [rdsStep, not_true_eq_false]

/-- RFC 3986 §5.2.4: "Finally, the output buffer is returned". The chosen
`length + 2` budget cannot truncate the loop; every budget at least `length`
agrees with it. -/
theorem rds_fuel_sufficient (p : List Char) (n : Nat) (h : p.length ≤ n) :
    (rdsStep n (RdsInput.ofSegments (splitSlash p)) ⟨false, []⟩).render =
      removeDotSegments p := by
  have hz : (RdsInput.ofSegments (splitSlash p)).size = p.length := by
    rw [RdsInput.size_eq_length, RdsInput.render_ofSegments, joinSlash_splitSlash]
  unfold removeDotSegments
  rw [rdsStep_fuel_independent n (p.length + 2) _ _
    (RdsInput.valid_ofSegments _) (by omega) (by omega)]


/-- RFC 3986 §5.2.4 rule E: "including the initial "/" character (if any)".
Only segment characters and delimiters occur in a rendered segment list. -/
theorem mem_joinSlash (ss : List (List Char)) (c : Char)
    (h : c ∈ joinSlash ss) : c = '/' ∨ ∃ s ∈ ss, c ∈ s := by
  induction ss with
  | nil => simp [joinSlash] at h
  | cons s ss ih =>
    cases ss with
    | nil => exact Or.inr ⟨s, by simp, h⟩
    | cons t ts =>
      simp only [joinSlash, List.mem_append, List.mem_cons] at h
      rcases h with hc | rfl | ht
      · exact Or.inr ⟨s, by simp, hc⟩
      · exact Or.inl rfl
      · rcases ih ht with hs | ⟨q, hq, hc⟩
        · exact Or.inl hs
        · exact Or.inr ⟨q, by simp [hq], hc⟩

/-- RFC 3986 §5.2.4 rule E: "move the first path segment in the input buffer to the end
of the output buffer". Appending a segment to a nonempty segment list
adds exactly one delimiter. -/
theorem joinSlash_append_singleton (ss : List (List Char)) (s : List Char)
    (h : ss ≠ []) : joinSlash (ss ++ [s]) = joinSlash ss ++ '/' :: s := by
  induction ss with
  | nil => contradiction
  | cons t ts ih =>
    cases ts with
    | nil => simp [joinSlash]
    | cons q qs =>
      simp only [List.cons_append, joinSlash, List.append_assoc, List.cons_append]
      exact congrArg (fun x => t ++ '/' :: x) (by
        simpa only [List.cons_append] using ih (by simp))

/-- RFC 3986 §5.2.4 rule E: "move the first path segment in the input buffer to the end
of the output buffer". Concatenating into the final segment is textual
concatenation. -/
theorem joinSlash_append_last (ss : List (List Char)) (a b : List Char) :
    joinSlash (ss ++ [a ++ b]) = joinSlash (ss ++ [a]) ++ b := by
  cases ss with
  | nil => rfl
  | cons s ss =>
    rw [joinSlash_append_singleton _ _ (by simp),
      joinSlash_append_singleton _ _ (by simp)]
    simp [List.append_assoc]

/-- RFC 3986 §5.2.4 rule E: "move the first path segment in the input
buffer to the end of the output buffer, including the initial "/"
character (if any)". The internal output representation performs exactly
that append. -/
theorem RdsOutput.push_render (o : RdsOutput) (slash : Bool) (s : List Char) :
    (o.push slash s).render = o.render ++ (if slash then '/' :: s else s) := by
  obtain ⟨rooted, segments⟩ := o
  cases slash with
  | false =>
    cases segments with
    | nil => rfl
    | cons t ts =>
      simp only [RdsOutput.push, Bool.false_eq_true, ↓reduceIte, RdsOutput.render,
        List.reverse_cons]
      cases rooted <;> simp [joinSlash_append_last]
  | true =>
    cases segments with
    | nil => rfl
    | cons t ts =>
      simp only [RdsOutput.push, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte,
        RdsOutput.render, List.reverse_cons]
      rw [joinSlash_append_singleton _ _ (by simp)]
      cases rooted <;> simp

/-- RFC 3986 §5.2.4: "a complete path segment". Rendering an output
buffer retains its stored segments and at most the leading empty segment. -/
theorem RdsOutput.splitSlash_render (o : RdsOutput)
    (h : ∀ s ∈ o.segments, '/' ∉ s) :
    splitSlash o.render =
      if o.segments = [] then [[]]
      else if o.rooted then [] :: o.segments.reverse else o.segments.reverse := by
  obtain ⟨rooted, segments⟩ := o
  cases segments with
  | nil => rfl
  | cons s ss =>
    have hn : (s :: ss).reverse ≠ [] := by simp
    have hs : ∀ t ∈ (s :: ss).reverse, '/' ∉ t := by
      intro t ht
      exact h t (List.mem_reverse.mp ht)
    have he := splitSlash_joinSlash _ hn hs
    cases rooted <;> simp only [RdsOutput.render, Bool.false_eq_true,
      List.cons_ne_nil, ↓reduceIte, splitSlash_slash, he]

/-- RFC 3986 §5.2.4: "a complete path segment". No nonempty segment is
introduced when an output buffer is rendered. -/
theorem RdsOutput.mem_splitSlash_render (o : RdsOutput)
    (h : ∀ s ∈ o.segments, '/' ∉ s) (s : List Char)
    (hs : s ∈ splitSlash o.render) : s = [] ∨ s ∈ o.segments := by
  rw [o.splitSlash_render h] at hs
  split at hs
  · exact Or.inl (by simpa using hs)
  · split at hs
    · rcases List.mem_cons.mp hs with he | hm
      · exact Or.inl he
      · exact Or.inr (List.mem_reverse.mp hm)
    · exact Or.inr (List.mem_reverse.mp hs)

/-- RFC 3986 §5.2.4: "a complete path segment" is the unit removed by
rules A–D. This predicate states a property of every input segment. -/
def RdsInput.All (P : List Char → Prop) : RdsInput → Prop
  | .empty => True
  | .rootless s ss => ∀ t ∈ s :: ss, P t
  | .absolute s ss => ∀ t ∈ s :: ss, P t

/-- RFC 3986 §5.2.4, rule E: "including the initial "/" character (if
any)". Only an initial rootless input can lack that slash, before any output
has been emitted. -/
def RdsAligned (i : RdsInput) (o : RdsOutput) : Prop :=
  match i with
  | .rootless _ _ => o.segments = []
  | _ => True

/-- RFC 3986 §5.2.4: "the special "." and ".." complete path segments". -/
def NonDot (s : List Char) : Prop := s ≠ ['.'] ∧ s ≠ ['.', '.']

/-- RFC 3986 §5.2.4: "the special "." and ".." complete path segments". The
predicate excludes exactly these two segments, retaining all other text. -/
def NoDotSegments (p : List Char) : Prop := ∀ s ∈ splitSlash p, NonDot s

/-- RFC 3986 §5.2.4: "The input buffer is initialized with the now-appended
path components"; converting its representation only drops a leading empty
marker, never adds a segment. -/
theorem RdsInput.all_ofSegments (P : List Char → Prop) (ss : List (List Char))
    (h : ∀ s ∈ ss, P s) : (ofSegments ss).All P := by
  cases ss with
  | nil => trivial
  | cons s ss => cases s with
    | nil => cases ss with
      | nil => trivial
      | cons t ts => exact fun q hq => h q (by simp [hq])
    | cons c cs => exact h

/-- RFC 3986 §5.2.4, rule E: "up to, but not including, the next "/"
character". The remaining buffer contains only the remaining segments. -/
theorem RdsInput.all_afterSlash (P : List Char → Prop) (ss : List (List Char))
    (h : ∀ s ∈ ss, P s) : (afterSlash ss).All P := by
  cases ss with
  | nil => trivial
  | cons s ss => exact h

/-- RFC 3986 §5.2.4, rules B/C: "replace that prefix with "/"". The only
new segment this replacement can introduce is empty. -/
theorem RdsInput.all_replaceDot (P : List Char → Prop) (ss : List (List Char))
    (he : P []) (h : ∀ s ∈ ss, P s) : (replaceDot ss).All P := by
  cases ss with
  | nil =>
    intro s hs
    have hh : s = [] := by simpa using hs
    exact hh ▸ he
  | cons s ss => exact h

/-- RFC 3986 §5.2.4, rule E: "including the initial "/" character (if
any)". Alignment is preserved after each rule. -/
theorem rdsNext_aligned (i : RdsInput) (o : RdsOutput) (h : RdsAligned i o) :
    RdsAligned (rdsNext i o).1 (rdsNext i o).2 := by
  cases i with
  | empty => trivial
  | rootless s ss =>
    simp only [rdsNext]
    split
    · cases ss with
      | nil => trivial
      | cons t ts => cases t with
        | nil => cases ts <;> trivial
        | cons c cs => exact h
    · cases ss <;> trivial
  | absolute s ss =>
    simp only [rdsNext]
    split
    · cases ss <;> trivial
    · split <;> cases ss <;> trivial

/-- RFC 3986 §5.2.4: rules A–D remove dot segments; rule E "move the
first path segment". Any segment property allowing the empty segment is
preserved collectively across both buffers. -/
theorem rdsNext_all (P : List Char → Prop) (he : P [])
    (i : RdsInput) (o : RdsOutput) (ha : RdsAligned i o)
    (hi : i.All P) (ho : ∀ s ∈ o.segments, P s) :
    (rdsNext i o).1.All P ∧ ∀ s ∈ (rdsNext i o).2.segments, P s := by
  cases i with
  | empty => exact ⟨trivial, ho⟩
  | rootless s ss =>
    have hs : P s := hi s (by simp)
    have ht : ∀ t ∈ ss, P t := fun t hm => hi t (by simp [hm])
    simp only [rdsNext]
    split
    · exact ⟨RdsInput.all_ofSegments P ss ht, ho⟩
    · refine ⟨RdsInput.all_afterSlash P ss ht, ?_⟩
      change o.segments = [] at ha
      simpa [RdsOutput.push, ha] using hs
  | absolute s ss =>
    have hs : P s := hi s (by simp)
    have ht : ∀ t ∈ ss, P t := fun t hm => hi t (by simp [hm])
    simp only [rdsNext]
    split
    · exact ⟨RdsInput.all_replaceDot P ss he ht, ho⟩
    · split
      · refine ⟨RdsInput.all_replaceDot P ss he ht, ?_⟩
        intro t hm
        exact ho t (List.mem_of_mem_tail hm)
      · refine ⟨RdsInput.all_afterSlash P ss ht, ?_⟩
        intro t hm
        simp only [RdsOutput.push, ↓reduceIte] at hm
        rcases List.mem_cons.mp hm with rfl | hm
        · exact hs
        · exact ho t hm

/-- RFC 3986 §5.2.4: "While the input buffer is not empty, loop as
follows". Lift the segment invariant through the whole structural loop. -/
theorem rdsStep_all (P : List Char → Prop) (he : P []) (n : Nat)
    (i : RdsInput) (o : RdsOutput) (ha : RdsAligned i o)
    (hi : i.All P) (ho : ∀ s ∈ o.segments, P s) :
    ∀ s ∈ (rdsStep n i o).segments, P s := by
  induction n generalizing i o with
  | zero => exact ho
  | succ n ih =>
    have hall := rdsNext_all P he i o ha hi ho
    have hnext := ih (rdsNext i o).1 (rdsNext i o).2
      (rdsNext_aligned i o ha) hall.1 hall.2
    cases i with
    | empty => exact ho
    | rootless s ss => exact hnext
    | absolute s ss => exact hnext

/-- RFC 3986 §5.2.4: "the output buffer is initialized to the empty string."
This initial state satisfies the segment-alignment invariant. -/
theorem rdsAligned_empty (i : RdsInput) : RdsAligned i ⟨false, []⟩ := by
  cases i <;> trivial

/-- RFC 3986 §5.2.4: "Finally, the output buffer is returned". Every
segment property permitting empty segments is inherited from the input. -/
theorem rds_output_all (P : List Char → Prop) (he : P []) (p : List Char)
    (hp : ∀ s ∈ splitSlash p, P s) :
    ∀ s ∈ (rdsStep (p.length + 2) (RdsInput.ofSegments (splitSlash p))
      ⟨false, []⟩).segments, P s :=
  rdsStep_all P he _ _ _ (rdsAligned_empty _) (RdsInput.all_ofSegments P _ hp)
    (by intro s hs; contradiction)

/-- RFC 3986 §5.2.4: rules A–D remove complete dot segments and rule E
"move the first path segment". L-E: every nonempty output segment was
already a complete input segment; no percent-encoded token is split. -/
theorem rds_segment_conservation (p s : List Char)
    (h : s ∈ splitSlash (removeDotSegments p)) : s = [] ∨ s ∈ splitSlash p := by
  have hslash := rds_output_all (fun t => '/' ∉ t) (by simp) p
    (fun t ht => noSlash_of_mem_splitSlash p t ht)
  have hsrc := rds_output_all (fun t => t = [] ∨ t ∈ splitSlash p) (Or.inl rfl) p
    (fun t ht => Or.inr ht)
  rcases RdsOutput.mem_splitSlash_render _ hslash s h with he | hm
  · exact Or.inl he
  · exact hsrc s hm

/-- RFC 3986 §5.2.4 rules A–D remove complete "."/".." segments before
rule E moves a segment. Therefore the output invariant is preserved. -/
theorem rdsNext_nondot (i : RdsInput) (o : RdsOutput)
    (ha : RdsAligned i o) (ho : ∀ s ∈ o.segments, NonDot s) :
    ∀ s ∈ (rdsNext i o).2.segments, NonDot s := by
  cases i with
  | empty => exact ho
  | rootless s ss =>
    simp only [rdsNext]
    split
    · exact ho
    · rename_i hn
      have hs : NonDot s := by simpa [NonDot, not_or] using hn
      change o.segments = [] at ha
      simpa [RdsOutput.push, ha] using hs
  | absolute s ss =>
    simp only [rdsNext]
    split
    · exact ho
    · rename_i hdot
      split
      · intro t ht; exact ho t (List.mem_of_mem_tail ht)
      · rename_i hparent
        intro t ht
        simp only [RdsOutput.push, ↓reduceIte] at ht
        rcases List.mem_cons.mp ht with rfl | hm
        · exact ⟨hdot, hparent⟩
        · exact ho t hm

/-- RFC 3986 §5.2.4: "While the input buffer is not empty, loop as
follows". The output buffer contains no complete dot segment at any stage. -/
theorem rdsStep_nondot (n : Nat) (i : RdsInput) (o : RdsOutput)
    (ha : RdsAligned i o) (ho : ∀ s ∈ o.segments, NonDot s) :
    ∀ s ∈ (rdsStep n i o).segments, NonDot s := by
  induction n generalizing i o with
  | zero => exact ho
  | succ n ih =>
    have hnext := ih (rdsNext i o).1 (rdsNext i o).2
      (rdsNext_aligned i o ha) (rdsNext_nondot i o ha ho)
    cases i with
    | empty => exact ho
    | rootless s ss => exact hnext
    | absolute s ss => exact hnext

/-- RFC 3986 §5.2.4: "interpreting and removing the special "." and ".." complete path
segments from a referenced path."
R2: no such segment survives in the result. -/
theorem rds_no_dot_segments (p : List Char) : NoDotSegments (removeDotSegments p) := by
  have hslash := rds_output_all (fun t => '/' ∉ t) (by simp) p
    (fun t ht => noSlash_of_mem_splitSlash p t ht)
  have hnd := rdsStep_nondot (p.length + 2) (RdsInput.ofSegments (splitSlash p))
    ⟨false, []⟩ (rdsAligned_empty _) (by intro s hs; contradiction)
  intro s hs
  rcases RdsOutput.mem_splitSlash_render _ hslash s hs with rfl | hm
  · simp [NonDot]
  · exact hnd s hm

/-- RFC 3986 §5.2.4, rule C: "remove the last segment and its preceding
"/" (if any)". A rooted computation may temporarily empty its output,
but then retains an absolute input that will restore a slash by rule E. -/
def RdsRooted (i : RdsInput) (o : RdsOutput) : Prop :=
  (o.segments = [] ∨ o.rooted = true) ∧
    match i with
    | .empty => o.segments ≠ []
    | .absolute _ _ => True
    | .rootless _ _ => False

/-- RFC 3986 §5.2.4, rule E: "including the initial "/" character".
Appending an absolute segment preserves the output's leading slash. -/
theorem RdsOutput.push_true_rooted (o : RdsOutput) (s : List Char)
    (h : o.segments = [] ∨ o.rooted = true) : (o.push true s).rooted = true := by
  rcases h with he | hr
  · simp [push, he]
  · simp [push, hr]

/-- RFC 3986 §5.2.4 rules B/C "replace that prefix with "/"" and rule E
includes the initial slash. These operations preserve rootedness jointly
across the input and output buffers. -/
theorem rdsNext_rooted (i : RdsInput) (o : RdsOutput) (h : RdsRooted i o) :
    RdsRooted (rdsNext i o).1 (rdsNext i o).2 := by
  cases i with
  | empty => exact h
  | rootless s ss => exact False.elim h.2
  | absolute s ss =>
    simp only [rdsNext]
    split
    · cases ss <;> exact ⟨h.1, trivial⟩
    · split
      · have hp : o.pop.segments = [] ∨ o.pop.rooted = true := by
          rcases h.1 with he | hr
          · exact Or.inl (by simp [RdsOutput.pop, he])
          · exact Or.inr hr
        cases ss <;> exact ⟨hp, trivial⟩
      · have hp : (o.push true s).rooted = true := o.push_true_rooted s h.1
        have hn : (o.push true s).segments ≠ [] := by simp [RdsOutput.push]
        cases ss with
        | nil => exact ⟨Or.inr hp, hn⟩
        | cons t ts => exact ⟨Or.inr hp, trivial⟩

/-- RFC 3986 §5.2.4: "Finally, the output buffer is returned". Once a
rooted computation exhausts its input (using sufficient fuel), the output
is nonempty and begins with its preserved slash. -/
theorem rdsStep_rooted (n : Nat) (i : RdsInput) (o : RdsOutput)
    (hv : i.Valid) (hn : i.size ≤ n) (hr : RdsRooted i o) :
    (rdsStep n i o).rooted = true ∧ (rdsStep n i o).segments ≠ [] := by
  induction n generalizing i o with
  | zero =>
    have he : i = .empty := i.eq_empty_of_size_zero hv (by omega)
    subst i
    exact ⟨hr.1.resolve_left hr.2, hr.2⟩
  | succ n ih =>
    by_cases he : i = .empty
    · subst i
      exact ⟨hr.1.resolve_left hr.2, hr.2⟩
    · have hl := rdsNext_size_lt i o hv he
      have hs := ih (rdsNext i o).1 (rdsNext i o).2 (rdsNext_valid i o)
        (by omega) (rdsNext_rooted i o hr)
      cases i with
      | empty => exact False.elim (he rfl)
      | rootless s ss => exact hs
      | absolute s ss => exact hs

/-- RFC 3986 §5.2.4, rule E: "including the initial "/" character (if
any)". Rendering a nonempty rooted output starts with exactly that slash. -/
theorem RdsOutput.head_render (o : RdsOutput) (hr : o.rooted = true)
    (hn : o.segments ≠ []) : o.render.head? = some '/' := by
  cases hs : o.segments with
  | nil => exact False.elim (hn hs)
  | cons s ss => simp [render, hs, hr]

/-- RFC 3986 §5.2.4, rules B/C: "replace that prefix with "/""; rule E:
"including the initial "/" character (if any)". R3: an initial slash
is preserved, including after every output segment has been popped. -/
theorem rds_leading_slash (p : List Char) (h : p.head? = some '/') :
    (removeDotSegments p).head? = some '/' := by
  have hz : (RdsInput.ofSegments (splitSlash p)).size = p.length := by
    rw [RdsInput.size_eq_length, RdsInput.render_ofSegments, joinSlash_splitSlash]
  have hr : RdsRooted (RdsInput.ofSegments (splitSlash p)) ⟨false, []⟩ := by
    cases p with
    | nil => contradiction
    | cons c cs =>
      have hc : c = '/' := by simpa using h
      subst c
      rw [splitSlash_slash]
      cases hs : splitSlash cs with
      | nil => exact False.elim (splitSlash_ne_nil cs hs)
      | cons s ss => exact ⟨Or.inl rfl, trivial⟩
  have ho := rdsStep_rooted (p.length + 2) (RdsInput.ofSegments (splitSlash p))
    ⟨false, []⟩ (RdsInput.valid_ofSegments _) (by omega) hr
  exact RdsOutput.head_render _ ho.1 ho.2


/-- RFC 3986 §5.2.4: "While the input buffer is not empty". An empty
buffer returns its output unchanged at every fuel budget. -/
theorem rdsStep_empty (n : Nat) (o : RdsOutput) : rdsStep n .empty o = o := by
  cases n <;> rfl

/-- RFC 3986 §5.2.4 rule E: "move the first path segment in the input buffer to the end
of the output buffer". With no dot segments every remaining step is E. -/
theorem rdsStep_afterSlash_dotfree (ss : List (List Char)) (o : RdsOutput) (n : Nat)
    (hn : ss.length ≤ n) (h : ∀ s ∈ ss, s ≠ ['.'] ∧ s ≠ ['.', '.']) :
    (rdsStep n (RdsInput.afterSlash ss) o).render =
      o.render ++ (RdsInput.afterSlash ss).render := by
  induction ss generalizing n o with
  | nil => simp [RdsInput.afterSlash, rdsStep_empty, RdsInput.render]
  | cons s ss ih =>
    have hs := h s (by simp)
    have ht : ∀ t ∈ ss, t ≠ ['.'] ∧ t ≠ ['.', '.'] := by
      intro t ht
      exact h t (by simp [ht])
    cases n with
    | zero => simp at hn
    | succ n =>
      have hn' : ss.length ≤ n := by simpa using hn
      change (rdsStep n (rdsNext (.absolute s ss) o).1
        (rdsNext (.absolute s ss) o).2).render = _
      simp only [rdsNext, hs.1, hs.2, ↓reduceIte]
      rw [ih _ _ hn' ht, RdsOutput.push_render]
      cases ss <;> simp [RdsInput.afterSlash, RdsInput.render, joinSlash, List.append_assoc]

/-- RFC 3986 §5.2.4 rule E: "including the initial "/" character (if
any)". A dot-free rootless buffer likewise transfers without alteration. -/
theorem rdsStep_rootless_dotfree (s : List Char) (ss : List (List Char))
    (o : RdsOutput) (n : Nat) (hn : ss.length + 1 ≤ n)
    (h : ∀ t ∈ s :: ss, t ≠ ['.'] ∧ t ≠ ['.', '.']) :
    (rdsStep n (.rootless s ss) o).render = o.render ++ joinSlash (s :: ss) := by
  have hs := h s (by simp)
  have ht : ∀ t ∈ ss, t ≠ ['.'] ∧ t ≠ ['.', '.'] := by
    intro t ht
    exact h t (by simp [ht])
  cases n with
  | zero => omega
  | succ n =>
    have hn' : ss.length ≤ n := by omega
    change (rdsStep n (rdsNext (.rootless s ss) o).1
      (rdsNext (.rootless s ss) o).2).render = _
    simp only [rdsNext, hs.1, hs.2, or_self, ↓reduceIte]
    rw [rdsStep_afterSlash_dotfree _ _ _ hn' ht, RdsOutput.push_render]
    cases ss <;> simp [RdsInput.afterSlash, RdsInput.render, joinSlash, List.append_assoc]

/-- RFC 3986 §5.2.4 rule E: "the next "/" character". A path has at
most one more delimiter-preserving segment than characters. -/
theorem splitSlash_length_le (p : List Char) : (splitSlash p).length ≤ p.length + 1 := by
  induction p with
  | nil => simp [splitSlash]
  | cons c cs ih =>
    by_cases hc : c = '/'
    · subst c
      simp only [splitSlash_slash, List.length_cons]
      omega
    · cases hs : splitSlash cs with
      | nil => exact False.elim (splitSlash_ne_nil cs hs)
      | cons s ss =>
        simp only [splitSlash, hc, ↓reduceIte, hs, List.length_cons]
        simp only [hs, List.length_cons] at ih
        omega

/-- RFC 3986 §5.2.4 rule E: "move the first path segment in the input buffer to the end
of the output buffer". With no complete dot segment, the initialized
buffer is transferred exactly. -/
theorem rdsStep_ofSegments_dotfree (ss : List (List Char)) (n : Nat)
    (hn : ss.length ≤ n) (h : ∀ s ∈ ss, NonDot s) :
    (rdsStep n (RdsInput.ofSegments ss) ⟨false, []⟩).render = joinSlash ss := by
  cases ss with
  | nil => simp [RdsInput.ofSegments, rdsStep_empty, RdsOutput.render, joinSlash]
  | cons s ss =>
    cases s with
    | nil =>
      cases ss with
      | nil => simp [RdsInput.ofSegments, rdsStep_empty, RdsOutput.render, joinSlash]
      | cons t ts =>
        have ht : ∀ s ∈ t :: ts, s ≠ ['.'] ∧ s ≠ ['.', '.'] := by
          intro s hs
          exact h s (by simp [hs])
        have hn' : (t :: ts).length ≤ n := by simp only [List.length_cons] at *; omega
        have hh := rdsStep_afterSlash_dotfree (t :: ts) ⟨false, []⟩ n hn' ht
        exact hh
    | cons c cs =>
      have hh := rdsStep_rootless_dotfree (c :: cs) ss ⟨false, []⟩ n hn h
      exact hh

/-- R5, derived from RFC 3986 §5.2.4 rule E: "move the first path segment
in the input buffer to the end of the output buffer". If no complete dot
segments occur, only E fires and the whole path is a fixed point. -/
theorem rds_dotfree_fixpoint (p : List Char) (h : NoDotSegments p) :
    removeDotSegments p = p := by
  have hn : (splitSlash p).length ≤ p.length + 2 := by
    have := splitSlash_length_le p
    omega
  have hh := rdsStep_ofSegments_dotfree (splitSlash p) (p.length + 2) hn h
  simpa [removeDotSegments, joinSlash_splitSlash] using hh

/-- R1, derived from RFC 3986 §5.2.4: "the special "." and ".." complete
path segments". Once these have been removed, a second pass is a fixed point. -/
theorem rds_idempotent (p : List Char) :
    removeDotSegments (removeDotSegments p) = removeDotSegments p :=
  rds_dotfree_fixpoint _ (rds_no_dot_segments p)


/-!
# Character conservation for §5.2.4

RFC §5.2.4: "remove", "replace", and "move" are the only buffer
operations. Whole segments retain their characters, and a separator can
appear in the result only when the original input contained one.
-/

/-- §5.2.4 E moves a segment "including the initial "/" character (if
any)". Joining a segment list retains every character of each member. -/
theorem mem_joinSlash_of_segment (ss : List (List Char)) (s : List Char)
    (hs : s ∈ ss) (c : Char) (hc : c ∈ s) : c ∈ joinSlash ss := by
  induction ss with
  | nil => contradiction
  | cons t ts ih =>
    cases ts with
    | nil =>
      have he : s = t := by simpa using hs
      simpa [joinSlash, he] using hc
    | cons u us =>
      rcases List.mem_cons.mp hs with he | ht
      · simp [joinSlash, ← he, hc]
      · have ht := ih ht
        simp only [joinSlash, List.mem_append, List.mem_cons]
        exact Or.inr (Or.inr ht)

/-- §5.2.4 E stops at "the next "/" character". A character in one
of the original segments is a character of the original path. -/
theorem mem_path_of_mem_splitSlash (p s : List Char) (hs : s ∈ splitSlash p)
    (c : Char) (hc : c ∈ s) : c ∈ p := by
  have h := mem_joinSlash_of_segment (splitSlash p) s hs c hc
  simpa [joinSlash_splitSlash] using h

/-- §5.2.4 D: "if the input buffer consists only of "." or "..",
then remove that from the input buffer; otherwise," E moves the whole
slash-free segment. A slash-free input therefore returns itself or empty. -/
theorem rds_noSlash_input (p : List Char) (hs : '/' ∉ p) :
    removeDotSegments p = [] ∨ removeDotSegments p = p := by
  cases p with
  | nil => exact Or.inl removeDotSegments_nil
  | cons c cs =>
    rw [removeDotSegments, splitSlash_of_noSlash _ hs]
    by_cases hd : c :: cs = ['.'] ∨ c :: cs = ['.', '.']
    · left
      have hn : rdsNext (.rootless (c :: cs) []) ⟨false, []⟩ =
          (.empty, ⟨false, []⟩) := by
        rw [rdsNext, ite_eq_left hd]
        rfl
      simp only [RdsInput.ofSegments, rdsStep, hn,
        RdsOutput.render]
    · right
      have hn : rdsNext (.rootless (c :: cs) []) ⟨false, []⟩ =
          (.empty, ⟨false, [c :: cs]⟩) := by
        rw [rdsNext, ite_eq_right hd]
        rfl
      simp [RdsInput.ofSegments, rdsStep, hn, RdsOutput.render, joinSlash]

/-- §5.2.4 D/E: "remove" or "move" a slash-free segment; neither creates
an input separator where none existed. -/
theorem rds_noSlash_of_noSlash (p : List Char) (hs : '/' ∉ p) :
    '/' ∉ removeDotSegments p := by
  rcases rds_noSlash_input p hs with he | he
  · simp [he]
  · simpa [he] using hs

/-- R4, derived from RFC §5.2.4's "remove", "replace", and "move"
operations: no character in the returned output is new to the input. -/
theorem rds_char_conservation (p : List Char) (c : Char)
    (hc : c ∈ removeDotSegments p) : c ∈ p := by
  by_cases hs : c = '/'
  · subst c
    by_cases hp : '/' ∈ p
    · exact hp
    · exact False.elim (rds_noSlash_of_noSlash p hp hc)
  · have hm : c ∈ joinSlash (splitSlash (removeDotSegments p)) := by
      simpa [joinSlash_splitSlash] using hc
    rcases mem_joinSlash _ c hm with he | ⟨s, hseg, hcs⟩
    · exact False.elim (hs he)
    · rcases rds_segment_conservation p s hseg with he | hp
      · simp [he] at hcs
      · exact mem_path_of_mem_splitSlash p s hp c hcs

/-- RFC 3986 §5.2.3: "excluding any characters after the right-most
"/" in the base URI path, or excluding the entire base URI path if it
 does not contain any "/" characters". This helper keeps that final slash. -/
def mergePrefix : List Char → List Char
  | [] => []
  | c :: cs => if '/' ∈ cs then c :: mergePrefix cs
    else if c = '/' then ['/'] else []

/-- RFC 3986 §5.2.3: "If the base URI has a defined authority component
and an empty path, then return a string consisting of "/" concatenated
with the reference's path; otherwise," and "return a string consisting
of the reference's path component appended to all but the last segment
of the base URI's path". The authority parameter makes explicit the
context used by the first bullet (erratum eid2933). -/
def merge (baseAuthority : Option (List Char)) (basePath refPath : List Char) : List Char :=
  if baseAuthority.isSome ∧ basePath = [] then '/' :: refPath
  else mergePrefix basePath ++ refPath

/-- RFC 3986 §5.2.3: "If the base URI has a defined authority component
and an empty path, then return a string consisting of "/" concatenated
with the reference's path". -/
theorem merge_bullet1 (a bp rp : List Char) (h : bp = []) :
    merge (some a) bp rp = '/' :: rp := by
  simp [merge, h]

/-- RFC 3986 §5.2.3: "excluding the entire base URI path if it does not
contain any "/" characters". This is the prefix operation in bullet 2. -/
theorem mergePrefix_noslash (bp : List Char) (h : '/' ∉ bp) :
    mergePrefix bp = [] := by
  cases bp with
  | nil => rfl
  | cons c cs =>
    simp only [List.mem_cons, not_or] at h
    simp [mergePrefix, Ne.symm h.1, h.2]

/-- RFC 3986 §5.2.3: "return a string consisting of the reference's path
component appended to all but the last segment of the base URI's path".
A slash in the base path excludes the empty-path first bullet. -/
theorem merge_bullet2 (auth : Option (List Char)) (bp rp : List Char)
    (h : '/' ∈ bp) : merge auth bp rp = mergePrefix bp ++ rp := by
  have hn : bp ≠ [] := by intro he; simp [he] at h
  simp [merge, hn]

/-- RFC 3986 §5.2.3: "otherwise," ... "excluding the entire base URI
path if it does not contain any "/" characters". The first-bullet
condition is excluded explicitly by `otherwise`. -/
theorem merge_bullet2_noslash (auth : Option (List Char)) (bp rp : List Char)
    (otherwise : ¬ (auth.isSome ∧ bp = [])) (h : '/' ∉ bp) :
    merge auth bp rp = rp := by
  simp [merge, otherwise, mergePrefix_noslash bp h]

/-- RFC 3986 §5.2.3: "If the base URI has a defined authority component
and an empty path" ... "otherwise,". These alternatives exhaust merge. -/
theorem merge_cases (auth : Option (List Char)) (bp rp : List Char) :
    (auth.isSome ∧ bp = [] ∧ merge auth bp rp = '/' :: rp) ∨
    (¬ (auth.isSome ∧ bp = []) ∧ merge auth bp rp = mergePrefix bp ++ rp) := by
  by_cases h : auth.isSome ∧ bp = []
  · exact Or.inl ⟨h.1, h.2, by simp [merge, h]⟩
  · exact Or.inr ⟨h, by simp [merge, h]⟩

/-- RFC 3986 §5.2.3: "excluding any characters after the right-most
"/" in the base URI path". The discarded suffix has no slash. -/
theorem mergePrefix_decomposition (bp : List Char) :
    ∃ tail, bp = mergePrefix bp ++ tail ∧ '/' ∉ tail := by
  induction bp with
  | nil => exact ⟨[], rfl, by simp⟩
  | cons c cs ih =>
    by_cases hs : '/' ∈ cs
    · obtain ⟨tail, ht, hn⟩ := ih
      exact ⟨tail, by simpa [mergePrefix, hs] using congrArg (List.cons c) ht, hn⟩
    · by_cases hc : c = '/'
      · subst c
        exact ⟨cs, by simp [mergePrefix, hs], hs⟩
      · exact ⟨c :: cs, by simp [mergePrefix, hs, hc], by simp [Ne.symm hc, hs]⟩

/-- RFC 3986 §5.2.3: "excluding any characters after the right-most
"/" in the base URI path". A nonempty retained prefix ends in slash. -/
theorem mergePrefix_final_slash (bp : List Char) :
    mergePrefix bp = [] ∨ ∃ pre, mergePrefix bp = pre ++ ['/'] := by
  induction bp with
  | nil => exact Or.inl rfl
  | cons c cs ih =>
    by_cases hs : '/' ∈ cs
    · rcases ih with he | ⟨pre, he⟩
      · obtain ⟨tail, ht, hn⟩ := mergePrefix_decomposition cs
        rw [he, List.nil_append] at ht
        exact False.elim (hn (ht ▸ hs))
      · exact Or.inr ⟨c :: pre, by simp [mergePrefix, hs, he]⟩
    · by_cases hc : c = '/'
      · exact Or.inr ⟨[], by simp [mergePrefix, hs, hc]⟩
      · exact Or.inl (by simp [mergePrefix, hs, hc])

/-- RFC 3986 §5.2.3: "return a string consisting of "/" concatenated
with the reference's path; otherwise," ... "all but the last segment
of the base URI's path". For an authority-bearing base whose path is
empty or slash-led, merge is slash-led. -/
theorem merge_authority_leading_slash (a bp rp : List Char)
    (hp : bp = [] ∨ bp.head? = some '/') :
    (merge (some a) bp rp).head? = some '/' := by
  rcases hp with hp | hp
  · simp [merge, hp]
  · cases bp with
    | nil => simp at hp
    | cons c cs =>
      simp only [List.head?_cons, Option.some.injEq] at hp
      subst c
      by_cases hs : '/' ∈ cs <;> simp [merge, mergePrefix, hs]


/-- RFC 3986 §5.2.3: "excluding any characters after the right-most
"/" in the base URI path". A delimiter after a prefix retains that
whole prefix. -/
theorem mergePrefix_append_slash (pre rest : List Char) :
    mergePrefix (pre ++ '/' :: rest) = pre ++ '/' :: mergePrefix rest := by
  induction pre with
  | nil =>
    by_cases hs : '/' ∈ rest
    · simp [mergePrefix, hs]
    · simp [mergePrefix, hs, mergePrefix_noslash rest hs]
  | cons c cs ih =>
    simp [mergePrefix, ih]

/-- RFC 3986 §5.2.3: "all but the last segment of the base URI's path".
In delimiter-preserving segment notation, these are exactly `dropLast`. -/
theorem splitSlash_mergePrefix_joinSlash (ss : List (List Char))
    (hn : ss ≠ []) (h : ∀ s ∈ ss, '/' ∉ s) (rp : List Char) :
    splitSlash (mergePrefix (joinSlash ss) ++ rp) = ss.dropLast ++ splitSlash rp := by
  induction ss with
  | nil => contradiction
  | cons s ss ih =>
    cases ss with
    | nil => simp [joinSlash, mergePrefix_noslash s (h s (by simp))]
    | cons t ts =>
      simp only [joinSlash, mergePrefix_append_slash, List.append_assoc,
        List.cons_append, List.dropLast_cons_cons]
      rw [splitSlash_append_slash s _ (h s (by simp))]
      rw [ih (by simp) (by intro q hq; exact h q (by simp [hq]))]

/-- RFC 3986 §5.2.3: "return a string consisting of the reference's path
component appended to all but the last segment of the base URI's path".
This is the exact segment-level form of the second bullet. -/
theorem splitSlash_mergePrefix (bp rp : List Char) :
    splitSlash (mergePrefix bp ++ rp) = (splitSlash bp).dropLast ++ splitSlash rp := by
  have h := splitSlash_mergePrefix_joinSlash (splitSlash bp) (splitSlash_ne_nil bp)
    (fun s hs => noSlash_of_mem_splitSlash bp s hs) rp
  simpa only [joinSlash_splitSlash] using h

/-- RFC 3986 §5.2.3: ""/" concatenated with the reference's path" or
"the reference's path component appended to all but the last segment of
the base URI's path". No nonempty segment is manufactured by merge. -/
theorem merge_segment_conservation (auth : Option (List Char)) (bp rp s : List Char)
    (h : s ∈ splitSlash (merge auth bp rp)) :
    s = [] ∨ s ∈ splitSlash bp ∨ s ∈ splitSlash rp := by
  unfold merge at h
  split at h
  · simp only [splitSlash_slash, List.mem_cons] at h
    rcases h with he | hr
    · exact Or.inl he
    · exact Or.inr (Or.inr hr)
  · rw [splitSlash_mergePrefix] at h
    rcases List.mem_append.mp h with hb | hr
    · exact Or.inr (Or.inl (List.dropLast_subset (splitSlash bp) hb))
    · exact Or.inr (Or.inr hr)

/-- RFC 3986 §5.2.2: "A non-strict parser may ignore a scheme in the
reference if it is identical to the base URI's scheme."
```
if ((not strict) and (R.scheme == Base.scheme)) then
   undefine(R.scheme);
endif;
```
-/
def applyStrict (strict : Bool) (baseScheme : Option (List Char))
    (ref : Components) : Components :=
  if strict = false ∧ ref.scheme = baseScheme then { ref with scheme := none } else ref

/-- RFC 3986 §5.2.2: "if defined(R.scheme) then" ... "else" ...
"if defined(R.authority) then" ... "if (R.path == "") then" ...
"if (R.path starts-with "/") then" ... "T.path = merge(Base.path, R.path);".
The five branches follow the pseudocode in order; the common final line
is "T.fragment = R.fragment;". -/
def transformReferencesCore (base ref : Components) : Components :=
  if ref.scheme.isSome then
    { scheme := ref.scheme, authority := ref.authority,
      path := removeDotSegments ref.path, query := ref.query, fragment := ref.fragment }
  else if ref.authority.isSome then
    { scheme := base.scheme, authority := ref.authority,
      path := removeDotSegments ref.path, query := ref.query, fragment := ref.fragment }
  else if ref.path = [] then
    { scheme := base.scheme, authority := base.authority,
      path := base.path, query := ref.query.or base.query, fragment := ref.fragment }
  else if ref.path.head? = some '/' then
    { scheme := base.scheme, authority := base.authority,
      path := removeDotSegments ref.path, query := ref.query, fragment := ref.fragment }
  else
    { scheme := base.scheme, authority := base.authority,
      path := removeDotSegments (merge base.authority base.path ref.path),
      query := ref.query, fragment := ref.fragment }

/-- RFC 3986 §5.2.2: "A non-strict parser may ignore a scheme in the
reference if it is identical to the base URI's scheme." The adjusted
reference then enters the five-way transform.

The grammar-level interface uses `URI` and `URIReference` trees: §5.2.1,
"The base URI (Base) is established according to the procedure of
Section 5.1 and parsed into the five main components described in
Section 3. Note that only the scheme component is required to be present
in a base URI; the other components may be empty or undefined."
-/
def transformReferences (strict : Bool) (base ref : Components) : Components :=
  transformReferencesCore base (applyStrict strict base.scheme ref)

/-- RFC 3986 §5.2.2: "A non-strict parser may ignore a scheme in the
reference if it is identical to the base URI's scheme." Strict mode
leaves all components unchanged. -/
theorem applyStrict_true (scheme : Option (List Char)) (ref : Components) :
    applyStrict true scheme ref = ref := by
  simp [applyStrict]

/-- RFC 3986 §5.2.2: "if ((not strict) and (R.scheme == Base.scheme)) then
undefine(R.scheme);". -/
theorem applyStrict_false_same (ref : Components) :
    applyStrict false ref.scheme ref = { ref with scheme := none } := by
  simp [applyStrict]

/-- RFC 3986 §5.2.2: "A non-strict parser may ignore a scheme in the
reference if it is identical to the base URI's scheme." A different
scheme passes through unchanged. -/
theorem applyStrict_false_different (scheme : Option (List Char)) (ref : Components)
    (h : ref.scheme ≠ scheme) : applyStrict false scheme ref = ref := by
  simp [applyStrict, h]

/-- RFC 3986 §5.2.2: "undefine(R.scheme);". The adjustment changes only
scheme, leaving authority, path, query and fragment intact. -/
theorem applyStrict_other_components (strict : Bool) (scheme : Option (List Char))
    (ref : Components) :
    (applyStrict strict scheme ref).authority = ref.authority ∧
    (applyStrict strict scheme ref).path = ref.path ∧
    (applyStrict strict scheme ref).query = ref.query ∧
    (applyStrict strict scheme ref).fragment = ref.fragment := by
  unfold applyStrict
  split <;> simp

/-- RFC 3986 §5.2.2 Branch 1, verbatim:
```
if defined(R.scheme) then
   T.scheme    = R.scheme;
   T.authority = R.authority;
   T.path      = remove_dot_segments(R.path);
   T.query     = R.query;
```
The common final assignment is "T.fragment = R.fragment;". -/
theorem transformReferencesCore_scheme (base ref : Components)
    (hs : ref.scheme.isSome) :
    transformReferencesCore base ref =
      { scheme := ref.scheme, authority := ref.authority,
        path := removeDotSegments ref.path, query := ref.query, fragment := ref.fragment } := by
  simp [transformReferencesCore, hs]

/-- RFC 3986 §5.2.2 Branch 2, verbatim:
```
if defined(R.authority) then
   T.authority = R.authority;
   T.path      = remove_dot_segments(R.path);
   T.query     = R.query;
```
The surrounding assignments are "T.scheme = Base.scheme;" and
"T.fragment = R.fragment;". -/
theorem transformReferencesCore_authority (base ref : Components)
    (hs : ref.scheme = none) (ha : ref.authority.isSome) :
    transformReferencesCore base ref =
      { scheme := base.scheme, authority := ref.authority,
        path := removeDotSegments ref.path, query := ref.query, fragment := ref.fragment } := by
  simp [transformReferencesCore, hs, ha]

/-- RFC 3986 §5.2.2 Branch 3, verbatim:
```
if (R.path == "") then
   T.path = Base.path;
   if defined(R.query) then
      T.query = R.query;
   else
      T.query = Base.query;
   endif;
```
The surrounding assignments are "T.authority = Base.authority;",
"T.scheme = Base.scheme;" and "T.fragment = R.fragment;". -/
theorem transformReferencesCore_empty_path (base ref : Components)
    (hs : ref.scheme = none) (ha : ref.authority = none) (hp : ref.path = []) :
    transformReferencesCore base ref =
      { scheme := base.scheme, authority := base.authority,
        path := base.path, query := ref.query.or base.query, fragment := ref.fragment } := by
  simp [transformReferencesCore, hs, ha, hp]

/-- RFC 3986 §5.2.2 Branch 4, verbatim:
```
if (R.path starts-with "/") then
   T.path = remove_dot_segments(R.path);
```
The surrounding assignments are "T.query = R.query;",
"T.authority = Base.authority;", "T.scheme = Base.scheme;" and
"T.fragment = R.fragment;". -/
theorem transformReferencesCore_absolute_path (base ref : Components)
    (hs : ref.scheme = none) (ha : ref.authority = none)
    (hp : ref.path.head? = some '/') :
    transformReferencesCore base ref =
      { scheme := base.scheme, authority := base.authority,
        path := removeDotSegments ref.path, query := ref.query, fragment := ref.fragment } := by
  have hn : ref.path ≠ [] := by intro he; simp [he] at hp
  simp [transformReferencesCore, hs, ha, hp, hn]

/-- RFC 3986 §5.2.2 Branch 5, verbatim:
```
T.path = merge(Base.path, R.path);
T.path = remove_dot_segments(T.path);
```
The surrounding assignments are "T.query = R.query;",
"T.authority = Base.authority;", "T.scheme = Base.scheme;" and
"T.fragment = R.fragment;". -/
theorem transformReferencesCore_merge (base ref : Components)
    (hs : ref.scheme = none) (ha : ref.authority = none)
    (hp : ref.path ≠ []) (hl : ref.path.head? ≠ some '/') :
    transformReferencesCore base ref =
      { scheme := base.scheme, authority := base.authority,
        path := removeDotSegments (merge base.authority base.path ref.path),
        query := ref.query, fragment := ref.fragment } := by
  simp [transformReferencesCore, hs, ha, hp, hl]

/-- RFC 3986 §5.2.2: "T.fragment = R.fragment;". -/
theorem transformReferences_fragment (strict : Bool) (base ref : Components) :
    (transformReferences strict base ref).fragment = ref.fragment := by
  unfold transformReferences transformReferencesCore
  split
  · exact (applyStrict_other_components strict base.scheme ref).2.2.2
  · split
    · exact (applyStrict_other_components strict base.scheme ref).2.2.2
    · split
      · exact (applyStrict_other_components strict base.scheme ref).2.2.2
      · split <;> exact (applyStrict_other_components strict base.scheme ref).2.2.2

/-- RFC 3986 §5.2.1: "only the scheme component is required to be present
in a base URI". These typed fields retain the grammar witnesses for every
component other than the path, whose reconstruction is separate. -/
structure ResolvedFields where
  scheme : Scheme
  authority : Option Authority
  path : List Char
  query : Option Query
  fragment : Option Fragment

/-- RFC 3986 §5.2.1: "parsed into the five main components described in
Section 3". Render each retained component witness. -/
def ResolvedFields.components (f : ResolvedFields) : Components :=
  { scheme := some f.scheme.render, authority := f.authority.map Authority.render,
    path := f.path, query := f.query.map Query.render, fragment := f.fragment.map Fragment.render }

/-- RFC 3986 §5.2.2: "(R.scheme, R.authority, R.path, R.query, R.fragment)
= parse(R);". Reference fields retain the M1 component derivation trees. -/
structure ReferenceFields where
  scheme : Option Scheme
  authority : Option Authority
  path : List Char
  query : Option Query
  fragment : Option Fragment

/-- RFC 3986 §5.2.2: "(R.scheme, R.authority, R.path, R.query, R.fragment)
= parse(R);". Render the already parsed fields; this is not a parser. -/
def ReferenceFields.components (f : ReferenceFields) : Components :=
  { scheme := f.scheme.map Scheme.render, authority := f.authority.map Authority.render,
    path := f.path, query := f.query.map Query.render, fragment := f.fragment.map Fragment.render }

/-- RFC 3986 §5.2.1: "parsed into the five main components described in
Section 3". Recover the authority witness from a hierarchical part. -/
def HierPart.authorityTree : HierPart → Option Authority
  | .authority a _ => some a
  | _ => none

/-- RFC 3986 §5.2.1: "parsed into the five main components described in
Section 3". Recover the authority witness from a relative part. -/
def RelativePart.authorityTree : RelativePart → Option Authority
  | .authority a _ => some a
  | _ => none

/-- RFC 3986 §5.2.1: "only the scheme component is required to be present
in a base URI". Extract the base's typed fields without inspecting text. -/
def ResolvedFields.ofURI (b : URI) : ResolvedFields :=
  ⟨b.scheme, b.hierPart.authorityTree, b.hierPart.pathString, b.query, b.fragment⟩

/-- RFC 3986 §5.2.2: "(R.scheme, R.authority, R.path, R.query, R.fragment)
= parse(R);". Tree typing supplies this precondition directly. -/
def ReferenceFields.ofReference : URIReference → ReferenceFields
  | .uri u =>
    ⟨some u.scheme, u.hierPart.authorityTree, u.hierPart.pathString, u.query, u.fragment⟩
  | .relative r =>
    ⟨none, r.relPart.authorityTree, r.relPart.pathString, r.query, r.fragment⟩

/-- RFC 3986 §5.2.1: "parsed into the five main components described in
Section 3". Extraction agrees with M1 component recomposition. -/
theorem ResolvedFields.ofURI_components (b : URI) :
    (ResolvedFields.ofURI b).components = b.components := by
  cases b with
  | mk s hp q f =>
    cases hp <;> rfl

/-- RFC 3986 §5.2.2: "(R.scheme, R.authority, R.path, R.query, R.fragment)
= parse(R);". Extraction agrees with M1's component functions. -/
theorem ReferenceFields.ofReference_components (x : URIReference) :
    (ReferenceFields.ofReference x).components = x.components := by
  cases x with
  | uri u =>
    obtain ⟨s, hp, q, f⟩ := u
    cases hp <;> rfl
  | relative r =>
    obtain ⟨rp, q, f⟩ := r
    cases rp <;> rfl

/-- RFC 3986 §5.2.2: "if ((not strict) and (R.scheme == Base.scheme)) then
undefine(R.scheme);". Compare rendered schemes while retaining typed
witnesses for every field. -/
def ReferenceFields.applyStrict (strict : Bool) (baseScheme : Scheme)
    (ref : ReferenceFields) : ReferenceFields :=
  if strict = false ∧ ref.scheme.map Scheme.render = some baseScheme.render then
    { ref with scheme := none }
  else ref

/-- RFC 3986 §5.2.2: "undefine(R.scheme);". Typed scheme adjustment agrees
with the component-level operation. -/
theorem ReferenceFields.applyStrict_components (strict : Bool) (scheme : Scheme)
    (ref : ReferenceFields) :
    (ref.applyStrict strict scheme).components =
      _root_.applyStrict strict (some scheme.render) ref.components := by
  unfold ReferenceFields.applyStrict _root_.applyStrict ReferenceFields.components
  split <;> rfl

/-- RFC 3986 §5.2.2: "T.scheme = Base.scheme;" and
"T.fragment = R.fragment;". Each branch copies grammar witnesses for
scheme, authority, query and fragment, applying the specified operations
only to the path. -/
def resolvedFieldsCore (base : ResolvedFields) (ref : ReferenceFields) : ResolvedFields :=
  match ref.scheme with
  | some s =>
    ⟨s, ref.authority, removeDotSegments ref.path, ref.query, ref.fragment⟩
  | none =>
    match ref.authority with
    | some a =>
      ⟨base.scheme, some a, removeDotSegments ref.path, ref.query, ref.fragment⟩
    | none =>
      if ref.path = [] then
        ⟨base.scheme, base.authority, base.path, ref.query.or base.query, ref.fragment⟩
      else if ref.path.head? = some '/' then
        ⟨base.scheme, base.authority, removeDotSegments ref.path, ref.query, ref.fragment⟩
      else
        ⟨base.scheme, base.authority,
          removeDotSegments (merge (base.authority.map Authority.render) base.path ref.path),
          ref.query, ref.fragment⟩

/-- RFC 3986 §5.2.2: "T.scheme = Base.scheme;" and
"T.fragment = R.fragment;". Retaining typed field witnesses computes
exactly the same five component branches. -/
theorem resolvedFieldsCore_components (base : ResolvedFields) (ref : ReferenceFields) :
    (resolvedFieldsCore base ref).components =
      transformReferencesCore base.components ref.components := by
  cases ref with
  | mk s a p q f =>
    cases s with
    | some s => rfl
    | none =>
      cases a with
      | some a => rfl
      | none =>
        by_cases hp : p = []
        · simp [resolvedFieldsCore, transformReferencesCore, ReferenceFields.components,
            ResolvedFields.components, hp, Option.map_or]
        · by_cases hl : p.head? = some '/'
          · simp [resolvedFieldsCore, transformReferencesCore, ReferenceFields.components,
              ResolvedFields.components, hp, hl]
          · simp [resolvedFieldsCore, transformReferencesCore, ReferenceFields.components,
              ResolvedFields.components, hp, hl]

/-- RFC 3986 §5.2.1: "only the scheme component is required to be present
in a base URI". Both strict modes retain typed witnesses for all target
components other than its path. -/
def resolvedFields (strict : Bool) (b : URI) (x : URIReference) : ResolvedFields :=
  resolvedFieldsCore (ResolvedFields.ofURI b)
    ((ReferenceFields.ofReference x).applyStrict strict b.scheme)

/-- RFC 3986 §5.2.2: "T.scheme = Base.scheme;" and
"T.fragment = R.fragment;". Typed field construction agrees with the
specified transform, uniformly in strict mode. -/
theorem resolvedFields_components (strict : Bool) (b : URI) (x : URIReference) :
    (resolvedFields strict b x).components =
      transformReferences strict b.components x.components := by
  unfold resolvedFields transformReferences
  rw [resolvedFieldsCore_components, ReferenceFields.applyStrict_components,
    ResolvedFields.ofURI_components, ReferenceFields.ofReference_components]
  rfl

set_option backward.isDefEq.respectTransparency false

/-!
# Constructing the target tree of §5.2

RFC §5.2.1: "the path component is never undefined, though it may be empty."
The reconstruction below keeps the input trees' segment witnesses.
-/

/-- §5.2.4 E moves "the first path segment"; the grammar's `pchar`
cannot contain the segment delimiter. -/
theorem PChar.slash_not_mem_render (p : PChar) : '/' ∉ p.render := by
  cases p with
  | unreserved c h =>
    simp only [PChar.render, List.mem_singleton]
    rintro rfl
    simp [IsUnreserved, IsAlpha, IsDigit] at h
  | pctEncoded p =>
    rcases p with ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    simp only [PChar.render, PctEncoded.render, List.mem_cons, List.not_mem_nil,
      or_false, not_or]
    refine ⟨by decide, ?_, ?_⟩
    · rintro rfl; simp [IsHexDig, IsDigit] at ha
    · rintro rfl; simp [IsHexDig, IsDigit] at hb
  | subDelims c h =>
    simp only [PChar.render, List.mem_singleton]
    rintro rfl
    simp [IsSubDelim] at h
  | colon => decide
  | «at» => decide

/-- §5.2.4 E moves "the first path segment"; `pchar` always renders
at least one character. -/
theorem PChar.render_ne_nil (p : PChar) : p.render ≠ [] := by
  cases p <;> simp [PChar.render, PctEncoded.render]

/-- §5.2.4 E stops "not including, the next "/" character":
a rendered `segment` has no slash. -/
theorem Segment.slash_not_mem_render (s : Segment) : '/' ∉ s.render := by
  intro h
  obtain ⟨p, _, hp⟩ := List.mem_flatMap.mp h
  exact p.slash_not_mem_render hp

/-- §5.2.4 E moves "the first path segment"; a `segment-nz`
renders a nonempty segment. -/
theorem SegmentNZ.render_ne_nil (s : SegmentNZ) : s.render ≠ [] := by
  intro h
  exact s.head.render_ne_nil (List.append_eq_nil_iff.mp h).1

/-- §5.2.4 E stops "not including, the next "/" character":
the first character of a nonempty segment is not a slash. -/
theorem SegmentNZ.render_not_slash (s : SegmentNZ) : s.render.head? ≠ some '/' := by
  intro h
  have hs : '/' ∈ s.render := List.mem_of_head? h
  exact (Segment.slash_not_mem_render (s.head :: s.tail)) hs

/-- RFC §3.3: "If a URI does not contain an authority component,
then the path cannot begin with two slash characters ("//")." -/
def ValidTargetComponents (c : Components) : Prop :=
  c.authority.isSome ∨ ¬ ['/', '/'].isPrefixOf c.path

instance (c : Components) : Decidable (ValidTargetComponents c) := by
  unfold ValidTargetComponents
  infer_instance

/-- RFC §3.3: "If a URI does not contain an authority component,
then the path cannot begin with two slash characters ("//")." -/
theorem validTargetComponents_of_uri (u : URI) : ValidTargetComponents u.components := by
  rcases u with ⟨sch, hp, q, f⟩
  cases hp with
  | authority a p => exact Or.inl rfl
  | empty p => cases p; exact Or.inr (by simp [URI.components, HierPart.pathString, PathEmpty.render])
  | rootless p =>
    right
    have h := p.first.render_not_slash
    have hn := p.first.render_ne_nil
    cases he : p.first.render with
    | nil => exact False.elim (hn he)
    | cons c cs =>
      have hc : '/' ≠ c := fun e => h (by rw [he]; exact congrArg some e.symm)
      simp [URI.components, HierPart.pathString, PathRootless.render, he,
        List.isPrefixOf, hc]
  | absolute p =>
    cases p with
    | empty => exact Or.inr (by simp [URI.components, HierPart.pathString, PathAbsolute.render])
    | nonempty first rest =>
      right
      have h := first.render_not_slash
      have hn := first.render_ne_nil
      cases he : first.render with
      | nil => exact False.elim (hn he)
      | cons c cs =>
        have hc : '/' ≠ c := fun e => h (by rw [he]; exact congrArg some e.symm)
        simp [URI.components, HierPart.pathString, PathAbsolute.render, he,
          List.isPrefixOf, hc]

/-- §5.2.4: "the first path segment". A segment tree is preserved as
a whole, including each three-character `pct-encoded` token. -/
def SegNZNCChar.toPChar : SegNZNCChar → PChar
  | .unreserved c h => .unreserved c h
  | .pctEncoded p => .pctEncoded p
  | .subDelims c h => .subDelims c h
  | .at => .at

/-- §5.2.4: "the first path segment". Forgetting the no-colon
restriction does not change its characters. -/
theorem SegNZNCChar.render_toPChar (c : SegNZNCChar) :
    c.toPChar.render = c.render := by cases c <;> rfl

/-- §5.2.4: "the first path segment". Preserve the nonempty tree. -/
def SegmentNZNC.toSegment (s : SegmentNZNC) : Segment :=
  s.head.toPChar :: s.tail.map SegNZNCChar.toPChar

/-- §5.2.4: "the first path segment". The conversion retains all
characters and percent-encoded tokens. -/
theorem SegmentNZNC.render_toSegment (s : SegmentNZNC) :
    s.toSegment.render = s.render := by
  simp [SegmentNZNC.toSegment, Segment.render, SegmentNZNC.render,
    NEList.render, List.flatMap_map, SegNZNCChar.render_toPChar]

/-- §5.2.4 E: "including the initial "/" character (if any)".
Joining known segment trees reproduces their path rendering. -/
theorem joinSlash_render_cons (s : Segment) (ss : List Segment) :
    joinSlash ((s :: ss).map Segment.render) = s.render ++ PathAbempty.render ss := by
  induction ss generalizing s with
  | nil => simp [joinSlash, PathAbempty.render]
  | cons t ts ih =>
    change s.render ++ '/' :: joinSlash ((t :: ts).map Segment.render) = _
    rw [ih]
    rfl

/-- §5.2.4 E: "including the initial "/" character (if any)".
An empty initial segment represents the leading slash. -/
theorem joinSlash_render_abempty (ss : List Segment) :
    joinSlash ([] :: ss.map Segment.render) = PathAbempty.render ss := by
  simpa [Segment.render] using joinSlash_render_cons [] ss

/-- §5.2.4 E: "the first path segment". Collect the source's existing
segment witnesses; there is no character parser here. -/
def HierPart.segmentTrees : HierPart → List Segment
  | .authority _ p => [] :: p
  | .absolute .empty => [[], []]
  | .absolute (.nonempty f r) => [] :: (f.head :: f.tail) :: r
  | .rootless p => (p.first.head :: p.first.tail) :: p.rest
  | .empty _ => [[]]

/-- §5.2.4 E: "the first path segment". Collect the relative source's
segment witnesses, converting `segment-nz-nc` without changing text. -/
def RelativePart.segmentTrees : RelativePart → List Segment
  | .authority _ p => [] :: p
  | .absolute .empty => [[], []]
  | .absolute (.nonempty f r) => [] :: (f.head :: f.tail) :: r
  | .noscheme p => p.first.toSegment :: p.rest
  | .empty _ => [[]]

/-- §5.2.4 E: "including the initial "/" character (if any)".
The source hierarchy's segment representation loses no delimiters. -/
theorem HierPart.join_segmentTrees (hp : HierPart) :
    joinSlash (hp.segmentTrees.map Segment.render) = hp.pathString := by
  cases hp with
  | authority a p => exact joinSlash_render_abempty p
  | absolute p =>
    cases p with
    | empty => rfl
    | nonempty f r =>
      change '/' :: joinSlash (((f.head :: f.tail) :: r).map Segment.render) = _
      rw [joinSlash_render_cons]
      rfl
  | rootless p =>
    simpa [HierPart.segmentTrees, HierPart.pathString, PathRootless.render,
      Segment.render, SegmentNZ.render, NEList.render, PathAbempty.render]
      using joinSlash_render_cons (p.first.head :: p.first.tail) p.rest
  | empty p => cases p; rfl

/-- §5.2.4 E: "including the initial "/" character (if any)".
The relative source's segment representation loses no delimiters. -/
theorem RelativePart.join_segmentTrees (hp : RelativePart) :
    joinSlash (hp.segmentTrees.map Segment.render) = hp.pathString := by
  cases hp with
  | authority a p => exact joinSlash_render_abempty p
  | absolute p =>
    cases p with
    | empty => rfl
    | nonempty f r =>
      change '/' :: joinSlash (((f.head :: f.tail) :: r).map Segment.render) = _
      rw [joinSlash_render_cons]
      rfl
  | noscheme p =>
    simpa [RelativePart.segmentTrees, RelativePart.pathString, PathNoscheme.render,
      SegmentNZNC.render_toSegment, PathAbempty.render]
      using joinSlash_render_cons p.first.toSegment p.rest
  | empty p => cases p; rfl

/-- §5.2.4 E: "the first path segment". The hierarchy's witnesses are
exactly its delimiter-preserving split. -/
theorem HierPart.split_segmentTrees (hp : HierPart) :
    splitSlash hp.pathString = hp.segmentTrees.map Segment.render := by
  rw [← hp.join_segmentTrees]
  apply splitSlash_joinSlash
  · cases hp with
    | absolute p => cases p <;> simp [HierPart.segmentTrees]
    | _ => simp [HierPart.segmentTrees]
  · intro s hs
    obtain ⟨w, _, rfl⟩ := List.mem_map.mp hs
    exact w.slash_not_mem_render

/-- §5.2.4 E: "the first path segment". The relative source's witnesses
are exactly its delimiter-preserving split. -/
theorem RelativePart.split_segmentTrees (hp : RelativePart) :
    splitSlash hp.pathString = hp.segmentTrees.map Segment.render := by
  rw [← hp.join_segmentTrees]
  apply splitSlash_joinSlash
  · cases hp with
    | absolute p => cases p <;> simp [RelativePart.segmentTrees]
    | _ => simp [RelativePart.segmentTrees]
  · intro s hs
    obtain ⟨w, _, rfl⟩ := List.mem_map.mp hs
    exact w.slash_not_mem_render

/-- §5.2.4 E: "move the first path segment". Recover a whole known
segment by finite search among input witnesses, not by parsing characters. -/
def recoverSegment (pool : List Segment) (s : List Char)
    (h : s ∈ pool.map Segment.render) : {w : Segment // w.render = s} :=
  match pool with
  | [] => False.elim (List.not_mem_nil h)
  | w :: ws =>
    if hw : w.render = s then ⟨w, hw⟩
    else recoverSegment ws s (by
      have hm := List.mem_cons.mp h
      exact hm.resolve_left (Ne.symm hw))

/-- §5.2.4 E: "move the first path segment". Rebuild the output's
list of segment trees using only whole source segments and empty segments. -/
def recoverSegments (pool : List Segment) (ss : List (List Char))
    (h : ∀ s ∈ ss, s = [] ∨ s ∈ pool.map Segment.render) :
    {ws : List Segment // ws.map Segment.render = ss} :=
  match ss with
  | [] => ⟨[], rfl⟩
  | s :: rest =>
    let w : {w : Segment // w.render = s} :=
      if hs : s = [] then ⟨[], hs.symm⟩
      else recoverSegment pool s ((h s (by simp)).resolve_left hs)
    let ws := recoverSegments pool rest (fun t ht => h t (by simp [ht]))
    ⟨w.val :: ws.val, by simp only [List.map_cons, w.property, ws.property]⟩

/-- RFC §3.3: "If a URI does not contain an authority component, then
the path cannot begin with two slash characters ("//")." Build the
hierarchy from recovered segment trees; the theorem below checks its shape. -/
def hierarchyFromSegments (a : Option Authority) (ss : List Segment) : HierPart :=
  match a with
  | some auth => .authority auth ss.tail
  | none => match ss with
    | [] => .empty .mk
    | [[]] => .empty .mk
    | [[], []] => .absolute .empty
    | [] :: (p :: ps) :: rest => .absolute (.nonempty ⟨p, ps⟩ rest)
    | (p :: ps) :: rest => .rootless ⟨⟨p, ps⟩, rest⟩
    | _ => .empty .mk

/-- RFC §3.3: "If a URI does not contain an authority component".
The hierarchy constructor preserves the chosen authority in every case. -/
theorem hierarchyFromSegments_authority (a : Option Authority) (ss : List Segment) :
    (hierarchyFromSegments a ss).authorityString = a.map Authority.render := by
  cases a with
  | some a => rfl
  | none => simp only [hierarchyFromSegments]; split <;> rfl

/-- §5.2.4 E: "including the initial "/" character (if any)".
A nonempty first segment starts with a non-slash character. -/
theorem joinSlash_render_nonempty_first (p : PChar) (ps : List PChar)
    (rest : List Segment) :
    (joinSlash (((p :: ps) :: rest).map Segment.render)).head? ≠ some '/' ∧
    joinSlash (((p :: ps) :: rest).map Segment.render) ≠ [] := by
  rw [joinSlash_render_cons]
  have hn := SegmentNZ.render_ne_nil ⟨p, ps⟩
  have hs := SegmentNZ.render_not_slash ⟨p, ps⟩
  change (Segment.render (p :: ps)).head? ≠ some '/' at hs
  change (Segment.render (p :: ps) ++ _).head? ≠ _ ∧ _ ≠ []
  constructor
  · simpa [List.head?_append, show Segment.render (p :: ps) ≠ [] from hn] using hs
  · intro h
    exact hn (List.append_eq_nil_iff.mp h).1

/-- RFC §3.3: "If a URI does not contain an authority component, then
the path cannot begin with two slash characters ("//")." L-A/L-B/L-C:
the guarded shape cases reconstruct exactly the recovered path. -/
theorem hierarchyFromSegments_path (a : Option Authority) (ss : List Segment)
    (ha : a.isSome → joinSlash (ss.map Segment.render) = [] ∨
      (joinSlash (ss.map Segment.render)).head? = some '/')
    (hv : a.isSome ∨ ¬ ['/', '/'].isPrefixOf (joinSlash (ss.map Segment.render))) :
    (hierarchyFromSegments a ss).pathString = joinSlash (ss.map Segment.render) := by
  cases a with
  | some a =>
    have hh := ha rfl
    cases ss with
    | nil => rfl
    | cons s rest =>
      cases s with
      | nil => exact (joinSlash_render_abempty rest).symm
      | cons p ps =>
        have hn := joinSlash_render_nonempty_first p ps rest
        exact False.elim (hh.elim hn.2 hn.1)
  | none =>
    have hv' : ¬ ['/', '/'].isPrefixOf (joinSlash (ss.map Segment.render)) := by
      simpa using hv
    cases ss with
    | nil => rfl
    | cons s rest =>
      cases s with
      | cons p ps =>
        simpa [hierarchyFromSegments, HierPart.pathString, PathRootless.render,
          SegmentNZ.render, NEList.render, Segment.render, PathAbempty.render]
          using (joinSlash_render_cons (p :: ps) rest).symm
      | nil =>
        cases rest with
        | nil => rfl
        | cons t ts =>
          cases t with
          | cons p ps =>
            change _ = '/' :: joinSlash (((p :: ps) :: ts).map Segment.render)
            rw [joinSlash_render_cons]
            rfl
          | nil =>
            cases ts with
            | nil => rfl
            | cons t ts =>
              simp [joinSlash, Segment.render] at hv'

/-- §5.2.4 E: "the first path segment". The reference supplies a
finite list of already typed segments, regardless of reference form. -/
def URIReference.segmentTrees : URIReference → List Segment
  | .uri u => u.hierPart.segmentTrees
  | .relative r => r.relPart.segmentTrees

/-- §5.2.4 E: "the first path segment". Input tree witnesses exactly
match the reference's slash-delimited components. -/
theorem URIReference.split_segmentTrees (x : URIReference) :
    splitSlash x.components.path = x.segmentTrees.map Segment.render := by
  cases x with
  | uri u => exact u.hierPart.split_segmentTrees
  | relative r => exact r.relPart.split_segmentTrees

/-- §5.2.4 E: "move the first path segment". This pool includes the
whole segments from both inputs and no parsed or synthesized nonempty token. -/
def targetSegmentPool (b : URI) (x : URIReference) : List Segment :=
  b.hierPart.segmentTrees ++ x.segmentTrees

/-- §5.2.4 E: "move the first path segment". A base segment is in the
finite pool used for constructive recovery. -/
theorem targetSegmentPool_base (b : URI) (x : URIReference) (s : List Char)
    (h : s ∈ splitSlash b.components.path) :
    s ∈ (targetSegmentPool b x).map Segment.render := by
  change s ∈ splitSlash b.hierPart.pathString at h
  rw [b.hierPart.split_segmentTrees] at h
  simpa [targetSegmentPool, List.map_append] using
    List.mem_append_left (x.segmentTrees.map Segment.render) h

/-- §5.2.4 E: "move the first path segment". A reference segment is
in the finite pool used for constructive recovery. -/
theorem targetSegmentPool_reference (b : URI) (x : URIReference) (s : List Char)
    (h : s ∈ splitSlash x.components.path) :
    s ∈ (targetSegmentPool b x).map Segment.render := by
  rw [x.split_segmentTrees] at h
  simpa [targetSegmentPool, List.map_append] using
    List.mem_append_right (b.hierPart.segmentTrees.map Segment.render) h

/-- §5.2.4: "Finally, the output buffer is returned". Whole recovered
segments rejoin to exactly that output buffer. -/
theorem recoverSegments_join (pool : List Segment) (p : List Char)
    (h : ∀ s ∈ splitSlash p, s = [] ∨ s ∈ pool.map Segment.render) :
    joinSlash ((recoverSegments pool (splitSlash p) h).val.map Segment.render) = p := by
  rw [(recoverSegments pool (splitSlash p) h).property, joinSlash_splitSlash]

/-- §5.2: "The components can then be recomposed, as described in
Section 5.3, to form the target URI." Rebuild a target from retained
typed fields and whole source segments. Equality requires the shape guard. -/
def rebuildTarget (f : ResolvedFields) (pool : List Segment)
    (h : ∀ s ∈ splitSlash f.path, s = [] ∨ s ∈ pool.map Segment.render) : URI :=
  ⟨f.scheme, hierarchyFromSegments f.authority (recoverSegments pool (splitSlash f.path) h).val,
    f.query, f.fragment⟩

/-- §5.2: "The components can then be recomposed, as described in
Section 5.3, to form the target URI." L-A/L-B/L-C with segment
conservation: under the exact shape guard, reconstruction preserves fields. -/
theorem rebuildTarget_components (f : ResolvedFields) (pool : List Segment)
    (h : ∀ s ∈ splitSlash f.path, s = [] ∨ s ∈ pool.map Segment.render)
    (ha : f.authority.isSome → f.path = [] ∨ f.path.head? = some '/')
    (hv : ValidTargetComponents f.components) :
    (rebuildTarget f pool h).components = f.components := by
  have hj := recoverSegments_join pool f.path h
  have hp := hierarchyFromSegments_path f.authority
    (recoverSegments pool (splitSlash f.path) h).val
    (by simpa only [hj] using ha)
    (by simpa [hj, ValidTargetComponents, ResolvedFields.components] using hv)
  simp only [rebuildTarget, URI.components, ResolvedFields.components,
    hierarchyFromSegments_authority, hp, hj]

/-- RFC §3.3: "If a URI contains an authority component, then the path
component must either be empty or begin with a slash ("/") character."
This is the input shape used by §5.2's authority branches. -/
def AuthorityPathShape (c : Components) : Prop :=
  c.authority.isSome → c.path = [] ∨ c.path.head? = some '/'

/-- RFC §3.3: "If a URI contains an authority component, then the path
component must either be empty or begin with a slash ("/") character." -/
theorem URI.authorityPathShape (u : URI) : AuthorityPathShape u.components := by
  rcases u with ⟨s, hp, q, f⟩
  cases hp with
  | authority a p =>
    cases p with
    | nil => exact fun _ => Or.inl rfl
    | cons s ss => exact fun _ => Or.inr rfl
  | _ => simp [AuthorityPathShape, URI.components, HierPart.authorityString]

/-- RFC §3.3: "If a URI contains an authority component, then the path
component must either be empty or begin with a slash ("/") character." -/
theorem URIReference.authorityPathShape (x : URIReference) : AuthorityPathShape x.components := by
  cases x with
  | uri u => exact u.authorityPathShape
  | relative r =>
    rcases r with ⟨rp, q, f⟩
    cases rp with
    | authority a p =>
      cases p with
      | nil => exact fun _ => Or.inl rfl
      | cons s ss => exact fun _ => Or.inr rfl
    | _ => simp [AuthorityPathShape, URIReference.components, RelativeRef.components,
        RelativePart.authorityString]

/-- §5.2.2: "undefine(R.scheme);". The optional adjustment preserves
the authority/path shape because neither of those fields changes. -/
theorem applyStrict_authorityPathShape (strict : Bool) (bs : Option (List Char))
    (ref : Components) (h : AuthorityPathShape ref) :
    AuthorityPathShape (applyStrict strict bs ref) := by
  unfold applyStrict
  split <;> exact h

/-- §5.2.2 Branch 3: "T.path = Base.path;" and
"T.authority = Base.authority;". L-D reuses the base hierarchy's shape. -/
theorem target_shape_empty_path (b : URI) (ref : Components)
    (hs : ref.scheme = none) (ha : ref.authority = none) (hp : ref.path = []) :
    ValidTargetComponents (transformReferencesCore b.components ref) := by
  rw [transformReferencesCore_empty_path b.components ref hs ha hp]
  exact validTargetComponents_of_uri b

/-- §5.2.2: "T.authority = R.authority;" or
"T.authority = Base.authority;". Once the adjusted reference has no
scheme, an authority-bearing base guarantees target validity. -/
theorem transformReferencesCore_valid_of_authority (base ref : Components)
    (hb : base.authority.isSome) (hr : ref.scheme = none ∨ ref.authority.isSome) :
    ValidTargetComponents (transformReferencesCore base ref) := by
  unfold transformReferencesCore
  split
  · rename_i hs
    rcases hr with hr | hr
    · simp [hr] at hs
    · exact Or.inl hr
  · split
    · rename_i ha
      exact Or.inl ha
    · split
      · exact Or.inl hb
      · split <;> exact Or.inl hb

/-- §5.2.2: "T.authority = R.authority;" or
"T.authority = Base.authority;". This URI-reference wrapper also covers
legacy `http:g` after its scheme has been undefined. -/
theorem transformReferences_valid_of_authority (strict : Bool) (b : URI) (x : URIReference)
    (hb : b.components.authority.isSome)
    (hr : (applyStrict strict b.components.scheme x.components).scheme = none ∨
      x.components.authority.isSome) :
    ValidTargetComponents (transformReferences strict b.components x.components) := by
  apply transformReferencesCore_valid_of_authority _ _ hb
  simpa only [(applyStrict_other_components strict b.components.scheme x.components).1] using hr

/-- §5.2.2: "T.authority = Base.authority;". A `relative-ref` has
no scheme, so this validity result is unconditional for an authority base. -/
theorem transformReferences_relative_valid (strict : Bool) (b : URI) (r : RelativeRef)
    (hb : b.components.authority.isSome) :
    ValidTargetComponents (transformReferences strict b.components r.components) := by
  apply transformReferences_valid_of_authority strict b (.relative r) hb
  left
  simp [applyStrict, URIReference.components, RelativeRef.components, URI.components]

/-- §5.2.2: "T.path = Base.path;", "T.path = remove_dot_segments(R.path);",
or "T.path = merge(Base.path, R.path);" followed by dot removal.
L-E: every nonempty target segment comes from one of the two inputs. -/
theorem transformReferences_segment_conservation (strict : Bool) (base ref : Components)
    (s : List Char) (h : s ∈ splitSlash (transformReferences strict base ref).path) :
    s = [] ∨ s ∈ splitSlash base.path ∨ s ∈ splitSlash ref.path := by
  have ho := applyStrict_other_components strict base.scheme ref
  unfold transformReferences transformReferencesCore at h
  split at h
  · rcases rds_segment_conservation _ s h with he | hm
    · exact Or.inl he
    · exact Or.inr (Or.inr (ho.2.1 ▸ hm))
  · split at h
    · rcases rds_segment_conservation _ s h with he | hm
      · exact Or.inl he
      · exact Or.inr (Or.inr (ho.2.1 ▸ hm))
    · split at h
      · exact Or.inr (Or.inl h)
      · split at h
        · rcases rds_segment_conservation _ s h with he | hm
          · exact Or.inl he
          · exact Or.inr (Or.inr (ho.2.1 ▸ hm))
        · rcases rds_segment_conservation _ s h with he | hm
          · exact Or.inl he
          · have hc := merge_segment_conservation _ _ _ s hm
            simpa only [ho.2.1] using hc

/-- §5.2.4 E: "move the first path segment". L-E supplies exactly
the finite witness-pool membership needed to rebuild the target path. -/
theorem targetSegmentPool_covers (strict : Bool) (b : URI) (x : URIReference)
    (s : List Char) (h : s ∈ splitSlash (resolvedFields strict b x).path) :
    s = [] ∨ s ∈ (targetSegmentPool b x).map Segment.render := by
  have hf := congrArg Components.path (resolvedFields_components strict b x)
  change (resolvedFields strict b x).path = _ at hf
  rw [hf] at h
  rcases transformReferences_segment_conservation strict b.components x.components s h with
    he | hb | hx
  · exact Or.inl he
  · exact Or.inr (targetSegmentPool_base b x s hb)
  · exact Or.inr (targetSegmentPool_reference b x s hx)

/-- §5.2.4 B/C: "replace that prefix with "/" in the input buffer".
The shape required by authority-bearing paths survives dot removal. -/
theorem rds_authorityPathShape (p : List Char) (h : p = [] ∨ p.head? = some '/') :
    removeDotSegments p = [] ∨ (removeDotSegments p).head? = some '/' := by
  rcases h with rfl | hs
  · exact Or.inl removeDotSegments_nil
  · exact Or.inr (rds_leading_slash p hs)

/-- §5.2.2: "T.path = remove_dot_segments(R.path);" or
"T.path = merge(Base.path, R.path);". L-A: the five branches preserve
the empty-or-slash path shape whenever the output has an authority. -/
theorem transformReferencesCore_authorityPathShape (base ref : Components)
    (hb : AuthorityPathShape base) (hr : AuthorityPathShape ref) :
    AuthorityPathShape (transformReferencesCore base ref) := by
  unfold transformReferencesCore
  split
  · exact fun ha => rds_authorityPathShape _ (hr ha)
  · split
    · exact fun ha => rds_authorityPathShape _ (hr ha)
    · split
      · exact hb
      · split
        · rename_i hs
          exact fun _ => Or.inr (rds_leading_slash _ hs)
        · intro ha
          apply Or.inr
          apply rds_leading_slash
          cases he : base.authority with
          | none => simp [he] at ha
          | some a =>
            simpa only [he] using merge_authority_leading_slash a base.path ref.path (hb ha)

/-- §5.2.2: "T.authority = R.authority;" or
"T.authority = Base.authority;". L-A holds in both strict modes. -/
theorem transformReferences_authorityPathShape (strict : Bool) (b : URI) (x : URIReference) :
    AuthorityPathShape (transformReferences strict b.components x.components) := by
  exact transformReferencesCore_authorityPathShape _ _ b.authorityPathShape
    (applyStrict_authorityPathShape strict b.components.scheme x.components x.authorityPathShape)

/-- §5.2.1: "only the scheme component is required to be present in a
base URI". L-A transfers the path shape to the retained typed fields. -/
theorem resolvedFields_authorityPathShape (strict : Bool) (b : URI) (x : URIReference) :
    (resolvedFields strict b x).authority.isSome →
      (resolvedFields strict b x).path = [] ∨
      (resolvedFields strict b x).path.head? = some '/' := by
  have hs := transformReferences_authorityPathShape strict b x
  rw [← resolvedFields_components strict b x] at hs
  simpa [AuthorityPathShape, ResolvedFields.components] using hs

/-- §5.2: "The components can then be recomposed, as described in
Section 5.3, to form the target URI." This total constructive interface
requires the exact grammar guard; no choice or character parser is used.
The proof parameter restricts the interface, while whole segment recovery
computes its result independently of the guard's proof term. -/
def target (strict : Bool) (b : URI) (x : URIReference)
    (_h : ValidTargetComponents (transformReferences strict b.components x.components)) : URI :=
  rebuildTarget (resolvedFields strict b x) (targetSegmentPool b x)
    (targetSegmentPool_covers strict b x)

/-- §5.2: "converting a URI reference that might be relative to a
given base URI into the parsed components of the reference's target."
The guarded constructive tree has exactly those components. -/
theorem target_components (strict : Bool) (b : URI) (x : URIReference)
    (h : ValidTargetComponents (transformReferences strict b.components x.components)) :
    (target strict b x h).components = transformReferences strict b.components x.components := by
  unfold target
  rw [rebuildTarget_components _ _ _ (resolvedFields_authorityPathShape strict b x)
    (by simpa only [resolvedFields_components] using h)]
  exact resolvedFields_components strict b x

/-- §5.2: "The components can then be recomposed, as described in
Section 5.3, to form the target URI." The grammar guard is necessary
and sufficient for a target with exactly the transformed components. -/
theorem target_valid_iff (strict : Bool) (b : URI) (x : URIReference) :
    (∃ t : URI, t.components = transformReferences strict b.components x.components) ↔
      ValidTargetComponents (transformReferences strict b.components x.components) := by
  constructor
  · rintro ⟨t, ht⟩
    rw [← ht]
    exact validTargetComponents_of_uri t
  · intro h
    exact ⟨target strict b x h, target_components strict b x h⟩

/-- §5.2: "The components can then be recomposed, as described in
Section 5.3, to form the target URI." This is the composition with
M1's already proved grammar/recomposition bridge. -/
theorem target_render (strict : Bool) (b : URI) (x : URIReference)
    (h : ValidTargetComponents (transformReferences strict b.components x.components)) :
    (target strict b x h).render = recompose (transformReferences strict b.components x.components) := by
  rw [← URI.recompose_components, target_components]

/-- §5.2.2: "T.authority = R.authority;" or
"T.authority = Base.authority;". Every relative reference against an
authority-bearing base has a target, with no validity guard from callers.
This covers the 40 RelativeRef examples #2–#41 of §5.4. -/
def targetRelOfAuthority (strict : Bool) (b : URI) (hb : b.components.authority.isSome)
    (r : RelativeRef) : URI :=
  target strict b (.relative r) (transformReferences_relative_valid strict b r hb)

/-- §5.2.2: "T.authority = R.authority;" or
"T.authority = Base.authority;". The unconditional relative target
has precisely the specified transform components. -/
theorem targetRelOfAuthority_components (strict : Bool) (b : URI)
    (hb : b.components.authority.isSome) (r : RelativeRef) :
    (targetRelOfAuthority strict b hb r).components =
      transformReferences strict b.components r.components :=
  target_components strict b (.relative r) _

/-- §5.2: "The components can then be recomposed, as described in
Section 5.3, to form the target URI." The authority corollary composes
with the same M1 bridge. -/
theorem targetRelOfAuthority_render (strict : Bool) (b : URI)
    (hb : b.components.authority.isSome) (r : RelativeRef) :
    (targetRelOfAuthority strict b hb r).render =
      recompose (transformReferences strict b.components r.components) :=
  target_render strict b (.relative r) _

/-- §5.2.2: "A non-strict parser may ignore a scheme in the reference
if it is identical to the base URI's scheme." The URI-reference wrapper
also admits legacy `http:g`; scheme-bearing Branch 1 still needs its guard. -/
def targetReferenceOfAuthority (strict : Bool) (b : URI) (hb : b.components.authority.isSome)
    (x : URIReference)
    (hr : (applyStrict strict b.components.scheme x.components).scheme = none ∨
      x.components.authority.isSome) : URI :=
  target strict b x (transformReferences_valid_of_authority strict b x hb hr)

/-- §5.2: "The components can then be recomposed, as described in
Section 5.3, to form the target URI." This wrapper preserves all five
fields after the strict-undefine step. -/
theorem targetReferenceOfAuthority_components (strict : Bool) (b : URI)
    (hb : b.components.authority.isSome) (x : URIReference)
    (hr : (applyStrict strict b.components.scheme x.components).scheme = none ∨
      x.components.authority.isSome) :
    (targetReferenceOfAuthority strict b hb x hr).components =
      transformReferences strict b.components x.components :=
  target_components strict b x _

/-- §5.2: "The components can then be recomposed, as described in
Section 5.3, to form the target URI." The wrapper covers 41/43 §5.4
assertions, excluding `g:h` and strict `http:g` in Branch 1. -/
theorem targetReferenceOfAuthority_render (strict : Bool) (b : URI)
    (hb : b.components.authority.isSome) (x : URIReference)
    (hr : (applyStrict strict b.components.scheme x.components).scheme = none ∨
      x.components.authority.isSome) :
    (targetReferenceOfAuthority strict b hb x hr).render =
      recompose (transformReferences strict b.components x.components) :=
  target_render strict b x _


/-- §5.2.2: "if defined(R.scheme) then". When the existing reference
tree's scheme is undefined, its constructor must be `relative`; extracting
that subtree performs no parsing. -/
def relativeRefOfNoScheme : (x : URIReference) → x.components.scheme = none → RelativeRef
  | .relative r, _ => r
  | .uri u, h => False.elim (by
      simp [URIReference.components, URI.components] at h)

/-- §5.2.2: "if defined(R.scheme) then". Extracting the no-scheme
relative subtree preserves the original reference tree exactly. -/
theorem relativeRefOfNoScheme_eq (x : URIReference) (h : x.components.scheme = none) :
    URIReference.relative (relativeRefOfNoScheme x h) = x := by
  cases x with
  | uri u => simp [URIReference.components, URI.components] at h
  | relative r => rfl

/-- §5.2.1: "parsed into the five main components". Extracting an
already parsed relative subtree preserves all five components. -/
theorem relativeRefOfNoScheme_components (x : URIReference)
    (h : x.components.scheme = none) :
    (relativeRefOfNoScheme x h).components = x.components := by
  exact congrArg URIReference.components (relativeRefOfNoScheme_eq x h)

/-- RFC 3986 §5.2.2: "T.authority = R.authority;" or
"T.authority = Base.authority;". A URI with a defined authority carries
an actual `path-abempty` derivation, not only a leading-slash condition. -/
theorem URI.path_abempty_of_authority (u : URI) (ha : u.components.authority.isSome) :
    ∃ p : PathAbempty, p.render = u.components.path := by
  obtain ⟨s, hp, q, f⟩ := u
  cases hp with
  | authority a p => exact ⟨p, rfl⟩
  | absolute p => simp [URI.components, HierPart.authorityString] at ha
  | rootless p => simp [URI.components, HierPart.authorityString] at ha
  | empty p => simp [URI.components, HierPart.authorityString] at ha

/-- RFC 3986 §5.2.2: "if (R.path starts-with "/") then".
For a grammar URI with no authority, a slash-led path supplies a
`path-absolute` derivation. -/
theorem URI.path_absolute_of_slash (u : URI) (ha : u.components.authority = none)
    (hp : u.components.path.head? = some '/') :
    ∃ p : PathAbsolute, p.render = u.components.path := by
  obtain ⟨s, hier, q, f⟩ := u
  cases hier with
  | authority a p => simp [URI.components, HierPart.authorityString] at ha
  | absolute p => exact ⟨p, rfl⟩
  | rootless p =>
    have hn := p.first.render_ne_nil
    have hs := p.first.render_not_slash
    cases he : p.first.render with
    | nil => exact False.elim (hn he)
    | cons c cs =>
      have hc : some c = some '/' := by
        simpa [URI.components, HierPart.pathString, PathRootless.render, he] using hp
      exact False.elim (hs (by simpa [he] using hc))
  | empty p => cases p; simp [URI.components, HierPart.pathString, PathEmpty.render] at hp

/-- RFC 3986 §5.2.2: "if (R.path == "") then" and
"if (R.path starts-with "/") then". The remaining grammar alternative,
when authority is absent, is `path-rootless`. -/
theorem URI.path_rootless_of_nonempty (u : URI) (ha : u.components.authority = none)
    (hne : u.components.path ≠ []) (hslash : u.components.path.head? ≠ some '/') :
    ∃ p : PathRootless, p.render = u.components.path := by
  obtain ⟨s, hier, q, f⟩ := u
  cases hier with
  | authority a p => simp [URI.components, HierPart.authorityString] at ha
  | absolute p =>
    cases p <;> simp [URI.components, HierPart.pathString, PathAbsolute.render] at hslash
  | rootless p => exact ⟨p, rfl⟩
  | empty p => cases p; simp [URI.components, HierPart.pathString, PathEmpty.render] at hne

/-- L-A, derived from RFC 3986 §5.2.2: "T.authority = R.authority;" or
"T.authority = Base.authority;". A defined transformed authority gives
a `path-abempty` witness without requiring callers to supply a guard. -/
theorem target_path_abempty (strict : Bool) (b : URI) (x : URIReference)
    (ha : (transformReferences strict b.components x.components).authority.isSome) :
    ∃ p : PathAbempty, p.render = (transformReferences strict b.components x.components).path := by
  let t := target strict b x (Or.inl ha)
  have ht : t.components = transformReferences strict b.components x.components :=
    target_components strict b x _
  have hat : t.components.authority.isSome := by rw [ht]; exact ha
  obtain ⟨p, hp⟩ := t.path_abempty_of_authority hat
  exact ⟨p, by rw [hp, ht]⟩

/-- L-B, derived from RFC 3986 §5.2.2: "if (R.path starts-with "/") then".
The validity guard supplies the necessary no-`//` condition when authority
is absent; with it the transformed path has a `path-absolute` witness. -/
theorem target_path_absolute (strict : Bool) (b : URI) (x : URIReference)
    (h : ValidTargetComponents (transformReferences strict b.components x.components))
    (ha : (transformReferences strict b.components x.components).authority = none)
    (hp : (transformReferences strict b.components x.components).path.head? = some '/') :
    ∃ p : PathAbsolute, p.render = (transformReferences strict b.components x.components).path := by
  let t := target strict b x h
  have ht : t.components = transformReferences strict b.components x.components :=
    target_components strict b x h
  have hat : t.components.authority = none := by rw [ht]; exact ha
  have hpt : t.components.path.head? = some '/' := by rw [ht]; exact hp
  obtain ⟨p, hp⟩ := t.path_absolute_of_slash hat hpt
  exact ⟨p, by rw [hp, ht]⟩

/-- L-C, derived from RFC 3986 §5.2.2: "if (R.path == "") then" and
"if (R.path starts-with "/") then". A nonempty transformed path with
no leading slash and no authority has a `path-rootless` witness. -/
theorem target_path_rootless (strict : Bool) (b : URI) (x : URIReference)
    (ha : (transformReferences strict b.components x.components).authority = none)
    (hne : (transformReferences strict b.components x.components).path ≠ [])
    (hp : (transformReferences strict b.components x.components).path.head? ≠ some '/') :
    ∃ p : PathRootless, p.render = (transformReferences strict b.components x.components).path := by
  have h : ValidTargetComponents (transformReferences strict b.components x.components) := by
    right
    cases he : (transformReferences strict b.components x.components).path with
    | nil => simp
    | cons c cs =>
      have hc : '/' ≠ c := fun e => hp (by rw [he]; exact congrArg some e.symm)
      simp [List.isPrefixOf, hc]
  let t := target strict b x h
  have ht : t.components = transformReferences strict b.components x.components :=
    target_components strict b x h
  have hat : t.components.authority = none := by rw [ht]; exact ha
  have hnt : t.components.path ≠ [] := by rw [ht]; exact hne
  have hpt : t.components.path.head? ≠ some '/' := by rw [ht]; exact hp
  obtain ⟨p, hp⟩ := t.path_rootless_of_nonempty hat hnt hpt
  exact ⟨p, by rw [hp, ht]⟩

/-- L-C, derived from RFC 3986 §5.2.2: "if (R.path == "") then".
An empty transformed path has the unique `path-empty` derivation. -/
theorem target_path_empty (strict : Bool) (b : URI) (x : URIReference)
    (hp : (transformReferences strict b.components x.components).path = []) :
    ∃ p : PathEmpty, p.render = (transformReferences strict b.components x.components).path :=
  ⟨.mk, hp.symm⟩

/-!
# The string-level boundary of §5.2 resolution

RFC §5.2.2: "T.path = remove_dot_segments(R.path);"
The grammar can reject the resulting recomposed string. The argument below
inspects existing derivation trees; it defines no parser.
-/

/-- §5.2.1 requires components "parsed into the five main components".
A delimiter absent from both prefixes uniquely determines that split. -/
theorem boundary_delimiter_split (d : Char) (a b x y : List Char)
    (ha : d ∉ a) (hb : d ∉ b) (h : a ++ d :: x = b ++ d :: y) :
    a = b ∧ x = y := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => simpa using h
    | cons c cs =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      exact False.elim (hb (by simp [← h.1]))
  | cons c cs ih =>
    cases b with
    | nil =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      exact False.elim (ha (by simp [h.1]))
    | cons e es =>
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, ht⟩ := h
      obtain ⟨rfl, rfl⟩ := ih es (fun hm => ha (List.mem_cons_of_mem c hm))
        (fun hm => hb (List.mem_cons_of_mem c hm)) ht
      exact ⟨rfl, rfl⟩

/-- §5.2.1 takes a parsed scheme: "only the scheme component is required
 to be present". A scheme character does not contain its `:` separator. -/
theorem SchemeChar.colon_not_mem_render (s : SchemeChar) : ':' ∉ s.render := by
  cases s with
  | alpha c hc =>
    simp only [SchemeChar.render, List.mem_singleton]
    rintro rfl
    simp [IsAlpha] at hc
  | digit c hc =>
    simp only [SchemeChar.render, List.mem_singleton]
    rintro rfl
    simp [IsDigit] at hc
  | plus => decide
  | minus => decide
  | dot => decide

/-- §5.2.1 takes a parsed scheme: "only the scheme component is required
 to be present". The scheme cannot consume its `:` separator. -/
theorem Scheme.colon_not_mem_render (s : Scheme) : ':' ∉ s.render := by
  intro h
  simp only [Scheme.render, List.mem_cons] at h
  rcases h with h | h
  · have hs := s.first.property
    rw [← h] at hs
    exact (by decide : ¬ IsAlpha ':') hs
  · obtain ⟨c, _, hc⟩ := List.mem_flatMap.mp h
    exact c.colon_not_mem_render hc

/-- §5.2.1 uses "the five main components" from the grammar; a reg-name
cannot consume the authority's `:` separator. -/
theorem RegNameChar.colon_not_mem_render (c : RegNameChar) : ':' ∉ c.render := by
  cases c with
  | unreserved c hc =>
    simp only [RegNameChar.render, List.mem_singleton]
    rintro rfl
    simp [IsUnreserved, IsAlpha, IsDigit] at hc
  | pctEncoded p =>
    rcases p with ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    simp only [RegNameChar.render, PctEncoded.render, List.mem_cons,
      List.not_mem_nil, or_false, not_or]
    refine ⟨by decide, ?_, ?_⟩
    · rintro rfl; simp [IsHexDig, IsDigit] at ha
    · rintro rfl; simp [IsHexDig, IsDigit] at hb
  | subDelims c hc =>
    simp only [RegNameChar.render, List.mem_singleton]
    rintro rfl
    simp [IsSubDelim] at hc

/-- §5.2.1 uses "the five main components" from the grammar; a reg-name
cannot consume the authority's `:` separator. -/
theorem RegName.colon_not_mem_render (r : RegName) : ':' ∉ r.render := by
  intro h
  obtain ⟨c, _, hc⟩ := List.mem_flatMap.mp h
  exact c.colon_not_mem_render hc

/-- §5.2.1 uses "the five main components" from the grammar. A port is
`*DIGIT`, so the boundary string's final `b` cannot be part of one. -/
theorem Port.b_not_mem_render (p : Port) : 'b' ∉ p.render := by
  intro h
  obtain ⟨⟨c, hc⟩, _, he⟩ := List.mem_flatMap.mp h
  simp only [List.mem_singleton] at he
  rw [← he] at hc
  exact (by decide : ¬ IsDigit 'b') hc

/-- §5.2.1 uses "the five main components" from the grammar. IPv4
addresses contain a literal dot, excluding the boundary authority `a:b`. -/
theorem IPv4Address.dot_mem_render (a : IPv4Address) : '.' ∈ a.render := by
  simp [IPv4Address.render]

/-- §5.2.1 uses "the five main components" from the grammar. IP literals
contain `[`, excluding the boundary authority `a:b`. -/
theorem IPLiteral.lbracket_mem_render (a : IPLiteral) : '[' ∈ a.render := by
  cases a <;> simp [IPLiteral.render]

/-- §5.2.2: "T.path = remove_dot_segments(R.path);" may expose an
unrenderable authority-looking substring: the grammar rejects `a:b`. -/
theorem no_authority_render_a_b (a : Authority) : a.render ≠ "a:b".toList := by
  intro h
  have hu : a.userinfo = none := by
    cases hu : a.userinfo with
    | none => rfl
    | some u =>
      have hm : '@' ∈ a.render := by simp [Authority.render, hu]
      rw [h] at hm
      contradiction
  have hc : a.host.render ++ (match a.port with
      | some p => ':' :: p.render
      | none => []) = ['a', ':', 'b'] := by
    change (a.render : List Char) = ['a', ':', 'b'] at h
    cases hp : a.port <;> simpa [Authority.render, hu, hp] using h
  cases hh : a.host with
  | ipLiteral lit =>
    have hm : '[' ∈ a.host.render := by simpa [hh, Host.render] using lit.lbracket_mem_render
    have := List.mem_append_left (match a.port with
      | some p => ':' :: p.render
      | none => []) hm
    rw [hc] at this
    contradiction
  | ipv4 ip =>
    have hm : '.' ∈ a.host.render := by simpa [hh, Host.render] using ip.dot_mem_render
    have := List.mem_append_left (match a.port with
      | some p => ':' :: p.render
      | none => []) hm
    rw [hc] at this
    contradiction
  | regName rn =>
    cases hp : a.port with
    | none =>
      have hr : rn.render = ['a', ':', 'b'] := by simpa [hh, hp, Host.render] using hc
      exact rn.colon_not_mem_render (by simp [hr])
    | some port =>
      have hr : rn.render ++ ':' :: port.render = ['a'] ++ ':' :: ['b'] := by
        simpa [hh, hp, Host.render] using hc
      have he := (boundary_delimiter_split ':' rn.render ['a'] port.render ['b']
        rn.colon_not_mem_render (by decide) hr).2
      exact port.b_not_mem_render (by simp [he])

/-- §5.2.2: "T.path = remove_dot_segments(R.path);" can expose a leading
`//`. The grammar cannot derive the resulting hierarchical part `//a:b`. -/
theorem no_hierpart_render_slashslash_a_b (hp : HierPart) :
    hp.render ≠ "//a:b".toList := by
  intro h
  cases hp with
  | empty p => cases p; contradiction
  | rootless p =>
    have hn := p.first.render_ne_nil
    have hs := p.first.render_not_slash
    cases he : p.first.render with
    | nil => exact hn he
    | cons c cs =>
      have hc : c = '/' := by
        simpa [HierPart.render, PathRootless.render, he] using congrArg List.head? h
      apply hs
      simp [he, hc]
  | absolute p =>
    cases p with
    | empty => contradiction
    | nonempty first rest =>
      have hn := first.render_ne_nil
      have hs := first.render_not_slash
      have hh : first.render ++ rest.flatMap (fun s => '/' :: Segment.render s) =
          ['/', 'a', ':', 'b'] := by
        simpa [HierPart.render, PathAbsolute.render] using h
      cases he : first.render with
      | nil => exact hn he
      | cons c cs =>
        have hc : c = '/' := by
          simpa [he] using congrArg List.head? hh
        apply hs
        simp [he, hc]
  | authority a p =>
    have hh : a.render ++ p.render = ['a', ':', 'b'] := by
      simpa [HierPart.render] using h
    have hn : '/' ∉ a.render ++ p.render := by rw [hh]; decide
    cases p with
    | nil =>
      apply no_authority_render_a_b a
      simpa [PathAbempty.render] using hh
    | cons s ss =>
      apply hn
      simp [PathAbempty.render]

/-- §5.2.2: "T.path = remove_dot_segments(R.path);" does not guarantee
that §5.3 recomposition is a grammar URI. No Appendix A tree renders
`g://a:b`: `//` forces authority, and `b` cannot be a port digit. -/
theorem no_uri_render_g_slashslash_a_b :
    ¬ ∃ t : URI, t.render = "g://a:b".toList := by
  rintro ⟨t, ht⟩
  have hq : t.query = none := by
    cases hq : t.query with
    | none => rfl
    | some q =>
      have hm : '?' ∈ t.render := by simp [URI.render, hq]
      rw [ht] at hm
      contradiction
  have hf : t.fragment = none := by
    cases hf : t.fragment with
    | none => rfl
    | some f =>
      have hm : '#' ∈ t.render := by simp [URI.render, hf]
      rw [ht] at hm
      contradiction
  have hh : t.scheme.render ++ ':' :: t.hierPart.render =
      ['g'] ++ ':' :: ['/', '/', 'a', ':', 'b'] := by
    simpa [URI.render, hq, hf, List.append_assoc] using ht
  have he := (boundary_delimiter_split ':' t.scheme.render ['g']
    t.hierPart.render ['/', '/', 'a', ':', 'b'] t.scheme.colon_not_mem_render
    (by decide) hh).2
  exact no_hierpart_render_slashslash_a_b t.hierPart he

/-- Beyond-RFC boundary pin of §5.2.4 B: "replace that prefix with
"/" in the input buffer". This is a grammar-valid relative reference. -/
def ref_slashdot_slashslash_g : RelativeRef :=
  ⟨.absolute (.nonempty nzSegDot [segEmpty, segG]), none, none⟩

/-- Beyond-RFC boundary pin of §5.2.4 B: "replace that prefix with
"/" in the input buffer". A colon is a legal `pchar` in this segment. -/
def ref_slashdot_slashslash_a_b : RelativeRef :=
  ⟨.absolute (.nonempty nzSegDot [segEmpty, [u 'a', .colon, u 'b']]), none, none⟩

/-- §5.2.1: "parsed into the five main components described in
Section 3". The first boundary input is admitted by the M1 grammar. -/
theorem ref_slashdot_slashslash_g_render :
    ref_slashdot_slashslash_g.render = "/.//g".toList := by decide

/-- §5.2.1: "parsed into the five main components described in
Section 3". The second boundary input is admitted by the M1 grammar. -/
theorem ref_slashdot_slashslash_a_b_render :
    ref_slashdot_slashslash_a_b.render = "/.//a:b".toList := by decide

/-- §5.2.2: "T.path = remove_dot_segments(R.path);". Its result can
have no authority yet a `//` path: no URI tree has those exact components. -/
theorem no_target_slashslash_g :
    ¬ ∃ t : URI, t.components = transformReferences true uri_g_h.components
      ref_slashdot_slashslash_g.components := by
  rintro ⟨t, ht⟩
  have hv := validTargetComponents_of_uri t
  rw [ht] at hv
  exact (by decide : ¬ ValidTargetComponents (transformReferences true uri_g_h.components
    ref_slashdot_slashslash_g.components)) hv

/-- §5.2: "The components can then be recomposed, as described in
Section 5.3". This boundary output serializes as an authority-bearing
string even though the transform's authority field is absent. -/
theorem recompose_smuggles_authority :
    recompose (transformReferences true uri_g_h.components
      ref_slashdot_slashslash_g.components) = "g://g".toList := by decide

/-- §5.2: "The components can then be recomposed, as described in
Section 5.3". At this boundary the recomposed string itself is outside
the grammar: the would-be port `b` is not numeric. -/
theorem no_render_slashslash_a_b :
    ¬ ∃ t : URI, t.render = recompose (transformReferences true uri_g_h.components
      ref_slashdot_slashslash_a_b.components) := by
  have he : recompose (transformReferences true uri_g_h.components
      ref_slashdot_slashslash_a_b.components) = "g://a:b".toList := by decide
  rw [he]
  exact no_uri_render_g_slashslash_a_b

/-- §5.2.2: "A non-strict parser may ignore a scheme in the reference".
These references contain no scheme, so both modes have the same boundaries. -/
theorem boundary_strict_independent (strict : Bool) :
    transformReferences strict uri_g_h.components ref_slashdot_slashslash_g.components =
      transformReferences true uri_g_h.components ref_slashdot_slashslash_g.components ∧
    transformReferences strict uri_g_h.components ref_slashdot_slashslash_a_b.components =
      transformReferences true uri_g_h.components ref_slashdot_slashslash_a_b.components := by
  cases strict <;> decide
