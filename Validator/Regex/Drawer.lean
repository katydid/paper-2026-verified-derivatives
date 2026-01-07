import Validator.Regex.Extract
import Validator.Regex.Replace

-- In Map.lean we have defined a map function over a regular expression:

-- inductive Regex (σ: Type) where
--   | emptyset
--   | emptystr
--   | symbol (s: σ)
--   | or (p q: Regex σ)
--   | concat (p q: Regex σ)
--   | star (p: Regex σ)
--   deriving DecidableEq, Ord, Repr, Hashable

-- def Regex.map (r: Regex σ) (f: σ → σ'): Regex σ' :=
--   match r with
--   | emptyset => emptyset
--   | emptystr => emptystr
--   | symbol s => symbol (f s)
--   | or r1 r2 => or (r1.map f) (r2.map f)
--   | concat r1 r2 => concat (r1.map f) (r2.map f)
--   | star r1 => star (r1.map f)

-- In this file we prove that if we split function application of the functor up into three steps:
-- 1. extract
-- 2. apply function
-- 3. replace
-- it is the same as Regex.map

-- We have proved functor properties:
-- * r = replace (extract r).1 (extract r).2
-- * Regex.map r f = replace (extract r).1 (Vec.map (extract r).2 f)
-- * rs = replacesFrom (extracts rs acc).1 (extracts rs acc).2
-- * Regex.maps rs f = replacesFrom (extractsFrom rs).1 (Vec.map (extractsFrom rs).2 f)

namespace Regex

theorem extractAcc_replace_is_id (r: Regex σ) (acc: Vector σ l):
  r = replace (extractAcc r acc).1 (extractAcc r acc).2 := by
  simp only [replace]
  generalize_proofs hr
  revert acc l
  induction r with
  | emptyset =>
    intro n acc hr
    simp only [replaceLE, extractAcc]
  | emptystr =>
    intro n acc hr
    simp only [replaceLE, extractAcc]
  | symbol s =>
    intro n acc hr
    simp only [replaceLE, extractAcc]
    rw [Vector.snoc_get]
  | or r1 r2 ih1 ih2 =>
    intro n acc hr
    simp only [extractAcc]
    simp only [replaceLE]
    have hh1 :
      r1 =
        (replaceLE
          (RegexID.cast_assoc (RegexID.cast_add (symbols r2) (extractAcc r1 acc).1))
          (Vector.cast_assoc (extractAcc r2 (extractAcc r1 acc).2).2)
          hr
        ) := by
      clear ih2
      rw [RegexID.cast_assoc]
      rw [Vector.cast_assoc]
      rw [<- replaceLE_cast_both]
      rw [<- replaceLE_regexid_add]
      rw [<- replaceLE_take]
      generalize_proofs h1
      rw [extractAcc_take]
      generalize_proofs h1 h2
      nth_rewrite 1 [ih1 acc]
      rw [replaceLE_cast_symbols]
      omega
    rw [<- hh1]
    clear hh1
    clear ih1
    congr
    rw [RegexID.cast_assoc]
    rw [Vector.cast_assoc]
    rw [<- replaceLE_cast_both]
    rw [<- ih2 ((extractAcc r1 acc).2)]
  | concat r1 r2 ih1 ih2 =>
    intro n acc hr
    simp only [extractAcc]
    simp only [replaceLE]
    have hh1 :
      r1 =
        (replaceLE
          (RegexID.cast_assoc (RegexID.cast_add (symbols r2) (extractAcc r1 acc).1))
          (Vector.cast_assoc (extractAcc r2 (extractAcc r1 acc).2).2)
          hr
        ) := by
      clear ih2
      rw [RegexID.cast_assoc]
      rw [Vector.cast_assoc]
      rw [<- replaceLE_cast_both]
      rw [<- replaceLE_regexid_add]
      rw [<- replaceLE_take]
      generalize_proofs h1
      rw [extractAcc_take]
      generalize_proofs h1 h2
      nth_rewrite 1 [ih1 acc]
      rw [replaceLE_cast_symbols]
      omega
    rw [<- hh1]
    clear hh1
    clear ih1
    congr
    rw [RegexID.cast_assoc]
    rw [Vector.cast_assoc]
    rw [<- replaceLE_cast_both]
    rw [<- ih2 ((extractAcc r1 acc).2)]
  | star r1 ih1 =>
    simp only [extractAcc]
    simp only [replaceLE]
    intro n acc hr
    rw [<- ih1 acc]

theorem extractAcc_replaceLE_is_id (r: Regex σ) (acc: Vector σ l):
  r = replaceLE (extractAcc r acc).1 (extractAcc r acc).2 (by omega) := by
  rw [<- replace]
  rw [<- extractAcc_replace_is_id]

lemma extract_replace_is_id : ∀ (r: Regex σ),
  r = replace (extract r).1 (extract r).2 := by
  intro r
  simp only [extract]
  simp only [replace]
  rw [<- replaceLE_cast_both]
  rw [<- extractAcc_replaceLE_is_id r #v[]]

theorem extractAcc_replace_is_fmap (r: Regex α) (acc: Vector α l) (f: α → β):
  Regex.map r f = replace (extractAcc r acc).1 (Vector.map f (extractAcc r acc).2) := by
  simp only [replace]
  generalize_proofs hr
  revert acc l
  induction r with
  | emptyset =>
    intro n acc hr
    simp only [replaceLE, extractAcc, Regex.map]
  | emptystr =>
    intro n acc hr
    simp only [replaceLE, extractAcc, Regex.map]
  | symbol s =>
    intro n acc hr
    simp only [replaceLE, extractAcc, Regex.map]
    simp only [Vector.snoc_map]
    rw [Vector.snoc_get]
  | or r1 r2 ih1 ih2 =>
    intro n acc hr
    simp only [extractAcc]
    simp only [replaceLE]
    simp only [Regex.map]
    have hh1 :
      Regex.map r1 f =
        (replaceLE
          (RegexID.cast_assoc (RegexID.cast_add (symbols r2) (extractAcc r1 acc).1))
          (Vector.map f (Vector.cast_assoc (extractAcc r2 (extractAcc r1 acc).2).2))
          hr
        ) := by
      clear ih2
      rw [RegexID.cast_assoc]
      rw [Vector.cast_assoc]
      rw [Vector.map_cast]
      rw [<- replaceLE_cast_both]
      rw [<- replaceLE_regexid_add]
      rw [<- replaceLE_take]
      generalize_proofs h1
      rw [extractAcc_take_fmap]
      generalize_proofs h1 h2
      have ih1' := ih1 acc
      nth_rewrite 1 [ih1']
      rw [replaceLE_cast_symbols]
      omega
    rw [<- hh1]
    clear hh1
    clear ih1
    congr
    rw [RegexID.cast_assoc]
    rw [Vector.cast_assoc]
    rw [Vector.map_cast]
    rw [<- replaceLE_cast_both]
    rw [<- ih2 ((extractAcc r1 acc).2)]
  | concat r1 r2 ih1 ih2 =>
    intro n acc hr
    simp only [extractAcc]
    simp only [replaceLE]
    simp only [Regex.map]
    have hh1 :
      Regex.map r1 f =
        (replaceLE
          (RegexID.cast_assoc (RegexID.cast_add (symbols r2) (extractAcc r1 acc).1))
          (Vector.map f (Vector.cast_assoc (extractAcc r2 (extractAcc r1 acc).2).2))
          hr
        ) := by
      clear ih2
      rw [RegexID.cast_assoc]
      rw [Vector.cast_assoc]
      rw [Vector.map_cast]
      rw [<- replaceLE_cast_both]
      rw [<- replaceLE_regexid_add]
      rw [<- replaceLE_take]
      generalize_proofs h1
      rw [extractAcc_take_fmap]
      generalize_proofs h1 h2
      have ih1' := ih1 acc
      nth_rewrite 1 [ih1']
      rw [replaceLE_cast_symbols]
      omega
    rw [<- hh1]
    clear hh1
    clear ih1
    congr
    rw [RegexID.cast_assoc]
    rw [Vector.cast_assoc]
    rw [Vector.map_cast]
    rw [<- replaceLE_cast_both]
    rw [<- ih2 ((extractAcc r1 acc).2)]
  | star r1 ih1 =>
    simp only [extractAcc]
    simp only [replaceLE]
    intro n acc hr
    rw [<- ih1 acc]
    simp only [Regex.map]

theorem extractAcc_replaceLE_is_fmap (r: Regex α) (acc: Vector α l) (f: α → β):
  Regex.map r f = replaceLE (extractAcc r acc).1 (Vector.map f (extractAcc r acc).2) (by omega) := by
  rw [<- replace]
  rw [<- extractAcc_replace_is_fmap]

lemma extract_replace_is_map:
  ∀ (r: Regex α) (f: α → β),
  Regex.map r f = replace (extract r).1 (Vector.map f (extract r).2) := by
  intro r f
  simp only [extract]
  simp only [replace]
  rw [Vector.map_cast]
  rw [<- replaceLE_cast_both]
  rw [<- extractAcc_replaceLE_is_fmap r #v[]]
