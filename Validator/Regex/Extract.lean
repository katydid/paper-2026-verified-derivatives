import Validator.Regex.Num
import Validator.Regex.Regex
import Validator.Regex.RegexID

namespace Regex

theorem lt_add_symbol:
  n < n + symbols (symbol s) := by
  simp only [symbols]
  omega

def extractAcc (r: Regex σ) (acc: Vector σ n): RegexID (n + symbols r) × Vector σ (n + symbols r) :=
  match r with
  | emptyset => (emptyset, acc)
  | emptystr => (emptystr, acc)
  | symbol s => (symbol (Fin.mk acc.size lt_add_symbol), Vector.snoc acc s)
  | or r1 r2 =>
    let (rid1, acc1) := extractAcc r1 acc
    let (rid2, acc2) := extractAcc r2 acc1
    (or (rid1.cast_add (symbols r2)).cast_assoc rid2.cast_assoc, acc2.cast_assoc)
  | concat r1 r2 =>
    let (rid1, acc1) := extractAcc r1 acc
    let (rid2, acc2) := extractAcc r2 acc1
    (concat (rid1.cast_add (symbols r2)).cast_assoc rid2.cast_assoc, acc2.cast_assoc)
  | star r1 => let (rid1, acc1) := extractAcc r1 acc; (star rid1, acc1)

def extract (r: Regex σ): RegexID (symbols r) × Vector σ (symbols r) :=
  let (rid, xs) := extractAcc r #v[]
  (RegexID.cast rid (by omega), Vector.cast (by omega) xs)

#guard extract (Regex.or (Regex.symbol 'a') (Regex.symbol 'b'))
  = ((Regex.or (Regex.symbol 0) (Regex.symbol 1)), #v['a', 'b'])

theorem extractAcc_append_toList (acc: Vector σ n) (r: Regex σ):
  Vector.toList (extractAcc r acc).2 = Vector.toList (acc ++ (extractAcc r #v[]).2) := by
  induction r generalizing acc n  with
  | emptyset =>
    simp only [symbols, Nat.add_zero, extractAcc, Vector.append_nil, Vector.cast_toList]
  | emptystr =>
    simp only [symbols, Nat.add_zero, extractAcc, Vector.append_nil, Vector.cast_toList]
  | symbol s =>
    simp only [extractAcc]
    rw [Vector.snoc_append]
    -- aesop?
    simp_all only [symbols, Nat.reduceAdd]
    rfl
  | or r1 r2 ih1 ih2 =>
    simp only [extractAcc]
    rw [Vector.cast_assoc]
    generalize_proofs h1 h2 h3
    rw [Vector.cast_assoc]
    generalize_proofs h4
    rw [Vector.toList_append]
    rw [Vector.cast_toList]
    rw [Vector.cast_toList]
    rw [ih2]
    rw [Vector.toList_append]
    rw [ih1]
    rw [Vector.toList_append]
    nth_rewrite 2 [ih2]
    rw [Vector.toList_append]
    -- aesop?
    simp_all only [symbols, zero_add, List.append_assoc]
  | concat r1 r2 ih1 ih2 =>
    simp only [extractAcc]
    rw [Vector.cast_assoc]
    generalize_proofs h1 h2 h3
    rw [Vector.cast_assoc]
    generalize_proofs h4
    rw [Vector.toList_append]
    rw [Vector.cast_toList]
    rw [Vector.cast_toList]
    rw [ih2]
    rw [Vector.toList_append]
    rw [ih1]
    rw [Vector.toList_append]
    nth_rewrite 2 [ih2]
    rw [Vector.toList_append]
    -- aesop?
    simp_all only [symbols, zero_add, List.append_assoc]
  | star r1 ih1 =>
    simp only [extractAcc]
    rw [ih1]

theorem extract_take_toList (acc: Vector σ l):
  (Vector.toList
    (Vector.take
      (extractAcc r2
        (extractAcc r1 acc).2).2
      (l + symbols r1)
    )
  )
  =
  (Vector.toList (extractAcc r1 acc).2) := by
  rw [Vector.toList_take]
  rw [extractAcc_append_toList]
  rw [Vector.toList_append]
  -- aesop?
  simp_all only [Vector.length_toList, List.take_left']

theorem extractAcc_take (acc: Vector σ l):
  (Vector.take
    (extractAcc r2
      (extractAcc r1 acc).2).2
    (l + symbols r1)
  )
  =
    Vector.cast
    (by omega)
    (extractAcc r1 acc).2 := by
  apply Vector.eq
  rw [extract_take_toList]
  rw [<- Vector.cast_toList]

theorem extractAcc_take_toList_fmap (acc: Vector σ l):
  (Vector.toList
    (Vector.take
      (Vector.map
        f
        (extractAcc r2
          (extractAcc r1 acc).2).2
      )
      (l + symbols r1)
    )
  )
  =
  (Vector.toList
    (Vector.map
      f
      (extractAcc r1 acc).2
    )
  ) := by
  rw [Vector.toList_take]
  rw [Vector.map_toList]
  rw [extractAcc_append_toList]
  rw [Vector.toList_append]
  rw [Vector.toList_map]
  -- aesop?
  simp_all only [List.map_append, List.length_map, Vector.length_toList,
    List.take_left']

theorem extractAcc_take_fmap (acc: Vector α l) (f: α → β):
  (Vector.take
    (Vector.map
      f
      (extractAcc r2
        (extractAcc r1 acc).2).2
    )
    (l + symbols r1)
  )
  =
    Vector.cast
    (by omega)
    (Vector.map
      f
      (extractAcc r1 acc).2
    ) := by
  apply Vector.eq
  rw [extractAcc_take_toList_fmap]
  rw [<- Vector.cast_toList]
