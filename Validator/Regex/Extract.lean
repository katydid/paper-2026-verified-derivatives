import Validator.Regex.Num
import Validator.Regex.Regex
import Validator.Regex.RegexID

namespace Regex

theorem Symbol.lt_add_symbol:
  n < n + num (symbol s) := by
  simp only [num]
  omega

def Symbol.extract (r: Regex σ) (acc: Vector σ n): RegexID (n + num r) × Vector σ (n + num r) :=
  match r with
  | emptyset => (emptyset, acc)
  | emptystr => (emptystr, acc)
  | symbol s => (symbol (Fin.mk n lt_add_symbol), Vec.snoc acc s)
  | or r1 r2 =>
    let (rid1, acc1) := extract r1 acc
    let (rid2, acc2) := extract r2 acc1
    (or (rid1.cast_add (num r2)).cast_assoc rid2.cast_assoc, acc2.cast_assoc)
  | concat r1 r2 =>
    let (rid1, acc1) := extract r1 acc
    let (rid2, acc2) := extract r2 acc1
    (concat (rid1.cast_add (num r2)).cast_assoc rid2.cast_assoc, acc2.cast_assoc)
  | star r1 => let (rid1, acc1) := extract r1 acc; (star rid1, acc1)

def Symbol.extractFrom (r: Regex σ): RegexID (num r) × Vector σ (num r) :=
  let (rid, xs) := extract r #v[]
  (RegexID.cast rid (by omega), Vec.cast xs (by omega))

end Regex

namespace Regex.Symbol

theorem extract_append_toList (acc: Vector σ n) (r: Regex σ):
  Vector.toList (extract r acc).2 = Vector.toList (Vector.append acc (extract r #v[]).2) := by
  induction r generalizing acc n  with
  | emptyset =>
    simp only [Symbol.num, Nat.add_zero, extract, Vec.append_nil, Vec.cast_toList]
  | emptystr =>
    simp only [Symbol.num, Nat.add_zero, extract, Vec.append_nil, Vec.cast_toList]
  | symbol s =>
    simp only [extract]
    rw [Vec.snoc_append]
    -- aesop?
    simp_all only [num, Nat.reduceAdd]
    rfl
  | or r1 r2 ih1 ih2 =>
    simp only [extract]
    rw [Vector.cast_assoc]
    generalize_proofs h1 h2 h3
    rw [Vector.cast_assoc]
    generalize_proofs h4
    rw [Vec.toList_append]
    rw [Vec.cast_toList]
    rw [Vec.cast_toList]
    rw [ih2]
    rw [Vec.toList_append]
    rw [ih1]
    rw [Vec.toList_append]
    nth_rewrite 2 [ih2]
    rw [Vec.toList_append]
    -- aesop?
    simp_all only [num, zero_add, List.append_eq, List.append_assoc]
  | concat r1 r2 ih1 ih2 =>
    simp only [extract]
    rw [Vector.cast_assoc]
    generalize_proofs h1 h2 h3
    rw [Vector.cast_assoc]
    generalize_proofs h4
    rw [Vec.toList_append]
    rw [Vec.cast_toList]
    rw [Vec.cast_toList]
    rw [ih2]
    rw [Vec.toList_append]
    rw [ih1]
    rw [Vec.toList_append]
    nth_rewrite 2 [ih2]
    rw [Vec.toList_append]
    -- aesop?
    simp_all only [num, zero_add, List.append_eq, List.append_assoc]
  | star r1 ih1 =>
    simp only [extract]
    rw [ih1]

theorem extract_take_toList (acc: Vector σ l):
  (Vector.toList
    (Vector.take
      (extract r2
        (extract r1 acc).2).2
      (l + Symbol.num r1)
    )
  )
  =
  (Vector.toList (extract r1 acc).2) := by
  rw [<- Vec.toList_take]
  rw [extract_append_toList]
  rw [Vec.toList_append]
  -- aesop?
  simp_all only [List.append_eq, Vector.length_toList, List.take_left']

theorem extract_take (acc: Vector σ l):
  (Vector.take
    (extract r2
      (extract r1 acc).2).2
    (l + Symbol.num r1)
  )
  =
    Vec.cast
    (extract r1 acc).2
    (by omega) := by
  apply Vec.eq
  rw [extract_take_toList]
  rw [<- Vec.cast_toList]

theorem extract_take_toList_fmap (acc: Vector σ l):
  (Vector.toList
    (Vector.take
      (Vec.map
        (extract r2
        (extract r1 acc).2).2
        f
      )
      (l + Symbol.num r1)
    )
  )
  =
  (Vector.toList
    (Vec.map
      (extract r1 acc).2
      f
    )
  ) := by
  rw [<- Vec.toList_take]
  rw [Vec.map_toList]
  rw [extract_append_toList]
  rw [Vec.toList_append]
  rw [Vec.toList_map]
  -- aesop?
  simp_all only [List.append_eq, List.map_append, List.length_map, Vector.length_toList,
    List.take_left']

theorem extract_take_fmap (acc: Vector α l) (f: α -> β):
  (Vector.take
    (Vec.map
      (extract r2
        (extract r1 acc).2).2
      f
    )
    (l + Symbol.num r1)
  )
  =
    Vec.cast
    (Vec.map
      (extract r1 acc).2
      f
    )
    (by omega) := by
  apply Vec.eq
  rw [extract_take_toList_fmap]
  rw [<- Vec.cast_toList]
