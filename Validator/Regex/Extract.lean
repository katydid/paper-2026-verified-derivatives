import Validator.Regex.Num
import Validator.Regex.Regex
import Validator.Regex.RegexID

namespace Regex

theorem Symbol.lt_add_symbol:
  n < n + num (symbol s) := by
  simp only [num]
  omega

def Symbol.extract (r: Regex σ) (acc: Vec σ n): RegexID (n + num r) × Vec σ (n + num r) :=
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

def Symbol.extractFrom (r: Regex σ): RegexID (num r) × Vec σ (num r) :=
  let (rid, xs) := extract r Vec.nil
  (RegexID.cast rid (by omega), Vec.cast xs (by omega))

end Regex

namespace Regex.Symbol

theorem extract_append_toList (acc: Vec σ n) (r: Regex σ):
  Vec.toList (extract r acc).2 = Vec.toList (Vec.append acc (extract r Vec.nil).2) := by
  induction r generalizing acc n  with
  | emptyset =>
    simp only [Symbol.num, Nat.add_zero, extract, Vec.append_nil, Vec.cast_toList]
  | emptystr =>
    simp only [Symbol.num, Nat.add_zero, extract, Vec.append_nil, Vec.cast_toList]
  | symbol s =>
    simp only [extract, Vec.snoc]
    rw [Vec.snoc_append]
  | or r1 r2 ih1 ih2 =>
    simp only [extract]
    rw [Vec.cast_assoc]
    generalize_proofs h1 h2 h3
    rw [Vec.cast_assoc]
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
    ac_rfl
  | concat r1 r2 ih1 ih2 =>
    simp only [extract]
    rw [Vec.cast_assoc]
    generalize_proofs h1 h2 h3
    rw [Vec.cast_assoc]
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
    ac_rfl
  | star r1 ih1 =>
    simp only [extract]
    rw [ih1]

theorem extract_append (acc: Vec σ l) (r: Regex σ):
  (extract r acc).2 = Vec.cast (Vec.append acc (extract r Vec.nil).2) (by omega) := by
  apply Vec.eq
  rw [extract_append_toList]
  rw [<- Vec.cast_toList]

theorem extract_take_toList (acc: Vec σ l):
  (Vec.toList
    (Vec.take
      (l + Symbol.num r1)
      (extract r2
      (extract r1 acc).2).2
    )
  )
  =
  (Vec.toList (extract r1 acc).2) := by
  rw [<- Vec.toList_take]
  rw [extract_append_toList]
  rw [Vec.toList_append]
  rw [List.take_left']
  rw [Vec.toList_length]

theorem extract_take (acc: Vec σ l):
  (Vec.take
    (l + Symbol.num r1)
    (extract r2
      (extract r1 acc).2).2
  )
  =
    Vec.cast
    (extract r1 acc).2
    (by omega) := by
  apply Vec.eq
  rw [extract_take_toList]
  rw [<- Vec.cast_toList]

theorem extract_take_toList_fmap (acc: Vec σ l):
  (Vec.toList
    (Vec.take
      (l + Symbol.num r1)
      (Vec.map
        (extract r2
        (extract r1 acc).2).2
        f
      )
    )
  )
  =
  (Vec.toList
    (Vec.map
      (extract r1 acc).2
      f
    )
  ) := by
  rw [<- Vec.toList_take]
  rw [Vec.map_toList]
  rw [extract_append_toList]
  rw [Vec.toList_append]
  simp_all only [List.map_append, Vec.toList_map]
  rw [List.take_left']
  rw [<- Vec.map_toList]
  rw [Vec.toList_length]

theorem extract_take_fmap (acc: Vec α l) (f: α -> β):
  (Vec.take
    (l + Symbol.num r1)
    (Vec.map
      (extract r2
        (extract r1 acc).2).2
      f
    )
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

theorem extract_lift_cast (r: Regex α) (acc: Vec α n) (h1: n + Symbol.num r = l + Symbol.num r) (h2: n = l):
  (Vec.cast (extract r acc).2 h1) = (extract r (Vec.cast acc h2)).2 := by
  subst h2
  rfl

theorem extract_lift_cast_1 (r: Regex α) (acc: Vec α n) (h1: n + Symbol.num r = l + Symbol.num r) (h2: n = l):
  RegexID.cast (extract r acc).1 h1 = (extract r (Vec.cast acc h2)).1 := by
  subst h2
  rfl

theorem extract_is_fmap_2 (r: Regex α) (acc: Vec α n) (f: α -> β):
  (extract (Regex.map r f) (Vec.map acc f)).2 = Vec.cast (Vec.map (extract r acc).2 f) (by rw [Symbol.num_map]) := by
  generalize_proofs hr
  fun_induction extract with
  | case1 =>
    apply Vec.eq
    simp only [extract, Regex.map]
    rfl
  | case2 =>
    apply Vec.eq
    simp only [extract, Regex.map]
    rfl
  | case3 =>
    apply Vec.eq
    simp only [extract, Regex.map, Symbol.num]
    rw [Vec.cast_toList]
    rw [Vec.snoc_map]
  | case4 acc r1 r2 er1 acc1 he1 er2 acc2 he2 ih1 ih2 => -- or
    rename_i n
    simp [Regex.map] at *
    have hacc1 : acc1 = (extract r1 acc).2 := by
      rw [he1]
    have hacc2 : acc2 = (extract r2 (extract r1 acc).2).2 := by
      rw [<- hacc1]
      rw [he2]
    rw [hacc2]
    rw [hacc1] at ih2
    have ih1' := ih1 (by rw [Symbol.num_map])
    clear ih1
    have ih2' := ih2 (by rw [Symbol.num_map])
    clear ih2
    simp only [extract]
    simp only [Vec.cast_assoc]
    rw [ih1']
    have hh: n + Symbol.num r1 + Symbol.num (r2.map f) = n + Symbol.num (r1.map f) + Symbol.num (r2.map f) := by
      repeat rw [Symbol.num_map]
    rw [<- extract_lift_cast (h1 := hh)]
    rw [ih2']
    apply Vec.eq
    rw [Vec.map_cast]
    repeat rw [Vec.cast_cast]
  | case5 acc r1 r2 er1 acc1 he1 er2 acc2 he2 ih1 ih2 => -- concat
    rename_i n
    simp only [Regex.map] at *
    have hacc1 : acc1 = (extract r1 acc).2 := by
      rw [he1]
    have hacc2 : acc2 = (extract r2 (extract r1 acc).2).2 := by
      rw [<- hacc1]
      rw [he2]
    rw [hacc2]
    rw [hacc1] at ih2
    have ih1' := ih1 (by rw [Symbol.num_map])
    clear ih1
    have ih2' := ih2 (by rw [Symbol.num_map])
    clear ih2
    simp only [extract]
    simp only [Vec.cast_assoc]
    rw [ih1']
    have hh: n + Symbol.num r1 + Symbol.num (r2.map f) = n + Symbol.num (r1.map f) + Symbol.num (r2.map f) := by
      repeat rw [Symbol.num_map]
    rw [<- extract_lift_cast (h1 := hh)]
    rw [ih2']
    apply Vec.eq
    rw [Vec.map_cast]
    congr 1
    simp only [Vec.cast_cast]
  | case6 acc r1 er1 acc1 he ih1 => -- star
    simp only [Nat.add_left_cancel_iff, Regex.map, Symbol.num] at *
    have hacc1 : acc1 = (extract r1 acc).2 := by
      rw [he]
    rw [hacc1]
    rw [<- ih1]
    rfl
    rw [Symbol.num_map]

theorem extract_is_fmap_1 (r: Regex α) (acc: Vec α n) (f: α -> β):
  (extract (Regex.map r f) (Vec.map acc f)).1 = RegexID.cast (extract r acc).1 (by simp only [Symbol.num_map]) := by
  generalize_proofs hr
  fun_induction extract with
  | case1 =>
    simp only [Regex.map, extract, RegexID.cast]
  | case2 =>
    simp only [Regex.map, extract, RegexID.cast]
  | case3 =>
    simp only [Regex.map, extract, RegexID.cast]
  | case4 acc r1 r2 er1 acc1 he1 er2 acc2 he2 ih1 ih2 =>
    rename_i n

    have hacc1 : acc1 = (extract r1 acc).2 := by
      rw [he1]
    have hacc2 : acc2 = (extract r2 (extract r1 acc).2).2 := by
      rw [<- hacc1]
      rw [he2]
    have her1 : er1 = (extract r1 acc).1 := by
      rw [he1]
    have her2 : er2 = (extract r2 (extract r1 acc).2).1 := by
      rw [<- hacc1]
      rw [he2]
    rw [hacc1] at ih2
    clear he1
    clear he2

    subst_vars

    have hr1: n + Symbol.num r1 = n + Symbol.num (r1.map f) := by
      rw [Symbol.num_map]
    have ih1' := ih1 hr1
    clear ih1
    have hr2: n + Symbol.num r1 + Symbol.num r2 = n + Symbol.num r1 + Symbol.num (r2.map f) := by
      rw [Symbol.num_map]
    have ih2' := ih2 hr2
    clear ih2

    simp only [Regex.map]
    simp only [extract]

    rw [ih1']
    rw [extract_is_fmap_2]
    generalize_proofs
    have hhlift : n + Symbol.num r1 + Symbol.num (r2.map f) = n + Symbol.num (r1.map f) + Symbol.num (r2.map f) := by
      repeat rw [Symbol.num_map]
    have hlift := extract_lift_cast_1 (r := r2.map f) (acc := Vec.map (extract r1 acc).2 f) (h2 := hr1) (h1 := hhlift)
    rw [<- hlift]
    clear hlift
    rw [ih2']
    clear ih1'
    clear ih2'

    simp only [RegexID.cast_add]
    simp only [RegexID.cast_assoc]
    repeat rw [RegexID.cast_is_cast_map]
    unfold RegexID.cast_map
    simp only [Regex.map_map]
    congr 1
    · simp only [Symbol.num, Fin.castLE_castLE, Regex.map_map]
    · simp only [Symbol.num, Fin.castLE_castLE, Regex.map_map]
  | case5 acc r1 r2 er1 acc1 he1 er2 acc2 he2 ih1 ih2 =>
    rename_i n

    have hacc1 : acc1 = (extract r1 acc).2 := by
      rw [he1]
    have hacc2 : acc2 = (extract r2 (extract r1 acc).2).2 := by
      rw [<- hacc1]
      rw [he2]
    have her1 : er1 = (extract r1 acc).1 := by
      rw [he1]
    have her2 : er2 = (extract r2 (extract r1 acc).2).1 := by
      rw [<- hacc1]
      rw [he2]
    rw [hacc1] at ih2
    clear he1
    clear he2

    subst_vars

    have hr1: n + Symbol.num r1 = n + Symbol.num (r1.map f) := by
      rw [Symbol.num_map]
    have ih1' := ih1 hr1
    clear ih1
    have hr2: n + Symbol.num r1 + Symbol.num r2 = n + Symbol.num r1 + Symbol.num (r2.map f) := by
      rw [Symbol.num_map]
    have ih2' := ih2 hr2
    clear ih2

    simp only [Regex.map]
    simp only [extract]

    rw [ih1']
    rw [extract_is_fmap_2]
    generalize_proofs
    have hhlift : n + Symbol.num r1 + Symbol.num (r2.map f) = n + Symbol.num (r1.map f) + Symbol.num (r2.map f) := by
      repeat rw [Symbol.num_map]
    have hlift := extract_lift_cast_1 (r := r2.map f) (acc := Vec.map (extract r1 acc).2 f) (h2 := hr1) (h1 := hhlift)
    rw [<- hlift]
    rw [ih2']

    simp only [RegexID.cast_add]
    simp only [RegexID.cast_assoc]
    repeat rw [RegexID.cast_is_cast_map]
    unfold RegexID.cast_map
    simp only [Regex.map_map]
    congr 1
    · simp only [Symbol.num, Fin.castLE_castLE, Regex.map_map]
    · simp only [Symbol.num, Fin.castLE_castLE, Regex.map_map]
  | case6 acc r1 er1 acc1 he1 ih1 =>
    rename_i n

    have hacc1 : acc1 = (extract r1 acc).2 := by
      rw [he1]
    have her1 : er1 = (extract r1 acc).1 := by
      rw [he1]
    clear he1

    subst_vars

    have hr1: n + Symbol.num r1 = n + Symbol.num (r1.map f) := by
      rw [Symbol.num_map]
    have ih1' := ih1 hr1
    clear ih1

    simp only [Regex.map]
    simp only [extract]

    rw [ih1']
    generalize (extract r1 acc).1 = rid

    repeat rw [RegexID.cast_is_cast_map]
    unfold RegexID.cast_map
    simp only [Regex.map]
