import Mathlib.Tactic.NthRewrite
import Mathlib.Tactic.RewriteSearch

namespace List

abbrev ElemOf {α: Type} (xs: List α) := { y: α // y ∈ xs }

def ElemOf.mk {α: Type} (y: α) (xs: List α) (property : y ∈ xs) : ElemOf xs :=
  (Subtype.mk y property)

def ElemOf.self {α: Type} (x: α) : ElemOf [x] :=
  (Subtype.mk x (by simp only [mem_cons, not_mem_nil, or_false]))

def ElemOf.selfs {α: Type} (xs: List α) : List (ElemOf xs) :=
  map (fun x =>
    ElemOf.mk x.val xs x.property
  ) xs.attach

theorem list_elem_lt [SizeOf α] {xs: List α} (h: x ∈ xs): sizeOf x ≤ sizeOf xs := by
  rw [show (x ∈ xs) = List.Mem x xs from rfl] at h
  induction h with
  | head xs' =>
    simp +arith
  | tail _ _ ih =>
    apply Nat.le_trans ih
    simp +arith

theorem list_foldl_attach {f: β -> α -> β} {init: β} {xs: List α}:
  List.foldl (fun res ⟨x, _hx⟩ => f res x) init (List.attach xs)
  = List.foldl f init xs := by
  simp only [foldl_subtype, unattach_attach]

theorem list_splitAt_n: xs = (List.splitAt n xs).1 ++ (List.splitAt n xs).2 := by
  simp only [List.splitAt_eq, List.take_append_drop]

theorem list_splitAt_fst_take: (List.splitAt n xs).1 = take n xs := by
  simp only [List.splitAt_eq]

theorem list_splitAt_snd_drop: (List.splitAt n xs).2 = drop n xs := by
  simp only [List.splitAt_eq]

theorem list_take_drop_n (n: Nat) (xs: List α): xs = List.take n xs ++ List.drop n xs := by
  simp only [List.take_append_drop]

theorem list_sizeOf_prepend [SizeOf α] (xs ys: List α):
  sizeOf xs <= sizeOf (ys ++ xs) := by
  induction ys with
  | nil =>
    simp only [List.nil_append, Nat.le_refl]
  | cons y ys ih =>
    simp +arith only [List.cons_append, List.cons.sizeOf_spec]
    omega

theorem list_sizeOf_insert [SizeOf α] (xs ys: List α):
  sizeOf (y::xs ++ ys) = sizeOf (xs ++ y::ys) := by
  induction xs with
  | nil =>
    simp [List.cons.sizeOf_spec]
  | cons x xs ih =>
    simp [List.cons.sizeOf_spec]
    rw [<- ih]
    simp +arith [List.cons.sizeOf_spec]

theorem list_sizeOf_append [SizeOf α] (xs ys: List α):
  sizeOf xs <= sizeOf (xs ++ ys) := by
  induction ys with
  | nil =>
    simp only [append_nil, Nat.le_refl]
  | cons y ys ih =>
    rw [<- list_sizeOf_insert]
    simp +arith only [List.cons_append, List.cons.sizeOf_spec]
    omega

theorem list_sizeOf_cons [SizeOf α] (xs ys: List α):
  sizeOf xs < sizeOf (y::ys ++ xs) := by
  induction ys with
  | nil =>
    simp +arith only [List.cons_append, List.cons.sizeOf_spec]
    simp only [List.nil_append, Nat.le_add_left]
  | cons y ys ih =>
    simp only [List.cons_append] at *
    simp only [List.cons.sizeOf_spec] at *
    omega

theorem list_length_neq_take {n: Nat} {xs: List α}:
  ¬List.take n xs = xs -> (List.take n xs).length < xs.length := by
  intro h
  fun_induction List.take
  case case1 xs =>
    simp
    cases xs with
    | nil =>
      simp at h
    | cons x xs =>
      simp
  case case2 =>
    simp at h
  case case3 n x xs h' =>
    simp at h
    have h' := h' h
    simp only [length_cons]
    omega

theorem list_length_neq_drop {n: Nat} {xs: List α}:
  ¬List.drop n xs = xs -> (List.drop n xs).length < xs.length := by
  intro h
  induction n with
  | zero =>
    simp at h
  | succ n =>
    cases xs with
    | nil =>
      simp at h
    | cons x xs =>
      simp
      omega

theorem list_length_drop_lt_cons {n: Nat} {xs: List α}:
  (List.drop n xs).length < (x :: xs).length := by
  simp only [length_drop, length_cons]
  omega

theorem list_sizeOf_slice [SizeOf α] (xs ys zs: List α):
  sizeOf ys <= sizeOf (xs ++ (ys ++ zs)) := by
  induction xs with
  | nil =>
    simp only [nil_append]
    apply list_sizeOf_append ys zs
  | cons x xs ih =>
    simp [List.cons.sizeOf_spec]
    omega

theorem list_drop_exists (n: Nat) (xs: List α): ∃ ys, xs = ys ++ (List.drop n xs) := by
  cases n with
  | zero =>
    rw [drop_zero]
    exists []
  | succ n' =>
    cases xs with
    | nil =>
      rewrite [drop_nil]
      exists []
    | cons x xs =>
      simp only [List.drop_succ_cons]
      exists (x::List.take n' xs)
      simp only [cons_append]
      congr
      simp only [take_append_drop]

theorem list_self_neq_cons_append:
  xs ≠ y :: (ys ++ xs) := by
  intro h
  rw [←List.cons_append] at h
  rw [List.self_eq_append_left] at h
  nomatch h

theorem list_drop_neq_cons:
  List.drop n xs ≠ x :: xs := by
  have h := list_drop_exists n xs
  cases h with
  | intro ys h =>
  nth_rewrite 2 [h]
  simp
  exact list_self_neq_cons_append (xs := drop n xs) (y := x) (ys := ys)

theorem list_sizeOf_take_drop_le [SizeOf α] (xs: List α):
  sizeOf (List.take t (List.drop d xs)) <= sizeOf xs := by
  induction xs generalizing t d with
  | nil =>
    simp
  | cons x xs ih =>
    simp only [List.cons.sizeOf_spec]
    cases d with
    | zero =>
      simp
      cases t with
      | zero =>
        simp
        omega
      | succ t =>
        simp
        have ih' := @ih t 0
        simp at ih'
        assumption
    | succ d =>
      simp
      have ih' := @ih t d
      omega

theorem list_take_n_nil {n: Nat} {α: Type}:
  @List.take α n [] = [] := by
  simp

theorem list_infix_take_is_infix:
  List.IsInfix xs (List.take n ys) ->
  List.IsInfix xs ys := by
  intro h
  have hys := List.infix_append [] (List.take n ys) (List.drop n ys)
  simp at hys
  apply List.IsInfix.trans h hys

theorem list_infix_drop_is_infix:
  List.IsInfix xs (List.drop n ys) ->
  List.IsInfix xs ys := by
  intro h
  have hys := List.infix_append (List.take n ys) (List.drop n ys) []
  simp at hys
  apply List.IsInfix.trans h hys

theorem list_infix_def {xs ys: List α}:
  List.IsInfix xs ys ->
  ∃ xs1 xs2, xs1 ++ xs ++ xs2 = ys := by
  intro h
  obtain ⟨xs1, h⟩ := h
  obtain ⟨xs2, h⟩ := h
  exists xs1
  exists xs2

abbrev InfixOf {α: Type} (xs: List α) := { ys: List α // List.IsInfix ys xs }

def InfixOf.mk {α: Type} {xs: List α} (ys: List α) (property : List.IsInfix ys xs) : InfixOf xs :=
  (Subtype.mk ys property)

def InfixOf.self (xs: List α): InfixOf xs :=
  Subtype.mk xs (by simp only [List.infix_rfl])

theorem list_infixof_take_is_infix {xs: List α} (ys: InfixOf (List.take n xs)):
  List.IsInfix ys.val xs := by
  obtain ⟨ys, hys⟩ := ys
  simp
  have h1 := list_infix_take_is_infix hys
  assumption

theorem list_infixof_drop_is_infix {xs: List α} (ys: InfixOf (List.drop n xs)):
  List.IsInfix ys.val xs := by
  obtain ⟨ys, hys⟩ := ys
  simp
  have h1 := list_infix_drop_is_infix hys
  assumption

theorem list_infix_is_leq_sizeOf {α: Type} [SizeOf α] {xs ys: List α}:
  List.IsInfix xs ys ->
  sizeOf xs <= sizeOf ys := by
  intro h
  have h' := List.list_infix_def h
  obtain ⟨xs1, xs2, h'⟩ := h'
  rw [<- h']
  have hh2 := List.list_sizeOf_append (xs1 ++ xs) xs2
  have hh1 := List.list_sizeOf_prepend xs xs1
  apply Nat.le_trans hh1 hh2

theorem list_take_eq_self_iff (x : List α) {n : Nat} : x.take n = x ↔ x.length ≤ n :=
  ⟨fun h ↦ by rw [← h]; simp; omega, take_of_length_le⟩

theorem list_elemof_take_is_elem {xs: List α} (y: List.ElemOf (List.take n xs)):
  y.val ∈ xs := by
  obtain ⟨y, hy⟩ := y
  simp only
  rw [list_take_drop_n n xs]
  rw [List.mem_append]
  exact Or.inl hy

theorem list_elemof_drop_is_elem {xs: List α} (y: List.ElemOf (List.drop n xs)):
  y.val ∈ xs := by
  obtain ⟨y, hy⟩ := y
  simp only
  rw [list_take_drop_n n xs]
  rw [List.mem_append]
  exact Or.inr hy

def intersectionsAcc (xs: List α) (acc: List (List α × List α)): List (List α × List α) :=
  match xs with
  | [] => acc
  | (x::xs) =>
    let acc' := intersectionsAcc xs acc
    let fsts := List.map (fun (fst, snd) => (x::fst, snd)) acc'
    let snds := List.map (fun (fst, snd) => (fst, x::snd)) acc'
    fsts ++ snds

def intersections (xs: List α): List (List α × List α) :=
  intersectionsAcc xs [([], [])]

def intersectionsAcc_length (xs: List α) (acc: List (List α × List α)): Nat :=
  acc.length * (2 ^ xs.length)

theorem intersectionsAcc_length_is_correct (xs: List α) (acc: List (List α × List α)):
  (intersectionsAcc xs acc).length = intersectionsAcc_length xs acc := by
  unfold intersectionsAcc_length
  induction xs with
  | nil =>
    simp [intersectionsAcc]
  | cons x xs ih =>
    simp [intersectionsAcc]
    rw [ih]
    simp +arith
    rw [Nat.mul_left_comm]
    rw [Nat.pow_add']

def intersections_length (xs: List α): Nat := 2 ^ xs.length

theorem intersections_length_is_correct (xs: List α):
  (intersections xs).length = intersections_length xs := by
  unfold intersections_length
  unfold intersections
  rw [intersectionsAcc_length_is_correct]
  unfold intersectionsAcc_length
  simp

theorem intersections1_length_is_le (xs: List α):
  ∀ ys ∈ (List.map (·.1) (intersections xs)),
    ys.length <= length xs
  := by
  intro ys hys
  induction xs generalizing ys with
    | nil =>
      simp [intersections, intersectionsAcc] at hys
      rw [hys]
      simp
    | cons x xs ih =>
      simp [intersections, intersectionsAcc, List.map_append] at hys
      simp [List.mem_map] at ih
      rcases hys with hys | hys
      · rcases hys with ⟨fst, ⟨snd, hpair⟩, hys⟩
        have hlen := ih fst snd hpair
        rw [←hys]
        simp only [length_cons, Nat.add_le_add_iff_right]
        assumption
      · rcases hys with ⟨snd, hpair⟩
        have hlen := ih ys snd hpair
        rw [length_cons]
        exact Nat.le_succ_of_le hlen

-- theorem intersectionsAcc_contains_itself_fst (xs: List α) (i: Fin (intersections_length xs)):

theorem intersections_contains_itself_fst (xs: List α):
  ∃ p ∈ intersections xs, p.1 = xs := by
  induction xs with
  | nil =>
    simp only [intersections, intersectionsAcc, mem_cons, not_mem_nil, or_false, exists_eq_left]
  | cons x xs ih =>
    rcases ih with ⟨p, hp_mem, p_fst_eq_xs⟩
    exists (x :: p.1, p.2)
    constructor
    · simp [intersections, intersectionsAcc, List.mem_append, List.mem_map]
      apply Or.inl
      apply hp_mem
    · simp only [cons.injEq, true_and]
      assumption

theorem intersections_contains_itself_fst_idx (xs: List α):
  ∃ i, ((List.intersections xs).get i).1 = xs := by
  have hmem := intersections_contains_itself_fst xs
  rcases hmem with ⟨p, hp_mem, hp_eq⟩
  rcases (mem_iff_get).1 hp_mem with ⟨i, hi⟩
  exists i
  rw [hi]
  exact hp_eq

theorem intersections_sizeOf1 (xs: List α) (i: Fin (List.intersections xs).length):
  ((List.intersections xs).get i).1 = xs \/ sizeOf ((List.intersections xs).get i).1 < sizeOf xs := by
  obtain ⟨i, hi⟩ := i
  induction xs generalizing i with
  | nil =>
    simp [intersections, intersectionsAcc]
  | cons x xs ih =>
    simp [intersections, intersectionsAcc]
    sorry
