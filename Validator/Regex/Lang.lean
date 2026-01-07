def Lang (α: Type): Type := List α → Prop

def Lang.emptyset: Lang α := fun _ => False
def Lang.emptystr: Lang α := fun xs => xs = []
def Lang.symbol (Φ: σ → α → Prop) (s: σ): Lang α :=
  fun xs => ∃ x, xs = [x] /\ Φ s x
def Lang.onlyif (cond : Prop) (P : Lang α): Lang α := fun xs => cond /\ P xs
def Lang.or (P : Lang α) (Q : Lang α): Lang α := fun xs => P xs \/ Q xs
def Lang.concat (P : Lang α) (Q : Lang α): Lang α := fun (xs : List α) =>
  ∃ n: Fin (xs.length + 1), P (List.take n xs) /\ Q (List.drop n xs)
def Lang.star (R: Lang α) (xs: List α): Prop :=
  match xs with
  | [] => True
  | (x::xs') => ∃ (n: Fin xs.length),
      R (x::List.take n xs') /\ Lang.star R (List.drop n xs')
  termination_by xs.length

def Lang.derive (R: Lang α) (x: α): Lang α :=
  fun (xs: List α) => R (x :: xs)

namespace Lang

open List (
  append_assoc
  append_eq_nil_iff
  append_nil
  cons
  cons_append
  cons.injEq
  foldl_nil
  nil
  nil_append
  nil_eq
  singleton_append
)

-- attribute [simp] allows these definitions to be unfolded when using the simp tactic.
attribute [simp] emptyset emptystr onlyif or and

example: Lang α := emptystr
example: Lang α := emptyset
example: Lang α := (star emptyset)

def null {α: Type} (R: Lang α): Prop :=
  R []

def derives {α: Type} (R: Lang α) (xs: List α): Lang α :=
  λ ys => R (xs ++ ys)

def derive' {α: Type} (R: Lang α) (x: α): Lang α :=
  derives R [x]

attribute [simp] null derive derives derive'

theorem derive_is_derive' {α: Type}:
  @derive α = derive' :=
  rfl

theorem derives_empty_list {α: Type} (R: Lang α):
  derives R [] = R :=
  rfl

theorem derives_strings {α: Type} (R: Lang α) (xs ys: List α):
  derives R (xs ++ ys) = derives (derives R xs) ys :=
  match xs with
  | [] => rfl
  | (x :: xs) => derives_strings (derive R x) xs ys

theorem derives_step {α: Type} (R: Lang α) (x: α) (xs: List α):
  derives R (x :: xs) = derives (derive R x) xs := by
  rw [derive_is_derive']
  simp only [derive']
  rw [<- derives_strings]
  congr

theorem null_derives {α: Type} (R: Lang α) (xs: List α):
  (null ∘ derives R) xs = R xs := by
  unfold derives
  unfold null
  simp only [Function.comp_apply]
  simp only [append_nil]

theorem validate {α: Type} (R: Lang α) (xs: List α):
  null (derives R xs) = R xs := by
  unfold derives
  unfold null
  simp only [append_nil]

theorem derives_foldl (R: Lang α) (xs: List α):
  (derives R) xs = (List.foldl derive R) xs := by
  revert R
  induction xs with
  | nil =>
    unfold derives
    simp only [nil_append, foldl_nil, implies_true]
  | cons x xs ih =>
    rw [derive_is_derive']
    simp only [List.foldl_cons, derive']
    intro R
    rw [derives_step]
    rw [ih (derive R x)]
    rw [derive_is_derive']
    simp only [derive']

-- Theorems: null

theorem null_emptyset {α: Type}:
  @null α emptyset = False :=
  rfl

theorem null_iff_emptyset {α: Type}:
  @null α emptyset <-> False := by
  rw [null_emptyset]

theorem not_null_if_emptyset {α: Type}:
  @null α emptyset → False :=
  null_iff_emptyset.mp

theorem null_iff_emptystr {α: Type}:
  @null α emptystr <-> True :=
  Iff.intro
    (fun _ => True.intro)
    (fun _ => rfl)

theorem null_if_emptystr {α: Type}:
  @null α emptystr :=
  rfl

theorem null_emptystr {α: Type}:
  @null α emptystr = True := by
  rw [null_iff_emptystr]

theorem null_iff_symbol {σ: Type} {α: Type} {Φ: σ → α → Prop} {s: σ}:
  null (symbol Φ s) <-> False :=
  Iff.intro nofun nofun

theorem not_null_if_symbol {σ: Type} {α: Type} {Φ: σ → α → Prop} {s: σ}:
  null (symbol Φ s) → False :=
  nofun

theorem null_symbol {σ: Type} {α: Type} {Φ: σ → α → Prop} {s: σ}:
  null (symbol Φ s) = False := by
  rw [null_iff_symbol]

theorem null_or {α: Type} {P Q: Lang α}:
  null (or P Q) = ((null P) \/ (null Q)) :=
  rfl

theorem null_iff_or {α: Type} {P Q: Lang α}:
  null (or P Q) <-> ((null P) \/ (null Q)) := by
  rw [null_or]

theorem null_iff_concat {α: Type} {P Q: Lang α}:
  null (concat P Q) <-> ((null P) /\ (null Q)) := by
  refine Iff.intro ?toFun ?invFun
  case toFun =>
    intro ⟨⟨n, hn⟩, hp, hq⟩
    simp at hn
    subst hn
    simp only [List.take] at hp
    simp only [List.drop] at hq
    exact And.intro hp hq
  case invFun =>
    intro ⟨hp, hq⟩
    unfold concat
    simp only [null, List.length_nil, Nat.reduceAdd, Fin.val_eq_zero, List.take_nil, List.drop_nil,
      exists_const]
    exact And.intro hp hq

theorem null_concat {α: Type} {P Q: Lang α}:
  null (concat P Q) = ((null P) /\ (null Q)) := by
  rw [null_iff_concat]

theorem null_iff_star {α: Type} {R: Lang α}:
  null (star R) <-> True :=
  Iff.intro
    (fun _ => True.intro)
    (fun _ => by
      unfold null
      simp only [star]
    )

theorem null_star {α: Type} {R: Lang α}:
  null (star R) = True := by
  rw [null_iff_star]

-- Theorems: derive

theorem derive_emptyset {α: Type} {a: α}:
  (derive emptyset a) = emptyset :=
  rfl

theorem derive_iff_emptystr {α: Type} {a: α} {w: List α}:
  (derive emptystr a) w <-> emptyset w :=
  Iff.intro nofun nofun

theorem derive_emptystr {α: Type} {a: α}:
  (derive emptystr a) = emptyset := by
  funext
  rw [derive_iff_emptystr]

theorem derive_iff_symbol {α: Type} {Φ: σ → α → Prop} {x: α} {xs: List α}:
  (derive (symbol Φ s) x) xs <-> (onlyif (Φ s x) emptystr) xs := by
  rw [derive_is_derive']
  simp only [derive', derives, singleton_append]
  simp only [onlyif, emptystr]
  refine Iff.intro ?toFun ?invFun
  case toFun =>
    intro D
    match D with
    | Exists.intro x' D =>
    simp only [cons.injEq] at D
    match D with
    | And.intro (And.intro hxx' hxs) hpx =>
    rw [<- hxx'] at hpx
    exact And.intro hpx hxs
  case invFun =>
    intro ⟨ hpx , hxs  ⟩
    unfold symbol
    exists x
    simp only [cons.injEq, true_and]
    exact And.intro hxs hpx

theorem derive_symbol {α: Type} {Φ: σ → α → Prop} {x: α}:
  (derive (symbol Φ s) x) = (onlyif (Φ s x) emptystr) := by
  funext
  rw [derive_iff_symbol]

theorem derive_or {α: Type} {a: α} {P Q: Lang α}:
  (derive (or P Q) a) = (or (derive P a) (derive Q a)) :=
  rfl

theorem derive_onlyif {α: Type} {a: α} {s: Prop} {P: Lang α}:
  (derive (onlyif s P) a) = (onlyif s (derive P a)) :=
  rfl

theorem derive_iff_star {α: Type} {x: α} {R: Lang α} {xs: List α}:
  (derive (star R) x) xs <-> (concat (derive R x) (star R)) xs := by
  rw [derive_is_derive']
  refine Iff.intro ?toFun ?invFun
  case toFun =>
    intro h
    unfold derive' at h
    unfold derives at h
    simp only [cons_append, nil_append] at h
    simp only [star] at h
    unfold concat
    obtain ⟨n, h⟩ := h
    simp only [List.length_cons] at h
    exists n
  case invFun =>
    intro h
    unfold concat at h
    obtain ⟨n, h⟩ := h
    simp only [derive', derives, cons_append, nil_append] at h
    unfold derive'
    unfold derives
    simp only [cons_append, nil_append]
    simp only [star]
    exists n

theorem derive_star {α: Type} {x: α} {R: Lang α}:
  (derive (star R) x) = (concat (derive R x) (star R)) := by
  funext
  rw [derive_iff_star]

theorem derive_iff_concat {α: Type} {x: α} {P Q: Lang α} {xs: List α}:
  (derive (concat P Q) x) xs <->
    (or (concat (derive P x) Q) (onlyif (null P) (derive Q x))) xs := by
  rw [derive_is_derive']
  apply Iff.intro
  case mp =>
    intro h
    obtain ⟨n, hp, hq⟩ := h
    simp only [Lang.or, Lang.concat, derive', derives, null, onlyif]
    simp only [cons_append, nil_append, List.length_cons] at n
    obtain ⟨n, hn⟩ := n
    simp_all only
    cases n with
    | zero =>
      apply Or.inr
      simp_all
    | succ n =>
      apply Or.inl
      simp_all
      exists Fin.mk n (by omega)
  case mpr =>
    simp only [Lang.or, Lang.concat, derive', derives, null, onlyif]
    intro h
    cases h with
    | inl h =>
      obtain ⟨⟨n, hn⟩, hp, hq⟩ := h
      simp_all
      exists Fin.mk (n+1) (by omega)
    | inr h =>
      obtain ⟨hp, hq⟩ := h
      exists Fin.mk 0 (by omega)

theorem derive_concat {α: Type} {x: α} {P Q: Lang α}:
  (derive (concat P Q) x) =
    (or (concat (derive P x) Q) (onlyif (null P) (derive Q x))) := by
  funext
  rw [derive_iff_concat]

theorem simp_or_emptyset_l_is_r (r: Lang α):
  or emptyset r = r := by
  unfold or
  simp only [emptyset, false_or]

theorem simp_or_emptyset_r_is_l (r: Lang α):
  or r emptyset = r := by
  unfold or
  simp only [emptyset, or_false]

theorem simp_or_null_l_emptystr_is_l
  (r: Lang α)
  (nullr: null r):
  or r emptystr = r := by
  unfold or
  simp only [emptystr]
  unfold null at nullr
  funext xs
  simp only [eq_iff_iff, or_iff_left_iff_imp]
  intro hxs
  rw [hxs]
  exact nullr

theorem simp_or_emptystr_null_r_is_r
  (r: Lang α)
  (nullr: null r):
  or emptystr r = r := by
  unfold or
  simp only [emptystr]
  unfold null at nullr
  funext xs
  simp only [eq_iff_iff, or_iff_right_iff_imp]
  intro hxs
  rw [hxs]
  exact nullr

theorem simp_or_idemp (r: Lang α):
  or r r = r := by
  unfold or
  funext xs
  apply or_self

theorem simp_or_comm (r s: Lang α):
  or r s = or s r := by
  unfold or
  funext xs
  simp only [eq_iff_iff]
  apply Iff.intro
  case mp =>
    intro h
    match h with
    | Or.inl h =>
      exact Or.inr h
    | Or.inr h =>
      exact Or.inl h
  case mpr =>
    intro h
    match h with
    | Or.inl h =>
      exact Or.inr h
    | Or.inr h =>
      exact Or.inl h

theorem simp_or_assoc (r s t: Lang α):
  or (or r s) t = or r (or s t) := by
  unfold or
  funext xs
  simp only [eq_iff_iff]
  apply Iff.intro
  · case mp =>
    intro h
    cases h with
    | inl h =>
      cases h with
      | inl h =>
        left
        exact h
      | inr h =>
        right
        left
        exact h
    | inr h =>
      right
      right
      exact h
  · case mpr =>
    intro h
    cases h with
    | inl h =>
      left
      left
      exact h
    | inr h =>
      cases h with
      | inl h =>
        left
        right
        exact h
      | inr h =>
        right
        exact h

-- class Associative found in Init/Core.lean in namespace Std
-- It is used by the ac_rfl tactic.
instance IsAssociative_or {α: Type}: Std.Associative (@or α) :=
  { assoc := @simp_or_assoc α }

-- class Commutative found in Init/Core.lean in namespace Std
-- It is used by the ac_rfl tactic.
instance IsCommutative_or {α: Type}: Std.Commutative (@or α) :=
  { comm := @simp_or_comm α }

-- class IdempotentOp found in Init/Core.lean in namespace Std
-- It is used by the ac_rfl tactic.
instance IsIdempotentOp_or {α: Type}: Std.IdempotentOp (@or α) :=
  { idempotent := simp_or_idemp }

instance IsLawfulCommIdentity_or {α: Type} : Std.LawfulCommIdentity (@or α) (@emptyset α) where
  right_id r := simp_or_emptyset_r_is_l r

-- Test that ac_rfl uses the instance of Std.LawfulCommIdentity
example (r: Lang α):
  or r emptyset = r := by
  ac_rfl

-- Test that ac_rfl uses the instance of Std.Commutative
example (r s: Lang α):
  or r s = or s r := by
  ac_rfl

-- Test that ac_rfl uses the instance of Std.Associative
example (r s t: Lang α):
  or (or r s) t = or r (or s t) := by
  ac_rfl

-- Test that ac_rfl uses the instance of Std.IdempotentOp
example (r: Lang α):
  or (or r r) r = r := by
  ac_rfl

-- Test that ac_rfl uses both the instances of Std.Associative and Std.Commutative
example (a b c d : Lang α):
  (or a (or b (or c d))) = (or d (or (or b c) a)) := by ac_rfl

-- Test that ac_rfl uses both the instances of Std.Associative and Std.Commutative and Std.IdempotentOp
example (a b c d : Lang α):
  (or a (or b (or c d))) = (or a (or d (or (or b c) a))) := by ac_rfl

-- Test ac_nf tactic
example (r s: Lang α) (H: s = r):
  or emptyset (or r s) = (or r r) := by
  ac_nf
  rw [H]
  ac_rfl

theorem not_not_intro' {p : Prop} (h : p) : ¬ ¬ p :=
  fun hn : (p → False) => hn h

def onlyif_true {cond: Prop} {l: List α → Prop} (condIsTrue: cond):
  Lang.onlyif cond l = l := by
  unfold Lang.onlyif
  funext xs
  simp only [eq_iff_iff, and_iff_right_iff_imp]
  intro p
  assumption

def onlyif_false {cond: Prop} {l: List α → Prop} (condIsFalse: ¬cond):
  Lang.onlyif cond l = Lang.emptyset := by
  funext xs
  rw [eq_iff_iff]
  apply Iff.intro
  case mp =>
    intro h
    cases h
    case intro condIsTrue lxs =>
    contradiction
  case mpr =>
    intro h
    nomatch h

theorem simp_onlyif_and {α: Type} (cond1 cond2 : Prop) (P : Lang α):
  onlyif (cond1 /\ cond2) P = onlyif cond1 (onlyif cond2 P) := by
  unfold onlyif
  funext xs
  -- aesop?
  simp_all only [eq_iff_iff]
  apply Iff.intro
  · intro a
    simp_all only [and_self]
  · intro a
    simp_all only [and_self]
