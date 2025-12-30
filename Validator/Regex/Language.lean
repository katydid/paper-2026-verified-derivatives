import Mathlib.Tactic.Linarith -- split_ands

namespace Language

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

-- Definitions

def Langs (α: Type): Type := List α -> Prop

def emptyset : Langs α :=
  fun _ => False

def universal {α: Type} : Langs α :=
  fun _ => True

def emptystr {α: Type} : Langs α :=
  fun xs => xs = []

def char {α: Type} (x : α): Langs α :=
  fun xs => xs = [x]

def pred {α: Type} (p : α -> Prop): Langs α :=
  fun xs => ∃ x, xs = [x] /\ p x

def symbol {α: Type} (Φ: σ -> α -> Prop) (s: σ): Langs α :=
  fun xs => ∃ x, xs = [x] /\ Φ s x

def any {α: Type}: Langs α :=
  fun xs => ∃ x, xs = [x]

-- onlyif is used as an and to make derive char not require an if statement
-- (derive (char c) a) w <-> (onlyif (a = c) emptystr)
def onlyif {α: Type} (cond : Prop) (P : Langs α) : Langs α :=
  fun xs => cond /\ P xs

def or {α: Type} (P : Langs α) (Q : Langs α) : Langs α :=
  fun xs => P xs \/ Q xs

def and {α: Type} (P : Langs α) (Q : Langs α) : Langs α :=
  fun xs => P xs /\ Q xs

-- alternative definition of concat
def concat_n {α: Type} (P : Langs α) (Q : Langs α) : Langs α :=
  fun (xs : List α) =>
    ∃ n: Fin (xs.length + 1), P (List.take n xs) /\ Q (List.drop n xs)

-- alternative definition of star
def star_n {α: Type} (R: Langs α) (xs: List α): Prop :=
  match xs with
  | [] => True
  | (x'::xs') =>
    ∃ (n: Fin xs.length),
      R (List.take (n + 1) (x'::xs')) /\
      (star_n R (List.drop (n + 1) (x'::xs')))
  termination_by xs.length
  decreasing_by
    obtain ⟨n, hn⟩ := n
    simp
    omega

def not {α: Type} (R: Langs α): Langs α :=
  fun xs => (Not (R xs))

-- attribute [simp] allows these definitions to be unfolded when using the simp tactic.
attribute [simp] universal emptyset emptystr char onlyif or and

example: Langs α := universal
example: Langs α := emptystr
example: Langs α := (or emptystr universal)
example: Langs α := (and emptystr universal)
example: Langs α := emptyset
example: Langs α := (star_n emptyset)
example: Langs Char := char 'a'
example: Langs Char := char 'b'
example: Langs Char := (or (char 'a') emptyset)
example: Langs Char := (and (char 'a') (char 'b'))
example: Langs Nat := (and (char 1) (char 2))
example: Langs Nat := (onlyif True (char 2))
example: Langs Nat := (concat_n (char 1) (char 2))
example: Langs Nat := (pred (fun x => x = 1))

def null {α: Type} (R: Langs α): Prop :=
  R []

def derives {α: Type} (R: Langs α) (xs: List α): Langs α :=
  λ ys => R (xs ++ ys)

def derive {α: Type} (R: Langs α) (x: α): Langs α :=
  derives R [x]

def derive' {α: Type} (R: Langs α) (x: α): Langs α :=
  fun (xs: List α) => R (x :: xs)

attribute [simp] null derive derives derive'

theorem derive_is_derive' {α: Type} (R: Langs α) (x: α):
  derive R x = derive' R x :=
  rfl

theorem derives_empty_list {α: Type} (R: Langs α):
  derives R [] = R :=
  rfl

theorem derives_strings {α: Type} (R: Langs α) (xs ys: List α):
  derives R (xs ++ ys) = derives (derives R xs) ys :=
  match xs with
  | [] => rfl
  | (x :: xs) => derives_strings (derive R x) xs ys

theorem derives_step {α: Type} (R: Langs α) (x: α) (xs: List α):
  derives R (x :: xs) = derives (derive R x) xs := by
  simp only [derive]
  rw [<- derives_strings]
  congr

theorem null_derives {α: Type} (R: Langs α) (xs: List α):
  (null ∘ derives R) xs = R xs := by
  unfold derives
  unfold null
  simp only [Function.comp_apply]
  simp only [append_nil]

theorem validate {α: Type} (R: Langs α) (xs: List α):
  null (derives R xs) = R xs := by
  unfold derives
  unfold null
  simp only [append_nil]

theorem derives_foldl (R: Langs α) (xs: List α):
  (derives R) xs = (List.foldl derive R) xs := by
  revert R
  induction xs with
  | nil =>
    unfold derives
    simp only [nil_append, foldl_nil, implies_true]
  | cons x xs ih =>
    simp only [List.foldl_cons, derive]
    intro R
    rw [derives_step]
    rw [ih (derive R x)]
    simp only [derive]

-- Theorems: null

theorem null_emptyset {α: Type}:
  @null α emptyset = False :=
  rfl

theorem null_iff_emptyset {α: Type}:
  @null α emptyset <-> False := by
  rw [null_emptyset]

theorem not_null_if_emptyset {α: Type}:
  @null α emptyset -> False :=
  null_iff_emptyset.mp

theorem null_universal {α: Type}:
  @null α universal = True :=
  rfl

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

theorem null_iff_any {α: Type}:
  @null α any <-> False :=
  Iff.intro nofun nofun

theorem not_null_if_any {α: Type}:
  @null α any -> False :=
  nofun

theorem null_any {α: Type}:
  @null α any = False := by
  rw [null_iff_any]

theorem null_iff_char {α: Type} {c: α}:
  null (char c) <-> False :=
  Iff.intro nofun nofun

theorem not_null_if_char {α: Type} {c: α}:
  null (char c) -> False :=
  nofun

theorem null_char {α: Type} {c: α}:
  null (char c) = False := by
  rw [null_iff_char]

theorem null_iff_pred {α: Type} {p: α -> Prop}:
  null (pred p) <-> False :=
  Iff.intro nofun nofun

theorem not_null_if_pred {α: Type} {p: α -> Prop}:
  null (pred p) -> False :=
  nofun

theorem null_pred {α: Type} {p: α -> Prop}:
  null (pred p) = False := by
  rw [null_iff_pred]

theorem null_iff_symbol {σ: Type} {α: Type} {Φ: σ -> α -> Prop} {s: σ}:
  null (symbol Φ s) <-> False :=
  Iff.intro nofun nofun

theorem not_null_if_symbol {σ: Type} {α: Type} {Φ: σ -> α -> Prop} {s: σ}:
  null (symbol Φ s) -> False :=
  nofun

theorem null_symbol {σ: Type} {α: Type} {Φ: σ -> α -> Prop} {s: σ}:
  null (symbol Φ s) = False := by
  rw [null_iff_symbol]

theorem null_or {α: Type} {P Q: Langs α}:
  null (or P Q) = ((null P) \/ (null Q)) :=
  rfl

theorem null_iff_or {α: Type} {P Q: Langs α}:
  null (or P Q) <-> ((null P) \/ (null Q)) := by
  rw [null_or]

theorem null_and {α: Type} {P Q: Langs α}:
  null (and P Q) = ((null P) /\ (null Q)) :=
  rfl

theorem null_iff_concat_n {α: Type} {P Q: Langs α}:
  null (concat_n P Q) <-> ((null P) /\ (null Q)) := by
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
    unfold concat_n
    simp only [null, List.length_nil, Nat.reduceAdd, Fin.val_eq_zero, List.take_nil, List.drop_nil,
      exists_const]
    exact And.intro hp hq

theorem null_concat_n {α: Type} {P Q: Langs α}:
  null (concat_n P Q) = ((null P) /\ (null Q)) := by
  rw [null_iff_concat_n]

theorem null_iff_star_n {α: Type} {R: Langs α}:
  null (star_n R) <-> True :=
  Iff.intro
    (fun _ => True.intro)
    (fun _ => by
      unfold null
      simp only [star_n]
    )

theorem null_star_n {α: Type} {R: Langs α}:
  null (star_n R) = True := by
  rw [null_iff_star_n]

theorem null_not {α: Type} {R: Langs α}:
  null (not R) = null (Not ∘ R) :=
  rfl

theorem null_iff_not {α: Type} {R: Langs α}:
  null (not R) <-> null (Not ∘ R) := by
  rw [null_not]

-- Theorems: derive

theorem derive_emptyset {α: Type} {a: α}:
  (derive emptyset a) = emptyset :=
  rfl

theorem derive_universal {α: Type} {a: α}:
  (derive universal a) = universal :=
  rfl

theorem derive_iff_emptystr {α: Type} {a: α} {w: List α}:
  (derive emptystr a) w <-> emptyset w :=
  Iff.intro nofun nofun

theorem derive_emptystr {α: Type} {a: α}:
  (derive emptystr a) = emptyset := by
  funext
  rw [derive_iff_emptystr]

theorem derive_iff_char {α: Type} [DecidableEq α] {a: α} {c: α} {w: List α}:
  (derive (char c) a) w <-> (onlyif (a = c) emptystr) w := by
  refine Iff.intro ?toFun ?invFun
  case toFun =>
    intro D
    cases D with | refl =>
    exact ⟨ rfl, rfl ⟩
  case invFun =>
    intro ⟨ H1 , H2  ⟩
    cases H1 with | refl =>
    cases H2 with | refl =>
    exact rfl

theorem derive_char {α: Type} [DecidableEq α] {a: α} {c: α}:
  (derive (char c) a) = (onlyif (a = c) emptystr) := by
  funext
  rw [derive_iff_char]

theorem derive_iff_pred {α: Type} {p: α -> Prop} {x: α} {xs: List α}:
  (derive (pred p) x) xs <-> (onlyif (p x) emptystr) xs := by
  simp only [derive, derives, singleton_append]
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
    unfold pred
    exists x
    simp only [cons.injEq, true_and]
    exact And.intro hxs hpx

theorem derive_pred {α: Type} {p: α -> Prop} {x: α}:
  (derive (pred p) x) = (onlyif (p x) emptystr) := by
  funext
  rw [derive_iff_pred]

theorem derive_iff_symbol {α: Type} {Φ: σ -> α -> Prop} {x: α} {xs: List α}:
  (derive (symbol Φ s) x) xs <-> (onlyif (Φ s x) emptystr) xs := by
  simp only [derive, derives, singleton_append]
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

theorem derive_symbol {α: Type} {Φ: σ -> α -> Prop} {x: α}:
  (derive (symbol Φ s) x) = (onlyif (Φ s x) emptystr) := by
  funext
  rw [derive_iff_symbol]

theorem derive_or {α: Type} {a: α} {P Q: Langs α}:
  (derive (or P Q) a) = (or (derive P a) (derive Q a)) :=
  rfl

theorem derive_and {α: Type} {a: α} {P Q: Langs α}:
  (derive (and P Q) a) = (and (derive P a) (derive Q a)) :=
  rfl

theorem derive_onlyif {α: Type} {a: α} {s: Prop} {P: Langs α}:
  (derive (onlyif s P) a) = (onlyif s (derive P a)) :=
  rfl

theorem derive_iff_star_n {α: Type} {x: α} {R: Langs α} {xs: List α}:
  (derive (star_n R) x) xs <-> (concat_n (derive R x) (star_n R)) xs := by
  refine Iff.intro ?toFun ?invFun
  case toFun =>
    intro h
    unfold derive at h
    unfold derives at h
    simp only [cons_append, nil_append] at h
    simp only [star_n] at h
    unfold concat_n
    obtain ⟨n, h⟩ := h
    simp only [List.length_cons, List.take_succ_cons, List.drop_succ_cons] at h
    exists n
  case invFun =>
    intro h
    unfold concat_n at h
    obtain ⟨n, h⟩ := h
    simp only [derive, derives, cons_append, nil_append] at h
    unfold derive
    unfold derives
    simp only [cons_append, nil_append]
    simp only [star_n]
    exists n

theorem derive_star_n {α: Type} {x: α} {R: Langs α}:
  (derive (star_n R) x) = (concat_n (derive R x) (star_n R)) := by
  funext
  rw [derive_iff_star_n]

theorem derive_not {α: Type} {x: α} {R: Langs α}:
  (derive (not R) x) = Not ∘ (derive R x) :=
  rfl

theorem derive_iff_not {α: Type} {x: α} {R: Langs α} {xs: List α}:
  (derive (not R) x) xs <-> Not ((derive R x) xs) := by
  rw [derive_not]
  rfl

theorem derive_iff_concat_n {α: Type} {x: α} {P Q: Langs α} {xs: List α}:
  (derive (concat_n P Q) x) xs <->
    (or (concat_n (derive P x) Q) (onlyif (null P) (derive Q x))) xs := by
  apply Iff.intro
  case mp =>
    intro h
    obtain ⟨n, hp, hq⟩ := h
    simp only [Language.or, Language.concat_n, derive, derives, null, onlyif]
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
    simp only [Language.or, Language.concat_n, derive, derives, null, onlyif]
    intro h
    cases h with
    | inl h =>
      obtain ⟨⟨n, hn⟩, hp, hq⟩ := h
      simp_all
      exists Fin.mk (n+1) (by omega)
    | inr h =>
      obtain ⟨hp, hq⟩ := h
      exists Fin.mk 0 (by omega)

theorem derive_concat_n {α: Type} {x: α} {P Q: Langs α}:
  (derive (concat_n P Q) x) =
    (or (concat_n (derive P x) Q) (onlyif (null P) (derive Q x))) := by
  funext
  rw [derive_iff_concat_n]

theorem simp_or_emptyset_l_is_r (r: Langs α):
  or emptyset r = r := by
  unfold or
  simp only [emptyset, false_or]

theorem simp_or_emptyset_r_is_l (r: Langs α):
  or r emptyset = r := by
  unfold or
  simp only [emptyset, or_false]

theorem simp_or_universal_l_is_universal (r: Langs α):
  or universal r = universal := by
  unfold or
  simp only [universal, true_or]
  rfl

theorem simp_or_universal_r_is_universal (r: Langs α):
  or r universal = universal := by
  unfold or
  simp only [universal, or_true]
  rfl

theorem simp_or_null_l_emptystr_is_l
  (r: Langs α)
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
  (r: Langs α)
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

theorem simp_or_idemp (r: Langs α):
  or r r = r := by
  unfold or
  funext xs
  apply or_self

theorem simp_or_comm (r s: Langs α):
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

theorem simp_or_assoc (r s t: Langs α):
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
example (r: Langs α):
  or r emptyset = r := by
  ac_rfl

-- Test that ac_rfl uses the instance of Std.Commutative
example (r s: Langs α):
  or r s = or s r := by
  ac_rfl

-- Test that ac_rfl uses the instance of Std.Associative
example (r s t: Langs α):
  or (or r s) t = or r (or s t) := by
  ac_rfl

-- Test that ac_rfl uses the instance of Std.IdempotentOp
example (r: Langs α):
  or (or r r) r = r := by
  ac_rfl

-- Test that ac_rfl uses both the instances of Std.Associative and Std.Commutative
example (a b c d : Langs α):
  (or a (or b (or c d))) = (or d (or (or b c) a)) := by ac_rfl

-- Test that ac_rfl uses both the instances of Std.Associative and Std.Commutative and Std.IdempotentOp
example (a b c d : Langs α):
  (or a (or b (or c d))) = (or a (or d (or (or b c) a))) := by ac_rfl

-- Test ac_nf tactic
example (r s: Langs α) (H: s = r):
  or emptyset (or r s) = (or r r) := by
  ac_nf
  rw [H]
  ac_rfl

theorem simp_and_emptyset_l_is_emptyset (r: Langs α):
  and emptyset r = emptyset := by
  unfold and
  simp only [emptyset, false_and]
  rfl

theorem simp_and_emptyset_r_is_emptyset (r: Langs α):
  and r emptyset = emptyset := by
  unfold and
  simp only [emptyset, and_false]
  rfl

theorem simp_and_universal_l_is_r (r: Langs α):
  and universal r = r := by
  unfold and
  simp only [universal, true_and]

theorem simp_and_universal_r_is_l (r: Langs α):
  and r universal = r := by
  unfold and
  simp only [universal, and_true]

theorem simp_and_null_l_emptystr_is_emptystr
  (r: Langs α)
  (nullr: null r):
  and r emptystr = emptystr := by
  funext xs
  simp only [and, emptystr, eq_iff_iff, and_iff_right_iff_imp]
  intro hxs
  rw [hxs]
  exact nullr

theorem simp_and_emptystr_null_r_is_emptystr
  (r: Langs α)
  (nullr: null r):
  and emptystr r = emptystr := by
  funext xs
  simp only [null] at nullr
  simp only [and, emptystr, eq_iff_iff, and_iff_left_iff_imp]
  intro hxs
  rw [hxs]
  exact nullr

theorem simp_and_not_null_l_emptystr_is_emptyset
  (r: Langs α)
  (notnullr: Not (null r)):
  and r emptystr = emptyset := by
  funext xs
  simp only [and, emptystr, emptyset, eq_iff_iff, iff_false, not_and]
  intro hr hxs
  rw [hxs] at hr
  contradiction

theorem simp_and_emptystr_not_null_r_is_emptyset
  (r: Langs α)
  (notnullr: Not (null r)):
  and emptystr r = emptyset := by
  funext xs
  simp only [and, emptystr, emptyset, eq_iff_iff, iff_false, not_and]
  intro hxs
  rw [hxs]
  exact notnullr

theorem simp_and_idemp (r: Langs α):
  and r r = r := by
  unfold and
  funext xs
  simp only [eq_iff_iff]
  apply Iff.intro
  case mp =>
    intro h
    cases h
    assumption
  case mpr =>
    intro h
    exact And.intro h h

theorem simp_and_comm (r s: Langs α):
  and r s = and s r := by
  unfold and
  funext xs
  simp only [eq_iff_iff]
  apply Iff.intro
  case mp =>
    intro h
    cases h with
    | intro hr hs =>
      exact And.intro hs hr
  case mpr =>
    intro h
    cases h with
    | intro hs hr =>
      exact And.intro hr hs

theorem simp_and_assoc (r s t: Langs α):
  and (and r s) t = and r (and s t) := by
  unfold and
  funext xs
  simp only [eq_iff_iff]
  apply Iff.intro
  case mp =>
    intro h
    match h with
    | And.intro (And.intro h1 h2) h3 =>
    exact And.intro h1 (And.intro h2 h3)
  case mpr =>
    intro h
    match h with
    | And.intro h1 (And.intro h2 h3) =>
    exact And.intro (And.intro h1 h2) h3

-- class Associative found in Init/Core.lean in namespace Std
-- It is used by the ac_rfl tactic.
instance IsAssociative_and {α: Type}: Std.Associative (@and α) :=
  { assoc := @simp_and_assoc α }

-- class Commutative found in Init/Core.lean in namespace Std
-- It is used by the ac_rfl tactic.
instance IsCommutative_and {α: Type}: Std.Commutative (@and α) :=
  { comm := @simp_and_comm α }

-- class IdempotentOp found in Init/Core.lean in namespace Std
-- It is used by the ac_rfl tactic.
instance IsIdempotentOp_and {α: Type}: Std.IdempotentOp (@and α) :=
  { idempotent := simp_and_idemp }

instance IsLawfulCommIdentity_and {α: Type} : Std.LawfulCommIdentity (@and α) (@universal α) where
  right_id r := simp_and_universal_r_is_l r

-- Test that ac_rfl uses the instance of Std.LawfulCommIdentity
example (r: Langs α):
  and r universal = r := by
  ac_rfl

-- Test that ac_rfl uses the instance of Std.Commutative
example (r s: Langs α):
  and r s = and s r := by
  ac_rfl

-- Test that ac_rfl uses the instance of Std.Associative
example (r s t: Langs α):
  and (and r s) t = and r (and s t) := by
  ac_rfl

-- Test that ac_rfl uses the instance of Std.IdempotentOp
example (r: Langs α):
  and r (and r r) = r := by
  ac_rfl

-- Test that ac_rfl uses both the instances of Std.Associative and Std.Commutative
example (a b c d : Langs α):
  (and a (and b (and c d))) = (and d (and (and b c) a)) := by ac_rfl

-- Test that ac_rfl uses both the instances of Std.Associative and Std.Commutative and Std.IdempotentOp
example (a b c d : Langs α):
  (and a (and b (and c d))) = (and d (and d (and (and b c) a))) := by ac_rfl

theorem not_not_intro' {p : Prop} (h : p) : ¬ ¬ p :=
  fun hn : (p -> False) => hn h

theorem simp_not_not_is_double_negation
  (r: Langs α) [DecidablePred r]:
  not (not r) = r := by
  unfold not
  funext xs
  simp only [eq_iff_iff]
  exact Decidable.not_not

theorem simp_not_and_demorgen
  (r s: Langs α) (xs: List α) [Decidable (r xs)] [Decidable (s xs)]:
  not (and r s) xs = or (not r) (not s) xs := by
  unfold and
  unfold or
  unfold not
  simp only [eq_iff_iff]
  exact Decidable.not_and_iff_not_or_not

theorem simp_not_or_demorgen (r s: Langs α):
  not (or r s) = and (not r) (not s) := by
  unfold not
  unfold or
  unfold and
  simp only [not_or]

theorem simp_and_not_emptystr_l_not_null_r_is_r
  (r: Langs α)
  (notnullr: Not (null r)):
  and (not emptystr) r = r := by
  funext xs
  simp only [and, not, emptystr, eq_iff_iff, and_iff_right_iff_imp]
  intro hr hxs
  rw [hxs] at hr
  contradiction

theorem simp_and_not_null_l_not_emptystr_r_is_l
  (r: Langs α)
  (notnullr: Not (null r)):
  and r (not emptystr) = r := by
  funext xs
  simp only [null] at notnullr
  simp only [and, not, emptystr, eq_iff_iff, and_iff_left_iff_imp]
  intro hr hxs
  rw [hxs] at hr
  contradiction

def onlyif_true {cond: Prop} {l: List α -> Prop} (condIsTrue: cond):
  Language.onlyif cond l = l := by
  unfold Language.onlyif
  funext xs
  simp only [eq_iff_iff, and_iff_right_iff_imp]
  intro p
  assumption

def onlyif_false {cond: Prop} {l: List α -> Prop} (condIsFalse: ¬cond):
  Language.onlyif cond l = Language.emptyset := by
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

theorem simp_or_and_left_distrib (a b c : Langs α) : and a (or b c) = or (and a b) (and a c) := by
  unfold and
  unfold or
  funext xs
  simp only [eq_iff_iff]
  apply Iff.intro
  · case mp =>
    intro H
    cases H with
    | intro Ha Hbc =>
    cases Hbc with
    | inl Hb =>
      apply Or.inl
      apply And.intro Ha Hb
    | inr Hc =>
      apply Or.inr
      apply And.intro Ha Hc
  · case mpr =>
    intro H
    cases H with
    | inl Hab =>
      cases Hab with
      | intro Ha Hb =>
        apply And.intro
        exact Ha
        apply Or.inl
        exact Hb
    | inr Hac =>
      cases Hac with
      | intro Ha Hc =>
        apply And.intro
        exact Ha
        apply Or.inr
        exact Hc

theorem simp_or_and_right_distrib (a b c : Langs α) : and (or a b) c = or (and a c) (and b c) := by
  unfold and
  unfold or
  funext xs
  simp only [eq_iff_iff]
  apply Iff.intro
  · case mp =>
    intro H
    cases H with
    | intro Hab Hc =>
    cases Hab with
    | inl Ha =>
      apply Or.inl
      apply And.intro Ha Hc
    | inr Hb =>
      apply Or.inr
      apply And.intro Hb Hc
  · case mpr =>
    intro H
    cases H with
    | inl Hac =>
      cases Hac with
      | intro Ha Hc =>
        apply And.intro
        apply Or.inl
        exact Ha
        exact Hc
    | inr Hbc =>
      cases Hbc with
      | intro Hb Hc =>
        apply And.intro
        apply Or.inr
        exact Hb
        exact Hc

theorem simp_and_or_left_distrib (a b c : Langs α) : or a (and b c) = and (or a b) (or a c) := by
  unfold and
  unfold or
  funext xs
  simp only [eq_iff_iff]
  apply Iff.intro
  · case mp =>
    intro H
    cases H with
    | inl H =>
      apply And.intro
      · apply Or.inl H
      · apply Or.inl H
    | inr H =>
      cases H with
      | intro Hb Hc =>
      apply And.intro
      · apply Or.inr Hb
      · apply Or.inr Hc
  · case mpr =>
    intro H
    cases H with
    | intro Hab Hac =>
    cases Hab with
    | inl Ha =>
      apply Or.inl Ha
    | inr Hb =>
      cases Hac with
      | inl Ha =>
        apply Or.inl Ha
      | inr Hc =>
        apply Or.inr
        apply And.intro Hb Hc

theorem simp_and_or_right_distrib (a b c : Langs α) : or (and a b) c = and (or a c) (or b c) := by
  unfold and
  unfold or
  funext xs
  simp only [eq_iff_iff]
  apply Iff.intro
  · case mp =>
    intro H
    cases H with
    | inl h => simp_all only [true_or, and_self]
    | inr h_1 => simp_all only [or_true, and_self]
  · case mpr =>
    intro H
    cases H with
    | intro Hleft Hright =>
    cases Hleft with
    | inl h =>
      cases Hright with
      | inl h_1 => simp_all only [and_self, true_or]
      | inr h_2 => simp_all only [true_and, or_true]
    | inr h_1 =>
      cases Hright with
      | inl h => simp_all only [and_true, or_true]
      | inr h_2 => simp_all only [or_true]

theorem simp_onlyif_and {α: Type} (cond1 cond2 : Prop) (P : Langs α):
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
