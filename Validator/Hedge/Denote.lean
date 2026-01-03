import Validator.Std.List

import Validator.Regex.Language
import Validator.Hedge.Grammar
import Validator.Hedge.Language

namespace Hedge.Grammar

theorem decreasing_or_l {α: Type} {σ: Type} [SizeOf σ] (r1 r2: Regex σ) (xs: Hedge α):
  Prod.Lex
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (xs, r1)
    (xs, Regex.or r1 r2) := by
  apply Prod.Lex.right
  simp +arith only [Regex.or.sizeOf_spec]

theorem decreasing_or_r {α: Type} {σ: Type} [SizeOf σ] (r1 r2: Regex σ) (xs: Hedge α):
  Prod.Lex
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (xs, r2)
    (xs, Regex.or r1 r2) := by
  apply Prod.Lex.right
  simp +arith only [Regex.or.sizeOf_spec]

theorem decreasing_concat_l {α: Type} {σ: Type} [SizeOf σ] (r1 r2: Regex σ) (xs: Hedge α):
  Prod.Lex
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (xs, r1)
    (xs, Regex.concat r1 r2) := by
  apply Prod.Lex.right
  simp +arith only [Regex.concat.sizeOf_spec]

theorem decreasing_concat_r {α: Type} {σ: Type} [SizeOf σ] (r1 r2: Regex σ) (xs: Hedge α):
  Prod.Lex
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (xs, r2)
    (xs, Regex.concat r1 r2) := by
  apply Prod.Lex.right
  simp +arith only [Regex.concat.sizeOf_spec]

theorem decreasing_star {α: Type} {σ: Type} [SizeOf σ] (r: Regex σ) (xs: Hedge α):
  Prod.Lex
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (xs, r)
    (xs, Regex.star r) := by
  apply Prod.Lex.right
  simp +arith only [Regex.star.sizeOf_spec]

theorem decreasing_symbol {α: Type} {σ: Type} [SizeOf σ] (r1 r2: Regex σ) (x: Hedge.Node α):
  Prod.Lex
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (x.getChildren, r1)
    ([x], r2) := by
  apply Prod.Lex.left
  cases x with
  | mk label children =>
  simp only [Hedge.Node.getChildren]
  simp only [List.cons.sizeOf_spec, Node.mk.sizeOf_spec, sizeOf_default, add_zero,
    List.nil.sizeOf_spec]
  omega

theorem denote_sizeOf_concat_left {α: Type} {σ: Type} [SizeOf σ] {r1 r2: Regex σ} {xs: Hedge α}:
  Prod.Lex (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂) (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂) (List.take n xs, r1) (xs, Regex.concat r1 r2) := by
  have h := Hedge.sizeOf_take n xs
  cases h with
  | inl h =>
    rw [h]
    apply decreasing_concat_l
  | inr h =>
    apply Prod.Lex.left
    assumption

theorem denote_sizeOf_concat_right {α: Type} {σ: Type} [SizeOf σ] {p q: Regex σ} {xs: Hedge α}:
  Prod.Lex (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂) (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂) ((List.drop n xs), q) (xs, Regex.concat p q) := by
  have h := Hedge.sizeOf_drop n xs
  cases h with
  | inl h =>
    rw [h]
    apply decreasing_concat_r
  | inr h =>
    apply Prod.Lex.left
    assumption

theorem denote_sizeOf_star_left {α: Type} {σ: Type} [SizeOf σ] {p: Regex σ} {x: Hedge.Node α} {xs: Hedge α}:
  Prod.Lex (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂) (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂) (x::(List.take n xs), p) (x::xs, Regex.star p) := by
  have h := Hedge.sizeOf_take n xs
  cases h with
  | inl h =>
    rw [h]
    apply decreasing_star
  | inr h =>
    apply Prod.Lex.left
    simp only [List.cons.sizeOf_spec, add_lt_add_iff_left]
    assumption

theorem denote_sizeOf_star_right {α: Type} {σ: Type} [SizeOf σ] {p: Regex σ} {x: Hedge.Node α} {xs: Hedge α}:
  Prod.Lex (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂) (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂) ((List.drop (n + 1) (x::xs)), Regex.star p) ((x::xs), Regex.star p) := by
  simp only [List.drop_succ_cons]
  apply Prod.Lex.left
  have h := Hedge.sizeOf_drop n xs
  cases h with
  | inl h =>
    rw [h]
    simp only [List.cons.sizeOf_spec, lt_add_iff_pos_left, add_pos_iff, zero_lt_one, true_or]
  | inr h =>
    simp only [List.cons.sizeOf_spec, gt_iff_lt]
    omega

-- Language.or, Language.concat and Language.star are unfolded to help with the termination proof.
-- Φ needs to be the last parameter, so that simp only works on this function when the parameter r is provided.
def Rule.denote' (G: Grammar n φ)
  (r: Regex (φ × Ref n)) (Φ: φ -> α -> Prop) (xs: Hedge α): Prop := match r with
  | Regex.emptyset => False | Regex.emptystr => xs = []
  | Regex.symbol (pred, ref) => match xs with
    | [x] => (Φ pred x.getLabel) /\ denote' G (G.lookup ref) Φ x.getChildren
    | _ => False
  | Regex.or r1 r2 => (denote' G r1 Φ xs) \/ (denote' G r2 Φ xs)
  | Regex.concat r1 r2 => ∃ (i: Fin (xs.length + 1)),
      (denote' G r1 Φ (List.take i xs)) /\ (denote' G r2 Φ (List.drop i xs))
  | Regex.star r1 => match xs with
    | [] => True
    | (x'::xs') => ∃ (i: Fin xs.length),
         (denote' G r1 Φ (x'::List.take i xs'))
      /\ (denote' G (Regex.star r1) Φ (List.drop i xs'))
  termination_by (xs, r)
  decreasing_by
    · apply decreasing_symbol
    · apply decreasing_or_l
    · apply decreasing_or_r
    · apply denote_sizeOf_concat_left
    · apply denote_sizeOf_concat_right
    · apply denote_sizeOf_star_left
    · apply denote_sizeOf_star_right

def Rule.denote
  {α: Type} {n: Nat} {φ: Type}
  (G: Grammar n φ)
  (Φ: φ -> α -> Prop)
  (r: Regex (φ × Ref n)) (xs: Hedge α): Prop :=
  Rule.denote' G r Φ xs

theorem denote_emptyset {α: Type} {φ: Type} (G: Hedge.Grammar n φ) (Φ: φ -> α -> Prop):
  Rule.denote G Φ Regex.emptyset = Language.emptyset := by
  unfold Rule.denote
  simp only [Rule.denote']
  rfl

theorem denote_emptystr {α: Type} {φ: Type} (G: Hedge.Grammar n φ) (Φ: φ -> α -> Prop):
  Rule.denote G Φ Regex.emptystr = Language.emptystr := by
  unfold Rule.denote
  simp only [Rule.denote']
  rfl

theorem denote_onlyif {α: Type}
  (condition: Prop) [dcond: Decidable condition]
  (G: Grammar n φ) {Φ: φ -> α -> Prop} (x: Regex (φ × Ref n)):
  Rule.denote G Φ (Regex.onlyif condition x) = Language.onlyif condition (Rule.denote G Φ x) := by
  unfold Language.onlyif
  unfold Regex.onlyif
  funext xs
  split_ifs
  case pos hc =>
    simp only [eq_iff_iff, iff_and_self]
    intro d
    assumption
  case neg hc =>
    simp only [eq_iff_iff]
    rw [Rule.denote]
    rw [Rule.denote']
    simp only [false_iff, not_and]
    intro h
    contradiction

theorem denote_symbol {α: Type} {φ: Type} (G: Hedge.Grammar n φ) (Φ: φ -> α -> Prop) [DecidableRel Φ] (s: (φ × Ref n)):
  Rule.denote G Φ (Regex.symbol s) = Language.tree (fun a => Φ s.1 a) (Rule.denote G Φ (G.lookup s.2)) := by
  unfold Rule.denote
  unfold Language.tree
  funext xs
  simp only
  cases xs with
  | nil =>
    rw [Rule.denote']
    simp only [List.ne_cons_self, decide_eq_true_eq, false_and, exists_const, exists_false]
    intro x h
    contradiction
  | cons x xs =>
    cases xs with
    | nil =>
      rw [Rule.denote']
      simp only [List.cons.injEq, and_true, decide_eq_true_eq]
      cases x with
      | mk label children =>
      simp only [Node.mk.injEq, ↓existsAndEq, and_true, exists_eq_left']
      simp only [Node.getLabel]
      simp_all only [eq_iff_iff, and_congr_right_iff]
      intro a
      obtain ⟨fst, snd⟩ := s
      simp_all only
      rfl
    | cons x' xs =>
      rw [Rule.denote']
      simp
      intro x h
      simp at h

theorem denote_or {α: Type} {φ: Type} (G: Hedge.Grammar n φ) (Φ: φ -> α -> Prop) (r1 r2: Regex (φ × Ref n)):
  Rule.denote G Φ (Regex.or r1 r2) = Language.or (Rule.denote G Φ r1) (Rule.denote G Φ r2) := by
  unfold Rule.denote
  funext
  simp only [Rule.denote', Language.or]

theorem denote_concat {α: Type} {φ: Type} (G: Hedge.Grammar n φ) (Φ: φ -> α -> Prop) (p q: Regex (φ × Ref n)):
  Rule.denote G Φ (Regex.concat p q) = Language.concat (Rule.denote G Φ p) (Rule.denote G Φ q) := by
  unfold Rule.denote
  funext
  simp only [Rule.denote']
  unfold Language.concat
  rfl

theorem unfold_denote_star {α: Type} {φ: Type} (G: Hedge.Grammar n φ) (Φ: φ -> α -> Prop) (r: Regex (φ × Ref n)) (xs: Hedge α):
  Rule.denote' G (Regex.star r) (fun p x' => Φ p x') xs
  = (match xs with
    | [] => True
    | (x'::xs') =>
       ∃ (n: Fin xs.length),
         (Rule.denote' G r Φ (x'::List.take n xs'))
      /\ (Rule.denote' G (Regex.star r) Φ (List.drop n xs'))) := by
  cases xs with
  | nil =>
    simp [Rule.denote']
  | cons x xs =>
    cases xs with
    | cons _ _ =>
      simp only [Rule.denote']
    | nil =>
      simp only [Rule.denote']

theorem denote_star_iff' {α: Type} {φ: Type} (G: Hedge.Grammar n φ) (Φ: φ -> α -> Prop) (r: Regex (φ × Ref n)) (xs: Hedge α):
  Rule.denote' G (Regex.star r) (fun p x' => Φ p x') xs <-> Language.star (Rule.denote' G r (fun p x' => Φ p x')) xs := by
  rw [<- eq_iff_iff]
  unfold Language.star
  rw [unfold_denote_star]
  cases xs with
  | nil =>
    rfl
  | cons x xs =>
    simp only
    congr
    ext n
    rw [<- eq_iff_iff]
    congr
    simp only [List.length_cons, eq_iff_iff]
    rw [<- denote_star_iff']
  termination_by xs.length
  decreasing_by
    obtain ⟨n, hn⟩ := n
    apply List.list_length_drop_lt_cons

theorem denote_star_iff {α: Type} {φ: Type} (G: Hedge.Grammar n φ) (Φ: φ -> α -> Prop) (r: Regex (φ × Ref n)) (xs: Hedge α):
  Rule.denote G Φ (Regex.star r) xs <-> Language.star (Rule.denote G Φ r) xs := by
  unfold Rule.denote
  rw [denote_star_iff']

theorem denote_star {α: Type} {φ: Type} (G: Hedge.Grammar n φ) (Φ: φ -> α -> Prop) (r: Regex (φ × Ref n)):
  Rule.denote G Φ (Regex.star r) = Language.star (Rule.denote G Φ r) := by
  funext
  rw [denote_star_iff]

theorem null_commutes {α: Type}
  (G: Grammar n φ) (Φ: φ -> α -> Prop) [DecidableRel Φ] (x: Regex (φ × Ref n)):
  ((Regex.null x) = true) = Language.null (Rule.denote G Φ x) := by
  induction x with
  | emptyset =>
    rw [denote_emptyset]
    rw [Language.null_emptyset]
    unfold Regex.null
    apply Bool.false_eq_true
  | emptystr =>
    rw [denote_emptystr]
    rw [Language.null_emptystr]
    unfold Regex.null
    simp only
  | symbol s =>
    obtain ⟨p, children⟩ := s
    rw [denote_symbol]
    rw [Language.null_tree]
    unfold Regex.null
    apply Bool.false_eq_true
  | or p q ihp ihq =>
    rw [denote_or]
    rw [Language.null_or]
    unfold Regex.null
    rw [<- ihp]
    rw [<- ihq]
    unfold Regex.null
    rw [Bool.or_eq_true]
  | concat p q ihp ihq =>
    rw [denote_concat]
    rw [Language.null_concat]
    unfold Regex.null
    rw [<- ihp]
    rw [<- ihq]
    unfold Regex.null
    rw [Bool.and_eq_true]
  | star r ih =>
    rw [denote_star]
    rw [Language.null_star]
    unfold Regex.null
    simp only

theorem denote_nil_is_null (Φ: φ -> α -> Prop) [DecidableRel Φ]:
  Rule.denote G Φ r [] = Regex.null r := by
  rw [null_commutes G (fun s a => Φ s a)]
  cases r with
  | emptyset =>
    simp only [denote_emptyset, Language.emptyset, Language.null]
  | emptystr =>
    simp only [denote_emptystr, Language.emptystr, Language.null]
  | symbol s =>
    simp only [denote_symbol]
    simp only [Language.null]
  | or r1 r2 =>
    simp only [denote_or, Language.or, Language.null]
  | concat r1 r2 =>
    simp only [denote_concat, Language.null]
  | star r1 =>
    simp only [denote_star, Language.null]

def denote (G: Grammar n φ) (Φ: φ -> α -> Prop) (xs: Hedge α): Prop :=
  Rule.denote G Φ G.start xs
