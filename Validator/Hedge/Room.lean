import Mathlib.Tactic.SimpRw

import Validator.Std.Decidable
import Validator.Std.Hedge

import Validator.Regex.Language
import Validator.Regex.Room
import Validator.Hedge.Denote
import Validator.Hedge.Grammar
import Validator.Hedge.IfExpr
import Validator.Hedge.Language

namespace Hedge

def Grammar.Room.derive
  (G: Grammar n φ) (Φ: φ -> α -> Bool) (r: Rule n φ) (node: Node α): Rule n φ :=
  Regex.Room.derive (fun (s: Symbol n φ) =>
    let ⟨label, children⟩ := node
    let childr: Rule n φ := evalif G Φ s label
    Regex.null (List.foldl (derive G Φ) childr children)
  ) r

end Hedge

namespace Hedge.Grammar.Room

theorem unapply_hedge_param_and_flip
  (G: Grammar n φ) (Φ: φ -> α -> Bool) (x: Node α):
  (fun (symbol: Grammar.Symbol n φ) =>
    match x with
    | Node.mk label children =>
      let ifExpr: Grammar.Symbol n φ := symbol
      let childr: Grammar.Rule n φ := Grammar.evalif G Φ ifExpr label
      let dchildr: Grammar.Rule n φ := List.foldl (derive G Φ) childr children
      Regex.null dchildr
  )
  =
  (flip fun (symbol: Grammar.Symbol n φ) (x': Node α) =>
    match x' with
    | Node.mk label children =>
      let ifExpr: Grammar.Symbol n φ := symbol
      let childr: Grammar.Rule n φ := Grammar.evalif G Φ ifExpr label
      let dchildr: Grammar.Rule n φ := List.foldl (derive G Φ) childr children
      Regex.null dchildr
  ) x := by
  rfl

theorem derive_emptyset {α: Type} (G: Grammar n φ) (Φ: φ -> α -> Bool) (a: Node α):
  Grammar.Room.derive G Φ Regex.emptyset a = Regex.emptyset := by
  unfold derive
  rw [unapply_hedge_param_and_flip]
  rw [Regex.Room.derive_emptyset]

theorem derive_emptystr {α: Type} (G: Grammar n φ) (Φ: φ -> α -> Bool) (a: Node α):
  Grammar.Room.derive G Φ Regex.emptystr a = Regex.emptyset := by
  unfold derive
  rw [unapply_hedge_param_and_flip]
  rw [Regex.Room.derive_emptystr]

theorem derive_symbol {α: Type} (G: Grammar n φ) (Φ: φ -> α -> Bool) (a: Node α):
  Grammar.Room.derive G Φ (Regex.symbol s) a
    = Regex.onlyif (
        ( match a with
          | Node.mk label children =>
            (List.foldl (derive G Φ) (G.evalif Φ s label) children).null
        ) = true)
        Regex.emptystr := by
  unfold derive
  rw [unapply_hedge_param_and_flip]
  rw [Regex.Room.derive_symbol]

theorem derive_or {α: Type} (G: Grammar n φ) (Φ: φ -> α -> Bool) (r1 r2: Rule n φ) (a: Node α):
  Grammar.Room.derive G Φ (Regex.or r1 r2) a
  = Regex.or (Grammar.Room.derive G Φ r1 a) (Grammar.Room.derive G Φ r2 a) := by
  unfold derive
  rw [unapply_hedge_param_and_flip]
  rw [Regex.Room.derive_or]

theorem derive_concat {α: Type} (G: Grammar n φ) (Φ: φ -> α -> Bool) (r1 r2: Rule n φ) (a: Node α):
  Grammar.Room.derive G Φ (Regex.concat r1 r2) a
    = Regex.or
      (Regex.concat (Grammar.Room.derive G Φ r1 a) r2)
      (Regex.onlyif (Regex.null r1) (Grammar.Room.derive G Φ r2 a)) := by
  unfold derive
  rw [unapply_hedge_param_and_flip]
  rw [Regex.Room.derive_concat]

theorem derive_star {α: Type} (G: Grammar n φ) (Φ: φ -> α -> Bool) (r1: Rule n φ) (a: Node α):
  Grammar.Room.derive G Φ (Regex.star r1) a
  = Regex.concat (Grammar.Room.derive G Φ r1 a) (Regex.star r1) := by
  unfold derive
  rw [unapply_hedge_param_and_flip]
  rw [Regex.Room.derive_star]

theorem and_start {α: Type} (G: Grammar n φ) (Φ: φ -> α -> Prop) [DecidableRel Φ] (label: α) (children: Hedge α):
  ((List.foldl (derive G (decideRel Φ)) (if decideRel Φ p label then G.lookup ref else Regex.emptyset) children).null = true)
  = ((Φ p label = true) /\ ((List.foldl (derive G (decideRel Φ)) (G.lookup ref) children).null = true)) := by
  generalize (G.lookup ref) = r
  split_ifs
  case pos h =>
    simp_all [decideRel]
  case neg h =>
    simp_all only [decideRel, decide_eq_true_eq, eq_iff_iff, iff_true, false_and, iff_false,
      Bool.not_eq_true]
    induction children with
    | nil =>
      simp only [Regex.null, List.foldl_nil, Regex.null]
    | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [derive_emptyset]
      rw [ih]

theorem derive_denote_symbol_is_onlyif {α: Type} (G: Grammar n φ) (Φ: φ -> α -> Prop) [DecidableRel Φ] (label: α) (children: Hedge α):
  Language.derive
    (Rule.denote G Φ
      (Regex.symbol (pred, ref))
    )
    (Node.mk label children)
  =
    Language.onlyif
      (Φ pred label ∧ Rule.denote G Φ (G.lookup ref) children)
      Language.emptystr
  := by
  funext xs
  rw [Grammar.denote_symbol]
  rw [Language.derive_iff_tree]
  simp only [decide_eq_true_eq]

theorem derive_commutes_symbol {α: Type}
  (G: Grammar n φ)
  (Φ: φ -> α -> Prop)
  [DecidableRel Φ]
  (pred: φ)
  (ref: Ref n)
  (x4: Node α)
  (xs: Hedge α)
  (ihr:
    ∀ (r: Grammar.Rule n φ) (x3: Node.DescendantOf x4) (xs: Hedge α),
        Grammar.Rule.denote G Φ (Grammar.Room.derive G (decideRel Φ) r x3.val) xs
    <-> Language.derive (Grammar.Rule.denote G Φ r) x3.val xs
  )
  :
  Rule.denote G Φ (derive G (decideRel Φ) (Regex.symbol (pred, ref)) x4) xs =
  Language.derive (Rule.denote G Φ (Regex.symbol (pred, ref))) x4 xs := by
  cases x4 with
  | mk label children =>

  rw [derive_denote_symbol_is_onlyif]

  rw [derive_symbol]
  simp only
  rw [Grammar.denote_onlyif]

  rw [Grammar.denote_emptystr]
  congr

  simp only [evalif]
  simp only [and_start]
  simp only [eq_iff_iff, iff_true]
  rw [<- eq_iff_iff]
  congr

  generalize G.lookup ref = r
  induction children generalizing r with
  | nil =>
    simp only [List.foldl_nil]
    rw [Grammar.denote_nil_is_null]
  | cons x2 xs ihxs =>
    simp only [List.foldl]
    rw [ihxs]
    · have hchild := Node.Descendant.mkFirstChild_eq label x2 xs
      have ihr := ihr (r := r) (x3 := hchild.val) (xs := xs)
      cases hchild with
      | mk hdes heq =>
      rw [<- heq]
      rw [ihr]
      rfl
    · intro r' x3 xs'
      have hcons := Node.Descendant.consFirstChild_eq x2 x3
      have ihr := ihr r' hcons.val xs'
      cases hcons with
      | mk hdes heq =>
      rw [<- heq]
      simp at ihr
      rw [ihr]
      rfl

theorem revert_param (f g: α -> β):
  f = g -> ∀ x, f x = g x := by
  intro a x
  subst a
  simp_all only

theorem derive_commutes_iff {α: Type} (G: Grammar n φ) (Φ: φ -> α -> Prop) [DecidableRel Φ] (r: Grammar.Rule n φ) (x: Node α) (xs: Hedge α):
  Grammar.Rule.denote G Φ (Grammar.Room.derive G (decideRel Φ) r x) xs
  <-> Language.derive (Grammar.Rule.denote G Φ r) x xs := by
  rw [<- eq_iff_iff]
  apply revert_param
  induction r with
  | emptyset =>
    rw [derive_emptyset]
    rw [Grammar.denote_emptyset]
    rw [Language.derive_emptyset]
  | emptystr =>
    rw [derive_emptystr]
    rw [Grammar.denote_emptystr]
    rw [Grammar.denote_emptyset]
    rw [Language.derive_emptystr]
  | symbol s =>
    funext xs
    cases s with
    | mk pred ref =>
    let ihr :=
      fun (r: Grammar.Rule n φ) (x7: Node.DescendantOf x) (xs: Hedge α) =>
        derive_commutes_iff G Φ r x7 xs
    rw [derive_commutes_symbol (ihr := ihr) (x4 := x)]
  | or r1 r2 ih1 ih2 =>
    rw [derive_or]
    rw [Grammar.denote_or]
    rw [Grammar.denote_or]
    rw [Language.derive_or]
    rw [ih1]
    rw [ih2]
  | concat r1 r2 ih1 ih2 =>
    rw [derive_concat]
    rw [Grammar.denote_concat]
    rw [Grammar.denote_or]
    rw [Grammar.denote_concat]
    rw [Grammar.denote_onlyif]
    rw [Language.derive_concat]
    rw [<- ih1]
    rw [<- ih2]
    congr
    apply Grammar.null_commutes
  | star r1 ih1 =>
    rw [derive_star]
    rw [Grammar.denote_star]
    rw [Grammar.denote_concat]
    rw [Grammar.denote_star]
    rw [Language.derive_star]
    rw [ih1]
  termination_by x
  decreasing_by
    apply Node.DescendantOf.sizeOf

theorem derive_commutes (G: Grammar n φ) (Φ: φ -> α -> Prop) [DecidableRel Φ] (r: Rule n φ) (x: Node α):
  Rule.denote G Φ (Grammar.Room.derive G (decideRel Φ) r x)
  = Language.derive (Rule.denote G Φ r) x := by
  funext xs
  rw [derive_commutes_iff]

theorem derive_commutesb (G: Grammar n φ) (Φ: φ -> α -> Bool) (r: Rule n φ) (x: Node α):
  Rule.denote G (fun s a => Φ s a) (Grammar.Room.derive G Φ r x)
  = Language.derive (Rule.denote G (fun s a => Φ s a) r) x := by
  have h1: (fun s a => Φ s a) = decideRel (fun s a => Φ s a) := by
    unfold decideRel
    aesop
  have h2: (fun s a => Φ s a) = Φ := by
    rfl
  nth_rewrite 2 [<- h2]
  rw [h1]
  rw [derive_commutes]
