import Validator.Std.Vec

import Validator.Regex.Language

-- A regular expression is defined over a generic symbol
inductive Regex (σ: Type) where
  | emptyset | emptystr | symbol (s: σ)
  | or (r1 r2: Regex σ) | concat (r1 r2: Regex σ) | star (r1: Regex σ)
  deriving DecidableEq, Ord, Repr, Hashable, Repr

instance [Ord σ]: Ord (Regex σ) := inferInstance

instance [Repr σ]: Repr (Regex σ) := inferInstance

instance [DecidableEq σ]: DecidableEq (Regex σ) := inferInstance

instance [DecidableEq σ]: BEq (Regex σ) := inferInstance

instance [Hashable σ]: Hashable (Regex σ) := inferInstance

def Regex.null: (r: Regex σ) → Bool
  | emptyset => false | emptystr => true | symbol _ => false | star _ => true
  | or p q => (null p || null q) | concat p q => (null p && null q)

namespace Regex

-- A regular expression is denoted as usual, expect that allow the user to inject the denotation of the generic symbol, Φ.
-- This allows us to handle generic predicates or even trees, without extending the original regular expression with new operators.
def denote (Φ : σ → α → Prop) (r: Regex σ): (xs: List α) → Prop :=
  match r with
  | emptyset => Lang.emptyset
  | emptystr => Lang.emptystr
  | symbol s => Lang.symbol Φ s
  | or p q => Lang.or (denote Φ p) (denote Φ q)
  | concat p q => Lang.concat (denote Φ p) (denote Φ q)
  | star p => Lang.star (denote Φ p)

def unescapable :(x: Regex σ) → Bool
  | emptyset => true | _ => false

def onlyif (cond: Prop) [dcond: Decidable cond] (r: Regex σ): Regex σ :=
  if cond then r else emptyset

theorem denote_onlyif {α: Type} (Φ : σ → α → Prop) (condition: Prop) [dcond: Decidable condition] (r: Regex σ):
  denote Φ (onlyif condition r) = Lang.onlyif condition (denote Φ r) := by
  unfold Lang.onlyif
  unfold onlyif
  funext xs
  split_ifs
  case pos hc =>
    simp only [eq_iff_iff, iff_and_self]
    intro d
    assumption
  case neg hc =>
    simp only [eq_iff_iff]
    rw [denote]
    rw [Lang.emptyset]
    simp only [false_iff, not_and]
    intro hc'
    contradiction

end Regex

def Regex.derive (Φ: σ → α → Bool) (r: Regex σ) (a: α): Regex σ := match r with
  | emptyset => emptyset | emptystr => emptyset
  | symbol s => onlyif (Φ s a) emptystr
  | or r1 r2 => or (derive Φ r1 a) (derive Φ r2 a)
  | concat r1 r2 => or
      (concat (derive Φ r1 a) r2)
      (onlyif (null r1) (derive Φ r2 a))
  | star r1 => concat (derive Φ r1 a) (star r1)

namespace Regex

#guard
  derive (· == ·) (Regex.or (Regex.symbol 1) (Regex.symbol 2)) 1
  = Regex.or Regex.emptystr Regex.emptyset

def map_derive (Φ: σ → α → Bool) (rs: Vector (Regex σ) l) (a: α): Vector (Regex σ) l :=
  Vector.map (fun r => derive Φ r a) rs

def fold_derive (Φ: σ → α → Bool) (r: Regex σ) (xs: List α): Regex σ :=
  (List.foldl (derive Φ) r) xs

def validate (Φ: σ → α → Bool) (r: Regex σ) (xs: List α): Bool :=
  null (fold_derive Φ r xs)

-- derive char

end Regex

def Regex.Char.derive (r: Regex Char) (a: Char): Regex Char := match r with
  | emptyset => emptyset | emptystr => emptyset
  | symbol s => onlyif (s == a) emptystr
  | or r1 r2 => or (derive r1 a) (derive r2 a)
  | concat r1 r2 => or
    (concat (derive r1 a) r2)
    (onlyif (null r1) (derive r2 a))
  | star r1 => concat (derive r1 a) (star r1)

theorem Regex.Char.derive_is_derive_symbol:
  Regex.Char.derive r a = Regex.derive (fun s a => s == a) r a := by
  induction r with
  | emptyset => rfl
  | emptystr => rfl
  | symbol s => rfl
  | or r1 r2 ih1 ih2 =>
    simp only [Regex.Char.derive, Regex.derive]
    rw [ih1]
    rw [ih2]
  | concat r1 r2 ih1 ih2 =>
    simp only [Regex.Char.derive, Regex.derive]
    rw [ih1]
    rw [ih2]
  | star r1 ih1 =>
    simp only [Regex.Char.derive, Regex.derive]
    rw [ih1]

-- derive theorems

namespace Regex

theorem derive_emptyset {α: Type} {σ: Type} (Φ: σ → α → Bool) (a: α):
  derive Φ emptyset a = emptyset := by
  simp only [derive]

theorem derive_emptystr {α: Type} {σ: Type} (Φ: σ → α → Bool) (a: α):
  derive Φ emptystr a = emptyset := by
  simp only [derive]

theorem derive_symbol {α: Type} {σ: Type} (Φ: σ → α → Bool) (s: σ) (a: α):
  derive Φ (symbol s) a = onlyif (Φ s a) emptystr := by
  simp only [derive]

theorem derive_or {α: Type} {σ: Type} (Φ: σ → α → Bool) (r1 r2: Regex σ) (a: α):
  derive Φ (or r1 r2) a = or (derive Φ r1 a) (derive Φ r2 a) := by
  simp only [derive]

theorem derive_concat {α: Type} {σ: Type} (Φ: σ → α → Bool) (r1 r2: Regex σ) (a: α):
  derive Φ (concat r1 r2) a
    = or
      (concat (derive Φ r1 a) r2)
      (onlyif (null r1) (derive Φ r2 a)) := by
  simp only [derive]

theorem derive_star {α: Type} {σ: Type} (Φ: σ → α → Bool) (r1: Regex σ) (a: α):
  derive Φ (star r1) a = concat (derive Φ r1 a) (star r1) := by
  simp only [derive]

-- We prove that for each regular expression the denotation holds for the specific language definition:
-- * Regex.denote Φ Regex.emptyset = Lang.emptyset
-- * Regex.denote Φ Regex.emptystr = Lang.emptystr
-- * Regex.denote Φ (Regex.symbol s) = Φ s
-- * Regex.denote Φ (Regex.or p q) = Lang.or (Regex.denote Φ p) (Regex.denote Φ q)
-- * Regex.denote Φ (Regex.concat p q) = Lang.concat (Regex.denote Φ p) (Regex.denote Φ q)
-- * Regex.denote Φ (Regex.star r) = Lang.star (Regex.denote Φ r)

theorem denote_emptyset {α: Type} {σ: Type} (Φ: σ → α → Prop):
  denote Φ emptyset = Lang.emptyset := by
  simp only [denote]

theorem denote_emptystr {α: Type} {σ: Type} (Φ: σ → α → Prop):
  denote Φ emptystr = Lang.emptystr := by
  simp only [denote]

theorem denote_symbol {α: Type} {σ: Type} (Φ: σ → α → Prop) (s: σ):
  denote Φ (symbol s) = Lang.symbol Φ s := by
  simp only [denote]

theorem denote_or {α: Type} {σ: Type} (Φ: σ → α → Prop) (p q: Regex σ):
  denote Φ (or p q) = Lang.or (denote Φ p) (denote Φ q) := by
  funext
  simp only [denote, Lang.or]

theorem denote_concat {α: Type} {σ: Type} (Φ: σ → α → Prop) (p q: Regex σ):
  denote Φ (concat p q) = Lang.concat (denote Φ p) (denote Φ q) := by
  funext
  simp only [denote]

theorem denote_star' {α: Type} {σ: Type} (Φ: σ → α → Prop) (r: Regex σ) (xs: List α):
  denote Φ (star r) xs ↔ Lang.star (denote Φ r) xs := by
  simp only [denote]

theorem denote_star {α: Type} {σ: Type} (Φ: σ → α → Prop) (r: Regex σ):
  denote Φ (star r) = Lang.star (denote Φ r) := by
  simp only [denote]

-- Commutes proofs

theorem null_commutes {σ: Type} {α: Type} (Φ: σ → α → Prop) (r: Regex σ):
  ((null r) = true) = Lang.null (denote Φ r) := by
  induction r with
  | emptyset =>
    unfold denote
    rw [Lang.null_emptyset]
    unfold null
    apply Bool.false_eq_true
  | emptystr =>
    unfold denote
    rw [Lang.null_emptystr]
    unfold null
    simp only
  | symbol p =>
    unfold denote
    rw [Lang.null_symbol]
    unfold null
    apply Bool.false_eq_true
  | or p q ihp ihq =>
    unfold denote
    rw [Lang.null_or]
    unfold null
    rw [<- ihp]
    rw [<- ihq]
    rw [Bool.or_eq_true]
  | concat p q ihp ihq =>
    unfold denote
    rw [Lang.null_concat]
    unfold null
    rw [<- ihp]
    rw [<- ihq]
    rw [Bool.and_eq_true]
  | star r ih =>
    unfold denote
    rw [Lang.null_star]
    unfold null
    simp only

theorem derive_commutes {σ: Type} {α: Type} (Φ: σ → α → Prop) [DecidableRel Φ] (r: Regex σ) (x: α):
  denote Φ (derive (fun s a => Φ s a) r x) = Lang.derive (denote Φ r) x := by
  induction r with
  | emptyset =>
    simp only [denote, derive]
    rw [Lang.derive_emptyset]
  | emptystr =>
    simp only [denote, derive]
    rw [Lang.derive_emptystr]
  | symbol p =>
    simp only [denote]
    rw [Lang.derive_symbol]
    unfold derive
    rw [denote_onlyif]
    simp only [denote]
    simp only [decide_eq_true_eq]
  | or p q ihp ihq =>
    simp only [denote, derive]
    rw [Lang.derive_or]
    unfold Lang.or
    rw [ihp]
    rw [ihq]
  | concat p q ihp ihq =>
    simp only [denote, derive]
    rw [Lang.derive_concat]
    rw [<- ihp]
    rw [<- ihq]
    rw [denote_onlyif]
    congrm (Lang.or (Lang.concat (denote Φ (derive (fun s a => Φ s a) p x)) (denote Φ q)) ?_)
    rw [null_commutes]
  | star r ih =>
    simp only [denote, derive]
    rw [Lang.derive_star]
    guard_target =
      Lang.concat (denote Φ (derive (fun s a => Φ s a) r x)) (Lang.star (denote Φ r))
      = Lang.concat (Lang.derive (denote Φ r) x) (Lang.star (denote Φ r))
    congrm ((Lang.concat ?_ (Lang.star (denote Φ r))))
    guard_target = denote Φ (derive (fun s a => Φ s a) r x) = Lang.derive (denote Φ r) x
    exact ih

theorem derive_commutesb {σ: Type} {α: Type} (Φ: σ → α → Bool) (r: Regex σ) (x: α):
  denote (fun s a => Φ s a) (derive (fun s a => Φ s a) r x) = Lang.derive (denote (fun s a => Φ s a) r) x := by
  rw [<- derive_commutes]
  congr
  funext s a
  simp only [Bool.decide_eq_true]

theorem derives_commutes {α: Type} (Φ: σ → α → Prop) [DecidableRel Φ] (r: Regex σ) (xs: List α):
  denote Φ (fold_derive (fun s a => Φ s a) r xs) = Lang.derives (denote Φ r) xs := by
  unfold fold_derive
  rw [Lang.derives_foldl]
  induction xs generalizing r with
  | nil =>
    simp only [List.foldl_nil]
  | cons x xs ih =>
    simp only [List.foldl_cons]
    have h := derive_commutes Φ r x
    have ih' := ih (derive (fun s a => Φ s a) r x)
    rw [h] at ih'
    exact ih'

theorem validate_commutes {α: Type} (Φ: σ → α → Prop) [DecidableRel Φ] (r: Regex σ) (xs: List α):
  (validate (fun s a => Φ s a) r xs = true) = (denote Φ r) xs := by
  rw [<- Lang.validate (denote Φ r) xs]
  unfold validate
  rw [<- derives_commutes]
  rw [<- null_commutes]

-- decidableDenote shows that the derivative algorithm is decidable
-- https://leanprover.zulipchat.com/#narrow/channel/270676-lean4/topic/restricting.20axioms
def decidableDenote (Φ: σ → α → Prop) [DecidableRel Φ] (r: Regex σ): DecidablePred (denote Φ r) :=
  fun xs => decidable_of_decidable_of_eq (validate_commutes Φ r xs)
