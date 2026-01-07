import Validator.Std.Vec

import Validator.Regex.Lang

-- A regular expression is defined over a generic symbol
inductive Regex (σ: Type) where
  | emptyset | emptystr | symbol (s: σ)
  | or (r1 r2: Regex σ) | concat (r1 r2: Regex σ) | star (r1: Regex σ)
  deriving DecidableEq, Ord, Repr, Hashable, BEq

def Regex.null: (r: Regex σ) → Bool
  | emptyset => false | emptystr => true | symbol _ => false | star _ => true
  | or p q => (null p || null q) | concat p q => (null p && null q)

def Regex.denote (Φ : σ → α → Prop) (r: Regex σ) (xs: List α): Prop :=
  match r with
  | emptyset => False
  | emptystr => xs = []
  | symbol s => match xs with
    | [x] => Φ s x | _ => False
  | or r1 r2 => (denote Φ r1 xs) \/ (denote Φ r2 xs)
  | concat r1 r2 => ∃ (i: Fin (xs.length + 1)),
      (denote Φ r1 (List.take i xs)) /\ (denote Φ r2 (List.drop i xs))
  | star r1 => match xs with
    | [] => True
    | (x::xs') => ∃ (i: Fin xs.length),
                        (denote Φ r1 (x::List.take i xs'))
                        /\ (denote Φ (Regex.star r1) (List.drop i xs'))
  termination_by (r, xs.length)

namespace Regex

def unescapable :(x: Regex σ) → Bool
  | emptyset => true | _ => false

def onlyif (cond: Prop) [dcond: Decidable cond] (r: Regex σ): Regex σ :=
  if cond then r else emptyset

def oneOrMore (r: Regex σ): Regex σ := Regex.concat r (Regex.star r)

def optional (r: Regex σ): Regex σ := Regex.or r Regex.emptystr

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
  funext xs
  simp only [denote, Lang.emptyset]

theorem denote_emptystr {α: Type} {σ: Type} (Φ: σ → α → Prop):
  denote Φ emptystr = Lang.emptystr := by
  funext xs
  simp only [denote, Lang.emptystr]

theorem denote_symbol {α: Type} {σ: Type} (Φ: σ → α → Prop) (s: σ):
  denote Φ (symbol s) = Lang.symbol Φ s := by
  funext xs
  cases xs with
  | nil =>
    simp only [denote, Lang.symbol]
    -- aesop?
    simp_all only [List.ne_cons_self, false_and, exists_false]
  | cons x xs =>
    cases xs with
    | nil =>
      simp only [denote, Lang.symbol]
      -- aesop?
      simp_all only [List.cons.injEq, and_true, exists_eq_left']
    | cons x' xs =>
      simp only [denote, Lang.symbol]
      -- aesop?
      simp_all only [List.cons.injEq, reduceCtorEq, and_false, false_and, exists_false]

theorem denote_or {α: Type} {σ: Type} (Φ: σ → α → Prop) (p q: Regex σ):
  denote Φ (or p q) = Lang.or (denote Φ p) (denote Φ q) := by
  funext
  simp only [denote, Lang.or]

theorem denote_concat {α: Type} {σ: Type} (Φ: σ → α → Prop) (p q: Regex σ):
  denote Φ (concat p q) = Lang.concat (denote Φ p) (denote Φ q) := by
  funext
  simp only [denote, Lang.concat]

theorem denote_star_iff {α: Type} {σ: Type} (Φ: σ → α → Prop) (r: Regex σ) (xs: List α):
  denote Φ (star r) xs ↔ Lang.star (denote Φ r) xs := by
  cases xs with
  | nil =>
    simp only [denote, Lang.star]
  | cons x xs =>
    simp only [denote, Lang.star]
    apply Iff.intro
    case mp =>
      intro h
      obtain ⟨⟨i, hi⟩, h1, h2⟩ := h
      exists ⟨i, hi⟩
      apply And.intro h1
      rw [<- (denote_star_iff Φ r (List.drop i xs))]
      simp only at h2
      exact h2
    case mpr =>
      intro h
      obtain ⟨⟨i, hi⟩, h1, h2⟩ := h
      exists ⟨i, hi⟩
      apply And.intro h1
      rw [(denote_star_iff Φ r (List.drop i xs))]
      simp only at h2
      exact h2
  termination_by xs.length

theorem denote_star {α: Type} {σ: Type} (Φ: σ → α → Prop) (r: Regex σ):
  denote Φ (star r) = Lang.star (denote Φ r) := by
  funext xs
  rw [denote_star_iff]

-- Commutes proofs

theorem null_commutes {σ: Type} {α: Type} (Φ: σ → α → Prop) (r: Regex σ):
  ((null r) = true) = Lang.null (denote Φ r) := by
  unfold Lang.null
  induction r with
  | emptyset =>
    unfold denote
    unfold null
    apply Bool.false_eq_true
  | emptystr =>
    unfold denote
    unfold null
    simp only
  | symbol p =>
    unfold denote
    unfold null
    apply Bool.false_eq_true
  | or p q ihp ihq =>
    unfold denote
    unfold null
    rw [<- ihp]
    rw [<- ihq]
    rw [Bool.or_eq_true]
  | concat p q ihp ihq =>
    unfold denote
    unfold null
    rw [Bool.and_eq_true p.null q.null]
    rw [ihp]
    rw [ihq]
    simp only [List.length_nil, Nat.reduceAdd, Fin.val_eq_zero, List.take_nil, List.drop_nil,
      exists_const]
  | star r ih =>
    unfold denote
    unfold null
    simp only

theorem derive_commutes {σ: Type} {α: Type} (Φ: σ → α → Prop) [DecidableRel Φ] (r: Regex σ) (x: α):
  denote Φ (derive (fun s a => Φ s a) r x) = Lang.derive (denote Φ r) x := by
  induction r with
  | emptyset =>
    simp only [derive, denote_emptyset]
    rw [Lang.derive_emptyset]
  | emptystr =>
    simp only [derive, denote_emptyset, denote_emptystr]
    rw [Lang.derive_emptystr]
  | symbol p =>
    simp only [denote_symbol]
    rw [Lang.derive_symbol]
    unfold derive
    rw [denote_onlyif]
    simp only [denote_emptystr]
    simp only [decide_eq_true_eq]
  | or p q ihp ihq =>
    simp only [denote_or, derive]
    rw [Lang.derive_or]
    unfold Lang.or
    rw [ihp]
    rw [ihq]
  | concat p q ihp ihq =>
    simp only [denote_concat, denote_or, derive]
    rw [Lang.derive_concat]
    rw [<- ihp]
    rw [<- ihq]
    rw [denote_onlyif]
    congrm (Lang.or (Lang.concat (denote Φ (derive (fun s a => Φ s a) p x)) (denote Φ q)) ?_)
    rw [null_commutes]
  | star r ih =>
    simp only [denote_star, denote_concat, derive]
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
