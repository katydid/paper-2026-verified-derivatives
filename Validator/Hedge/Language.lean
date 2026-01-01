import Validator.Std.Hedge
import Validator.Regex.Language

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

def Lang (α: Type): Type := Langs (Hedge.Node α)

def tree {α: Type} (φ: α -> Bool) (R: Lang α): Lang α :=
  fun xs => ∃ label children, xs = [Hedge.Node.mk label children] /\ φ label /\ R children

def tree_match {α: Type} (φ: α -> Bool) (R: Lang α): Lang α :=
  fun xs =>
    match xs with
    | [Hedge.Node.mk label children] =>
      φ label /\ R children
    | _ => False

theorem tree_exists_is_tree_match:
  tree φ R = tree_match φ R := by
  unfold tree
  unfold tree_match
  funext xs
  cases xs with
  | nil =>
    simp only [List.ne_cons_self, false_and, exists_const, exists_false]
  | cons x xs =>
    cases xs with
    | nil =>
      simp only [cons.injEq, and_true, eq_iff_iff]
      cases x with
      | mk label children =>
      simp only [Hedge.Node.mk.injEq]
      apply Iff.intro
      case mp =>
        intro h
        obtain ⟨label1, children1, ⟨h1, h2⟩, h3⟩ := h
        subst_vars
        exact h3
      case mpr =>
        intro ⟨h1, h2⟩
        exists label
        exists children
    | cons x' xs =>
      simp only [cons.injEq, reduceCtorEq, and_false, false_and, exists_const, exists_false]

example: Lang Nat := (tree (fun x => x = 1) (Language.or (tree (fun x => x = 1) Language.emptystr) Language.emptyset))

theorem null_iff_tree {α: Type} {p: α -> Bool} {children: Lang α}:
  Language.null (tree p children) <-> False :=
  Iff.intro nofun nofun

theorem null_tree {α: Type} {p: α -> Bool} {children: Lang α}:
  Language.null (tree p children) = False := by
  rw [null_iff_tree]

theorem derive_iff_tree {α: Type} {p: α -> Bool} {childlang: Lang α} {label: α} {children: Hedge α} {xs: Hedge α}:
  (Language.derive (tree p childlang) (Hedge.Node.mk label children)) xs <->
  (Language.onlyif (p label /\ childlang children) Language.emptystr) xs := by
  simp only [Language.derive, Language.derives, singleton_append]
  simp only [Language.onlyif, Language.emptystr]
  refine Iff.intro ?toFun ?invFun
  case toFun =>
    unfold tree
    simp only [cons.injEq, Hedge.Node.mk.injEq]
    intro ⟨ label', children', ⟨ ⟨ hlabel', hchildren' ⟩, hxs ⟩ , hif ⟩
    subst_vars
    simp only [and_true]
    exact hif
  case invFun =>
    intro ⟨ hif , hxs  ⟩
    unfold tree
    exists label
    exists children
    rw [hxs]
    simp only [true_and]
    exact hif

-- Hedge.Language.derive (Hedge.Language.tree p.eval (Denote.denote children)) a
theorem derive_tree {α: Type} {p: α -> Bool} {childlang: Lang α} {label: α} {children: Hedge α}:
  (Language.derive (tree p childlang) (Hedge.Node.mk label children)) =
  (Language.onlyif (p label /\ childlang children) Language.emptystr) := by
  funext
  rw [derive_iff_tree]
