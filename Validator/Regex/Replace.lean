import Validator.Regex.Num
import Validator.Regex.Regex
import Validator.Regex.RegexID

namespace Regex

def Symbol.replace (r: RegexID n) (xs: Vector σ l) (h: n <= l): Regex σ :=
  match r with
  | emptyset => emptyset | emptystr => emptystr
  | symbol ⟨s, hs⟩ => symbol (Vector.get xs (Fin.mk s (by omega)))
  | or r1 r2 => or (replace r1 xs h) (replace r2 xs h)
  | concat r1 r2 => concat (replace r1 xs h) (replace r2 xs h)
  | star r1 => star (replace r1 xs h)

def Symbol.replaceFrom (r: RegexID n) (xs: Vector σ n): Regex σ :=
  replace r xs (Nat.le_refl n)

end Regex

namespace Regex.Symbol

theorem replace_cast_both (r: RegexID n) (xs: Vector σ n) (h: n = l):
  replace r xs (by omega) = replace (RegexID.cast r h) (Vec.cast xs h) (by omega) := by
  subst h
  simp only [Vec.cast_rfl]
  rfl

theorem replace_cast_symbols (r: RegexID n) (xs: Vector σ n) (h: n = l):
  replace r xs (by omega) = replace r (Vec.cast xs h) (by omega) := by
  subst h
  simp only [Vec.cast_rfl]

theorem replace_take (r: RegexID n) (xs: Vector σ (n + l)):
  replace r (Vector.take xs n) (by omega) = replace r xs (by omega):= by
  induction r with
  | emptyset =>
    simp only [replace]
  | emptystr =>
    simp only [replace]
  | symbol s =>
    generalize_proofs h1 h2 at *
    simp only [replace]
    obtain ⟨s, hs⟩ := s
    simp only [Regex.symbol.injEq]
    generalize_proofs h3 h4
    rw [Vec.take_get]
    omega
  | or r1 r2 ih1 ih2 =>
    simp only [replace, Regex.or.injEq]
    generalize_proofs h1 h2 at *
    rw [<- ih1]
    rw [<- ih2]
    apply And.intro rfl rfl
  | concat r1 r2 ih1 ih2 =>
    simp only [replace, Regex.concat.injEq]
    generalize_proofs h1 h2 at *
    rw [<- ih1]
    rw [<- ih2]
    apply And.intro rfl rfl
  | star r1 ih1 =>
    simp only [replace]
    generalize_proofs h1 at *
    rw [<- ih1]

theorem replace_regexid_add (r: RegexID n) (xs: Vector σ (n + l)):
  replace r xs (by omega) = replace (RegexID.cast_add l r) xs (by omega):= by
  generalize_proofs h1 h2
  induction r with
  | emptyset =>
    simp only [replace, RegexID.cast_add, Regex.map]
  | emptystr =>
    simp only [replace, RegexID.cast_add, Regex.map]
  | symbol s =>
    generalize_proofs h1 h2 at *
    simp only [replace, RegexID.cast_add, Regex.map, Fin.coe_castLE]
  | or r1 r2 ih1 ih2 =>
    simp only [replace, RegexID.cast_add, Regex.map, Regex.or.injEq]
    generalize_proofs h1 h2 at *
    rw [ih1]
    rw [ih2]
    apply And.intro rfl rfl
  | concat r1 r2 ih1 ih2 =>
    simp only [replace, RegexID.cast_add, Regex.map, Regex.concat.injEq]
    generalize_proofs h1 h2 at *
    rw [ih1]
    rw [ih2]
    apply And.intro rfl rfl
  | star r1 ih1 =>
    simp only [replace, RegexID.cast_add, Regex.map, Regex.star.injEq]
    generalize_proofs h1 h2 at *
    rw [ih1]
    rfl
