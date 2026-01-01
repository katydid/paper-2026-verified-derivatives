import Validator.Regex.Regex
import Validator.Regex.Num

namespace Regex.Symbol

abbrev RegexID n := Regex (Fin n)

def RegexID.cast_add {n: Nat} (m: Nat) (r: RegexID n): RegexID (n + m) :=
  Regex.map r (fun s => (Fin.castLE (by omega) s))

def RegexID.cast (r: RegexID n) (h: n = m): RegexID m :=
  match h with
  | Eq.refl _ => r

def RegexID.castLE {n: Nat} (r: RegexID n) (h : n ≤ m): RegexID m :=
  Regex.map r (fun s => (Fin.castLE h s))

def RegexID.cast_map (r: RegexID n) (h: n = m): RegexID m :=
  Regex.map r (fun s => Fin.castLE (by omega) s)

abbrev RegexID.cast_assoc (r: RegexID (n + Symbol.num r1 + Symbol.num r2)): RegexID (n + (Symbol.num r1 + Symbol.num r2)) :=
  have h : (n + Symbol.num r1 + Symbol.num r2) = n + (Symbol.num r1 + Symbol.num r2) := by
    rw [<- Nat.add_assoc]
  RegexID.cast r h

def RegexID.cast_or (r: RegexID (n + Symbol.num r1 + Symbol.num r2)): RegexID (n + Symbol.num (Regex.or r1 r2)) :=
  RegexID.cast_assoc r

def RegexID.cast_concat (r: RegexID (n + Symbol.num r1 + Symbol.num r2)): RegexID (n + Symbol.num (Regex.concat r1 r2)) :=
  RegexID.cast_assoc r

theorem RegexID.cast_rfl (r: RegexID n): RegexID.cast r rfl = r := by
  rfl

theorem RegexID.cast_rfl' (r: RegexID n) (h: n = n): RegexID.cast r h = r := by
  rfl

theorem RegexID.cast_map_rfl (r: RegexID n): RegexID.cast_map r rfl = r := by
  unfold RegexID.cast_map
  simp only [Fin.castLE_refl]
  rw [Regex.map_id]

theorem RegexID.cast_is_cast_map (r: RegexID n) (h: n = m):
  RegexID.cast r h = RegexID.cast_map r h := by
  subst h
  rw [RegexID.cast_rfl]
  rw [RegexID.cast_map_rfl]

theorem RegexID.castLE_id {h: n ≤ n}:
  (RegexID.castLE r h) = r := by
  simp only [RegexID.castLE]
  simp_all only [Fin.castLE_refl]
  simp_all only [le_refl]
  rw [Regex.map_id]

theorem RegexID.cast_add_zero:
  (RegexID.cast_add 0 r) = r := by
  simp only [Nat.add_zero, RegexID.cast_add]
  simp_all only [Fin.castLE_refl]
  simp only [Regex.map_id]

theorem RegexID.cast_add_cast_is_castLE (r: RegexID n) (h: n = m):
  (RegexID.cast_add k (RegexID.cast r h)) = RegexID.castLE r (by omega) := by
  simp only [RegexID.cast_add, RegexID.cast]
  subst h
  simp_all only
  rfl

theorem RegexID.cast_add_is_castLE (r: RegexID n):
  (RegexID.cast_add k r) = RegexID.castLE r (by omega) := by
  simp only [RegexID.cast_add, RegexID.castLE]
