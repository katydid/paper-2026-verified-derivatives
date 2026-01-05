import Validator.Std.Vec

import Validator.Regex.Enter
import Validator.Regex.Drawer
import Validator.Regex.Language
import Validator.Regex.Leave
import Validator.Regex.Num
import Validator.Regex.Regex

-- room, since we enter and leave
-- Also this a power in One Piece, which seems appropriate: https://onepiece.fandom.com/wiki/Ope_Ope_no_Mi
def Regex.Room.derive (Φ: σ → Bool) (r: Regex σ): Regex σ :=
  enter r |> Vector.map Φ |> leave r

namespace Regex.Room

def derive_pretty {σ: Type} (Φ: σ → Bool) (r: Regex σ): Regex σ :=
  leave r (Vector.map Φ (enter r))

def derive_distrib {σ: Type}
  (ps: {n: Nat} → Vector σ n → Vector Bool n) (r: Regex σ): Regex σ :=
  let pred_results: Vector Bool (symbols r) := ps (enter r)
  leave r pred_results

def derive_unapplied {σ: Type} {α: Type} (Φ: σ → α → Bool) (r: Regex σ) (a: α): Regex σ :=
  let pred_results: Vector Bool (symbols r) := Vector.map (flip Φ a) (enter r)
  leave r pred_results

lemma derive_unfolds_to_map (Φ: σ → α → Bool) (r: Regex σ) (a: α):
  Room.derive (flip Φ a) r = Point.derive
    (replace (extract r).1 (Vector.map (fun s => (s, Φ s a)) (extract r).2)) := by
  simp only [Room.derive, enter, leave, <- Vector.map_zip_is_zip_map, flip]

end Regex.Room

lemma Regex.Room.derive_is_Regex_derive (Φ: σ → α → Bool) (r: Regex σ) (a: α):
  Regex.Room.derive (flip Φ a) r = Regex.derive Φ r a := by
  simp only [Room.derive, enter, leave, <- Vector.map_zip_is_zip_map, flip]
  rw [<- Regex.extract_replace_is_map]
  rw [Regex.Point.regex_derive_is_point_derive]

namespace Regex.Room

theorem derive_emptyset {α: Type} {σ: Type} (Φ: σ → α → Bool) (a: α):
  Room.derive (flip Φ a) emptyset = emptyset := by
  repeat rw [Regex.Room.derive_is_Regex_derive]
  rw [Regex.derive_emptyset]

theorem derive_emptystr {α: Type} {σ: Type} (Φ: σ → α → Bool) (a: α):
  Room.derive (flip Φ a) emptystr = emptyset := by
  repeat rw [Regex.Room.derive_is_Regex_derive]
  rw [Regex.derive_emptystr]

theorem derive_symbol {α: Type} {σ: Type} (Φ: σ → α → Bool) (s: σ) (a: α):
  Room.derive (flip Φ a) (symbol s) = onlyif (Φ s a) emptystr := by
  repeat rw [Regex.Room.derive_is_Regex_derive]
  rw [Regex.derive_symbol]

theorem derive_or {α: Type} {σ: Type} (Φ: σ → α → Bool) (r1 r2: Regex σ) (a: α):
  Room.derive (flip Φ a) (or r1 r2) = or (Room.derive (flip Φ a) r1) (Room.derive (flip Φ a) r2) := by
  repeat rw [Regex.Room.derive_is_Regex_derive]
  rw [Regex.derive_or]

theorem derive_concat {α: Type} {σ: Type} (Φ: σ → α → Bool) (r1 r2: Regex σ) (a: α):
  Room.derive (flip Φ a) (concat r1 r2)
    = or
      (concat (Room.derive (flip Φ a) r1) r2)
      (onlyif (null r1) (Room.derive (flip Φ a) r2)) := by
  repeat rw [Regex.Room.derive_is_Regex_derive]
  rw [Regex.derive_concat]

theorem derive_star {α: Type} {σ: Type} (Φ: σ → α → Bool) (r1: Regex σ) (a: α):
  Room.derive (flip Φ a) (star r1) = concat (Room.derive (flip Φ a) r1) (star r1) := by
  repeat rw [Regex.Room.derive_is_Regex_derive]
  rw [Regex.derive_star]

theorem derive_commutesb {σ: Type} {α: Type} (Φ: σ → α → Bool) (r: Regex σ) (a: α):
  Regex.denote (fun s a => Φ s a) (Room.derive (flip Φ a) r)
  = Lang.derive (Regex.denote (fun s a => Φ s a) r) a := by
  rw [Regex.Room.derive_is_Regex_derive]
  rw [<- Regex.derive_commutesb]
