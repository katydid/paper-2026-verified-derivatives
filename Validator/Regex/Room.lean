import Validator.Std.Vec

import Validator.Regex.Enter
import Validator.Regex.Drawer
import Validator.Regex.Language
import Validator.Regex.Leave
import Validator.Regex.Num
import Validator.Regex.Regex

-- room, since we enter and leave
-- Also this a power in One Piece, which seems appropriate: https://onepiece.fandom.com/wiki/Ope_Ope_no_Mi
def Regex.Room.derive (Φ: σ -> Bool) (r: Regex σ): Regex σ :=
  leave r (Vec.map (enter r) Φ)

namespace Regex.Room

def derive_pretty {σ: Type} (Φ: σ -> Bool) (r: Regex σ): Regex σ :=
  leave r (Vec.map (enter r) Φ)

def derive_distrib {σ: Type}
  (ps: {n: Nat} -> Vector σ n -> Vector Bool n) (r: Regex σ): Regex σ :=
  let symbols: Vector σ (Symbol.num r) := enter r
  let pred_results: Vector Bool (Symbol.num r) := ps symbols
  leave r pred_results

def derive_unapplied {σ: Type} {α: Type} (Φ: σ -> α -> Bool) (r: Regex σ) (a: α): Regex σ :=
  let symbols: Vector σ (Symbol.num r) := enter r
  let pred_results: Vector Bool (Symbol.num r) := Vec.map symbols (flip Φ a)
  leave r pred_results

theorem derive_is_Regex_derive (Φ: σ -> α -> Bool) (r: Regex σ) (a: α):
  Room.derive (flip Φ a) r = Regex.derive Φ r a := by
  simp only [Room.derive, enter, leave, <- Vec.zip_map, flip]
  rw [<- Symbol.extractFrom_replaceFrom_is_fmap]
  rw [Regex.Point.derive_is_point_derive]

theorem derive_emptyset {α: Type} {σ: Type} (Φ: σ -> α -> Bool) (a: α):
  Room.derive (flip Φ a) emptyset = emptyset := by
  repeat rw [derive_is_Regex_derive]
  rw [Regex.derive_emptyset]

theorem derive_emptystr {α: Type} {σ: Type} (Φ: σ -> α -> Bool) (a: α):
  Room.derive (flip Φ a) emptystr = emptyset := by
  repeat rw [derive_is_Regex_derive]
  rw [Regex.derive_emptystr]

theorem derive_symbol {α: Type} {σ: Type} (Φ: σ -> α -> Bool) (s: σ) (a: α):
  Room.derive (flip Φ a) (symbol s) = onlyif (Φ s a) emptystr := by
  repeat rw [derive_is_Regex_derive]
  rw [Regex.derive_symbol]

theorem derive_or {α: Type} {σ: Type} (Φ: σ -> α -> Bool) (r1 r2: Regex σ) (a: α):
  Room.derive (flip Φ a) (or r1 r2) = or (Room.derive (flip Φ a) r1) (Room.derive (flip Φ a) r2) := by
  repeat rw [derive_is_Regex_derive]
  rw [Regex.derive_or]

theorem derive_concat {α: Type} {σ: Type} (Φ: σ -> α -> Bool) (r1 r2: Regex σ) (a: α):
  Room.derive (flip Φ a) (concat r1 r2)
    = or
      (concat (Room.derive (flip Φ a) r1) r2)
      (onlyif (null r1) (Room.derive (flip Φ a) r2)) := by
  repeat rw [derive_is_Regex_derive]
  rw [Regex.derive_concat]

theorem derive_star {α: Type} {σ: Type} (Φ: σ -> α -> Bool) (r1: Regex σ) (a: α):
  Room.derive (flip Φ a) (star r1) = concat (Room.derive (flip Φ a) r1) (star r1) := by
  repeat rw [derive_is_Regex_derive]
  rw [Regex.derive_star]

theorem derive_commutesb {σ: Type} {α: Type} (Φ: σ -> α -> Bool) (r: Regex σ) (a: α):
  Regex.denote (fun s a => Φ s a) (Room.derive (flip Φ a) r)
  = Language.derive (Regex.denote (fun s a => Φ s a) r) a := by
  rw [derive_is_Regex_derive]
  rw [<- Regex.derive_commutesb]
