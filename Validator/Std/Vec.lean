import Init.Data.Nat

import Batteries.Tactic.GeneralizeProofs
import Mathlib.Tactic.NthRewrite
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.RewriteSearch
import Mathlib.Tactic.SimpRw

def Vec.cast {n1 n2 : Nat} (xs: Vector α n1) (h : n1 = n2): Vector α n2 :=
  Vector.cast h xs

def Vector.cast_assoc (xs: Vector σ (n + n1 + n2)): Vector σ (n + (n1 + n2)) :=
  have h : (n + n1 + n2) = n + (n1 + n2) := by
    rw [<- Nat.add_assoc]
  Vec.cast xs h

namespace Vec

def map (xs: Vector α n) (f: α -> β): Vector β n :=
  Vector.map f xs

def zip (xs: Vector α n) (ys: Vector β n): Vector (α × β) n :=
  Vector.zip xs ys

def snoc (xs: Vector α l) (y: α): Vector α (l + 1) :=
  xs.push y

def head (xs: Vector α (Nat.succ l)): α :=
  xs.head

theorem eq (xs ys: Vector α n) (h: Vector.toList xs = Vector.toList ys): xs = ys := by
  obtain ⟨⟨xs⟩, hxs⟩ := xs
  obtain ⟨⟨ys⟩, hxs⟩ := ys
  simp_all

theorem cast_rfl {α: Type u} (xs: Vector α n) (h: n = n):
  cast xs h = xs := by
  rfl

theorem cast_toList_nil {α: Type u} (h: 0 = n):
  (Vec.cast (α := α) #v[] h).toList = [] := by
  cases n with
  | zero =>
    rw [cast_rfl]
    simp
  | succ n =>
    contradiction

theorem cast_toList {n: Nat} (xs: Vector α n) (h: n = n2):
  (cast xs h).toList = xs.toList := by
  subst h
  rw [cast_rfl]

theorem Vector.cast_rfl {α: Type u} (xs: Vector α n) (h: n = n):
  Vector.cast h xs = xs := by
  rfl

theorem Vector.cast_toList {n: Nat} (xs: Vector α n) (h: n = n2):
  (Vector.cast h xs).toList = xs.toList := by
  subst h
  rw [cast_rfl]

theorem take_zero (xs : Vector α n):
  Vector.take xs 0 = Vec.cast #v[] (Eq.symm (Nat.zero_min n)) := by
  simp only [Vector.take, Vec.cast, Vector.take]
  simp

theorem Vector.take_zero (xs : Vector α n):
  Vector.take xs 0 = #v[] := by
  simp only [Vector.take]
  simp

theorem Vector.drop_zero (xs : Vector α n):
  Vector.drop xs 0 = xs := by
  simp only [Vector.drop]
  simp

theorem drop_zero (xs : Vector α n):
  Vector.drop xs 0 = Vec.cast xs (by omega) := by
  simp only [Vector.drop]
  simp only [cast_rfl]
  simp

theorem take_nil (i: Nat):
  Vector.take #v[] i  = Vec.cast (α := α) #v[] (Eq.symm (Nat.min_zero i)) := by
  induction i with
  | zero =>
    rw [take_zero]
  | succ i ih =>
    congr

theorem drop_nil (i: Nat):
  Vector.drop #v[] i = Vec.cast (α := α) #v[] (by omega) := by
  cases i with
  | zero =>
    rw [drop_zero]
  | succ i =>
    simp only [Vector.drop]
    simp

theorem toList_take {xs: Vector α n}:
  List.take i xs.toList = (Vector.take xs i).toList := by
  rw [Vector.toList_take]

theorem map_nil {f: α -> β}:
  Vec.map #v[] f = #v[] := by
  simp only [Vec.map]
  simp

theorem toList_map (xs: Vector α n) (f: α -> β):
  (Vec.map xs f).toList = (List.map f xs.toList) := by
  unfold Vec.map
  rw [@Vector.toList_map]

def List.snoc (xs: List α) (x: α) :=
  xs ++ [x]

def toList_append:
  (Vector.append xs ys).toList = List.append (xs.toList) (ys.toList) := by
  simp
  rw [<- show xs ++ ys = xs.append ys from rfl]
  rw [Vector.toList_append]

theorem toList_snoc {xs : Vector α n} :
  (Vec.snoc xs x).toList = List.snoc xs.toList x := by
  simp [snoc, List.snoc, Vector.push]
  rfl

def cons (x: α) (xs: Vector α n): Vector α (n + 1) :=
  Vec.cast (Vector.append #v[x] xs) (by omega)

theorem singleton_toList:
  [x] = #v[x].toList := by
  simp

theorem cons_cast {α: Type u} {l n: Nat} (x: α) (xs: Vector α l) (h: l = n):
  (Vec.cons x (Vec.cast xs h)) = Vec.cast (Vec.cons x xs) (by omega) := by
  subst h
  rfl

theorem Vector.cast_cast (xs: Vector α n) (h1: n = k) (h2: k = l):
  (Vector.cast h2 (Vector.cast h1 xs)) = Vector.cast (by subst h1 h2; simp only) xs := by
  simp

theorem cast_cast (xs: Vector α n) (h1: n = k) (h2: k = l):
  (Vec.cast (Vec.cast xs h1) h2) = Vec.cast xs (by subst h1 h2; simp only):= by
  simp only [cast]
  rw [Vector.cast_cast]

theorem toList_cons {xs : Vector α n} :
  (Vec.cons x xs).toList = List.cons x xs.toList := by
  rw [← List.singleton_append]
  simp only [Vec.cons]
  nth_rw 2 [singleton_toList]
  rw [← Vector.toList_append]
  rw [<- show #v[x] ++ xs = #v[x].append xs from rfl]
  rw [cast_toList]

theorem append_nil (xs: Vector α n):
  Vector.append xs #v[] = Vec.cast xs (Eq.symm (Nat.add_zero n)) := by
  apply eq
  rw [toList_append]
  simp
  rfl

theorem cons_append_list (xs: Vector α n1) (ys: Vector α n2):
  (Vec.cons x (Vector.append xs ys)).toList = (Vector.append (Vec.cons x xs) ys).toList := by
  rw [toList_cons]
  rw [toList_append]
  rw [toList_append]
  rw [toList_cons]
  simp

theorem cons_append (xs: Vector α n1) (ys: Vector α n2):
  Vec.cons x (Vector.append xs ys) = Vec.cast (Vector.append (Vec.cons x xs) ys) (by omega) := by
  apply eq
  rw [cons_append_list]
  rw [cast_toList]

theorem Vector.nil_append (xs: Vector α n):
  Vector.append #v[] xs = Vec.cast xs (Eq.symm (Nat.zero_add n)) := by
  simp [Vector.append, Vec.cast]

theorem cast_append (xs: Vector α n1) (ys: Vector α n2):
  Vector.append (Vec.cast xs h1) ys = Vec.cast (Vector.append xs ys) h2 := by
  subst h1
  rw [cast_rfl]
  rw [cast_rfl]

theorem append_cons_list (xs: Vector α n1) (ys: Vector α n2):
  (Vector.append (Vec.cons x xs) ys).toList = (Vec.cons x (Vector.append xs ys)).toList := by
  rw [cons_append_list]

theorem append_cons (xs: Vector α n1) (ys: Vector α n2):
  Vector.append (Vec.cons x xs) ys = Vec.cast (Vec.cons x (Vector.append xs ys)) (by omega) := by
  apply eq
  rw [append_cons_list]
  rw [cast_toList]

theorem append_cast_r {h: n2 = n3} (xs: Vector α n1) (ys: Vector α n2):
  Vector.append xs (Vec.cast ys h) = Vec.cast (Vector.append xs ys) (by subst h; rfl) := by
  subst h
  rw [cast_rfl]
  rw [cast_rfl]

theorem take_append_drop_list (i : Nat) (xs : Vector α l): (Vector.append (xs.take i) (xs.drop i)).toList = xs.toList := by
  induction i generalizing xs l with
  | zero =>
    simp only [Vector.take_zero]
    simp only [Vector.drop_zero]
    rw [Vector.nil_append]
    rw [cast_toList]
  | succ i ih =>
    rw [toList_append]
    rw [Vector.toList_take]
    rw [Vector.toList_drop]
    simp

theorem take_append_drop (i : Nat) (xs : Vector α l): (Vector.append (xs.take i) (xs.drop i)) = (Vector.cast (by omega) xs) := by
  apply eq
  rw [take_append_drop_list]
  rw [Vector.cast_toList]

theorem take_append_drop_cast (i : Nat) (xs : Vector α l): Vec.cast (Vector.append (xs.take i) (xs.drop i)) (by omega) = xs := by
  rw [take_append_drop]
  unfold Vec.cast
  simp

theorem get_cast (xs: Vector α n) (h: n = m):
  Vector.get (Vec.cast xs h) i = Vector.get xs ⟨i.val, by omega⟩ := by
  subst h
  simp_all only [Fin.eta]
  rfl

theorem get_is_getElem {n: Nat} {α: Type u} (xs: Vector α n) (hi: i < n):
  Vector.get xs (Fin.mk i hi) = xs[i] := by
  aesop

theorem append_getElem (xs: Vector α n) (ys: Vector α m) (h: i < n):
  (Vector.append xs ys)[i] = xs[i] := by
  rw [<- show xs ++ ys = xs.append ys from rfl]
  rw [Vector.getElem_append_left]

theorem append_get (xs: Vector α n) (ys: Vector α m) (h: i < n):
  Vector.get (Vector.append xs ys) ⟨i, by omega⟩ = Vector.get xs ⟨i, h⟩ := by
  rw [get_is_getElem]
  rw [get_is_getElem]
  rw [append_getElem]

theorem take_get (xs: Vector α (n + m)) (h1: i < n):
  Vector.get (Vector.take xs n) ⟨i, (by omega)⟩ = Vector.get xs ⟨i, h⟩ := by
  have h := take_append_drop_cast (xs := xs) (i := n)
  nth_rewrite 2 [<- h]
  rw [Vec.get_cast]
  simp only
  rw [append_get]

theorem cons_snoc:
  (Vec.snoc (cons x xs) y) = cons x (Vec.snoc xs y) := by
  apply eq
  rw [toList_snoc]
  rw [toList_cons]
  rw [toList_cons]
  rw [toList_snoc]
  simp only [List.snoc]
  ac_rfl

theorem snoc_append (xs: Vector α l):
  (Vec.snoc xs y) = (xs.append #v[y]) := by
  unfold Vec.snoc
  rfl

theorem snoc_getElem {n: Nat} {α: Type u} (xs: Vector α n) (y: α):
  (Vec.snoc xs y)[n] = y := by
  simp only [Vec.snoc]
  simp_all only [Vector.getElem_push_eq]

theorem snoc_get {n: Nat} {α: Type u} (xs: Vector α n) (y: α):
  Vector.get (Vec.snoc xs y) (Fin.mk n (by omega)) = y := by
  rw [get_is_getElem]
  rw [snoc_getElem]

theorem snoc_map_list (xs: Vector α l) (f: α -> β):
  (Vec.map (Vec.snoc xs x) f).toList
  = (Vec.snoc (Vec.map xs f) (f x)).toList := by
  rw [toList_map (snoc xs x) f]
  rw [toList_snoc]
  rw [toList_snoc]
  rw [toList_map]
  simp only [List.snoc]
  simp

theorem snoc_map (xs: Vector α l) (f: α -> β):
  (Vec.map (Vec.snoc xs x) f)
  = (Vec.snoc (Vec.map xs f) (f x)) := by
  apply eq
  apply snoc_map_list

theorem toList_length (xs : Vector α l):
  xs.toList.length = l := by
  simp

theorem map_toList:
  (Vec.map xs f).toList = List.map f (xs.toList) := by
  simp_all only [Vec.toList_map]

theorem map_cast (xs : Vector α l) (f: α -> β) (h: l = n):
  (Vec.map (Vec.cast xs h) f) = Vec.cast (Vec.map xs f) h := by
  apply eq
  rw [map_toList]
  repeat rw [cast_toList]
  rw [map_toList]

theorem zip_map {α: Type u} {β: Type v} (f: α -> β) (xs: Vector α l):
  (Vec.map xs (fun x => (x, f x))) =
  (Vec.zip xs (Vec.map xs f)) := by
  unfold Vec.map
  unfold Vec.zip
  ext i h : 2
  · simp_all only [Vector.getElem_map, Vector.getElem_zip]
  · simp_all only [Vector.getElem_map, Vector.getElem_zip]
