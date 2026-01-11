import Validator.Std.Vec

inductive IfExpr (σ: Type) (l: Nat) where
  | res (bools: Vector Bool l): IfExpr σ l
  | expr (s: σ) (thn: IfExpr σ l) (els: IfExpr σ l)

def IfExpr.cast (x: IfExpr σ l) (h: l = k): IfExpr σ k := by
  cases h
  exact x

def IfExpr.eval (x: IfExpr σ l) (Φ: σ -> Bool): Vector Bool l :=
  match x with
  | res bools => bools
  | expr s thn els =>
    if Φ s
    then thn.eval Φ
    else els.eval Φ

def IfExpr.mkAcc (xs: Vector σ k) (acc: Vector Bool l): IfExpr σ (l + k) :=
  match k with
  | 0 =>
    IfExpr.res (Vector.cast (by omega) acc)
  | k + 1 =>
    let xs': Vector σ k := Vector.cast (by omega) (Vector.tail xs)
    let pos: Vector Bool (l + 1) := (Vector.push acc true)
    let neg: Vector Bool (l + 1) := (Vector.push acc false)
    let posexpr: IfExpr σ ((l + 1) + k) := IfExpr.mkAcc xs' pos
    let negexpr: IfExpr σ ((l + 1) + k) := IfExpr.mkAcc xs' neg
    IfExpr.expr (Vector.head xs)
      (IfExpr.cast posexpr (by omega))
      (IfExpr.cast negexpr (by omega))

def IfExpr.mk (xs: Vector σ n): IfExpr σ n :=
  IfExpr.cast (IfExpr.mkAcc xs #v[]) (by omega)

theorem IfExpr.lift_mkAcc_cast2 (xs: Vector σ j) (acc: Vector Bool k) (h: k = l) (hlift: k + j = l + j):
  (mkAcc xs (Vector.cast h acc)) = IfExpr.cast (mkAcc xs acc) hlift :=
  sorry

theorem IfExpr.lift_cast_eval (x: IfExpr σ k) (h: k = l):
  (x.cast h).eval Φ = Vector.cast h (x.eval Φ) :=
  sorry

theorem Vector.append_zero_list (xs: Vector σ 0) (ys: Vector σ k):
  (xs ++ ys).toList = ys.toList := by
  sorry

theorem Vector.append_zero (xs: Vector σ 0) (ys: Vector σ k):
  (xs ++ ys) = (Vector.cast (by omega) ys) := by
  apply Vector.eq
  rw [Vector.append_zero_list]
  rw [Vector.cast_toList]

def IfExpr.mkAcc_eval_append_list (xs: Vector σ k) (acc1: Vector Bool l1) (acc2: Vector Bool l2):
  ((IfExpr.mkAcc xs (acc1 ++ acc2)).eval Φ).toList = (acc1 ++ (IfExpr.mkAcc xs acc2).eval Φ).toList := by
  induction l1 with
  | zero =>
    rw [Vector.append_zero_list]
    rw [Vector.append_zero]
    rw [IfExpr.lift_mkAcc_cast2]
    rw [IfExpr.lift_cast_eval]
    rw [Vector.cast_toList]
    omega
  | succ l1 ih =>

    sorry

theorem Vector.tail_cons (x: α) (xs: List α) (hxs : (Array.mk (x :: xs)).size = n + 1):
  (Vector.mk { toList := x :: xs } hxs).tail = Vector.mk { toList := xs } (by simp_all) := by
  sorry

theorem IfExpr.eval_is_map_list (xs: Vector σ n):
  ((IfExpr.mk xs).eval Φ).toList = (Vector.map Φ xs).toList := by
  simp only [Vector.toList_map]
  induction n with
  | zero =>
    simp [IfExpr.mk, IfExpr.mkAcc, IfExpr.eval]
    sorry
  | succ n ih =>

    obtain ⟨⟨xs⟩, hxs⟩ := xs
    cases xs with
    | nil =>
      simp at hxs
    | cons x xs =>
      have ih := ih (Vector.mk (Array.mk xs) (by simp_all))
      simp at ih
      simp only [Vector.toList_mk, List.map_cons]
      rw [<- ih]
      simp only [IfExpr.mk, IfExpr.mkAcc]
      rw [show (Vector.mk { toList := x :: xs } hxs).head = x from rfl]
      rw [Vector.tail_cons]
      simp only [Vector.push, Array.push, List.concat]



      rw??



      sorry




theorem IfExpr.eval_is_map:
  (IfExpr.mk xs).eval Φ = Vector.map Φ xs := by
  apply Vector.eq
  rw [IfExpr.eval_is_map_list]
