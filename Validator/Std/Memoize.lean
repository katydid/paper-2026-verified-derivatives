import Std

import Mathlib.Tactic.Linarith

abbrev MemTable {α: Type} {β: α → Type} [DecidableEq α] [Hashable α] (f: (a: α) → β a) :=
  Std.ExtDHashMap
    α
    (fun a =>
      { b: β a // b = f a }
    )

def MemTable.init {α: Type} {β: α -> Type} [DecidableEq α] [Hashable α]
  (f: (a: α) → β a): MemTable f := Std.ExtDHashMap.emptyWithCapacity

def callM
  {α: Type} {β: α -> Type}
  [DecidableEq α] [Hashable α] (f: (a: α) -> β a)
  [Monad m] [MonadState (MemTable f) m]
  (a: α): m { b: β a // b = f a } := do
  let table <- MonadState.get
  match Std.ExtDHashMap.get? table a with
  | Option.none =>
    let b: { b: β a // b = f a } := Subtype.mk (f a) rfl
    MonadState.set (Std.ExtDHashMap.insert table a b)
    return b
  | Option.some b => return b

@[always_inline, inline, expose]
def StateM.run {σ : Type u} {α : Type u} (x : StateM σ α) (s : σ) : α × σ :=
  x s

@[always_inline, inline, expose]
def StateM.run' {σ : Type u} {α : Type u} (x : StateM σ α) (s : σ) : α :=
  (·.1) <$> x s

def call
  {α: Type} {β: α -> Type}
  [DecidableEq α] [Hashable α] (f: (a: α) -> β a) (a: α) (table: MemTable f): ({b: β a // b = f a} × MemTable f) :=
  StateM.run (s := table) (callM f a)

theorem call_is_correct {α: Type} {β: Type}
  [DecidableEq α] [Hashable α] (f: α -> β)
  (table: MemTable f) (a: α):
  (call f a table).fst.val = f a := by
  generalize ((call f a table).fst) = x
  obtain ⟨x, hx⟩ := x
  simp only
  assumption

class Memoize (m: Type -> Type u) {α: Type} {β: α -> Type} [DecidableEq α] [Hashable α] (f: (a: α) → β a) where
  call : (a: α) -> m { b: β a // b = f a }

-- Example

private def fib (n: Nat): Nat :=
  match n with
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

private def fibM' [Monad m] [MonadState (MemTable fib) m] (n: Nat): m { res: Nat // res = fib n } := do
  match n with
  | 0 => callM fib 0
  | 1 => callM fib 1
  | n + 2 =>
    let table <- MonadState.get
    match Std.ExtDHashMap.get? table (n + 2) with
    | Option.none =>
      let fn <- fibM' n
      let fn1 <- fibM' (n + 1)
      let b: { res: Nat // res = fib (n + 2) } := Subtype.mk (fn + fn1) (by
        obtain ⟨fn, hfn⟩ := fn
        obtain ⟨fn1, hfn1⟩ := fn1
        simp only
        unfold fib
        subst_vars
        rfl
      )
      MonadState.set (Std.ExtDHashMap.insert table (n + 2) b)
      return b
    | Option.some b => return b

private def fibM (n: Nat): Nat :=
  (StateM.run (s := MemTable.init fib) (fibM' n)).1

private theorem fibM_is_correct (n: Nat): fib n = (StateM.run (s := table) (fibM' n)).1 := by
  have h := call_is_correct fib
  unfold call at h
  fun_induction fibM' generalizing table
  case case1 => -- 0
    rw [h]
  case case2 => -- 1
    rw [h]
  case case3 n ih1 ih2 => -- n + 2
    simp only [StateM.run]
    sorry
