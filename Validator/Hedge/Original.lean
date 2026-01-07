import Validator.Std.Decidable
import Validator.Std.Except
import Validator.Std.List

import Validator.Std.Hedge

import Validator.Pred.AnyEq
import Validator.Hedge.Denote
import Validator.Hedge.Grammar
import Validator.Regex.Regex

theorem decreasing_or_l {α: Type} {σ: Type} [SizeOf σ] (r1 r2: Regex σ) (x: Hedge.Node α):
  Prod.Lex
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (x, r1)
    (x, Regex.or r1 r2) := by
  apply Prod.Lex.right
  simp +arith only [Regex.or.sizeOf_spec]

theorem decreasing_or_r {α: Type} {σ: Type} [SizeOf σ] (r1 r2: Regex σ) (x: Hedge.Node α):
  Prod.Lex
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (x, r2)
    (x, Regex.or r1 r2) := by
  apply Prod.Lex.right
  simp +arith only [Regex.or.sizeOf_spec]

theorem decreasing_concat_l {α: Type} {σ: Type} [SizeOf σ] (r1 r2: Regex σ) (x: Hedge.Node α):
  Prod.Lex
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (x, r1)
    (x, Regex.concat r1 r2) := by
  apply Prod.Lex.right
  simp +arith only [Regex.concat.sizeOf_spec]

theorem decreasing_concat_r {α: Type} {σ: Type} [SizeOf σ] (r1 r2: Regex σ) (x: Hedge.Node α):
  Prod.Lex
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (x, r2)
    (x, Regex.concat r1 r2) := by
  apply Prod.Lex.right
  simp +arith only [Regex.concat.sizeOf_spec]

theorem decreasing_star {α: Type} {σ: Type} [SizeOf σ] (r: Regex σ) (x: Hedge.Node α):
  Prod.Lex
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (x, r)
    (x, Regex.star r) := by
  apply Prod.Lex.right
  simp +arith only [Regex.star.sizeOf_spec]

theorem decreasing_symbol {α: Type} {σ: Type} [SizeOf σ] (r1 r2: Regex σ) (label: α) (children: Hedge α) (x: Hedge.Node α) (h: x ∈ children):
  Prod.Lex
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (x, r1)
    (Hedge.Node.mk label children, r2) := by
  apply Prod.Lex.left
  simp +arith only [Hedge.Node.mk.sizeOf_spec]
  have h' := List.list_elem_lt h
  omega

def Original.Rule.derive (G: Hedge.Grammar n φ) (Φ: φ → α → Bool)
  (r: Regex (φ × Ref n)) (node: Hedge.Node α): Regex (φ × Ref n) :=
  match r with
  | Regex.emptyset => Regex.emptyset
  | Regex.emptystr => Regex.emptyset
  | Regex.symbol (pred, ref) =>
    let ⟨label, children⟩ := node
    Regex.onlyif (Φ pred label
      /\ Regex.null (List.foldl (derive G Φ) (G.lookup ref) children)
    ) Regex.emptystr
  | Regex.or r1 r2 =>
    Regex.or (derive G Φ r1 node) (derive G Φ r2 node)
  | Regex.concat r1 r2 =>
    Regex.or
      (Regex.concat (derive G Φ r1 node) r2)
      (Regex.onlyif (Regex.null r1) (derive G Φ r2 node))
  | Regex.star r1 =>
    Regex.concat (derive G Φ r1 node) (Regex.star r1)
  -- Lean cannot guess how the recursive function terminates,
  -- so we have to tell it how the arguments decrease in size.
  -- The arguments decrease in the tree case first
  -- (which only happens in the Regex.symbol case)
  -- and in the expression, r, second (which is all other cases).
  -- This means if the tree is not destructed, then the expression is destructed.
  termination_by (node, r)
  -- Once we tell Lean how the function terminates we have to prove that
  -- the size of the arguments decrease on every call.
  -- Prod.Lex.left represents the case where the tree argument decreases.
  -- Prod.Lex.right represents the case where the tree argument does not decrease
  -- and the expression r does decrease.
  decreasing_by
    · apply decreasing_symbol (h := by assumption)
    · apply decreasing_symbol (h := by assumption)
    · apply decreasing_symbol (h := by assumption)
    · apply decreasing_or_l
    · apply decreasing_or_r
    · apply decreasing_concat_l
    · apply decreasing_concat_r
    · apply decreasing_star

def validate
  (G: Hedge.Grammar n φ) (Φ: φ → α → Bool)
  (r: Regex (φ × Ref n)) (hedge: Hedge α): Bool :=
  Regex.null (List.foldl (Original.Rule.derive G Φ) r hedge)

def run [DecidableEq α] (G: Hedge.Grammar n (AnyEq.Pred α)) (nodes: Hedge α): Bool :=
  validate G AnyEq.Pred.evalb G.start nodes

-- Tests

abbrev node {α} (label: α) children := Hedge.Node.mk label children

#guard run
  (Hedge.Grammar.singleton Regex.emptyset)
  [node "a" [node "b" [], node "c" [node "d" []]]] =
  false

#guard run
  (Hedge.Grammar.mk (n := 1)
    (Regex.symbol (AnyEq.Pred.eq "a", 0))
    #v[Regex.emptystr]
  )
  [node "a" []] =
  true

#guard run
  (Hedge.Grammar.mk (n := 1)
    (Regex.symbol (AnyEq.Pred.eq "a", 0))
    #v[Regex.emptystr]
  )
  [node "a" [node "b" []]] =
  false

#guard run
  (Hedge.Grammar.mk (n := 2)
    (Regex.symbol (AnyEq.Pred.eq "a", 0))
    #v[
      (Regex.symbol (AnyEq.Pred.eq "b", 1))
      , Regex.emptystr
    ]
  )
  [node "a" [node "b" []]]
  = true

#guard run
  (Hedge.Grammar.mk (n := 2)
    (Regex.symbol (AnyEq.Pred.eq "a", 0))
    #v[
      (Regex.concat
        (Regex.symbol (AnyEq.Pred.eq "b", 1))
        (Regex.symbol (AnyEq.Pred.eq "c", 1))
      )
      , Regex.emptystr
    ]
  )
  [node "a" [node "b" [], node "c" []]] =
  true

#guard run
  (Hedge.Grammar.mk (n := 3)
    (Regex.symbol (AnyEq.Pred.eq "a", 0))
    #v[
      (Regex.concat
        (Regex.symbol (AnyEq.Pred.eq "b", 1))
        (Regex.symbol (AnyEq.Pred.eq "c", 2))
      )
      , Regex.emptystr
      , (Regex.symbol (AnyEq.Pred.eq ("d"), 1))
    ]
  )
  [node "a" [node "b" [], node "c" [node "d" []]]] =
  true

-- modified example from https://books.xmlschemata.org/relaxng/relax-CHP-5-SECT-4.html

private def example_grammar_library: Hedge.Grammar 5 (Option String) :=
  Hedge.Grammar.mk
    (start := Regex.symbol (some "library", 0))
    (prods := #v[
      Regex.oneOrMore (Regex.symbol (some "book", 1)),
      Regex.concat
        (Regex.symbol (some "isbn", 3))
        (Regex.concat
          (Regex.symbol (some "title", 3))
          (Regex.oneOrMore (Regex.symbol (some "author", 2)))
        ),
      Regex.concat
        (Regex.symbol (some "name", 3))
        (Regex.optional (Regex.symbol (some "born", 3))),
      Regex.symbol (Option.none, 4),
      Regex.emptystr
    ])

#guard validate
  example_grammar_library
  (fun s a =>
    match s with
    | Option.none => true
    | Option.some s' => s' == a
  )
  example_grammar_library.start
  [node "library"
    [node "book" [
      (node "isbn" [node "123" []]),
      (node "title" [node "numbers" []]),
      (node "author" [node "name" [node "Brink" []]]),
      (node "author" [node "name" [node "Paul" []], node "born" [node "July" []]])
    ]]
  ]
  = true

-- no authors fails
#guard validate
  example_grammar_library
  (fun s a =>
    match s with
    | Option.none => true
    | Option.some s' => s' == a
  )
  example_grammar_library.start
  [node "library"
    [node "book" [
      (node "isbn" [node "456" []]),
      (node "title" [node "numbers" []])
    ]]
  ]
  = false

-- modified example from Taxonomy of XML Section 6.5

private def example_grammar_doc: Hedge.Grammar 3 String :=
  Hedge.Grammar.mk
    (start := Regex.symbol ("doc", 0))
    (prods := #v[
      Regex.oneOrMore (Regex.symbol ("para", 1)),
      Regex.symbol ("pcdata", 2),
      Regex.emptystr,
    ])

#guard validate example_grammar_doc (· == ·) example_grammar_doc.start
  [node "doc" [node "para" [node "pcdata" []]]]
  = true

#guard validate example_grammar_doc (· == ·) example_grammar_doc.start
  [node "doc" [node "para" []]]
  = false

#guard validate example_grammar_doc (· == ·) example_grammar_doc.start
  [node "doc" [node "para" [node "pcdata" []], node "para" [node "pcdata" []]]]
  = true

#guard validate example_grammar_doc (· == ·) example_grammar_doc.start
  [node "doc" [node "para" [node "pcdata" []], node "para" [node "pcdata" []], node "para" [node "pcdata" []]]]
  = true

-- modified example from Taxonomy of XML Section 7.1
private def example_grammar_sec: Hedge.Grammar 2 String :=
  Hedge.Grammar.mk
    (start := Regex.oneOrMore (Regex.symbol ("sec", 0)))
    (prods := #v[
      Regex.oneOrMore (Regex.or
        (Regex.symbol ("sec", 0))
        (Regex.symbol ("p", 1))
      ),
      Regex.emptystr
    ])

#guard validate example_grammar_sec (· == ·) example_grammar_sec.start
  [node "sec" [node "p" []]]
  = true

#guard validate example_grammar_sec (· == ·) example_grammar_sec.start
  [node "sec" [node "p" []], node "sec" [node "sec" [node "p" []], node "sec" [node "p" []], node "sec" [node "p" []]]]
  = true

#guard validate example_grammar_sec (· == ·) example_grammar_sec.start
  [node "sec" []]
  = false

#guard validate example_grammar_sec (· == ·) example_grammar_sec.start
  [node "p" []]
  = false

theorem Original.derive_commutes {α: Type} {φ: Type}
  (G: Hedge.Grammar n φ) (Φ: φ → α → Prop) [DecidableRel Φ]
  (r: Regex (φ × Ref n)) (x: Hedge.Node α):
  Hedge.Grammar.Rule.denote G Φ (Original.Rule.derive G (decideRel Φ) r x)
  = Lang.derive (Hedge.Grammar.Rule.denote G Φ r) x := by
  fun_induction (Rule.derive G (fun p a => Φ p a)) r x with
  | case1 => -- emptyset
    rw [Hedge.Grammar.denote_emptyset]
    rw [Lang.derive_emptyset]
  | case2 => -- emptystr
    rw [Hedge.Grammar.denote_emptyset]
    rw [Hedge.Grammar.denote_emptystr]
    rw [Lang.derive_emptystr]
  | case3 p childRef label children ih =>
    rw [Hedge.Grammar.denote_symbol]
    rw [Lang.derive_tree]
    rw [Hedge.Grammar.denote_onlyif]
    rw [Hedge.Grammar.denote_emptystr]
    apply (congrArg fun x => Lang.onlyif x Lang.emptystr)
    congr
    generalize (G.lookup childRef) = childExpr
    rw [Hedge.Grammar.null_commutes (Φ := Φ)]
    unfold Lang.null
    induction children generalizing childExpr with
    | nil =>
      simp only [List.foldl_nil]
      rfl
    | cons c cs ih' =>
      simp only [List.foldl]
      rw [ih']
      · cases c
        rw [ih]
        simp only [Lang.derive]
        rw [List.mem_cons]
        apply Or.inl
        rfl
      · intro x child hchild
        apply ih
        rw [List.mem_cons]
        apply Or.inr hchild
  | case4 x p q ihp ihq => -- or
    rw [Hedge.Grammar.denote_or]
    rw [Hedge.Grammar.denote_or]
    unfold Lang.or
    rw [ihp]
    rw [ihq]
    rfl
  | case5 x r1 r2 ih1 ih2 => -- concat
    rw [Hedge.Grammar.denote_concat]
    rw [Hedge.Grammar.denote_or]
    rw [Hedge.Grammar.denote_concat]
    rw [Hedge.Grammar.denote_onlyif]
    rw [Lang.derive_concat]
    rw [<- ih1]
    rw [<- ih2]
    congr
    rw [Hedge.Grammar.null_commutes (Φ := Φ)]
  | case6 x r ih => -- star
    rw [Hedge.Grammar.denote_star]
    rw [Hedge.Grammar.denote_concat]
    rw [Hedge.Grammar.denote_star]
    rw [Lang.derive_star]
    rw [ih]
