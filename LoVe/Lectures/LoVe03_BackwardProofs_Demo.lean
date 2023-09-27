/- Copyright © 2018–2023 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.Lectures.LoVe01_02_TypesAndTerms_DemoMaster


/- # LoVe Demo 3: Backward Proofs

A __tactic__ operates on a proof goal and either proves it or creates new
subgoals. Tactics are a __backward__ proof mechanism: They start from the goal
and work towards the available hypotheses and theorems. -/


namespace LoVe

namespace BackwardProofs


/- ## Tactic Mode

Syntax of tactical proofs:

    by
      _tactic₁_
      …
      _tacticN

The keyword `by` indicates to Lean the proof is tactical. -/


theorem fst_of_two_props :
  ∀a b : Prop, a → b → a :=
  by
    intro a2 /- Introduces a2 as some proposition, which peels off a layer of the for all statement-/
    intro b2 /- Introduces b2 as another proposition. Now we just need to prove a2 → b2 → a2 -/
    /- intro x  Introduces x (where x is of type a2)-/
    /- intro y  Introduces y where y is of type b2. Doesn't exactly make sense b/c b2 is a proposition.
    Instead, we say that y is a "proof" or hypothesis of b2-/
    intro ha
    intro hb
    apply ha
    done


/- Note that `a → b → a` is parsed as `a → (b → a)`.

Propositions in Lean are terms of type `Prop`. `Prop` is a type, just like `Nat`
and `List Bool`. In fact there is a close correspondence between propositons and
types, which will be explained in lecture 4.


## Basic Tactics

`intro` moves `∀`-quantified variables, or the assumptions of implications `→`,
from the goal's conclusion (after `⊢`) into the goal's hypotheses (before `⊢`).

`apply` matches the goal's conclusion with the conclusion of the specified
theorem and adds the theorem's hypotheses as new goals.

Food for thought: how do these compare to the typing derivation rules for 
lambda and application expressions?

-/


theorem fst_of_two_props_params (a b : Prop) (ha : a) (hb : b) :
  a :=
  by 
    apply ha
    done


theorem prop_comp (a b c : Prop) (hab : a → b) (hbc : b → c) :
  a → c :=
  by
    intro ha
    apply hbc (hab ha)
    -- apply hba
    -- apply ha
    done


/- The above proof step by step:

* Assume we have a proof of `a`.
* The goal is `c`, which we can show if we prove `b` (from `hbc`).
* The goal is `b`, which we can show if we prove `a` (from `hab`).
* We already know `a` (from `ha`).

Next, `exact` matches the goal's conclusion with the specified theorem, closing
the goal. We can often use `apply` in such situations, but `exact` communicates
our intentions better. -/

theorem fst_of_two_props_exact (a b : Prop) (ha : a) (hb : b) :
  a :=
  by exact ha

/- `assumption` finds a hypothesis from the local context that matches the
goal's conclusion and applies it to prove the goal. -/

theorem fst_of_two_props_assumption (a b : Prop)
    (ha : a) (hb : b) :
  a :=
  by assumption


/- ## Reasoning about Logical Connectives and Quantifiers

Introduction rules: -/

-- ∀ x : ℕ, P x ∧ Q x

#check True.intro
#check And.intro
#check Or.inl
#check Or.inr
#check Iff.intro
#check Exists.intro

/- Elimination rules: -/

#check False.elim
#check And.left
#check And.right
#check Or.elim
#check Iff.mp
#check Iff.mpr
#check Exists.elim

/- Definition of `¬` and related theorems: -/

#print Not
#check Classical.em
#check Classical.byContradiction

/- There are no explicit rules for `Not` (`¬`) since `¬ p` is defined as
`p → False`. -/


theorem And_swap (a b : Prop) :
  a ∧ b → b ∧ a :=
  by
    intro hab
    apply And.intro
    apply And.right 
    exact hab
    apply And.left 
    exact hab
    done

theorem And_swap2 (a b : Prop) :
  a ∧ b → b ∧ a :=
  by
    intro hab
    have ha : a
    apply And.left
    exact hab
    have hb : b
    apply And.right
    exact hab
    apply And.intro
    assumption
    assumption
    done

theorem And_swap3 (a b : Prop) :
  a ∧ b → b ∧ a :=
  by
    intro hab
    cases' hab with ha hb
    constructor
    assumption
    assumption
    done

/- The above proof step by step:

* Assume we know `a ∧ b`.
* The goal is `b ∧ a`.
* Show `b`, which we can if we can show a conjunction with `b` on the right.
* We can, we already have `a ∧ b`.
* Show `a`, which we can if we can show a conjunction with `a` on the left.
* We can, we already have `a ∧ b`.

The `{ … }` combinator focuses on a specific subgoal. The tactic inside must
fully prove it. In the proof below, `{ … }` is used for each of the two subgoals
to give more structure to the proof. -/


theorem And_swap_braces :
  ∀a b : Prop, a ∧ b → b ∧ a :=
  by
    intro a b hab
    apply And.intro
    { exact And.right hab }
    { exact And.left hab }

theorem And_swap_braces2 :
  ∀a b : Prop, a ∧ b → b ∧ a :=
  by
    intro a b hab
    apply And.intro
    { apply And.right 
      assumption }
    { exact And.left hab }


/- Notice above how we pass the hypothesis `hab` directly to the theorems
`And.right` and `And.left`, instead of waiting for the theorems' assumptions to
appear as new subgoals. This is a small forward step in an otherwise backward
proof. -/

opaque f : ℕ → ℕ


theorem f5_if (h : ∀n : ℕ, f n = n) :
  f 5 = 5 :=
  by exact h 5


theorem Or_swap (a b : Prop) :
  a ∨ b → b ∨ a :=
  by
    intro hab
    -- apply Or.inl (wrong proof step, even though we want to work on the goal we shouldn't break symmetry)
    apply Or.elim hab
    { intro ha
      apply Or.inr
      assumption}
    { intro hb
      apply Or.inl
      assumption}
    done

-- theorem foo (a b c : Prop) : a ∨ b ∨ c := by
  -- apply Or.inr
  -- apply Or.inr
  -- done

theorem modus_ponens (a b : Prop) :
  (a → b) → a → b :=
  by
    intro hab ha
    apply hab
    exact ha

theorem Not_Not_intro (a : Prop) :
  a → ¬¬ a :=
  by
    intro ha
    -- rw[Not] this means rewrite Not (which unfolds one layer)
    -- rw[Not]
    -- change (a → False) → False 
    change ¬a → False
    intro hna
    rw[Not] at hna
    apply hna ha
    done
  
theorem Not_Not_intro2 (a : Prop) :
  a → ¬¬ a :=
  by
    intro ha
    rw[Not]
    intro hna
    contradiction -- this proves whatever you want if context contains a contradiction


def double (n : ℕ) : ℕ :=
  n + n


theorem Exists_double_iden :
  ∃n : ℕ, double n = n :=
  by
    apply Exists.intro 0
    rfl -- tells lean to do some computation, must be last step like exact
    -- rw[double]
    done

theorem not_Exists_double_lt :
¬ ∃ n : ℕ, double n < n :=
-- ∀ n : ℕ, double n ≥ n
by
  intro hex
  apply Exists.elim hex
  intro n hn
  rw[double] at hn
  linarith
  done

theorem rephrasing_impl (p q : Prop) :
(p → q) → (¬ p ∨ q) :=
by
  sorry


/- ## Reasoning about Equality

0 = 0
double 2 = 2 + 2

def f : ℕ → ℕ 
 | 0 => 3
 | n + 1 => n

def g (k : ℕ) : : ℕ :=
if k = 0 then 3 else k - 1

f 1 = 0




*Syntactic* equality:
  x = x
  [2, 1, 3] = [2, 1, 3]
  
*Definitional* equality (*intensional*, *up to computation*):
  2 + 2 = 4
  quicksort [2, 1, 3] = mergesort [2, 1, 3]
  all of the `by refl` examples below

*Propositional* equality (*provable*):
  x + y = y + x
  quicksort = mergesort
 -/



/- `rfl` proves `l = r`, where the two sides are syntactically equal up to
computation. Computation means unfolding of definitions, β-reduction
(application of `fun` to an argument), `let`, and more. -/

theorem α_example {α β : Type} (f : α → β) :
  (fun x ↦ f x) = (fun y ↦ f y) :=
  by rfl


theorem β_example {α β : Type} (f : α → β) (a : α) :
  (fun x ↦ f x) a = f a :=
  by rfl



theorem δ_example :
  double 5 = 5 + 5 :=
  by rfl

/- `let` introduces a definition that is locally scoped. Below, `n := 2` is only
in scope in the expression `n + n`. -/

theorem ζ_example :
  (let n : ℕ := 2
   n + n) = 4 :=
  by rfl

theorem η_example {α β : Type} (f : α → β) :
  (fun x ↦ f x) = f :=
  by rfl


inductive myProd (α β : Type) : Type 
| mk : α → β → myProd α β 

def myProd.first {α β : Type} : myProd α β → α 
| myProd.mk a b => a


theorem ι_example {α β : Type} (a : α) (b : β) :
  myProd.first (myProd.mk a b) = a :=
  by rfl


/-!

Which ones of these are *reduction rules*?

-/







#check Eq.refl
#check Eq.symm
#check Eq.trans
#check Eq.subst

/- The above rules can be used directly: -/


theorem Eq_trans_symm {α : Type} (a b c : α)
    (hab : a = b) (hcb : c = b) :
  a = c :=
  by
    apply Eq.trans
    { exact hab }
    { apply Eq.symm
      exact hcb }


/- `rw` applies a single equation as a left-to-right rewrite rule, once. To
apply an equation right-to-left, prefix its name with `←`. -/


theorem Eq_trans_symm_rw {α : Type} (a b c : α)
    (hab : a = b) (hcb : c = b) :
  a = c :=
  by
    rw [hab]
    rw [hcb]


/- `rw` can expand a definition. Below, `¬¬ a` becomes `¬ a → False`, and `¬ a`
becomes `a → False`. -/

theorem a_proof_of_negation (a : Prop) :
  a → ¬¬ a :=
  by
    rw [Not]
    rw [Not]
    intro ha
    intro hna
    apply hna
    exact ha

/- `simp` applies a standard set of rewrite rules (the __simp set__)
exhaustively. The set can be extended using the `@[simp]` attribute. Theorems
can be temporarily added to the simp set with the syntax
`simp [_theorem₁_, …, _theoremN_]`. -/


theorem cong_two_args_1p1 {α : Type} (a b c d : α)
    (g : α → α → ℕ → α) (hab : a = b) (hcd : c = d) :
  g a c (1 + 1) = g b d 2 :=
  by simp [hab, hcd]


/- `ac_rfl` is similar to `rfl`, but it can reason up to associativity and
commutativity of `+`, `*`, and other binary operators. -/

theorem abc_Eq_cba (a b c : ℕ) :
  a + b + c = c + b + a :=
  by ac_rfl


/- ## Proofs by Mathematical Induction

`induction` performs induction on the specified variable. It gives rise to one
named subgoal per constructor. -/


theorem add_zero (n : ℕ) :
  add 0 n = n :=
  by
    induction n with
    | zero       => rfl
    | succ n' ih => simp [add, ih]



theorem add_succ (m n : ℕ) :
  add (Nat.succ m) n = Nat.succ (add m n) :=
  by
    induction n with
    | zero       => rfl
    | succ n' ih => simp [add, ih]



theorem add_comm (m n : ℕ) :
  add m n = add n m :=
  by
    induction n with
    | zero       => simp [add, add_zero]
    | succ n' ih => simp [add, add_succ, ih]



theorem add_assoc (l m n : ℕ) :
  add (add l m) n = add l (add m n) :=
  by
    induction n with
    | zero       => rfl
    | succ n' ih => simp [add, ih]


/- `ac_rfl` is extensible. We can register `add` as a commutative and
associative operator using the type class instance mechanism (explained in
lecture 5). This is useful for the `ac_rfl` invocation below. -/


instance IsAssociative_add : IsAssociative ℕ add :=
  { assoc := add_assoc }

instance IsCommutative_add : IsCommutative ℕ add :=
  { comm := add_comm }



theorem mul_add (l m n : ℕ) :
  mul l (add m n) = add (mul l m) (mul l n) :=
  by
    induction n with
    | zero       => rfl
    | succ n' ih =>
      simp [add, mul, ih]
      ac_rfl



/- ## Cleanup Tactics

`clear` removes unused variables or hypotheses.

`rename` changes the name of a variable or hypothesis. -/

theorem cleanup_example (a b c : Prop) (ha : a) (hb : b)
    (hab : a → b) (hbc : b → c) :
  c :=
  by
    clear ha hab a
    apply hbc
    clear hbc c
    rename b => h
    exact h

end BackwardProofs

end LoVe
