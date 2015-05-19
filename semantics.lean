/- Formulization of the operational semantics of a simple While language
   Based on the lecture notes of 'Semantics of programming languages', KIT, 2015
   https://pp.info.uni-karlsruhe.de/lehre/SS2015/semantik/
-/

import data.int

open bool
open int
open eq.ops

-- should probably become part of the standard library at some point?

definition bool.from_decidable (p : Prop) [dec : decidable p] : bool :=
match dec with
| inl := tt
| inr := ff
end

definition string.decidable_eq [instance] (s₁ s₂ : string) : decidable (s₁ = s₂) := sorry

namespace function
  variables {A B : Type}
  variables [dec : Π(a a' : A), decidable (a = a')]
  include dec

  definition update (f : A → B) (a : A) (b : B) : A → B := λa', if a' = a then b else f a'

  notation f `[` a `↦` b `]` := update f a b
end function

open function

-- section 2: definition of While

abbreviation Var := string
notation `Σ`     := Var → ℤ

inductive AExp :=
| lit : ℤ → AExp
| var : Var → AExp
| sub : AExp → AExp → AExp
| mul : AExp → AExp → AExp

namespace AExp
  attribute lit [coercion]

  -- should coercions resolve abbreviations?
  definition var' : string → AExp := var
  attribute var' [coercion]

  infixl `-`     := sub
  notation - x   := 0 - x
  notation x + y := x - (-y)
  infixl `*`     := mul

  definition val (σ : Σ) : AExp → ℤ
  | (lit n) := n
  | (var x) := σ x
  -- namespace needed?
  | (#AExp a - b) := val a - val b
  | (#AExp a * b) := val a * val b

  notation `A⟦` a `⟧` σ:100 := val σ a

  lemma val.add (a₁ a₂ : AExp) (σ : Σ) : A⟦a₁ + a₂⟧σ = A⟦a₁⟧σ + A⟦a₂⟧σ :=
  calc
    A⟦a₁ + a₂⟧σ = A⟦a₁⟧σ - (0 - A⟦a₂⟧σ) : rfl
            ... = A⟦a₁⟧σ + A⟦a₂⟧σ       : by rewrite [zero_sub, sub_neg_eq_add]
end AExp

open AExp

inductive BExp :=
| true : BExp
| leq : AExp → AExp → BExp
| not : BExp → BExp
| and : BExp → BExp → BExp

namespace BExp
  infixl `≤`  := leq
  infixl `&&` := and
  prefix `¬`  := bnot

  definition val (σ : Σ) : BExp → bool
  | true        := tt
  | (leq a₁ a₂) := bool.from_decidable (A⟦a₁⟧σ ≤ A⟦a₂⟧σ)
  | (not b)     := ¬val b
  | (b₁ && b₂)  := val b₁ && val b₂

  notation `B⟦` b `⟧` σ:100 := val σ b
end BExp

open BExp

inductive Com :=
| skip : Com
| ass : Var → AExp → Com
| seq : Com → Com → Com
| cond : BExp → Com → Com → Com
| while : BExp → Com → Com

open Com

infix `::=`:50 := ass
infix `;;`:30  := seq

example: Com := "x"::=1;; while ("x" ≤ 4) ("x" ::= "x" * 2)

-- chapter 3.1: a bigstep semantics of While

inductive bigstep : Com → Σ → Σ → Prop :=
  notation `⟨` c `,` σ `⟩⟱` σ':100 := bigstep c σ σ'
| skip : Π{σ}, ⟨skip,σ⟩⟱σ
| ass  : Π{x a σ}, ⟨x ::= a,σ⟩⟱σ[x ↦ A⟦a⟧σ]
| seq  : Π{c₁ c₂ σ σ' σ''} (H₁ : ⟨c₁,σ⟩⟱σ') (H₂ : ⟨c₂,σ'⟩⟱σ''), ⟨c₁;;c₂,σ⟩⟱σ''
| if_tt : Π{b c₁ c₂ σ σ'} (Hb : B⟦b⟧σ = tt) (H₁ : ⟨c₁,σ⟩⟱σ'), ⟨cond b c₁ c₂,σ⟩⟱σ'
| if_ff : Π{b c₁ c₂ σ σ'} (Hb : B⟦b⟧σ = ff) (H₂ : ⟨c₂,σ⟩⟱σ'), ⟨cond b c₁ c₂,σ⟩⟱σ'
| while_tt : Π{b c σ σ' σ''} (Hb : B⟦b⟧σ = tt) (Hc : ⟨c,σ⟩⟱σ') (Hind : ⟨while b c,σ'⟩⟱σ''), ⟨while b c,σ⟩⟱σ''
| while_ff : Π{b c σ} (Hb : B⟦b⟧σ = ff), ⟨while b c,σ⟩⟱σ

notation `⟨` c `,` σ `⟩⟱` σ':100 := bigstep c σ σ'

namespace bigstep
  variables {b : BExp} {c : Com}
  variables {σ σ' σ₁ σ₂ : Σ}

  lemma unroll_loop : ⟨while b c, σ⟩⟱σ' ↔ ⟨cond b (c;; while b c) Com.skip, σ⟩⟱σ' :=
  iff.intro
    (assume H : ⟨while b c, σ⟩⟱σ',
     show ⟨cond b (c;; while b c) Com.skip, σ⟩⟱σ',
     begin
       cases H,
       { apply (bigstep.if_tt Hb (bigstep.seq Hc Hind)) },
       { apply (bigstep.if_ff Hb bigstep.skip) }
     end)
    (assume H : ⟨cond b (c;; while b c) Com.skip, σ⟩⟱σ',
     show ⟨while b c, σ⟩⟱σ',
     begin
       cases H,
       { cases H₁, apply (bigstep.while_tt Hb H₁_1 H₂) },
       { cases H₂, apply (bigstep.while_ff Hb) }
     end)

  lemma deterministic (H₁ : ⟨c, σ⟩⟱σ₁) (H₂ : ⟨c, σ⟩⟱σ₂) : σ₁ = σ₂ :=
  begin
    -- induction on H₁ for the predicate '∀σ₂, ⟨c, σ⟩⟱σ₂ → σ₁ = σ₂'
    revert H₂,
    revert σ₂,
    induction H₁,
    { intro σ₂ H₂, cases H₂, exact rfl },
    { intro σ₂ H₂, cases H₂, exact rfl },
    { intro σ₂ H₂',
      cases H₂',
      apply v_1,
      rewrite (v_0 σ'_1 H₁_1),
      exact H₂_1
    },
    { intro σ₂ H₂,
      cases H₂,
      { exact v_0 σ₂ H₁_1 },
      { exact bool.no_confusion (Hb_1⁻¹ ⬝ Hb) }
    },
    { intro σ₂ H₂,
      cases H₂,
      { exact bool.no_confusion (Hb_1⁻¹ ⬝ Hb) },
      { exact v_0 σ₂ H₂_1 }
    },
    { intro σ₂ H₂,
      cases H₂,
      { apply v_1, rewrite (v_0 σ'_1 Hc_1), exact Hind_1 },
      { exact bool.no_confusion (Hb_1⁻¹ ⬝ Hb) }
    },
    { intro σ₂ H₂,
      cases H₂,
      { exact bool.no_confusion (Hb_1⁻¹ ⬝ Hb) },
      { exact rfl }
    }
  end
end bigstep
