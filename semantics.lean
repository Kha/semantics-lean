import data.int.basic
import data.int.order

open bool
open int
open eq.ops

-- 1

abbreviation Var := string
notation `Σ`     := Var → ℤ

inductive AExp :=
| lit : ℤ → AExp
| var : Var → AExp
| sub : AExp → AExp → AExp
| mul : AExp → AExp → AExp

namespace AExp
  attribute lit [coercion]
  attribute var [coercion]

  infixl `-` := sub
  prefix `-` := λx, 0 - x
  infixl `+` := λx y, x - (-y)
  infixl `*` := mul

  definition val (σ : Σ): AExp → ℤ
  | (lit n) := n
  | (var x) := σ x
  -- no infix?
  | (sub a b) := val a - val b
  | (mul a b) := val a * val b

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

definition bool.of_eq (p : Prop) [dec : decidable p] : bool :=
match dec with
| inl := tt
| inr := ff
end

namespace BExp
  infixl `≤` := leq
  infixl `&&` := and

  prefix `¬` := bnot

  definition val (σ : Σ) : BExp → bool
  | true := tt
  | (leq a₁ a₂) := bool.of_eq (le A⟦a₁⟧σ A⟦a₂⟧σ)
  | (not b) := ¬val b
  | (b₁ && b₂) := val b₁ && val b₂

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

-- 3

definition string.eq.decidable [instance] (s₁ s₂ : string) : decidable (s₁ = s₂) := sorry

inductive bigstep : Com → Σ → Σ → Prop :=
| skip : Π{σ : Σ}, bigstep skip σ σ
| ass  : Π{x : Var} {a : AExp} {σ : Σ}, bigstep (x ::= a) σ
  (λx', if x' = x then A⟦a⟧σ else σ x')
| seq  : Π{c₁ c₂ : Com} {σ σ' σ'': Σ} (H₁ : bigstep c₁ σ σ') (H₂ : bigstep c₂ σ' σ''), bigstep (c₁;;c₂) σ σ''
| if_tt : Π{b : BExp} {c₁ c₂ : Com} {σ σ': Σ} (Hb : B⟦b⟧σ = tt) (H₁ : bigstep c₁ σ σ'), bigstep (cond b c₁ c₂) σ σ'
| if_ff : Π{b : BExp} {c₁ c₂ : Com} {σ σ': Σ} (Hb : B⟦b⟧σ = ff) (H₂ : bigstep c₂ σ σ'), bigstep (cond b c₁ c₂) σ σ'
| while_tt : Π{b : BExp} {c : Com} {σ σ' σ'': Σ} (Hb : B⟦b⟧σ = tt) (Hc : bigstep c σ σ') (Hind : bigstep (while b c) σ' σ''), bigstep (while b c) σ σ''
| while_ff : Π{b : BExp} {c : Com} {σ: Σ} (Hb : B⟦b⟧σ = ff), bigstep (while b c) σ σ

notation `⟨` c `,` σ `⟩⟱` σ':100 := bigstep c σ σ'

namespace bigstep
  variables {b : BExp} {c : Com}
  variables {σ σ' σ₁ σ₂ : Σ}

  lemma unroll_loop' : ⟨while b c, σ⟩⟱σ' ↔ ⟨cond b (c;; while b c) Com.skip, σ⟩⟱σ' :=
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
    revert H₂,
    revert σ₂,
    eapply bigstep.induction_on H₁,
    { intro σ σ₂ H₂, cases H₂, apply rfl },
    { intro x a σ σ₂ H₂, cases H₂, apply rfl },
    { clear H₁ c σ σ₁, intro c₁ c₂ σ σ' σ'' Hc₁ Hc₂ Hind₁ Hind₂ σ₂ H₂, cases H₂ with σ'₂ }
  end
end