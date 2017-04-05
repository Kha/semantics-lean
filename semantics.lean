/- Formulization of the operational semantics of a simple While language
   Based on the lecture notes of 'Semantics of programming languages', KIT, 2015
   https://pp.info.uni-karlsruhe.de/lehre/SS2015/semantik/
-/

namespace function
  variables {α β : Type}
  variables [decidable_eq α]

  def update (f : α → β) (a : α) (b : β) : α → β :=
  λ a', if a' = a then b else f a'

  notation f `[` a ` ↦ ` b `]` := update f a b
end function

-- section 2: definition of While

notation `Var` := string
notation `Σ` := Var → ℤ

inductive AExp
| lit : ℤ → AExp
| var : Var → AExp
| sub : AExp → AExp → AExp
| mul : AExp → AExp → AExp

namespace AExp
  instance has_coe_from_int : has_coe ℤ AExp := ⟨lit⟩
  instance has_coe_from_Var : has_coe Var AExp := ⟨var⟩
  instance : has_sub AExp := ⟨sub⟩
  instance : has_mul AExp := ⟨mul⟩
  instance : has_neg AExp := ⟨λ x, ↑0 - x⟩
  instance : has_add AExp := ⟨λ x y, x - -y⟩

  def val (σ : Σ) : AExp → ℤ
  | (lit n) := n
  | (var x) := σ x
  | (sub a b) := val a - val b
  | (mul a b) := val a * val b

  notation `A⟦` a `⟧` σ:100 := val σ a

  lemma val.add (a₁ a₂ : AExp) (σ : Σ) : A⟦a₁ + a₂⟧σ = A⟦a₁⟧σ + A⟦a₂⟧σ :=
  calc
    A⟦a₁ + a₂⟧σ = A⟦a₁⟧σ - (0 - A⟦a₂⟧σ) : rfl
            ... = A⟦a₁⟧σ + A⟦a₂⟧σ       : by rewrite [zero_sub, sub_neg_eq_add]
end AExp

inductive BExp
| true : BExp
| leq : AExp → AExp → BExp
| not : BExp → BExp
| and : BExp → BExp → BExp

namespace BExp
  infixl ≤  := leq
  infixl && := and
  prefix ¬  := bnot

  definition val (σ : Σ) : BExp → bool
  | true        := tt
  | (leq a₁ a₂) := A⟦a₁⟧σ ≤ A⟦a₂⟧σ
  | (not b)     := ¬val b
  | (and b₁ b₂) := val b₁ && val b₂

  notation `B⟦` b `⟧` σ:100 := val σ b
end BExp

inductive Com
| skip : Com
| ass : Var → AExp → Com
| seq : Com → Com → Com
| cond : BExp → Com → Com → Com
| while : BExp → Com → Com

open Com

infix ` ::= `:50 := ass
infix `;; `:30  := seq

example: Com := "x" ::= ↑1;; while ("x" ≤ ↑4) ("x" ::= "x" * ↑2)

-- chapter 3.1: a bigstep semantics of While

inductive bigstep : Com → Σ → Σ → Prop
  notation `⟨` c `,` σ `⟩⟱` σ':100 := bigstep c σ σ'
| skip {σ} : ⟨skip,σ⟩⟱σ
| ass  {x a σ} : ⟨x ::= a,σ⟩⟱σ[x ↦ A⟦a⟧σ]
| seq  {c c' σ σ' σ''} (h : ⟨c,σ⟩⟱σ') (h' : ⟨c',σ'⟩⟱σ'') : ⟨c;;c',σ⟩⟱σ''
| if_tt {b cₜ cₑ σ σ'} (hb : B⟦b⟧σ = tt) (ht : ⟨cₜ,σ⟩⟱σ') : ⟨cond b cₜ cₑ,σ⟩⟱σ'
| if_ff {b cₜ cₑ σ σ'} (hb : B⟦b⟧σ = ff) (he : ⟨cₑ,σ⟩⟱σ') : ⟨cond b cₜ cₑ,σ⟩⟱σ'
| while_tt {b c σ σ' σ''} (hb : B⟦b⟧σ = tt) (hc : ⟨c,σ⟩⟱σ') (hind : ⟨while b c,σ'⟩⟱σ'') : ⟨while b c,σ⟩⟱σ''
| while_ff {b c σ} (hb : B⟦b⟧σ = ff) : ⟨while b c,σ⟩⟱σ

notation `⟨` c `,` σ `⟩⟱` σ':100 := bigstep c σ σ'

namespace bigstep
  variables {b : BExp} {c : Com}
  variables {σ σ' σ₁ σ₂ : Σ}

  lemma unroll_loop : ⟨while b c, σ⟩⟱σ' ↔ ⟨cond b (c;; while b c) Com.skip, σ⟩⟱σ' :=
  iff.intro
    (assume h : ⟨while b c, σ⟩⟱σ',
     show ⟨cond b (c;; while b c) Com.skip, σ⟩⟱σ',
     begin
       cases h,
       { apply bigstep.if_tt hb (bigstep.seq hc hind) },
       { apply bigstep.if_ff hb bigstep.skip }
     end)
    (assume h : ⟨cond b (c;; while b c) Com.skip, σ⟩⟱σ',
     show ⟨while b c, σ⟩⟱σ',
     begin
       cases h,
       { cases ht, apply bigstep.while_tt hb h_1 h' },
       { cases he, apply bigstep.while_ff hb }
     end)

  lemma deterministic (h₁ : ⟨c, σ⟩⟱σ₁) (h₂ : ⟨c, σ⟩⟱σ₂) : σ₁ = σ₂ :=
  begin
    -- induction on h₁ for the predicate '∀ σ₂, ⟨c, σ⟩⟱σ₂ → σ₁ = σ₂'
    revert h₂,
    revert σ₂,
    induction h₁,
    { intros σ₂ h₂, cases h₂, exact rfl },
    { intros σ₂ h₂, cases h₂, exact rfl },
    { intros σ₂ h₂,
      cases h₂,
      apply ih_2,
      rewrite ih_1 h_1,
      assumption
    },
    { intros σ₂ h₂,
      cases h₂,
      { exact ih_1 hₜ_1 },
      { rewrite hb_1 at hb, contradiction }
    },
    { intros σ₂ h₂,
      cases h₂,
      { rewrite hb_1 at hb, contradiction },
      { exact ih_1 hₑ_1 }
    },
    { intros σ₂ h₂,
      cases h₂,
      { apply ih_2, rewrite ih_1 hc_1, assumption },
      { rewrite hb_1 at hb, contradiction }
    },
    { intros σ₂ h₂,
      cases h₂,
      { rewrite hb_1 at hb, contradiction },
      { exact rfl }
    }
  end
end bigstep
