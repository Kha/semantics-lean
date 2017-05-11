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

-- chapter 4.1: a bigstep semantics of While

inductive bigstep : Com → Σ → Σ → Prop
  notation `⟨` c `,` σ `⟩⟱` σ':100 := bigstep c σ σ'
| skip {σ} : ⟨skip,σ⟩⟱σ
| ass  {x a σ} : ⟨x ::= a,σ⟩⟱σ[x ↦ A⟦a⟧σ]
| seq  {c c' σ σ' σ''} (h : ⟨c,σ⟩⟱σ') (h' : ⟨c',σ'⟩⟱σ'') : ⟨c;;c',σ⟩⟱σ''
| if_tt {b cₜ cₑ σ σ'} (b_tt : B⟦b⟧σ = tt) (ht : ⟨cₜ,σ⟩⟱σ') : ⟨cond b cₜ cₑ,σ⟩⟱σ'
| if_ff {b cₜ cₑ σ σ'} (b_ff : B⟦b⟧σ = ff) (he : ⟨cₑ,σ⟩⟱σ') : ⟨cond b cₜ cₑ,σ⟩⟱σ'
| while_tt {b c σ σ' σ''} (b_tt : B⟦b⟧σ = tt) (hc : ⟨c,σ⟩⟱σ') (hind : ⟨while b c,σ'⟩⟱σ'') : ⟨while b c,σ⟩⟱σ''
| while_ff {b c σ} (b_ff : B⟦b⟧σ = ff) : ⟨while b c,σ⟩⟱σ

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
       { apply bigstep.if_tt b_tt (bigstep.seq hc hind) },
       { apply bigstep.if_ff b_ff bigstep.skip }
     end)
    (assume h : ⟨cond b (c;; while b c) Com.skip, σ⟩⟱σ',
     show ⟨while b c, σ⟩⟱σ',
     begin
       cases h,
       { cases ht, apply bigstep.while_tt b_tt h_1 h' },
       { cases he, apply bigstep.while_ff b_ff }
     end)

  -- chapter 4.2
  lemma deterministic (h₁ : ⟨c, σ⟩⟱σ₁) (h₂ : ⟨c, σ⟩⟱σ₂) : σ₁ = σ₂ :=
  begin
    induction h₁ generalizing σ₂,
    case skip { cases h₂, refl },
    case ass { cases h₂, refl },
    case seq c c' σ σ₁' σ₁ h₁ h₁' ih₁ ih₂ {
      cases ‹⟨c;; c', σ⟩⟱σ₂›, case bigstep.seq σ₂' {
        have σ₁' = σ₂',    from ih₁ ‹⟨c, σ⟩⟱σ₂'›,
        have ⟨c', σ₁'⟩⟱σ₂, by simp [this, ‹⟨c', σ₂'⟩⟱σ₂›],
        show σ₁ = σ₂,      from ih₂ this
      },
      /- cases h₂,
      apply ih',
      rewrite ih h,
      assumption -/
    },
    case if_tt { cases h₂,
      case if_tt { exact ih_1 ht_1 },
      case if_ff { rewrite b_ff at b_tt, contradiction }
    },
    case if_ff { cases h₂,
      case if_tt { rewrite b_ff at b_tt, contradiction },
      case if_ff { exact ih_1 he_1 }
    },
    case while_tt { cases h₂,
      case while_tt { apply ih_2, rewrite ih_1 hc_1, assumption },
      case while_ff { rewrite b_ff at b_tt, contradiction }
    },
    case while_ff { cases h₂,
      case while_tt { rewrite b_ff at b_tt, contradiction },
      case while_ff { exact rfl }
    }
  end
end bigstep

-- chapter 4.3: a bigstep semantics of While

inductive smallstep : Com → Σ → Com → Σ → Prop
  notation `⟨` c `, ` σ `⟩` ` →₁ ` `⟨` c' `, ` σ' `⟩` := smallstep c σ c' σ'
| ass {x a σ} : ⟨x ::= a,σ⟩ →₁ ⟨skip, σ[x ↦ A⟦a⟧σ]⟩
| seq₁ {c₁ σ c₁' σ' c₂} (h : ⟨c₁,σ⟩ →₁ ⟨c₁', σ'⟩) : ⟨c₁;;c₂,σ⟩ →₁ ⟨c₁';;c₂,σ'⟩
| seq₂ {c σ} : ⟨skip;;c,σ⟩ →₁ ⟨c,σ⟩
| if_tt {b cₜ cₜ' cₑ σ σ'} (b_tt : B⟦b⟧σ = tt) (ht : ⟨cₜ,σ⟩ →₁ ⟨cₜ',σ'⟩) : ⟨cond b cₜ cₑ,σ⟩ →₁ ⟨cond b cₜ' cₑ,σ'⟩
| if_ff {b cₜ cₑ cₑ' σ σ'} (b_ff : B⟦b⟧σ = ff) (he : ⟨cₑ,σ⟩ →₁ ⟨cₑ',σ'⟩) : ⟨cond b cₜ cₑ,σ⟩ →₁ ⟨cond b cₜ cₑ',σ'⟩
| while {b c σ} : ⟨while b c,σ⟩ →₁ ⟨cond b (c;;while b c) skip,σ⟩

notation `⟨` c `,` σ `⟩` ` →₁ ` `⟨` c' `,` σ' `⟩` := smallstep c σ c' σ'

def blocked c σ := ∀ c' σ', ¬ ⟨c, σ⟩ →₁ ⟨c', σ'⟩

notation `⟨` c `,` σ `⟩` ` ↛₁` := blocked c σ
