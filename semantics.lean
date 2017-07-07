/- Formulization of the operational semantics of a simple While language
   Based on the lecture notes of 'Semantics of programming languages', KIT, 2015
   https://pp.info.uni-karlsruhe.de/lehre/SS2015/semantik/
-/

import tools.auto.finish

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
| skip
| ass (x : Var) (a : AExp)
| seq (c : Com) (c' : Com)
| cond (b : BExp) (cₜ cₑ : Com)
| while (b : BExp) (c : Com)

instance : decidable_eq AExp := by tactic.mk_dec_eq_instance
instance : decidable_eq BExp := by tactic.mk_dec_eq_instance
instance : decidable_eq Com := by tactic.mk_dec_eq_instance

open Com

infix ` ::= `:50 := ass
infix `;; `:30  := seq

example: Com := "x" ::= ↑1;; while ("x" ≤ ↑4) ("x" ::= "x" * ↑2)

-- chapter 4.1: a bigstep semantics of While

inductive bigstep : Com × Σ → Σ → Prop
  notation cs `⇓` σ':100 := bigstep cs σ'
| skip {σ} : ⟨skip,σ⟩⇓σ
| ass  {x a σ} : ⟨x ::= a,σ⟩⇓σ[x ↦ A⟦a⟧σ]
| seq  {c c' σ σ' σ''} (h : ⟨c,σ⟩⇓σ') (h' : ⟨c',σ'⟩⇓σ'') : ⟨c;;c',σ⟩⇓σ''
| if_tt {b cₜ cₑ σ σ'} (b_tt : B⟦b⟧σ = tt) (ht : ⟨cₜ,σ⟩⇓σ') : ⟨cond b cₜ cₑ,σ⟩⇓σ'
| if_ff {b cₜ cₑ σ σ'} (b_ff : B⟦b⟧σ = ff) (he : ⟨cₑ,σ⟩⇓σ') : ⟨cond b cₜ cₑ,σ⟩⇓σ'
| while_tt {b c σ σ' σ''} (b_tt : B⟦b⟧σ = tt) (hc : ⟨c,σ⟩⇓σ') (hind : ⟨while b c,σ'⟩⇓σ'') : ⟨while b c,σ⟩⇓σ''
| while_ff {b c σ} (b_ff : B⟦b⟧σ = ff) : ⟨while b c,σ⟩⇓σ

notation cs `⇓`:1000 σ':100 := bigstep cs σ'

namespace tactic.interactive
  open lean
  open lean.parser interactive interactive.types
  open tactic

  local postfix `?`:9001 := optional
  local postfix *:9001 := many

  meta def ginduction' (p : parse texpr) (rec_name : parse using_ident) (ids : parse with_ident_list)
    (revert : parse $ (tk "generalizing" *> ident*)?)
  : tactic unit :=
  do h ← i_to_expr p,
     t ← infer_type h,
     let nonlocals := t.get_app_args.filter (λ arg, not arg.is_local_constant),
     if nonlocals = [] then
       induction (to_pexpr p) rec_name ids revert
     else do {
       hn ← nonlocals.mmap $ λ arg, do {
         n ← revert_kdeps arg,
         tactic.generalize arg,
         intron n,
         let locals := arg.fold list.nil (λ e _ acc, if e.is_local_constant then e::acc else acc),
         locals.mfor' tactic.clear,
         --generalize2 (to_pexpr arg) `x `gind,
         pure h
       },
       h ← intro1,
       induction (to_pexpr h) rec_name ids revert
       --all_goals (hn.mfor' $ λ h, do rw h at *])
     }

open expr
end tactic.interactive

namespace bigstep
  variables {b : BExp} {c : Com}
  variables {σ σ' σ₁ σ₂ : Σ}

  lemma unroll_loop : ⟨while b c, σ⟩⇓σ' ↔ ⟨cond b (c;; while b c) Com.skip, σ⟩⇓σ' :=
  iff.intro
    (assume h : ⟨while b c, σ⟩⇓σ',
     show ⟨cond b (c;; while b c) Com.skip, σ⟩⇓σ',
     begin
       cases h,
       { apply bigstep.if_tt b_tt (bigstep.seq hc hind) },
       { apply bigstep.if_ff b_ff bigstep.skip }
     end)
    (assume h : ⟨cond b (c;; while b c) Com.skip, σ⟩⇓σ',
     show ⟨while b c, σ⟩⇓σ',
     begin
       cases h,
       { cases ht, apply bigstep.while_tt b_tt h_1 h' },
       { cases he, apply bigstep.while_ff b_ff }
     end)

  -- chapter 4.2
  lemma deterministic (h₁ : ⟨c, σ⟩⇓σ₁) (h₂ : ⟨c, σ⟩⇓σ₂) : σ₁ = σ₂ :=
  begin
    ginduction' h₁ generalizing σ₂,
    case skip { cases h₂, refl },
    case ass { cases h₂, refl },
    case seq c c' σ σ₁' σ₁ {
      cases h₂, case bigstep.seq σ₂' {
        have: σ₁' = σ₂',    from ih_1 ‹⟨c, σ⟩⇓σ₂'›,
        have: ⟨c', σ₁'⟩⇓σ₂, by simp [this, ‹⟨c', σ₂'⟩⇓σ₂›],
        show σ₁ = σ₂,       from ih_2 this
      },
    },
    case if_tt { cases h₂,
      case if_tt { exact ih_1 ‹⟨cₜ, σ⟩⇓σ₂› },
      case if_ff { rw b_ff at b_tt, contradiction }
    },
    case if_ff { cases h₂,
      case if_tt { rw b_ff at b_tt, contradiction },
      case if_ff { exact ih_1 ‹⟨cₑ, σ⟩⇓σ₂› }
    },
    case while_tt { cases h₂,
      case while_tt σ₂' { apply ih_2, rw ih_1 ‹⟨c, σ⟩⇓σ₂'›, assumption },
      case while_ff { rw b_ff at b_tt, contradiction }
    },
    case while_ff { cases h₂,
      case while_tt { rw b_ff at b_tt, contradiction },
      case while_ff { refl }
    }
  end
end bigstep

-- chapter 4.3: a smallstep semantics of While

inductive smallstep : Com × Σ → Com × Σ → Prop
  infix ` →₁ `:50 := smallstep
| ass {x a σ} : ⟨x ::= a,σ⟩ →₁ ⟨skip, σ[x ↦ A⟦a⟧σ]⟩
| seq₁ {c₁ σ c₁' σ' c₂} (h : ⟨c₁,σ⟩ →₁ ⟨c₁', σ'⟩) : ⟨c₁;;c₂,σ⟩ →₁ ⟨c₁';;c₂,σ'⟩
| seq₂ {c σ} : ⟨skip;;c,σ⟩ →₁ ⟨c,σ⟩
| if_tt {b cₜ cₑ σ} (b_tt : B⟦b⟧σ = tt) : ⟨cond b cₜ cₑ,σ⟩ →₁ ⟨cₜ,σ⟩
| if_ff {b cₜ cₑ σ} (b_ff : B⟦b⟧σ = ff) : ⟨cond b cₜ cₑ,σ⟩ →₁ ⟨cₑ,σ⟩
| while {b c σ} : ⟨while b c,σ⟩ →₁ ⟨cond b (c;;while b c) skip,σ⟩

infix ` →₁ `:50 := smallstep

def blocked κ := ∀ κ', ¬ κ →₁ κ'

postfix ` ̸→₁`:50 := blocked


universe u

def binrel (α : Type u) := α → α → Prop

inductive rtrancl {α : Type u} (r : binrel α) : binrel α
| refl (a : α) : rtrancl a a
| step {a b c} : rtrancl a b → r b c → rtrancl a c


infix ` →₁* `:50 := rtrancl (→₁)

namespace smallstep
lemma blocked_skip (σ) : ⟨skip, σ⟩ ̸→₁.

lemma progress (c σ) (unblocked : c ≠ skip) : ¬ ⟨c, σ⟩ ̸→₁ :=
begin
  induction c,
  case skip { contradiction },
  all_goals {
    clear unblocked,
    simp [blocked, classical.not_forall_iff_exists_not, classical.not_not_iff] at *,
  },
  case Com.ass { exact ⟨_, _, ass⟩ },
  case Com.seq {
    by_cases c = skip,
    { rw ‹c = skip›, exact ⟨_, _, seq₂⟩ },
    { exact let ⟨c', σ', _⟩ := ih_1 ‹c ≠ skip› in ⟨_, _, seq₁ ‹⟨c, σ⟩ →₁ ⟨c', σ'⟩›⟩ }
  },
  case Com.cond {
    generalize2 (B⟦b⟧σ) i j,
    --generalize' : b = B⟦b⟧σ,
    cases b,
    { exact ⟨_, _, if_ff this.symm⟩ },
    { exact ⟨_, _, if_tt this.symm⟩ }
  },
  case Com.while { exact ⟨_, _, while⟩ }
end

end smallstep
