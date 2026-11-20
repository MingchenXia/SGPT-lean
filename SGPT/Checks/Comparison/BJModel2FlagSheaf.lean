import SGPT.Checks.Comparison.BJModel2Product
import SGPT.NAPotential.BJModelFlagIdeal
import SGPT.Support.Principalization.Scheme.BlowUp.Transform.StrictTransform

/-!
# The ideal sheaf `t^b 𝔞` of a flag ideal on `X × ℙ¹` (lane BJ-MODEL2, step R1(b))

Source: [BJ22] (`references/bj22-trivval`), §2.1 (`sec:ideals`): a flag ideal
`𝔞 = ∑_λ 𝔞_λ t^{-λ}` (`equ:flagweight`) is a `𝔾_m`-invariant fractional ideal sheaf on `X × 𝔸¹`,
trivial on `X × 𝔾_m`; for `b` with `𝔞_λ = 0` for `λ > b`, `t^b 𝔞` is an honest ideal sheaf, and
it extends to `X × ℙ¹` by `𝒪` over `X × (ℙ¹ ∖ {0})`. Its normalized blow-up is the test
configuration of `𝔞` ([BJ22, §2.1], proof of `thm:VCarPL`). Blueprint: `claude-bj-model2.tex`.

With `𝓘 = centralIdeal p` the ideal sheaf of the central fibre `X × {0}` (`t` locally), we define

  `flagSheaf p 𝔞 b = ∑_{j ≥ 0} pr₁^*(𝔞_{b - j}) · 𝓘^j`   (the ideal `∑_j 𝔞_{b-j} t^j`).

## Main results

* `flagSheaf_add`: `t^b(𝔞 + 𝔟) = t^b 𝔞 + t^b 𝔟`;
* `flagSheaf_mul`: `t^{b+b'}(𝔞 𝔟) = t^b 𝔞 · t^{b'} 𝔟` when `b, b'` bound the weights of `𝔞, 𝔟`;
* `flagSheaf_succ`: `t^{b+1} 𝔞 = t^b 𝔞 · 𝓘`; `flagSheaf_monomial`: `t^b (t^{-c}) = 𝓘^{b-c}`;
* `support_flagSheaf_le`: `t^b 𝔞` is cosupported in the central fibre; in particular it is a
  nonzero ideal sheaf when `X ≠ ∅` (`support_flagSheaf_ne_top`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.NAPotential.BJ

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open SGPT.NAPotential.BJModel

/-! ### Distributivity of products of ideal sheaves over suprema -/

section distrib

variable {Y : Scheme.{0}}

theorem idealSheaf_mul_iSup {ι : Type*} (I : Y.IdealSheafData) (J : ι → Y.IdealSheafData) :
    I * (⨆ i, J i) = ⨆ i, I * J i := by
  ext U : 2
  simp only [Scheme.IdealSheafData.ideal_mul, Pi.mul_apply, Scheme.IdealSheafData.ideal_iSup,
    iSup_apply, Submodule.mul_iSup]

theorem idealSheaf_iSup_mul {ι : Type*} (I : ι → Y.IdealSheafData) (J : Y.IdealSheafData) :
    (⨆ i, I i) * J = ⨆ i, I i * J := by
  rw [mul_comm, idealSheaf_mul_iSup]
  simp only [mul_comm]

theorem idealSheaf_comap_sup {Z : Scheme.{0}} (I J : Y.IdealSheafData) (f : Z ⟶ Y) :
    (I ⊔ J).comap f = I.comap f ⊔ J.comap f :=
  (Scheme.IdealSheafData.map_gc f).l_sup

theorem idealSheaf_comap_bot {Z : Scheme.{0}} (f : Z ⟶ Y) :
    (⊥ : Y.IdealSheafData).comap f = ⊥ :=
  (Scheme.IdealSheafData.map_gc f).l_bot

end distrib

/-! ### Weight bounds -/

namespace FlagIdealBound

variable {X : Scheme.{0}}

/-- `b` **bounds the weights** of the flag ideal `𝔞`: `𝔞_λ = 0` for `λ > b`. Then `t^b 𝔞` is an
ideal sheaf on `X × 𝔸¹`. -/
def IsWeightBound (𝔞 : FlagIdeal X) (b : ℤ) : Prop := ∀ l, b < l → 𝔞.ideal l = ⊥

theorem exists_isWeightBound (𝔞 : FlagIdeal X) : ∃ b, IsWeightBound 𝔞 b := 𝔞.exists_eq_bot

theorem IsWeightBound.mono {𝔞 : FlagIdeal X} {b b' : ℤ} (h : IsWeightBound 𝔞 b) (hb : b ≤ b') :
    IsWeightBound 𝔞 b' := fun l hl => h l (hb.trans_lt hl)

theorem IsWeightBound.add {𝔞 𝔟 : FlagIdeal X} {b : ℤ} (h : IsWeightBound 𝔞 b)
    (h' : IsWeightBound 𝔟 b) : IsWeightBound (𝔞 + 𝔟) b := fun l hl => by
  rw [FlagIdeal.add_ideal, h l hl, h' l hl, sup_bot_eq]

theorem IsWeightBound.mul {𝔞 𝔟 : FlagIdeal X} {b b' : ℤ} (h : IsWeightBound 𝔞 b)
    (h' : IsWeightBound 𝔟 b') : IsWeightBound (𝔞 * 𝔟) (b + b') := fun l hl => by
  rw [FlagIdeal.mul_ideal]
  refine le_bot_iff.mp (iSup_le fun μ => ?_)
  by_cases hμ : b < μ
  · rw [h μ hμ, Scheme.IdealSheafData.bot_mul]
  · rw [h' (l - μ) (by omega), Scheme.IdealSheafData.mul_bot]

theorem isWeightBound_monomial (c : ℤ) : IsWeightBound (FlagIdeal.monomial X c) c := fun l hl => by
  rw [FlagIdeal.monomial_ideal, if_neg (not_le.mpr hl)]

end FlagIdealBound

open FlagIdealBound

/-! ### The ideal sheaf `t^b 𝔞` -/

variable {k : Type} [Field k] {X : Scheme.{0}} (p : X ⟶ Spec (.of k))

/-- **The ideal sheaf `t^b 𝔞` on `X × ℙ¹`** of a flag ideal `𝔞` ([BJ22, §2.1]):
`∑_{j ≥ 0} pr₁^*(𝔞_{b-j}) · 𝓘^j`, where `𝓘` is the ideal sheaf of the central fibre `X × {0}`
(`t` in the chart `X × 𝔸¹`). When `b` bounds the weights of `𝔞` this is `t^b ∑_λ 𝔞_λ t^{-λ}`;
over `X × (ℙ¹ ∖ {0})` it is the unit ideal. -/
def flagSheaf (𝔞 : FlagIdeal X) (b : ℤ) : (productLine p).IdealSheafData :=
  ⨆ j : ℕ, (𝔞.ideal (b - j)).comap (productFst p) * centralIdeal p ^ j

theorem le_flagSheaf (𝔞 : FlagIdeal X) (b : ℤ) (j : ℕ) :
    (𝔞.ideal (b - j)).comap (productFst p) * centralIdeal p ^ j ≤ flagSheaf p 𝔞 b :=
  le_iSup (α := (productLine p).IdealSheafData)
    (fun j : ℕ => (𝔞.ideal (b - j)).comap (productFst p) * centralIdeal p ^ j) j

/-- `t^b (𝔞 + 𝔟) = t^b 𝔞 + t^b 𝔟`. -/
theorem flagSheaf_add (𝔞 𝔟 : FlagIdeal X) (b : ℤ) :
    flagSheaf p (𝔞 + 𝔟) b = flagSheaf p 𝔞 b ⊔ flagSheaf p 𝔟 b := by
  simp only [flagSheaf, FlagIdeal.add_ideal, idealSheaf_comap_sup, Scheme.IdealSheafData.inf_mul]
  rw [← iSup_sup_eq]

/-- The pull-back of the weight ideal `(𝔞 𝔟)_l = ∑_μ 𝔞_μ 𝔟_{l - μ}`. -/
theorem comap_mul_ideal (𝔞 𝔟 : FlagIdeal X) (l : ℤ) :
    ((𝔞 * 𝔟).ideal l).comap (productFst p) =
      ⨆ μ : ℤ, (𝔞.ideal μ).comap (productFst p) * (𝔟.ideal (l - μ)).comap (productFst p) := by
  rw [FlagIdeal.mul_ideal, Scheme.IdealSheafData.comap_iSup]
  simp only [Scheme.IdealSheafData.comap_mul]

/-- **Product formula** `t^{b+b'}(𝔞 𝔟) = t^b 𝔞 · t^{b'} 𝔟` for weight bounds `b, b'` of `𝔞, 𝔟`. -/
theorem flagSheaf_mul {𝔞 𝔟 : FlagIdeal X} {b b' : ℤ} (h𝔞 : IsWeightBound 𝔞 b)
    (h𝔟 : IsWeightBound 𝔟 b') :
    flagSheaf p (𝔞 * 𝔟) (b + b') = flagSheaf p 𝔞 b * flagSheaf p 𝔟 b' := by
  apply le_antisymm
  · refine iSup_le fun m => ?_
    rw [comap_mul_ideal, idealSheaf_iSup_mul]
    refine iSup_le fun μ => ?_
    by_cases hμ : b < μ
    · rw [h𝔞 μ hμ, idealSheaf_comap_bot, Scheme.IdealSheafData.bot_mul,
        Scheme.IdealSheafData.bot_mul]
      exact bot_le
    obtain ⟨i, hi⟩ : ∃ i : ℕ, μ = b - i := ⟨(b - μ).toNat, by omega⟩
    by_cases hmi : (m : ℤ) < i
    · rw [h𝔟 (b + b' - m - μ) (by omega), idealSheaf_comap_bot, Scheme.IdealSheafData.mul_bot,
        Scheme.IdealSheafData.bot_mul]
      exact bot_le
    obtain ⟨j, hj⟩ : ∃ j : ℕ, m = i + j := ⟨m - i, by omega⟩
    have hb : b + b' - m - μ = b' - j := by omega
    rw [hb, hi, hj, pow_add]
    calc (𝔞.ideal (b - i)).comap (productFst p) * (𝔟.ideal (b' - j)).comap (productFst p) *
          (centralIdeal p ^ i * centralIdeal p ^ j)
        = ((𝔞.ideal (b - i)).comap (productFst p) * centralIdeal p ^ i) *
          ((𝔟.ideal (b' - j)).comap (productFst p) * centralIdeal p ^ j) := by ring
      _ ≤ flagSheaf p 𝔞 b * flagSheaf p 𝔟 b' :=
          mul_le_mul' (le_flagSheaf p 𝔞 b i) (le_flagSheaf p 𝔟 b' j)
  · rw [flagSheaf, idealSheaf_iSup_mul]
    refine iSup_le fun i => ?_
    rw [flagSheaf, idealSheaf_mul_iSup]
    refine iSup_le fun j => ?_
    refine le_trans ?_ (le_flagSheaf p (𝔞 * 𝔟) (b + b') (i + j))
    rw [comap_mul_ideal, idealSheaf_iSup_mul]
    refine le_trans ?_ (le_iSup _ (b - i))
    have hb : b + b' - ((i + j : ℕ) : ℤ) - (b - i) = b' - j := by push_cast; omega
    rw [hb, pow_add]
    calc ((𝔞.ideal (b - i)).comap (productFst p) * centralIdeal p ^ i) *
          ((𝔟.ideal (b' - j)).comap (productFst p) * centralIdeal p ^ j)
        = (𝔞.ideal (b - i)).comap (productFst p) * (𝔟.ideal (b' - j)).comap (productFst p) *
          (centralIdeal p ^ i * centralIdeal p ^ j) := by ring
      _ ≤ _ := le_rfl

/-- `t^{b+1} 𝔞 = t^b 𝔞 · 𝓘` for a weight bound `b` of `𝔞`. -/
theorem flagSheaf_succ {𝔞 : FlagIdeal X} {b : ℤ} (h𝔞 : IsWeightBound 𝔞 b) :
    flagSheaf p 𝔞 (b + 1) = flagSheaf p 𝔞 b * centralIdeal p := by
  rw [flagSheaf, flagSheaf, idealSheaf_iSup_mul]
  apply le_antisymm
  · refine iSup_le fun j => ?_
    cases j with
    | zero =>
      rw [h𝔞 _ (by push_cast; omega), idealSheaf_comap_bot, Scheme.IdealSheafData.bot_mul]
      exact bot_le
    | succ j =>
      refine le_trans ?_ (le_iSup _ j)
      have hb : b + 1 - ((j + 1 : ℕ) : ℤ) = b - j := by push_cast; omega
      rw [hb, pow_succ, mul_assoc]
  · refine iSup_le fun j => le_trans ?_ (le_iSup _ (j + 1))
    have hb : b + 1 - ((j + 1 : ℕ) : ℤ) = b - j := by push_cast; omega
    rw [hb, pow_succ, mul_assoc]

/-- `t^b (t^{-c}) = 𝓘^{b-c}` for `c ≤ b`. -/
theorem flagSheaf_monomial {c b : ℤ} (hcb : c ≤ b) :
    flagSheaf p (FlagIdeal.monomial X c) b = centralIdeal p ^ (b - c).toNat := by
  apply le_antisymm
  · refine iSup_le fun j => ?_
    rw [FlagIdeal.monomial_ideal]
    split_ifs with h
    · rw [Scheme.IdealSheafData.comap_top, Scheme.IdealSheafData.top_mul]
      exact pow_le_pow_right_of_le_one' le_top (by omega)
    · rw [idealSheaf_comap_bot, Scheme.IdealSheafData.bot_mul]
      exact bot_le
  · refine le_trans ?_ (le_flagSheaf p _ b (b - c).toNat)
    rw [FlagIdeal.monomial_ideal, if_pos (by omega), Scheme.IdealSheafData.comap_top,
      Scheme.IdealSheafData.top_mul]

/-- The trivial flag ideal gives the unit ideal: `t^0 · 1 = 𝒪`. -/
theorem flagSheaf_one : flagSheaf p (1 : FlagIdeal X) 0 = ⊤ := by
  rw [FlagIdeal.one_def, flagSheaf_monomial p le_rfl]
  simp

/-- **`t^b 𝔞` is cosupported in the central fibre** `X × {0}`. -/
theorem support_flagSheaf_le (𝔞 : FlagIdeal X) (b : ℤ) :
    (flagSheaf p 𝔞 b).support ≤ (centralIdeal p).support := by
  obtain ⟨a, ha⟩ := 𝔞.exists_eq_top
  let j : ℕ := (b - min a b).toNat
  have hj : (𝔞.ideal (b - j)).comap (productFst p) * centralIdeal p ^ j = centralIdeal p ^ j := by
    rw [ha _ (by omega), Scheme.IdealSheafData.comap_top, Scheme.IdealSheafData.top_mul]
  have hle : centralIdeal p ^ j ≤ flagSheaf p 𝔞 b := hj ▸ le_flagSheaf p 𝔞 b j
  refine le_trans (Scheme.IdealSheafData.support_antitone hle) ?_
  rcases Nat.eq_zero_or_pos j with h0 | hpos
  · rw [h0, pow_zero]
    exact le_of_eq_of_le Scheme.IdealSheafData.support_top bot_le
  · rw [Scheme.IdealSheafData.support_pow _ _ hpos.ne']

/-- `t^b 𝔞` is not the zero ideal sheaf: its support is not all of `X × ℙ¹` (for `X ≠ ∅`). -/
theorem support_flagSheaf_ne_top [Nonempty X] (𝔞 : FlagIdeal X) (b : ℤ) :
    (flagSheaf p 𝔞 b).support ≠ ⊤ := fun h =>
  support_centralIdeal_ne_top p (top_le_iff.mp (h ▸ support_flagSheaf_le p 𝔞 b))

end SGPT.NAPotential.BJ
