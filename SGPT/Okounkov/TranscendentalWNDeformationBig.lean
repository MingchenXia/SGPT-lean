import SGPT.Okounkov.TranscendentalWNDeformationStrict
import SGPT.Okounkov.TranscendentalBody2Lelong
import SGPT.PSH.BookCurrentSpace
import SGPT.Foundations.Analysis.Pending.GlobalPotentialPullback
import SGPT.Foundations.Analysis.Pending.GlobalMultilinearExpansion
import SGPT.Foundations.Analysis.Pending.NonKahlerLocusPoleSetBounded
import SGPT.Foundations.Analysis.Pending.KahlerDomination

/-!
# `β` is big and its Kähler locus meets `X_τ`, `X'` and `ℰ` (WN21 Proposition 4.1)

Blueprint `tok-wn-def:beta-big-route` (`claude-tok-wn-def`), proving `tok-wn:beta-big`
(`BetaBigStatement`).

Let `ξ = {θ}` be big with Kähler locus meeting `Z`, `0 < c < b`, and `ξ_c = ξ - c{Z}` big.  On the
deformation `μ : 𝒳 → X × ℙ¹`, `θ̃ = (π_X μ)^*θ + b ω'_FS - c η_ℰ` (`deformationForm`).  The
class `{θ̃}` only depends on the class of the metric of `𝒪(ℰ)`
(`bottChernRel_curvature_exceptional`), so we work with the explicit metric `η₀` of weight
`Λ = log W ∘ μ`.  For a Kähler form `ω` on `X` there are a Kähler form `κ` on `𝒳` and `t > 0` with
`κ = (π_X μ)^*ω + ω'_FS - t η₀ + dd^c f` (`exists_deformation_kahler`, Blanchard).

* (i) `exists_kahlerCurrent_strict`: for a Kähler current `θ₀ + dd^c φ ≥ ω₀` in `ξ`, with
  `0 < s ≤ min(1, b - c, c/(2t))` and `δ = s t`, the potential
  `Ψ₁ = φ ∘ π_X ∘ μ + (c - δ) log strictWeight + s f` is `(θ̃₀ - s κ)`-psh, `θ̃₀` the form of `θ₀`:
  `θ̃₀ - sκ + dd^c Ψ₁ ≥ (π_X μ)^*(θ₀ - ω₀ + dd^c φ) + (c-δ)[X'] ≥ 0`.  It is finite wherever
  `φ ∘ π_X ∘ μ` is finite and `strictWeight > 0`.
* (ii) `exists_kahlerCurrent_zStrict`: for a Kähler current `θ₁ + dd^c ψ ≥ ω₁` in `ξ_c`, with
  `0 < s ≤ min(1, b)` and `δ = s t`, the potential
  `Ψ₂ = ψ ∘ π_X ∘ μ + c log zStrictWeight + δ Λ + s f` is psh for `θ̃₀' - sκ`, `θ̃₀'` the form of
  `θ₁ + c η`, and finite off `ℰ` wherever `ψ ∘ π_X ∘ μ` is finite and `zStrictWeight > 0`.
* `exists_exceptional_strictWeight_eq_one`: over a point `y ∈ Z`, a cluster point of the points
  `μ⁻¹(y, τ)`, `τ → 0`, lies in `ℰ` and has `strictWeight = 1` (compactness of `𝒳`).
* `betaBig`: **`BetaBigStatement`**.  A Kähler current whose potential is finite at `z` has Lelong
  number `0` there, so `z ∉ E_nK(β)`.  The points are `μ⁻¹(y₀, τ) ∈ X_τ` and the cluster point in
  `ℰ` (route (i), `y₀ ∈ Z` with `φ(y₀)` finite: Boucksom's current with pole set `E_nK(ξ)`), and
  `ι'(x₀) ∈ X'` (route (ii), `x₀ ∉ Z` with `ψ(x₀)` finite).
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalWN

open Set Filter
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.FactorizedWeightForm
open SGPT.Foundations.Analysis.Pending.ProductComplexManifold
open scoped SGPT.Foundations.Analysis.Pending.ProductComplexManifold
open SGPT.Toric
open SGPT.Okounkov.TranscendentalMain

/-! ### Small facts about forms -/

section Forms

variable {k n : ℕ} {V M : Type*} [TopologicalSpace V] [ChartedSpace (ComplexModel k) V]
  [IsComplexManifold k V] [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- Pullback of closed forms is additive. -/
theorem pullback_add' {f : V → M} (hf : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ f)
    (a c : ClosedRealOneOneForm n M) :
    ClosedRealOneOneForm.pullback hf (a + c) =
      ClosedRealOneOneForm.pullback hf a + ClosedRealOneOneForm.pullback hf c := by
  apply ClosedRealOneOneForm.ext
  intro e z
  ext v
  rfl

/-- Pullback of closed forms commutes with scalar multiplication. -/
theorem pullback_smul'' {f : V → M}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ f) (t : ℝ)
    (a : ClosedRealOneOneForm n M) :
    ClosedRealOneOneForm.pullback hf (t • a) = t • ClosedRealOneOneForm.pullback hf a := by
  apply ClosedRealOneOneForm.ext
  intro e z
  ext v
  rfl

/-- A positive multiple of a Kähler form is Kähler. -/
def kahlerSmul' (omega : KahlerBackground n M) {c : ℝ} (hc : 0 < c) : KahlerBackground n M :=
  ⟨c • omega.form, ExceptionalMetricProof.isKahler_of_isStrictlyPositive fun e z hz v hv => by
    have h := (omega.isKahler.1 e z hz).2 v hv
    simp only [ClosedRealOneOneForm.coeff_smul, ContinuousAlternatingMap.smul_apply, smul_eq_mul]
    exact mul_pos hc h⟩

/-- A smooth closed form pulled back from a Kähler form is semipositive, and so are its
nonnegative multiples. -/
theorem isSemipositive_smul_pullback {f : V → M}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ f) (omega : KahlerBackground n M)
    {A : ℝ} (hA : 0 ≤ A) : (A • ClosedRealOneOneForm.pullback hf omega.form).val.IsSemipositive :=
  KahlerDomination.isSemipositive_smul
    (ClosedRealOneOneForm.pullback_isSemipositive hf omega.isSemipositive) hA

end Forms

/-- `a + r - s ≠ ⊥` in `EReal` for `a ≠ ⊥` and real `r`, `s`. -/
theorem ereal_add_coe_sub_coe_ne_bot {a : EReal} (ha : a ≠ ⊥) (r s : ℝ) :
    a + (r : EReal) - (s : EReal) ≠ ⊥ := by
  rw [sub_eq_add_neg, ← EReal.coe_neg]
  exact EReal.add_ne_bot_iff.mpr ⟨EReal.add_ne_bot_iff.mpr ⟨ha, EReal.coe_ne_bot _⟩,
    EReal.coe_ne_bot _⟩

/-- `c log U` is a real number where `U > 0`. -/
theorem coe_mul_logWeight_of_pos {n : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] {U : X → ℝ} {y : X} (hy : 0 < U y)
    (c : ℝ) :
    (c : EReal) * FactorizedWeightPsh.logWeight U y = ((c * Real.log (U y) : ℝ) : EReal) := by
  rw [FactorizedWeightPsh.logWeight_of_pos hy, ← EReal.coe_mul]

/-! ### The class of `θ̃` and the Kähler form of `𝒳` -/

section Deformation

variable {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))
variable {𝒳 : Type u} [TopologicalSpace 𝒳] [ChartedSpace (ComplexModel (m + 1 + 1)) 𝒳]
  [IsComplexManifold (m + 1 + 1) 𝒳] {μ : 𝒳 → F.carrier × ProjectiveLine}

/-- **The class `{θ̃}` only depends on the class of the metric of `𝒪(ℰ)`.** -/
theorem ofRepresentative_deformationForm_metric_congr
    (hμc : ContMDiff 𝓘(ℂ, ComplexModel (m + 1 + 1)) 𝓘(ℂ, ComplexModel (m + 1 + 1)) ∞ μ)
    (θ : ClosedRealOneOneForm (m + 1) F.carrier) (b c : ℝ)
    {E₁ E₂ : MeteredEffectiveQDivisor (m + 1 + 1) 𝒳}
    (h : RealBottChern.ofRepresentative E₁.curvature =
      RealBottChern.ofRepresentative E₂.curvature) :
    RealBottChern.ofRepresentative (deformationForm F hμc θ b c E₁) =
      RealBottChern.ofRepresentative (deformationForm F hμc θ b c E₂) := by
  unfold deformationForm
  change RealBottChern.ofRepresentativeLinearMap _ = RealBottChern.ofRepresentativeLinearMap _
  rw [map_sub, map_sub, map_smul, map_smul]
  change _ - c • RealBottChern.ofRepresentative E₁.curvature =
    _ - c • RealBottChern.ofRepresentative E₂.curvature
  rw [h]

/-- **`β` does not depend on the metric of `𝒪(ℰ)`**: for two metrics of the exceptional divisor
the forms `θ̃` are cohomologous (`bottChernRel_curvature_exceptional`). -/
theorem ofRepresentative_deformationForm_eq_of_isDivisorMetric (hμ : IsNormalConeDeformation F μ)
    (θ : ClosedRealOneOneForm (m + 1) F.carrier) (b c : ℝ)
    {E₁ E₂ : MeteredEffectiveQDivisor (m + 1 + 1) 𝒳}
    (h₁ : DivisorMetric.IsDivisorMetric (BlowupExceptionalDivisor.exceptionalDivisor hμ) E₁)
    (h₂ : DivisorMetric.IsDivisorMetric (BlowupExceptionalDivisor.exceptionalDivisor hμ) E₂) :
    RealBottChern.ofRepresentative (deformationForm F hμ.contMDiff θ b c E₁) =
      RealBottChern.ofRepresentative (deformationForm F hμ.contMDiff θ b c E₂) :=
  ofRepresentative_deformationForm_metric_congr F hμ.contMDiff θ b c
    ((RealBottChern.ofRepresentative_eq_iff _ _).mpr (bottChernRel_curvature_exceptional hμ h₂ h₁))

/-- **A Kähler form on `𝒳`** (Blanchard): for a Kähler form `ω` (`om`) on `X` and a metric `Eℰ`
of the exceptional divisor there are a Kähler form `κ`, `t > 0` and a smooth `f` with
`κ = (π_X μ)^*ω + (π_{ℙ¹} μ)^*ω_FS - t η_ℰ + dd^c f`. -/
theorem exists_deformation_kahler [CompactSpace 𝒳] (hμ : IsNormalConeDeformation F μ)
    {Eℰ : MeteredEffectiveQDivisor (m + 1 + 1) 𝒳}
    (hEℰ : DivisorMetric.IsDivisorMetric (BlowupExceptionalDivisor.exceptionalDivisor hμ) Eℰ)
    (om : KahlerBackground (m + 1) F.carrier) :
    ∃ (κ : KahlerBackground (m + 1 + 1) 𝒳) (t : ℝ) (f : 𝒳 → ℝ), 0 < t ∧
      ChartSmooth (n := m + 1 + 1) f ∧
      ∀ (e : ComplexChart (m + 1 + 1) 𝒳) (z : ComplexModel (m + 1 + 1)), z ∈ e.val.target →
        κ.form.val.coeff e z =
          (ClosedRealOneOneForm.pullback (contMDiff_deformationProjX F hμ.contMDiff)
              om.form).val.coeff e z +
            (ClosedRealOneOneForm.pullback (contMDiff_deformationProjP1 F hμ.contMDiff)
              projectiveNativeFSClosedForm).val.coeff e z -
            t • Eℰ.curvature.val.coeff e z + smoothDDC (fun y => f (e.val.symm y)) z := by
  obtain ⟨κ, t, ht, f, hf, hκ⟩ := exists_kahler_bottChernRel (N := m + 1) hμ
    (prodKahlerBackground om projectiveNativeFSBackground) hEℰ
  refine ⟨κ, t, f, ht, hf, fun e z hz => ?_⟩
  rw [hκ e z hz, BlowupBigPullback.coeff_sub, ClosedRealOneOneForm.coeff_smul]
  have hprod : (ClosedRealOneOneForm.pullback hμ.contMDiff
      (prodKahlerBackground om projectiveNativeFSBackground).form).val.coeff e z =
      (ClosedRealOneOneForm.pullback (contMDiff_deformationProjX F hμ.contMDiff)
          om.form).val.coeff e z +
        (ClosedRealOneOneForm.pullback (contMDiff_deformationProjP1 F hμ.contMDiff)
          projectiveNativeFSClosedForm).val.coeff e z := by
    rw [prodKahlerBackground_form, prodForm, pullback_add', ClosedRealOneOneForm.coeff_add]
    have h1 := pullback_comp_geometricallyEq' (contMDiff_fst (n := m + 1) (m := 1)
      (X := F.carrier) (Y := ProjectiveLine)) hμ.contMDiff om.form.val e hz
    have h2 := pullback_comp_geometricallyEq' (contMDiff_snd (n := m + 1) (m := 1)
      (X := F.carrier) (Y := ProjectiveLine)) hμ.contMDiff projectiveNativeFSClosedForm.val e hz
    exact congrArg₂ (· + ·) h1.symm h2.symm
  rw [hprod]

/-- **Route (i)** (`tok-wn-def:beta-big-route`, part (i)): a Kähler current
`θ₀ + dd^c φ ≥ ω₀` in `ξ = {θ}` gives a Kähler current in `β = {θ̃}` with potential
`φ ∘ π_X ∘ μ + (c - δ) log strictWeight + s f`, finite wherever `φ ∘ π_X ∘ μ` is finite and
`strictWeight > 0`. -/
theorem exists_kahlerCurrent_strict [CompactSpace 𝒳] (hμ : IsNormalConeDeformation F μ)
    {E : MeteredEffectiveQDivisor (m + 1) F.carrier} (hE : IsFirstDivisorUnitMetric F E)
    {Eℰ : MeteredEffectiveQDivisor (m + 1 + 1) 𝒳}
    (hEℰ : DivisorMetric.IsDivisorMetric (BlowupExceptionalDivisor.exceptionalDivisor hμ) Eℰ)
    (hweight : ∀ z, Eℰ.weight z = ENNReal.log (ENNReal.ofReal (baseExceptionalWeight F E (μ z))))
    (hsupp : Eℰ.support = exceptionalSet F μ)
    (θ : ClosedRealOneOneForm (m + 1) F.carrier) {b c : ℝ} (hc : 0 < c) (hcb : c < b)
    (T : KahlerCurrent (RealBottChern.ofRepresentative θ)) :
    ∃ T' : KahlerCurrent
        (RealBottChern.ofRepresentative (deformationForm F hμ.contMDiff θ b c Eℰ)),
      ∀ z, T.potential (μ z).1 ≠ ⊥ → 0 < strictWeight F E μ z → T'.potential z ≠ ⊥ := by
  have hpX := contMDiff_deformationProjX F hμ.contMDiff
  have hpP := contMDiff_deformationProjP1 F hμ.contMDiff
  obtain ⟨κ, t, f₁, ht, hf₁, hκ⟩ := exists_deformation_kahler F hμ hEℰ T.lowerBound
  set s : ℝ := min 1 (min (b - c) (c / (2 * t))) with hs_def
  have hs : 0 < s := lt_min one_pos (lt_min (sub_pos.mpr hcb) (div_pos hc (by positivity)))
  have hs1 : s ≤ 1 := min_le_left _ _
  have hsbc : s ≤ b - c := (min_le_right _ _).trans (min_le_left _ _)
  have hsc : s ≤ c / (2 * t) := (min_le_right _ _).trans (min_le_right _ _)
  have hδc : s * t ≤ c / 2 := by
    have h := mul_le_mul_of_nonneg_right hsc ht.le
    have he : c / (2 * t) * t = c / 2 := by field_simp
    linarith
  have hcδ : 0 < c - s * t := by linarith
  have hφ := T.strictlyPsh
  -- the psh pieces
  have hA1 : ThetaPlurisubharmonic
      (ClosedRealOneOneForm.pullback hpX (T.representative - T.lowerBound.form)).val
      (fun z => T.potential (μ z).1) :=
    GlobalPotentialPullback.thetaPlurisubharmonic_comp hpX hφ.1
  have hA2 := FactorizedWeightPsh.thetaPlurisubharmonic_logWeight (strictFactorization F hμ hE) hcδ
  have hA := FirstPass.LocalPotentials.thetaPlurisubharmonic_add hA1 hA2
  have hP : ((1 - s) • ClosedRealOneOneForm.pullback hpX T.lowerBound.form +
      (b - s - (c - s * t)) •
        ClosedRealOneOneForm.pullback hpP projectiveNativeFSClosedForm).val.IsSemipositive :=
    UniformPerturbedKahlerLowerBound.isSemipositive_add
      (isSemipositive_smul_pullback hpX T.lowerBound (by linarith))
      (isSemipositive_smul_pullback hpP projectiveNativeFSBackground
        (by linarith [mul_pos hs ht]))
  have hAP := LocalPotentials.thetaPlurisubharmonic_add_of_semipositive hA hP
  have hg : ChartSmooth (n := m + 1 + 1) (fun y => -s * f₁ y) := fun e => (hf₁ e).const_smul (-s)
  have hcoeff : ∀ (e : ComplexChart (m + 1 + 1) 𝒳) (z : ComplexModel (m + 1 + 1)),
      z ∈ e.val.target →
      (deformationForm F hμ.contMDiff T.representative b c Eℰ - (kahlerSmul' κ hs).form).val.coeff
          e z =
        ((ClosedRealOneOneForm.pullback hpX (T.representative - T.lowerBound.form) +
            -((c - s * t) • (strictFactorization F hμ hE).closedForm)) +
          ((1 - s) • ClosedRealOneOneForm.pullback hpX T.lowerBound.form +
            (b - s - (c - s * t)) • ClosedRealOneOneForm.pullback hpP
              projectiveNativeFSClosedForm)).val.coeff e z +
        smoothDDC (fun y => -s * f₁ (e.val.symm y)) z := by
    intro e z hz
    have hD : smoothDDC (fun y => -s * f₁ (e.val.symm y)) z =
        (-s) • smoothDDC (fun y => f₁ (e.val.symm y)) z :=
      smoothDDC_smul e.val.open_target (hf₁ e) (-s) hz
    have hF := strictFactorization_closedForm_coeff F hμ hE hweight hsupp e hz
    have hK : (kahlerSmul' κ hs).form.val.coeff e z = s • κ.form.val.coeff e z := rfl
    rw [hD, BlowupBigPullback.coeff_sub, hK, hκ e z hz, BoucksomResolutionStep.pullback_sub]
    unfold deformationForm
    simp only [BlowupBigPullback.coeff_sub, ClosedRealOneOneForm.coeff_add,
      ClosedRealOneOneForm.coeff_smul, ClosedRealOneOneForm.coeff_neg, hF]
    module
  have hfin := GlobalPotentialTransforms.thetaPlurisubharmonic_sub_smooth hg hcoeff hAP
  have hval : ∀ z, T.potential (μ z).1 ≠ ⊥ → 0 < strictWeight F E μ z →
      T.potential (μ z).1 + ((c - s * t : ℝ) : EReal) *
        FactorizedWeightPsh.logWeight (strictWeight F E μ) z - ((-s * f₁ z : ℝ) : EReal) ≠ ⊥ := by
    intro z hz hpos
    rw [coe_mul_logWeight_of_pos (n := m + 1 + 1) hpos]
    exact ereal_add_coe_sub_coe_ne_bot hz _ _
  refine ⟨⟨deformationForm F hμ.contMDiff T.representative b c Eℰ,
    ofRepresentative_deformationForm_eq F hμ.contMDiff T.represents b c Eℰ, _, kahlerSmul' κ hs,
    hfin, ?_⟩, hval⟩
  intro x U hU hxU
  obtain ⟨y, hyU, hyP, hy0⟩ := exists_mem_proj_notMem_firstFlag F hμ hU ⟨x, hxU⟩
    {x | T.potential x ≠ ⊥} fun V hV ⟨v, hv⟩ => by
      obtain ⟨w, hwV, hw⟩ := hφ.2 v V hV hv
      exact ⟨w, hwV, hw⟩
  exact ⟨y, hyU, hval y hyP (strictWeight_pos F hμ hE hy0)⟩

/-- **Route (ii)** (`tok-wn-def:beta-big-route`, part (ii)): a Kähler current
`θ₁ + dd^c ψ ≥ ω₁` in `ξ_c = {θ} - c{Z}` gives a Kähler current in `β = {θ̃}` with potential
`ψ ∘ π_X ∘ μ + c log zStrictWeight + δ Λ + s f`, finite off `ℰ` wherever `ψ ∘ π_X ∘ μ` is finite
and `zStrictWeight > 0`. -/
theorem exists_kahlerCurrent_zStrict [CompactSpace 𝒳] (hμ : IsNormalConeDeformation F μ)
    {E : MeteredEffectiveQDivisor (m + 1) F.carrier} (hE : IsFirstDivisorUnitMetric F E)
    {Eℰ : MeteredEffectiveQDivisor (m + 1 + 1) 𝒳}
    (hEℰ : DivisorMetric.IsDivisorMetric (BlowupExceptionalDivisor.exceptionalDivisor hμ) Eℰ)
    (hweight : ∀ z, Eℰ.weight z = ENNReal.log (ENNReal.ofReal (baseExceptionalWeight F E (μ z))))
    (hsupp : Eℰ.support = exceptionalSet F μ)
    (θ : ClosedRealOneOneForm (m + 1) F.carrier) {b c : ℝ} (hc : 0 < c) (hcb : c < b)
    (T : KahlerCurrent (RealBottChern.ofRepresentative θ -
      c • RealBottChern.ofRepresentative E.curvature)) :
    ∃ T' : KahlerCurrent
        (RealBottChern.ofRepresentative (deformationForm F hμ.contMDiff θ b c Eℰ)),
      ∀ z, T.potential (μ z).1 ≠ ⊥ → 0 < zStrictWeight F E μ z → z ∉ exceptionalSet F μ →
        T'.potential z ≠ ⊥ := by
  have hpX := contMDiff_deformationProjX F hμ.contMDiff
  have hpP := contMDiff_deformationProjP1 F hμ.contMDiff
  obtain ⟨κ, t, f₁, ht, hf₁, hκ⟩ := exists_deformation_kahler F hμ hEℰ T.lowerBound
  set s : ℝ := min 1 b with hs_def
  have hs : 0 < s := lt_min one_pos (hc.trans hcb)
  have hs1 : s ≤ 1 := min_le_left _ _
  have hsb : s ≤ b := min_le_right _ _
  have hδ : 0 < s * t := mul_pos hs ht
  have hφ := T.strictlyPsh
  have hrep : RealBottChern.ofRepresentative (T.representative + c • E.curvature) =
      RealBottChern.ofRepresentative θ := by
    rw [RealBottChern.ofRepresentative_add, RealBottChern.ofRepresentative_smul, T.represents,
      sub_add_cancel]
  -- the psh pieces
  have hA1 : ThetaPlurisubharmonic
      (ClosedRealOneOneForm.pullback hpX (T.representative - T.lowerBound.form)).val
      (fun z => T.potential (μ z).1) :=
    GlobalPotentialPullback.thetaPlurisubharmonic_comp hpX hφ.1
  have hA2 := FactorizedWeightPsh.thetaPlurisubharmonic_logWeight (zStrictFactorization F hμ hE) hc
  have hA3 := GlobalMultilinearExpansion.thetaPlurisubharmonic_smul hδ
    (MeteredDivisorPositivity.thetaPlurisubharmonic_weight Eℰ)
  have hA := FirstPass.LocalPotentials.thetaPlurisubharmonic_add
    (FirstPass.LocalPotentials.thetaPlurisubharmonic_add hA1 hA2) hA3
  have hP : ((1 - s) • ClosedRealOneOneForm.pullback hpX T.lowerBound.form +
      (b - s) •
        ClosedRealOneOneForm.pullback hpP projectiveNativeFSClosedForm).val.IsSemipositive :=
    UniformPerturbedKahlerLowerBound.isSemipositive_add
      (isSemipositive_smul_pullback hpX T.lowerBound (by linarith))
      (isSemipositive_smul_pullback hpP projectiveNativeFSBackground (by linarith))
  have hAP := LocalPotentials.thetaPlurisubharmonic_add_of_semipositive hA hP
  have hg : ChartSmooth (n := m + 1 + 1) (fun y => -s * f₁ y) := fun e => (hf₁ e).const_smul (-s)
  have hcoeff : ∀ (e : ComplexChart (m + 1 + 1) 𝒳) (z : ComplexModel (m + 1 + 1)),
      z ∈ e.val.target →
      (deformationForm F hμ.contMDiff (T.representative + c • E.curvature) b c Eℰ -
          (kahlerSmul' κ hs).form).val.coeff e z =
        (((ClosedRealOneOneForm.pullback hpX (T.representative - T.lowerBound.form) +
            -(c • (zStrictFactorization F hμ hE).closedForm)) + (s * t) • Eℰ.curvature) +
          ((1 - s) • ClosedRealOneOneForm.pullback hpX T.lowerBound.form +
            (b - s) • ClosedRealOneOneForm.pullback hpP
              projectiveNativeFSClosedForm)).val.coeff e z +
        smoothDDC (fun y => -s * f₁ (e.val.symm y)) z := by
    intro e z hz
    have hD : smoothDDC (fun y => -s * f₁ (e.val.symm y)) z =
        (-s) • smoothDDC (fun y => f₁ (e.val.symm y)) z :=
      smoothDDC_smul e.val.open_target (hf₁ e) (-s) hz
    have hF := zStrictFactorization_closedForm_coeff F hμ hE hweight hsupp e hz
    have hK : (kahlerSmul' κ hs).form.val.coeff e z = s • κ.form.val.coeff e z := rfl
    rw [hD, BlowupBigPullback.coeff_sub, hK, hκ e z hz, BoucksomResolutionStep.pullback_sub]
    unfold deformationForm
    rw [pullback_add', pullback_smul'']
    simp only [BlowupBigPullback.coeff_sub, ClosedRealOneOneForm.coeff_add,
      ClosedRealOneOneForm.coeff_smul, ClosedRealOneOneForm.coeff_neg, hF]
    module
  have hfin := GlobalPotentialTransforms.thetaPlurisubharmonic_sub_smooth hg hcoeff hAP
  have hval : ∀ z, T.potential (μ z).1 ≠ ⊥ → 0 < zStrictWeight F E μ z →
      z ∉ exceptionalSet F μ →
      T.potential (μ z).1 + (c : EReal) * FactorizedWeightPsh.logWeight (zStrictWeight F E μ) z +
        ((s * t : ℝ) : EReal) * Eℰ.weight z - ((-s * f₁ z : ℝ) : EReal) ≠ ⊥ := by
    intro z hz hpos hzE
    have hW := baseExceptionalWeight_pos F hE hzE
    rw [coe_mul_logWeight_of_pos (n := m + 1 + 1) hpos, hweight, ENNReal.log_ofReal_of_pos hW,
      ← EReal.coe_mul, add_assoc, ← EReal.coe_add]
    exact ereal_add_coe_sub_coe_ne_bot hz _ _
  refine ⟨⟨deformationForm F hμ.contMDiff (T.representative + c • E.curvature) b c Eℰ,
    ofRepresentative_deformationForm_eq F hμ.contMDiff hrep b c Eℰ, _, kahlerSmul' κ hs,
    hfin, ?_⟩, hval⟩
  intro x U hU hxU
  obtain ⟨y, hyU, hyP, hy0⟩ := exists_mem_proj_notMem_firstFlag F hμ hU ⟨x, hxU⟩
    {x | T.potential x ≠ ⊥ ∧ x ∉ F.flag (1 : Fin (m + 2))} fun V hV hne => by
      obtain ⟨v, hvV, hvZ⟩ := inter_compl_firstFlag_nonempty F hV hne
      obtain ⟨w, hwV, hw⟩ := hφ.2 v (V ∩ (F.flag (1 : Fin (m + 2)))ᶜ)
        (hV.inter F.firstDivisor.1.isOpen_compl) ⟨hvV, hvZ⟩
      exact ⟨w, hwV.1, hw, hwV.2⟩
  have hyE : y ∉ exceptionalSet F μ := fun h => hyP.2 ((mem_deformationCentre_iff F).mp h).1
  exact ⟨y, hyU, hval y hyP.1 (zStrictWeight_pos F hμ hE hyP.2) hyE⟩

/-- A cluster point of a filter converging to `a`, in a Hausdorff space, is `a`. -/
theorem eq_of_clusterPt_nhds {X : Type*} [TopologicalSpace X] [T2Space X] {x a : X}
    (h : ClusterPt x (𝓝 a)) : x = a := by
  by_contra hne
  exact h.ne (disjoint_iff.mp (disjoint_nhds_nhds.mpr hne))

/-- **A point of `ℰ` over `y₀ ∈ Z` where `strictWeight = 1`**: a cluster point (in the compact
`𝒳`) of the points `μ⁻¹(y₀, τ)` as `τ → 0`, where `strictWeight = N₀ / N₀ = 1`. -/
theorem exists_exceptional_strictWeight_eq_one [CompactSpace 𝒳] (hμ : IsNormalConeDeformation F μ)
    {E : MeteredEffectiveQDivisor (m + 1) F.carrier} (hE : IsFirstDivisorUnitMetric F E)
    {y₀ : F.carrier} (hy₀ : y₀ ∈ F.flag (1 : Fin (m + 2))) :
    ∃ z ∈ exceptionalSet F μ, (μ z).1 = y₀ ∧ strictWeight F E μ z = 1 := by
  set S : ℂ → ProjectiveLine := fun t => projectiveLineHomeomorph (t : OnePoint ℂ) with hS
  have hS0 : S 0 = projectiveZero := rfl
  have hSc : Continuous S := projectiveLineHomeomorph.continuous.comp OnePoint.continuous_coe
  have hSne : ∀ t : ℂ, t ≠ 0 → S t ≠ projectiveZero := fun t ht h =>
    ht (OnePoint.coe_injective (projectiveLineHomeomorph.injective h))
  have hex : ∀ t : ℂ, t ≠ 0 → ∃ z, μ z = (y₀, S t) := fun t ht => by
    obtain ⟨s, -, hμs, -⟩ := exists_fibreSection F hμ (hSne t ht)
    exact ⟨s y₀, hμs y₀⟩
  have : Nonempty 𝒳 := ⟨(hex 1 one_ne_zero).choose⟩
  set Q : ℂ → 𝒳 := fun t => Classical.epsilon fun z => μ z = (y₀, S t) with hQdef
  have hQ : ∀ t : ℂ, t ≠ 0 → μ (Q t) = (y₀, S t) := fun t ht => Classical.epsilon_spec (hex t ht)
  obtain ⟨z, hz⟩ := exists_clusterPt_of_compactSpace (Filter.map Q (𝓝[≠] (0 : ℂ)))
  -- `μ z = (y₀, 0)`
  have hμQ : Tendsto (fun t => μ (Q t)) (𝓝[≠] (0 : ℂ)) (𝓝 (y₀, projectiveZero)) := by
    have h1 : Tendsto (fun t => (y₀, S t)) (𝓝[≠] (0 : ℂ)) (𝓝 (y₀, projectiveZero)) := by
      rw [← hS0]
      exact (tendsto_const_nhds.prodMk_nhds (hSc.tendsto 0)).mono_left nhdsWithin_le_nhds
    refine h1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (hQ t ht).symm
  have hμz : μ z = (y₀, projectiveZero) :=
    eq_of_clusterPt_nhds (hz.map hμ.continuous.continuousAt (tendsto_map'_iff.mpr hμQ))
  -- `strictWeight z = 1`
  have hwQ : Tendsto (fun t => strictWeight F E μ (Q t)) (𝓝[≠] (0 : ℂ)) (𝓝 1) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have h := hQ t ht
    refine (strictWeight_eq_one F hμ hE ?_ ?_).symm
    · rw [h]; exact hy₀
    · rw [h]; exact hSne t ht
  have hwz : strictWeight F E μ z = 1 := eq_of_clusterPt_nhds
    (hz.map (WeightFactorization.continuousAt (strictFactorization F hμ hE) z)
      (tendsto_map'_iff.mpr hwQ))
  refine ⟨z, ?_, by rw [hμz], hwz⟩
  show μ z ∈ deformationCentre F
  rw [hμz]
  exact (mem_deformationCentre_iff F).mpr ⟨hy₀, rfl⟩

end Deformation

/-! ### `β` is big -/

open NonKahlerLocusPoleSetBounded in
/-- **`tok-wn:beta-big`** (WN21 Proposition 4.1, `BetaBigStatement`): if `ξ = {θ}` is big with
Kähler locus meeting `Z`, `0 < c < b` and `ξ_c = ξ - c{Z}` is big, then for every deformation
`μ` and every metric of `𝒪(ℰ)` the class `β = {θ̃}` is big and its Kähler locus meets every fibre
`X_τ` (`τ ≠ 0`), the strict transform `X'` and the exceptional divisor `ℰ`. -/
theorem betaBig {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1)) : BetaBigStatement F := by
  intro E hE 𝒳 _ _ _ _ μ hμ Eℰ hEℰ θ b c hc hcb hξ hξc
  obtain ⟨Eℰ₀, hmet₀, hsupp₀, hweight₀, -⟩ := exists_exceptionalMetric_weight F hμ hE
  have hcls : RealBottChern.ofRepresentative (deformationForm F hμ.contMDiff θ b c Eℰ) =
      RealBottChern.ofRepresentative (deformationForm F hμ.contMDiff θ b c Eℰ₀) :=
    ofRepresentative_deformationForm_eq_of_isDivisorMetric F hμ θ b c hEℰ hmet₀
  rw [hcls]
  set α := RealBottChern.ofRepresentative (deformationForm F hμ.contMDiff θ b c Eℰ₀) with hα
  -- the current of route (i)
  obtain ⟨hbig, y₀, hy₀Z, hy₀K⟩ := hξ
  have hbigc : IsBigClass (RealBottChern.ofRepresentative θ) :=
    (SGPT.PSH.BookCurrent.isBig_iff_isBigClass _).mp hbig
  obtain ⟨T, -, hpole⟩ :=
    exists_kahlerCurrent_analyticSingularityType_poleSet_eq_nonKahlerLocus (by omega) _ hbigc
  have hTy₀ : T.potential y₀ ≠ ⊥ := fun h => hy₀K (by rw [← hpole]; exact h)
  obtain ⟨T₁, hT₁⟩ := exists_kahlerCurrent_strict F hμ hE hmet₀ hweight₀ hsupp₀ θ hc hcb T
  -- the current of route (ii)
  obtain ⟨T'⟩ := (SGPT.PSH.BookCurrent.isBig_iff_isBigClass _).mp hξc
  obtain ⟨T₂, hT₂⟩ := exists_kahlerCurrent_zStrict F hμ hE hmet₀ hweight₀ hsupp₀ θ hc hcb T'
  -- finite potential ⇒ Lelong number `0` ⇒ Kähler locus
  have hnK : ∀ (T₀ : KahlerCurrent α) (z : 𝒳), T₀.potential z ≠ ⊥ → z ∉ nonKahlerLocus α := by
    intro T₀ z hz h
    have h0 := TranscendentalBody2.lelongNumber_eq_zero_of_ne_bot (by omega : 0 < m + 1 + 1)
      T₀.strictlyPsh.1 hz
    have h1 := h T₀
    rw [h0] at h1
    exact lt_irrefl _ h1
  refine ⟨(SGPT.PSH.BookCurrent.isBig_iff_isBigClass _).mpr ⟨T₁⟩, ?_, ?_, ?_⟩
  · -- the fibres `X_τ`, `τ ≠ 0`
    intro p hp
    obtain ⟨s, -, hμs, -⟩ := exists_fibreSection F hμ hp
    refine ⟨s y₀, ?_, hnK T₁ _ (hT₁ _ ?_ ?_)⟩
    · show μ (s y₀) ∈ univ ×ˢ {p}
      rw [hμs]
      exact ⟨mem_univ _, rfl⟩
    · rw [hμs]; exact hTy₀
    · exact strictWeight_pos F hμ hE (by rw [hμs]; exact hp)
  · -- the strict transform `X'`
    obtain ⟨v, -, hvZ⟩ := inter_compl_firstFlag_nonempty F isOpen_univ ⟨y₀, mem_univ _⟩
    obtain ⟨x₀, hx₀Z, hx₀⟩ := T'.strictlyPsh.2 v _ F.firstDivisor.1.isOpen_compl hvZ
    obtain ⟨ι, -, hμι, hrange, -⟩ := exists_centralSection F hμ
    refine ⟨ι x₀, by rw [← hrange]; exact mem_range_self x₀, hnK T₂ _ (hT₂ _ ?_ ?_ ?_)⟩
    · rw [hμι]; exact hx₀
    · exact zStrictWeight_pos F hμ hE (by rw [hμι]; exact hx₀Z)
    · show μ (ι x₀) ∉ deformationCentre F
      rw [hμι]
      exact fun h => hx₀Z ((mem_deformationCentre_iff F).mp h).1
  · -- the exceptional divisor `ℰ`
    obtain ⟨z, hzE, hz1, hzw⟩ := exists_exceptional_strictWeight_eq_one F hμ hE hy₀Z
    exact ⟨z, hzE, hnK T₁ z (hT₁ z (by rw [hz1]; exact hTy₀) (by rw [hzw]; exact one_pos))⟩

end SGPT.Okounkov.TranscendentalWN
