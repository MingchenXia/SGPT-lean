import SGPT.Envelopes.LapClass3Envelopes
import SGPT.Envelopes.LapClass3Sign

/-!
# `θ_fⁿ` and the Di Nezza–Trapani measure identities in dimension `0`, and in every dimension

Lane CZ-LP (`claude-cz-lp`, node `czlp:dim0`).  In dimension `n = 0` the complex Hessian of a
continuous function is the empty matrix, so every continuous `f` has a bounded complex Hessian
(`hasBoundedComplexHessian_of_dim_zero`), and the chart density `(0!/π⁰) Re det h` of `θ_f⁰` is `1`:

* `isLapTopMeasure_kahlerVolume_of_dim_zero`, `lapTopMeasure_eq_kahlerVolume_of_dim_zero`:
  `θ_f⁰ = lapTopMeasure θ f` is the Kähler volume `ω⁰` (counting measure of the points);
* `c11TopMeasure_eq_kahlerVolume_of_dim_zero`, `lapTopMeasure_eq_c11TopMeasure_of_dim_zero`: so is
  the measure `DNTC11.c11TopMeasure` of the bounded-Hessian clauses, which hold for `n = 0`.

Namespace `AllDim`: the statements of `LapClass3Measure`, `LapClass3Contact`, `LapClass3Sign` and
`LapClass3Envelopes` for `f ∈ C^{1,1̄}(X)` (continuous, bounded `ω`-Laplacian) in **every dimension
`n`**, `θ_fⁿ = lapTopMeasure θ f`: the case `n = m + 1` is `LapClass3`, the case `n = 0` is the
bridge above combined with the `DNTC11` theorems (valid for all `n`).

* `AllDim.exists_isLapTopMeasure`, `AllDim.lapTopMeasure_image_eq`: existence and chart formula of
  `θ_fⁿ` (positive part `max((n!/πⁿ) Re det h, 0)` of the signed density);
* `AllDim.lapTopMeasure_eq_c11TopMeasure`: consistency with `c11TopMeasure`;
* `AllDim.ae_hessDensity_nonneg_on_contact`: the signed density is `≥ 0` a.e. on contact sets;
* `AllDim.diagonalPotentialMeasure_restrict_contact_eq`,
  `AllDim.sourcePotentialNonPluripolarMeasure_restrict_contact_eq`,
  `AllDim.globalMixedMeasure_restrict_mixedContact_toReal_eq`,
  `AllDim.sourceMixedNonPluripolarMeasure_restrict_mixedContact_toReal_eq`: `thm:DNTcontact`;
* `AllDim.diagonalPotentialMeasure_rooftopEnvelope_eq`, `AllDim.sourceObstacleEnvelope_measure_eq`:
  `cor:DNTenvelope1`;
* `AllDim.sourceGeneralizedEnvelope_measure_eq`: `prop:DNTenvelope2`;
* `AllDim.sourceObstacleEnvelope_contact_measure_eq`,
  `AllDim.sourceGeneralizedEnvelope_contact_measure_eq`: `prop:DNTenvelope3`;
* `AllDim.roofEnvelope_measure_eq`: `lma:DNTroof`, measure assertions.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Envelopes.LapClass3

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.IntegrationCurrent
open SGPT.Foundations.Analysis.Pending.DiagonalMass SGPT.Foundations.Analysis.Pending.GlobalNonPluripolar
open SGPT.Foundations.Analysis.Pending.ManifoldTubePositivity
open SGPT.Foundations.Analysis.Pending.GlobalMultilinearExpansion
open SGPT.Envelopes.LapClass SGPT.Analysis.CZLp SGPT.Envelopes.DNTC11
open SGPT.Okounkov SGPT.Okounkov.TranscendentalWNReg SGPT.PSH.VariableComplexAtlas
open SGPT.Envelopes.DNT

/-! ### Dimension `0` -/

section Dim0

/-- In dimension `0` every continuous function has a bounded complex Hessian density (any `h`; the
matrices are empty and the Levi form vanishes). -/
theorem isBoundedHessianDensityOn_of_dim_zero {g : ComplexModel 0 → ℝ}
    {U : Set (ComplexModel 0)} (hU : IsOpen U) (hg : ContinuousOn g U)
    (h : ComplexModel 0 → Matrix (Fin 0) (Fin 0) ℂ) : IsBoundedHessianDensityOn g h U where
  isOpen := hU
  continuousOn := hg
  isHermitian := fun _ => Matrix.ext fun i => i.elim0
  measurable := fun i => i.elim0
  bounded := fun _ _ _ => ⟨0, Eventually.of_forall fun _ i => i.elim0⟩
  levi := by
    intro φ _ _ _ v
    have hv : v = 0 := PiLp.ext fun i => i.elim0
    subst hv
    simp [hermQuad, sesqForm]

/-- The chart density of `θ_f⁰` is `(0!/π⁰) Re det h = 1`. -/
theorem hessDensity_of_dim_zero (h : ComplexModel 0 → Matrix (Fin 0) (Fin 0) ℂ)
    (z : ComplexModel 0) : hessDensity h z = 1 := by
  simp [hessDensity, Matrix.det_isEmpty]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel 0) M]
  [IsComplexManifold 0 M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

omit [IsComplexManifold 0 M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
/-- **In dimension `0` every continuous function has a bounded complex Hessian.** -/
theorem hasBoundedComplexHessian_of_dim_zero {f : M → ℝ} (hf : Continuous f) :
    HasBoundedComplexHessian (n := 0) f :=
  ⟨hf, fun e => ⟨0, isBoundedHessianDensityOn_of_dim_zero e.val.open_target
    (hf.comp_continuousOn e.val.continuousOn_symm) 0⟩⟩

omit [BorelSpace M] in
/-- In dimension `0` the book's class `C^{1,1̄}(X)` has bounded complex Hessians. -/
theorem hasBoundedComplexHessian_of_hasBoundedMetricLaplacian_of_dim_zero
    (w : KahlerBackground 0 M) {f : M → ℝ} (hf : HasBoundedMetricLaplacian w f) :
    HasBoundedComplexHessian (n := 0) f :=
  hasBoundedComplexHessian_of_dim_zero hf.1

/-- The Kähler volume `ω⁰` in a chart of a `0`-dimensional manifold is Lebesgue measure (the Dirac
mass of the point). -/
theorem kahlerVolume_image_of_dim_zero (w : KahlerBackground 0 M) (e : ComplexChart 0 M)
    {K : Set (ComplexModel 0)} (hK : MeasurableSet K) (hKt : K ⊆ e.val.target) :
    kahlerVolume w (e.val.symm '' K) = volume K := by
  have hω : ∀ _ : Fin 0, ThetaPlurisubharmonic w.form.val (fun _ => 0) := fun _ =>
    ((LocalPotentials.isThetaPshPotential_zero_iff w.form).mpr w.isSemipositive).1
  have hvol : kahlerVolume w =
      GlobalNonPluripolar.globalMixedMeasure (fun _ : Fin 0 => w.form) (fun _ _ => 0) hω := rfl
  have h := SmoothMixedMeasureDensity.setLIntegral_image_eq hω e hK hKt (g := fun _ => 1)
    measurable_const
  have hden : ∀ z, SmoothMixedMeasureDensity.chartDensity (fun _ : Fin 0 => w.form) e z = 1 := by
    intro z
    simp [SmoothMixedMeasureDensity.chartDensity, actualMixedTopDensity, coordinateWedgeFamily,
      coordinateWedgeUnit]
  simp only [hden, mul_one, lintegral_const, one_mul, Measure.restrict_apply_univ] at h
  rw [hvol, h]

/-- **`θ_f⁰` is the Kähler volume**: `ω⁰` satisfies the chart formula of `θ_f⁰` for every `f`. -/
theorem isLapTopMeasure_kahlerVolume_of_dim_zero (w : KahlerBackground 0 M)
    (θ : ClosedRealOneOneForm 0 M) (f : M → ℝ) : IsLapTopMeasure θ f (kahlerVolume w) := by
  intro e W ψ h hψ _ K hK hKW
  rw [kahlerVolume_image_of_dim_zero w e hK (hKW.trans hψ.2.1)]
  simp only [hessDensity_of_dim_zero, ENNReal.ofReal_one, lintegral_const, one_mul,
    Measure.restrict_apply_univ]

/-- **`θ_f⁰ = lapTopMeasure θ f` is the Kähler volume** for continuous `f` (in particular for
`f ∈ C^{1,1̄}(X)`). -/
theorem lapTopMeasure_eq_kahlerVolume_of_dim_zero (w : KahlerBackground 0 M)
    (θ : ClosedRealOneOneForm 0 M) {f : M → ℝ} (hf : Continuous f) :
    lapTopMeasure θ f = kahlerVolume w :=
  (eq_lapTopMeasure (hasHessianDensities_of_hasBoundedComplexHessian
    (hasBoundedComplexHessian_of_dim_zero hf)) (isLapTopMeasure_kahlerVolume_of_dim_zero w θ f)).symm

/-- In dimension `0` the bounded-Hessian measure `DNTC11.c11TopMeasure` is the Kähler volume. -/
theorem c11TopMeasure_eq_kahlerVolume_of_dim_zero (w : KahlerBackground 0 M)
    (θ : ClosedRealOneOneForm 0 M) {f : M → ℝ} (hf : Continuous f) :
    c11TopMeasure w θ f = kahlerVolume w := by
  classical
  have hf' := hasBoundedComplexHessian_of_dim_zero hf
  obtain ⟨-, hT⟩ := c11Threshold_spec w θ hf'
  have hfT : IsThetaPshPotential (θ + lagNode (c11Threshold w θ f) (0 : Fin 1) • w.form).val
      (fun x => (f x : EReal)) := hT _ (by simp [lagNode])
  have hbump : bumpMeasure w θ f (lagNode (c11Threshold w θ f) (0 : Fin 1)) = kahlerVolume w := by
    rw [bumpMeasure_eq w θ hfT]
    exact AmbientMassBackgroundMonotone.globalMixedMeasure_congr_tuples (Subsingleton.elim _ _)
      (Subsingleton.elim _ _) _ (fun _ =>
        ((LocalPotentials.isThetaPshPotential_zero_iff w.form).mpr w.isSemipositive).1)
  have hw : lagWeight (n := 0) (c11Threshold w θ f) 0 = 1 := by
    have h := sum_lagWeight_mul_pow (n := 0) (c11Threshold w θ f) (j := 0) le_rfl
    simpa using h
  have hratio : (fun x => ENNReal.ofReal (c11Ratio w θ f x)) =ᵐ[kahlerVolume w] 1 := by
    filter_upwards [Measure.rnDeriv_self (kahlerVolume w)] with x hx
    simp only [c11Ratio, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    rw [hbump, hx, hw]
    simp
  rw [c11TopMeasure, withDensity_congr_ae hratio, withDensity_one]

/-- In dimension `0`, `θ_f⁰ = lapTopMeasure θ f` is the measure `DNTC11.c11TopMeasure` of the
bounded-Hessian clauses, for every continuous `f`. -/
theorem lapTopMeasure_eq_c11TopMeasure_of_dim_zero (w : KahlerBackground 0 M)
    (θ : ClosedRealOneOneForm 0 M) {f : M → ℝ} (hf : Continuous f) :
    lapTopMeasure θ f = c11TopMeasure w θ f := by
  rw [lapTopMeasure_eq_kahlerVolume_of_dim_zero w θ hf,
    c11TopMeasure_eq_kahlerVolume_of_dim_zero w θ hf]

end Dim0

/-! ### Every dimension -/

namespace AllDim

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-! #### The measure `θ_fⁿ` -/

/-- **`C^{1,1̄}(X) ⊆ W^{2,2}_loc`** (complex Hessians), every dimension. -/
theorem hasHessianDensities_of_hasBoundedMetricLaplacian (w : KahlerBackground n M) {f : M → ℝ}
    (hf : HasBoundedMetricLaplacian w f) : HasHessianDensities (n := n) f := by
  rcases n with _ | m
  · exact hasHessianDensities_of_hasBoundedComplexHessian (hasBoundedComplexHessian_of_dim_zero hf.1)
  · exact LapClass3.hasHessianDensities_of_hasBoundedMetricLaplacian w hf

/-- **Existence of `θ_fⁿ`** for `f ∈ C^{1,1̄}(X)`, every dimension. -/
theorem exists_isLapTopMeasure (w : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    {f : M → ℝ} (hf : HasBoundedMetricLaplacian w f) : ∃ μ : Measure M, IsLapTopMeasure θ f μ := by
  rcases n with _ | m
  · exact ⟨kahlerVolume w, isLapTopMeasure_kahlerVolume_of_dim_zero w θ f⟩
  · exact LapClass3.exists_isLapTopMeasure w θ hf

/-- **`θ_fⁿ` satisfies the chart formula** for `f ∈ C^{1,1̄}(X)`, every dimension. -/
theorem isLapTopMeasure_lapTopMeasure_of_hasBoundedMetricLaplacian (w : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) {f : M → ℝ} (hf : HasBoundedMetricLaplacian w f) :
    IsLapTopMeasure θ f (lapTopMeasure θ f) :=
  isLapTopMeasure_lapTopMeasure (AllDim.exists_isLapTopMeasure w θ hf)

/-- **The chart formula for `θ_fⁿ`**, `f ∈ C^{1,1̄}(X)`, every dimension: in a chart `e`, for a
smooth local potential `ψ` of `θ` on `W`, a Hessian density `h` of `f ∘ e⁻¹ + ψ` on `W` and a
measurable `K ⊆ W`, `θ_fⁿ(e⁻¹ K) = ∫_K max((n!/πⁿ) Re det h, 0)`. -/
theorem lapTopMeasure_image_eq (w : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    {f : M → ℝ} (hf : HasBoundedMetricLaplacian w f) {e : ComplexChart n M}
    {W : Set (ComplexModel n)} {ψ : ComplexModel n → ℝ} (hψ : IsSmoothLocalPotential θ.val e W ψ)
    {h : ComplexModel n → Matrix (Fin n) (Fin n) ℂ}
    (hh : IsHessianDensityOn (fun z => f (e.val.symm z) + ψ z) h W) {K : Set (ComplexModel n)}
    (hK : MeasurableSet K) (hKW : K ⊆ W) :
    lapTopMeasure θ f (e.val.symm '' K) = ∫⁻ z in K, ENNReal.ofReal (hessDensity h z) :=
  AllDim.isLapTopMeasure_lapTopMeasure_of_hasBoundedMetricLaplacian w θ hf e W ψ h hψ hh K hK hKW

/-- **`θ_fⁿ = c11TopMeasure`** for `f` with bounded complex Hessian, every dimension. -/
theorem lapTopMeasure_eq_c11TopMeasure (w : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    {f : M → ℝ} (hf : HasBoundedComplexHessian (n := n) f) :
    lapTopMeasure θ f = c11TopMeasure w θ f := by
  rcases n with _ | m
  · exact lapTopMeasure_eq_c11TopMeasure_of_dim_zero w θ hf.1
  · exact LapClass3.lapTopMeasure_eq_c11TopMeasure (Nat.succ_pos m) w θ hf

/-- **Second-order contact**, every dimension: if `g ≤ f` are in `C^{1,1̄}(X)`, then
`𝟙_{g = f} θ_gⁿ = 𝟙_{g = f} θ_fⁿ`. -/
theorem lapTopMeasure_restrict_eq_of_le (w : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    {f g : M → ℝ} (hf : HasBoundedMetricLaplacian w f) (hg : HasBoundedMetricLaplacian w g)
    (hle : ∀ x, g x ≤ f x) :
    (lapTopMeasure θ g).restrict {x | g x = f x} = (lapTopMeasure θ f).restrict {x | g x = f x} := by
  rcases n with _ | m
  · rw [lapTopMeasure_eq_kahlerVolume_of_dim_zero w θ hf.1,
      lapTopMeasure_eq_kahlerVolume_of_dim_zero w θ hg.1]
  · exact LapClass3.lapTopMeasure_restrict_eq_of_le w θ hf hg hle

variable [ConnectedSpace M]

/-- **The density of `θ_fⁿ` is nonnegative on contact sets**, every dimension: for
`φ ∈ PSH(X, θ)`, `f ∈ C^{1,1̄}(X)`, `φ ≤ f`, in every chart and for every Hessian density `h` of
`f ∘ e⁻¹ + ψ`, `(n!/πⁿ) Re det h ≥ 0` almost everywhere on `e({φ = f}) ∩ W`; so no positive part is
taken there. -/
theorem ae_hessDensity_nonneg_on_contact (w : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    {u : M → EReal} (hu : IsThetaPshPotential θ.val u) {f : M → ℝ}
    (hf : HasBoundedMetricLaplacian w f) (hle : ∀ x, u x ≤ (f x : EReal)) {e : ComplexChart n M}
    {W : Set (ComplexModel n)} {ψ : ComplexModel n → ℝ} (hψ : IsSmoothLocalPotential θ.val e W ψ)
    {h : ComplexModel n → Matrix (Fin n) (Fin n) ℂ}
    (hh : IsHessianDensityOn (fun z => f (e.val.symm z) + ψ z) h W) :
    ∀ᵐ z, z ∈ W → u (e.val.symm z) = (f (e.val.symm z) : EReal) → 0 ≤ hessDensity h z := by
  rcases n with _ | m
  · exact Eventually.of_forall fun z _ _ => by rw [hessDensity_of_dim_zero]; exact zero_le_one
  · exact LapClass3.ae_hessDensity_nonneg_on_contact w θ hu hf hle hψ hh

/-! #### `thm:DNTcontact` -/

/-- **`thm:DNTcontact`, diagonal case, for `f ∈ C^{1,1̄}(X)`, every dimension**:
`𝟙_{φ = f} ⟨(θ + ddᶜφ)ⁿ⟩ = 𝟙_{φ = f} θ_fⁿ`, `θ_fⁿ = lapTopMeasure θ f`. -/
theorem diagonalPotentialMeasure_restrict_contact_eq (w : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) {u : M → EReal} (hu : IsThetaPshPotential θ.val u)
    {f : M → ℝ} (hf : HasBoundedMetricLaplacian w f) (hle : ∀ x, u x ≤ (f x : EReal)) :
    (diagonalPotentialMeasure θ u hu).restrict {x | u x = (f x : EReal)} =
      (lapTopMeasure θ f).restrict {x | u x = (f x : EReal)} := by
  rcases n with _ | m
  · rw [lapTopMeasure_eq_c11TopMeasure_of_dim_zero w θ hf.1]
    exact DNTC11.diagonalPotentialMeasure_restrict_contact_eq w θ hu
      (hasBoundedComplexHessian_of_dim_zero hf.1) hle
  · exact LapClass3.diagonalPotentialMeasure_restrict_contact_eq w θ hu hf hle

/-- **`thm:DNTcontact`, diagonal case, source-facing form**, `f ∈ C^{1,1̄}(X)`, every dimension. -/
theorem sourcePotentialNonPluripolarMeasure_restrict_contact_eq (w : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) {u : M → EReal}
    (hu : (ofFixedModel n M).IsThetaPSH θ u) {f : M → ℝ}
    (hf : HasBoundedMetricLaplacian w f) (hle : ∀ x, u x ≤ (f x : EReal)) :
    (sourcePotentialNonPluripolarMeasure θ u hu).restrict {x | u x = (f x : EReal)} =
      (lapTopMeasure (atlasClosedFormToNative θ) f).restrict {x | u x = (f x : EReal)} := by
  rcases n with _ | m
  · rw [lapTopMeasure_eq_c11TopMeasure_of_dim_zero w _ hf.1]
    exact DNTC11.sourcePotentialNonPluripolarMeasure_restrict_contact_eq w θ hu
      (hasBoundedComplexHessian_of_dim_zero hf.1) hle
  · exact LapClass3.sourcePotentialNonPluripolarMeasure_restrict_contact_eq w θ hu hf hle

/-- **The mixed Monge–Ampère measure `θ_{1,f₁} ∧ ⋯ ∧ θ_{n,fₙ}`** of obstacles in `C^{1,1̄}(X)`,
every dimension, as a signed measure of the set `A`: the polarization
`(1/n!) ∑_S (-1)^{n-|S|} (θ_S + ddᶜf_S)ⁿ(A)` of the top powers `lapTopMeasure θ_S f_S`.  For
`n = m + 1` it is `LapClass3.lapMixedReal` (`lapMixedReal_succ`). -/
def lapMixedReal (θ : Fin n → ClosedRealOneOneForm n M) (f : Fin n → M → ℝ) (A : Set M) : ℝ :=
  ((n.factorial : ℝ))⁻¹ * ∑ S : Finset (Fin n), (-1 : ℝ) ^ (n - S.card) *
    (lapTopMeasure (sumForm S (fun _ => (1 : ℝ)) θ) (fun x => ∑ i ∈ S, f i x) A).toReal

theorem lapMixedReal_succ {m : ℕ} {Y : Type*} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y] [MeasurableSpace Y]
    [BorelSpace Y] [CompactSpace Y]
    (θ : Fin (m + 1) → ClosedRealOneOneForm (m + 1) Y) (f : Fin (m + 1) → Y → ℝ) (A : Set Y) :
    AllDim.lapMixedReal θ f A = LapClass3.lapMixedReal θ f A := rfl

omit [ConnectedSpace M] in
/-- In dimension `0` the mixed measure is `DNTC11.c11MixedReal`. -/
theorem lapMixedReal_eq_c11MixedReal_of_dim_zero {Y : Type*} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel 0) Y] [IsComplexManifold 0 Y] [MeasurableSpace Y] [BorelSpace Y]
    [CompactSpace Y] (w : KahlerBackground 0 Y) (θ : Fin 0 → ClosedRealOneOneForm 0 Y)
    {f : Fin 0 → Y → ℝ} (hf : ∀ i, Continuous (f i)) (A : Set Y) :
    AllDim.lapMixedReal θ f A = c11MixedReal w θ f A := by
  unfold AllDim.lapMixedReal c11MixedReal
  congr 1
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [lapTopMeasure_eq_c11TopMeasure_of_dim_zero w _ (continuous_finsetSum _ fun i _ => hf i)]

/-- **`thm:DNTcontact` for mixed products**, obstacles in `C^{1,1̄}(X)`, every dimension:
`⟨θ_{1,φ₁} ∧ ⋯ ∧ θ_{n,φₙ}⟩(A ∩ E) = (θ_{1,f₁} ∧ ⋯ ∧ θ_{n,fₙ})(A ∩ E)` for every measurable `A`,
`E = ⋂ᵢ {φᵢ = fᵢ}`. -/
theorem globalMixedMeasure_restrict_mixedContact_toReal_eq (w : KahlerBackground n M)
    (θ : Fin n → ClosedRealOneOneForm n M) {u : Fin n → M → EReal}
    (hu : ∀ i, IsThetaPshPotential (θ i).val (u i)) {f : Fin n → M → ℝ}
    (hf : ∀ i, HasBoundedMetricLaplacian w (f i)) (hle : ∀ i x, u i x ≤ (f i x : EReal))
    {A : Set M} (hA : MeasurableSet A) :
    ((globalMixedMeasure θ u fun i => (hu i).1).restrict (mixedContactSet u f) A).toReal =
      AllDim.lapMixedReal θ f (A ∩ mixedContactSet u f) := by
  rcases n with _ | m
  · rw [lapMixedReal_eq_c11MixedReal_of_dim_zero w θ (fun i => (hf i).1)]
    exact DNTC11.globalMixedMeasure_restrict_mixedContact_toReal_eq w θ hu
      (fun i => hasBoundedComplexHessian_of_dim_zero (hf i).1) hle hA
  · rw [lapMixedReal_succ]
    exact LapClass3.globalMixedMeasure_restrict_mixedContact_toReal_eq w θ hu hf hle hA

/-- The mixed measure of the obstacles is nonnegative on subsets of the common contact set, every
dimension. -/
theorem lapMixedReal_nonneg_of_mixedContact (w : KahlerBackground n M)
    (θ : Fin n → ClosedRealOneOneForm n M) {u : Fin n → M → EReal}
    (hu : ∀ i, IsThetaPshPotential (θ i).val (u i)) {f : Fin n → M → ℝ}
    (hf : ∀ i, HasBoundedMetricLaplacian w (f i)) (hle : ∀ i x, u i x ≤ (f i x : EReal))
    {A : Set M} (hA : MeasurableSet A) :
    0 ≤ AllDim.lapMixedReal θ f (A ∩ mixedContactSet u f) := by
  rw [← AllDim.globalMixedMeasure_restrict_mixedContact_toReal_eq w θ hu hf hle hA]
  exact ENNReal.toReal_nonneg

/-- **`thm:DNTcontact` for mixed products, source-facing form**, obstacles in `C^{1,1̄}(X)`, every
dimension. -/
theorem sourceMixedNonPluripolarMeasure_restrict_mixedContact_toReal_eq (w : KahlerBackground n M)
    (θ : Fin n → AtlasClosedRealOneOneForm (ofFixedModel n M)) {u : Fin n → M → EReal}
    (hu : ∀ i, (ofFixedModel n M).IsThetaPSH (θ i) (u i)) {f : Fin n → M → ℝ}
    (hf : ∀ i, HasBoundedMetricLaplacian w (f i)) (hle : ∀ i x, u i x ≤ (f i x : EReal))
    {A : Set M} (hA : MeasurableSet A) :
    ((sourceMixedNonPluripolarMeasure θ u hu).restrict (mixedContactSet u f) A).toReal =
      AllDim.lapMixedReal (fun i => atlasClosedFormToNative (θ i)) f (A ∩ mixedContactSet u f) :=
  AllDim.globalMixedMeasure_restrict_mixedContact_toReal_eq w (fun i => atlasClosedFormToNative (θ i))
    (fun i => (isThetaPSH_iff_nativeThetaPotential (θ i) (u i)).mp (hu i)) hf hle hA

/-! #### Envelopes -/

/-- **`cor:DNTenvelope1` for `f ∈ C^{1,1̄}(X)`**, native form, every dimension:
`⟨(θ + ddᶜP_θ(f))ⁿ⟩ = 𝟙_{P_θ(f) = f} θ_fⁿ`. -/
theorem diagonalPotentialMeasure_rooftopEnvelope_eq (w : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) {f : M → ℝ} (hf : HasBoundedMetricLaplacian w f)
    (hP : IsThetaPshPotential θ.val (rooftopEnvelope θ.val fun x => (f x : EReal))) :
    diagonalPotentialMeasure θ (rooftopEnvelope θ.val fun x => (f x : EReal)) hP =
      (lapTopMeasure θ f).restrict
        {x | rooftopEnvelope θ.val (fun y => (f y : EReal)) x = (f x : EReal)} := by
  rcases n with _ | m
  · rw [lapTopMeasure_eq_c11TopMeasure_of_dim_zero w θ hf.1]
    exact DNTC11.diagonalPotentialMeasure_rooftopEnvelope_eq w θ
      (hasBoundedComplexHessian_of_dim_zero hf.1) hP
  · exact LapClass3.diagonalPotentialMeasure_rooftopEnvelope_eq w θ hf hP

/-- **`cor:DNTenvelope1` for `f ∈ C^{1,1̄}(X)`**, source-facing form, every dimension: if
`PSH(X, θ) ≠ ∅`, `P = P_θ(f)` is `θ`-psh and `θⁿ_P = 𝟙_{P = f} θ_fⁿ`. -/
theorem sourceObstacleEnvelope_measure_eq (w : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hne : ∃ φ : M → EReal, (ofFixedModel n M).IsThetaPSH θ φ) {f : M → ℝ}
    (hf : HasBoundedMetricLaplacian w f) :
    ∃ hP : (ofFixedModel n M).IsThetaPSH θ
        (sourceRelativeEnvelope θ (fun _ => ⊤) fun x => (f x : EReal)),
      sourcePotentialNonPluripolarMeasure θ
          (sourceRelativeEnvelope θ (fun _ => ⊤) fun x => (f x : EReal)) hP =
        (lapTopMeasure (atlasClosedFormToNative θ) f).restrict
          {x | sourceRelativeEnvelope θ (fun _ => ⊤) (fun y => (f y : EReal)) x = (f x : EReal)} := by
  rcases n with _ | m
  · rw [lapTopMeasure_eq_c11TopMeasure_of_dim_zero w _ hf.1]
    exact DNTC11.sourceObstacleEnvelope_measure_eq w θ hne (hasBoundedComplexHessian_of_dim_zero hf.1)
  · exact LapClass3.sourceObstacleEnvelope_measure_eq w θ hne hf

/-- **`prop:DNTenvelope2`, first assertion, for `f ∈ C^{1,1̄}(X)`**, every dimension: for
`φ ∈ PSH(X, θ)` and `f ≥ φ`, `η = P_θ[φ](f)` is `θ`-psh and `θⁿ_η = 𝟙_{η = f} θ_fⁿ`. -/
theorem sourceGeneralizedEnvelope_measure_eq (w : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    {φ : M → EReal} (hφ : (ofFixedModel n M).IsThetaPSH θ φ) {f : M → ℝ}
    (hf : HasBoundedMetricLaplacian w f) (hle : ∀ x, φ x ≤ (f x : EReal)) :
    ∃ hη : (ofFixedModel n M).IsThetaPSH θ (sourceRelativeEnvelope θ φ fun x => (f x : EReal)),
      sourcePotentialNonPluripolarMeasure θ (sourceRelativeEnvelope θ φ fun x => (f x : EReal)) hη =
        (lapTopMeasure (atlasClosedFormToNative θ) f).restrict
          {x | sourceRelativeEnvelope θ φ (fun y => (f y : EReal)) x = (f x : EReal)} := by
  rcases n with _ | m
  · rw [lapTopMeasure_eq_c11TopMeasure_of_dim_zero w _ hf.1]
    exact DNTC11.sourceGeneralizedEnvelope_measure_eq w θ hφ
      (hasBoundedComplexHessian_of_dim_zero hf.1) hle
  · exact LapClass3.sourceGeneralizedEnvelope_measure_eq w θ hφ hf hle

/-- **`prop:DNTenvelope3`, first equality, for `f ∈ C^{1,1̄}(X)`**, every dimension: with
`P = P_θ(f)`, `𝟙_{φ = P} θⁿ_P = 𝟙_{φ = P} θⁿ_φ`. -/
theorem sourceObstacleEnvelope_contact_measure_eq (w : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    {φ : M → EReal} (hφ : (ofFixedModel n M).IsThetaPSH θ φ) {f : M → ℝ}
    (hf : HasBoundedMetricLaplacian w f) (hle : ∀ x, φ x ≤ (f x : EReal)) :
    ∃ hP : (ofFixedModel n M).IsThetaPSH θ
        (sourceRelativeEnvelope θ (fun _ => ⊤) fun x => (f x : EReal)),
      (sourcePotentialNonPluripolarMeasure θ
          (sourceRelativeEnvelope θ (fun _ => ⊤) fun x => (f x : EReal)) hP).restrict
          {x | φ x = sourceRelativeEnvelope θ (fun _ => ⊤) (fun y => (f y : EReal)) x} =
        (sourcePotentialNonPluripolarMeasure θ φ hφ).restrict
          {x | φ x = sourceRelativeEnvelope θ (fun _ => ⊤) (fun y => (f y : EReal)) x} := by
  rcases n with _ | m
  · exact DNTC11.sourceObstacleEnvelope_contact_measure_eq w θ hφ
      (hasBoundedComplexHessian_of_dim_zero hf.1) hle
  · exact LapClass3.sourceObstacleEnvelope_contact_measure_eq w θ hφ hf hle

/-- **`prop:DNTenvelope3`, second equality, for `f ∈ C^{1,1̄}(X)`**, every dimension: with
`η = P_θ[φ](f)`, `𝟙_{φ = η} θⁿ_η = 𝟙_{φ = η} θⁿ_φ`. -/
theorem sourceGeneralizedEnvelope_contact_measure_eq (w : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    {φ : M → EReal} (hφ : (ofFixedModel n M).IsThetaPSH θ φ) {f : M → ℝ}
    (hf : HasBoundedMetricLaplacian w f) (hle : ∀ x, φ x ≤ (f x : EReal)) :
    ∃ hη : (ofFixedModel n M).IsThetaPSH θ (sourceRelativeEnvelope θ φ fun x => (f x : EReal)),
      (sourcePotentialNonPluripolarMeasure θ (sourceRelativeEnvelope θ φ fun x => (f x : EReal))
          hη).restrict {x | φ x = sourceRelativeEnvelope θ φ (fun y => (f y : EReal)) x} =
        (sourcePotentialNonPluripolarMeasure θ φ hφ).restrict
          {x | φ x = sourceRelativeEnvelope θ φ (fun y => (f y : EReal)) x} := by
  rcases n with _ | m
  · exact DNTC11.sourceGeneralizedEnvelope_contact_measure_eq w θ hφ
      (hasBoundedComplexHessian_of_dim_zero hf.1) hle
  · exact LapClass3.sourceGeneralizedEnvelope_contact_measure_eq w θ hφ hf hle

/-- **`lma:DNTroof`, measure assertions, for `f₁, f₂ ∈ C^{1,1̄}(X)`**, every dimension: with
`P = P_ω(min{f₁, f₂})`, `Cᵢ = {P = fᵢ}`, `C = C₁ ∩ C₂`, `ω_{fᵢ}ⁿ = lapTopMeasure ω fᵢ`: `P` is
`ω`-psh, `𝟙_C ω_{f₁}ⁿ = 𝟙_C ω_{f₂}ⁿ`, `ωⁿ_P + 𝟙_C ω_{fⱼ}ⁿ = 𝟙_{C₁} ω_{f₁}ⁿ + 𝟙_{C₂} ω_{f₂}ⁿ`
(`eq:DNTroof_Pomega`, subtraction-free) and `ωⁿ_P ≥ 𝟙_{Cⱼ} ω_{fⱼ}ⁿ`. -/
theorem roofEnvelope_measure_eq (w : KahlerBackground n M) {f₁ f₂ : M → ℝ}
    (hf₁ : HasBoundedMetricLaplacian w f₁) (hf₂ : HasBoundedMetricLaplacian w f₂) :
    ∃ hP : IsThetaPshPotential w.form.val (roofEnvelope w f₁ f₂),
      (lapTopMeasure w.form f₁).restrict
          {x | roofEnvelope w f₁ f₂ x = (f₁ x : EReal) ∧ roofEnvelope w f₁ f₂ x = (f₂ x : EReal)} =
        (lapTopMeasure w.form f₂).restrict
          {x | roofEnvelope w f₁ f₂ x = (f₁ x : EReal) ∧ roofEnvelope w f₁ f₂ x = (f₂ x : EReal)} ∧
      (diagonalPotentialMeasure w.form (roofEnvelope w f₁ f₂) hP +
          (lapTopMeasure w.form f₁).restrict
            {x | roofEnvelope w f₁ f₂ x = (f₁ x : EReal) ∧
              roofEnvelope w f₁ f₂ x = (f₂ x : EReal)} =
        (lapTopMeasure w.form f₁).restrict {x | roofEnvelope w f₁ f₂ x = (f₁ x : EReal)} +
          (lapTopMeasure w.form f₂).restrict {x | roofEnvelope w f₁ f₂ x = (f₂ x : EReal)}) ∧
      (diagonalPotentialMeasure w.form (roofEnvelope w f₁ f₂) hP +
          (lapTopMeasure w.form f₂).restrict
            {x | roofEnvelope w f₁ f₂ x = (f₁ x : EReal) ∧
              roofEnvelope w f₁ f₂ x = (f₂ x : EReal)} =
        (lapTopMeasure w.form f₁).restrict {x | roofEnvelope w f₁ f₂ x = (f₁ x : EReal)} +
          (lapTopMeasure w.form f₂).restrict {x | roofEnvelope w f₁ f₂ x = (f₂ x : EReal)}) ∧
      (lapTopMeasure w.form f₁).restrict {x | roofEnvelope w f₁ f₂ x = (f₁ x : EReal)} ≤
        diagonalPotentialMeasure w.form (roofEnvelope w f₁ f₂) hP ∧
      (lapTopMeasure w.form f₂).restrict {x | roofEnvelope w f₁ f₂ x = (f₂ x : EReal)} ≤
        diagonalPotentialMeasure w.form (roofEnvelope w f₁ f₂) hP := by
  rcases n with _ | m
  · rw [lapTopMeasure_eq_c11TopMeasure_of_dim_zero w w.form hf₁.1,
      lapTopMeasure_eq_c11TopMeasure_of_dim_zero w w.form hf₂.1]
    exact DNTC11.roofEnvelope_measure_eq w (hasBoundedComplexHessian_of_dim_zero hf₁.1)
      (hasBoundedComplexHessian_of_dim_zero hf₂.1)
  · exact LapClass3.roofEnvelope_measure_eq w hf₁ hf₂

end AllDim

end SGPT.Envelopes.LapClass3
