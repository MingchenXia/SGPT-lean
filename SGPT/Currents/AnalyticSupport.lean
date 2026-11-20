import SGPT.Currents.AnalyticSupportLocal
import SGPT.Currents.PluriharmonicPotential
import SGPT.Siu.SiuDecomposition
import SGPT.Siu.SiuDecompositionGeneric
import SGPT.NPP.MassPushforwardInvariance
import SGPT.Foundations.Analysis.PlurisubharmonicIntegrability
import SGPT.Foundations.Analysis.PshRegularDistribution
import SGPT.Foundations.Analysis.Pending.PshAnalyticRemovable
import SGPT.Foundations.Analysis.Pending.ModificationMassInvariance
import SGPT.Foundations.Analysis.Pending.AnalyticJacobianCriterion
import SGPT.Foundations.Analysis.Pending.LocalStatementConnected
import SGPT.Foundations.Analysis.Pending.GlobalComponents
import SGPT.Foundations.Analysis.Pending.ActualCompactAnalyticGlobalComponents
import SGPT.Foundations.Analysis.Pending.ConstantRankImage
import SGPT.Foundations.Analysis.Pending.DimensionMonotone
import SGPT.Foundations.Analysis.Pending.RiemannExtension
import SGPT.Siu.SiuDecompositionLimits
import SGPT.Foundations.Analysis.Pending.DistributionRegularization

/-!
# The support theorem for closed positive `(1,1)`-currents carried by analytic sets

Source: Xia, *Foundations of pluripotential theory*, `thm:analytic-order-zero-support` (Demailly,
*Complex analytic and differential geometry*, III.2.10–2.14), used in the book for
`lma:Siudec_pullpush` ("due to the support theorems").  Let `X` be a compact complex manifold,
`E ⊆ X` a closed analytic subset with empty interior, and `T₁, T₂` closed positive
`(1,1)`-currents which agree on `X \ E` (`CurrentEqOn`).

* `isClosedPositiveCurrent_sub_of_currentEqOn` (**comparison theorem**): if `ν(T₂, D) = 0` for
  every prime divisor `D ⊆ E`, then `T₁ - T₂` is a closed positive current.
* `eq_of_currentEqOn` : if both have vanishing generic Lelong numbers along the prime divisors in
  `E` (e.g. both are non-divisorial, or `E` contains no prime divisor), then `T₁ = T₂`.
* `eq_siuDivisorialPart_of_currentEqOn_zero` (**support theorem, positive form**): a closed
  positive current `R` vanishing off `E` equals its divisorial part `∑_D ν(R, D)[D]`, a sum over
  the prime divisors `D ⊆ E` (all other coefficients vanish); in particular `R = 0` if `E`
  contains no prime divisor.

## The route

The book and FPT argue with measure coefficients (a current of order zero supported on a smooth
hypersurface is a constant multiple of its current of integration, and supports of codimension
at least two carry no such current).  We argue through potentials, which is how closed positive
currents are formalized here: write `Tᵢ = θᵢ + ddᶜφᵢ`.  Off `E` the two potentials differ by a
smooth function `v` with `ddᶜv = θ₂ - θ₁` (Weyl's lemma, `exists_local_difference`); the local
theorem `exists_nhds_le_of_eq_add` (slicing by complex lines and the one-variable logarithmic
decomposition) shows that `v` is locally bounded above near `E`, because the potential of `T₂`
has no logarithmic pole along any hypersurface piece of `E` (`sparseLogPoles_of_genericLelong`,
from Siu's semicontinuity theorem); the removable singularity theorem for `θ`-psh functions
bounded above (`PshAnalyticRemovable`) extends `v` to a `(θ₁ - θ₂)`-psh function `w`, and
`T₁ - T₂ = (θ₁ - θ₂) + ddᶜw ≥ 0`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff Manifold Distributions

namespace SGPT.Currents.AnalyticSupport

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.LocalCurrents
open NaturalThetaPshGeometricCurrent CanonicalCurrentFrame GlobalPositiveCurrentACRestriction
open SGPT.NPP.MassPushforward
open SquaredLogLelongSourceNormalization SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus

/-- **Agreement of two currents on a set `O`**: near every point of `O`, read in every chart,
the two currents coincide. -/
def CurrentEqOn {n : ℕ} {N : Type*} [TopologicalSpace N] [ChartedSpace (ComplexModel n) N]
    [IsComplexManifold n N] {k : CurrentDegree n} (S T : GlobalCurrent n N k) (O : Set N) :
    Prop :=
  ∀ (e : ComplexChart n N) (z : ComplexModel n), z ∈ e.val.target → e.val.symm z ∈ O →
    ∃ D : Opens (ComplexModel n), z ∈ D ∧ ∃ hD : D ≤ chartTarget e,
      S.restrictChart e hD = T.restrictChart e hD

theorem CurrentEqOn.symm {n : ℕ} {N : Type*} [TopologicalSpace N]
    [ChartedSpace (ComplexModel n) N] [IsComplexManifold n N] {k : CurrentDegree n}
    {S T : GlobalCurrent n N k} {O : Set N} (h : CurrentEqOn S T O) : CurrentEqOn T S O := by
  intro e z hz hzO
  obtain ⟨D, hzD, hD, heq⟩ := h e z hz hzO
  exact ⟨D, hzD, hD, heq.symm⟩

variable {m : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel (m + 1)) M]
  [IsComplexManifold (m + 1) M]

local notation "Cur" => GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m))
local notation "Prime" => SGPT.PSH.GeometricPrimeCarrier (m + 1) M

/-! ### Antisymmetry of positivity -/

section Antisymmetry

open LocalProductCurrents ActualAnalyticCurrentLocalDensity CanonicalComplementaryCurrentTests
open StronglyPositiveForms

/-- The degree cast of test forms (the same body as the casts used in `chartSpanCurrent`). -/
def castTestCLM' {n a b : ℕ} {U : Opens (ComplexModel n)} (h : a = b) :
    TestForm U a →L[ℝ] TestForm U b := h ▸ ContinuousLinearMap.id ℝ (TestForm U a)

theorem castTestCLM'_apply {n a b : ℕ} {U : Opens (ComplexModel n)} (h : a = b)
    (α : TestForm U a) : castTestCLM' h α = castTestDegree h α := by
  subst b; rfl

theorem castTestDegree_eq_zero {n a b : ℕ} {U : Opens (ComplexModel n)} (h : a = b)
    (α : TestForm U a) {x : ComplexModel n} (hx : α x = 0) : castTestDegree h α x = 0 := by
  subst b; exact hx

/-- `chartSpanCurrent T e γ φ` is the reading of `T` on the constant form `γ` times `φ`. -/
theorem chartSpanCurrent_apply_eq (T : Cur) (e : ComplexChart (m + 1) M)
    (γ : formSpan (m + 1) m) (φ : 𝓓(chartTarget e, ℝ)) :
    chartSpanCurrent T e γ φ = T.inChart e (castTestDegree
      (by rw [complexModel_real_finrank]; omega :
        2 * m = Module.finrank ℝ (ComplexModel (m + 1)) - 2)
      (constantTestFormCLM (γ : RealForm (m + 1) (2 * m)) φ)) := by
  rw [← castTestCLM'_apply]
  rfl

/-- A type-`(1,1)` current all of whose readings on strongly positive test forms supported in
`D` vanish restricts to zero on `D`. -/
theorem restrictChart_eq_zero_of_forall {T : Cur}
    (h11 : T.IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m)) (e : ComplexChart (m + 1) M)
    {D : Opens (ComplexModel (m + 1))} (hD : D ≤ chartTarget e)
    (hvan : ∀ (γ : formSpan (m + 1) m) (φ : 𝓓(chartTarget e, ℝ)),
      tsupport (φ : ComplexModel (m + 1) → ℝ) ⊆ D → chartSpanCurrent T e γ φ = 0) :
    T.restrictChart e hD = 0 := by
  ext η
  change T.inChart e (TestFunction.monoCLM ℝ η) = 0
  have hrep : T.inChart e (TestFunction.monoCLM ℝ η) =
      toLocalCurrent (canonicalBasis (m + 1)) (degreeTwo (Nat.succ_pos m))
        (T.coefficients (canonicalBasis (m + 1)) e) (TestFunction.monoCLM ℝ η) := by
    simp only [GlobalCurrent.coefficients, CurrentPairing.toLocalCurrent_fromLocalCurrent]
  rw [hrep]
  simp only [toLocalCurrent, wedgePairing_apply]
  apply Finset.sum_eq_zero
  intro s _
  obtain ⟨γ, hγ⟩ := SGPT.Siu.exists_formSpan_coefficient (m := m)
    (fun i => currentPairingBasis (canonicalBasis (m + 1)) (degreeTwo (Nat.succ_pos m))
      (s.out (Sum.inl i)))
  rw [SGPT.Siu.coefficients_eq_chartSpanCurrent h11 e hγ, hvan γ _ ?_, smul_zero]
  have hsub := SGPT.Siu.tsupport_monoCLM_subset (m := m) hD
  intro x hx
  apply (show tsupport ((TestFunction.monoCLM ℝ η : TestForm (chartTarget e) _) :
      ComplexModel (m + 1) → _) ⊆ D from ?_)
  · exact closure_mono (fun y hy => by
      intro h0
      apply hy
      simp [testCoefficientCLM_apply, h0]) hx
  · intro y hy
    have h1 : ((TestFunction.monoCLM ℝ η : TestForm (chartTarget e) _) :
        ComplexModel (m + 1) → _) = η := by
      funext z; exact testForm_inclusion_apply hD η z
    rw [h1] at hy
    exact η.tsupport_subset hy

/-- Readings of a current on strongly positive tests supported in a domain on which it restricts
to zero vanish. -/
theorem chartSpanCurrent_eq_zero_of_restrictChart {R : Cur} (e : ComplexChart (m + 1) M)
    {D : Opens (ComplexModel (m + 1))} (hD : D ≤ chartTarget e) (hR : R.restrictChart e hD = 0)
    (β : formSpan (m + 1) m) (ψ : 𝓓(chartTarget e, ℝ))
    (hψ : tsupport (ψ : ComplexModel (m + 1) → ℝ) ⊆ D) : chartSpanCurrent R e β ψ = 0 := by
  rw [chartSpanCurrent_apply_eq]
  set α := castTestDegree (by rw [complexModel_real_finrank]; omega :
      2 * m = Module.finrank ℝ (ComplexModel (m + 1)) - 2)
    (constantTestFormCLM (β : RealForm (m + 1) (2 * m)) ψ) with hαdef
  have hαsupp : tsupport (α : ComplexModel (m + 1) → _) ⊆ D := by
    have hsupp : Function.support (α : ComplexModel (m + 1) → _) ⊆
        Function.support (ψ : ComplexModel (m + 1) → ℝ) := by
      intro x hx h0
      apply hx
      exact castTestDegree_eq_zero _ _ (by rw [constantTestFormCLM_apply, h0, zero_smul])
    exact (closure_mono hsupp).trans hψ
  set α' : TestForm D _ := ⟨α, α.contDiff, α.hasCompactSupport, hαsupp⟩ with hα'def
  have hmono : (TestFunction.monoCLM ℝ α' : TestForm (chartTarget e) _) = α := by
    apply TestFunction.ext; intro x; rw [testForm_inclusion_apply hD]; rfl
  have := congrArg (fun T => T α') hR
  simp only [GlobalCurrent.restrictChart, zero_apply] at this
  rw [← hmono]; exact this

/-- **Local antisymmetry.**  If `Q` is closed positive, `R - Q` is positive and `R` restricts to
zero on `D`, then so does `Q`. -/
theorem restrictChart_eq_zero_of_le {Q R : Cur} (hQ : SGPT.Siu.IsClosedPositiveCurrent Q)
    (hRQ : IsFullPositive (R - Q)) (e : ComplexChart (m + 1) M)
    {D : Opens (ComplexModel (m + 1))} (hD : D ≤ chartTarget e)
    (hR : R.restrictChart e hD = 0) : Q.restrictChart e hD = 0 := by
  apply restrictChart_eq_zero_of_forall hQ.2.1 e hD
  intro γ φ hφ
  have hP : IsPositive (chartSpanCurrent Q e) := isPositive_chartSpanCurrent Q hQ.2.2 e
  have hP' : IsPositive (chartSpanCurrent (R - Q) e) := isPositive_chartSpanCurrent _ hRQ e
  -- a cut-off supported in `D`, equal to one near the support of `φ`
  obtain ⟨χ, hχ1, hχ⟩ := exists_testFunction_eq_one_nhds_compact (Ω := D) φ.hasCompactSupport hφ
  set χ' : 𝓓(chartTarget e, ℝ) := TestFunction.monoCLM ℝ χ with hχ'def
  have hχ'x : ∀ x, χ' x = χ x := fun x => by
    have h' := TestFunction.monoCLM_apply (𝕜 := ℝ) (n₂ := ⊤) (Ω₂ := chartTarget e) χ
    simpa only [le_refl, hD, and_self, ↓reduceIte] using congrFun h' x
  have hχ'0 : ∀ x, 0 ≤ χ' x := fun x => by rw [hχ'x]; exact (hχ x).1
  have hRvan := fun β ψ hψ => chartSpanCurrent_eq_zero_of_restrictChart e hD hR β ψ hψ
  -- the trace of `Q` vanishes on `χ'`
  set κp : formSpan (m + 1) m := kahlerPower (m + 1) m
  have hχ'supp : tsupport (χ' : ComplexModel (m + 1) → ℝ) ⊆ D :=
    SGPT.Siu.tsupport_monoCLM_subset (m := m) hD χ
  have htr0 : chartSpanCurrent Q e κp χ' = 0 := by
    have h1 := hP.positiveDistribution_trace χ' hχ'0
    have h2 := hP'.positiveDistribution_trace χ' hχ'0
    rw [SGPT.Siu.chartSpanCurrent_sub] at h2
    change 0 ≤ chartSpanCurrent R e κp χ' - chartSpanCurrent Q e κp χ' at h2
    rw [hRvan κp χ' hχ'supp] at h2
    change 0 ≤ chartSpanCurrent Q e κp χ' at h1
    linarith
  refine SGPT.Siu.chartSpanCurrent_eq_zero_of_trace hP hχ'0 htr0 (B := {x | 1 / 2 < χ' x})
    (fun x hx => lt_trans (by norm_num) hx) γ ?_
  intro x hx
  have h1 : χ x = 1 := hχ1.self_of_nhdsSet x hx
  show 1 / 2 < χ' x
  rw [hχ'x, h1]; norm_num

/-- **Antisymmetry.**  A type-`(1,1)` current which is positive together with its negative is
zero. -/
theorem eq_zero_of_isFullPositive_of_neg {T : Cur} (hT : SGPT.Siu.IsClosedPositiveCurrent T)
    (hn : IsFullPositive (-T)) : T = 0 := by
  ext e η
  have h0T : (0 : Cur) - T = -T := by abel
  have h := restrictChart_eq_zero_of_le (R := 0) hT (by rw [h0T]; exact hn) e le_rfl
    (by ext; rfl)
  have := congrArg (fun S => S η) h
  simpa only [GlobalCurrent.restrictChart_refl, GlobalCurrent.inChart_zero] using this

end Antisymmetry

/-! ### The smooth difference of two potentials off `E` -/

section Difference

/-- `d` is, on `U ⊆ e(M)`, a smooth difference `φ₁ - φ₂` with `ddᶜd = θ₂ - θ₁`. -/
def IsLocalDifference (θ₁ θ₂ : SmoothRealForm (m + 1) M 2) (φ₁ φ₂ : M → EReal)
    (e : ComplexChart (m + 1) M) (U : Set (ComplexModel (m + 1)))
    (d : ComplexModel (m + 1) → ℝ) : Prop :=
  IsOpen U ∧ U ⊆ e.val.target ∧ ContDiffOn ℝ ∞ d U ∧
    (∀ y ∈ U, smoothDDC d y = θ₂.coeff e y - θ₁.coeff e y) ∧
    ∀ y ∈ U, φ₁ (e.val.symm y) = φ₂ (e.val.symm y) + (d y : EReal)

theorem chart_reader_eq_integral (θ : SmoothRealForm (m + 1) M 2) {u : M → EReal}
    (hu : IsThetaPshPotential θ u) (e : ComplexChart (m + 1) M)
    {W D : Opens (ComplexModel (m + 1))} (hDW : D ≤ W) (ρ : ComplexModel (m + 1) → ℝ)
    (hpot : IsSmoothLocalPotential θ e W ρ) (η : TestForm D (testDeg m)) :
    (thetaPotentialCurrent θ u hu).inChart e (TestFunction.monoCLM ℝ η) =
      ∫ x, DDCOverlap.ddcAdjoint (pairFrame m) η x *
        (chartFunction u e x + (ρ x : EReal)).toReal := by
  have hDe : D ≤ chartTarget e := hDW.trans hpot.2.1
  have hmono : (TestFunction.monoCLM ℝ η : TestForm (chartTarget e) (testDeg m)) =
      TestFunction.monoCLM ℝ (TestFunction.monoCLM ℝ η : TestForm W (testDeg m)) := by
    apply TestFunction.ext
    intro x
    rw [testForm_inclusion_apply hDe, testForm_inclusion_apply hpot.2.1,
      testForm_inclusion_apply hDW]
  rw [hmono, thetaPotentialCurrent_inChart_mono_eq_integral θ hu e ρ hpot]
  congr 1
  funext x
  rw [DDCOverlap.ddcAdjoint_monoCLM_apply hDW]

/-- **Weyl's lemma off `E`.**  If `θ₁ + ddᶜφ₁` and `θ₂ + ddᶜφ₂` agree on the open set `O`, then
in every chart, near every point of `O`, `φ₁ - φ₂` is a smooth function `d` with
`ddᶜd = θ₂ - θ₁`. -/
theorem exists_local_difference {θ₁ θ₂ : SmoothRealForm (m + 1) M 2} {φ₁ φ₂ : M → EReal}
    (h₁ : IsThetaPshPotential θ₁ φ₁) (h₂ : IsThetaPshPotential θ₂ φ₂) {O : Set M}
    (hO : IsOpen O)
    (heq : CurrentEqOn (thetaPotentialCurrent θ₁ φ₁ h₁) (thetaPotentialCurrent θ₂ φ₂ h₂) O)
    (e : ComplexChart (m + 1) M) {z : ComplexModel (m + 1)} (hz : z ∈ e.val.target)
    (hzO : e.val.symm z ∈ O) :
    ∃ U d, z ∈ U ∧ U ⊆ e.val.symm ⁻¹' O ∧ IsLocalDifference θ₁ θ₂ φ₁ φ₂ e U d := by
  obtain ⟨W₁, ρ₁, hzW₁, hpot₁, hpsh₁⟩ := h₁.1 e z hz
  obtain ⟨W₂, ρ₂, hzW₂, hpot₂, hpsh₂⟩ := h₂.1 e z hz
  obtain ⟨D, hzD, hDe, hres⟩ := heq e z hz hzO
  set W₀ : Opens (ComplexModel (m + 1)) :=
    D ⊓ (⟨W₁, hpot₁.1⟩ : Opens _) ⊓ (⟨W₂, hpot₂.1⟩ : Opens _) with hW₀def
  have hzW₀ : z ∈ W₀ := ⟨⟨hzD, hzW₁⟩, hzW₂⟩
  have hW₀1 : W₀ ≤ (⟨W₁, hpot₁.1⟩ : Opens _) := fun y hy => hy.1.2
  have hW₀2 : W₀ ≤ (⟨W₂, hpot₂.1⟩ : Opens _) := fun y hy => hy.2
  have hW₀D : W₀ ≤ D := fun y hy => hy.1.1
  have hW₀e : W₀ ≤ chartTarget e := hW₀D.trans hDe
  have hF₁ := corrected_localQuasiPsh h₁ hW₀e (hpsh₁.mono (fun y hy => (hW₀1 hy)))
  have hF₂ := corrected_localQuasiPsh h₂ hW₀e (hpsh₂.mono (fun y hy => (hW₀2 hy)))
  have hint : ∀ η : TestForm W₀ (testDeg m),
      ∫ x, DDCOverlap.ddcAdjoint (pairFrame m) η x * (chartFunction φ₁ e x + (ρ₁ x : EReal)).toReal =
      ∫ x, DDCOverlap.ddcAdjoint (pairFrame m) η x * (chartFunction φ₂ e x + (ρ₂ x : EReal)).toReal := by
    intro η
    rw [← chart_reader_eq_integral θ₁ h₁ e hW₀1 ρ₁ hpot₁ η,
      ← chart_reader_eq_integral θ₂ h₂ e hW₀2 ρ₂ hpot₂ η]
    have hη : (TestFunction.monoCLM ℝ η : TestForm (chartTarget e) (testDeg m)) =
        TestFunction.monoCLM ℝ (TestFunction.monoCLM ℝ η : TestForm D (testDeg m)) := by
      apply TestFunction.ext
      intro x
      rw [testForm_inclusion_apply hW₀e, testForm_inclusion_apply hDe,
        testForm_inclusion_apply hW₀D]
    rw [hη]
    exact congrArg (fun T => T (TestFunction.monoCLM ℝ η : TestForm D (testDeg m))) hres
  have hddc := ddC_eq_of_forall_integral_eq hF₁ hF₂ hint
  obtain ⟨U, hUW, f, hzU, hfs, -, hEq, -, hlevi⟩ :=
    ActualQuasiPshPotentialSmoothCompatibility.exists_smooth_original_difference_of_equal_native_ddc
      hF₁ hF₂ hddc z hzW₀
  have hUe : (U : Set (ComplexModel (m + 1))) ⊆ e.val.target := fun y hy => hW₀e (hUW hy)
  set U' : Set (ComplexModel (m + 1)) := U ∩ (e.val.target ∩ e.val.symm ⁻¹' O) with hU'def
  have hU'o : IsOpen U' := U.isOpen.inter (e.val.isOpen_inter_preimage_symm hO)
  have hU'U : U' ⊆ U := inter_subset_left
  refine ⟨U', fun y => f y + ρ₂ y - ρ₁ y, ⟨hzU, hz, hzO⟩, fun y hy => hy.2.2, hU'o,
    fun y hy => hUe (hU'U hy), ?_, ?_, ?_⟩
  · have h1 : ContDiffOn ℝ ∞ f U' := hfs.contDiffOn.of_le (WithTop.coe_le_coe.mpr le_top) |>.mono
      (subset_univ _)
    have h2 : ContDiffOn ℝ ∞ ρ₂ U' :=
      hpot₂.2.2.1.mono (fun y hy => hW₀2 (hUW (hU'U hy)))
    have h3 : ContDiffOn ℝ ∞ ρ₁ U' :=
      hpot₁.2.2.1.mono (fun y hy => hW₀1 (hUW (hU'U hy)))
    exact (h1.add h2).sub h3
  · intro y hy
    have h1 : ContDiffOn ℝ ∞ f U' := hfs.contDiffOn.of_le (WithTop.coe_le_coe.mpr le_top) |>.mono
      (subset_univ _)
    have h2 : ContDiffOn ℝ ∞ ρ₂ U' :=
      hpot₂.2.2.1.mono (fun y hy => hW₀2 (hUW (hU'U hy)))
    have h3 : ContDiffOn ℝ ∞ ρ₁ U' :=
      hpot₁.2.2.1.mono (fun y hy => hW₀1 (hUW (hU'U hy)))
    rw [PositiveClasses.smoothDDC_sub hU'o (h1.add h2) h3 hy, smoothDDC_add hU'o h1 h2 hy,
      hpot₂.2.2.2 (hW₀2 (hUW (hU'U hy))), hpot₁.2.2.2 (hW₀1 (hUW (hU'U hy)))]
    have hf0 : smoothDDC f y = 0 :=
      SGPT.Currents.smoothDDC_eq_zero_of_leviForm_eq_zero
        ((hfs.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt) (hlevi y (hU'U hy))
    rw [hf0, zero_add]
  · intro y hy
    have h := hEq (hU'U hy)
    simp only [chartFunction] at h
    revert h
    generalize φ₁ (e.val.symm y) = a
    generalize φ₂ (e.val.symm y) = b
    intro h
    induction b using EReal.rec with
    | bot =>
      rw [EReal.bot_add] at h ⊢
      induction a using EReal.rec with
      | bot => rfl
      | top => simp at h
      | coe a => rw [← EReal.coe_add] at h; exact absurd h (EReal.coe_ne_bot _)
    | top =>
      rw [EReal.top_add_coe] at h ⊢
      induction a using EReal.rec with
      | bot => simp at h
      | top => rfl
      | coe a => rw [← EReal.coe_add] at h; exact absurd h (EReal.coe_ne_top _)
    | coe b =>
      induction a using EReal.rec with
      | bot => simp [← EReal.coe_add] at h
      | top => simp [← EReal.coe_add] at h
      | coe a =>
        rw [← EReal.coe_add, ← EReal.coe_add, ← EReal.coe_add] at h
        rw [← EReal.coe_add]
        have := EReal.coe_injective h
        congr 1
        linarith

/-- **Uniqueness of the difference.**  Two local differences agree where both are defined. -/
theorem IsLocalDifference.eq {θ₁ θ₂ : SmoothRealForm (m + 1) M 2} {φ₁ φ₂ : M → EReal}
    (h₂ : IsThetaPshPotential θ₂ φ₂) {e e' : ComplexChart (m + 1) M}
    {U U' : Set (ComplexModel (m + 1))} {d d' : ComplexModel (m + 1) → ℝ}
    (hd : IsLocalDifference θ₁ θ₂ φ₁ φ₂ e U d) (hd' : IsLocalDifference θ₁ θ₂ φ₁ φ₂ e' U' d')
    {y : M} (hye : y ∈ e.val.source) (hye' : y ∈ e'.val.source) (hyU : e.val y ∈ U)
    (hyU' : e'.val y ∈ U') : d (e.val y) = d' (e'.val y) := by
  set Q : Set M := (e.val.source ∩ e.val ⁻¹' U) ∩ (e'.val.source ∩ e'.val ⁻¹' U') with hQdef
  have hQo : IsOpen Q :=
    (e.val.isOpen_inter_preimage hd.1).inter (e'.val.isOpen_inter_preimage hd'.1)
  have hc : ContinuousOn (fun y => d (e.val y)) Q :=
    hd.2.2.1.continuousOn.comp (e.val.continuousOn.mono fun y hy => hy.1.1) fun y hy => hy.1.2
  have hc' : ContinuousOn (fun y => d' (e'.val y)) Q :=
    hd'.2.2.1.continuousOn.comp (e'.val.continuousOn.mono fun y hy => hy.2.1) fun y hy => hy.2.2
  have hyQ : y ∈ Q := ⟨⟨hye, hyU⟩, ⟨hye', hyU'⟩⟩
  by_contra hne
  have hopen : IsOpen (Q ∩ {y | d (e.val y) ≠ d' (e'.val y)}) := by
    have := (hc.prodMk hc').isOpen_inter_preimage hQo (isClosed_diagonal (X := ℝ)).isOpen_compl
    simpa [Set.preimage, Set.diagonal] using this
  obtain ⟨y', hy'U, hy'⟩ := h₂.2 y _ hopen ⟨hyQ, hne⟩
  apply hy'U.2
  have h1 := hd.2.2.2.2 (e.val y') hy'U.1.1.2
  have h2 := hd'.2.2.2.2 (e'.val y') hy'U.1.2.2
  rw [e.val.left_inv hy'U.1.1.1] at h1
  rw [e'.val.left_inv hy'U.1.2.1] at h2
  have htop : φ₂ y' ≠ ⊤ := h₂.1.quasiPlurisubharmonic.ne_top y'
  rw [h1] at h2
  rw [← EReal.coe_toReal htop hy', ← EReal.coe_add, ← EReal.coe_add] at h2
  have := EReal.coe_injective h2
  linarith

end Difference

/-! ### No logarithmic poles along the hypersurface part of `E` -/

section Poles

/-- **Non-divisoriality along `E` gives `SparseLogPoles`.**  Let `T = θ + ddᶜφ` have vanishing
generic Lelong number along every prime divisor contained in the analytic set `E`.  In the chart
at `x`, at a regular point `z` of the divisor of `g` near which `E` is the zero set of `g`, the
set `E` is regular of codimension one at `e⁻¹ z` and the closure of the corresponding connected
component of its regular locus is a prime divisor `D ⊆ E`; by Siu's semicontinuity theorem
(`exists_mem_inter_lt_currentLelong`) points of `D` with Lelong number `< a / 2` accumulate at
`e⁻¹ z`, and there the corrected potential has Lelong number `< a`, hence no logarithmic pole of
order `a`. -/
theorem sparseLogPoles_of_genericLelong [CompactSpace M] {T : Cur}
    (hT : SGPT.Siu.IsClosedPositiveCurrent T) {θ : SmoothRealForm (m + 1) M 2} {φ : M → EReal}
    {hφ : IsThetaPshPotential θ φ} (hTeq : T = thetaPotentialCurrent θ φ hφ) {E : Set M}
    (hE : IsComplexAnalyticSubset (n := m + 1) E)
    (hν : ∀ D : Prime, D.val ⊆ E → SGPT.Siu.currentGenericLelong T hT D = 0) (x : M)
    {Ω : Set (ComplexModel (m + 1))} (hΩ : IsOpen Ω)
    (hΩe : Ω ⊆ (complexChartAt (n := m + 1) x).val.target) {ρ : ComplexModel (m + 1) → ℝ}
    (hρ : ContinuousOn ρ Ω) {g : ComplexModel (m + 1) → ℂ}
    (hgE : ∀ z ∈ Ω, (complexChartAt (n := m + 1) x).val.symm z ∈ E → g z = 0) :
    SparseLogPoles (fun z => chartFunction φ (complexChartAt (n := m + 1) x) z + (ρ z : EReal))
      g {z | z ∈ Ω ∧ (complexChartAt (n := m + 1) x).val.symm z ∈ E} := by
  classical
  set e := complexChartAt (n := m + 1) x with hedef
  intro z hzA hPn hloc a ha O hO
  obtain ⟨P⟩ := hPn
  have hzt : z ∈ e.val.target := hΩe hzA.1
  set y := e.val.symm z with hydef
  have hys : y ∈ e.val.source := e.val.map_target hzt
  have hyE : y ∈ E := hzA.2
  -- a neighbourhood of `z` on which `E` is the zero set of `P.h`
  obtain ⟨N, hNsub, hNo, hzN⟩ := _root_.mem_nhds_iff.mp
    (inter_mem (inter_mem (P.isOpen.mem_nhds P.mem) (hΩ.mem_nhds hzA.1)) hloc)
  have hminor : ∃ j : Fin (m + 1),
      fderiv ℂ P.h z (AnalyticJacobianSingularCore.coordinateDirection j) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply P.dh_ne z P.mem
    apply ContinuousLinearMap.coe_injective
    apply (EuclideanSpace.basisFun (Fin (m + 1)) ℂ).toBasis.ext
    intro j
    simpa [AnalyticJacobianSingularCore.coordinateDirection] using hcon j
  obtain ⟨j, hj⟩ := hminor
  have hregModel : RegularAtDim (n := m + 1) (M := ComplexModel (m + 1))
      (e.val.target ∩ e.val.symm ⁻¹' E) (e.val y) (m + 1 - 1) := by
    rw [hydef, e.val.right_inv hzt]
    refine AnalyticJacobianCriterion.regularAtDim_of_localHypersurfaceMinor_ne_zero P.h hNo
      (by simpa [complexChartAt, chartAt_self_eq] using hzN)
      (by simp [complexChartAt, chartAt_self_eq])
      (P.h_diff.mono (fun w hw => (hNsub hw).1.1)) ?_ ⟨hzt, hyE⟩ j
      (by simpa [complexChartAt, chartAt_self_eq] using hj)
    intro y' _ hy'N
    simp only [complexChartAt, chartAt_self_eq, OpenPartialHomeomorph.refl_apply, id] at hy'N ⊢
    have hy'U := (hNsub hy'N).1.1
    have hy'Ω := (hNsub hy'N).1.2
    rw [← P.g_eq_zero_iff hy'U]
    constructor
    · rintro ⟨-, hy'E⟩; exact hgE y' hy'Ω hy'E
    · intro hg'; exact ⟨hΩe hy'Ω, ((hNsub hy'N).2 hg').2⟩
  have hreg : RegularAtDim (n := m + 1) E y m := by
    have := LocalStatementConnected.ConnectedParts.regularAtDim_of_chart (p := x) hys hregModel
    simpa using this
  -- the prime divisor through `y`
  set C := RegularLocusComponent.component (n := m + 1) E y with hCdef
  have hyC : y ∈ C := RegularLocusComponent.mem_component_self hreg
  let V : ClosedIrreducibleAnalyticSubvariety (m + 1) M :=
    { carrier := closure C
      isClosed_carrier := isClosed_closure
      irreducible_carrier :=
        RegularLocusComponent.isComplexAnalyticallyIrreducible_closure_component hE hreg
      dim := m
      dim_le := by omega
      regularLocus_nonempty := ⟨y, RegularLocusComponent.regularAtDim_closure_component hreg hyC⟩ }
  let D : Prime := ⟨closure C, V, rfl, rfl⟩
  have hDE : D.val ⊆ E := closure_minimal (RegularLocusComponent.component_subset E y) hE.isClosed
  have hyD : y ∈ D.val := subset_closure hyC
  -- a point of `D` near `y` with small Lelong number
  obtain ⟨O₀, hO₀sub, hO₀o, hzO₀⟩ := _root_.mem_nhds_iff.mp (inter_mem hO (hΩ.mem_nhds hzA.1))
  set O' : Set M := e.val.source ∩ e.val ⁻¹' O₀ with hO'def
  have hO'o : IsOpen O' := e.val.isOpen_inter_preimage hO₀o
  have hyO' : y ∈ O' := ⟨hys, by
    change e.val (e.val.symm z) ∈ O₀
    rw [e.val.right_inv hzt]; exact hzO₀⟩
  have hc : SGPT.Siu.currentGenericLelong T hT D < ENNReal.ofReal (a / 2) := by
    rw [hν D hDE]; exact ENNReal.ofReal_pos.mpr (by positivity)
  obtain ⟨x', ⟨hx'D, hx'O'⟩, hx'ν⟩ :=
    SGPT.Siu.exists_mem_inter_lt_currentLelong hT D hc hO'o ⟨y, hyD, hyO'⟩
  have hx's : x' ∈ e.val.source := hx'O'.1
  refine ⟨e.val x', ⟨(hO₀sub hx'O'.2).1, (hO₀sub hx'O'.2).2, ?_⟩, ?_⟩
  · show e.val.symm (e.val x') ∈ E
    rw [e.val.left_inv hx's]; exact hDE hx'D
  intro C' hC'
  have hz'Ω : e.val x' ∈ Ω := (hO₀sub hx'O'.2).2
  have hρc : ContinuousAt ρ (e.val x') := hρ.continuousAt (hΩ.mem_nhds hz'Ω)
  have hlel : lelongNumber (n := m + 1)
      (fun z => chartFunction φ e z + (ρ z : EReal)) (e.val x') =
      2 * squaredLogLelongNumber (n := m + 1) φ x' := by
    rw [LelongChartReaderInvariance.lelongNumber_add_continuous_eq hρc,
      LelongChartReaderInvariance.lelongNumber_chartFunction_eq e hx's,
      lelongNumber_eq_two_mul_squaredLog (Nat.succ_ne_zero m)]
  have hge : ENNReal.ofReal a ≤ lelongNumber (n := m + 1)
      (fun z => chartFunction φ e z + (ρ z : EReal)) (e.val x') := by
    unfold lelongNumber
    refine le_iSup₂_of_le (a.toNNReal) ⟨C', ?_⟩ le_rfl
    simpa [complexChartAt, chartAt_self_eq, Real.coe_toNNReal _ ha.le] using hC'
  have hcl := congrFun (SGPT.Siu.currentLelong_eq_of_eq_thetaPotentialCurrent hT hTeq) x'
  rw [hcl] at hx'ν
  rw [hlel] at hge
  have h2 : 2 * squaredLogLelongNumber (n := m + 1) φ x' < 2 * ENNReal.ofReal (a / 2) :=
    ENNReal.mul_lt_mul_right (by norm_num) (by norm_num) hx'ν
  have h3 : 2 * ENNReal.ofReal (a / 2) = ENNReal.ofReal a := by
    rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
    congr 1; ring
  rw [h3] at h2
  exact absurd hge (not_le.mpr h2)

end Poles

/-! ### The comparison theorem -/

section Comparison

/-- The identity theorem on a ball: a holomorphic function not vanishing identically near the
centre vanishes identically near no point. -/
theorem frequently_ne_zero_of_ball {n : ℕ} {f : ComplexModel n → ℂ} {z0 : ComplexModel n}
    {r : ℝ} (hf : DifferentiableOn ℂ f (ball z0 r)) (hi : ∃ᶠ z in 𝓝 z0, f z ≠ 0) :
    ∀ y ∈ ball z0 r, ∃ᶠ z in 𝓝 y, f z ≠ 0 := by
  intro y hy
  by_contra hcon
  rw [Filter.not_frequently] at hcon
  have hy0 : ∀ᶠ z in 𝓝 y, f z = 0 := hcon.mono fun z hz => not_not.mp hz
  have hr : 0 < r := pos_of_mem_ball hy
  have hzero := RiemannExtension.eventually_eq_zero_of_eventually_eq_zero
    isOpen_ball (convex_ball z0 r).isPreconnected hf hy hy0 z0 (mem_ball_self hr)
  exact hi (hzero.mono fun z hz => not_not.mpr hz)

theorem ae_chart_notMem_of_analytic {E : Set M} (hE : IsComplexAnalyticSubset (n := m + 1) E)
    (hEi : interior E = ∅) (e : ComplexChart (m + 1) M) :
    ∀ᵐ z ∂(volume.restrict (e.val.target)), e.val.symm z ∉ E := by
  have hnull := (ModificationMassInvariance.manifoldLocallyPluripolar_of_isComplexAnalyticSubset
    hE hEi).chart_measure_eq_zero e volume
  rw [ae_restrict_iff' e.val.open_target.measurableSet]
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with z hz hzt hzE
  exact hz ⟨hzt, hzE⟩

/-- **The comparison theorem.**  Let `T₁, T₂` be closed positive `(1,1)`-currents on a compact
complex manifold which agree off a closed analytic subset `E` with empty interior.  If `T₂` has
vanishing generic Lelong number along every prime divisor contained in `E`, then `T₁ - T₂` is a
closed positive `(1,1)`-current. -/
theorem isClosedPositiveCurrent_sub_of_currentEqOn [CompactSpace M] {T₁ T₂ : Cur}
    (h₁ : SGPT.Siu.IsClosedPositiveCurrent T₁) (h₂ : SGPT.Siu.IsClosedPositiveCurrent T₂)
    {E : Set M} (hE : IsComplexAnalyticSubset (n := m + 1) E) (hEi : interior E = ∅)
    (heq : CurrentEqOn T₁ T₂ Eᶜ)
    (hν : ∀ D : Prime, D.val ⊆ E → SGPT.Siu.currentGenericLelong T₂ h₂ D = 0) :
    SGPT.Siu.IsClosedPositiveCurrent (T₁ - T₂) := by
  classical
  obtain ⟨σ₁, φ₁, hφ₁, hT₁⟩ := h₁.exists_thetaPotential
  obtain ⟨σ₂, φ₂, hφ₂, hT₂⟩ := h₂.exists_thetaPotential
  have hEc : IsClosed E := hE.isClosed
  have heq' : CurrentEqOn (thetaPotentialCurrent σ₁.val φ₁ hφ₁)
      (thetaPotentialCurrent σ₂.val φ₂ hφ₂) Eᶜ := by
    rw [← hT₁, ← hT₂]; exact heq
  -- the difference `v = φ₁ - φ₂` off `E`
  have hloc : ∀ y, y ∉ E → ∃ U d, (complexChartAt (n := m + 1) y).val y ∈ U ∧
      U ⊆ (complexChartAt (n := m + 1) y).val.symm ⁻¹' Eᶜ ∧
      IsLocalDifference σ₁.val σ₂.val φ₁ φ₂ (complexChartAt (n := m + 1) y) U d := fun y hy =>
    exists_local_difference hφ₁ hφ₂ hEc.isOpen_compl heq' _
      ((complexChartAt (n := m + 1) y).val.map_source (mem_complexChartAt_source y))
      (by rw [(complexChartAt (n := m + 1) y).val.left_inv (mem_complexChartAt_source y)]; exact hy)
  choose! Uf df hUf hUfE hdf using hloc
  set v : M → ℝ := fun y => df y ((complexChartAt (n := m + 1) y).val y) with hvdef
  have hv_eq : ∀ (e : ComplexChart (m + 1) M) (U : Set (ComplexModel (m + 1)))
      (d : ComplexModel (m + 1) → ℝ), IsLocalDifference σ₁.val σ₂.val φ₁ φ₂ e U d →
      ∀ z ∈ U, e.val.symm z ∉ E → v (e.val.symm z) = d z := by
    intro e U d hd z hz hzE
    have hz' : z ∈ e.val.target := hd.2.1 hz
    have hye : e.val.symm z ∈ e.val.source := e.val.map_target hz'
    have h := (hdf _ hzE).eq hφ₂ hd (mem_complexChartAt_source _) hye (hUf _ hzE)
      (by rw [e.val.right_inv hz']; exact hz)
    rw [e.val.right_inv hz'] at h
    exact h
  have hφeq : ∀ y, y ∉ E → φ₁ y = φ₂ y + (v y : EReal) := by
    intro y hy
    have := (hdf y hy).2.2.2.2 _ (hUf y hy)
    rwa [(complexChartAt (n := m + 1) y).val.left_inv (mem_complexChartAt_source y)] at this
  -- `v` is `(θ₁ - θ₂)`-pluriharmonic off `E`
  have hoff : ThetaPshCodimTwoExtension.ThetaPshOff (σ₁ - σ₂).val E (fun y => (v y : EReal)) := by
    intro e z hz hzE
    obtain ⟨U, d, hzU, hUE, hd⟩ := exists_local_difference hφ₁ hφ₂ hEc.isOpen_compl heq' e hz hzE
    refine ⟨U, fun y => -d y, hzU, ⟨hd.1, hd.2.1, hd.2.2.1.neg, fun y hy => ?_⟩, ?_⟩
    · rw [smoothDDC_neg hd.1 hd.2.2.1 hy, hd.2.2.2.1 y hy, BlowupBigPullback.coeff_sub, neg_sub]
    · have hzero : PlurisubharmonicOn (fun _ : ComplexModel (m + 1) => (0 : EReal)) U :=
        fun y _ => plurisubharmonicAt_const 0 EReal.zero_ne_top y
      intro y hy
      refine (hzero y hy).congr ?_
      filter_upwards [hd.1.mem_nhds hy] with w hw
      simp only [chartFunction]
      rw [hv_eq e U d hd w hw (hUE hw), ← EReal.coe_add, add_neg_cancel, EReal.coe_zero]
  -- `v` is locally bounded above near `E`
  have hbound : PshAnalyticSetExtension.LocallyBoundedAboveOff E (fun y => (v y : EReal)) := by
    intro x
    by_cases hx : x ∉ E
    · have husc := ThetaPshCodimTwoExtension.upperSemicontinuousAt_of_thetaPshOff hoff hx
      obtain ⟨q, hq, -⟩ := EReal.exists_rat_btwn_of_lt (EReal.coe_lt_top (v x))
      exact ⟨_, husc _ hq, q, fun y hy _ => hy.le⟩
    push Not at hx
    set e := complexChartAt (n := m + 1) x with hedef
    have hxs : x ∈ e.val.source := mem_complexChartAt_source x
    set z0 := e.val x with hz0def
    have hz0 : z0 ∈ e.val.target := e.val.map_source hxs
    obtain ⟨W₁, ρ₁, hzW₁, hpot₁, hpsh₁⟩ := hφ₁.1 e z0 hz0
    obtain ⟨W₂, ρ₂, hzW₂, hpot₂, hpsh₂⟩ := hφ₂.1 e z0 hz0
    obtain ⟨P⟩ := hE x
    -- a local equation not vanishing identically near `z0`
    have hgen : ∃ i, ∃ᶠ z in 𝓝 z0, P.generator i z ≠ 0 := by
      by_contra hcon
      push Not at hcon
      have hall : ∀ᶠ z in 𝓝 z0, ∀ i, P.generator i z = 0 := by
        rw [Filter.eventually_all]
        intro i
        exact hcon i
      have hxint : x ∈ interior E := by
        rw [mem_interior_iff_mem_nhds]
        have hcx : ContinuousAt e.val x := e.val.continuousAt hxs
        filter_upwards [hcx.preimage_mem_nhds hall, e.val.open_source.mem_nhds hxs,
          hcx.preimage_mem_nhds (P.isOpen_coordinateNeighborhood.mem_nhds
            P.center_mem_coordinateNeighborhood)] with y hy hys hyN
        exact (P.zeroLocus hys hyN).mpr hy
      rw [hEi] at hxint
      exact hxint
    obtain ⟨i, hi⟩ := hgen
    set g := P.generator i with hgdef
    have hdom : W₁ ∩ W₂ ∩ P.coordinateNeighborhood ∈ 𝓝 z0 :=
      inter_mem (inter_mem (hpot₁.1.mem_nhds hzW₁) (hpot₂.1.mem_nhds hzW₂))
        (P.isOpen_coordinateNeighborhood.mem_nhds P.center_mem_coordinateNeighborhood)
    obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp hdom
    set Ω : Set (ComplexModel (m + 1)) := ball z0 r with hΩdef
    have hΩ1 : Ω ⊆ W₁ := fun z hz => (hrsub hz).1.1
    have hΩ2 : Ω ⊆ W₂ := fun z hz => (hrsub hz).1.2
    have hΩN : Ω ⊆ P.coordinateNeighborhood := fun z hz => (hrsub hz).2
    have hΩe : Ω ⊆ e.val.target := hΩ1.trans hpot₁.2.1
    have hg : DifferentiableOn ℂ g Ω := (P.generator_holomorphic i).mono hΩN
    have hg0 : ∀ y ∈ Ω, ∃ᶠ z in 𝓝 y, g z ≠ 0 := frequently_ne_zero_of_ball hg hi
    set A : Set (ComplexModel (m + 1)) := {z | z ∈ Ω ∧ e.val.symm z ∈ E} with hAdef
    have hgE : ∀ z ∈ Ω, e.val.symm z ∈ E → g z = 0 := by
      intro z hz hzE
      have hzt : z ∈ e.val.target := hΩe hz
      have h := (P.zeroLocus (y := e.val.symm z) (e.val.map_target hzt)
        (by rw [e.val.right_inv hzt]; exact hΩN hz)).mp hzE i
      rwa [e.val.right_inv hzt] at h
    have hAg : ∀ z ∈ A, g z = 0 := fun z hz => hgE z hz.1 hz.2
    have hΩA : Ω \ A = Ω ∩ (e.val.target ∩ e.val.symm ⁻¹' Eᶜ) := by
      ext z
      simp only [hAdef, Set.mem_sdiff, mem_inter_iff, mem_preimage, mem_compl_iff]
      constructor
      · rintro ⟨hz, hzA⟩; exact ⟨hz, hΩe hz, fun h => hzA ⟨hz, h⟩⟩
      · rintro ⟨hz, -, hzE⟩; exact ⟨hz, fun h => hzE h.2⟩
    have hAo : IsOpen (Ω \ A) := by
      rw [hΩA]; exact isOpen_ball.inter (e.val.isOpen_inter_preimage_symm hEc.isOpen_compl)
    -- the two local potentials
    set u₁ : ComplexModel (m + 1) → EReal := fun z => chartFunction φ₁ e z + (ρ₁ z : EReal)
    set u₂ : ComplexModel (m + 1) → EReal := fun z => chartFunction φ₂ e z + (ρ₂ z : EReal)
    have hu₁ : PlurisubharmonicOn u₁ Ω := hpsh₁.mono hΩ1
    have hu₂ : PlurisubharmonicOn u₂ Ω := hpsh₂.mono hΩ2
    have hne : ∀ {φ : M → EReal} {ρ : ComplexModel (m + 1) → ℝ}, LocallyNondegenerate φ →
        ∃ a ∈ Ω, chartFunction φ e a + (ρ a : EReal) ≠ ⊥ := by
      intro φ ρ hφ
      obtain ⟨y, hy, hyb⟩ := hφ.exists_chart_ne_bot e isOpen_ball hΩe (mem_ball_self hr)
      exact ⟨y, hy, EReal.add_ne_bot_iff.mpr ⟨hyb, EReal.coe_ne_bot _⟩⟩
    have hi₁ := hu₁.locallyIntegrableOn_toReal volume (convex_ball z0 r).isPreconnected
      (hne hφ₁.2)
    have hi₂ := hu₂.locallyIntegrableOn_toReal volume (convex_ball z0 r).isPreconnected
      (hne hφ₂.2)
    have hf₁ : ∀ᵐ z ∂volume.restrict Ω, u₁ z ≠ ⊥ :=
      (hu₁.ae_finite volume (convex_ball z0 r).isPreconnected (hne hφ₁.2)).mono fun z hz => hz.2
    have hf₂ : ∀ᵐ z ∂volume.restrict Ω, u₂ z ≠ ⊥ :=
      (hu₂.ae_finite volume (convex_ball z0 r).isPreconnected (hne hφ₂.2)).mono fun z hz => hz.2
    -- the pluriharmonic difference in the chart
    set h : ComplexModel (m + 1) → ℝ := fun z => v (e.val.symm z) + ρ₁ z - ρ₂ z with hhdef
    have hhloc : ∀ z ∈ Ω \ A, ∃ U' : Set (ComplexModel (m + 1)), IsOpen U' ∧ z ∈ U' ∧
        U' ⊆ Ω \ A ∧ ContDiffOn ℝ ∞ h U' ∧ ∀ y ∈ U', smoothDDC h y = 0 := by
      intro z hz
      have hzt : z ∈ e.val.target := hΩe hz.1
      have hzE : e.val.symm z ∉ E := fun hE' => hz.2 ⟨hz.1, hE'⟩
      obtain ⟨U, d, hzU, hUE, hd⟩ :=
        exists_local_difference hφ₁ hφ₂ hEc.isOpen_compl heq' e hzt hzE
      set U' := U ∩ (Ω \ A) with hU'def
      have hU'o : IsOpen U' := hd.1.inter hAo
      have hdeq : EqOn h (fun y => d y + ρ₁ y - ρ₂ y) U' := by
        intro y hy
        simp only [hhdef]
        rw [hv_eq e U d hd y hy.1 (hUE hy.1)]
      have hsm : ContDiffOn ℝ ∞ (fun y => d y + ρ₁ y - ρ₂ y) U' :=
        ((hd.2.2.1.mono inter_subset_left).add (hpot₁.2.2.1.mono fun y hy => hΩ1 hy.2.1)).sub
          (hpot₂.2.2.1.mono fun y hy => hΩ2 hy.2.1)
      refine ⟨U', hU'o, ⟨hzU, hz⟩, inter_subset_right, hsm.congr hdeq, fun y hy => ?_⟩
      have hev : h =ᶠ[𝓝 y] fun y => d y + ρ₁ y - ρ₂ y := by
        filter_upwards [hU'o.mem_nhds hy] with w hw
        exact hdeq hw
      rw [smoothDDC_congr hev]
      have h1 : ContDiffOn ℝ ∞ d U' := hd.2.2.1.mono inter_subset_left
      have h2 : ContDiffOn ℝ ∞ ρ₁ U' := hpot₁.2.2.1.mono fun y hy => hΩ1 hy.2.1
      have h3 : ContDiffOn ℝ ∞ ρ₂ U' := hpot₂.2.2.1.mono fun y hy => hΩ2 hy.2.1
      rw [PositiveClasses.smoothDDC_sub hU'o (h1.add h2) h3 hy, smoothDDC_add hU'o h1 h2 hy,
        hd.2.2.2.1 y hy.1, hpot₁.2.2.2 (hΩ1 hy.2.1), hpot₂.2.2.2 (hΩ2 hy.2.1)]
      abel
    have hhc : ContinuousOn h (Ω \ A) := by
      intro z hz
      obtain ⟨U', hU'o, hzU', -, hsm, -⟩ := hhloc z hz
      exact (hsm.continuousOn.continuousAt (hU'o.mem_nhds hzU')).continuousWithinAt
    have hhp : PlurisubharmonicOn (fun z => (h z : EReal)) (Ω \ A) := by
      intro z hz
      obtain ⟨U', hU'o, hzU', -, hsm, hddc⟩ := hhloc z hz
      exact plurisubharmonicOn_coe_of_smoothDDC_eq_zero hU'o hsm hddc z hzU'
    have hhn : PlurisubharmonicOn (fun z => ((-h z : ℝ) : EReal)) (Ω \ A) := by
      intro z hz
      obtain ⟨U', hU'o, hzU', -, hsm, hddc⟩ := hhloc z hz
      refine plurisubharmonicOn_coe_of_smoothDDC_eq_zero hU'o hsm.neg (fun y hy => ?_) z hzU'
      rw [smoothDDC_neg hU'o hsm hy, hddc y hy, neg_zero]
    have heqloc : ∀ z ∈ Ω \ A, u₁ z = u₂ z + (h z : EReal) := by
      intro z hz
      have hzE : e.val.symm z ∉ E := fun hE' => hz.2 ⟨hz.1, hE'⟩
      simp only [u₁, u₂, hhdef, chartFunction]
      rw [hφeq _ hzE]
      generalize φ₂ (e.val.symm z) = a
      induction a using EReal.rec with
      | bot => simp only [EReal.bot_add]
      | top => simp only [EReal.top_add_coe]
      | coe a =>
        rw [← EReal.coe_add, ← EReal.coe_add, ← EReal.coe_add, ← EReal.coe_add]
        congr 1
        ring
    have hsp := sparseLogPoles_of_genericLelong h₂ hT₂ hE hν x isOpen_ball hΩe
      (hpot₂.2.2.1.continuousOn.mono hΩ2) hgE
    obtain ⟨U, hU, C, hC⟩ := exists_nhds_le_of_eq_add isOpen_ball hu₁ hu₂ hi₁ hi₂ hf₁ hf₂ hg hg0
      hAg hAo hhc hhp hhn heqloc hsp (mem_ball_self hr)
    -- back on the manifold
    have hρ₁c : ContinuousAt ρ₁ z0 :=
      (hpot₁.2.2.1.continuousOn _ hzW₁).continuousAt (hpot₁.1.mem_nhds hzW₁)
    have hρ₂c : ContinuousAt ρ₂ z0 :=
      (hpot₂.2.2.1.continuousOn _ hzW₂).continuousAt (hpot₂.1.mem_nhds hzW₂)
    set Uc : Set (ComplexModel (m + 1)) :=
      U ∩ Ω ∩ {z | ρ₁ z0 - 1 < ρ₁ z} ∩ {z | ρ₂ z < ρ₂ z0 + 1} with hUcdef
    have hUc : Uc ∈ 𝓝 z0 :=
      inter_mem (inter_mem (inter_mem hU (isOpen_ball.mem_nhds (mem_ball_self hr)))
        (hρ₁c.eventually (lt_mem_nhds (by linarith))))
        (hρ₂c.eventually (gt_mem_nhds (by linarith)))
    refine ⟨e.val.source ∩ e.val ⁻¹' Uc,
      inter_mem (e.val.open_source.mem_nhds hxs) ((e.val.continuousAt hxs).preimage_mem_nhds hUc),
      C - (ρ₁ z0 - 1) + (ρ₂ z0 + 1), fun y hy hyE => ?_⟩
    have hys : y ∈ e.val.source := hy.1
    have hyU : e.val y ∈ Uc := hy.2
    have hyΩA : e.val y ∈ Ω \ A := ⟨hyU.1.1.2, fun h' => hyE (by
      have := h'.2; rwa [e.val.left_inv hys] at this)⟩
    have hb := hC _ hyU.1.1.1 hyΩA
    simp only [hhdef, e.val.left_inv hys] at hb
    have h1 : ρ₁ z0 - 1 < ρ₁ (e.val y) := hyU.1.2
    have h2 : ρ₂ (e.val y) < ρ₂ z0 + 1 := hyU.2
    exact EReal.coe_le_coe_iff.mpr (by linarith)
  -- the extension across `E`
  have hW : IsThetaPshPotential (σ₁ - σ₂).val
      (ThetaPshCodimTwoExtension.extensionAcross E (fun y => (v y : EReal))) := by
    have hWeq : ∀ y, y ∉ E →
        ThetaPshCodimTwoExtension.extensionAcross E (fun y => (v y : EReal)) y = (v y : EReal) :=
      fun y hy => ThetaPshCodimTwoExtension.extensionAcross_eq_of_notMem hEc hoff hy
    refine ⟨?_, ?_⟩
    · rcases isEmpty_or_nonempty M with hM | hM
      · intro e z hz
        exact isEmptyElim (e.val.symm z)
      · have hEne : E ≠ univ := by
          intro hEu
          obtain ⟨x⟩ := hM
          have : x ∈ interior E := by rw [hEu, interior_univ]; exact mem_univ x
          rw [hEi] at this; exact this
        exact PshAnalyticSetExtension.thetaPlurisubharmonic_extensionAcross_of_localClosure hEc hoff
          (PshAnalyticRemovable.analyticRemovableThetaPsh_of_closed (σ₁ - σ₂) E _ hE hEne hoff
            hbound)
    · intro x U hU hxU
      have hnot : ¬ U ⊆ E := by
        intro hsub
        have : x ∈ interior E := interior_maximal hsub hU hxU
        rw [hEi] at this; exact this
      obtain ⟨y, hyU, hyE⟩ := not_subset.mp hnot
      exact ⟨y, hyU, by rw [hWeq y hyE]; exact EReal.coe_ne_bot _⟩
  obtain ⟨hsum, hsum_eq⟩ := SGPT.Okounkov.exists_thetaPotentialCurrent_add hW hφ₂
  have hcongr : thetaPotentialCurrent ((σ₁ - σ₂) + σ₂).val
      (fun x => ThetaPshCodimTwoExtension.extensionAcross E (fun y => (v y : EReal)) x + φ₂ x)
      hsum = thetaPotentialCurrent σ₁.val φ₁ hφ₁ := by
    apply SGPT.Siu.thetaPotentialCurrent_congr_ae (by rw [sub_add_cancel])
    intro e
    filter_upwards [ae_chart_notMem_of_analytic hE hEi e] with z hz
    simp only [chartFunction]
    rw [ThetaPshCodimTwoExtension.extensionAcross_eq_of_notMem hEc hoff hz, hφeq _ hz, add_comm]
  have hTid : T₁ - T₂ = thetaPotentialCurrent (σ₁ - σ₂).val
      (ThetaPshCodimTwoExtension.extensionAcross E (fun y => (v y : EReal))) hW := by
    rw [hT₁, ← hcongr, hsum_eq, ← hT₂]
    abel
  rw [hTid]
  exact SGPT.Siu.isClosedPositiveCurrent_thetaPotentialCurrent _ _ _

end Comparison

/-! ### Consequences: equality and the support theorem -/

section Support

theorem restrictChart_zero (e : ComplexChart (m + 1) M) {D : Opens (ComplexModel (m + 1))}
    (hD : D ≤ chartTarget e) : (0 : Cur).restrictChart e hD = 0 := by
  ext; rfl

/-- **Lelong numbers are local**: a closed positive current vanishing near `x` has `ν(R, x) = 0`. -/
theorem currentLelong_eq_zero_of_currentEqOn_zero {R : Cur}
    (hR : SGPT.Siu.IsClosedPositiveCurrent R) {O : Set M} (h0 : CurrentEqOn R 0 O) {x : M}
    (hx : x ∈ O) : SGPT.Siu.currentLelong R hR x = 0 := by
  set e := complexChartAt (n := m + 1) x with hedef
  have hxs : x ∈ e.val.source := mem_complexChartAt_source x
  obtain ⟨D, hzD, hD, hres⟩ := h0 e (e.val x) (e.val.map_source hxs)
    (by rw [e.val.left_inv hxs]; exact hx)
  have hR0 : R.restrictChart e hD = 0 := by rw [hres]; exact restrictChart_zero e hD
  exact SGPT.Siu.currentLelong_eq_zero_of_chartSpanCurrent_eq_zero hR e D hD
    (fun γ ψ hψ => chartSpanCurrent_eq_zero_of_restrictChart e hD hR0 γ ψ hψ) hxs hzD

/-- **Equality off an analytic set.**  Two closed positive `(1,1)`-currents on a compact complex
manifold which agree off a closed analytic subset `E` with empty interior, and which both have
vanishing generic Lelong numbers along the prime divisors contained in `E`, are equal. -/
theorem eq_of_currentEqOn [CompactSpace M] {T₁ T₂ : Cur}
    (h₁ : SGPT.Siu.IsClosedPositiveCurrent T₁) (h₂ : SGPT.Siu.IsClosedPositiveCurrent T₂)
    {E : Set M} (hE : IsComplexAnalyticSubset (n := m + 1) E) (hEi : interior E = ∅)
    (heq : CurrentEqOn T₁ T₂ Eᶜ)
    (hν₁ : ∀ D : Prime, D.val ⊆ E → SGPT.Siu.currentGenericLelong T₁ h₁ D = 0)
    (hν₂ : ∀ D : Prime, D.val ⊆ E → SGPT.Siu.currentGenericLelong T₂ h₂ D = 0) : T₁ = T₂ := by
  have a := isClosedPositiveCurrent_sub_of_currentEqOn h₁ h₂ hE hEi heq hν₂
  have b := isClosedPositiveCurrent_sub_of_currentEqOn h₂ h₁ hE hEi heq.symm hν₁
  have hns : -(T₁ - T₂) = T₂ - T₁ := by abel
  have hz := eq_zero_of_isFullPositive_of_neg a (by rw [hns]; exact b.2.2)
  exact sub_eq_zero.mp hz

/-- The generic Lelong number of a closed positive current vanishing off `E` along a prime
divisor not contained in `E` is zero. -/
theorem currentGenericLelong_eq_zero_of_currentEqOn_zero {R : Cur}
    (hR : SGPT.Siu.IsClosedPositiveCurrent R) {E : Set M} (h0 : CurrentEqOn R 0 Eᶜ) (D : Prime)
    (hD : ¬ D.val ⊆ E) : SGPT.Siu.currentGenericLelong R hR D = 0 := by
  obtain ⟨x, hxD, hxE⟩ := not_subset.mp hD
  exact le_antisymm ((SGPT.Siu.currentGenericLelong_le hR D hxD).trans
    (le_of_eq (currentLelong_eq_zero_of_currentEqOn_zero hR h0 hxE))) bot_le

/-- The regular part of a closed positive current vanishing off `E` vanishes. -/
theorem siuRegularPart_eq_zero_of_currentEqOn_zero [CompactSpace M] {R : Cur}
    (hR : SGPT.Siu.IsClosedPositiveCurrent R) {E : Set M}
    (hE : IsComplexAnalyticSubset (n := m + 1) E) (hEi : interior E = ∅)
    (h0 : CurrentEqOn R 0 Eᶜ) : SGPT.Siu.siuRegularPart R hR = 0 := by
  set Q := SGPT.Siu.siuRegularPart R hR with hQdef
  have hQ := SGPT.Siu.isClosedPositiveCurrent_siuRegularPart hR
  have hRQ : IsFullPositive (R - Q) := by
    have : R - Q = SGPT.Siu.siuDivisorialPart R hR := by
      rw [hQdef, SGPT.Siu.siuRegularPart]; abel
    rw [this]; exact (SGPT.Siu.isClosedPositiveCurrent_siuDivisorialPart hR).2.2
  have hQ0 : CurrentEqOn Q 0 Eᶜ := by
    intro e z hz hzE
    obtain ⟨D, hzD, hD, hres⟩ := h0 e z hz hzE
    refine ⟨D, hzD, hD, ?_⟩
    have hR0 : R.restrictChart e hD = 0 := by rw [hres]; exact restrictChart_zero e hD
    rw [restrictChart_eq_zero_of_le hQ hRQ e hD hR0, restrictChart_zero]
  have hc := isClosedPositiveCurrent_sub_of_currentEqOn (T₁ := 0) (T₂ := Q)
    SGPT.Siu.isClosedPositiveCurrent_zero hQ hE hEi hQ0.symm
    (fun D _ => SGPT.Siu.currentGenericLelong_siuRegularPart hR D)
  have h0Q : (0 : Cur) - Q = -Q := by abel
  exact eq_zero_of_isFullPositive_of_neg hQ (by rw [← h0Q]; exact hc.2.2)

/-- **The support theorem for closed positive `(1,1)`-currents carried by an analytic set**
(Xia, *Foundations of pluripotential theory*, `thm:analytic-order-zero-support`, positive case).
A closed positive `(1,1)`-current `R` on a compact complex manifold vanishing off a closed
analytic subset `E` with empty interior is its divisorial part `∑_D ν(R, D)[D]`
(`siuDivisorialPart`), in which only prime divisors contained in `E` occur. -/
theorem eq_siuDivisorialPart_of_currentEqOn_zero [CompactSpace M] {R : Cur}
    (hR : SGPT.Siu.IsClosedPositiveCurrent R) {E : Set M}
    (hE : IsComplexAnalyticSubset (n := m + 1) E) (hEi : interior E = ∅)
    (h0 : CurrentEqOn R 0 Eᶜ) :
    R = SGPT.Siu.siuDivisorialPart R hR ∧
      ∀ D : Prime, ¬ D.val ⊆ E → SGPT.Siu.currentGenericLelong R hR D = 0 :=
  ⟨sub_eq_zero.mp (siuRegularPart_eq_zero_of_currentEqOn_zero hR hE hEi h0),
    currentGenericLelong_eq_zero_of_currentEqOn_zero hR h0⟩

/-- **Supports of codimension at least two.**  A closed positive `(1,1)`-current vanishing off a
closed analytic subset with empty interior which contains no prime divisor is zero. -/
theorem eq_zero_of_currentEqOn_zero [CompactSpace M] {R : Cur}
    (hR : SGPT.Siu.IsClosedPositiveCurrent R) {E : Set M}
    (hE : IsComplexAnalyticSubset (n := m + 1) E) (hEi : interior E = ∅)
    (hnod : ∀ D : Prime, ¬ D.val ⊆ E) (h0 : CurrentEqOn R 0 Eᶜ) : R = 0 := by
  have hc := isClosedPositiveCurrent_sub_of_currentEqOn (T₁ := 0) (T₂ := R)
    SGPT.Siu.isClosedPositiveCurrent_zero hR hE hEi h0.symm (fun D hD => absurd hD (hnod D))
  have h0R : (0 : Cur) - R = -R := by abel
  exact eq_zero_of_isFullPositive_of_neg hR (by rw [← h0R]; exact hc.2.2)

end Support

/-! ### Finiteness of the prime divisors in an analytic set -/

section Finite

/-- An analytic set regular of full dimension at a point is a neighbourhood of it. -/
theorem mem_nhds_of_regularAtDim_top {A : Set M} {c : M}
    (h : RegularAtDim (n := m + 1) A c (m + 1)) : A ∈ 𝓝 c := by
  obtain ⟨_, _, Φ, _, _, hflat⟩ := h
  have hS : IsOpen ((complexChartAt (n := m + 1) c).val.source ∩
      (complexChartAt (n := m + 1) c).val ⁻¹' Φ.source) :=
    (complexChartAt (n := m + 1) c).val.continuousOn.isOpen_inter_preimage
      (complexChartAt (n := m + 1) c).val.open_source Φ.isOpen_source
  refine mem_of_superset (hS.mem_nhds ⟨mem_complexChartAt_source c, Φ.center_mem_source⟩) ?_
  intro y hy
  refine (hflat hy.1 hy.2).mpr ?_
  intro i hi
  exact absurd i.2 (not_lt.mpr hi)

theorem isComplexAnalyticSubset_biUnion {ι : Type*} (s : Finset ι) {B : ι → Set M}
    (hB : ∀ j, IsComplexAnalyticSubset (n := m + 1) (B j)) :
    IsComplexAnalyticSubset (n := m + 1) (⋃ j ∈ s, B j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.set_biUnion_insert]
      exact ConstantRankImage.IsComplexAnalyticSubset.union (hB a) ih

/-- An irreducible analytic set contained in a finite union of analytic sets lies in one of
them. -/
theorem exists_subset_of_subset_biUnion {ι : Type*} (s : Finset ι) {B : ι → Set M}
    (hB : ∀ j, IsComplexAnalyticSubset (n := m + 1) (B j)) {Z : Set M}
    (hZ : IsComplexAnalyticallyIrreducible (n := m + 1) Z) (hsub : Z ⊆ ⋃ j ∈ s, B j) :
    ∃ j ∈ s, Z ⊆ B j := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      obtain ⟨x, hx⟩ := hZ.2.1
      simpa using hsub hx
  | @insert a s ha ih =>
      rw [Finset.set_biUnion_insert] at hsub
      have hsplit : Z = (Z ∩ B a) ∪ (Z ∩ ⋃ j ∈ s, B j) := by
        ext x
        constructor
        · intro hx
          rcases hsub hx with h | h
          · exact Or.inl ⟨hx, h⟩
          · exact Or.inr ⟨hx, h⟩
        · rintro (h | h) <;> exact h.1
      rcases hZ.2.2 _ _ (hZ.1.inter (hB a)) (hZ.1.inter (isComplexAnalyticSubset_biUnion s hB))
        inter_subset_left inter_subset_left hsplit with h | h
      · exact ⟨a, Finset.mem_insert_self a s, fun x hx => (h ▸ hx : x ∈ Z ∩ B a).2⟩
      · obtain ⟨j, hj, hZj⟩ := ih (fun x hx => (h ▸ hx : x ∈ Z ∩ ⋃ j ∈ s, B j).2)
        exact ⟨j, Finset.mem_insert_of_mem hj, hZj⟩

/-- **Finitely many prime divisors lie in an analytic set** with empty interior of a compact
manifold: each of them is one of its finitely many global irreducible components. -/
theorem finite_setOf_prime_subset [CompactSpace M] {E : Set M}
    (hE : IsComplexAnalyticSubset (n := m + 1) E) (hEi : interior E = ∅) :
    {D : Prime | D.val ⊆ E}.Finite := by
  classical
  obtain ⟨N, B, -, hrange, hB, hU⟩ :=
    ActualCompactAnalyticGlobalComponents.exists_finite_exact_global_components hE
  have hclaim : ∀ D : Prime, D.val ⊆ E → ∃ j, D.val = B j := by
    intro D hD
    obtain ⟨j, -, hj⟩ := exists_subset_of_subset_biUnion Finset.univ (fun j => (hB j).1.1)
      (SGPT.Siu.isIrreducible_primeCarrier D) (by simpa [← hU] using hD)
    refine ⟨j, ?_⟩
    have hjmem : B j ∈ GlobalComponents.globalComponents (n := m + 1) E := hrange ▸ ⟨j, rfl⟩
    obtain ⟨c, ⟨k, hk⟩, hBj⟩ := hjmem
    have hkle : k ≤ m := by
      by_contra hk'
      have hkk : k = m + 1 := le_antisymm hk.1 (by omega)
      rw [hkk] at hk
      have : c ∈ interior E := mem_interior_iff_mem_nhds.mpr (mem_nhds_of_regularAtDim_top hk)
      rw [hEi] at this; exact this
    let V : ClosedIrreducibleAnalyticSubvariety (m + 1) M :=
      { carrier := closure (RegularLocusComponent.component (n := m + 1) E c)
        isClosed_carrier := isClosed_closure
        irreducible_carrier :=
          RegularLocusComponent.isComplexAnalyticallyIrreducible_closure_component hE hk
        dim := k
        dim_le := hk.1
        regularLocus_nonempty := ⟨c, RegularLocusComponent.regularAtDim_closure_component hk
          (RegularLocusComponent.mem_component_self hk)⟩ }
    have hkge : m ≤ k := by
      obtain ⟨x, hx⟩ := SGPT.Siu.exists_regularAtDim_primeCarrier D
      have hloc := DimensionMonotone.locDimGE_of_regularAtDim_subset V.analytic
        (by rw [hBj] at hj; exact hj) hx
      obtain ⟨y, -, k', hk', hy⟩ := hloc univ univ_mem
      have := AnalyticIrreducibleComponents.eq_dim_of_regularAtDim V hy
      change k' = k at this
      omega
    have hkm : k = m := le_antisymm hkle hkge
    let P : Prime := ⟨B j, V, hBj.symm, by change k + 1 = m + 1; omega⟩
    exact congrArg Subtype.val (SGPT.Siu.eq_of_subset (P := D) (Q := P) hj)
  choose f hf using hclaim
  have hfin : Finite {D : Prime // D.val ⊆ E} :=
    Finite.of_injective (fun D => f D.1 D.2) (fun D D' h => Subtype.ext (Subtype.ext (by
      change D.1.val = D'.1.val
      rw [hf D.1 D.2, hf D'.1 D'.2]
      exact congrArg B h)))
  exact Set.finite_coe_iff.mp hfin

end Finite

end SGPT.Currents.AnalyticSupport
