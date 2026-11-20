import SGPT.Foundations.Analysis.Pending.DemaillyApproximationAnalyticType
import SGPT.Foundations.Analysis.Pending.DemaillyChartBranchLimit
import SGPT.Foundations.Analysis.Pending.BergmanWeightConvergence
import SGPT.Foundations.Analysis.Pending.IdealWeightComparison
import SGPT.Foundations.Analysis.Pending.MultiplierIdealBergmanNadelManifold
import SGPT.Foundations.Analysis.Pending.ThetaPshConvexCombination

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The weight of `𝓘(mψ)` dominates `ψ`, at every level `m`

Route F, `F-b` step 4 (plan `scratch/tn23-envelopes-qea-plan-0117.md` §5.2 and §8): for a
`ζ`-psh potential `ψ` on a compact complex manifold of positive dimension, every integer `m ≥ 1`
and every point `x`, a finite family `g` generating the germs of `𝓘(mψ)` at `x` satisfies

    ψ ≤ m⁻¹ log ∑ᵢ |gᵢ|² + C     near `x`.

This is Demailly's lower bound at an ARBITRARY level (the approximating sequence of the tree is
dyadic): the chart Bergman branch `b_{m,j}` of the fixed cover is `≥ ψ - (log C₀)/m` by the
Ohsawa–Takegoshi lower bound (`BergmanWeightConvergence.le_bergmanWeight`) and
`≤ m⁻¹ log ∑|gᵢ|² + C` near `x` (`DemaillyApproximationAnalyticType.exists_branch_le`).

Consumer (next): `Φ_q ≥ ((q+1)/q) V_{θ+εω} - C` from `𝓘((q+1)V_{θ+εω}) ⊆ 𝓘(qV_θ)` (step 3,
TN-CLASSICAL) and the type `(q⁻¹, 𝓘(qV_θ))` of `Φ_q`.  Sorry-free.
-/

open Set Filter Metric MeasureTheory
open scoped Topology Manifold ENNReal

namespace SGPT.Foundations.Analysis.Pending.MultiplierIdealWeightLowerBound

noncomputable section

open FirstPass FirstPass.HolomorphicIdealSheaves FirstPass.GlobalAnalyticSingularities
  QuantitativeRegularizationFixedCover QuantitativeRegularizationChartBranch BergmanSupWeight
  BergmanWeightConvergence QuantitativeRegularizationBergmanInstanceTransport
  DemaillyApproximationAnalyticType

variable {d : ℕ} {Z : Type*} [TopologicalSpace Z] [ChartedSpace (ComplexModel d) Z]
  [IsComplexManifold d Z]

/-- **Demailly's lower bound at level `m`**: near every point, `ψ ≤ m⁻¹ log ∑|gᵢ|² + C` for a
finite family `g` generating the germs of `𝓘(mψ)` there. -/
theorem exists_le_inv_mul_generatorLog [CompactSpace Z] (hd : 0 < d)
    {ζ : ClosedRealOneOneForm d Z} {ψ : Z → EReal} (hψ : IsThetaPshPotential ζ.val ψ)
    {m : ℕ} (hm : 0 < m) (x : Z) {N : ℕ} {g : Fin N → Z → ℂ}
    (hgx : ∀ h, (multiplierIdeal (n := d) (m : ℝ) ψ).mem x h →
      IsInSpanAt (n := d) (· ∈ range g) x h) :
    ∃ C : ℝ, ∀ᶠ y in 𝓝 x, ψ y ≤ (((m : ℝ)⁻¹ : ℝ) : EReal) * generatorLog g y + (C : EReal) := by
  let _ : MeasurableSpace (ComplexModel d) := borel _
  have _ : BorelSpace (ComplexModel d) := ⟨rfl⟩
  obtain ⟨F⟩ := exists_fixedChartCover (Z := Z) hd
  obtain ⟨ρ, hρ⟩ := F.exists_potentials ζ
  obtain ⟨j, hxU⟩ := F.cover.cover x
  have hxV : x ∈ F.cover.V j := F.cover.U_subset_V j hxU
  obtain ⟨C₁, hC₁⟩ := exists_branch_le F hρ hψ.1 hm j (subset_closure hxV) hgx
  -- the Ohsawa–Takegoshi lower bound on the chart ball of the `j`-th patch
  set e := F.chart j with hedef
  set B := ball (F.center j) (F.bergmanRadius j) with hBdef
  have hR : 0 < ‖F.center j‖ + F.bergmanRadius j := by
    have := F.bergmanRadius_pos j
    positivity
  obtain ⟨C₀, hC₀, hOT⟩ := le_bergmanWeight d (‖F.center j‖ + F.bergmanRadius j) hR
  have hpsh : PlurisubharmonicOn (correctedWeight e (ρ j) ψ) B :=
    (plurisubharmonicOn_correctedWeight hψ.1 (hρ j)).mono
      (ball_subset_ball (F.bergmanRadius_lt_potentialRadius j).le)
  have hnorm : ∀ z ∈ B, ‖z‖ < ‖F.center j‖ + F.bergmanRadius j := fun z hz =>
    DemaillyChartBranchLimit.norm_lt_of_mem_ball hz
  have hm1 : 1 ≤ m := hm
  have hlow : ∀ y ∈ F.cover.V j, ψ y ≤ F.branch ρ ψ m j y +
      ((((m : ℝ)⁻¹ * Real.log C₀ : ℝ)) : EReal) := by
    intro y hy
    have hyp : y ∈ chartPatch e B := F.closure_V_subset_chartPatch j (subset_closure hy)
    induction hψy : ψ y using EReal.rec with
    | bot => exact bot_le
    | top => exact absurd hψy (hψ.1.quasiPlurisubharmonic.ne_top y)
    | coe p =>
        have hcw : correctedWeight e (ρ j) ψ (e.val y) = ((p + ρ j (e.val y) : ℝ) : EReal) := by
          simp only [correctedWeight, chartFunction, e.val.left_inv hyp.1, hψy, EReal.coe_add]
        have hb := hOT B isOpen_ball (convex_ball _ _) hnorm (correctedWeight e (ρ j) ψ) hpsh m
          hm1 (e.val y) hyp.2 (p + ρ j (e.val y)) hcw
        have hbr : F.branch ρ ψ m j y =
            bergmanWeight B (correctedWeight e (ρ j) ψ) m (e.val y) +
              ((-ρ j (e.val y) : ℝ) : EReal) := by
          change chartBergmanBranch e B (ρ j) ψ m y = _
          rw [chartBergmanBranch_of_mem hyp, bergmanWeight,
            bergmanLog_congr_instance _ _ (borel (ComplexModel d)) ⟨rfl⟩, sub_eq_add_neg,
            EReal.coe_neg]
        rw [hbr]
        calc ((p : ℝ) : EReal)
            = ((p + ρ j (e.val y) - (m : ℝ)⁻¹ * Real.log C₀ : ℝ) : EReal) +
                ((-ρ j (e.val y) : ℝ) : EReal) + ((((m : ℝ)⁻¹ * Real.log C₀ : ℝ)) : EReal) := by
              rw [← EReal.coe_add, ← EReal.coe_add]
              congr 1
              ring
          _ ≤ bergmanWeight B (correctedWeight e (ρ j) ψ) m (e.val y) +
                ((-ρ j (e.val y) : ℝ) : EReal) + ((((m : ℝ)⁻¹ * Real.log C₀ : ℝ)) : EReal) := by
              gcongr
  refine ⟨C₁ + (m : ℝ)⁻¹ * Real.log C₀, ?_⟩
  filter_upwards [hC₁, (F.cover.isOpen_V j).mem_nhds hxV] with y hy1 hyV
  calc ψ y ≤ F.branch ρ ψ m j y + ((((m : ℝ)⁻¹ * Real.log C₀ : ℝ)) : EReal) := hlow y hyV
    _ ≤ ((((m : ℝ)⁻¹ : ℝ) : EReal) * generatorLog g y + (C₁ : EReal)) +
          ((((m : ℝ)⁻¹ * Real.log C₀ : ℝ)) : EReal) := add_le_add hy1 le_rfl
    _ = (((m : ℝ)⁻¹ : ℝ) : EReal) * generatorLog g y +
          ((C₁ + (m : ℝ)⁻¹ * Real.log C₀ : ℝ) : EReal) := by
        rw [add_assoc, ← EReal.coe_add]

/-- `c(a + r) ≤ c a + c r` bookkeeping: `(c : EReal) * (c' * a) = (c c') * a`. -/
theorem coe_mul_coe_mul (c c' : ℝ) (a : EReal) :
    (c : EReal) * ((c' : EReal) * a) = ((c * c' : ℝ) : EReal) * a := by
  rw [← mul_assoc, ← EReal.coe_mul]

/-- **Route F, `F-b` step 4 (P4b)**: if `𝓘((q+1)ψ) ⊆ 𝔞` and `Φ` has analytic singularities of type
`(q⁻¹, 𝔞)`, then `((q+1)/q) ψ ≤ Φ + C` on the compact manifold.  Locally: `ψ ≤ (q+1)⁻¹ log|h|² + C`
for generators `h` of `𝓘((q+1)ψ)` (`exists_le_inv_mul_generatorLog`), `log|h|² ≤ log|g|² + C` for
generators `g` of `𝔞` (the inclusion), and `Φ = q⁻¹ log|g|² + O(1)`. -/
theorem moreSingularOn_smul_of_multiplierIdeal_le [CompactSpace Z] (hd : 0 < d)
    {ζ : ClosedRealOneOneForm d Z} {ψ : Z → EReal} (hψ : IsThetaPshPotential ζ.val ψ)
    {q : ℕ} (hq : 0 < q) {Φ : Z → EReal} {𝔞 : GermIdeal d Z}
    (hΦ : HasAnalyticSingularitiesOfType (n := d) Φ ((q : ℚ)⁻¹) 𝔞)
    (hle : (multiplierIdeal (n := d) ((q + 1 : ℕ) : ℝ) ψ).Le 𝔞) :
    MoreSingularOn (fun x => ((((q + 1 : ℕ) : ℝ) / q : ℝ) : EReal) * ψ x) Φ univ := by
  refine IdealWeightComparison.moreSingularOn_univ_of_forall_moreSingularAt fun x => ?_
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hq1 : 0 < q + 1 := Nat.succ_pos q
  have hq1R : (0 : ℝ) < ((q + 1 : ℕ) : ℝ) := by exact_mod_cast hq1
  -- the type of `Φ` at `x`
  obtain ⟨-, -, hpres⟩ := hΦ
  obtain ⟨U, hU, hxU, N, g, hgdiff, hgiff, R, C₀, hRb, hΦeq⟩ := hpres x
  -- generators of `𝓘((q+1)ψ)` at `x`
  obtain ⟨U', hU', hxU', P, h, hhdiff, hhiff⟩ :=
    MultiplierIdealBergmanNadelManifold.isCoherent_multiplierIdeal_of_pos hd hψ.1 hq1R x
  obtain ⟨C₁, hC₁⟩ := exists_le_inv_mul_generatorLog hd hψ hq1 x
    (g := h) fun f hf => (hhiff x hxU' f).mp hf
  -- `log|h|² ≤ log|g|² + C₂` near `x`
  have hspan : ∀ i, IsInSpanAt (n := d) (· ∈ range g) x (h i) := fun i =>
    (hgiff x hxU (h i)).mp
      (hle x (h i) (IdealWeightComparison.mem_of_isPresentation hU' hxU' hhdiff hhiff i))
  obtain ⟨C₂, hC₂⟩ := IdealWeightComparison.moreSingularAt_generatorLog_of_forall_isInSpanAt hspan
  refine ⟨((q + 1 : ℕ) : ℝ) / q * C₁ + (q : ℝ)⁻¹ * C₂ + C₀, ?_⟩
  filter_upwards [hC₁, hC₂, hU.mem_nhds hxU] with y hy1 hy2 hyU
  have hc : (0 : ℝ) < ((q + 1 : ℕ) : ℝ) / q := by positivity
  have hqinv : (0 : ℝ) < (q : ℝ)⁻¹ := by positivity
  have hfac : ((q + 1 : ℕ) : ℝ) / q * ((q + 1 : ℕ) : ℝ)⁻¹ = (q : ℝ)⁻¹ := by
    field_simp
  have hΦy : Φ y = (((q : ℚ)⁻¹ : ℚ) : ℝ) * generatorLog g y + (R y : EReal) := hΦeq y hyU
  have hqcast : (((q : ℚ)⁻¹ : ℚ) : ℝ) = (q : ℝ)⁻¹ := by push_cast; ring
  rw [hqcast] at hΦy
  have hR : (-C₀ : ℝ) ≤ R y := (abs_le.mp (hRb y hyU)).1
  calc ((((q + 1 : ℕ) : ℝ) / q : ℝ) : EReal) * ψ y
      ≤ ((((q + 1 : ℕ) : ℝ) / q : ℝ) : EReal) *
          ((((q + 1 : ℕ) : ℝ)⁻¹ : ℝ) * generatorLog h y + (C₁ : EReal)) :=
        mul_le_mul_of_nonneg_left hy1 (EReal.coe_nonneg.mpr hc.le)
    _ = (((q : ℝ)⁻¹ : ℝ) : EReal) * generatorLog h y +
          ((((q + 1 : ℕ) : ℝ) / q * C₁ : ℝ) : EReal) := by
        rw [ThetaPshConvexCombination.coe_mul_add_coe hc, coe_mul_coe_mul, hfac]
    _ ≤ (((q : ℝ)⁻¹ : ℝ) : EReal) * (generatorLog g y + (C₂ : EReal)) +
          ((((q + 1 : ℕ) : ℝ) / q * C₁ : ℝ) : EReal) :=
        add_le_add (mul_le_mul_of_nonneg_left hy2 (EReal.coe_nonneg.mpr hqinv.le)) le_rfl
    _ = ((((q : ℝ)⁻¹ : ℝ) : EReal) * generatorLog g y + (R y : EReal)) +
          (((((q + 1 : ℕ) : ℝ) / q * C₁ + (q : ℝ)⁻¹ * C₂ - R y : ℝ)) : EReal) := by
        rw [ThetaPshConvexCombination.coe_mul_add_coe hqinv, add_assoc, add_assoc]
        congr 1
        rw [← EReal.coe_add, ← EReal.coe_add]
        congr 1
        ring
    _ ≤ Φ y + (((((q + 1 : ℕ) : ℝ) / q * C₁ + (q : ℝ)⁻¹ * C₂ + C₀ : ℝ)) : EReal) := by
        rw [hΦy]
        exact add_le_add le_rfl (EReal.coe_le_coe_iff.mpr (by linarith))

end

end SGPT.Foundations.Analysis.Pending.MultiplierIdealWeightLowerBound
