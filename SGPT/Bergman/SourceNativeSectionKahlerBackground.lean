import SGPT.Bergman.SourceNativeTwistedLogPsh
import SGPT.Foundations.Analysis.Pending.KahlerDomination

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Bergman.NativeHermitianMetric
open Bundle Set Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open HermitianHolomorphicLineBundle
open scoped Topology Manifold ContDiff ENNReal

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [ConnectedSpace X] [CompactSpace X]

/-- Literal source911-916: genuine physical normalized section logarithms
become (c1(L)+epsilon*omega)-PSH for ALL sufficiently large actual degrees.
ONE threshold precedes EVERY full original section. Actual Chern/smooth
data, scalar normalization and Kahler domination are produced internally. -/
theorem exists_sourceNormalizedSection_kahler_background
    (L T : HermitianHolomorphicLineBundle.{0,0} n X)
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
    (omega : KahlerBackground n X) {ε : ℝ} (hε : 0 < ε) :
    ∃ k₀ : ℕ, 0 < k₀ ∧ ∀ k : ℕ, k₀ ≤ k → ∀ s : twistedSections L T k,
      s ≠ 0 → IsThetaPshPotential
        (sourceNativeFirstChernForm L hL + ε • omega.form).val
        (fun x => (((k : ℝ)⁻¹ : ℝ) : EReal) * sourceSectionLogNormSq (twistedPower L T k) s x) := by
  let θL := sourceNativeFirstChernForm L hL
  let θT := sourceNativeFirstChernForm T hT
  obtain ⟨A, hA, hsemi⟩ := KahlerDomination.exists_pos_isSemipositive_add_smul omega (-θT)
  obtain ⟨N, hN⟩ := exists_nat_gt (A / ε)
  refine ⟨N + 1, Nat.succ_pos _, fun k hk s hs => ?_⟩
  have hkpos : 0 < k := lt_of_lt_of_le (Nat.succ_pos N) hk
  have hkp : (0 : ℝ) < k := Nat.cast_pos.mpr hkpos
  have hNk : (N : ℝ) < k := by
    exact_mod_cast (lt_of_lt_of_le (Nat.lt_succ_self N) hk)
  have hAk : A / (k : ℝ) ≤ ε := by
    apply (div_le_iff₀ hkp).mpr
    have h := (div_lt_iff₀ hε).mp (hN.trans hNk)
    nlinarith
  have hscaled := KahlerDomination.isSemipositive_smul hsemi (inv_nonneg.mpr hkp.le)
  have hscale : (k : ℝ)⁻¹ • (-θT + A • omega.form) =
      -((k : ℝ)⁻¹ • θT) + (A / (k : ℝ)) • omega.form := by
    simp only [div_eq_mul_inv]
    module
  rw [hscale] at hscaled
  have hshift := KahlerDomination.isSemipositive_add_smul_mono omega.isSemipositive hAk hscaled
  have hp := LocalPotentials.isThetaPshPotential_add_of_semipositive
    (sourceNormalizedTwistedSectionLogNormSq_isThetaPsh L T hL hT k hkpos s hs) hshift
  have hform : (θL + (k : ℝ)⁻¹ • θT) +
      (-((k : ℝ)⁻¹ • θT) + ε • omega.form) = θL + ε • omega.form := by module
  rwa [hform] at hp

end SGPT.Bergman.NativeHermitianMetric
