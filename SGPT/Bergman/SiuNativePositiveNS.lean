import SGPT.Bergman.SiuNativeSectionMetric
import SGPT.Bergman.SiuNativeSectionDense
import SGPT.Bergman.SiuNSProjectivity

/-! The actual positive native line bundle itself produces its original
Chern class in the existing real Cartier span, without a divisor input. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.BDivisor.NSKodaira
open Set Filter Bundle
open scoped Topology Manifold ContDiff BigOperators
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open SGPT.Bergman.NativeHermitianMetric SGPT.Bergman.QuantizationDraft
open SGPT.Bergman.CompactHolomorphicSectionsDraft SGPT.Bergman.AnalyticSectionProducts
open HermitianHolomorphicLineBundle SGPT.PSH.GlobalL2

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] [CompactSpace X]

/-- A positive original native bundle manufactures its actual Cartier
section divisor and hence its original Chern class in the existing NS_R.
All dimensions, disconnected and empty manifolds are included. -/
theorem positive_native_chern_mem_neronSeveri
    (L : HermitianHolomorphicLineBundle.{0,0} n X) (hL : IsSourceSmoothHermitianMetric L)
    (θ : ClosedRealOneOneForm n X) (hθ : IsOwnFirstChernForm L θ) (hK : θ.val.IsKahler) :
    RealBottChern.ofRepresentative θ ∈ DFAlg.neronSeveri n X := by
  obtain ⟨d, hd, N, t, hgen, _, _, _⟩ := SGPT.Bergman.SiuKodaira.kodairaEmbedding L hL θ hθ hK
  obtain ⟨s, hs⟩ := exists_dense_native_section_of_global_generation (positivePower L (d - 1)) t hgen
  have hmem := nativeSection_chern_mem_neronSeveri (positivePower L (d - 1))
    (sourceNativePositivePower_smooth L hL (d - 1)) s hs
  have hd' : d - 1 + 1 = d := Nat.sub_add_cancel hd
  have hclass : RealBottChern.ofRepresentative
      (sourceNativeFirstChernForm (positivePower L (d - 1))
        (sourceNativePositivePower_smooth L hL (d - 1))) =
      (d : ℝ) • RealBottChern.ofRepresentative θ := by
    rw [← RealBottChern.ofRepresentative_smul]
    apply RealBottChern.ofRepresentative_eq_of_geometricallyEq
    intro c z hz
    rw [sourceNativePositivePower_chern_coeff L hL c hz (d - 1), hd',
      ClosedRealOneOneForm.coeff_smul,
      sourceNativeFirstChernForm_geometricallyEq L hL hθ c hz]
  rw [hclass] at hmem
  have hdne : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have h := (DFAlg.neronSeveri n X).smul_mem ((d : ℝ)⁻¹) hmem
  simpa only [smul_smul, inv_mul_cancel₀ hdne, one_smul] using h

/-- Both directions use manufactured actual objects on the same original
compact manifold: a Kähler class in the real Cartier span is equivalent
to existence of an actual native positive integral holomorphic line bundle. -/
theorem exists_kahler_mem_neronSeveri_iff_positive_native_bundle :
    (∃ omega : ClosedRealOneOneForm n X, omega.val.IsKahler ∧
      RealBottChern.ofRepresentative omega ∈ DFAlg.neronSeveri n X) ↔
    ∃ (L : HermitianHolomorphicLineBundle.{0,0} n X), IsSourceSmoothHermitianMetric L ∧
      ∃ θ : ClosedRealOneOneForm n X, IsOwnFirstChernForm L θ ∧ θ.val.IsKahler := by
  constructor
  · rintro ⟨omega, hK, hNS⟩
    exact exists_positive_native_bundle_of_kahler_mem_neronSeveri omega hK hNS
  · rintro ⟨L, hL, θ, hθ, hK⟩
    exact ⟨θ, hK, positive_native_chern_mem_neronSeveri L hL θ hθ hK⟩

end SGPT.BDivisor.NSKodaira
