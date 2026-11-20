import SGPT.Bergman.SiuNSCartierBundle
import SGPT.Bergman.SiuNSRationalPositive
import SGPT.Bergman.SiuKodairaEmbedding

/-! A Kähler class in the actual real divisor span manufactures an actual
positive integral native bundle and an actual holomorphic projective embedding. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.BDivisor.NSKodaira
open Set Filter Bundle
open scoped Topology Manifold ContDiff BigOperators
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open SGPT.Bergman.NativeHermitianMetric SGPT.PSH.GlobalL2
open SGPT.Bergman.QuantizationDraft
open SGPT.Bergman.AnalyticSectionProducts SGPT.Bergman.CompactHolomorphicSectionsDraft
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open HermitianHolomorphicLineBundle

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] [CompactSpace X]

/-- A Kähler class in the original real divisor span produces an actual
positive native integral holomorphic line bundle on the original manifold.
No positive line bundle, integral class, or Chern certificate is an input. -/
theorem exists_positive_native_bundle_of_kahler_mem_neronSeveri
    (omega : ClosedRealOneOneForm n X) (hK : omega.val.IsKahler)
    (hNS : RealBottChern.ofRepresentative omega ∈ DFAlg.neronSeveri n X) :
    ∃ (G : HermitianHolomorphicLineBundle n X), IsSourceSmoothHermitianMetric G ∧
      ∃ θ : ClosedRealOneOneForm n X, IsOwnFirstChernForm G θ ∧ θ.val.IsKahler := by
  classical
  obtain ⟨N, D, E, a, hE, f, hf, hpotential⟩ := exists_finite_divisor_potential omega hNS
  obtain ⟨r, hr⟩ := exists_rational_positive_perturbation omega hK (fun i => (E i).curvature) a
  obtain ⟨q, hq, b, hb⟩ := exists_positive_common_denominator r
  let η := omega + ∑ i, ((r i : ℝ) - a i) • (E i).curvature
  let θa := ∑ i, a i • (E i).curvature
  let θr := ∑ i, (r i : ℝ) • (E i).curvature
  let θb := ∑ i, (b i : ℝ) • (E i).curvature
  have hlinear : θr = θa + ∑ i, ((r i : ℝ) - a i) • (E i).curvature := by
    dsimp only [θr, θa]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← add_smul]
    congr 1
    ring
  have hη : ∀ (c : ComplexChart n X) (z : ComplexModel n), z ∈ c.val.target →
      η.val.coeff c z = θr.val.coeff c z + smoothDDC (fun w => f (c.val.symm w)) z := by
    intro c z hz
    dsimp only [η]
    rw [ClosedRealOneOneForm.coeff_add, hpotential c z hz, hlinear,
      ClosedRealOneOneForm.coeff_add]
    abel
  have hθb : θb = (q : ℝ) • θr := by
    dsimp only [θb, θr]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [hb i, smul_smul]
  obtain ⟨L, hL, hcurv⟩ := exists_native_integral_divisor_metric D E hE b
  have hqf : ChartSmooth (n := n) (fun p => (q : ℝ) * f p) :=
    fun c => contDiffOn_const.mul (hf c)
  let G := rescaleExp L (fun p => (q : ℝ) * f p) hqf
  refine ⟨G, rescaleExp_smooth L hL _ hqf, (q : ℝ) • η, ?_, ?_⟩
  · apply rescale_exp_isOwnFirstChernForm L hL θb ((q : ℝ) • η) hcurv _ hqf
    intro c z hz
    rw [ClosedRealOneOneForm.coeff_smul, hη c z hz, smul_add, hθb,
      ClosedRealOneOneForm.coeff_smul]
    congr 1
    simpa only [smul_eq_mul] using (smoothDDC_smul c.val.open_target (hf c) (q : ℝ) hz).symm
  · refine ⟨fun c z hz => ⟨((q : ℝ) • η).property.2 c z hz, fun v hv => ?_⟩,
      ((q : ℝ) • η).property.1⟩
    simp only [ClosedRealOneOneForm.coeff_smul, ContinuousAlternatingMap.smul_apply, smul_eq_mul]
    exact mul_pos (by exact_mod_cast hq) ((hr.1 c z hz).2 v hv)

/-- The same original compact manifold has an actual native holomorphic
projective embedding defined by sections of one literal positive power of
the manufactured integral bundle, with injective actual differential. -/
theorem kodairaEmbedding_of_kahler_mem_neronSeveri
    (omega : ClosedRealOneOneForm n X) (hK : omega.val.IsKahler)
    (hNS : RealBottChern.ofRepresentative omega ∈ DFAlg.neronSeveri n X) :
    ∃ (G : HermitianHolomorphicLineBundle n X) (d : ℕ), 0 < d ∧ ∃ (N : ℕ)
      (s : Fin (N + 1) → HolomorphicSections (n := n) (positivePower G (d - 1)).Fiber)
      (hgen : ∀ x : X, ∃ j : Fin (N + 1), s j x ≠ 0),
      ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) ∞
        (sourceNativeFiniteSectionProjectiveMap (positivePower G (d - 1)) s hgen) ∧
      Topology.IsClosedEmbedding
        (sourceNativeFiniteSectionProjectiveMap (positivePower G (d - 1)) s hgen) ∧
      ∀ p : X, Function.Injective (mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N)
        (sourceNativeFiniteSectionProjectiveMap (positivePower G (d - 1)) s hgen) p) := by
  obtain ⟨G, hG, θ, hθ, hθK⟩ := exists_positive_native_bundle_of_kahler_mem_neronSeveri omega hK hNS
  obtain ⟨d, hd, N, s, hgen, hhol, hemb, himm⟩ := SGPT.Bergman.SiuKodaira.kodairaEmbedding G hG θ hθ hθK
  exact ⟨G, d, hd, N, s, hgen, hhol, hemb, himm⟩

end SGPT.BDivisor.NSKodaira
