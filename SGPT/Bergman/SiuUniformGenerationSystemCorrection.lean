import SGPT.Bergman.SiuUniformGenerationSystem

/-!
# Contraction and native holomorphic output on the fixed cover

The target bundle is arbitrary with the stated native physical curvature.
Its actual local frames are constructed on the fixed balls by LocalFrame;
all chart, partition, measure and contraction data remain those of `G`.
Blueprint: `siu-uniform-fixed-correction.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.Bergman.SiuUniformGeneration

open Set Filter Metric MeasureTheory Bundle
open scoped Topology ENNReal ContDiff Manifold
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Foundations.Analysis.Pending.ProductComplexManifold
open scoped ProductComplexManifold
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open SGPT.Bergman.CompactHolomorphicSectionsDraft
open HermitianHolomorphicLineBundle
open SGPT.PSH.GlobalL2 SGPT.PSH.SiuL2 SGPT.NAPotential.NAGaga SGPT.PSH.LineBundleMetric

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [MeasurableSpace X] [BorelSpace X]
  {μ : Measure X} {G E : HermitianHolomorphicLineBundle.{0, 0} n X}

section System

variable [SFinite μ] (D : SiuCover μ G G)
  (hG : IsSourceSmoothHermitianMetric G) (hE : IsSourceSmoothHermitianMetric E)
  {θ θG : ClosedRealOneOneForm n X} (hθG : IsOwnFirstChernForm G θG)
  {s : ℝ} {K m : ℕ} (hK : D.GoodPower s K) (hm : 0 < m)
  (hOwnE : IsOwnFirstChernForm E ((m : ℝ) • θ + (K : ℝ) • θG))
  (σ : Fin D.m → (x : X) → E.Fiber x)
  (hσ : ∀ a, IsHolomorphicSectionOn (n := n) E.Fiber (σ a) (fixedFrameBaseDomain D a))
  (hσ0 : ∀ a, ∀ x ∈ fixedFrameBaseDomain D a, σ a x ≠ 0)
  {Φ : X × unitDisc → EReal}
  (hΦ : IsThetaPshPotential
    (ClosedRealOneOneForm.pullback
      (contMDiff_fst (n := n) (m := 1) (X := X) (Y := unitDisc)) θ).val Φ)
  {Ψ : X × unitDisc → EReal}
  (hΨ : ThetaPlurisubharmonic
    (ClosedRealOneOneForm.pullback
      (contMDiff_fst (n := n) (m := 1) (X := X) (Y := unitDisc)) (s • θG)).val Ψ)
  (hΨt : ∀ q, Ψ q ≠ ⊤)

include hG hE hθG hK hm hOwnE σ hσ hσ0 hΦ hΨ hΨt in
/-- **The contraction factor is at most `1/4`.** -/
theorem kappa_fixedFrameSystem_le :
    (fixedFrameSystem D hG hE hθG hK hm hOwnE σ hσ hσ0 hΦ hΨ hΨt).kappa ≤ ENNReal.ofReal (1 / 4) := by
  simp only [DomainGluingSystem.kappa, fixedFrameSystem, Fintype.card_fin]
  have hlam := D.lam_pos
  have hA := D.Aμ_pos
  calc (D.m : ℝ≥0∞) * (ENNReal.ofReal ((D.m : ℝ) * D.M) * (ENNReal.ofReal D.Aμ *
        (ENNReal.ofReal D.Aμ * ENNReal.ofReal (2 / D.lam))))
      ≤ ENNReal.ofReal (D.m : ℝ) * (ENNReal.ofReal ((D.m : ℝ) * |D.M|) * (ENNReal.ofReal D.Aμ *
        (ENNReal.ofReal D.Aμ * ENNReal.ofReal (2 / D.lam)))) := by
        rw [ENNReal.ofReal_natCast]
        gcongr
        exact le_abs_self _
    _ = ENNReal.ofReal ((D.m : ℝ) * ((D.m : ℝ) * |D.M| * (D.Aμ * (D.Aμ * (2 / D.lam))))) := by
        rw [← ENNReal.ofReal_mul hA.le, ← ENNReal.ofReal_mul hA.le,
          ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (D.m : ℝ) * |D.M|),
          ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (D.m : ℝ))]
    _ ≤ ENNReal.ofReal (1 / 4) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hle : 8 * ((D.m : ℝ) ^ 2 * |D.M| * D.Aμ ^ 2) ≤ D.lam := by
          rw [SiuCover.lam]; linarith
        have : (D.m : ℝ) * ((D.m : ℝ) * |D.M| * (D.Aμ * (D.Aμ * (2 / D.lam)))) =
            2 * ((D.m : ℝ) ^ 2 * |D.M| * D.Aμ ^ 2) / D.lam := by
          field_simp
        rw [this, div_le_iff₀ hlam]
        linarith

include hG hE hθG hK hm hOwnE σ hσ hσ0 hΦ hΨ hΨt in
/-- Local holomorphic coefficients in the actual frames give native
holomorphicity in every original atlas frame of the target bundle. -/
theorem isHolomorphicProdSectionOn_of_fixedFrameLocal
    (S : (q : X × unitDisc) → E.Fiber q.1)
    (hS : ∀ a, ∃ f : ComplexModel (n + 1) → ℂ,
      DifferentiableOn ℂ f ((fixedFrameSystem D hG hE hθG hK hm hOwnE σ hσ hσ0 hΦ hΨ hΨt).domr a) ∧
      ∀ q ∈ (fixedFrameSystem D hG hE hθG hK hm hOwnE σ hσ hσ0 hΦ hΨ hΨt).small a,
        S q = f ((fixedFrameSystem D hG hE hθG hK hm hOwnE σ hσ hσ0 hΦ hΨ hΨt).chart a q) •
          (fixedFrameSystem D hG hE hθG hK hm hOwnE σ hσ hσ0 hΦ hΨ hΨt).frame a q) :
    IsHolomorphicProdSectionOn E S univ := by
  set GS := fixedFrameSystem D hG hE hθG hK hm hOwnE σ hσ hσ0 hΦ hΨ hΨt
  intro q _ e hqe
  let := e.property
  obtain ⟨a, ha⟩ := GS.cover q
  have hqs : q ∈ GS.small a := GS.smaller_subset_small a ha
  obtain ⟨f, hf, hSa⟩ := hS a
  have hbase : q.1 ∈ fixedFrameBaseDomain D a :=
    mem_fixedFrameBaseDomain D hqs.1 (GS.domr_sub a hqs.2)
  have h1 : HolomorphicAt (n + 1) (fun q' => f ((D.chartP a).val q')) q :=
    holomorphicAt_comp_chart' (D.chartP a) (GS.isOpen_domr a) hf hqs.1 hqs.2
  have h2 := isHolomorphicProdSectionOn_baseSection
    (isOpen_fixedFrameBaseDomain D a) (σ a) (hσ a) q hbase e hqe
  refine (HolomorphicAt.mul' h1 h2).congr ?_
  have hO : IsOpen (GS.small a ∩ Prod.fst ⁻¹' e.val.baseSet) :=
    (GS.isOpen_small a).inter (e.val.open_baseSet.preimage continuous_fst)
  filter_upwards [hO.mem_nhds ⟨hqs, hqe⟩] with q' hq'
  change f ((D.chartP a).val q') * e.val.continuousLinearMapAt ℂ q'.1
      (σ a q'.1) = e.val.continuousLinearMapAt ℂ q'.1 (S q')
  rw [hSa q' hq'.1, map_smul, smul_eq_mul]
  rfl

end System

end SGPT.Bergman.SiuUniformGeneration
