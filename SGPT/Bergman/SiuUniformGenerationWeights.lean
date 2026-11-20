import SGPT.Bergman.SiuUniformGenerationLocalFrame
import SGPT.PSH.SiuGenSystem
import SGPT.Foundations.Analysis.Pending.GlobalDiagonalScaling

/-!
# Native Chern and PSH weights for fixed-cover Siu correction

The actual all-degree tensor construction has the exact curvature
`m θ + K θG`. An arbitrary actual holomorphic nonzero frame of this bundle
on a preselected geometric ball gives the solver weight directly from its
physical norm. The curvature and PSH assertions below do not require that
the bundle's preferred atlas frame contain the entire ball.

Blueprint: `siu-uniform-fixed-weights.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.Bergman.SiuUniformGeneration

open Bundle Set Filter Metric MeasureTheory
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Foundations.Analysis.Pending.ProductComplexManifold
open scoped ProductComplexManifold
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open SGPT.Bergman.CompactHolomorphicSectionsDraft SGPT.Bergman.NativeHermitianMetric
open HermitianHolomorphicLineBundle
open SGPT.PSH.GlobalL2 SGPT.PSH.SiuL2 SGPT.NAPotential.NAGaga SGPT.PSH.LineBundleMetric

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

/-- The original physical tensor bundle, including every degree `m`, has
the exact original prescribed Chern background. -/
theorem twistedPower_isOwnFirstChernForm
    (L G : HermitianHolomorphicLineBundle.{0, 0} n X)
    (hL : IsSourceSmoothHermitianMetric L) (hG : IsSourceSmoothHermitianMetric G)
    {θ θG : ClosedRealOneOneForm n X}
    (hθ : IsOwnFirstChernForm L θ) (hθG : IsOwnFirstChernForm G θG)
    {K : ℕ} (hK : 1 ≤ K) (m : ℕ) :
    IsOwnFirstChernForm (twistedPower L (positivePower G (K - 1)) m)
      ((m : ℝ) • θ + (K : ℝ) • θG) := by
  intro c e z hz he
  have h := sourceNativeFirstChernForm_isOwn
    (twistedPower L (positivePower G (K - 1)) m)
    (sourceNativeTwistedPower_smooth L (positivePower G (K - 1)) hL
      (sourceNativePositivePower_smooth G hG (K - 1)) m) c e z hz he
  rw [sourceNativeTwistedPower_chern_coeff L (positivePower G (K - 1)) hL
    (sourceNativePositivePower_smooth G hG (K - 1)) c hz m,
    sourceNativePositivePower_chern_coeff G hG c hz (K - 1),
    sourceNativeFirstChernForm_geometricallyEq L hL hθ c hz,
    sourceNativeFirstChernForm_geometricallyEq G hG hθG c hz] at h
  have hdegree : ((K - 1 + 1 : ℕ) : ℝ) = (K : ℝ) := by
    rw [Nat.sub_add_cancel hK]
  simpa only [ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.coeff_smul,
    hdegree] using h

variable [MeasurableSpace X] [BorelSpace X]

/-- The native physical-frame local weight used by the fixed-cover solver. -/
def fixedFramePsi {μ : Measure X} {G E : HermitianHolomorphicLineBundle.{0, 0} n X}
    (D : SiuCover μ G G) (σ : Fin D.m → (x : X) → E.Fiber x)
    (m : ℕ) (Φ Ψ : X × unitDisc → EReal) (a : Fin D.m)
    (w : ComplexModel (n + 1)) : EReal :=
  SiuCover.thetaGen m Φ Ψ ((D.chartP a).val.symm w) +
    ((sectionWeight (σ a) (D.chartX a) (projX n w) -
      D.lam * ‖projX n w - ctr (n := n) (D.pt a)‖ ^ 2 : ℝ) : EReal)

/-- Actual frame norms on the fixed balls yield the required PSH local
weights. The only numerical positivity is the fixed cover's `GoodPower`. -/
theorem fixedFramePsi_psh {μ : Measure X}
    {G E : HermitianHolomorphicLineBundle.{0, 0} n X} (D : SiuCover μ G G)
    (hG : IsSourceSmoothHermitianMetric G) (hE : IsSourceSmoothHermitianMetric E)
    {θ θG : ClosedRealOneOneForm n X} (hθG : IsOwnFirstChernForm G θG)
    {s : ℝ} {K m : ℕ} (hK : D.GoodPower s K) (hm : 0 < m)
    (hOwnE : IsOwnFirstChernForm E ((m : ℝ) • θ + (K : ℝ) • θG))
    (σ : Fin D.m → (x : X) → E.Fiber x)
    (hσ : ∀ a, IsHolomorphicSectionOn (n := n) E.Fiber (σ a)
      ((D.chartX a).val.source ∩ (D.chartX a).val ⁻¹'
        ball (ctr (n := n) (D.pt a)) (3 * D.R a / 2)))
    (hσ0 : ∀ a, ∀ x ∈ (D.chartX a).val.source ∩ (D.chartX a).val ⁻¹'
      ball (ctr (n := n) (D.pt a)) (3 * D.R a / 2), σ a x ≠ 0)
    {Φ : X × unitDisc → EReal}
    (hΦ : IsThetaPshPotential
      (ClosedRealOneOneForm.pullback
        (contMDiff_fst (n := n) (m := 1) (X := X) (Y := unitDisc)) θ).val Φ)
    {Ψ : X × unitDisc → EReal}
    (hΨ : ThetaPlurisubharmonic
      (ClosedRealOneOneForm.pullback
        (contMDiff_fst (n := n) (m := 1) (X := X) (Y := unitDisc)) (s • θG)).val Ψ)
    (a : Fin D.m) :
    PlurisubharmonicOn (fixedFramePsi D σ m Φ Ψ a)
      (prodDom (ctr (n := n) (D.pt a)) (D.R a) 1) := by
  let U : Set X := (D.chartX a).val.source ∩ (D.chartX a).val ⁻¹'
    ball (ctr (n := n) (D.pt a)) (3 * D.R a / 2)
  have hU : IsOpen U :=
    (D.chartX a).val.isOpen_inter_preimage isOpen_ball
  have hρE := (isSmoothLocalPotential_sectionWeight hE hOwnE hU (σ a)
    (hσ a) (hσ0 a) (D.chartX a)).mono isOpen_ball (show
      ball (ctr (n := n) (D.pt a)) (D.R a) ⊆
        (D.chartX a).val.target ∩ (D.chartX a).val.symm ⁻¹' U from by
      intro z hz
      have hzt := D.ball_subset_targetX a hz
      exact ⟨hzt, (D.chartX a).val.map_target hzt, by
        rw [mem_preimage, (D.chartX a).val.right_inv hzt]
        exact ball_subset_ball (by linarith [D.R_pos a]) hz⟩)
  have hρG := (D.isSmoothLocalPotential_sρG hG hθG ((K : ℝ) - s) a).mono
    isOpen_ball (D.ball_subset_two a)
  have hred := LocalPotentials.localPotential_sub hρE hρG
  have hbackground : ((m : ℝ) • θ + (K : ℝ) • θG) - ((K : ℝ) - s) • θG =
      (m : ℝ) • θ + s • θG := by module
  rw [hbackground] at hred
  have hDo := isOpen_prodDom (ctr (n := n) (D.pt a)) (D.R a) 1
  have hsub : prodDom (ctr (n := n) (D.pt a)) (D.R a) 1 ⊆
      LocalPotentialPullback.potentialDomain Prod.fst (D.chartP a) (D.chartX a)
        (ball (ctr (n := n) (D.pt a)) (D.R a)) := by
    intro w hw
    refine ⟨⟨D.prodDom_subset_target a hw, ?_⟩, ?_⟩
    · change ((D.chartP a).val.symm w).1 ∈ (D.chartX a).val.source
      rw [D.symm_fst hw]
      exact (D.chartX a).val.map_target (D.ball_subset_targetX a hw.1)
    · change coordinateMap Prod.fst (D.chartP a) (D.chartX a) w ∈
        ball (ctr (n := n) (D.pt a)) (D.R a)
      rw [D.coordinateMap_eq hw]
      exact hw.1
  have hpot := (LocalPotentialPullback.isSmoothLocalPotential_pullback
    (contMDiff_fst (n := n) (m := 1) (X := X) (Y := unitDisc)) (D.chartP a) hred).mono hDo hsub
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have htotal := GlobalDiagonalScaling.thetaPlurisubharmonic_add_smul hm' zero_lt_one hΦ.1 hΨ
  simp only [EReal.coe_one, one_mul, one_smul] at htotal
  have hpull : SmoothRealForm.pullback
      (contMDiff_fst (n := n) (m := 1) (X := X) (Y := unitDisc))
      (((m : ℝ) • θ + s • θG).val) =
      ((m : ℝ) • ClosedRealOneOneForm.pullback
        (contMDiff_fst (n := n) (m := 1) (X := X) (Y := unitDisc)) θ +
        ClosedRealOneOneForm.pullback
        (contMDiff_fst (n := n) (m := 1) (X := X) (Y := unitDisc)) (s • θG)).val := by
    change SmoothRealForm.pullback
      (contMDiff_fst (n := n) (m := 1) (X := X) (Y := unitDisc))
      ((m : ℝ) • θ.val + s • θG.val) =
      (m : ℝ) • SmoothRealForm.pullback
        (contMDiff_fst (n := n) (m := 1) (X := X) (Y := unitDisc)) θ.val +
      SmoothRealForm.pullback
        (contMDiff_fst (n := n) (m := 1) (X := X) (Y := unitDisc)) (s • θG.val)
    rw [ProductTestForms.pullback_add, ProductTestForms.pullback_smul]
  rw [hpull] at hpot
  have h1 := SiuCover.plurisubharmonicOn_add_localPotential' htotal (D.chartP a) hpot
  have h4X : PlurisubharmonicOn (fun z => (D.gW s K a z : EReal))
      (ball (ctr (n := n) (D.pt a)) (D.R a)) :=
    plurisubharmonicOn_of_contDiffOn_levi_nonneg isOpen_ball
      (((contDiffOn_const.mul (D.contDiffOn_ρG hG a)).sub
        (contDiff_const.mul ((contDiff_norm_sq ℝ).comp
          (contDiff_id.sub contDiff_const))).contDiffOn).mono (D.ball_subset_two a))
      fun z hz v => D.leviForm_gW_nonneg hG hK a hz v
  have h4 : PlurisubharmonicOn (fun w => (D.gW s K a (projX n w) : EReal))
      (prodDom (ctr (n := n) (D.pt a)) (D.R a) 1) :=
    HolomorphicPullback.plurisubharmonicOn_comp_holomorphic hDo
      (projX n).differentiable.differentiableOn (fun w hw => hw.1) h4X
  intro w hw
  apply ((h1.add h4) w hw).congr
  filter_upwards [hDo.mem_nhds hw] with w hw
  symm
  change fixedFramePsi D σ m Φ Ψ a w =
    (((sectionWeight (σ a) (D.chartX a)
      (coordinateMap Prod.fst (D.chartP a) (D.chartX a) w) -
      ((K : ℝ) - s) * D.ρG a
        (coordinateMap Prod.fst (D.chartP a) (D.chartX a) w) : ℝ) : EReal) +
        SiuCover.thetaGen m Φ Ψ ((D.chartP a).val.symm w)) +
        (D.gW s K a (projX n w) : EReal)
  rw [D.coordinateMap_eq hw, fixedFramePsi, SiuCover.gW]
  rw [add_comm (_ : EReal) (SiuCover.thetaGen m Φ Ψ _), add_assoc, ← EReal.coe_add]
  congr 2
  ring

end SGPT.Bergman.SiuUniformGeneration
