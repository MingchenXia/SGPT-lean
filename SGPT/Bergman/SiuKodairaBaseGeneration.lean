import SGPT.Bergman.SiuKodairaUniformGeneration
import SGPT.Bergman.SiuKodairaPointIdeal
import SGPT.Trace.BertiniGlobalGeneration

/-!
# One actual positive power generates every original point ideal

The positive degree is chosen from fixed geometry before the pole point.
All ideal generators are actual native global bundle sections, obtained
through the checked original constant-product restriction bridge.
Blueprint: `siu-kodaira-embedding.tex`, node `siu-kodaira:uniform-point-ideals`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.Bergman.SiuKodaira

open Set Filter Metric MeasureTheory Bundle
open scoped Topology ENNReal Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open SGPT.Bergman.SiuUniformGeneration
open HermitianHolomorphicLineBundle
open SGPT.PSH.GlobalL2 SGPT.PSH.SiuL2 SGPT.Trace.BertiniGlobalGeneration

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

/-- The same literal power works for every original base potential in a
fixed Chern background, with the actual all-frame stalk meaning. -/
theorem exists_positivePower_baseGeneration [CompactSpace X]
    (G : HermitianHolomorphicLineBundle.{0, 0} n X) (hG : IsSourceSmoothHermitianMetric G)
    (θG : ClosedRealOneOneForm n X) (hθG : IsOwnFirstChernForm G θG)
    (hKah : θG.val.IsKahler) (ell : ℕ) :
    ∃ d : ℕ, 0 < d ∧ ∀ φ : X → EReal,
      IsThetaPshPotential ((ell : ℝ) • θG).val φ →
      IsBaseGloballyGenerated (positivePower G (d - 1)) (multiplierIdeal (n := n) 1 φ) := by
  obtain ⟨d, hd, hgen⟩ := exists_positivePower_productGeneration G hG θG hθG hKah ell
  exact ⟨d, hd, fun φ hφ => isBaseGloballyGenerated_of_prod _ hφ.1.quasiPlurisubharmonic
    one_pos (hgen φ hφ)⟩

/-- One actual positive power generates the intrinsic ideal of every
original point.  All geometric and tensor degrees precede the point. -/
theorem exists_positivePower_generates_pointIdeals [CompactSpace X] (hn : 0 < n)
    (G : HermitianHolomorphicLineBundle.{0, 0} n X) (hG : IsSourceSmoothHermitianMetric G)
    (θG : ClosedRealOneOneForm n X) (hθG : IsOwnFirstChernForm G θG)
    (hKah : θG.val.IsKahler) :
    ∃ d : ℕ, 0 < d ∧ ∀ p : X,
      IsBaseGloballyGenerated (positivePower G (d - 1)) (vanishingIdeal (n := n) ({p} : Set X)) := by
  let _ : MeasurableSpace X := borel X
  have _ : BorelSpace X := ⟨rfl⟩
  let omega : KahlerBackground n X := ⟨θG, hKah⟩
  have hμ := KahlerVolumeSmoothPositive.isSmoothPositiveVolume_kahlerVolume omega
  let D := fixedGeometry hμ G hG θG hθG hKah
  obtain ⟨B, hB0, hBa⟩ := D.exists_uniform_siuPoleB hKah
  let ell : ℕ := ⌈(n : ℝ) * B⌉₊
  have hell : (n : ℝ) * B ≤ (ell : ℝ) := Nat.le_ceil _
  obtain ⟨d, hd, hgen⟩ := exists_positivePower_baseGeneration G hG θG hθG hKah ell
  refine ⟨d, hd, fun p => ?_⟩
  have hne : ∑ a, D.χ a p ≠ 0 := by rw [D.sum_χ p]; exact one_ne_zero
  obtain ⟨a, -, ha⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  have hpa := D.tsupport_χ a (subset_tsupport _ ha)
  have hx : p ∈ (D.chartX a).val.source := hpa.1
  have hp : (D.chartX a).val p ∈ closedBall (ctr (n := n) (D.pt a)) (D.R a / 4) :=
    ball_subset_closedBall hpa.2
  obtain ⟨mω, hmω, hBm⟩ := hBa a
  have hφ := isThetaPshPotential_criticalPointWeight hn D hKah hB0 a hmω hBm hx hp
  have hsemi : (((ell : ℝ) - (n : ℝ) * B) • θG).val.IsSemipositive :=
    KahlerDomination.isSemipositive_smul omega.isSemipositive (sub_nonneg.mpr hell)
  have hphi := LocalPotentials.thetaPlurisubharmonic_add_of_semipositive hφ.1 hsemi
  have hform : ((n : ℝ) * B) • θG + ((ell : ℝ) - (n : ℝ) * B) • θG = (ell : ℝ) • θG := by module
  rw [hform] at hphi
  have hφell : IsThetaPshPotential ((ell : ℝ) • θG).val (criticalPointWeight D a p) := ⟨hphi, hφ.2⟩
  have hgg := hgen (criticalPointWeight D a p) hφell
  rwa [multiplierIdeal_criticalPointWeight_eq_pointIdeal hn D hKah hB0 a hmω hBm hx hp] at hgg

end SGPT.Bergman.SiuKodaira
