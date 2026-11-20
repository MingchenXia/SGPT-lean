import SGPT.Bergman.SiuKodairaPoleIdeal

/-! The actual critical pole ideal is the existing intrinsic singleton
vanishing ideal at every original stalk, including points away from its pole.
Blueprint: `siu-kodaira-embedding.tex`, node `siu-kodaira:intrinsic-point-ideal`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.Bergman.SiuKodaira

open Set Filter Metric MeasureTheory
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open HermitianHolomorphicLineBundle SGPT.PSH.GlobalL2 SGPT.PSH.SiuL2

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

/-- The original singleton vanishing condition is a value condition at the
point and is vacuous in every other original stalk. -/
theorem vanishingIdeal_singleton_mem_iff (p q : X) (g : X → ℂ) :
    (vanishingIdeal (n := n) ({p} : Set X)).mem q g ↔
      HolomorphicAt n g q ∧ (q = p → g q = 0) := by
  constructor
  · intro hg
    exact ⟨hg.1, fun h => hg.2.self_of_nhds (mem_singleton_iff.mpr h)⟩
  · rintro ⟨hg, hzero⟩
    refine ⟨hg, ?_⟩
    by_cases hqp : q = p
    · exact Eventually.of_forall fun y hy => by
        have hyp : y = p := mem_singleton_iff.mp hy
        subst y
        simpa only [hqp] using hzero hqp
    · filter_upwards [isOpen_compl_singleton.mem_nhds hqp] with y hy
      exact fun h => False.elim (hy h)

variable [MeasurableSpace X] [BorelSpace X]
  {μ : Measure X} {G : HermitianHolomorphicLineBundle.{0, 0} n X}

/-- Equality of the complete original germ ideals, produced from the actual
fixed geometric pole rather than an assumed point-ideal certificate. -/
theorem multiplierIdeal_criticalPointWeight_eq_pointIdeal (hn : 0 < n)
    (D : SiuCover μ G G) {θG : ClosedRealOneOneForm n X} (hKah : θG.val.IsKahler)
    {B : ℝ} (hB0 : 0 < B) (a : Fin D.m) {mω : ℝ}
    (hmω : ∀ w ∈ closedBall (ctr (n := n) (D.pt a)) (D.R a), ∀ v : ComplexModel n,
      mω * ‖v‖ ^ 2 ≤ θG.val.coeff (D.chartX a) w ![v, Complex.I • v])
    (hBm : 2 * poleK / D.siuPoleR a ^ 2 ≤ Real.pi * B * mω)
    {x₀ : X} (hx₀ : x₀ ∈ (D.chartX a).val.source)
    (hp : (D.chartX a).val x₀ ∈ closedBall (ctr (n := n) (D.pt a)) (D.R a / 4)) :
    multiplierIdeal (n := n) 1 (criticalPointWeight D a x₀) =
      vanishingIdeal (n := n) ({x₀} : Set X) := by
  apply GermIdeal.ext
  funext q g
  apply propext
  rw [vanishingIdeal_singleton_mem_iff]
  by_cases hqx : q = x₀
  · subst q
    rw [multiplierIdeal_criticalPointWeight_mem_iff hn D hKah hB0 a hmω hBm hx₀ hp]
    simp only [true_implies]
  · rw [multiplierIdeal_criticalPointWeight_mem_iff_of_ne hn D hKah hB0 a hmω hBm hx₀ hp hqx]
    simp only [hqx, false_implies, and_true]

end SGPT.Bergman.SiuKodaira
