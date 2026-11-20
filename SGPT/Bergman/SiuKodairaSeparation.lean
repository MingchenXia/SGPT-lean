import SGPT.Bergman.SiuKodairaBaseGeneration
import SGPT.Bergman.SiuKodairaGermSpan
import SGPT.Bergman.SiuKodairaNativeSection

/-!
# Actual positive-power sections separate values and first derivatives

Every section below is produced from the original point-ideal generation
relation. Evaluation and differentiation of that finite actual relation
supply the required nonzero native values and derivatives.
Blueprint: `siu-kodaira-embedding.tex`, node `siu-kodaira:separation`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.Bergman.SiuKodaira

open Set Filter Metric Bundle
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open SGPT.Bergman.QuantizationDraft
open HermitianHolomorphicLineBundle
open SGPT.PSH.GlobalL2 SGPT.PSH.LineBundleMetric SGPT.Trace.BertiniGlobalGeneration
open SGPT.NAPotential.GAGAMult

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] (E : HermitianHolomorphicLineBundle.{0, 0} n X)

/-- An actual global section of the original point ideal vanishes in its
original fibre at that point. -/
theorem eq_zero_of_isBaseSectionIn_pointIdeal {p : X} {s : (x : X) → E.Fiber x}
    (hs : IsBaseSectionIn E (vanishingIdeal (n := n) ({p} : Set X)) s) : s p = 0 := by
  let e := prefFrame E p
  let := e.property
  have he : p ∈ e.val.baseSet := mem_prefFrame E p
  have hi := hs.2 p e he
  have hz : e.val.continuousLinearMapAt ℂ p (s p) = 0 :=
    ((vanishingIdeal_singleton_mem_iff p p _).mp hi).2 rfl
  have h := trivialization_eq_coef_smul_frame e.val he (s p)
  rw [hz, zero_smul] at h
  exact h

/-- Evaluate the generated unit germ at a different point and retain the
actual original section, rather than only a nonzero scalar germ. -/
theorem exists_section_vanish_ne_of_pointIdeal_generation {p q : X} (hpq : p ≠ q)
    (hgen : IsBaseGloballyGenerated E (vanishingIdeal (n := n) ({p} : Set X))) :
    ∃ s : HolomorphicSections (n := n) E.Fiber, s p = 0 ∧ s q ≠ 0 := by
  let e := prefFrame E q
  let := e.property
  have he : q ∈ e.val.baseSet := mem_prefFrame E q
  have hunit : (vanishingIdeal (n := n) ({p} : Set X)).mem q (fun _ => 1) :=
    (vanishingIdeal_singleton_mem_iff p q _).mpr
      ⟨Eventually.of_forall fun _ => mdifferentiableAt_const,
        fun hqp => False.elim (hpq hqp.symm)⟩
  have hspan := hgen q e he (fun _ => 1) hunit
  obtain ⟨h, ⟨s, hs, hcoef⟩, h0⟩ := exists_generator_ne_zero_of_isInSpanAt hspan one_ne_zero
  refine ⟨nativeSectionOfHolomorphic E s hs.1, eq_zero_of_isBaseSectionIn_pointIdeal E hs, ?_⟩
  intro hs0
  apply h0
  change s q = 0 at hs0
  have hz := congrArg (e.val.continuousLinearMapAt ℂ q) hs0
  have hz' : e.val.continuousLinearMapAt ℂ q (s q) = 0 := by
    simpa only [map_zero] using hz
  exact (congrFun hcoef q).trans hz'

/-- Positive dimension supplies another original point; its generated point
ideal produces a genuine section nonzero at the requested point. -/
theorem exists_section_nonzero_of_pointIdeals_generation (hn : 0 < n)
    (hgen : ∀ p : X, IsBaseGloballyGenerated E (vanishingIdeal (n := n) ({p} : Set X)))
    (q : X) : ∃ s : HolomorphicSections (n := n) E.Fiber, s q ≠ 0 := by
  obtain ⟨p, -, hpq⟩ := exists_ne_mem_of_isOpen hn isOpen_univ (mem_univ q)
  obtain ⟨s, -, hsq⟩ := exists_section_vanish_ne_of_pointIdeal_generation E hpq (hgen p)
  exact ⟨s, hsq⟩

/-- The finite original point-ideal germ relation produces a genuine global
section with a nonzero first derivative in any chosen original chart/frame. -/
theorem exists_section_derivative_ne_of_pointIdeal_generation
    {p : X} (hgen : IsBaseGloballyGenerated E (vanishingIdeal (n := n) ({p} : Set X)))
    (e : AtlasFrame E) (he : p ∈ e.val.baseSet)
    (c : ComplexChart n X) (hc : p ∈ c.val.source) (v : ComplexModel n) (hv : v ≠ 0) :
    ∃ s : HolomorphicSections (n := n) E.Fiber, s p = 0 ∧
      fderiv ℂ (fun z => e.val.continuousLinearMapAt ℂ (c.val.symm z) (s (c.val.symm z)))
        (c.val p) v ≠ 0 := by
  classical
  let := e.property
  obtain ⟨j, hj⟩ : ∃ j : Fin n, v j ≠ 0 := by
    by_contra h
    push Not at h
    apply hv
    ext j
    simpa only [PiLp.zero_apply] using h j
  let g : X → ℂ := fun y => centredCoords (c.val p) j (c.val y)
  have hg : HolomorphicAt n g p :=
    DemaillyApproximationAnalyticType.holomorphicAt_comp_atlas hc
      (Eventually.of_forall fun z => differentiable_centredCoords (c.val p) j z)
  have hg0 : g p = 0 := centredCoords_self _ _
  have hmem : (vanishingIdeal (n := n) ({p} : Set X)).mem p g :=
    (vanishingIdeal_singleton_mem_iff p p g).mpr ⟨hg, fun _ => hg0⟩
  have hspan := hgen p e he g hmem
  have hder : fderiv ℂ (fun z => g (c.val.symm z)) (c.val p) v ≠ 0 := by
    have heq : (fun z => g (c.val.symm z)) =ᶠ[𝓝 (c.val p)] centredCoords (c.val p) j := by
      filter_upwards [c.val.open_target.mem_nhds (c.val.map_source hc)] with z hz
      dsimp only [g]
      rw [c.val.right_inv hz]
    rw [heq.fderiv_eq]
    have hfd : fderiv ℂ (centredCoords (c.val p) j) (c.val p) = EuclideanSpace.proj (𝕜 := ℂ) j :=
      ((EuclideanSpace.proj (𝕜 := ℂ) j).hasFDerivAt.sub_const ((c.val p) j)).fderiv
    rw [hfd]
    exact hj
  obtain ⟨h, hh, hderh⟩ := exists_generator_derivative_ne_zero_of_isInSpanAt hspan
    (fun h hh => by
      obtain ⟨s, hs, rfl⟩ := hh
      exact (hs.2 p e he).1)
    (fun h hh => by
      obtain ⟨s, hs, rfl⟩ := hh
      exact ((vanishingIdeal_singleton_mem_iff p p _).mp (hs.2 p e he)).2 rfl)
    c hc v hder
  obtain ⟨s, hs, rfl⟩ := hh
  exact ⟨nativeSectionOfHolomorphic E s hs.1, eq_zero_of_isBaseSectionIn_pointIdeal E hs, hderh⟩

/-- One literal original positive power has actual global sections separating
all original points and all nonzero original chart tangent vectors. -/
theorem exists_positivePower_point_tangent_separation [CompactSpace X] (hn : 0 < n)
    (G : HermitianHolomorphicLineBundle.{0, 0} n X) (hG : IsSourceSmoothHermitianMetric G)
    (θG : ClosedRealOneOneForm n X) (hθG : IsOwnFirstChernForm G θG) (hKah : θG.val.IsKahler) :
    ∃ d : ℕ, 0 < d ∧
      (∀ p : X, ∃ s : HolomorphicSections (n := n) (positivePower G (d - 1)).Fiber, s p ≠ 0) ∧
      (∀ p q : X, p ≠ q → ∃ s : HolomorphicSections (n := n) (positivePower G (d - 1)).Fiber,
        s p = 0 ∧ s q ≠ 0) ∧
      ∀ (p : X) (e : AtlasFrame (positivePower G (d - 1))), p ∈ e.val.baseSet →
        ∀ (c : ComplexChart n X), p ∈ c.val.source → ∀ v : ComplexModel n, v ≠ 0 →
          ∃ s : HolomorphicSections (n := n) (positivePower G (d - 1)).Fiber, s p = 0 ∧
            fderiv ℂ (fun z => e.val.continuousLinearMapAt ℂ (c.val.symm z) (s (c.val.symm z)))
              (c.val p) v ≠ 0 := by
  obtain ⟨d, hd, hgen⟩ := exists_positivePower_generates_pointIdeals hn G hG θG hθG hKah
  exact ⟨d, hd, exists_section_nonzero_of_pointIdeals_generation _ hn hgen,
    fun p q hpq => exists_section_vanish_ne_of_pointIdeal_generation _ hpq (hgen p),
    fun p e he c hc v hv => exists_section_derivative_ne_of_pointIdeal_generation _ (hgen p) e he c hc v hv⟩

end SGPT.Bergman.SiuKodaira
