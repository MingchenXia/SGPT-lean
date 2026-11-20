import SGPT.Toric.ToricMonomialChart
import SGPT.Okounkov.ActualPrincipalLogDivisor
import SGPT.Okounkov.TranscendentalPoleExtension
import SGPT.Foundations.Analysis.Pending.IdealComparisonResidual

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set Filter MeasureTheory SGPT.PSH SGPT.PSH.VariableComplexAtlas SGPT.Convex
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.GlobalAnalyticSingularities
open MeteredDivisorSingleGenerator
open scoped Topology ContDiff BigOperators Manifold ENNReal

variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- The actual original global section coefficient in a specified original
vertex frame, extended as a function only to name its native germs. -/
def monomialChartCoefficient (D : ToricDivisor γ hs) (q : ℕ) (m : Fin n → ℤ)
    (v : latticePolytopeVertices γ) : PolytopeToricVariety γ hs → ℂ :=
  fun y => toricMonomial ((q : ℤ) • D) v m (originalPolytopeNativeModelChart γ hs v y)

theorem monomialChartCoefficient_holomorphic (D : ToricDivisor γ hs) (q : ℕ)
    (m : Fin n → ℤ) (v : latticePolytopeVertices γ) :
    MDifferentiableOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ)
      (monomialChartCoefficient D q m v) (originalPolytopeNativeModelChart γ hs v).source := by
  intro y hy
  exact (holomorphicAt_comp_vertexChart v hy (Eventually.of_forall fun _ =>
    (differentiable_toricMonomial ((q : ℤ) • D) v m).differentiableAt)).mdifferentiableAt.mdifferentiableWithinAt

theorem monomialChartCoefficient_nowhereZero {D : ToricDivisor γ hs} {q : ℕ}
    {m : Fin n → ℤ} (hm : m ∈ toricLatticePoints ((q : ℤ) • D))
    (v : latticePolytopeVertices γ) :
    NowhereIdenticallyZeroOn (monomialChartCoefficient D q m v)
      (originalPolytopeNativeModelChart γ hs v).source := by
  intro W hW _ hne
  obtain ⟨a, ha⟩ := (denseRange_originalPolytopeNativeOrbitMap γ).exists_mem_open hW hne
  refine ⟨polytopeToricEmbedding γ hs a, ha, ?_⟩
  intro hzero
  have hchar := latticeCharacter_eq_toricMonomial (hs := hs) ((q : ℤ) • D) hm v a
  change toricMonomial ((q : ℤ) • D) v m
    (originalPolytopeNativeModelChart γ hs v (polytopeToricEmbedding γ hs a)) = 0 at hzero
  rw [hzero, zero_mul] at hchar
  exact (Units.ne_zero (latticeCharacter m a)) hchar

namespace BigToricMetric
variable {D : ToricDivisor γ hs} (h : BigToricMetric D)

/-- The literal smooth metric remainder in the actual monomial section frame. -/
def monomialChartRemainder (q : ℕ) (v : latticePolytopeVertices γ) :
    PolytopeToricVariety γ hs → ℝ :=
  fun y => -(q : ℝ) * h.weight v (originalPolytopeNativeModelChart γ hs v y)

theorem monomialChartRemainder_continuousAt (q : ℕ) (v : latticePolytopeVertices γ)
    {y : PolytopeToricVariety γ hs} (hy : y ∈ (originalPolytopeNativeModelChart γ hs v).source) :
    ContinuousAt (h.monomialChartRemainder q v) y := by
  exact continuousAt_const.mul ((h.smooth v).continuous.continuousAt.comp
    ((originalPolytopeNativeModelChart γ hs v).continuousAt hy))

/-- Genuine section logarithm identity on the original chart source,
with its actual metric remainder and all zeros retained. -/
theorem monomialPotential_log_presentation {q : ℕ} (hq : 0 < q) {m : Fin n → ℤ}
    (hm : m ∈ toricLatticePoints ((q : ℤ) • D))
    (v : latticePolytopeVertices γ) {y : PolytopeToricVariety γ hs}
    (hy : y ∈ (originalPolytopeNativeModelChart γ hs v).source) :
    ((q : ℝ) : EReal) * h.monomialPotential hq hm y =
      singleLog (monomialChartCoefficient D q m v) y +
        (h.monomialChartRemainder q v y : EReal) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have heq := h.monomialPotential_chart hq hm v
    (originalPolytopeNativeModelChart γ hs v y)
  rw [(originalPolytopeNativeModelChart γ hs v).left_inv hy] at heq
  have hcancel : ((q : ℝ) : EReal) * (((q : ℝ)⁻¹ : ℝ) : EReal) = 1 := by
    rw [← EReal.coe_mul, mul_inv_cancel₀ hqR.ne', EReal.coe_one]
  have hscaled := congrArg (fun t : EReal => ((q : ℝ) : EReal) * t) heq
  rw [EReal.left_distrib_of_nonneg_of_ne_top (EReal.coe_nonneg.mpr hqR.le)
      (EReal.coe_ne_top _), ← mul_assoc,
    hcancel, one_mul, ← EReal.coe_mul] at hscaled
  have hs' : ((q : ℝ) : EReal) * h.monomialPotential hq hm y +
      ((q * h.weight v (originalPolytopeNativeModelChart γ hs v y) : ℝ) : EReal) =
      singleLog (monomialChartCoefficient D q m v) y + ((0 : ℝ) : EReal) := by
    simpa only [singleLog, SGPT.Okounkov.TranscendentalCore.generatorLog_single,
      logNormSq, monomialChartCoefficient, EReal.coe_zero, add_zero] using hscaled
  have ht := MeteredDivisorGlobalIdeal.eq_add_sub_of_add_eq_add hs'
  simpa only [zero_sub, monomialChartRemainder, neg_mul] using ht

/-- The SAME original monomial current manufactures an actual effective
divisor ideal. Every original chart coefficient is proved to generate it. -/
theorem exists_monomial_effectiveDivisor {q : ℕ} (hq : 0 < q) {m : Fin n → ℤ}
    (hm : m ∈ toricLatticePoints ((q : ℤ) • D)) :
    ∃ E : EffectiveDivisor n (PolytopeToricVariety γ hs),
      HasAnalyticSingularitiesOfType
        (fun y => ((q : ℝ) : EReal) * h.monomialPotential hq hm y) 1 E.ideal ∧
      ∀ (v : latticePolytopeVertices γ) y,
        y ∈ (originalPolytopeNativeModelChart γ hs v).source → ∀ f,
        E.ideal.mem y f ↔ IsInSpanAt (n := n)
          (· = monomialChartCoefficient D q m v) y f := by
  have hd : ∀ x : PolytopeToricVariety γ hs, ∃ U : Set (PolytopeToricVariety γ hs),
      IsOpen U ∧ x ∈ U ∧ ∃ (G : PolytopeToricVariety γ hs → ℂ)
        (r : PolytopeToricVariety γ hs → ℝ),
      MDifferentiableOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) G U ∧
      NowhereIdenticallyZeroOn G U ∧ (∀ y ∈ U, ContinuousAt r y) ∧
      ∀ y ∈ U, ((q : ℝ) : EReal) * h.monomialPotential hq hm y =
        singleLog G y + (r y : EReal) := by
    intro x
    obtain ⟨v, hv⟩ := originalPolytopeNativeModelChart_cover γ hs x
    exact ⟨_, (originalPolytopeNativeModelChart γ hs v).open_source, hv,
      monomialChartCoefficient D q m v, h.monomialChartRemainder q v,
      monomialChartCoefficient_holomorphic D q m v,
      monomialChartCoefficient_nowhereZero hm v,
      fun _ hy => h.monomialChartRemainder_continuousAt q v hy,
      fun _ hy => h.monomialPotential_log_presentation hq hm v hy⟩
  obtain ⟨E, hE, hread⟩ := SGPT.Okounkov.exists_effectiveDivisor_of_log_presentation _ hd
  refine ⟨E, hE, fun v => ?_⟩
  exact hread _ (originalPolytopeNativeModelChart γ hs v).open_source
    (monomialChartCoefficient D q m v) (h.monomialChartRemainder q v)
    (monomialChartCoefficient_holomorphic D q m v)
    (monomialChartCoefficient_nowhereZero hm v)
    (fun _ hy => h.monomialChartRemainder_continuousAt q v hy)
    (fun _ hy => h.monomialPotential_log_presentation hq hm v hy)

/-- Rational normalization preserves the actual global coherent analytic
type; the ideal is the original monomial divisor just constructed. -/
theorem monomialPotential_hasAnalyticSingularities {q : ℕ} (hq : 0 < q) {m : Fin n → ℤ}
    (hm : m ∈ toricLatticePoints ((q : ℤ) • D)) :
    HasAnalyticSingularities (n := n) (h.monomialPotential hq hm) := by
  obtain ⟨E, hE, _⟩ := h.exists_monomial_effectiveDivisor hq hm
  have hqQ : (0 : ℚ) < q := by exact_mod_cast hq
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have ht := IdealComparisonResidual.hasAnalyticSingularitiesOfType_smul
    (inv_pos.mpr hqQ) hE
  refine ⟨(q : ℚ)⁻¹, E.ideal, ?_⟩
  simpa only [Rat.cast_inv, Rat.cast_natCast, mul_one, ← mul_assoc,
    ← EReal.coe_mul, inv_mul_cancel₀ hqR, EReal.coe_one, one_mul] using ht

end BigToricMetric
end SGPT.Toric
