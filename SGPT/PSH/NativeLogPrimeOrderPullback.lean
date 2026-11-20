import SGPT.PSH.NativeCommonPrimeLogPullback
import SGPT.PSH.NativeLogPrimeOrders

set_option autoImplicit false
noncomputable section
namespace SGPT.PSH
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open HolomorphicIdealSheaves AnalyticGermDecomposition InvertibleIdealQuotient DivisorExponent
open scoped Topology Manifold ContDiff
universe u
variable {m : ℕ} {X Y : Type u}
  [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y]

/-- Actual modification geometry and ORIGINAL functions produce the literal
ideal-image total transform, the SAME native QPSH pullback, and actual
DISTINCT primes on ONE original upstairs U with every reduced stalk and a
uniform bound for the literal logarithmic formula on ALL of the SAME U. -/
theorem exists_native_modification_common_open_log_prime_orders
    (D : EffectiveDivisor (m + 1) X) {π : Y → X}
    (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := m + 1) π)
    (u : X → EReal) (hu : (VariableComplexAtlas.ofFixedModel (m + 1) X).IsQPSH u)
    (z0 : Y) (g : X → ℂ)
    (hgen : ∀ᶠ z in 𝓝 (π z0), HolomorphicAt (m + 1) g z ∧ ∀ b,
      D.ideal.mem z b ↔ IsInSpanAt (n := m + 1) (· = g) z b)
    (c : ℚ) (hc : 0 < c) (R : X → ℝ) (hR : BoundedRealGermAt R (π z0))
    (hsource : u =ᶠ[𝓝 (π z0)] fun z => ((c : ℝ) : EReal) * logNormSq (g z) + (R z : EReal)) :
    (VariableComplexAtlas.ofFixedModel (m + 1) Y).IsQPSH (u ∘ π) ∧
    let Δ := GermIdealTotalTransform.EffectiveDivisor.totalTransform hπ.1
      (interior_exceptionalLocus_eq_empty_of_native_analyticModification hπ) D
    Δ.support = π ⁻¹' D.support ∧
    ∃ Ω : Opens (ComplexModel (m + 1)), (0 : ComplexModel (m + 1)) ∈ Ω ∧
      ∃ htarget : ∀ z ∈ Ω, z + (complexChartAt (n := m + 1) z0).val z0 ∈
        (complexChartAt (n := m + 1) z0).val.target,
      z0 ∈ centeredChartOpen z0 Ω ∧
      (∀ y ∈ centeredChartOpen z0 Ω, HolomorphicAt (m + 1) (g ∘ π) y ∧ ∀ b,
        Δ.ideal.mem y b ↔ IsInSpanAt (n := m + 1) (· = (g ∘ π)) y b) ∧
      ∃ (r : ℕ) (q : Fin r → ComplexModel (m + 1) → ℂ)
        (hq : ∀ i, OkaRelationSheaf.HolAt (q i) 0) (a : Fin r → ℕ)
        (p : Fin r → centeredChartOpen z0 Ω → ℂ)
        (W : Fin r → ClosedIrreducibleAnalyticSubvariety (m + 1) (centeredChartOpen z0 Ω))
        (B : Fin r → GlobalComponents.globalComponents (n := m + 1) Δ.support)
        (bU : centeredChartOpen z0 Ω → ℝ) (C : ℝ),
        (∀ i j, i ≠ j → (W i).carrier ≠ (W j).carrier) ∧
        (∀ i, Prime (HolGerm.mk (q i) (hq i)) ∧ 0 < a i ∧
          (∃ hf : OkaRelationSheaf.HolAt (fun z => (g ∘ π) ((complexChartAt (n := m + 1) z0).val.symm
            (z + (complexChartAt (n := m + 1) z0).val z0))) 0,
            a i = multiplicity (HolGerm.mk (q i) (hq i))
              (HolGerm.mk (fun z => (g ∘ π) ((complexChartAt (n := m + 1) z0).val.symm
                (z + (complexChartAt (n := m + 1) z0).val z0))) hf)) ∧
          0 < c * (a i : ℚ) ∧ a i = regularComponentOrder Δ Δ.support (B i) ∧
          p i = (fun y => q i (centeredChartHomeomorph z0 Ω htarget y)) ∧
          (W i).carrier = {y | p i y = 0} ∧ (W i).dim = m ∧
          (∀ y, HolomorphicAt (m + 1) (p i) y) ∧
          ∀ (y : centeredChartOpen z0 Ω) (b : centeredChartOpen z0 Ω → ℂ),
            (vanishingIdeal (n := m + 1) (W i).carrier).mem y b ↔
              IsInSpanAt (n := m + 1) (· = p i) y b) ∧
        (∀ y : centeredChartOpen z0 Ω, (y : Y) ∈ Δ.support ↔ ∃ i, y ∈ (W i).carrier) ∧
        0 ≤ C ∧ (∀ y, |bU y| ≤ C) ∧
        (∀ y : centeredChartOpen z0 Ω, (u ∘ π) y =
          (∑ i, (((c * (a i : ℚ) : ℚ) : ℝ) : EReal) * logNormSq (p i y)) + (bU y : EReal)) ∧
        ∀ i, ∃ y : centeredChartOpen z0 Ω, y ∈ (W i).carrier ∧
          RegularAtDim (n := m + 1) Δ.support (y : Y) m ∧
          divExp (m + 1) Δ.ideal (Subtype.val '' (W i).carrier) (y : Y) = a i ∧
          ∀ d : ℕ, IsDivNear (m + 1) Δ.ideal (Subtype.val '' (W i).carrier) d (y : Y) ↔ d ≤ a i := by
  refine ⟨hu.comp_native_analyticModification hπ, ?_⟩
  let Δ := GermIdealTotalTransform.EffectiveDivisor.totalTransform hπ.1
    (interior_exceptionalLocus_eq_empty_of_native_analyticModification hπ) D
  have hsupport : Δ.support = π ⁻¹' D.support :=
    BlowupExceptionalDivisor.zeroLocus_pullback hπ.1
      (DivisorMetric.isCoherent_of_isInvertible D.isInvertible)
  have hgencomp : ∀ᶠ z in 𝓝 z0, HolomorphicAt (m + 1) (g ∘ π) z ∧ ∀ b,
      Δ.ideal.mem z b ↔ IsInSpanAt (n := m + 1) (· = g ∘ π) z b := by
    filter_upwards [(hπ.1.continuous.tendsto z0).eventually hgen] with z hgz
    exact ⟨hgz.1.comp_contMDiff (Eventually.of_forall fun w => hπ.1.contMDiffAt),
      fun b => MemberPullback.pullback_mem_iff_of_generator hπ.1 hgz.1 hgz.2 b⟩
  have hRcomp : BoundedRealGermAt (R ∘ π) z0 :=
    hR.comp_continuousAt hπ.1.continuous.continuousAt
  have hsourcecomp : (u ∘ π) =ᶠ[𝓝 z0] fun z => ((c : ℝ) : EReal) * logNormSq ((g ∘ π) z) +
      ((R ∘ π) z : EReal) := (hπ.1.continuous.tendsto z0).eventually hsource
  exact ⟨hsupport, exists_native_common_open_log_prime_orders
    Δ z0 (g ∘ π) hgencomp c hc (u ∘ π) (R ∘ π) hRcomp hsourcecomp⟩


#print axioms exists_native_modification_common_open_log_prime_orders
end SGPT.PSH
