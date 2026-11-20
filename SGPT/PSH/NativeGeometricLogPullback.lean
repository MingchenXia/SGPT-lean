import SGPT.PSH.NativeCommonCartierWithin
import SGPT.PSH.NativeLogIntegralEquation
import SGPT.PSH.GeometricQOpenCartierCompatibility
import SGPT.PSH.FiniteCartierPullback
import SGPT.PSH.NativeQPSHPullback

set_option autoImplicit false
noncomputable section
namespace SGPT.PSH
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open HolomorphicIdealSheaves
open scoped Topology Manifold ContDiff

universe u
variable {m : ℕ} {X Y : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y]

/-- ORIGINAL D,u and actual modification retain the EXACT integral F/d/S
chosen from the source logarithmic potential, manufacture its genuine
grouped pullback coefficients, and internally produce every field of the
native logarithmic predicate on one original open at each upstairs point. -/
theorem NativeHasLogSingularitiesAlong.comp_native_analyticModification
    {D : EffectiveGeometricQDivisor (m + 1) X} {u : X → EReal}
    (hu : NativeHasLogSingularitiesAlong D u) {π : Y → X}
    (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := m + 1) π) :
    NativeHasLogSingularitiesAlong (geometricQDivisorModificationPullback D hπ) (u ∘ π) := by
  classical
  refine ⟨hu.1.comp_native_analyticModification hπ, ?_⟩
  intro y
  obtain ⟨V, hxV, s, d, a, hs, hd, ha, g, hgen, b, hb, hlog⟩ :=
    hu.exists_original_integral_equation (π y)
  let F := ∑ P ∈ s, a P • geometricPrimeCarrierEffectiveDivisor P.val
  let H := cartierModificationPullback hπ F
  have hHsum : H = ∑ P ∈ s, a P • geometricPrimeCarrierTotalTransform P.val hπ :=
    cartierModificationPullback_finite_prime_sum hπ s (fun P => P.val) a
  have hglobal (A : GeometricPrimeCarrier (m + 1) Y)
      (hA : (A.val ∩ π ⁻¹' (V : Set X)).Nonempty) :
      (geometricQDivisorModificationPullback D hπ).coefficient A =
        (cartierGeometricPrimeCoefficient H A : ℚ) / (d : ℚ) := by
    rw [geometricQDivisorModificationPullback_local_coefficient D hπ V s hs A hA,
      hHsum, cartierGeometricPrimeCoefficient_finset_sum, Nat.cast_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro P hP
    rw [(ha P hP).2, Nat.cast_mul]
    ring
  have hgencomp : ∀ᶠ z in 𝓝 y, HolomorphicAt (m + 1) (g ∘ π) z ∧ ∀ f,
      H.ideal.mem z f ↔ IsInSpanAt (n := m + 1) (· = g ∘ π) z f := by
    filter_upwards [(hπ.1.continuous.tendsto y).eventually hgen] with z hgz
    refine ⟨hgz.1.comp_contMDiff (Eventually.of_forall fun _ => hπ.1.contMDiffAt), ?_⟩
    intro f
    exact MemberPullback.pullback_mem_iff_of_generator hπ.1 hgz.1 hgz.2 f
  have hbcomp : BoundedRealGermAt (b ∘ π) y := hb.comp_continuousAt hπ.1.continuous.continuousAt
  have hlogcomp : (u ∘ π) =ᶠ[𝓝 y] fun z =>
      (((1 / (d : ℚ) : ℚ) : ℝ) : EReal) * logNormSq ((g ∘ π) z) + ((b ∘ π) z : EReal) :=
    (hπ.1.continuous.tendsto y).eventually hlog
  have hdQ : (0 : ℚ) < d := by exact_mod_cast hd
  have hN : π ⁻¹' (V : Set X) ∈ 𝓝 y :=
    (hπ.1.continuous.tendsto y).eventually (V.isOpen.mem_nhds hxV)
  obtain ⟨U, hyU, hUN, _hgenU, r, W, e, p, _v, R, C,
    hW, he, hp, hideal, _hv, _hfactor, hCartier, hC, hbound, hlogU⟩ :=
    exists_native_common_open_cartier_prime_logarithms_within H y (g ∘ π) hgencomp
      (1 / (d : ℚ)) (by positivity) (u ∘ π) (b ∘ π) hbcomp hlogcomp
      (π ⁻¹' (V : Set X)) hN
  refine ⟨U, hyU, r, W, (fun i => (e i : ℚ) / (d : ℚ)), p, R, C,
    hW, (fun i => div_pos (by exact_mod_cast he i) hdQ), hp, hideal, ?_, hC, hbound, ?_⟩
  · intro A
    have hA : (A.val ∩ (Subtype.val : U → Y) ⁻¹' (π ⁻¹' (V : Set X))).Nonempty := by
      obtain ⟨z, hz⟩ := A.nonempty
      exact ⟨z, hz, hUN z.2⟩
    have hreader := geometricQDivisorOpenRestriction_coefficient_of_local_cartier_coefficients
      (geometricQDivisorModificationPullback D hπ) H (1 / (d : ℚ)) (by positivity)
      (π ⁻¹' (V : Set X)) (fun A hA => by rw [hglobal A hA]; ring) U A hA
    rw [hreader, hCartier, cartierGeometricPrimeCoefficient_finset_sum,
      Nat.cast_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : W i = A
    · simp [cartierGeometricPrimeCoefficient_reduced, hi, div_eq_mul_inv, mul_comm]
    · simp [cartierGeometricPrimeCoefficient_reduced, hi, Ne.symm hi]
  · intro z
    have hweights (i : Fin r) : (1 / (d : ℚ)) * (e i : ℚ) = (e i : ℚ) / (d : ℚ) := by ring
    simpa only [hweights] using hlogU z

end SGPT.PSH
