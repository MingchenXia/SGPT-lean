import SGPT.PSH.LocalIntegralOpenCoefficients
import SGPT.PSH.OriginalAnalyticConventions

set_option autoImplicit false
noncomputable section
namespace SGPT.PSH
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending
open scoped Topology Manifold ContDiff

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The ORIGINAL finite rational logarithms and one bound on an original
open produce an actual connected intrinsic analytic presentation. The local
denominator and singleton product are manufactured internally, including poles
and empty families. -/
theorem exists_native_rational_analytic_presentation_of_finite_logs
    (U : Opens M) (x : M) (hx : x ∈ U) {r : ℕ}
    (p : Fin r → U → ℂ) (hp : ∀ i y, HolomorphicAt n (p i) y)
    (w : Fin r → ℚ) (hw : ∀ i, 0 < w i) (u : M → EReal)
    (R : U → ℝ) (C : ℝ) (hC : 0 ≤ C) (hR : ∀ y, |R y| ≤ C)
    (hu : ∀ y : U, u y =
      (∑ i, ((w i : ℝ) : EReal) * logNormSq (p i y)) + (R y : EReal)) :
    (VariableComplexAtlas.ofFixedModel n M).HasRationalAnalyticPresentationAt u x := by
  classical
  obtain ⟨d, a, hd, _ha, hlog⟩ := exists_finite_rational_logarithmic_product_grouping
    (Finset.univ : Finset (Fin r)) w (fun i _ => hw i)
  let f : Fin r → M → ℂ := fun i => extendOpens U (p i)
  let G : M → ℂ := fun y => ∏ i, f i y ^ a i
  have hG (y : M) (hy : y ∈ U) : HolomorphicAt n G y := by
    apply MonomialPart.holomorphicAt_finset_prod Finset.univ
    intro i _
    exact CompanionReduction.holomorphicAt_pow_of
      ((holomorphicAt_iff_extendOpens U).mp (hp i ⟨y, hy⟩)) (a i)
  have hgroup (y : U) :
      (∑ i, ((w i : ℝ) : EReal) * logNormSq (p i y)) =
        (((1 / (d : ℚ) : ℚ) : ℝ) : EReal) * logNormSq (G y) := by
    simpa [Finset.sum_coe_sort, Finset.prod_coe_sort, G, f] using hlog (fun i => p i y)
  let b : M → ℝ := fun y => if hy : y ∈ U then R ⟨y, hy⟩ else 0
  have hb (y : M) (hy : y ∈ U) : b y = R ⟨y, hy⟩ := by
    dsimp only [b]
    rw [dif_pos hy]
  let : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace (ComplexModel n) M
  obtain ⟨V, ⟨hV, hxV, hconn⟩, hVU⟩ :=
    (LocallyConnectedSpace.open_connected_basis x).mem_iff.mp (U.isOpen.mem_nhds hx)
  refine ⟨1 / (d : ℚ), 1, (fun _ => G), b, C, V,
    by positivity, hC, hV, hconn, hxV, ?_, ?_, ?_⟩
  · intro _
    apply (VariableComplexAtlas.chartHolomorphicOn_iff_native hV).mpr
    intro y hy
    exact (hG y (hVU hy)).mdifferentiableAt.mdifferentiableWithinAt
  · intro y hy
    rw [hb y (hVU hy)]
    exact hR ⟨y, hVU hy⟩
  · intro y hy
    have hsingle : generatorLog (fun _ : Fin 1 => G) y = logNormSq (G y) := by
      rw [generatorLog_eq_log_sum]
      simp [logNormSq]
    change u y = (((1 / (d : ℚ) : ℚ) : ℝ) : EReal) *
      generatorLog (fun _ : Fin 1 => G) y + (b y : EReal)
    rw [hsingle]
    rw [hb y (hVU hy)]
    exact (hu ⟨y, hVU hy⟩).trans (congrArg (fun t => t + (R ⟨y, hVU hy⟩ : EReal))
      (hgroup ⟨y, hVU hy⟩))

section Logarithmic
variable {m : ℕ} {X : Type*} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]

open Classical in
/-- Source Definition1.6.2 in native positive uniform dimension: genuine
QPSH and a finite DISTINCT actual prime presentation of the ENTIRE actual
restricted divisor, SAME defining equations at EVERY reduced stalk, and one
bounded real logarithmic remainder on ALL of the original chosen open. -/
def NativeHasLogSingularitiesAlong
    (D : EffectiveGeometricQDivisor (m + 1) X) (u : X → EReal) : Prop :=
  (VariableComplexAtlas.ofFixedModel (m + 1) X).IsQPSH u ∧
    ∀ x : X, ∃ U : Opens X, x ∈ U ∧
      ∃ (r : ℕ) (W : Fin r → GeometricPrimeCarrier (m + 1) U)
        (a : Fin r → ℚ) (p : Fin r → U → ℂ) (R : U → ℝ) (C : ℝ),
        Function.Injective W ∧ (∀ i, 0 < a i) ∧
        (∀ i y, HolomorphicAt (m + 1) (p i) y) ∧
        (∀ i y b, (vanishingIdeal (n := m + 1) (W i).val).mem y b ↔
          IsInSpanAt (n := m + 1) (· = p i) y b) ∧
        (∀ A : GeometricPrimeCarrier (m + 1) U,
          (geometricQDivisorOpenRestriction D U).coefficient A =
            ∑ i, if W i = A then a i else 0) ∧
        0 ≤ C ∧ (∀ y, |R y| ≤ C) ∧
        ∀ y : U, u y =
          (∑ i, ((a i : ℝ) : EReal) * logNormSq (p i y)) + (R y : EReal)

/-- The source's actual logarithmic singularities imply genuine intrinsic
rational analytic singularities of the SAME original potential. -/
theorem NativeHasLogSingularitiesAlong.intrinsic
    {D : EffectiveGeometricQDivisor (m + 1) X} {u : X → EReal}
    (hu : NativeHasLogSingularitiesAlong D u) :
    (VariableComplexAtlas.ofFixedModel (m + 1) X).HasRationalAnalyticType u := by
  intro x
  obtain ⟨U, hx, _r, _W, a, p, R, C, _hW, ha, hp, _hideal, _hcoeff, hC, hR, heq⟩ := hu.2 x
  exact exists_native_rational_analytic_presentation_of_finite_logs U x hx p hp a ha u R C hC hR heq

end Logarithmic
end SGPT.PSH
