import SGPT.Checks.Comparison.TraceNativeAnalyticNonzero
import SGPT.Checks.Comparison.TraceNativePrimeFamilyOrder

/-! The SAME original global rational analytic type in actual native flat coordinates.
Blueprint: `trace-native-prime-reader.tex`. No smooth-remainder strengthening. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.NAPotential.TraceComparison.NativeImage

open Set Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.GlobalAnalyticSingularities
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open FixedGermNormalOrder DemaillyApproximantDivisorialLelong
open scoped Topology Manifold ContDiff ENNReal

/-- Original global analytic type gives its SAME rational coefficient,
actual entire local generators, genuine flat holomorphy/nonvanishing and
literal bounded-remainder formula in the SAME actual prime flattening. -/
theorem exists_actualFlatPresentation_of_globalAnalyticType
    {m : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (ComplexModel (m+1)) M]
    [IsComplexManifold (m+1) M] {u : M → EReal} (hu : LocallyNondegenerate u)
    {c : ℚ} {A : GermIdeal (m+1) M}
    (htype : HasAnalyticSingularitiesOfType (n := m+1) u c A)
    {E : Set M} {x : M} (Φ : DivisorFlattening (m := m) E x) :
    ∃ (N : ℕ) (g : Fin N → M → ℂ) (_hg : ∀ j, HolomorphicAt (m+1) (g j) x),
      (∀ v, A.mem x v ↔ IsInSpanAt (n := m+1) (· ∈ range g) x v) ∧
      (∀ j, ∀ᶠ z in 𝓝 (0 : ComplexModel (m+1)),
        DifferentiableAt ℂ (fun w => g j (Φ.point w)) z) ∧
      (∃ j, ¬ ∀ᶠ z in 𝓝 (0 : ComplexModel (m+1)), g j (Φ.point z) = 0) ∧
      ∃ b : ComplexModel (m+1) → ℝ, BoundedRealGermAt b 0 ∧
        (fun z => u (Φ.point z)) =ᶠ[𝓝 (0 : ComplexModel (m+1))]
          (fun z => ((c : ℝ) : EReal) * generatorLog (fun j w => g j (Φ.point w)) z + (b z : EReal)) := by
  obtain ⟨hc, _hcoh, hlocal⟩ := htype
  obtain ⟨U, hU, hxU, N, g, hgd, hgen, R, C, hRC, heq⟩ := hlocal x
  have hg (j : Fin N) : HolomorphicAt (m+1) (g j) x :=
    InvertibleIdealQuotient.holomorphicAt_of_mdifferentiableOn hU (hgd j) hxU
  have hpointT : Tendsto Φ.point (𝓝 (0 : ComplexModel (m+1))) (𝓝 x) := by
    simpa only [Φ.point_zero] using (Φ.mdifferentiableAt_point Φ.zero_mem_target).continuousAt.tendsto
  have hpointU : ∀ᶠ z in 𝓝 (0 : ComplexModel (m+1)), Φ.point z ∈ U :=
    hpointT.eventually (hU.mem_nhds hxU)
  have hF (j : Fin N) : ∀ᶠ z in 𝓝 (0 : ComplexModel (m+1)),
      DifferentiableAt ℂ (fun w => g j (Φ.point w)) z := by
    filter_upwards [hpointT.eventually (hg j),
      Φ.Φ.isOpen_target.mem_nhds Φ.zero_mem_target] with z hz hzT
    exact mdifferentiableAt_iff_differentiableAt.mp (hz.comp z (Φ.mdifferentiableAt_point hzT))
  let b : ComplexModel (m+1) → ℝ := fun z => R (Φ.point z)
  have hb : BoundedRealGermAt b 0 :=
    ⟨C, (abs_nonneg (R x)).trans (hRC x hxU), hpointU.mono fun z hz => hRC _ hz⟩
  have hrep : (fun z => u (Φ.point z)) =ᶠ[𝓝 (0 : ComplexModel (m+1))]
      (fun z => ((c : ℝ) : EReal) * generatorLog (fun j w => g j (Φ.point w)) z + (b z : EReal)) :=
    hpointU.mono fun z hz => heq _ hz
  have hne : ∃ j, ¬ ∀ᶠ z in 𝓝 (0 : ComplexModel (m+1)), g j (Φ.point z) = 0 := by
    by_contra hn
    have hzero : ∀ j, ∀ᶠ z in 𝓝 (0 : ComplexModel (m+1)), g j (Φ.point z) = 0 := by
      simpa only [not_exists, not_not] using hn
    have hbotPull : ∀ᶠ z in 𝓝 (0 : ComplexModel (m+1)), u (Φ.point z) = ⊥ := by
      filter_upwards [hrep, eventually_all.mpr hzero] with z hz hzall
      rw [hz, (generatorLog_eq_bot_iff (fun j w => g j (Φ.point w)) z).mpr hzall,
        EReal.coe_mul_bot_of_pos (Rat.cast_pos.mpr hc), EReal.bot_add]
    have hcoordT : Tendsto Φ.coord (𝓝 x) (𝓝 (0 : ComplexModel (m+1))) := by
      simpa only [Φ.coord_x] using Φ.mdifferentiableAt_coord.continuousAt.tendsto
    have hbot : ∀ᶠ y in 𝓝 x, u y = ⊥ := by
      filter_upwards [hcoordT.eventually hbotPull, Φ.eventually_point_coord] with y hy he
      rwa [he] at hy
    obtain ⟨W, hWsub, hWopen, hxW⟩ := mem_nhds_iff.mp hbot
    obtain ⟨y, hyW, hy⟩ := hu x W hWopen hxW
    exact hy (hWsub hyW)
  exact ⟨N, g, hg, hgen x hxU, hF, hne, b, hb, hrep⟩

end SGPT.NAPotential.TraceComparison.NativeImage
