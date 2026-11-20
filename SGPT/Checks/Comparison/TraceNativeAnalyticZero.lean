import SGPT.Checks.Comparison.TraceNativeAnalyticNonzero
import SGPT.Checks.Comparison.TraceNativePrimeFamilyOrder

/-! The ENTIRE original ideal order of an identically minus-infinite original
analytic weight. Blueprint: `trace-native-rational-sup.tex`. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.NAPotential.TraceComparison.NativeImage

open Set Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.GlobalAnalyticSingularities
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open FixedGermNormalOrder DemaillyApproximantDivisorialLelong
open scoped Topology ENNReal

/-- The original entire ideal order is infinite when its SAME actual
positive rational analytic weight is identically minus infinity. All actual
generators and their zero germs are derived from the original type. -/
theorem originalNormalOrder_eq_top_of_globalAnalyticType_eq_bot
    {m : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (ComplexModel (m+1)) M]
    [IsComplexManifold (m+1) M] {u : M → EReal} {c : ℚ} {A : GermIdeal (m+1) M}
    (htype : HasAnalyticSingularitiesOfType (n := m+1) u c A) (hbot : ∀ x, u x = ⊥)
    {E : Set M} {x : M} (Φ : DivisorFlattening (m := m) E x) :
    originalStalkNormalOrder Φ A = ⊤ := by
  obtain ⟨hc, _hcoh, hlocal⟩ := htype
  obtain ⟨U, hU, hxU, N, g, hgd, hgen, R, C, _hRC, heq⟩ := hlocal x
  have hg (j : Fin N) : HolomorphicAt (m+1) (g j) x :=
    InvertibleIdealQuotient.holomorphicAt_of_mdifferentiableOn hU (hgd j) hxU
  have hzero (j : Fin N) (y : M) (hy : y ∈ U) : g j y = 0 :=
    ((scaled_generatorLog_add_eq_bot_iff g y (Rat.cast_pos.mpr hc) (R y)).mp
      ((heq y hy).symm.trans (hbot y))) j
  have hpointT : Tendsto Φ.point (𝓝 (0 : ComplexModel (m+1))) (𝓝 x) := by
    simpa only [Φ.point_zero] using (Φ.mdifferentiableAt_point Φ.zero_mem_target).continuousAt.tendsto
  rw [originalStalkNormalOrder_eq_generators Φ A g hg (hgen x hxU)]
  apply iInf_eq_top.mpr
  intro j
  rw [ActualFlatNormalOrder.functionNormalOrder_eq_flat]
  have hflat : ActualFlatNormalOrder.flatFunctionGerm Φ (g j) (hg j) = 0 := by
    apply Subtype.ext
    change ((fun z : ComplexModel (m+1) => g j (Φ.point z)) : Germ (𝓝 (0 : ComplexModel (m+1))) ℂ) =
      ((fun _ : ComplexModel (m+1) => (0 : ℂ)) : Germ (𝓝 (0 : ComplexModel (m+1))) ℂ)
    have hgz : ∀ᶠ y in 𝓝 x, g j y = 0 := by
      filter_upwards [hU.mem_nhds hxU] with y hy
      exact hzero j y hy
    exact Germ.coe_eq.mpr (hpointT.eventually hgz)
  rw [hflat, emultiplicity_zero]

end SGPT.NAPotential.TraceComparison.NativeImage
