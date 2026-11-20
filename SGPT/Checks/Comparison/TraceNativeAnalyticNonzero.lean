import SGPT.Foundations.Analysis.Pending.IdealPowerNormalOrder

/-! Genuine original global analytic type manufactures nonzero whole ideal
germs and actual prime-order constancy. Blueprint: `trace-native-prime-reader.tex`. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.NAPotential.TraceComparison.NativeImage

open Set Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.GlobalAnalyticSingularities
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open FixedGermNormalOrder DemaillyApproximantDivisorialLelong
open scoped Topology ENNReal

/-- The ACTUAL original local nondegeneracy and global analytic type produce
a genuine nonzero germ in the SAME entire ideal at EVERY original point. -/
theorem isNonzeroAt_of_globalAnalyticType {n : ℕ} {M : Type}
    [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    {u : M → EReal} (hu : LocallyNondegenerate u) {c : ℚ} {A : GermIdeal n M}
    (htype : HasAnalyticSingularitiesOfType (n := n) u c A) (x : M) :
    DivisorExponent.IsNonzeroAt A x := by
  obtain ⟨hc, _hcoh, hlocal⟩ := htype
  obtain ⟨U, hU, hxU, N, g, hg, hgen, R, C, _hRC, heq⟩ := hlocal x
  have hnon : ∃ j, ∃ᶠ y in 𝓝 x, g j y ≠ 0 := by
    by_contra h
    have hzero (j : Fin N) : ∀ᶠ y in 𝓝 x, g j y = 0 := by
      have hn : ¬ ∃ᶠ y in 𝓝 x, g j y ≠ 0 := fun hj => h ⟨j, hj⟩
      simpa only [not_not] using Filter.not_frequently.mp hn
    have hbot : ∀ᶠ y in 𝓝 x, u y = ⊥ := by
      filter_upwards [hU.mem_nhds hxU, eventually_all.mpr hzero] with y hy hgy
      rw [heq y hy]
      have hsum : ∑ j, ‖g j y‖ ^ 2 = 0 := by simp only [hgy, norm_zero, ne_eq,
        OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero]
      rw [generatorLog_eq_bot_of_normSq_eq_zero' g hsum,
        EReal.coe_mul_bot_of_pos (Rat.cast_pos.mpr hc), EReal.bot_add]
    obtain ⟨W, hWsub, hWopen, hxW⟩ := mem_nhds_iff.mp hbot
    obtain ⟨y, hyW, hy⟩ := hu x W hWopen hxW
    exact hy (hWsub hyW)
  obtain ⟨j, hj⟩ := hnon
  refine ⟨g j, (hgen x hxU (g j)).mpr ?_, hj⟩
  exact InvertibleIdealQuotient.isInSpanAt_self ⟨j, rfl⟩
    (InvertibleIdealQuotient.holomorphicAt_of_mdifferentiableOn hU (hg j) hxU)

/-- The SAME original analytic type and nondegenerate potential internally
produce one finite genuine ideal order on the SAME connected native prime. -/
theorem exists_originalNormalOrder_of_globalAnalyticType
    {m : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (ComplexModel (m+1)) M]
    [IsComplexManifold (m+1) M] {u : M → EReal} (hu : LocallyNondegenerate u)
    {c : ℚ} {A : GermIdeal (m+1) M}
    (htype : HasAnalyticSingularitiesOfType (n := m+1) u c A)
    {E : Set M} (hE : IsClosedConnectedSubmanifold (m+1) E m) :
    ∃ a : ℕ, ∀ y ∈ E, ∀ Φ : DivisorFlattening (m := m) E y,
      originalStalkNormalOrder Φ A = (a : ℕ∞) :=
  IdealPowerNormalOrder.exists_originalStalkNormalOrder_on_connected_hypersurface
    hE A htype.2.1 (isNonzeroAt_of_globalAnalyticType hu htype)

end SGPT.NAPotential.TraceComparison.NativeImage
