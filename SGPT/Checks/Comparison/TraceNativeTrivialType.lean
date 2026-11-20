import SGPT.Checks.Comparison.TraceNativeAnalyticNonzero
import SGPT.NAPotential.GAGAMultSiuGerms

/-! The SAME entire original analytic ideal is zero or nonzero from its
actual analytic weight. Blueprint: `trace-native-trivial.tex`. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.NAPotential.TraceComparison.NativeTrivial

open Set Filter
open SGPT.Okounkov SGPT.NAPotential.GAGAMult
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.GlobalAnalyticSingularities
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open scoped Topology

variable {k : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (ComplexModel k) M]
  [IsComplexManifold k M]

omit [IsComplexManifold k M] in
/-- An actual nonzero member of the coherent original ideal gives a
nonzero member in its actual entire native germ ideal. -/
theorem spanGerms_ne_bot_of_isNonzeroAt {A : GermIdeal k M}
    (hcoh : A.IsCoherent) {x : M} (hne : DivisorExponent.IsNonzeroAt A x) :
    spanGerms (n := k) (A.mem x) x ≠ ⊥ := by
  obtain ⟨g, hg, hgne⟩ := hne
  obtain ⟨U, _hU, hxU, N, s, _hs, hgen⟩ := hcoh x
  have hgd : HolomorphicAt k g x := ((hgen x hxU g).mp hg).1
  intro hbot
  have hmem := mk_mem_spanGerms hgd hg
  rw [hbot] at hmem
  have hzero : g =ᶠ[𝓝 x] 0 := by
    apply Germ.coe_eq.mp
    exact congrArg Subtype.val (show NativeHolGerm.mk g hgd = 0 from hmem)
  exact hgne (hzero.mono fun y hy => fun hn => hn hy)

/-- Original local nondegeneracy and SAME positive rational analytic type
produce a nonzero ENTIRE original native analytic germ ideal, in every dimension. -/
theorem spanGerms_ne_bot_of_globalAnalyticType
    {u : M → EReal} (hu : LocallyNondegenerate u) {c : ℚ} {A : GermIdeal k M}
    (htype : HasAnalyticSingularitiesOfType (n := k) u c A) (x : M) :
    spanGerms (n := k) (A.mem x) x ≠ ⊥ :=
  spanGerms_ne_bot_of_isNonzeroAt htype.2.1
    (NativeImage.isNonzeroAt_of_globalAnalyticType hu htype x)

omit [IsComplexManifold k M] in
/-- An identically minus-infinite original analytic weight forces the
ENTIRE same original analytic germ ideal to vanish, in every dimension. -/
theorem spanGerms_eq_bot_of_globalAnalyticType_eq_bot
    {u : M → EReal} {c : ℚ} {A : GermIdeal k M}
    (htype : HasAnalyticSingularitiesOfType (n := k) u c A) (hbot : ∀ x, u x = ⊥) (x : M) :
    spanGerms (n := k) (A.mem x) x = ⊥ := by
  obtain ⟨hc, _hcoh, hlocal⟩ := htype
  obtain ⟨U, hU, hxU, N, g, _hgd, hgen, R, C, _hRC, heq⟩ := hlocal x
  have hzero (j : Fin N) : g j =ᶠ[𝓝 x] 0 := by
    filter_upwards [hU.mem_nhds hxU] with y hy
    exact ((scaled_generatorLog_add_eq_bot_iff g y (Rat.cast_pos.mpr hc) (R y)).mp
      ((heq y hy).symm.trans (hbot y))) j
  apply Ideal.span_eq_bot.mpr
  rintro _ ⟨v, hv, hAv, rfl⟩
  obtain ⟨_hvd, K, s, a, hs, _ha, hvs⟩ := (hgen x hxU v).mp hAv
  have hs0 (j : Fin K) : s j =ᶠ[𝓝 x] 0 := by
    obtain ⟨i, hi⟩ := hs j
    rw [← hi]
    exact hzero i
  have hv0 : v =ᶠ[𝓝 x] 0 := by
    filter_upwards [hvs, eventually_all.mpr hs0] with y hy hsy
    simpa only [hsy, Pi.zero_apply, mul_zero, Finset.sum_const_zero] using hy
  apply Subtype.ext
  exact Germ.coe_eq.mpr hv0

end SGPT.NAPotential.TraceComparison.NativeTrivial
