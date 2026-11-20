import SGPT.Checks.Comparison.TraceNativeFlatAnalyticType
import SGPT.Foundations.Analysis.Pending.SourceGenericSubmanifoldMinimum

/-! The SAME entire ideal normal order is the ORIGINAL normalized native
generic reader. Blueprint: `trace-native-prime-reader.tex`. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.NAPotential.TraceComparison.NativeImage

open Set Filter Metric
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.GlobalAnalyticSingularities
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open FixedGermNormalOrder DemaillyApproximantDivisorialLelong
open SourceTraceRepresentativeDefinition SquaredLogLelongSourceNormalization
open scoped Topology Manifold ContDiff ENNReal

/-- **The ORIGINAL source-normalized generic Lelong reader is the SAME
positive rational coefficient times the ENTIRE actual ideal normal order.**
Original quasi-PSH nondegeneracy, minimum point, local factors, all ideal
orders and factor-two normalization are produced internally. -/
theorem sourceGenericLelong_eq_originalNormalOrder_of_globalAnalyticType
    {m : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (ComplexModel (m+1)) M]
    [IsComplexManifold (m+1) M] {u : M → EReal}
    (hu : IsGlobalQuasiPshPotential (n := m+1) u) {c : ℚ} {A : GermIdeal (m+1) M}
    (htype : HasAnalyticSingularitiesOfType (n := m+1) u c A)
    {E : Set M} (hE : IsClosedConnectedSubmanifold (m+1) E m)
    {y : M} (hy : y ∈ E) (Φ : DivisorFlattening (m := m) E y) :
    sourceGenericLelongNumber (n := m+1) (Subtype.val : E → M) u =
      ENNReal.ofReal (c : ℝ) * (originalStalkNormalOrder Φ A : ℝ≥0∞) := by
  obtain ⟨a, ha⟩ := exists_originalNormalOrder_of_globalAnalyticType hu.2 htype hE
  obtain ⟨x, hxmin⟩ := SourceGenericSubmanifoldMinimum.exists_sourceGeneric_subtype_minimum hu.1 hE
  obtain ⟨Φx⟩ := DivisorFlattening.nonempty_of_regularAtDim (hE.2.2 x x.property)
  obtain ⟨N, g, hg, hgen, hF, hne, b, hb, hrep⟩ :=
    exists_actualFlatPresentation_of_globalAnalyticType hu.2 htype Φx
  let F : Fin N → ComplexModel (m+1) → ℂ := fun j z => g j (Φx.point z)
  obtain ⟨d, H, hH, hfactor, hfreq, hreader⟩ :=
    ActualFiniteFamilyPrimeMultiplicity.exists_generic_prime_reader F hF hne
  have horder := originalNormalOrder_eq_commonFactorization Φx A g hg hgen hF H hH hfactor hfreq
  have hda : d = a := by exact_mod_cast horder.symm.trans (ha x x.property Φx)
  subst d
  have hc : (0 : ℝ) < c := Rat.cast_pos.mpr htype.1
  obtain ⟨R, _O, hR, _hO, _hOR, _hOplane, _hlower, _hunit, hinf, _hhalf⟩ := hreader c hc b hb
  obtain ⟨δ, hδ, hδrep⟩ := Metric.eventually_nhds_iff_ball.mp hrep.eventuallyEq_nhds
  obtain ⟨ρ, hρ, hρlocal⟩ := FlattenedGlobalGenericLelongComparison.exists_radius_generic_le_local Φx u
  let r := min R (min δ ρ)
  have hr : 0 < r := lt_min hR (lt_min hδ hρ)
  have hrR : r ≤ R := min_le_left _ _
  have hrδ : r ≤ δ := (min_le_right _ _).trans (min_le_left _ _)
  have hrρ : r ≤ ρ := (min_le_right _ _).trans (min_le_right _ _)
  have hlocal : (⨅ z ∈ ball (0 : ComplexModel (m+1)) r ∩ {z | z (Fin.last m) = 0},
      lelongNumber (n := m+1) (fun w => u (Φx.point w)) z) =
        ENNReal.ofReal (2 * (c : ℝ) * (a : ℝ)) := by
    calc
      _ = ⨅ z ∈ ball (0 : ComplexModel (m+1)) r ∩ {z | z (Fin.last m) = 0},
          lelongNumber (n := m+1)
            (fun w => ((c : ℝ) : EReal) * generatorLog F w + (b w : EReal)) z := by
        refine iInf_congr fun z => iInf_congr fun hz => ?_
        exact LelongNumberComparison.lelongNumber_congr (hδrep z (ball_subset_ball hrδ hz.1))
      _ = _ := hinf r hr hrR
  have hrawgeneric : (⨅ z ∈ E, lelongNumber (n := m+1) u z) =
      2 * sourceGenericLelongNumber (n := m+1) (Subtype.val : E → M) u := by
    simpa only [iInf_subtype] using
      nativeGeneric_eq_two_mul_source (by omega : m+1 ≠ 0) (Subtype.val : E → M) u
  have hlow := hρlocal r hr hrρ
  rw [hrawgeneric, hlocal] at hlow
  have hzero : lelongNumber (n := m+1) (fun w => u (Φx.point w)) 0 =
      lelongNumber (n := m+1) u x := by
    simpa only [Φx.point_zero] using
      FlattenedGlobalGenericLelongComparison.lelongNumber_comp_point_eq Φx u Φx.zero_mem_target
  have hxraw : lelongNumber (n := m+1) u x =
      2 * sourceGenericLelongNumber (n := m+1) (Subtype.val : E → M) u := by
    rw [lelongNumber_eq_two_mul_squaredLog (by omega : m+1 ≠ 0), hxmin]
  have hupp : ENNReal.ofReal (2 * (c : ℝ) * (a : ℝ)) ≤
      2 * sourceGenericLelongNumber (n := m+1) (Subtype.val : E → M) u := by
    rw [← hlocal, ← hxraw, ← hzero]
    exact iInf₂_le_of_le (0 : ComplexModel (m+1))
      ⟨by simpa using hr, by simp⟩ le_rfl
  have hnorm : ENNReal.ofReal (2 * (c : ℝ) * (a : ℝ)) =
      2 * (ENNReal.ofReal (c : ℝ) * (a : ℝ≥0∞)) := by
    calc
      _ = ENNReal.ofReal (2 * ((c : ℝ) * (a : ℝ))) := congrArg ENNReal.ofReal (by ring)
      _ = ENNReal.ofReal 2 * ENNReal.ofReal ((c : ℝ) * (a : ℝ)) := ENNReal.ofReal_mul (by norm_num)
      _ = _ := by rw [ENNReal.ofReal_mul hc.le]; simp
  have hmul := (le_antisymm hlow hupp).trans hnorm
  rw [ha y hy Φ]
  simpa using
    (ENNReal.mul_right_inj (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)).mp hmul

end SGPT.NAPotential.TraceComparison.NativeImage
