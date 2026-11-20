import SGPT.Toric.ProjectiveLineNativePotential
import SGPT.Toric.ProjectiveLineLogSingularity
import SGPT.Foundations.Analysis.Pending.ProductComplexManifold
import SGPT.Foundations.Analysis.Pending.GlobalPotentialPullback
import SGPT.Foundations.Analysis.Pending.LocalPotentials
import SGPT.Foundations.Analysis.Pending.GlobalMultilinearExpansion
import SGPT.Foundations.Analysis.Pending.IEnvelopeStrongOpenness
import SGPT.Foundations.Analysis.Pending.NefBoundedMixedMass
import SGPT.Foundations.Analysis.Pending.RationalAnalyticMaximum
import SGPT.Foundations.Analysis.Pending.QuasiEquisingularRationalScaling
import SGPT.Foundations.Analysis.Pending.AnalyticTypeHolomorphicPullback
import SGPT.Foundations.Analysis.Pending.QuasiEquisingularComparison

/-!
# The global model `ℙ¹ × ℙ¹` for the local examples of the trace chapter

Source: `chapter_trace.tex`. The examples `ex:naive_res2` and `ex:trace:L407` are local
computations near the origin of `ℂ²` ("Both examples below are local, but can easily be
globalized since the singularities are isolated"). This file supplies a global compact
Kähler model containing the affine chart `ℂ² = ℂ × ℂ`: the product `X = ℙ¹ × ℙ¹` with the
product complex structure of `SGPT.Foundations.Analysis.Pending.ProductComplexManifold`
(modelled on `ℂ^{1+1}`) and the product Fubini–Study Kähler form
`ω = pr₁^* ω_FS + pr₂^* ω_FS`.

Main results:

* `SGPT.Trace.BertiniModel.omegaX`: the Kähler background `ω` on `ℙ¹ × ℙ¹`;
* `SGPT.Trace.BertiniModel.originChart`: the affine product chart `([1:z], [1:w]) ↦ (z, w)`;
* `SGPT.Trace.BertiniModel.isThetaPshPotential_comp_fst`, `…_comp_snd`: pullbacks of
  `ω_FS`-psh potentials along the projections are `ω`-psh;
* `SGPT.Trace.BertiniModel.isThetaPshPotential_smul_logSingularity`: `c · log(|Z₁|²/‖Z‖²)` is
  `ω_FS`-psh for `0 < c ≤ 1`;
* `SGPT.Trace.BertiniModel.hasManifoldAnalyticSingularityType_logSingularity`: the logarithmic
  potential `log(|Z₁|²/‖Z‖²)` of `ℙ¹` has analytic singularities.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology Manifold ContDiff

namespace SGPT.Trace.BertiniModel

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses
  SGPT.Foundations.Analysis.FirstPass.QuasiEquisingularApproximation
  SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.ProductComplexManifold
open SGPT.Toric

local notation "P1" => Projectivization ℂ (Fin 2 → ℂ)

/-! ### The product manifold and its Kähler background -/

/-- The product Fubini–Study Kähler background `pr₁^* ω_FS + pr₂^* ω_FS` on `ℙ¹ × ℙ¹`. -/
def omegaX : KahlerBackground (1 + 1) (P1 × P1) :=
  prodKahlerBackground projectiveNativeFSBackground projectiveNativeFSBackground

theorem omegaX_form : omegaX.form =
    ClosedRealOneOneForm.pullback contMDiff_fst projectiveNativeFSBackground.form +
      ClosedRealOneOneForm.pullback contMDiff_snd projectiveNativeFSBackground.form := rfl

/-- The affine product chart `([1:z], [1:w]) ↦ (z, w)` of `ℙ¹ × ℙ¹` (both finite charts). -/
def prodNativeChart (a b : Bool) : ComplexChart (1 + 1) (P1 × P1) :=
  ⟨prodChart (projectiveNativeChart a).val (projectiveNativeChart b).val,
    mem_image2_of_mem (projectiveNativeChart a).property (projectiveNativeChart b).property⟩

/-- The affine chart of `ℂ² ⊆ ℙ¹ × ℙ¹` centred at the origin. -/
abbrev originChart : ComplexChart (1 + 1) (P1 × P1) := prodNativeChart false false

/-- The origin `(0, 0)` of the affine chart. -/
def origin : P1 × P1 := (projectiveOrigin, projectiveOrigin)

/-- Every chart of the product atlas is one of the four product charts. -/
theorem exists_eq_prodNativeChart (e : ComplexChart (1 + 1) (P1 × P1)) :
    ∃ a b : Bool, e = prodNativeChart a b := by
  obtain ⟨_, ⟨f, hf, g, hg, rfl⟩⟩ := e
  obtain ⟨a, rfl⟩ := (mem_projectiveNativeAtlas_iff f).mp hf
  obtain ⟨b, rfl⟩ := (mem_projectiveNativeAtlas_iff g).mp hg
  exact ⟨a, b, rfl⟩

theorem prodNativeChart_target (a b : Bool) : (prodNativeChart a b).val.target = univ := by
  simp [prodNativeChart, projectiveNativeChart, projectiveModelChart,
    projectiveQuotientScalarChart_target]

theorem chartFunction_prodNativeChart (u : P1 × P1 → EReal) (a b : Bool)
    (z : ComplexModel (1 + 1)) :
    chartFunction u (prodNativeChart a b) z =
      u ((projectiveModelChart a).symm ((prodModelEquiv 1 1).symm z).1,
        (projectiveModelChart b).symm ((prodModelEquiv 1 1).symm z).2) := rfl

/-! ### Locally nondegenerate pullbacks -/

theorem locallyNondegenerate_comp_fst {u : P1 → EReal} (hu : LocallyNondegenerate u) :
    LocallyNondegenerate (fun x : P1 × P1 => u x.1) := by
  intro x U hU hxU
  obtain ⟨V, W, hV, hW, hxV, hxW, hVW⟩ := isOpen_prod_iff.mp hU x.1 x.2 hxU
  obtain ⟨y, hyV, hy⟩ := hu x.1 V hV hxV
  exact ⟨(y, x.2), hVW ⟨hyV, hxW⟩, hy⟩

theorem locallyNondegenerate_comp_snd {u : P1 → EReal} (hu : LocallyNondegenerate u) :
    LocallyNondegenerate (fun x : P1 × P1 => u x.2) := by
  intro x U hU hxU
  obtain ⟨V, W, hV, hW, hxV, hxW, hVW⟩ := isOpen_prod_iff.mp hU x.1 x.2 hxU
  obtain ⟨y, hyW, hy⟩ := hu x.2 W hW hxW
  exact ⟨(x.1, y), hVW ⟨hxV, hyW⟩, hy⟩

/-! ### Pulled-back potentials are `ω`-psh -/

private theorem semipositive_pullback_fst :
    (ClosedRealOneOneForm.pullback (contMDiff_fst (X := P1) (Y := P1) (n := 1) (m := 1))
      projectiveNativeFSBackground.form).val.IsSemipositive :=
  ClosedRealOneOneForm.pullback_isSemipositive _ projectiveNativeFSBackground.isSemipositive

private theorem semipositive_pullback_snd :
    (ClosedRealOneOneForm.pullback (contMDiff_snd (X := P1) (Y := P1) (n := 1) (m := 1))
      projectiveNativeFSBackground.form).val.IsSemipositive :=
  ClosedRealOneOneForm.pullback_isSemipositive _ projectiveNativeFSBackground.isSemipositive

/-- The pullback along the first projection of an `ω_FS`-psh potential is `ω`-psh. -/
theorem isThetaPshPotential_comp_fst {u : P1 → EReal}
    (hu : IsThetaPshPotential projectiveNativeFSBackground.form.val u) :
    IsThetaPshPotential omegaX.form.val (fun x : P1 × P1 => u x.1) := by
  have h := GlobalPotentialPullback.isThetaPshPotential_comp
    (contMDiff_fst (X := P1) (Y := P1) (n := 1) (m := 1)) hu.1
    (locallyNondegenerate_comp_fst hu.2)
  rw [omegaX_form]
  exact LocalPotentials.isThetaPshPotential_add_of_semipositive h semipositive_pullback_snd

/-- The pullback along the second projection of an `ω_FS`-psh potential is `ω`-psh. -/
theorem isThetaPshPotential_comp_snd {u : P1 → EReal}
    (hu : IsThetaPshPotential projectiveNativeFSBackground.form.val u) :
    IsThetaPshPotential omegaX.form.val (fun x : P1 × P1 => u x.2) := by
  have h := GlobalPotentialPullback.isThetaPshPotential_comp
    (contMDiff_snd (X := P1) (Y := P1) (n := 1) (m := 1)) hu.1
    (locallyNondegenerate_comp_snd hu.2)
  rw [omegaX_form, add_comm (ClosedRealOneOneForm.pullback contMDiff_fst _)]
  exact LocalPotentials.isThetaPshPotential_add_of_semipositive h semipositive_pullback_fst

/-! ### The logarithmic potential of `ℙ¹` -/

/-- The logarithmic potential `log(|Z₁|²/‖Z‖²)` is `ω_FS`-psh. -/
theorem isThetaPshPotential_logSingularity :
    IsThetaPshPotential projectiveNativeFSBackground.form.val projectiveLogSingularity :=
  isThetaPshPotential_projectiveNativeFS_of_source isThetaPSH_projectiveLogSingularity

/-- `c · log(|Z₁|²/‖Z‖²)` is `ω_FS`-psh for `0 < c ≤ 1`. -/
theorem isThetaPshPotential_smul_logSingularity {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) :
    IsThetaPshPotential projectiveNativeFSBackground.form.val
      (fun p => (c : EReal) * projectiveLogSingularity p) := by
  have hpsh := GlobalMultilinearExpansion.thetaPlurisubharmonic_smul hc0
    isThetaPshPotential_logSingularity.1
  have hsemi := NefBoundedMixedMass.isSemipositive_smul
    projectiveNativeFSBackground.isSemipositive (sub_nonneg.mpr hc1)
  have h := LocalPotentials.thetaPlurisubharmonic_add_of_semipositive hpsh hsemi
  have hform : c • projectiveNativeFSBackground.form + (1 - c) • projectiveNativeFSBackground.form =
      projectiveNativeFSBackground.form := by module
  rw [hform] at h
  refine ⟨h, ?_⟩
  intro x U hU hxU
  obtain ⟨y, hyU, hy⟩ := isThetaPshPotential_logSingularity.2 x U hU hxU
  refine ⟨y, hyU, ?_⟩
  have hytop := projectiveLogSingularity_ne_top y
  lift projectiveLogSingularity y to ℝ using ⟨hytop, hy⟩ with r
  rw [← EReal.coe_mul]
  exact EReal.coe_ne_bot _

/-- The chart expression of the logarithmic potential: in the finite chart it is
`log |z|² - log(1 + |z|²)`, in the chart at infinity it is `-log(1 + |w|²)`. -/
theorem chartFunction_logSingularity (b : Bool) (z : ComplexModel 1) :
    chartFunction projectiveLogSingularity (projectiveNativeChart b) z =
      (if b then 0 else logNormSq (z 0)) - (projectiveFSPotential z : EReal) := by
  have h := projectiveLogSingularity_corrected_chart b z
  change projectiveLogSingularity ((projectiveModelChart b).symm z) = _
  rw [← h, EReal.add_sub_cancel_right]

private theorem generatorLog_single (g : ComplexModel 1 → ℂ) (z : ComplexModel 1) :
    generatorLog (fun (_ : Fin 1) => g) z = logNormSq (g z) := by
  rw [generatorLog_eq_log_sum, Fin.sum_univ_one]
  rfl

/-- The logarithmic potential of `ℙ¹` has analytic singularity type in every chart. -/
theorem hasManifoldAnalyticSingularityType_logSingularity :
    HasManifoldAnalyticSingularityType (n := 1) projectiveLogSingularity := by
  intro e z _
  obtain ⟨b, hb⟩ := (mem_projectiveNativeAtlas_iff e.val).mp e.property
  have he : e = projectiveNativeChart b := Subtype.ext hb
  subst he
  have hcont : ContinuousAt (fun y : ComplexModel 1 => -projectiveFSPotential y) z :=
    contDiff_projectiveFSPotential.continuous.neg.continuousAt
  have key : ∀ g : ComplexModel 1 → ℂ, DifferentiableOn ℂ g univ →
      (∀ y, chartFunction projectiveLogSingularity (projectiveNativeChart b) y =
        logNormSq (g y) - (projectiveFSPotential y : EReal)) →
      HasAnalyticSingularityTypeAt
        (chartFunction projectiveLogSingularity (projectiveNativeChart b)) z := by
    intro g hg hval
    refine ⟨1, 1, fun _ => g, by norm_num, ⟨univ, isOpen_univ, mem_univ z, fun _ => hg⟩,
      fun y => -projectiveFSPotential y, boundedRealGermAt_of_continuousAt hcont,
      Eventually.of_forall fun y => ?_⟩
    change chartFunction projectiveLogSingularity (projectiveNativeChart b) y =
      ((1 : ℚ) : ℝ) * generatorLog (fun (_ : Fin 1) => g) y + ((-projectiveFSPotential y : ℝ) : EReal)
    rw [hval, generatorLog_single, sub_eq_add_neg, EReal.coe_neg]
    simp
  cases b
  · refine key (fun y => y 0)
      (by fun_prop : Differentiable ℂ fun y : ComplexModel 1 => y 0).differentiableOn ?_
    intro y
    rw [chartFunction_logSingularity]
    simp
  · refine key (fun _ => 1) (differentiableOn_const 1) ?_
    intro y
    rw [chartFunction_logSingularity]
    simp [logNormSq]

end SGPT.Trace.BertiniModel
