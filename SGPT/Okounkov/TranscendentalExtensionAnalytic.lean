import SGPT.Okounkov.TranscendentalExtensionLocal
import SGPT.Foundations.Analysis.Pending.RationalAnalyticMaximum
import SGPT.Foundations.Analysis.Pending.QuasiEquisingularRationalScaling
import SGPT.Foundations.Analysis.FirstPass.QuasiEquisingularApproximation

/-!
# Analytic singularities of the local extensions (DRWNXZ Theorem 6.1, last step)

Blueprint `tok:ct-extension` (package EXT). TN's local notion `HasAnalyticSingularityTypeAt`
(near the point, `u = c log ∑ |f_i|² + O(1)`, `c ∈ ℚ_{>0}`) is stable under

* changing `u` off a neighbourhood (`hasAnalyticSingularityTypeAt_congr`),
* adding a continuous real function (`hasAnalyticSingularityTypeAt_add_continuous`),
* holomorphic pullback (`hasAnalyticSingularityTypeAt_comp`),
* finite maxima, including the empty maximum `⊥ = log 0` (`hasAnalyticSingularityTypeAt_finset_sup`).

Consequently, if `φ` has analytic singularities on `Y`, then `φ ∘ π` has analytic singularity type
at every point of the domain of a flattening retraction `π`, in every chart of `X`
(`hasAnalyticSingularityTypeAt_chart_comp_retr`; FPT Step 6: "so does the holomorphic pullback
`φ ∘ π_j`").
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

universe u

open Set Filter
open scoped Topology Manifold ContDiff

namespace SGPT.Okounkov.TranscendentalExtension

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.RegularLocusDense
open SGPT.Foundations.Analysis.FirstPass.RegularPatchNeighborhood
open SGPT.Foundations.Analysis.FirstPass.QuasiEquisingularApproximation
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.SubmanifoldChartedSpace

section Local

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem hasAnalyticSingularityTypeAt_congr {u v : E → EReal} {x : E}
    (hu : HasAnalyticSingularityTypeAt u x) (huv : u =ᶠ[𝓝 x] v) :
    HasAnalyticSingularityTypeAt v x := by
  obtain ⟨c, N, f, hc, hf, b, hb, heq⟩ := hu
  exact ⟨c, N, f, hc, hf, b, hb, huv.symm.trans heq⟩

theorem hasAnalyticSingularityTypeAt_add_continuous {u : E → EReal} {h : E → ℝ} {x : E}
    (hu : HasAnalyticSingularityTypeAt u x) (hh : ContinuousAt h x) :
    HasAnalyticSingularityTypeAt (fun y => u y + (h y : EReal)) x := by
  obtain ⟨c, N, f, hc, hf, b, hb, heq⟩ := hu
  refine ⟨c, N, f, hc, hf, fun y => b y + h y, hb.add (boundedRealGermAt_of_continuousAt hh), ?_⟩
  filter_upwards [heq] with y hy
  rw [hy, EReal.coe_add, add_assoc]

theorem hasAnalyticSingularityTypeAt_comp {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E']
    {u : E → EReal} {F : E' → E} {U : Set E'} (hU : IsOpen U) (hF : DifferentiableOn ℂ F U)
    {x : E'} (hx : x ∈ U) (hu : HasAnalyticSingularityTypeAt u (F x)) :
    HasAnalyticSingularityTypeAt (fun y => u (F y)) x := by
  obtain ⟨c, N, f, hc, ⟨V, hV, hFxV, hfV⟩, b, ⟨C, hC, hbC⟩, heq⟩ := hu
  have hFc : ContinuousAt F x := (hF.continuousOn).continuousAt (hU.mem_nhds hx)
  refine ⟨c, N, fun j => f j ∘ F, hc, ⟨U ∩ F ⁻¹' V,
    hF.continuousOn.isOpen_inter_preimage hU hV, ⟨hx, hFxV⟩,
    fun j => (hfV j).comp (hF.mono inter_subset_left) fun y hy => hy.2⟩, b ∘ F,
    ⟨C, hC, hFc.eventually hbC⟩, ?_⟩
  filter_upwards [hFc.eventually heq] with y hy
  simpa only [Function.comp_apply, generatorLog, generatorVector] using hy

/-- `⊥ = log 0` has analytic singularity type (empty family of generators). -/
theorem hasAnalyticSingularityTypeAt_bot (x : E) :
    HasAnalyticSingularityTypeAt (fun _ : E => (⊥ : EReal)) x := by
  refine ⟨1, 0, fun j => Fin.elim0 j, by norm_num, ⟨univ, isOpen_univ, mem_univ x,
    fun j => Fin.elim0 j⟩, fun _ => 0, ⟨0, le_rfl, Eventually.of_forall fun _ => by simp⟩,
    Eventually.of_forall fun y => ?_⟩
  have hlog : generatorLog (fun j : Fin 0 => Fin.elim0 j : Fin 0 → E → ℂ) y = ⊥ := by
    rw [generatorLog_eq_log_sum]
    simp
  simp only [hlog, Rat.cast_one, EReal.coe_one, one_mul, EReal.coe_zero, add_zero]

theorem hasAnalyticSingularityTypeAt_finset_sup {ι : Type*} (J : Finset ι) {g : ι → E → EReal}
    {x : E} (hg : ∀ j ∈ J, HasAnalyticSingularityTypeAt (g j) x) :
    HasAnalyticSingularityTypeAt (fun y => J.sup fun j => g j y) x := by
  classical
  induction J using Finset.induction_on with
  | empty => simpa using hasAnalyticSingularityTypeAt_bot x
  | insert a J ha ih =>
      have h1 := hg a (Finset.mem_insert_self a J)
      have h2 := ih fun j hj => hg j (Finset.mem_insert_of_mem hj)
      simpa only [Finset.sup_insert] using
        RationalAnalyticMaximum.hasAnalyticSingularityTypeAt_max h1 h2

end Local

section Retraction

variable {n k : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {Y : Set X}

/-- **Analytic singularities pull back along the retraction.** If `φ` has analytic singularities
on `Y` (in the submanifold charts), then `φ ∘ π` has analytic singularity type at every point of
the domain of the retraction `π = retr G`, in every chart of `X`. -/
theorem hasAnalyticSingularityTypeAt_chart_comp_retr (hk : k ≤ n)
    (hY : ∀ x ∈ Y, RegularAtDim (n := n) Y x k) (G : FlatData n k X Y) {φ : Y → EReal}
    (hφ : letI := chartedSpace hk hY
      HasManifoldAnalyticSingularityType (n := k) φ)
    {x : X} (hx : x ∈ retrDomain G) (e : ComplexChart n X) (hxe : x ∈ e.val.source) :
    HasAnalyticSingularityTypeAt (chartFunction (fun z => φ (retr G z)) e) (e.val x) := by
  let _ := chartedSpace hk hY
  let eY : ComplexChart k Y := ⟨G.chart hk, chart_mem_atlas hk hY G⟩
  let T := chartTransition e G.amb
  let Fm : ComplexModel n → ComplexModel k := fun z => coordinateProjection n k (G.flat (T z))
  let U : Set (ComplexModel n) := T.source ∩ T ⁻¹' G.flat.source
  have hU : IsOpen U := T.continuousOn.isOpen_inter_preimage T.open_source G.flat.open_source
  have hFm : DifferentiableOn ℂ Fm U :=
    ((coordinateProjection n k).differentiable.comp_differentiableOn
      G.differentiableOn_flat).comp ((differentiableOn_chartTransition e G.amb).mono
        inter_subset_left) fun _ hz => hz.2
  have hTx : T (e.val x) = G.amb.val x := by
    show G.amb.val (e.val.symm (e.val x)) = G.amb.val x
    rw [e.val.left_inv hxe]
  have hxU : e.val x ∈ U := by
    refine ⟨⟨e.val.map_source hxe, ?_⟩, ?_⟩
    · show e.val.symm (e.val x) ∈ G.amb.val.source
      rw [e.val.left_inv hxe]; exact hx.1.1
    · show T (e.val x) ∈ G.flat.source
      rw [hTx]; exact hx.1.2
  have hFmx : Fm (e.val x) = flatProj G x := by
    show coordinateProjection n k (G.flat (T (e.val x))) = _
    rw [hTx]; rfl
  have hφζ : HasAnalyticSingularityTypeAt (chartFunction φ eY) (Fm (e.val x)) := by
    rw [hFmx]
    exact hφ eY _ hx.2
  have h := hasAnalyticSingularityTypeAt_comp hU hFm hxU hφζ
  refine hasAnalyticSingularityTypeAt_congr h (Eventually.of_forall fun z => ?_)
  rfl

end Retraction

end SGPT.Okounkov.TranscendentalExtension
