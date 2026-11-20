import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Analysis.Convex.Topology

set_option autoImplicit false
noncomputable section
namespace SGPT.Convex
open Set Filter MeasureTheory
open scoped Topology Pointwise ENNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
/-- Actual compact Minkowski thickenings decrease to the original compact
set. The auxiliary body is genuine compact convex and contains the origin;
the original set may be empty or have any dimension. -/
theorem iInter_compact_add_pos_smul_eq
    {A B : Set E} (hA : IsCompact A) (hB : IsCompact B)
    (hB0 : (0 : E) ∈ B)
    {t : ℕ → ℝ} (ht : ∀ j, 0 < t j) (hlim : Tendsto t atTop (𝓝 0)) :
    (⋂ j, A + t j • B) = A := by
  obtain ⟨R,hR,hRB⟩ := hB.isBounded.exists_pos_norm_le
  ext x
  constructor
  · intro hx
    apply hA.isClosed.closure_eq ▸ (show x ∈ closure A from ?_)
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    have hev : ∀ᶠ j in atTop, t j < ε / R := hlim.eventually (gt_mem_nhds (div_pos hε hR))
    obtain ⟨j,hj⟩ := hev.exists
    obtain ⟨a,ha,b,hb,heq⟩ := mem_iInter.mp hx j
    obtain ⟨b,hb,rfl⟩ := hb
    refine ⟨a,ha,?_⟩
    rw [←heq, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos (ht j)]
    exact (mul_le_mul_of_nonneg_left (hRB b hb) (ht j).le).trans_lt ((lt_div_iff₀ hR).mp hj)
  · intro hx
    apply mem_iInter.mpr
    intro j
    exact ⟨x,hx,0,⟨0,hB0,smul_zero _⟩,add_zero x⟩

omit [MeasurableSpace E] [BorelSpace E] in
/-- Nonnegative parameter order produces actual inclusion of the genuine
convex-origin Minkowski thickenings. -/
theorem compact_add_pos_smul_antitone
    {A B : Set E} (hBc : Convex ℝ B) (hB0 : (0 : E) ∈ B)
    {t : ℕ → ℝ} (ht : ∀ j, 0 < t j) (hanti : Antitone t) :
    Antitone (fun j => A + t j • B) := by
  intro i j hij
  rintro x ⟨a,ha,b,hb,rfl⟩
  obtain ⟨b,hb,rfl⟩ := hb
  have hratio : t j / t i ∈ Icc (0 : ℝ) 1 :=
    ⟨(div_pos (ht j) (ht i)).le, (div_le_one (ht i)).mpr (hanti hij)⟩
  refine ⟨a,ha,t j • b,⟨(t j / t i) • b,hBc.smul_mem_of_zero_mem hB0 hb hratio,?_⟩,rfl⟩
  change t i • ((t j / t i) • b) = t j • b
  rw [smul_smul]
  congr 1
  field_simp [(ht i).ne']

/-- Actual finite-on-compacts measures are right-continuous on these genuine
Minkowski thickenings. In particular this applies to normalized lattice Haar
volume, including rank0 and lower-dimensional or empty original faces. -/
theorem tendsto_measure_compact_add_pos_smul
    (μ : Measure E) [IsFiniteMeasureOnCompacts μ]
    {A B : Set E} (hA : IsCompact A) (hB : IsCompact B)
    (hBc : Convex ℝ B) (hB0 : (0 : E) ∈ B)
    {t : ℕ → ℝ} (ht : ∀ j, 0 < t j) (hanti : Antitone t)
    (hlim : Tendsto t atTop (𝓝 0)) :
    Tendsto (fun j => μ (A + t j • B)) atTop (𝓝 (μ A)) := by
  have hcompact (j : ℕ) : IsCompact (A + t j • B) := hA.add (hB.smul (t j))
  have hmeasure := tendsto_measure_iInter_atTop
    (μ := μ) (fun j => (hcompact j).measurableSet.nullMeasurableSet)
    (compact_add_pos_smul_antitone hBc hB0 ht hanti)
    ⟨0,(hcompact 0).measure_ne_top⟩
  simpa only [Function.comp_def, iInter_compact_add_pos_smul_eq hA hB hB0 ht hlim] using hmeasure

end SGPT.Convex
