import SGPT.Convex.PointwiseTopology
import Mathlib.Topology.Order.ExtendFrom
import Mathlib.Topology.CompactOpen

/-! Actual finite convex strip profiles extend to the closed strip, with their
literal finite endpoint values and +∞ off the strip. All continuity is produced
from the original pointwise endpoint limits, not supplied as a certificate. -/

set_option autoImplicit false
noncomputable section
namespace SGPT.Convex
open Set Filter Topology
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
private theorem convexOn_strip_slice {g : E × ℝ → ℝ}
    (hg : ConvexOn ℝ (univ ×ˢ Ioo (0 : ℝ) 1) g)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    ConvexOn ℝ univ (fun x => g (x, t)) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  have hh := hg.2 (x := (x, t)) (y := (y, t))
    ⟨mem_univ x, ht⟩ ⟨mem_univ y, ht⟩ ha hb hab
  have hp : a • (x, t) + b • (y, t) = (a • x + b • y, t) := by
    ext <;> simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
    rw [← add_mul, hab, one_mul]
  simpa only [hp] using hh

/-- The original interior slice curve in the actual pointwise space of finite
convex functions; its unused off-strip values are the first endpoint. -/
def finiteConvexStripCurve (g : E × ℝ → ℝ) (f₀ : E → ℝ)
    (hf₀ : ConvexOn ℝ univ f₀)
    (hg : ConvexOn ℝ (univ ×ˢ Ioo (0 : ℝ) 1) g) : ℝ → RealConvexFunction E :=
  fun t => if ht : t ∈ Ioo (0 : ℝ) 1 then
    ⟨fun x => g (x, t), convexOn_strip_slice hg ht⟩ else ⟨f₀, hf₀⟩

private theorem continuousOn_finiteConvexStripCurve (g : E × ℝ → ℝ) (f₀ : E → ℝ)
    (hf₀ : ConvexOn ℝ univ f₀)
    (hg : ConvexOn ℝ (univ ×ˢ Ioo (0 : ℝ) 1) g) :
    ContinuousOn (finiteConvexStripCurve g f₀ hf₀ hg) (Ioo (0 : ℝ) 1) := by
  have hc := hg.continuousOn (isOpen_univ.prod isOpen_Ioo)
  apply continuousOn_iff_continuous_domRestrict.mpr
  have hval : Continuous (fun t : Ioo (0 : ℝ) 1 => fun x : E => g (x, t.val)) := by
    apply continuous_pi
    intro x
    exact hc.comp_continuous (continuous_const.prodMk continuous_subtype_val)
      (fun t => ⟨mem_univ x, t.property⟩)
  convert hval.subtype_mk (fun t => convexOn_strip_slice hg t.property) using 1
  funext t
  apply Subtype.ext
  change (finiteConvexStripCurve g f₀ hf₀ hg t.val).val = fun x => g (x, t.val)
  simp only [finiteConvexStripCurve, dif_pos t.property]

omit [FiniteDimensional ℝ E] in
private theorem tendsto_finiteConvexStripCurve_left (g : E × ℝ → ℝ) (f₀ : E → ℝ)
    (hf₀ : ConvexOn ℝ univ f₀)
    (hg : ConvexOn ℝ (univ ×ˢ Ioo (0 : ℝ) 1) g)
    (h₀ : ∀ x, Tendsto (fun t => g (x, t)) (𝓝[>] 0) (𝓝 (f₀ x))) :
    Tendsto (finiteConvexStripCurve g f₀ hf₀ hg) (𝓝[>] 0) (𝓝 ⟨f₀, hf₀⟩) := by
  apply tendsto_subtype_rng.mpr
  apply tendsto_pi_nhds.mpr
  intro x
  apply (h₀ x).congr'
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
  simp only [finiteConvexStripCurve, dif_pos ht]

omit [FiniteDimensional ℝ E] in
private theorem tendsto_finiteConvexStripCurve_right (g : E × ℝ → ℝ) (f₀ f₁ : E → ℝ)
    (hf₀ : ConvexOn ℝ univ f₀) (hf₁ : ConvexOn ℝ univ f₁)
    (hg : ConvexOn ℝ (univ ×ˢ Ioo (0 : ℝ) 1) g)
    (h₁ : ∀ x, Tendsto (fun t => g (x, t)) (𝓝[<] 1) (𝓝 (f₁ x))) :
    Tendsto (finiteConvexStripCurve g f₀ hf₀ hg) (𝓝[<] 1) (𝓝 ⟨f₁, hf₁⟩) := by
  apply tendsto_subtype_rng.mpr
  apply tendsto_pi_nhds.mpr
  intro x
  apply (h₁ x).congr'
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with t ht
  simp only [finiteConvexStripCurve, dif_pos ht]

/-- Extend the actual convex-function-valued curve, retaining the spatial
convexity of every value. Endpoint readback is proved from the original limits. -/
def closedConvexStripCurve (g : E × ℝ → ℝ) (f₀ : E → ℝ)
    (hf₀ : ConvexOn ℝ univ f₀)
    (hg : ConvexOn ℝ (univ ×ˢ Ioo (0 : ℝ) 1) g) : ℝ → RealConvexFunction E :=
  extendFrom (Ioo (0 : ℝ) 1) (finiteConvexStripCurve g f₀ hf₀ hg)

def closedConvexStripProfile (g : E × ℝ → ℝ) (f₀ : E → ℝ)
    (hf₀ : ConvexOn ℝ univ f₀)
    (hg : ConvexOn ℝ (univ ×ˢ Ioo (0 : ℝ) 1) g) (p : E × ℝ) : ℝ :=
  (closedConvexStripCurve g f₀ hf₀ hg p.2).val p.1

theorem closedConvexStripProfile_interior (g : E × ℝ → ℝ) (f₀ : E → ℝ)
    (hf₀ : ConvexOn ℝ univ f₀)
    (hg : ConvexOn ℝ (univ ×ˢ Ioo (0 : ℝ) 1) g)
    {p : E × ℝ} (hp : p.2 ∈ Ioo (0 : ℝ) 1) :
    closedConvexStripProfile g f₀ hf₀ hg p = g p := by
  unfold closedConvexStripProfile closedConvexStripCurve
  rw [extendFrom_extends (continuousOn_finiteConvexStripCurve g f₀ hf₀ hg) p.2 hp]
  simp only [finiteConvexStripCurve, dif_pos hp]

omit [FiniteDimensional ℝ E] in
theorem closedConvexStripProfile_left (g : E × ℝ → ℝ) (f₀ : E → ℝ)
    (hf₀ : ConvexOn ℝ univ f₀)
    (hg : ConvexOn ℝ (univ ×ˢ Ioo (0 : ℝ) 1) g)
    (h₀ : ∀ x, Tendsto (fun t => g (x, t)) (𝓝[>] 0) (𝓝 (f₀ x))) (x : E) :
    closedConvexStripProfile g f₀ hf₀ hg (x, 0) = f₀ x := by
  unfold closedConvexStripProfile closedConvexStripCurve
  rw [eq_lim_at_left_extendFrom_Ioo (show (0 : ℝ) < 1 by norm_num)
    (tendsto_finiteConvexStripCurve_left g f₀ hf₀ hg h₀)]

omit [FiniteDimensional ℝ E] in
theorem closedConvexStripProfile_right (g : E × ℝ → ℝ) (f₀ f₁ : E → ℝ)
    (hf₀ : ConvexOn ℝ univ f₀) (hf₁ : ConvexOn ℝ univ f₁)
    (hg : ConvexOn ℝ (univ ×ˢ Ioo (0 : ℝ) 1) g)
    (h₁ : ∀ x, Tendsto (fun t => g (x, t)) (𝓝[<] 1) (𝓝 (f₁ x))) (x : E) :
    closedConvexStripProfile g f₀ hf₀ hg (x, 1) = f₁ x := by
  unfold closedConvexStripProfile closedConvexStripCurve
  rw [eq_lim_at_right_extendFrom_Ioo (show (0 : ℝ) < 1 by norm_num)
    (tendsto_finiteConvexStripCurve_right g f₀ f₁ hf₀ hf₁ hg h₁)]

/-- Genuine joint continuity at every boundary point follows from the actual
pointwise convex-function topology and its produced compact-open embedding. -/
theorem continuousOn_closedConvexStripProfile (g : E × ℝ → ℝ) (f₀ f₁ : E → ℝ)
    (hf₀ : ConvexOn ℝ univ f₀) (hf₁ : ConvexOn ℝ univ f₁)
    (hg : ConvexOn ℝ (univ ×ˢ Ioo (0 : ℝ) 1) g)
    (h₀ : ∀ x, Tendsto (fun t => g (x, t)) (𝓝[>] 0) (𝓝 (f₀ x)))
    (h₁ : ∀ x, Tendsto (fun t => g (x, t)) (𝓝[<] 1) (𝓝 (f₁ x))) :
    ContinuousOn (closedConvexStripProfile g f₀ hf₀ hg) (univ ×ˢ Icc (0 : ℝ) 1) := by
  have hc : ContinuousOn (closedConvexStripCurve g f₀ hf₀ hg) (Icc (0 : ℝ) 1) :=
    continuousOn_Icc_extendFrom_Ioo
      (continuousOn_finiteConvexStripCurve g f₀ hf₀ hg)
      (tendsto_finiteConvexStripCurve_left g f₀ hf₀ hg h₀)
      (tendsto_finiteConvexStripCurve_right g f₀ f₁ hf₀ hf₁ hg h₁)
  apply continuousOn_iff_continuous_domRestrict.mpr
  have ht : Continuous (fun p : (univ : Set E) ×ˢ Icc (0 : ℝ) 1 =>
      closedConvexStripCurve g f₀ hf₀ hg p.val.2) :=
    hc.comp_continuous (continuous_snd.comp continuous_subtype_val) (fun p => p.property.2)
  exact continuous_eval.comp
    ((continuous_realConvexToContinuousMap.comp ht).prodMk
      (continuous_fst.comp continuous_subtype_val))

private def contractStrip (ε : ℝ) (p : E × ℝ) : E × ℝ :=
  (p.1, ε + (1 - 2 * ε) * p.2)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
private theorem contractStrip_mem {ε : ℝ} (hε : ε ∈ Ioo (0 : ℝ) (1 / 2))
    {p : E × ℝ} (hp : p ∈ univ ×ˢ Icc (0 : ℝ) 1) :
    contractStrip ε p ∈ univ ×ˢ Ioo (0 : ℝ) 1 := by
  have hcoef : 0 ≤ 1 - 2 * ε := by linarith [hε.2]
  refine ⟨mem_univ _, ?_, ?_⟩
  · change 0 < ε + (1 - 2 * ε) * p.2
    nlinarith [hε.1, mul_nonneg hcoef hp.2.1]
  · change ε + (1 - 2 * ε) * p.2 < 1
    nlinarith [hε.1, mul_nonneg hcoef (sub_nonneg.mpr hp.2.2)]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
private theorem tendsto_contractStrip (p : E × ℝ) :
    Tendsto (fun ε => contractStrip ε p) (𝓝[>] 0) (𝓝 p) := by
  have hh : Continuous (fun ε => contractStrip ε p) := by unfold contractStrip; fun_prop
  simpa only [contractStrip, mul_zero, zero_mul, sub_zero, one_mul, zero_add, Prod.eta]
    using (hh.tendsto 0).mono_left nhdsWithin_le_nhds

/-- Joint convexity extends from the open strip using actual affine contractions
and the internally proved joint closed-strip continuity. -/
theorem convexOn_closedConvexStripProfile (g : E × ℝ → ℝ) (f₀ f₁ : E → ℝ)
    (hf₀ : ConvexOn ℝ univ f₀) (hf₁ : ConvexOn ℝ univ f₁)
    (hg : ConvexOn ℝ (univ ×ˢ Ioo (0 : ℝ) 1) g)
    (h₀ : ∀ x, Tendsto (fun t => g (x, t)) (𝓝[>] 0) (𝓝 (f₀ x)))
    (h₁ : ∀ x, Tendsto (fun t => g (x, t)) (𝓝[<] 1) (𝓝 (f₁ x))) :
    ConvexOn ℝ (univ ×ˢ Icc (0 : ℝ) 1) (closedConvexStripProfile g f₀ hf₀ hg) := by
  let P := closedConvexStripProfile g f₀ hf₀ hg
  have hc := continuousOn_closedConvexStripProfile g f₀ f₁ hf₀ hf₁ hg h₀ h₁
  have ht (p : E × ℝ) (hp : p ∈ univ ×ˢ Icc (0 : ℝ) 1) :
      Tendsto (fun ε => g (contractStrip ε p)) (𝓝[>] 0) (𝓝 (P p)) := by
    have hm : Tendsto (fun ε => contractStrip ε p) (𝓝[>] 0)
        (𝓝[univ ×ˢ Icc (0 : ℝ) 1] p) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
        (fun ε => contractStrip ε p) (tendsto_contractStrip p) (by
        filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with ε hε
        exact ⟨mem_univ _, (contractStrip_mem hε hp).2.1.le,
          (contractStrip_mem hε hp).2.2.le⟩)
    apply (Filter.Tendsto.comp (hc p hp) hm).congr'
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with ε hε
    exact closedConvexStripProfile_interior g f₀ hf₀ hg (contractStrip_mem hε hp).2
  refine ⟨convex_univ.prod (convex_Icc 0 1), ?_⟩
  intro p hp q hq a b ha hb hab
  have hz := (convex_univ.prod (convex_Icc 0 1)) hp hq ha hb hab
  apply le_of_tendsto_of_tendsto (ht (a • p + b • q) hz)
    (((ht p hp).const_smul a).add ((ht q hq).const_smul b))
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with ε hε
  have heq : contractStrip ε (a • p + b • q) =
      a • contractStrip ε p + b • contractStrip ε q := by
    ext
    · rfl
    · simp only [contractStrip, Prod.snd_add, Prod.smul_snd, smul_eq_mul]
      have ha' : a = 1 - b := by linarith
      rw [ha']
      ring
  rw [heq]
  exact hg.2 (contractStrip_mem hε hp) (contractStrip_mem hε hq) ha hb hab

/-- The literal +∞ extension of the produced closed-strip profile. -/
def closedStripExtension (g : E × ℝ → ℝ) (f₀ : E → ℝ)
    (hf₀ : ConvexOn ℝ univ f₀)
    (hg : ConvexOn ℝ (univ ×ˢ Ioo (0 : ℝ) 1) g) (p : E × ℝ) : EReal :=
  if p.2 ∈ Icc (0 : ℝ) 1 then (closedConvexStripProfile g f₀ hf₀ hg p : EReal) else ⊤

theorem closedStripExtension_interior (g : E × ℝ → ℝ) (f₀ : E → ℝ)
    (hf₀ : ConvexOn ℝ univ f₀)
    (hg : ConvexOn ℝ (univ ×ˢ Ioo (0 : ℝ) 1) g)
    {p : E × ℝ} (hp : p.2 ∈ Ioo (0 : ℝ) 1) :
    closedStripExtension g f₀ hf₀ hg p = (g p : EReal) := by
  simp only [closedStripExtension, if_pos (Ioo_subset_Icc_self hp),
    closedConvexStripProfile_interior g f₀ hf₀ hg hp]

omit [FiniteDimensional ℝ E] in
theorem closedStripExtension_effectiveDomain (g : E × ℝ → ℝ) (f₀ : E → ℝ)
    (hf₀ : ConvexOn ℝ univ f₀)
    (hg : ConvexOn ℝ (univ ×ˢ Ioo (0 : ℝ) 1) g) :
    effectiveDomain (closedStripExtension g f₀ hf₀ hg) = univ ×ˢ Icc (0 : ℝ) 1 := by
  ext p
  change (if p.2 ∈ Icc (0 : ℝ) 1 then
    (closedConvexStripProfile g f₀ hf₀ hg p : EReal) else ⊤) < ⊤ ↔ _
  by_cases hp : p.2 ∈ Icc (0 : ℝ) 1
  · rw [if_pos hp]
    exact iff_of_true (EReal.coe_lt_top _) ⟨mem_univ _, hp⟩
  · rw [if_neg hp]
    simp only [lt_self_iff_false, false_iff]
    exact fun h => hp h.2

theorem closedStripExtension_isProper_lowerSemicontinuous
    (g : E × ℝ → ℝ) (f₀ f₁ : E → ℝ)
    (hf₀ : ConvexOn ℝ univ f₀) (hf₁ : ConvexOn ℝ univ f₁)
    (hg : ConvexOn ℝ (univ ×ˢ Ioo (0 : ℝ) 1) g)
    (h₀ : ∀ x, Tendsto (fun t => g (x, t)) (𝓝[>] 0) (𝓝 (f₀ x)))
    (h₁ : ∀ x, Tendsto (fun t => g (x, t)) (𝓝[<] 1) (𝓝 (f₁ x))) :
    IsProper (closedStripExtension g f₀ hf₀ hg) ∧
      LowerSemicontinuous (closedStripExtension g f₀ hf₀ hg) := by
  let P := closedConvexStripProfile g f₀ hf₀ hg
  have hc := convexOn_closedConvexStripProfile g f₀ f₁ hf₀ hf₁ hg h₀ h₁
  have hcont := continuousOn_closedConvexStripProfile g f₀ f₁ hf₀ hf₁ hg h₀ h₁
  have hepi : epigraph (closedStripExtension g f₀ hf₀ hg) =
      {p : (E × ℝ) × ℝ | p.1 ∈ univ ×ˢ Icc (0 : ℝ) 1 ∧ P p.1 ≤ p.2} := by
    ext p
    change (if p.1.2 ∈ Icc (0 : ℝ) 1 then (P p.1 : EReal) else ⊤) ≤
      (p.2 : EReal) ↔ _
    by_cases hp : p.1.2 ∈ Icc (0 : ℝ) 1
    · rw [if_pos hp]
      simp only [mem_ofPred_eq, EReal.coe_le_coe_iff, mem_prod, mem_univ,
        true_and, hp]
    · rw [if_neg hp]
      have hnot : p.1 ∉ univ ×ˢ Icc (0 : ℝ) 1 := fun h => hp h.2
      simp only [mem_ofPred_eq, hnot, false_and, iff_false]
      exact not_le.mpr (EReal.coe_lt_top _)
  have hconv : IsConvex (closedStripExtension g f₀ hf₀ hg) := by
    rw [IsConvex, hepi]
    intro p hp q hq a b ha hb hab
    refine ⟨hc.1 hp.1 hq.1 ha hb hab, ?_⟩
    exact (hc.2 hp.1 hq.1 ha hb hab).trans
      (add_le_add (smul_le_smul_of_nonneg_left hp.2 ha)
        (smul_le_smul_of_nonneg_left hq.2 hb))
  refine ⟨⟨hconv, ?_, ?_⟩, ?_⟩
  · rw [closedStripExtension_effectiveDomain]
    exact ⟨(0, 0), mem_univ _, by norm_num⟩
  · intro p
    unfold closedStripExtension
    split <;> simp
  · apply isClosed_epigraph_iff_lowerSemicontinuous.mp
    rw [hepi]
    exact (isClosed_univ.prod isClosed_Icc).epigraph hcont

end SGPT.Convex
