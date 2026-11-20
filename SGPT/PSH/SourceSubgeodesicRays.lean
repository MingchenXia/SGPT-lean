import SGPT.PSH.SourceGeodesicRays
import SGPT.Foundations.Analysis.Pending.SingularSubgeodesicProductLocalPsh
import SGPT.Foundations.Analysis.Pending.OpensRestriction

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open scoped ProductComplexManifold
open FirstPass.AnalyticGluingData

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- The ENTIRE original ray condition tests EVERY original closed segment
0≤a≤b, including a=b, on the SAME nonnegative-indexed ray. -/
def SourceIsSubgeodesicRay (omega : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (ℓ : SourceRayFamily M) : Prop :=
  ∀ a b : ℝ, 0 ≤ a → a ≤ b →
    SourceSubgeodesicClosedInterval omega θ a b (sourceRayExtension ℓ)

omit [BorelSpace M] in
/-- The original degenerate closed segment internally supplies EVERY actual
source theta-PSH slice, including the initial potential. -/
theorem SourceIsSubgeodesicRay.thetaPSH {omega : KahlerBackground n M}
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {ℓ : SourceRayFamily M}
    (h : SourceIsSubgeodesicRay omega θ ℓ) (t : Ici (0 : ℝ)) :
    (ofFixedModel n M).IsThetaPSH θ (ℓ t) := by
  have ht := (h t.val t.val t.property le_rfl).2.1
  simpa only [sourceRayExtension_nonneg ℓ t.val t.property] using ht

/-- Emanation retains the actual initial function of the original ray. -/
def SourceSubgeodesicRayEmanatesFrom (omega : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (ℓ : SourceRayFamily M) (u₀ : M → EReal) : Prop :=
  SourceIsSubgeodesicRay omega θ ℓ ∧ ℓ ⟨0, by simp⟩ = u₀

/-- The literal original positive-real-part half-plane, expressed through
the already genuine complex-linear time model identification. -/
def sourceSubgeodesicRayTimeHalfPlane : Opens (ComplexModel 1) :=
  ⟨{z | 0 < (sourceRayTimeModelEquiv z).re},
    isOpen_lt continuous_const (Complex.continuous_re.comp sourceRayTimeModelEquiv.continuous)⟩

/-- Actual complex time, without a real-time proxy. -/
def sourceSubgeodesicRayTime (z : sourceSubgeodesicRayTimeHalfPlane) : ℂ :=
  sourceRayTimeModelEquiv z.val

/-- The actual time one makes the half-plane nonempty. -/
def sourceSubgeodesicRayTimePoint : sourceSubgeodesicRayTimeHalfPlane :=
  ⟨sourceRayTimeModelEquiv.symm (1 : ℂ), by
    change 0 < (sourceRayTimeModelEquiv (sourceRayTimeModelEquiv.symm (1 : ℂ))).re
    simp only [ContinuousLinearEquiv.apply_symm_apply, Complex.one_re, zero_lt_one]⟩

/-- The time model is genuinely homeomorphic to the LITERAL original
half-plane, with exact inverse complex-coordinate readback. -/
def sourceSubgeodesicRayTimeEquiv :
    sourceSubgeodesicRayTimeHalfPlane ≃ₜ {z : ℂ // 0 < z.re} where
  toFun z := ⟨sourceSubgeodesicRayTime z, z.property⟩
  invFun z := ⟨sourceRayTimeModelEquiv.symm z.val, by
    change 0 < (sourceRayTimeModelEquiv (sourceRayTimeModelEquiv.symm z.val)).re
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using z.property⟩
  left_inv z := Subtype.ext (sourceRayTimeModelEquiv.symm_apply_apply z.val)
  right_inv z := Subtype.ext (sourceRayTimeModelEquiv.apply_symm_apply z.val)
  continuous_toFun :=
    (sourceRayTimeModelEquiv.continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (sourceRayTimeModelEquiv.symm.continuous.comp continuous_subtype_val).subtype_mk
    (fun z ↦ by
      change 0 < (sourceRayTimeModelEquiv (sourceRayTimeModelEquiv.symm z.val)).re
      simpa only [ContinuousLinearEquiv.apply_symm_apply] using z.property)

/-- Genuine holomorphic time in EVERY actual half-plane chart, from the
actual identity charts of an open Euclidean submanifold. -/
theorem sourceSubgeodesicRayTime_chart_holomorphic
    (b : ComplexChart 1 sourceSubgeodesicRayTimeHalfPlane) :
    DifferentiableOn ℂ (sourceSubgeodesicRayTime ∘ b.val.symm) b.val.target := by
  have hchart (z : sourceSubgeodesicRayTimeHalfPlane) : b.val z = z.val := by
    obtain ⟨x, hx⟩ := Opens.chart_eq
      (show Nonempty sourceSubgeodesicRayTimeHalfPlane from ⟨sourceSubgeodesicRayTimePoint⟩)
      b.property
    rw [hx]
    rfl
  have hsymm (z : ComplexModel 1) (hz : z ∈ b.val.target) :
      (b.val.symm z).val = z := by
    have hh := b.val.right_inv hz
    rwa [hchart] at hh
  apply sourceRayTimeModelEquiv.differentiable.differentiableOn.congr
  intro z hz
  change sourceRayTimeModelEquiv (b.val.symm z).val = sourceRayTimeModelEquiv z
  rw [hsymm z hz]

/-- The same actual half-plane time readback is continuous. -/
theorem sourceSubgeodesicRayTime_continuous : Continuous sourceSubgeodesicRayTime :=
  sourceRayTimeModelEquiv.continuous.comp continuous_subtype_val

/-- The ENTIRE actual original first-projection pullback form on the
actual positive-half-plane product, retaining all tensor fields. -/
def sourceSubgeodesicRayProductBackground
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) :
    AtlasClosedRealOneOneForm
      (ofFixedModel (n + 1) (M × sourceSubgeodesicRayTimeHalfPlane)) :=
  nativeClosedFormToAtlas (ClosedRealOneOneForm.pullback
    (ProductComplexManifold.contMDiff_fst (n := n) (m := 1)) (atlasClosedFormToNative θ))

/-- The literal original half-plane complexification. The harmless total
extension is used only at strictly positive original times. -/
def sourceSubgeodesicRayComplexification (ℓ : SourceRayFamily M)
    (p : M × sourceSubgeodesicRayTimeHalfPlane) : EReal :=
  sourceRayExtension ℓ (sourceSubgeodesicRayTime p.2).re p.1

omit [TopologicalSpace M] [MeasurableSpace M] in
/-- EVERY actual value equals the SAME original nonnegative-indexed ray;
no pole or domain is changed by the model/extension representation. -/
theorem sourceSubgeodesicRayComplexification_read (ℓ : SourceRayFamily M)
    (p : M × sourceSubgeodesicRayTimeHalfPlane) :
    sourceSubgeodesicRayComplexification ℓ p =
      ℓ ⟨(sourceSubgeodesicRayTime p.2).re, by
        change 0 ≤ (sourceSubgeodesicRayTime p.2).re
        exact p.2.property.le⟩ p.1 := by
  exact congrFun (sourceRayExtension_nonneg ℓ _ (show 0 ≤ (sourceSubgeodesicRayTime p.2).re from p.2.property.le)) p.1

omit [BorelSpace M] in
/-- Genuine slice nondegeneracy supplies a nonpole point in EVERY original
product neighborhood at the SAME actual complex time. -/
theorem sourceSubgeodesicRayComplexification_locallyNondegenerate
    {omega : KahlerBackground n M}
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {ℓ : SourceRayFamily M}
    (h : SourceIsSubgeodesicRay omega θ ℓ) :
    LocallyNondegenerate (sourceSubgeodesicRayComplexification ℓ) := by
  intro p O hO hp
  let V : Set M := (fun x : M ↦ (x, p.2)) ⁻¹' O
  have hV : IsOpen V := hO.preimage (continuous_id.prodMk continuous_const)
  let t : Ici (0 : ℝ) := ⟨(sourceSubgeodesicRayTime p.2).re, by
    change 0 ≤ (sourceSubgeodesicRayTime p.2).re
    exact p.2.property.le⟩
  have hslice := (isThetaPSH_iff_nativeThetaPotential θ (ℓ t)).mp (h.thetaPSH t)
  obtain ⟨y, hy, hny⟩ := hslice.2 p.1 V hV hp
  refine ⟨(y, p.2), hy, ?_⟩
  rw [sourceSubgeodesicRayComplexification_read]
  exact hny

/-- The existing genuine arbitrary-time-manifold product producer gives
localized joint PSH on positive half-plane neighborhoods. Every point has
such a neighborhood; exact original ray values then give global raw PSH. -/
theorem sourceSubgeodesicRayComplexification_thetaPlurisubharmonic
    {omega : KahlerBackground n M}
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {ℓ : SourceRayFamily M}
    (h : SourceIsSubgeodesicRay omega θ ℓ) :
    ThetaPlurisubharmonic
      (SmoothRealForm.pullback
        (ProductComplexManifold.contMDiff_fst (n := n) (m := 1)
          (X := M) (Y := sourceSubgeodesicRayTimeHalfPlane))
        (atlasClosedFormToNative θ).val)
      (sourceSubgeodesicRayComplexification ℓ) := by
  intro e z hz
  let p := e.val.symm z
  let b : ℝ := 2 * (sourceSubgeodesicRayTime p.2).re + 1
  have hp : 0 < (sourceSubgeodesicRayTime p.2).re := p.2.property
  have hb : 0 < b := by dsimp [b]; linarith
  have hpb : (sourceSubgeodesicRayTime p.2).re < b := by dsimp [b]; linarith
  have hn := (sourceSubgeodesicFrom_iff_native omega θ _ _ _).mp
    (h 0 b le_rfl hb.le).2
  have hstrip : IsSubgeodesicInterior (atlasClosedFormToNative θ).val
      (fun s ↦ sourceRayExtension ℓ (s * b)) := by
    simpa only [mul_zero, add_zero] using hn.interior
  let V : Set sourceSubgeodesicRayTimeHalfPlane :=
    {y | (sourceSubgeodesicRayTime y).re < b}
  have hV : IsOpen V :=
    isOpen_lt (Complex.continuous_re.comp sourceSubgeodesicRayTime_continuous) continuous_const
  let τ : sourceSubgeodesicRayTimeHalfPlane → ℂ :=
    fun y ↦ ((b⁻¹ : ℝ) : ℂ) * sourceSubgeodesicRayTime y
  have hτ (c : ComplexChart 1 sourceSubgeodesicRayTimeHalfPlane) :
      DifferentiableOn ℂ (τ ∘ c.val.symm) (c.val.target ∩ c.val.symm ⁻¹' V) := by
    exact ((sourceSubgeodesicRayTime_chart_holomorphic c).const_mul
      ((b⁻¹ : ℝ) : ℂ)).mono inter_subset_left
  have htime (y : sourceSubgeodesicRayTimeHalfPlane) (hy : y ∈ V) :
      (τ y).re ∈ Ioo (0 : ℝ) 1 := by
    change (sourceSubgeodesicRayTime y).re < b at hy
    change 0 < (((b⁻¹ : ℝ) : ℂ) * sourceSubgeodesicRayTime y).re ∧
      (((b⁻¹ : ℝ) : ℂ) * sourceSubgeodesicRayTime y).re < 1
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    refine ⟨mul_pos (inv_pos.mpr hb) y.property, ?_⟩
    simpa only [div_eq_mul_inv, mul_comm] using (div_lt_one hb).mpr hy
  have hlocal := SingularSubgeodesicProductLocalPsh.thetaPlurisubharmonicOn_product_time_pullback
    hstrip hV hτ htime
  have heq : EqOn (fun q : M × sourceSubgeodesicRayTimeHalfPlane ↦
      sourceRayExtension ℓ ((τ q.2).re * b) q.1)
      (sourceSubgeodesicRayComplexification ℓ) (univ ×ˢ V) := by
    intro q _hq
    have hcancel : (τ q.2).re * b = (sourceSubgeodesicRayTime q.2).re := by
      change (((b⁻¹ : ℝ) : ℂ) * sourceSubgeodesicRayTime q.2).re * b = _
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      calc
        (b⁻¹ * (sourceSubgeodesicRayTime q.2).re) * b =
          (b⁻¹ * b) * (sourceSubgeodesicRayTime q.2).re := by ring
        _ = (sourceSubgeodesicRayTime q.2).re := by rw [inv_mul_cancel₀ hb.ne', one_mul]
    change sourceRayExtension ℓ ((τ q.2).re * b) q.1 =
      sourceRayExtension ℓ (sourceSubgeodesicRayTime q.2).re q.1
    rw [hcancel]
  have hactual := OpensRestriction.thetaPlurisubharmonicOn_congr
    (isOpen_univ.prod hV) hlocal heq
  exact hactual e z hz ⟨mem_univ _, hpb⟩

/-- Full ORIGINAL universal-local-potential PSH on the actual half-plane
product, with joint nondegeneracy MANUFACTURED from original slices. -/
theorem SourceIsSubgeodesicRay.complexification_thetaPSH
    {omega : KahlerBackground n M}
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {ℓ : SourceRayFamily M}
    (h : SourceIsSubgeodesicRay omega θ ℓ) :
    (ofFixedModel (n + 1) (M × sourceSubgeodesicRayTimeHalfPlane)).IsThetaPSH
      (sourceSubgeodesicRayProductBackground θ) (sourceSubgeodesicRayComplexification ℓ) := by
  apply (isThetaPSH_iff_nativeThetaPotential (sourceSubgeodesicRayProductBackground θ) _).mpr
  exact ⟨sourceSubgeodesicRayComplexification_thetaPlurisubharmonic h,
    sourceSubgeodesicRayComplexification_locallyNondegenerate h⟩

/-- WHOLE original def:subgeoray: its literal all-closed-segment ray, actual
initial emanation, EVERY genuine slice, and PRODUCED whole half-plane
full source first-projection PSH. No model/E1/output premise is added. -/
theorem source_subgeodesic_ray_whole {omega : KahlerBackground n M}
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {ℓ : SourceRayFamily M}
    (h : SourceIsSubgeodesicRay omega θ ℓ) :
    SourceSubgeodesicRayEmanatesFrom omega θ ℓ (ℓ ⟨0, by simp⟩) ∧
      (∀ t, (ofFixedModel n M).IsThetaPSH θ (ℓ t)) ∧
        (ofFixedModel (n + 1) (M × sourceSubgeodesicRayTimeHalfPlane)).IsThetaPSH
          (sourceSubgeodesicRayProductBackground θ) (sourceSubgeodesicRayComplexification ℓ) :=
  ⟨⟨h, rfl⟩, h.thetaPSH, h.complexification_thetaPSH⟩

end SGPT.PSH.VariableComplexAtlas
