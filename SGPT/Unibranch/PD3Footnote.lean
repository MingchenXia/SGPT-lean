import SGPT.Unibranch.PD3GRexten2
import SGPT.Unibranch.HironakaG11BlowupLocality
import SGPT.Unibranch.FNASuspension

/-!
# Grauert--Remmert: the canonical open subspace, and the footnote counterexample

Source `thm:GRexten2` (Appendix B, `appendix_unibranch.tex`).

* `grauertRemmert_extension_bounded_openSubspace`: item (2) for the library's canonical open
  subspace `X \ Z` (`HironakaG11BlowupLocality.openSubspace`), whenever it is paracompact (the
  statements of `PD3GRexten2`/`PD3CodimTwo` hold for every realization `j : W → X` of the open
  subspace).
* The footnote of `thm:GRexten2`: "Unibranchness is very important here. Otherwise, consider the
  case where `X` is the union of two copies of `ℂ` intersecting only at their origins, `Z` is the
  common origin. If we set `φ ≡ 0` on one punctured plane and `φ ≡ 1` on the other, then it is
  clear that `φ` cannot be extended to `X`."  With `X = {z₀ z₁ = 0} ⊆ ℂ²` (`twoLines`), `Z` the
  origin and `φ = 1` on `{z₀ = 0}`, `0` elsewhere: `φ ∈ PSH(X \ Z)` (`twoLines_isPSH_off`), `Z` is
  analytic with empty interior and `φ` is bounded, but `φ` has no psh extension
  (`twoLines_not_exists_extension`: the extension would be `≥ 1` at the origin by upper
  semicontinuity along `{z₀ = 0}`, and `≤ 0` by the maximum principle along the disc `t ↦ (t, 0)`).
  Consequently `X` is not unibranch (`twoLines_not_isUnibranch`, from item (2)).

Lane PD3, blueprint `pd3.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.HironakaReducedComplexAnalyticSpaces
open SGPT.Foundations.Analysis.Pending.HironakaActualAnalyticSubspaceMaps

noncomputable section

namespace SGPT.Unibranch.PD3

open SourceReducedComplexSpace
open SGPT.PSH.VariableComplexAtlas (analyticExtension)

/-! ### The canonical open subspace -/

/-- **`thm:GRexten2` (2) for the canonical open subspace** `X \ Z` (when it is paracompact). -/
theorem grauertRemmert_extension_bounded_openSubspace {X : SourceReducedComplexSpace}
    (hX : X.IsUnibranch) {Z : Set X.obj.left} (hZ : X.IsAnalyticSubset Z)
    (hZi : interior Z = ∅)
    [ParacompactSpace (⟨Zᶜ, hZ.isClosed.isOpen_compl⟩ : Opens X.obj.left)]
    {φ : X.obj.left → EReal}
    (hφ : (HironakaG11BlowupLocality.openSubspace X ⟨Zᶜ, hZ.isClosed.isOpen_compl⟩).IsPSH
      (fun w => φ ((HironakaG11BlowupLocality.openSubspaceInclusion X
        ⟨Zᶜ, hZ.isClosed.isOpen_compl⟩).hom.left.base w)))
    (hb : ∀ x ∈ Z, ∃ Nb ∈ 𝓝 x, ∃ C : ℝ, ∀ y ∈ Nb, y ∉ Z → φ y ≤ C) :
    ∃! η : X.obj.left → EReal, X.IsPSH η ∧ EqOn η φ Zᶜ :=
  existsUnique_grauertRemmert_extension_bounded hX hZ hZi _ inferInstance
    (HironakaG11BlowupLocality.range_openSubspaceInclusion X _) hφ hb

/-! ### The footnote: two lines meeting at a point -/

/-- The ambient open set `ℂ²`. -/
abbrev twoLinesAmbient : Opens (ComplexModel 2) := ⊤

/-- The union of the two coordinate axes `{z₀ z₁ = 0}` in `ℂ²`. -/
def twoLinesCarrier : Set twoLinesAmbient := {w | w.val 0 * w.val 1 = 0}

theorem isComplexAnalyticSubset_twoLinesCarrier :
    IsComplexAnalyticSubset (n := 2) twoLinesCarrier := by
  have h : FNR.HasLocalEquationsOn {z : ComplexModel 2 | z 0 * z 1 = 0}
      (twoLinesAmbient : Set (ComplexModel 2)) := by
    intro x _
    refine ⟨univ, isOpen_univ, trivial, 1, fun _ z => z 0 * z 1, fun _ => ?_, fun y _ => ?_⟩
    · exact ((EuclideanSpace.proj (0 : Fin 2) : ComplexModel 2 →L[ℂ] ℂ).differentiable.mul
        (EuclideanSpace.proj (1 : Fin 2) : ComplexModel 2 →L[ℂ] ℂ).differentiable).differentiableOn
    · simp
  exact FNA.isComplexAnalyticSubset_of_hasLocalEquationsOn (Ω := twoLinesAmbient) h

/-- The complex space `X = {z₀ z₁ = 0} ⊆ ℂ²`: two copies of `ℂ` meeting only at their origins. -/
abbrev twoLines : SourceReducedComplexSpace :=
  sourceReducedComplexSpaceModel twoLinesAmbient twoLinesCarrier
    isComplexAnalyticSubset_twoLinesCarrier

/-- The coordinate point of `twoLines`. -/
def twoLinesPoint (z : ComplexModel 2) (hz : z 0 * z 1 = 0) : twoLines.obj.left :=
  (⟨⟨z, trivial⟩, hz⟩ : twoLinesCarrier)

/-- The common origin. -/
def twoLinesOrigin : twoLines.obj.left := twoLinesPoint 0 (by simp)

/-- The coordinates of a point of `twoLines`. -/
def twoLinesCoord (x : twoLines.obj.left) : ComplexModel 2 :=
  (x : twoLinesCarrier).val.val

theorem twoLinesCoord_mul (x : twoLines.obj.left) :
    twoLinesCoord x 0 * twoLinesCoord x 1 = 0 := (x : twoLinesCarrier).property

theorem continuous_twoLinesCoord : Continuous twoLinesCoord :=
  continuous_subtype_val.comp continuous_subtype_val

theorem twoLinesCoord_injective : Function.Injective twoLinesCoord := fun _ _ h =>
  Subtype.ext (Subtype.ext h)

theorem twoLinesCoord_point (z : ComplexModel 2) (hz : z 0 * z 1 = 0) :
    twoLinesCoord (twoLinesPoint z hz) = z := rfl

theorem eq_origin_iff (x : twoLines.obj.left) :
    x = twoLinesOrigin ↔ twoLinesCoord x = 0 :=
  ⟨fun h => h ▸ rfl, fun h => twoLinesCoord_injective h⟩

/-- `φ = 1` on the axis `{z₀ = 0}`, `0` on the other axis. -/
def twoLinesPhi (x : twoLines.obj.left) : EReal :=
  open Classical in
  if twoLinesCoord x 0 = 0 then ((1 : ℝ) : EReal) else ((0 : ℝ) : EReal)

/-- The punctured space `X \ {0}`, as an open subset. -/
def twoLinesPunctured : Opens twoLines.obj.left :=
  ⟨{twoLinesOrigin}ᶜ, by
    have : T2Space twoLines.obj.left := twoLines.property.1
    exact isOpen_compl_singleton⟩

instance : ParacompactSpace twoLinesPunctured := by
  change ParacompactSpace {x : twoLinesCarrier // x ∈ ({twoLinesOrigin}ᶜ : Set twoLinesCarrier)}
  infer_instance

/-- The open subspace `X \ Z`, `Z` the origin. -/
abbrev twoLinesOff : SourceReducedComplexSpace :=
  HironakaG11BlowupLocality.openSubspace twoLines twoLinesPunctured

/-- The inclusion `X \ Z → X`. -/
abbrev twoLinesIncl : twoLinesOff ⟶ twoLines :=
  HironakaG11BlowupLocality.openSubspaceInclusion twoLines twoLinesPunctured

theorem twoLinesIncl_range : range twoLinesIncl.hom.left.base = {twoLinesOrigin}ᶜ :=
  HironakaG11BlowupLocality.range_openSubspaceInclusion twoLines twoLinesPunctured

/-- A constant function is in `PSH(Ω)` on a nonempty domain. -/
theorem pshOn_const {N : ℕ} {Ω : Set (ComplexModel N)} (hΩ : Ω.Nonempty) (a : ℝ) :
    SGPT.PSH.PSHOn (fun _ => (a : EReal)) Ω :=
  ⟨SGPT.Foundations.Analysis.discPshOn_const (a : EReal) (EReal.coe_ne_top a) Ω,
    by obtain ⟨z, hz⟩ := hΩ; exact ⟨z, hz, EReal.coe_ne_bot a⟩⟩

/-- **Footnote of `thm:GRexten2`: `φ ∈ PSH(X \ Z)`.** -/
theorem twoLines_isPSH_off :
    twoLinesOff.IsPSH (fun w => twoLinesPhi (twoLinesIncl.hom.left.base w)) := by
  classical
  refine ⟨fun K hK => ?_, fun w => ?_⟩
  · obtain ⟨z, hz⟩ := hK.1.2.1
    refine ⟨z, hz, ?_⟩
    simp only [twoLinesPhi]
    split_ifs <;> exact EReal.coe_ne_bot _
  · set incl := twoLinesIncl.hom.left.base with hincl
    have hcont : Continuous (fun w' => twoLinesCoord (incl w')) :=
      continuous_twoLinesCoord.comp twoLinesIncl.hom.left.base.hom.continuous
    have hw0 : incl w ≠ twoLinesOrigin := by
      have h : incl w ∈ range incl := mem_range_self w
      rw [hincl, twoLinesIncl_range] at h
      exact h
    have hcw : twoLinesCoord (incl w) ≠ 0 := fun h => hw0 ((eq_origin_iff _).mpr h)
    by_cases h0 : twoLinesCoord (incl w) 0 = 0
    · -- on the axis `{z₀ = 0}`: `φ = 1` nearby
      have h1 : twoLinesCoord (incl w) 1 ≠ 0 := by
        intro h1
        apply hcw
        ext i
        fin_cases i
        · exact h0
        · exact h1
      set Nb : Set twoLinesOff.obj.left := {w' | twoLinesCoord (incl w') 1 ≠ 0}
      have hNb : IsOpen Nb := isOpen_ne.preimage
        ((continuous_apply 1).comp ((PiLp.continuous_ofLp 2 _).comp hcont))
      obtain ⟨e, ⟨c, hc⟩, hNe, hconn⟩ := LocalEmbedding.exists_domain (X := twoLinesOff) w hNb h1
      refine ⟨e, ⟨c, hc⟩, hconn, fun _ => ((1 : ℝ) : EReal),
        pshOn_const ⟨c.val.val, c.val.property⟩ 1, fun c' => ?_⟩
      have hN : e.toPoint c' ∈ Nb := hNe ⟨c', rfl⟩
      have hmul := twoLinesCoord_mul (incl (e.toPoint c'))
      have hz0 : twoLinesCoord (incl (e.toPoint c')) 0 = 0 :=
        (mul_eq_zero.mp hmul).resolve_right hN
      simp only [twoLinesPhi, hz0, if_true]
    · -- on the axis `{z₁ = 0}` minus the origin: `φ = 0` nearby
      set Nb : Set twoLinesOff.obj.left := {w' | twoLinesCoord (incl w') 0 ≠ 0}
      have hNb : IsOpen Nb := isOpen_ne.preimage
        ((continuous_apply 0).comp ((PiLp.continuous_ofLp 2 _).comp hcont))
      obtain ⟨e, ⟨c, hc⟩, hNe, hconn⟩ := LocalEmbedding.exists_domain (X := twoLinesOff) w hNb h0
      refine ⟨e, ⟨c, hc⟩, hconn, fun _ => ((0 : ℝ) : EReal),
        pshOn_const ⟨c.val.val, c.val.property⟩ 0, fun c' => ?_⟩
      have hN : e.toPoint c' ∈ Nb := hNe ⟨c', rfl⟩
      simp only [twoLinesPhi]
      rw [if_neg hN]

/-- A continuous coordinate curve in `twoLines`. -/
theorem continuous_twoLinesPoint {g : ℂ → ComplexModel 2} (hg : Continuous g)
    (hg0 : ∀ t, g t 0 * g t 1 = 0) : Continuous (fun t => twoLinesPoint (g t) (hg0 t)) := by
  change Continuous (fun t => (⟨⟨g t, trivial⟩, hg0 t⟩ : twoLinesCarrier))
  exact (hg.subtype_mk (fun _ => trivial)).subtype_mk _

/-- The two axes through the origin. -/
def axis (i : Fin 2) (t : ℂ) : twoLines.obj.left :=
  twoLinesPoint (t • EuclideanSpace.single i (1 : ℂ)) (by fin_cases i <;> simp)

theorem continuous_axis (i : Fin 2) : Continuous (axis i) :=
  continuous_twoLinesPoint (continuous_id.smul continuous_const) _

theorem axis_coord (i : Fin 2) (t : ℂ) : twoLinesCoord (axis i t) i = t := by
  simp [axis, twoLinesCoord_point]

theorem axis_zero (i : Fin 2) : axis i 0 = twoLinesOrigin :=
  (eq_origin_iff _).mpr (by simp [axis, twoLinesCoord_point])

theorem axis_ne_origin (i : Fin 2) {t : ℂ} (ht : t ≠ 0) : axis i t ≠ twoLinesOrigin := by
  intro h
  apply ht
  rw [← axis_coord i t, h]
  simp [twoLinesOrigin, twoLinesCoord_point]

/-- The origin is an analytic subset of `twoLines` with empty interior. -/
theorem twoLines_origin_analytic :
    twoLines.IsAnalyticSubset {twoLinesOrigin} ∧
      interior {twoLinesOrigin} = (∅ : Set twoLines.obj.left) := by
  refine ⟨isAnalyticSubset_singleton _ _, ?_⟩
  rw [eq_empty_iff_forall_notMem]
  intro x hx
  have hx0 : x = twoLinesOrigin := mem_singleton_iff.mp (interior_subset hx)
  subst hx0
  have hmem : ({twoLinesOrigin} : Set twoLines.obj.left) ∈ 𝓝 twoLinesOrigin :=
    mem_interior_iff_mem_nhds.mp hx
  have hpre : axis 0 ⁻¹' {twoLinesOrigin} ∈ 𝓝 (0 : ℂ) :=
    (continuous_axis 0).continuousAt.preimage_mem_nhds (by rw [axis_zero]; exact hmem)
  have hsub : axis 0 ⁻¹' {twoLinesOrigin} ⊆ {0} := by
    intro t ht
    by_contra ht0
    exact axis_ne_origin 0 ht0 ht
  have h0 : ({0} : Set ℂ) ∈ 𝓝 (0 : ℂ) := mem_of_superset hpre hsub
  have hemp : (∅ : Set ℂ) ∈ 𝓝[≠] (0 : ℂ) := by
    have := inter_mem_nhdsWithin ({0}ᶜ : Set ℂ) h0
    rwa [compl_inter_self] at this
  exact (NormedField.nhdsNE_neBot (0 : ℂ)).ne (empty_mem_iff_bot.mp hemp)

/-- The linear disc `t ↦ (t, 0)` in coordinates. -/
def axisMap : ComplexModel 1 →L[ℂ] ComplexModel 2 :=
  (EuclideanSpace.proj (0 : Fin 1) : ComplexModel 1 →L[ℂ] ℂ).smulRight
    (EuclideanSpace.single (0 : Fin 2) (1 : ℂ))

theorem axisMap_apply (z : ComplexModel 1) : axisMap z = EuclideanSpace.single 0 (z 0) := by
  ext i
  fin_cases i <;> simp [axisMap]

/-- **Footnote of `thm:GRexten2`: no psh extension.** The function `φ` (`1` on `{z₀ = 0}`, `0` on
`{z₁ = 0} \ {0}`) has no psh extension across the origin of `twoLines`. -/
theorem twoLines_not_exists_extension :
    ¬ ∃ η : twoLines.obj.left → EReal, twoLines.IsPSH η ∧
      EqOn η twoLinesPhi {twoLinesOrigin}ᶜ := by
  classical
  rintro ⟨η, hη, hηφ⟩
  -- upper semicontinuity along the axis `{z₀ = 0}` (where `φ = 1`)
  have hge : ((1 : ℝ) : EReal) ≤ η twoLinesOrigin := by
    by_contra hlt
    push Not at hlt
    have hev : ∀ᶠ x in 𝓝 twoLinesOrigin, η x < ((1 : ℝ) : EReal) :=
      hη.upperSemicontinuous twoLinesOrigin _ hlt
    have hev2 : ∀ᶠ t in 𝓝 (0 : ℂ), η (axis 1 t) < ((1 : ℝ) : EReal) :=
      (continuous_axis 1).continuousAt.eventually (by rw [axis_zero]; exact hev)
    have hev3 : ∀ᶠ t in 𝓝[≠] (0 : ℂ), η (axis 1 t) < ((1 : ℝ) : EReal) :=
      nhdsWithin_le_nhds hev2
    have := NormedField.nhdsNE_neBot (0 : ℂ)
    obtain ⟨t, ht, ht0⟩ := (hev3.and self_mem_nhdsWithin).exists
    rw [hηφ (axis_ne_origin 1 ht0)] at ht
    have hc : twoLinesCoord (axis 1 t) 0 = 0 := by simp [axis, twoLinesCoord_point]
    simp [twoLinesPhi, hc] at ht
  -- the maximum principle along the disc `t ↦ (t, 0)` (where `φ = 0` off the centre)
  have hle : η twoLinesOrigin ≤ 0 := by
    let g : unitDiscOpens → twoLinesAmbient := fun z => ⟨axisMap z, trivial⟩
    have hg : ContMDiff 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ComplexModel 2) ∞ g := by
      apply (ContMDiff.subtypeVal_comp_iff twoLinesAmbient g).mp
      exact axisMap.contDiff.contMDiff.comp contMDiff_subtype_val
    have hcar : ∀ c : unitDiscOpens, c ∈ (univ : Set unitDiscOpens) → g c ∈ twoLinesCarrier := by
      intro c _
      change (axisMap c.val) 0 * (axisMap c.val) 1 = 0
      simp [axisMap_apply]
    let F : unitDisc ⟶ twoLines :=
      ObjectProperty.homMk (Over.homMk
        (actualSubspaceMap hg (C := (univ : Set unitDiscOpens)) (D := twoLinesCarrier) hcar)
        (actualSubspaceMap_point hg _))
    have hF : ∀ t (ht : t ∈ ball (0 : ℂ) 1), discPullback F η t =
        η (twoLinesPoint (axisMap (discCoordinate t)) (by simp [axisMap_apply])) := by
      intro t ht
      have h := discCoordinate_mem_unitDiscOpens ht
      simp only [discPullback, modelPullback, dif_pos h]
      rfl
    have hD := discPshOn_modelPullback hη.2 F.hom.left (Over.w F.hom)
    have hL := hD.comp_affine discCoordinate 0
    rw [discCoordinate_preimage] at hL
    have heq : (fun t : ℂ => modelPullback F.hom.left η (0 + discCoordinate t)) =
        discPullback F η := by
      funext t
      simp [discPullback]
    rw [heq] at hL
    have h1 := PD.le_limsup_punctured hL
    have h0 : discPullback F η 0 = η twoLinesOrigin := by
      rw [hF 0 (mem_ball_self one_pos)]
      congr 1
      exact (eq_origin_iff _).mpr (by simp [twoLinesCoord_point])
    rw [h0] at h1
    refine h1.trans (limsup_le_of_le (by isBoundedDefault) ?_)
    have hball : ball (0 : ℂ) 1 ∈ 𝓝[≠] (0 : ℂ) :=
      nhdsWithin_le_nhds (isOpen_ball.mem_nhds (mem_ball_self one_pos))
    filter_upwards [hball, self_mem_nhdsWithin] with t ht ht0
    rw [hF t ht]
    have hc0 : twoLinesCoord (twoLinesPoint (axisMap (discCoordinate t))
        (by simp [axisMap_apply])) 0 = t := by
      simp [twoLinesCoord_point, axisMap_apply, discCoordinate]
    have hne : twoLinesPoint (axisMap (discCoordinate t)) (by simp [axisMap_apply]) ≠
        twoLinesOrigin := by
      intro h
      rw [h] at hc0
      apply ht0
      rw [← hc0]
      simp [twoLinesOrigin, twoLinesCoord_point]
    rw [hηφ hne]
    have ht0' : t ≠ 0 := ht0
    simp only [twoLinesPhi, hc0]
    rw [if_neg ht0']
    simp
  have := hge.trans hle
  rw [← EReal.coe_zero, EReal.coe_le_coe_iff] at this
  norm_num at this

/-- The two lines meeting at a point do not form a unibranch space: otherwise `thm:GRexten2` (2)
would extend `φ`. -/
theorem twoLines_not_isUnibranch : ¬ twoLines.IsUnibranch := by
  intro hX
  obtain ⟨hZa, hZi⟩ := twoLines_origin_analytic
  obtain ⟨η, ⟨hη, hηφ⟩, -⟩ := existsUnique_grauertRemmert_extension_bounded hX hZa hZi
    twoLinesIncl inferInstance twoLinesIncl_range twoLines_isPSH_off
    (fun x _ => ⟨univ, univ_mem, 1, fun y _ _ => by
      simp only [twoLinesPhi]
      split_ifs <;> norm_num⟩)
  exact twoLines_not_exists_extension ⟨η, hη, hηφ⟩

/-- **The footnote of `thm:GRexten2`** ("Unibranchness is very important here"). For `X` the union
of two copies of `ℂ` meeting only at their origins (`{z₀ z₁ = 0} ⊆ ℂ²`), `Z` the common origin and
`φ = 1` on one punctured line, `0` on the other: `Z` is analytic of codimension `≥ 1` (empty
interior), `φ ∈ PSH(X \ Z)` is bounded, yet `φ` cannot be extended to `PSH(X)`; and `X` is not
unibranch. -/
theorem grauertRemmert_footnote :
    twoLines.IsAnalyticSubset {twoLinesOrigin} ∧
      interior {twoLinesOrigin} = (∅ : Set twoLines.obj.left) ∧
      twoLinesOff.IsPSH (fun w => twoLinesPhi (twoLinesIncl.hom.left.base w)) ∧
      (∀ x, twoLinesPhi x ≤ ((1 : ℝ) : EReal)) ∧
      (¬ ∃ η : twoLines.obj.left → EReal, twoLines.IsPSH η ∧
        EqOn η twoLinesPhi {twoLinesOrigin}ᶜ) ∧
      ¬ twoLines.IsUnibranch :=
  ⟨twoLines_origin_analytic.1, twoLines_origin_analytic.2, twoLines_isPSH_off,
    fun x => by simp only [twoLinesPhi]; split_ifs <;> norm_num,
    twoLines_not_exists_extension, twoLines_not_isUnibranch⟩

end SGPT.Unibranch.PD3
