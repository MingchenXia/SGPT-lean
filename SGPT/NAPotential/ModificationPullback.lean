import SGPT.NAPotential.DHGeneral
import SGPT.PSH.SourceModificationOrders
import SGPT.PSH.SourceNASumAlgebra
import SGPT.Foundations.Analysis.Pending.KahlerDomination

/-!
# Genuine forward map for the whole original NA modification corollary

Actual all-dimensional forward pullback, with original inverse-system
compatibility, intrinsic order reflection and positive-curve naturality.

Source: `69360cfd`, `author/chapter_NApotential.tex:262–267`,
`cor:PSHNAbimero`. This draft constructs the actual forward inverse system,
its intrinsic order reflection and injectivity. The genuine semipositive
positive-volume reader and full inverse are supplied by SemipositiveVolume
and ModificationEquiv.

There is no supplied compatibility, descent, positivity certificate, or
bimeromorphic conclusion. The only hypotheses are the original geometric
ones. In particular a pulled-back Kähler form is never asserted to be Kähler.
-/

set_option autoImplicit false
noncomputable section
universe u

namespace SGPT.PSH.VariableComplexAtlas.WholeClosureNA

open Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
open scoped Topology Manifold ContDiff

variable {n : ℕ} {X Y : Type u}
  [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] [ConnectedSpace Y]
  {θ σ : AtlasClosedRealOneOneForm (ofFixedModel n X)} {π : Y → X}

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X]
  [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] [ConnectedSpace Y] in
/-- Total-coefficient additivity of the existing actual native pullback. -/
private theorem nativePullback_add
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ π)
    (a b : ClosedRealOneOneForm n X) :
    ClosedRealOneOneForm.pullback hf (a + b) =
      ClosedRealOneOneForm.pullback hf a + ClosedRealOneOneForm.pullback hf b := by
  apply ClosedRealOneOneForm.ext
  intro e z
  ext v
  rfl

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X]
  [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] [ConnectedSpace Y] in
/-- Total-coefficient linearity; no quotient representative is substituted. -/
private theorem nativePullback_smul
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ π)
    (c : ℝ) (a : ClosedRealOneOneForm n X) :
    ClosedRealOneOneForm.pullback hf (c • a) =
      c • ClosedRealOneOneForm.pullback hf a := by
  apply ClosedRealOneOneForm.ext
  intro e z
  ext v
  rfl

omit [MeasurableSpace Y] [BorelSpace Y] [ConnectedSpace Y] in
/-- Compact domination supplies an arbitrarily small multiple of a given
smooth background below an actual Kähler form. It includes dimension zero. -/
theorem exists_small_semipositive_difference (omegaY : KahlerBackground n Y)
    (β : ClosedRealOneOneForm n Y) :
    ∃ c : ℝ, 0 < c ∧ (omegaY.form - c • β).val.IsSemipositive := by
  obtain ⟨A, hA, h⟩ :=
    KahlerDomination.exists_pos_isSemipositive_add_smul omegaY (-β)
  have hc : 0 < A⁻¹ := inv_pos.mpr hA
  have hh := KahlerDomination.isSemipositive_smul h hc.le
  have heq : A⁻¹ • (-β + A • omegaY.form) = omegaY.form - A⁻¹ • β := by
    rw [smul_add, smul_neg, smul_smul, inv_mul_cancel₀ hA.ne', one_smul]
    abel
  rw [heq] at hh
  exact ⟨A⁻¹, hc, hh⟩

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X]
  [MeasurableSpace Y] [BorelSpace Y] [ConnectedSpace Y] in
/-- For EVERY upstairs Kähler index there is a genuine downstairs Kähler
index whose pullback is dominated there. No pullback-Kähler assumption. -/
theorem exists_downstairs_kahler_reader
    (omegaX : KahlerBackground n X) (omegaY : KahlerBackground n Y)
    (hπ : IsAnalyticModification (n := n) π) :
    ∃ c : ℝ, ∃ hc : 0 < c,
      (omegaY.form - ClosedRealOneOneForm.pullback hπ.1
        (KahlerBackground.smul hc omegaX).form).val.IsSemipositive := by
  obtain ⟨c, hc, h⟩ := exists_small_semipositive_difference omegaY
    (ClosedRealOneOneForm.pullback hπ.1 omegaX.form)
  refine ⟨c, hc, ?_⟩
  simpa only [KahlerBackground.smul_form, nativePullback_smul] using h

/-- The selected background is actual Kähler data, not an assumed target
reader, compatibility family or descent certificate. -/
private def downstairsReader
    (omegaX : KahlerBackground n X) (omegaY : KahlerBackground n Y)
    (hπ : IsAnalyticModification (n := n) π) : KahlerBackground n X :=
  KahlerBackground.smul
    (exists_downstairs_kahler_reader omegaX omegaY hπ).choose_spec.choose
    omegaX

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X]
  [MeasurableSpace Y] [BorelSpace Y] [ConnectedSpace Y] in
private theorem downstairsReader_dominated
    (omegaX : KahlerBackground n X) (omegaY : KahlerBackground n Y)
    (hπ : IsAnalyticModification (n := n) π) :
    (omegaY.form - ClosedRealOneOneForm.pullback hπ.1
      (downstairsReader omegaX omegaY hπ).form).val.IsSemipositive :=
  (exists_downstairs_kahler_reader omegaX omegaY hπ).choose_spec.choose_spec

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X]
  [MeasurableSpace Y] [BorelSpace Y] [ConnectedSpace Y] in
/-- The SAME geometric estimate supplies the entire actual transition
background, including the arbitrary original pseudo-effective base. -/
private theorem componentGap
    (omegaX : KahlerBackground n X) (hπ : IsAnalyticModification (n := n) π)
    (κ : SourceKahlerForm n Y) :
    (atlasClosedFormToNative (sourceNAComponentBackground
        (θ.nativeHolomorphicPullback hπ.1) κ) -
      atlasClosedFormToNative ((sourceTestCurveEnlargedBackground
        (downstairsReader omegaX (sourceKahlerFormRepresentative κ) hπ) θ).nativeHolomorphicPullback hπ.1)).val.IsSemipositive := by
  simp only [sourceNAComponentBackground_native,
    AtlasClosedRealOneOneForm.nativeHolomorphicPullback,
    sourceNativeAtlasForm_roundTrip, sourceTestCurveEnlargedBackground_native,
    nativePullback_add]
  convert downstairsReader_dominated omegaX (sourceKahlerFormRepresentative κ) hπ using 1
  congr 1
  abel

omit [ConnectedSpace Y] in
/-- Genuine intrinsic curve order, with actual existential global-P witnesses,
is preserved and reflected by modification pullback in every dimension. -/
theorem curvePOrder_modificationPullback_iff
    (omegaX : KahlerBackground n X) (omegaY : KahlerBackground n Y)
    (hπ : IsAnalyticModification (n := n) π)
    (G : SourceTestCurve θ) (H : SourceTestCurve σ) :
    SourceTestCurvePOrder G H ↔
      SourceTestCurvePOrder (G.modificationPullback hπ) (H.modificationPullback hπ) := by
  constructor
  · intro h
    refine ⟨h.cutoff_le, ?_⟩
    intro r hr
    exact (SGPT.PSH.ModificationOrders.sourcePOrder_modification_pullback_iff
      omegaX omegaY hπ ⟨θ, G.thetaPSH ⟨r, hr⟩⟩
      ⟨σ, H.thetaPSH ⟨r, hr.trans_le h.cutoff_le⟩⟩).mp (h.slice_le r hr)
  · intro h
    refine ⟨h.cutoff_le, ?_⟩
    intro r hr
    exact (SGPT.PSH.ModificationOrders.sourcePOrder_modification_pullback_iff
      omegaX omegaY hπ ⟨θ, G.thetaPSH ⟨r, hr⟩⟩
      ⟨σ, H.thetaPSH ⟨r, hr.trans_le h.cutoff_le⟩⟩).mpr (h.slice_le r hr)

/-- The actual positive I-model output at an arbitrary geometric upstairs
Kähler index: read downstairs, pull back, then take the genuine transition. -/
def sourceNAPullbackComponent (omegaX : KahlerBackground n X)
    (hπ : IsAnalyticModification (n := n) π)
    (Γ : SourceNAPotential θ) (κ : SourceKahlerForm n Y) :
    SourcePositiveIModelTestCurve
      (sourceNAComponentBackground (θ.nativeHolomorphicPullback hπ.1) κ) :=
  sourceIModelTestCurveTransition (sourceKahlerFormRepresentative κ)
    (componentGap (θ := θ) omegaX hπ κ)
    (SGPT.NAPotential.DH.positiveCurveModificationPullback hπ
      (sourceKahlerFormRepresentative κ)
      (Γ.realizedComponent (downstairsReader omegaX (sourceKahlerFormRepresentative κ) hπ)))

/-- This output has exactly the pulled-back type of its actual downstairs
reader. The compatibility proof below therefore needs no supplied family law. -/
private theorem component_POrder_reader
    (omegaX : KahlerBackground n X) (hπ : IsAnalyticModification (n := n) π)
    (Γ : SourceNAPotential θ) (κ : SourceKahlerForm n Y) :
    SourceTestCurvePOrder
      ((Γ.realizedComponent (downstairsReader omegaX (sourceKahlerFormRepresentative κ) hπ)).val.modificationPullback hπ) (sourceNAPullbackComponent omegaX hπ Γ κ).val ∧
    SourceTestCurvePOrder (sourceNAPullbackComponent omegaX hπ Γ κ).val
      ((Γ.realizedComponent (downstairsReader omegaX (sourceKahlerFormRepresentative κ) hπ)).val.modificationPullback hπ) :=
  sourceIModelTestCurveTransition_POrder_equivalent (sourceKahlerFormRepresentative κ)
    (componentGap (θ := θ) omegaX hπ κ)
    (SGPT.NAPotential.DH.positiveCurveModificationPullback hπ
      (sourceKahlerFormRepresentative κ)
      (Γ.realizedComponent (downstairsReader omegaX (sourceKahlerFormRepresentative κ) hπ)))

/-- The independently chosen downstairs readers give the same original
intrinsic type. This is the analytic reason all upstairs components agree. -/
theorem sourceNAPullbackComponent_POrder_equivalent
    (omegaX : KahlerBackground n X) (hπ : IsAnalyticModification (n := n) π)
    (Γ : SourceNAPotential θ) (κ ζ : SourceKahlerForm n Y) :
    SourceTestCurvePOrder (sourceNAPullbackComponent omegaX hπ Γ κ).val
      (sourceNAPullbackComponent omegaX hπ Γ ζ).val ∧
    SourceTestCurvePOrder (sourceNAPullbackComponent omegaX hπ Γ ζ).val
      (sourceNAPullbackComponent omegaX hπ Γ κ).val := by
  let omegaY := sourceKahlerFormRepresentative ζ
  have hr := Γ.realizedComponent_POrder_equivalent
    (downstairsReader omegaX (sourceKahlerFormRepresentative κ) hπ)
    (downstairsReader omegaX omegaY hπ)
  have hk := component_POrder_reader omegaX hπ Γ κ
  have hz := component_POrder_reader omegaX hπ Γ ζ
  have hp := (curvePOrder_modificationPullback_iff omegaX omegaY hπ _ _).mp hr.1
  have hq := (curvePOrder_modificationPullback_iff omegaX omegaY hπ _ _).mp hr.2
  exact ⟨SourceTestCurvePOrder.trans omegaY
      (SourceTestCurvePOrder.trans omegaY hk.2 hp) hz.1,
    SourceTestCurvePOrder.trans omegaY
      (SourceTestCurvePOrder.trans omegaY hz.2 hq) hk.1⟩

/-- Any independently prescribed literal downstairs reader describes the
same intrinsic type of the actual output component. -/
theorem sourceNAPullbackComponent_POrder_equivalent_reader
    (omegaX : KahlerBackground n X) (hπ : IsAnalyticModification (n := n) π)
    (Γ : SourceNAPotential θ) (κ : SourceKahlerForm n Y) (omega : KahlerBackground n X) :
    SourceTestCurvePOrder (sourceNAPullbackComponent omegaX hπ Γ κ).val
      ((Γ.realizedComponent omega).val.modificationPullback hπ) ∧
    SourceTestCurvePOrder ((Γ.realizedComponent omega).val.modificationPullback hπ)
      (sourceNAPullbackComponent omegaX hπ Γ κ).val := by
  let omegaY := sourceKahlerFormRepresentative κ
  have hc := component_POrder_reader omegaX hπ Γ κ
  have hr := Γ.realizedComponent_POrder_equivalent
    (downstairsReader omegaX omegaY hπ) omega
  have hp := (curvePOrder_modificationPullback_iff omegaX omegaY hπ _ _).mp hr.1
  have hq := (curvePOrder_modificationPullback_iff omegaX omegaY hπ _ _).mp hr.2
  exact ⟨SourceTestCurvePOrder.trans omegaY hc.2 hp,
    SourceTestCurvePOrder.trans omegaY hq hc.1⟩

/-- Original inverse-system compatibility is a proved consequence of genuine
P-type and same-background antisymmetry; the upstairs index is unrestricted. -/
theorem sourceNAPullbackComponent_compatible
    (omegaX : KahlerBackground n X) (hπ : IsAnalyticModification (n := n) π)
    (Γ : SourceNAPotential θ) (κ ζ : SourceKahlerForm n Y)
    (h : sourceKahlerFormLE κ ζ) :
    sourceIModelTestCurveTransition (sourceKahlerFormRepresentative ζ)
      (sourceNAComponentBackground_difference (θ.nativeHolomorphicPullback hπ.1) h)
      (sourceNAPullbackComponent omegaX hπ Γ κ) = sourceNAPullbackComponent omegaX hπ Γ ζ := by
  let omegaY := sourceKahlerFormRepresentative ζ
  have ht := sourceIModelTestCurveTransition_POrder_equivalent omegaY
    (sourceNAComponentBackground_difference (θ.nativeHolomorphicPullback hπ.1) h)
    (sourceNAPullbackComponent omegaX hπ Γ κ)
  have hs := sourceNAPullbackComponent_POrder_equivalent omegaX hπ Γ κ ζ
  apply Subtype.ext
  exact SourceTestCurvePOrder.antisymm omegaY
    (SourceTestCurvePOrder.trans omegaY ht.2 hs.1)
    (SourceTestCurvePOrder.trans omegaY hs.2 ht.1)

/-- The genuine forward map in `cor:PSHNAbimero` at ALL upstairs indices. -/
def sourceNAPullback (omegaX : KahlerBackground n X)
    (hπ : IsAnalyticModification (n := n) π) (Γ : SourceNAPotential θ) :
    SourceNAPotential (θ.nativeHolomorphicPullback hπ.1) where
  component κ := sourceNAPullbackComponent omegaX hπ Γ κ
  compatible κ ζ h := sourceNAPullbackComponent_compatible omegaX hπ Γ κ ζ h

/-- Auxiliary downstairs Kähler choices do not change the actual map. -/
theorem sourceNAPullback_independent
    (omegaX omegaX' : KahlerBackground n X) (hπ : IsAnalyticModification (n := n) π)
    (Γ : SourceNAPotential θ) : sourceNAPullback omegaX hπ Γ = sourceNAPullback omegaX' hπ Γ := by
  apply SourceNAPotential.ext
  intro κ
  let omegaY := sourceKahlerFormRepresentative κ
  have h := sourceNAPullbackComponent_POrder_equivalent_reader omegaX hπ Γ κ omegaX
  have h' := sourceNAPullbackComponent_POrder_equivalent_reader omegaX' hπ Γ κ omegaX
  apply Subtype.ext
  exact SourceTestCurvePOrder.antisymm omegaY
    (SourceTestCurvePOrder.trans omegaY h.1 h'.2)
    (SourceTestCurvePOrder.trans omegaY h'.1 h.2)

/-- The map extends literal modification pullback of actual positive
I-model test curves, so it is the source pullback rather than an arbitrary
bijection between the two inverse-system types. -/
theorem sourceNAPullback_positive_embedding
    (omegaX : KahlerBackground n X) (omegaY : KahlerBackground n Y)
    (hπ : IsAnalyticModification (n := n) π) (G : SourcePositiveIModelTestCurve θ) :
    sourceNAPullback omegaX hπ (sourcePositiveTestCurveToNA G) =
      sourcePositiveTestCurveToNA (SGPT.NAPotential.DH.positiveCurveModificationPullback hπ omegaY G) := by
  let E := sourcePositiveTestCurveToNA G
  let H := SGPT.NAPotential.DH.positiveCurveModificationPullback hπ omegaY G
  have he := sourcePositiveTestCurveToNA_realizedComponent_POrder_equivalent G omegaX
  have hp := (curvePOrder_modificationPullback_iff omegaX omegaY hπ _ _).mp he.1
  have hq := (curvePOrder_modificationPullback_iff omegaX omegaY hπ _ _).mp he.2
  apply SourceNAPotential.ext
  intro κ
  let B := sourceKahlerFormRepresentative κ
  have hf := sourceNAPullbackComponent_POrder_equivalent_reader omegaX hπ E κ omegaX
  have ht := sourceIModelTestCurveTransition_POrder_equivalent B
    (sourceNAComponentBackground_positive (θ.nativeHolomorphicPullback hπ.1) κ) H
  apply Subtype.ext
  exact SourceTestCurvePOrder.antisymm omegaY
    (SourceTestCurvePOrder.trans omegaY hf.1 (SourceTestCurvePOrder.trans omegaY hp ht.1))
    (SourceTestCurvePOrder.trans omegaY ht.2 (SourceTestCurvePOrder.trans omegaY hq hf.2))

/-- The forward map preserves and reflects the original order across arbitrary
original backgrounds; this supplies injectivity without assuming descent. -/
theorem sourceNAPOrder_pullback_iff
    (omegaX : KahlerBackground n X) (omegaY : KahlerBackground n Y)
    (hπ : IsAnalyticModification (n := n) π)
    (Γ : SourceNAPotential θ) (Δ : SourceNAPotential σ) :
    SourceNAPOrder Γ Δ ↔
      SourceNAPOrder (sourceNAPullback omegaX hπ Γ) (sourceNAPullback omegaX hπ Δ) := by
  let κ := sourceKahlerFormOfBackground omegaY
  let D := downstairsReader omegaX (sourceKahlerFormRepresentative κ) hπ
  have hg := component_POrder_reader omegaX hπ Γ κ
  have hd := component_POrder_reader omegaX hπ Δ κ
  rw [sourceNAPOrder_iff_realizedComponents Γ Δ D D,
    sourceNAPOrder_iff_component _ _ κ]
  constructor
  · intro h
    have hp := (curvePOrder_modificationPullback_iff omegaX omegaY hπ _ _).mp h
    exact SourceTestCurvePOrder.trans omegaY
      (SourceTestCurvePOrder.trans omegaY hg.2 hp) hd.1
  · intro h
    apply (curvePOrder_modificationPullback_iff omegaX omegaY hπ _ _).mpr
    exact SourceTestCurvePOrder.trans omegaY
      (SourceTestCurvePOrder.trans omegaY hg.1 h) hd.2

/-- Injectivity is genuine but is only one half of the source corollary. -/
theorem sourceNAPullback_injective
    (omegaX : KahlerBackground n X) (omegaY : KahlerBackground n Y)
    (hπ : IsAnalyticModification (n := n) π) :
    Function.Injective (sourceNAPullback (θ := θ) omegaX hπ) := by
  intro Γ Δ h
  apply SourceNAPOrder.antisymm
  · apply (sourceNAPOrder_pullback_iff omegaX omegaY hπ Γ Δ).mpr
    rw [h]
    exact SourceNAPOrder.refl omegaY _
  · apply (sourceNAPOrder_pullback_iff omegaX omegaY hπ Δ Γ).mpr
    rw [h]
    exact SourceNAPOrder.refl omegaY _

end SGPT.PSH.VariableComplexAtlas.WholeClosureNA
