import SGPT.NAPotential.BJPrepDivisorialTransform
import SGPT.PSH.SourceTestCurveGeneralSup
import SGPT.PSH.SourceMixedIVolumeSemicontinuityTails

/-! Actual cofinal original slice readers for increasing divisorial transforms.
Blueprint: increasing-divisorial-sup.tex. -/
set_option autoImplicit false
noncomputable section
universe u v
namespace SGPT.NAPotential.BJPrep
open Set Filter
open scoped ENNReal Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.PSH SGPT.PSH.VariableComplexAtlas SGPT.PSH.CompactPrimeOver

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

/-- The SAME original reader on the actual increasing-supremum slice,
with a genuine cofinal tail of original strict slices. -/
theorem presentationReader_increasingSup_potential {I : Type v} [Preorder I]
    [IsDirectedOrder I] [Nonempty I] (omega : KahlerBackground n M)
    (Γ : I → SourceTestCurve θ)
    (hm : ∀ i j, i ≤ j → SourceTestCurvePOrder (Γ i) (Γ j))
    (hb : BddAbove (range fun i => (Γ i).max))
    (r : Iio (SourceTestCurve.increasingSup omega Γ hm hb).max)
    (i₀ : I) (hr₀ : r.val < (Γ i₀).max) (p : PrimePresentation n M) :
    presentationReader ((SourceTestCurve.increasingSup omega Γ hm hb).potential r) p =
      ⨅ i : {i : I // i₀ ≤ i}, presentationReader
        ((Γ i.val).potential ⟨r.val,hr₀.trans_le (hm i₀ i.val i.property).cutoff_le⟩) p := by
  let J := {i : I // i₀ ≤ i}
  have : Nonempty J := ⟨⟨i₀,le_rfl⟩⟩
  have ho (i : J) : r.val < (Γ i.val).max :=
    hr₀.trans_le (hm i₀ i.val i.property).cutoff_le
  let u : J → M → EReal := fun i => (Γ i.val).potential ⟨r.val,ho i⟩
  have heq : (⨆ i : J, u i) =
      ⨆ i, sourceTestCurveAt (Γ i).toSourceTestCurvePredata r.val := by
    have htail := sourceIncreasing_iSup_tail
      (fun i => sourceTestCurveAt (Γ i).toSourceTestCurvePredata r.val)
      (sourceTestCurveSup_extension_monotone omega Γ hm r.val) i₀
    convert htail using 1
    congr 1
    funext i
    exact (sourceTestCurveAt_of_lt _ (ho i)).symm
  have hreader := SGPT.PSH.SourceUSCTailsDraft.presentationReader_uscSup_eq_iInf θ u
    (fun i => (Γ i.val).thetaPSH ⟨r.val,ho i⟩)
    (B := 0) (fun i x => (Γ i.val).le_zero ⟨r.val,ho i⟩ x) p
  change presentationReader (sourceTestCurveSupPotential Γ r.val) p = _
  simpa only [uscSup,← iSup_apply,heq,sourceTestCurveSupPotential] using hreader

omit [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in
/-- Every actual transform term is below the original cutoff. -/
theorem curveDivisorialTransform_le_cutoff (C : SourceTestCurvePredata θ)
    (p : PrimePresentation n M) {t : ℝ} (ht : 0 ≤ t) :
    curveDivisorialTransform C p t ≤ (C.max : EReal) := by
  refine iSup₂_le fun r hr => ?_
  rw [curveDivisorialTransform_term C p t hr]
  apply EReal.coe_le_coe_iff.mpr
  nlinarith [sliceLelong_nonneg C p r]

/-- The actual original directed supremum has the SAME pointwise
supremum of original prime transforms, with all cofinal-reader data internal. -/
theorem curveDivisorialTransform_increasingSup {I : Type v} [Preorder I]
    [IsDirectedOrder I] [Nonempty I] (omega : KahlerBackground n M)
    (Γ : I → SourceTestCurve θ)
    (hm : ∀ i j, i ≤ j → SourceTestCurvePOrder (Γ i) (Γ j))
    (hb : BddAbove (range fun i => (Γ i).max))
    (p : PrimePresentation n M) {t : ℝ} (ht : 0 < t) :
    curveDivisorialTransform (SourceTestCurve.increasingSup omega Γ hm hb).toSourceTestCurvePredata p t =
      ⨆ i, curveDivisorialTransform (Γ i).toSourceTestCurvePredata p t := by
  classical
  let D := SourceTestCurve.increasingSup omega Γ hm hb
  let F : I → EReal := fun i => curveDivisorialTransform (Γ i).toSourceTestCurvePredata p t
  obtain ⟨B,hB⟩ := hb
  have hupper : (⨆ i, F i) ≤ (B : EReal) := by
    apply iSup_le
    intro i
    exact (curveDivisorialTransform_le_cutoff (Γ i).toSourceTestCurvePredata p ht.le).trans
      (EReal.coe_le_coe_iff.mpr (hB (mem_range_self i)))
  have htop : (⨆ i, F i) ≠ ⊤ := ne_of_lt (hupper.trans_lt (EReal.coe_lt_top B))
  let j := Classical.arbitrary I
  have hj : (Γ j).max-1 < (Γ j).max := by linarith
  have hlow := (le_curveDivisorialTransform (Γ j).toSourceTestCurvePredata p t hj).trans
    (le_iSup F j)
  rw [curveDivisorialTransform_term (Γ j).toSourceTestCurvePredata p t hj] at hlow
  have hbot : (⨆ i, F i) ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hlow
  let A := (⨆ i, F i).toReal
  have hA : (⨆ i, F i) = (A : EReal) := (EReal.coe_toReal htop hbot).symm
  change curveDivisorialTransform D.toSourceTestCurvePredata p t = ⨆ i, F i
  apply le_antisymm
  · rw [hA]
    refine iSup₂_le fun r hr => ?_
    obtain ⟨i₀,hr₀⟩ := sourceTestCurveSupCutoff_exists Γ hr
    have hν := presentationReader_ne_top (D.thetaPSH ⟨r,hr⟩) p
    have hcost : ENNReal.ofReal ((r-A)/t) ≤ presentationReader (D.potential ⟨r,hr⟩) p := by
      rw [presentationReader_increasingSup_potential omega Γ hm ⟨B,hB⟩ ⟨r,hr⟩ i₀ hr₀ p]
      refine le_iInf fun i => ?_
      have hi : r < (Γ i.val).max := hr₀.trans_le (hm i₀ i.val i.property).cutoff_le
      have hiν := presentationReader_ne_top ((Γ i.val).thetaPSH ⟨r,hi⟩) p
      have hterm := (le_curveDivisorialTransform (Γ i.val).toSourceTestCurvePredata p t hi).trans
        ((le_iSup F i.val).trans_eq hA)
      rw [← EReal.coe_ennreal_toReal hiν,← EReal.coe_mul,← EReal.coe_sub] at hterm
      have htermR := EReal.coe_le_coe_iff.mp hterm
      rw [ENNReal.ofReal_le_iff_le_toReal hiν]
      apply (div_le_iff₀ ht).mpr
      linarith
    have hcostR := (ENNReal.ofReal_le_iff_le_toReal hν).mp hcost
    rw [← EReal.coe_ennreal_toReal hν,← EReal.coe_mul,← EReal.coe_sub]
    apply EReal.coe_le_coe_iff.mpr
    have hmul := (div_le_iff₀ ht).mp hcostR
    linarith
  · apply iSup_le
    intro i
    obtain ⟨hcut,hle⟩ := (sourceTestCurvePOrder_iff omega (Γ i) D).mp
      (SourceTestCurve.le_increasingSup omega Γ hm ⟨B,hB⟩ i)
    exact curveDivisorialTransform_mono (Γ i).toSourceTestCurvePredata D.toSourceTestCurvePredata
      p hcut (fun r hr => presentationReader_anti (hle r hr) p) ht.le

end SGPT.NAPotential.BJPrep
