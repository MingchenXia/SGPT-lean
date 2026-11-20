import SGPT.Checks.Comparison.BJActualMaxPromotion

/-! Genuine source GF promotion and internally constructed fixed-numerical
target decreasing nets across an actual ample class gap. This does not claim
singular class-perturbation limit closure. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
namespace SGPT.NAPotential.BJ.Printed
open AlgebraicGeometry CategoryTheory Filter Topology SGPT.Foundations.Schemes
open Scheme.Modules SGPT.Foundations.Envelope SGPT.Foundations.Envelope.NativeNumericalFubiniStudy
open SGPT.NAPotential.Berkovich SGPT.NAPotential.Berkovich.BJSections
open SGPT.NAPotential.BJ SGPT.NAPotential.BJ.NativePicard
open SGPT.NAPotential.BJ.MaxClosure
open scoped Classical NNReal ENNReal
variable {X : Scheme.{0}} (p : X ⟶ Spec (.of ℂ)) [IsProjective p] [IsIntegral X]
local instance : IsProper p := (ProjectiveFactorizationRingIso.of_isProjective p).isProper

/-- A genuine numerical ample gap internally produces an actual prescribed
ray and original sections/atlas/rational weights, retaining the whole function. -/
theorem exists_sourceGF_of_ample_gap (D : RationalGFPackage X) (L : RationalPicardSpace X)
    (hgap : NativePicard.numericalClass p L-D.numericalClass p∈NativeRealNumericalClasses.ampleCone p) :
    ∃ E : RationalGFPackage X, E.numericalClass p=NativePicard.numericalClass p L ∧
      ∀ v : BerkovichPoint p,E.eval p v=D.eval p v := by
  obtain ⟨M,a,m,hm,hrep⟩ := exists_actual_line_presentation L
  let hM := isInvertible_of_atlas a
  have hclass : NativePicard.numericalClass p L=
      (m:ℝ)⁻¹•NativeRealNumericalClasses.lineClass p M hM := by
    rw [hrep,numericalClass_normalized_line]
  have hGap : (((m:ℚ)⁻¹:ℚ):ℝ)•NativeRealNumericalClasses.lineClass p M hM-
      D.toNative.numericalClass p∈NativeRealNumericalClasses.ampleCone p := by
    rw [Rat.cast_inv,Rat.cast_natCast,← hclass,D.toNative_numericalClass]
    exact hgap
  obtain ⟨R,hRat,hNZ,hEval⟩ := RationalPromotion.exists_rationalRay_of_numerical_ampleGap p
    D.toNative D.toNative_nonzero D.toNative_isRational M hM (m:ℚ)⁻¹
    (inv_nonneg.mpr (Nat.cast_nonneg m)) hGap
  let N := FSData.ofRay M hM R
  let E := NativeGF.ofNativeRational N hNZ hRat
  refine ⟨E,?_,?_⟩
  · rw [NativeGF.ofNativeRational_numericalClass,FSData.ofRay_numericalClass]
    rw [Rat.cast_inv,Rat.cast_natCast,← hclass]
  · intro v
    rw [NativeGF.ofNativeRational_eval,FSData.ofRay_eval,hEval,D.toNative_eval]

/-- Every actual original psh metric has a genuine decreasing net with a
prescribed constant numerical class across an ordinary geometric ample gap.
No target net/index/directedness/value/class output is a caller premise. -/
theorem IsModuleTopologyPSH.exists_fixed_target_numericalClass_net
    {L M : RationalPicardSpace X} {φ : BerkovichPoint p → EReal}
    (h : IsModuleTopologyPSH.{u} p L φ)
    (hgap : NativePicard.numericalClass p M-NativePicard.numericalClass p L∈
      NativeRealNumericalClasses.ampleCone p) :
    ∃ E : DecreasingGFNet.{u} p,
      (∀ i,(E.term i).numericalClass p=NativePicard.numericalClass p M) ∧
      ∀ v,Tendsto (fun i => (E.term i).eval p v) atTop (𝓝 (φ v)) := by
  obtain ⟨_,D,hclass,hlim⟩ := h
  have hAmp := ampleTendsto_of_moduleTopology p hclass
  have hev : ∀ᶠ i in atTop,
      NativePicard.numericalClass p M-(D.term i).numericalClass p∈
        NativeRealNumericalClasses.ampleCone p := by
    have heq : NativePicard.numericalClass p L+
        (NativePicard.numericalClass p M-NativePicard.numericalClass p L)=
        NativePicard.numericalClass p M := by abel
    simpa only [heq] using hAmp.eventually_sub_mem hgap
  obtain ⟨i₀,hi₀⟩ := eventually_atTop.mp hev
  let I := {i : D.I // i₀ ≤ i}
  have : Nonempty I := ⟨⟨i₀,le_rfl⟩⟩
  have : IsDirectedOrder I := isDirected_subtype_le i₀
  choose F hFclass hFeval using fun i : I =>
    exists_sourceGF_of_ample_gap p (D.term i) M (hi₀ i i.property)
  let E : DecreasingGFNet.{u} p := {
    I := I
    preorder := inferInstance
    nonempty := inferInstance
    directed := inferInstance
    term := F
    decreasing := fun v i j hij => by
      change (F j).eval p v ≤ (F i).eval p v
      rw [hFeval i v,hFeval j v]
      exact D.decreasing v hij }
  refine ⟨E,hFclass,?_⟩
  intro v
  have ht := (hlim v).comp (tendsto_subtype_val_atTop i₀)
  convert ht using 1
  funext i
  exact hFeval i v

/-- Honest one-sided original class operation, valid also for non-nef L;
the singular limiting-class stability proposition is a separate obligation. -/
theorem IsModuleTopologyPSH.mono_ample_class
    {L M : RationalPicardSpace X} {φ : BerkovichPoint p → EReal}
    (h : IsModuleTopologyPSH.{u} p L φ)
    (hgap : NativePicard.numericalClass p M-NativePicard.numericalClass p L∈
      NativeRealNumericalClasses.ampleCone p) : IsModuleTopologyPSH.{u} p M φ := by
  let := numericalModuleTopology p
  obtain ⟨E,hclass,hlim⟩ := h.exists_fixed_target_numericalClass_net p hgap
  refine ⟨h.1,E,?_,hlim⟩
  have heq : (fun i : E.I => (E.term i).numericalClass p)=
      fun _ : E.I => NativePicard.numericalClass p M := funext hclass
  rw [heq]
  exact tendsto_const_nhds

end SGPT.NAPotential.BJ.Printed
