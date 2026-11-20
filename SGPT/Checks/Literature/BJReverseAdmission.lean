import SGPT.Checks.LiteratureBridge.BJAmpleRayReindex
import SGPT.Checks.Literature.BJRationalization
import SGPT.Checks.LiteratureBridge.BJNativePSHAdmission

/-! Genuine native-to-original admission through internally constructed
numerical ample-ray nets. No numerical topology equality is asserted. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.NAPotential.BJ.ExternalReverseAdmission
open AlgebraicGeometry CategoryTheory Filter Topology
open SGPT.Foundations.PublishedEnvelope SGPT.Foundations.PublishedEnvelope.NativeNumericalFubiniStudy
open SGPT.NAPotential.Berkovich SGPT.NAPotential.Berkovich.BJSections
open SGPT.NAPotential.BJ SGPT.NAPotential.BJ.NativePicard
open SGPT.NAPotential.BJ.Printed
open SGPT.NAPotential.BJ.MaxClosure
open scoped Classical NNReal ENNReal
variable {X : Scheme.{0}} (p : X ⟶ Spec (.of ℂ)) [IsProjective p] [IsIntegral X]
local instance : IsProper p := (ProjectiveFactorizationRingIso.of_isProjective p).isProper

/-- Every actual native psh function gives an ORIGINAL module-topology
rational-GF net at the actual rational Picard target. All output data are produced. -/
theorem isModuleTopologyPSH_of_nativePSH_with_ample
    (H : X.Modules) (hH : SchemeLineAmpleness.IsAmple p H)
    {L : RationalPicardSpace X} {φ : BerkovichPoint p → EReal}
    (h : Variety.IsPSH p (NativePicard.numericalClass p L)
      (fun y => φ ((pointEquiv p).symm y))) : IsModuleTopologyPSH.{0} p L φ := by
  obtain ⟨J,hJ,hDir,hNe,D,hD,hDclass,hAnti,hInf⟩ := varietyPSH_exists_rationalFS_net p h
  let := hJ
  let := hDir
  let := hNe
  let aH := atlasOfInvertible hH.isInvertible
  let θ := NativePicard.numericalClass p L
  let η := NativeRealNumericalClasses.lineClass p H hH.isInvertible
  let target : ℕ → RationalPicardSpace X :=
    fun N => L+perturbationCoefficient N•rationalPicardClass aH
  have hη : η∈NativeRealNumericalClasses.ampleCone p :=
    NativeRealNumericalClasses.ampleLineClass_mem_ampleCone p H hH
  have hεpos (N : ℕ) : 0<(perturbationCoefficient N:ℝ) := by
    unfold perturbationCoefficient
    positivity
  have hTarget (N : ℕ) : NativePicard.numericalClass p (target N)=
      θ+(perturbationCoefficient N:ℝ)•η := by
    change NativePicard.numericalClass p
      (L+perturbationCoefficient N•rationalPicardClass aH)=_
    rw [map_add,numericalClass_rat_smul_real,NativePicard.numericalClass_line]
  have hAmp (N : ℕ) : (perturbationCoefficient N:ℝ)•η∈
      NativeRealNumericalClasses.ampleCone p :=
    (NativeRealNumericalClasses.ampleCone p).smul_mem (hεpos N) hη
  choose iN hiN using fun N => eventually_atTop.mp (hDclass.eventually_sub_mem (hAmp N))
  let K := SimultaneousTails iN iN
  let S (i : J) : RationalGFPackage X := NativeGF.ofNativeRational (D i) (hD i).2 (hD i).1
  have hSclass (i : J) : (S i).numericalClass p=(D i).numericalClass p :=
    NativeGF.ofNativeRational_numericalClass p (D i) (hD i).2 (hD i).1
  have hSeval (i : J) (v : BerkovichPoint p) : (S i).eval p v=(D i).eval p (pointEquiv p v) :=
    NativeGF.ofNativeRational_eval p (D i) (hD i).2 (hD i).1 v
  choose F hFclass hFeval using fun k : K =>
    exists_sourceGF_of_ample_gap p (S (first iN iN k)) (target (level iN iN k)) (by
      rw [hSclass,hTarget]
      exact hiN _ _ (first_ge_threshold iN iN k))
  let E : DecreasingGFNet.{0} p := {
    I := K
    preorder := inferInstance
    nonempty := inferInstance
    directed := inferInstance
    term := F
    decreasing := fun v i j hij => by
      change (F j).eval p v≤(F i).eval p v
      rw [hFeval i v,hFeval j v,hSeval,hSeval]
      exact hAnti (pointEquiv p v) (first_monotone iN iN hij) }
  have hne : ∃ v,φ v≠⊥ := by
    obtain ⟨y,hy⟩ := h.exists_ne_bot
    exact ⟨(pointEquiv p).symm y,hy⟩
  refine ⟨hne,E,?_,?_⟩
  · let := numericalModuleTopology p
    let : IsTopologicalAddGroup (NativeRealNumericalClasses.Space p) :=
      IsModuleTopology.topologicalAddGroup ℝ (NativeRealNumericalClasses.Space p)
    let : ContinuousSMul ℝ (NativeRealNumericalClasses.Space p) :=
      ModuleTopology.continuousSMul ℝ (NativeRealNumericalClasses.Space p)
    have hεlim : Tendsto (fun N => (perturbationCoefficient N:ℝ)) atTop (𝓝 (0:ℝ)) := by
      simpa [perturbationCoefficient] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    have hc : Continuous (fun t : ℝ => θ+t•η) := by
      exact (continuous_const : Continuous (fun _ : ℝ => θ)).add
        ((continuous_id : Continuous (fun t : ℝ => t)).smul
          (continuous_const : Continuous (fun _ : ℝ => η)))
    have ht : Tendsto (fun N => θ+(perturbationCoefficient N:ℝ)•η) atTop (𝓝 θ) := by
      simpa only [Function.comp_def,zero_smul,add_zero] using (hc.tendsto 0).comp hεlim
    have hNum (k : K) : (E.term k).numericalClass p=
        θ+(perturbationCoefficient (level iN iN k):ℝ)•η := by
      change (F k).numericalClass p=_
      rw [hFclass,hTarget]
    exact (ht.comp (level_tendsto iN iN)).congr' (Eventually.of_forall fun k => (hNum k).symm)
  · intro v
    have hlim : Tendsto (fun i => (D i).eval p (pointEquiv p v)) atTop (𝓝 (φ v)) := by
      have hi := hInf (pointEquiv p v)
      simp only [Equiv.symm_apply_apply] at hi
      rw [hi]
      exact tendsto_atTop_iInf (hAnti (pointEquiv p v))
    have ht := hlim.comp (first_tendsto iN iN)
    convert ht using 1
    funext k
    exact (hFeval k v).trans (hSeval _ v)

/-- The ample line required by reverse admission is internally produced. -/
theorem isModuleTopologyPSH_of_nativePSH
    {L : RationalPicardSpace X} {φ : BerkovichPoint p → EReal}
    (h : Variety.IsPSH p (NativePicard.numericalClass p L)
      (fun y => φ ((pointEquiv p).symm y))) : IsModuleTopologyPSH.{0} p L φ := by
  obtain ⟨H,hH⟩ := NativeRealNumericalClasses.exists_geometric_ample_line p
  exact isModuleTopologyPSH_of_nativePSH_with_ample p H hH h

/-- Equality of actual original/native psh predicates, produced geometrically;
this is NOT an equality of all numerical topologies. -/
theorem isModuleTopologyPSH_iff_nativePSH
    (L : RationalPicardSpace X) (φ : BerkovichPoint p → EReal) :
    IsModuleTopologyPSH.{0} p L φ ↔ Variety.IsPSH p (NativePicard.numericalClass p L)
      (fun y => φ ((pointEquiv p).symm y)) :=
  ⟨fun h => h.isNativePSH p,isModuleTopologyPSH_of_nativePSH p⟩

end SGPT.NAPotential.BJ.ExternalReverseAdmission
