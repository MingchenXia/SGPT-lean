import SGPT.Checks.Comparison.ThinApprox.BJActualMaxPromotion
import SGPT.Checks.Comparison.BJCofinalMaxTails

/-! ENTIRE original BJ maximum closure for the explicit canonical numerical
module-topology definition. All ample lines, data, output index/cofinalities,
classes and ALL original-point limits are produced internally; no global FD.
The book topology convention is an explicit source-review interpretation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
namespace SGPT.NAPotential.OperationComparison
open AlgebraicGeometry CategoryTheory Filter Topology SGPT.Foundations.Schemes
open Scheme.Modules SGPT.Foundations.Envelope
open SGPT.NAPotential.Berkovich SGPT.NAPotential.BJ.NativePicard
open SGPT.NAPotential.BJ
open SGPT.NAPotential.BJ.Printed
open SGPT.NAPotential.BJ.MaxClosure SGPT.NAPotential.ThinApprox.BJ.MaxClosure
open scoped Classical
variable {X : Scheme.{0}} (p : X ⟶ Spec (.of ℂ)) [IsProjective p] [IsIntegral X]

/-- All clauses of the source pointwise-maximum assertion, for the ACTUAL
original rational classes, section GF data and complete Berkovich point space.
Canonical moduleTopology is explicit; no FD/topology-equality/output certificate. -/
theorem isModuleTopologyPSH_max {L : RationalPicardSpace X}
    {φ ψ : BerkovichPoint p → EReal}
    (hφ : IsModuleTopologyPSH.{u} p L φ) (hψ : IsModuleTopologyPSH.{u} p L ψ) :
    IsModuleTopologyPSH.{u} p L (fun v => Max.max (φ v) (ψ v)) := by
  obtain ⟨hneφ,D,hDclass,hDlim⟩ := hφ
  obtain ⟨hneψ,E,hEclass,hElim⟩ := hψ
  obtain ⟨H,hH⟩ := NativeRealNumericalClasses.exists_geometric_ample_line p
  let aH := atlasOfInvertible hH.isInvertible
  let θ := NativePicard.numericalClass p L
  let η := NativeRealNumericalClasses.lineClass p H hH.isInvertible
  let ε : ℕ → ℚ := fun N => 1/((N+1:ℕ):ℚ)
  let target : ℕ → RationalPicardSpace X := fun N => L+ε N•rationalPicardClass aH
  have hη : η∈NativeRealNumericalClasses.ampleCone p :=
    NativeRealNumericalClasses.ampleLineClass_mem_ampleCone p H hH
  have hεpos (N : ℕ) : 0<(ε N:ℝ) := by
    dsimp only [ε]
    positivity
  have hTarget (N : ℕ) : NativePicard.numericalClass p (target N)=θ+(ε N:ℝ)•η := by
    change NativePicard.numericalClass p (L+ε N•rationalPicardClass aH)=_
    rw [map_add,numericalClass_rat_smul_real,NativePicard.numericalClass_line]
  have hAmp (N : ℕ) : (ε N:ℝ)•η∈NativeRealNumericalClasses.ampleCone p :=
    (NativeRealNumericalClasses.ampleCone p).smul_mem (hεpos N) hη
  have hOrderD := ampleTendsto_of_moduleTopology p hDclass
  have hOrderE := ampleTendsto_of_moduleTopology p hEclass
  choose iN hiN using fun N => eventually_atTop.mp (hOrderD.eventually_sub_mem (hAmp N))
  choose jN hjN using fun N => eventually_atTop.mp (hOrderE.eventually_sub_mem (hAmp N))
  let K := SimultaneousTails iN jN
  have hGapD (t : K) : NativePicard.numericalClass p (target (level iN jN t))-
      (D.term (first iN jN t)).numericalClass p∈NativeRealNumericalClasses.ampleCone p := by
    rw [hTarget]
    exact hiN _ _ (first_ge_threshold iN jN t)
  have hGapE (t : K) : NativePicard.numericalClass p (target (level iN jN t))-
      (E.term (second iN jN t)).numericalClass p∈NativeRealNumericalClasses.ampleCone p := by
    rw [hTarget]
    exact hjN _ _ (second_ge_threshold iN jN t)
  choose F hFclass hFeval using fun t : K => exists_sourceGF_max_of_ample_gaps p
    (D.term (first iN jN t)) (E.term (second iN jN t)) (target (level iN jN t))
    (hGapD t) (hGapE t)
  let Out : DecreasingGFNet.{u} p := {
    I := K
    preorder := inferInstance
    nonempty := inferInstance
    directed := inferInstance
    term := F
    decreasing := fun v t s hts => by
      change (F s).eval p v≤(F t).eval p v
      rw [hFeval s,hFeval t]
      exact max_le_max (D.decreasing v (first_monotone iN jN hts))
        (E.decreasing v (second_monotone iN jN hts)) }
  have hne : ∃ v,Max.max (φ v) (ψ v)≠⊥ := by
    obtain ⟨v,hv⟩ := hneφ
    exact ⟨v,ne_bot_of_le_ne_bot hv (le_max_left _ _)⟩
  refine ⟨hne,Out,?_,?_⟩
  · let := numericalModuleTopology p
    let : IsTopologicalAddGroup (NativeRealNumericalClasses.Space p) :=
      IsModuleTopology.topologicalAddGroup ℝ (NativeRealNumericalClasses.Space p)
    have hεlim : Tendsto (fun N => (ε N:ℝ)) atTop (𝓝 (0:ℝ)) := by
      simpa only [ε,Rat.cast_div,Rat.cast_add,Rat.cast_one,Rat.cast_natCast,Nat.cast_add,Nat.cast_one]
        using tendsto_one_div_add_atTop_nhds_zero_nat
    let : ContinuousSMul ℝ (NativeRealNumericalClasses.Space p) :=
      ModuleTopology.continuousSMul ℝ (NativeRealNumericalClasses.Space p)
    have hc : Continuous (fun t : ℝ => θ+t•η) := by
      have hs : Continuous (fun t : ℝ => t•η) :=
        (continuous_id : Continuous (fun t : ℝ => t)).smul
          (continuous_const : Continuous (fun _ : ℝ => η))
      exact (continuous_const : Continuous (fun _ : ℝ => θ)).add hs
    have ht : Tendsto (fun N => θ+(ε N:ℝ)•η) atTop (𝓝 θ) := by
      simpa only [Function.comp_def,zero_smul,add_zero] using (hc.tendsto 0).comp hεlim
    have hlev := ht.comp (level_tendsto iN jN)
    exact hlev.congr' (Eventually.of_forall fun t : K =>
      ((hFclass t).trans (hTarget (level iN jN t))).symm)
  · intro v
    have hlim := ((hDlim v).comp (first_tendsto iN jN)).max
      ((hElim v).comp (second_tendsto iN jN))
    exact hlim.congr' (Eventually.of_forall fun t : K => (hFeval t v).symm)

end SGPT.NAPotential.OperationComparison
