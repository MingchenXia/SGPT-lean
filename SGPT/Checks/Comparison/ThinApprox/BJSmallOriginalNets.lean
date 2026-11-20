import SGPT.Checks.Comparison.ThinApprox.BJAmpleRayReindex
import SGPT.Checks.Comparison.BJSmallObservableNets

namespace SGPT.NAPotential.BJ
end SGPT.NAPotential.BJ
namespace SGPT.NAPotential.BJ.AppSeq
end SGPT.NAPotential.BJ.AppSeq
namespace SGPT.NAPotential.BJ.FixedRay
end SGPT.NAPotential.BJ.FixedRay
namespace SGPT.NAPotential.BJ.MaxClosure
end SGPT.NAPotential.BJ.MaxClosure
namespace SGPT.NAPotential.BJ.Pair3ClassStability
end SGPT.NAPotential.BJ.Pair3ClassStability
namespace SGPT.NAPotential.BJ.Pair3Div
end SGPT.NAPotential.BJ.Pair3Div
namespace SGPT.NAPotential.BJ.Printed
end SGPT.NAPotential.BJ.Printed
namespace SGPT.NAPotential.BJ.RationalPromotion
end SGPT.NAPotential.BJ.RationalPromotion
namespace SGPT.NAPotential.BJ.SourceDXZPositive
end SGPT.NAPotential.BJ.SourceDXZPositive
namespace SGPT.NAPotential.BJ.SourceDivUnique
end SGPT.NAPotential.BJ.SourceDivUnique
namespace SGPT.NAPotential.BJ.SourceNet
end SGPT.NAPotential.BJ.SourceNet
namespace SGPT.NAPotential.BJ.SourceRationalPromotion
end SGPT.NAPotential.BJ.SourceRationalPromotion
namespace SGPT.NAPotential.BJCycle
end SGPT.NAPotential.BJCycle
namespace SGPT.NAPotential.BJModel
end SGPT.NAPotential.BJModel
namespace SGPT.NAPotential.ThinApprox.BJ
end SGPT.NAPotential.ThinApprox.BJ
namespace SGPT.NAPotential.ThinApprox.BJ.AppSeq
end SGPT.NAPotential.ThinApprox.BJ.AppSeq
namespace SGPT.NAPotential.ThinApprox.BJ.FixedRay
end SGPT.NAPotential.ThinApprox.BJ.FixedRay
namespace SGPT.NAPotential.ThinApprox.BJ.MaxClosure
end SGPT.NAPotential.ThinApprox.BJ.MaxClosure
namespace SGPT.NAPotential.ThinApprox.BJ.Pair3ClassStability
end SGPT.NAPotential.ThinApprox.BJ.Pair3ClassStability
namespace SGPT.NAPotential.ThinApprox.BJ.Pair3Div
end SGPT.NAPotential.ThinApprox.BJ.Pair3Div
namespace SGPT.NAPotential.ThinApprox.BJ.Printed
end SGPT.NAPotential.ThinApprox.BJ.Printed
namespace SGPT.NAPotential.ThinApprox.BJ.SourceDXZPositive
end SGPT.NAPotential.ThinApprox.BJ.SourceDXZPositive
namespace SGPT.NAPotential.ThinApprox.BJ.SourceDivUnique
end SGPT.NAPotential.ThinApprox.BJ.SourceDivUnique
namespace SGPT.NAPotential.ThinApprox.BJ.SourceNet
end SGPT.NAPotential.ThinApprox.BJ.SourceNet
namespace SGPT.NAPotential.ThinApprox.BJCycle
end SGPT.NAPotential.ThinApprox.BJCycle
namespace SGPT.NAPotential.ThinApprox.BJModel
end SGPT.NAPotential.ThinApprox.BJModel


/-! Arbitrary-universe ORIGINAL rational GF net definitions internally
produce genuine Type0-indexed ORIGINAL nets. No Small(Pic/NS), FD or
original-index-cofinal choice is assumed. Class labels and whole functions
are small observables; actual sheaf/section data are retained by choice. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
namespace SGPT.NAPotential.ThinApprox.BJ.Printed
open SGPT.NAPotential.BJ.Printed
open AlgebraicGeometry CategoryTheory Filter Topology
open SGPT.NAPotential.Berkovich SGPT.NAPotential.BJ.NativePicard
open SGPT.Foundations.Envelope
variable {X : Scheme.{0}} (p : X ⟶ Spec (.of ℂ)) [IsProjective p] [IsIntegral X]

/-- ALL original points and actual numerical convergence retained while the
actual output directed index is internally reconstructed in Type0. -/
theorem IsModuleTopologyPSH.exists_small_original_net
    {L : RationalPicardSpace X} {φ : BerkovichPoint p → EReal}
    (h : IsModuleTopologyPSH.{u} p L φ) :
    ∃ E : DecreasingGFNet.{0} p,
      Tendsto (fun i => (E.term i).numericalClass p) atTop
        (@nhds _ (numericalModuleTopology p) (SGPT.NAPotential.BJ.NativePicard.numericalClass p L)) ∧
      ∀ v,Tendsto (fun i => (E.term i).eval p v) atTop (𝓝 (φ v)) := by
  obtain ⟨η,R,level,_hη,hlevel,hclass,hlim⟩ := SGPT.NAPotential.ThinApprox.BJ.Printed.IsModuleTopologyPSH.exists_ample_ray_labeled_net p h
  let B : Type := ℕ × (BerkovichPoint p → EReal)
  let q : R.I → B := fun i => (level i,(R.term i).eval p)
  let a : B → BerkovichPoint p → EReal := fun b => b.2
  have hanti : ∀ v,Antitone fun i => a (q i) v := R.decreasing
  let J := SGPT.NAPotential.BJ.SmallObservable.Index q a
  have : Nonempty J := SGPT.NAPotential.BJ.SmallObservable.indexNonempty q a
  have : IsDirectedOrder J := SGPT.NAPotential.BJ.SmallObservable.indexDirected q a hanti
  let r : J → R.I := SGPT.NAPotential.BJ.SmallObservable.sourceIndex q a
  have hr (j : J) : q (r j)=j.value := SGPT.NAPotential.BJ.SmallObservable.sourceIndex_spec q a j
  have hval (j : J) (v : BerkovichPoint p) : (R.term (r j)).eval p v=a j.value v :=
    congrArg (fun b : B => a b v) (hr j)
  have hlabel : Tendsto (fun j : J => q (r j)) atTop (Filter.map q atTop) := by
    have heq : (fun j : J => q (r j))=fun j : J => j.value := funext hr
    rw [heq]
    exact SGPT.NAPotential.BJ.SmallObservable.value_tendsto q a hanti
  let E : DecreasingGFNet.{0} p := {
    I := J
    preorder := inferInstance
    nonempty := inferInstance
    directed := inferInstance
    term := fun j => R.term (r j)
    decreasing := fun v i j hij => by
      change (R.term (r j)).eval p v ≤ (R.term (r i)).eval p v
      rw [hval j v,hval i v]
      exact SGPT.NAPotential.BJ.SmallObservable.value_antitone q a v hij }
  refine ⟨E,?_,?_⟩
  · let := numericalModuleTopology p
    let : IsTopologicalAddGroup (NativeRealNumericalClasses.Space p) :=
      IsModuleTopology.topologicalAddGroup ℝ (NativeRealNumericalClasses.Space p)
    let : ContinuousSMul ℝ (NativeRealNumericalClasses.Space p) :=
      ModuleTopology.continuousSMul ℝ (NativeRealNumericalClasses.Space p)
    let θ := SGPT.NAPotential.BJ.NativePicard.numericalClass p L
    let γ : ℕ → NativeRealNumericalClasses.Space p :=
      fun N => θ+(perturbationCoefficient N:ℝ)•η
    have hε : Tendsto (fun N => (perturbationCoefficient N:ℝ)) atTop (𝓝 (0:ℝ)) := by
      simpa only [perturbationCoefficient,Rat.cast_div,Rat.cast_add,Rat.cast_one,
        Rat.cast_natCast,Nat.cast_add,Nat.cast_one] using tendsto_one_div_add_atTop_nhds_zero_nat
    have hc : Continuous (fun t : ℝ => θ+t•η) := by
      have hs : Continuous (fun t : ℝ => t•η) :=
        (continuous_id : Continuous (fun t : ℝ => t)).smul
          (continuous_const : Continuous (fun _ : ℝ => η))
      exact (continuous_const : Continuous (fun _ : ℝ => θ)).add hs
    have hγ : Tendsto γ atTop (𝓝 θ) := by
      simpa only [Function.comp_def,zero_smul,add_zero] using (hc.tendsto 0).comp hε
    have hγq : Tendsto (fun b : B => γ b.1) (Filter.map q atTop) (𝓝 θ) :=
      tendsto_map'_iff.mpr (hγ.comp hlevel)
    have ht := hγq.comp hlabel
    exact ht.congr' (Eventually.of_forall fun j : J => (hclass (r j)).symm)
  · intro v
    have hp : Tendsto (fun b : B => b.2 v) (Filter.map q atTop) (𝓝 (φ v)) :=
      tendsto_map'_iff.mpr (hlim v)
    exact hp.comp hlabel

/-- Genuine universe-size reduction for the direct ORIGINAL predicate;
neither the actual line/Picard/NS objects nor the original points change. -/
theorem IsModuleTopologyPSH.shrink
    {L : RationalPicardSpace X} {φ : BerkovichPoint p → EReal}
    (h : IsModuleTopologyPSH.{u} p L φ) : IsModuleTopologyPSH.{0} p L φ := by
  obtain ⟨E,hclass,hlim⟩ := SGPT.NAPotential.ThinApprox.BJ.Printed.IsModuleTopologyPSH.exists_small_original_net p h
  exact ⟨h.1,E,hclass,hlim⟩

end SGPT.NAPotential.ThinApprox.BJ.Printed
