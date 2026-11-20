import SGPT.Checks.LiteratureBridge.BJAmpleTargetNets
import SGPT.Checks.LiteratureBridge.BJCofinalMaxTails

/-! Actual ample-ray numerical labels for every arbitrary-universe original
rational GF net. Projectivity produces the direction, genuine promotion
produces packages, and actual cofinality produces every limit. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
namespace SGPT.NAPotential.BJ.Printed
open AlgebraicGeometry CategoryTheory Filter Topology SGPT.Foundations.Schemes
open Scheme.Modules SGPT.Foundations.PublishedEnvelope
open SGPT.NAPotential.Berkovich SGPT.NAPotential.BJ.NativePicard
open SGPT.NAPotential.BJ.MaxClosure
variable {X : Scheme.{0}} (p : X ⟶ Spec (.of ℂ)) [IsProjective p] [IsIntegral X]

def perturbationCoefficient (N : ℕ) : ℚ := 1/((N+1:ℕ):ℚ)

/-- Genuine original ray-labeled net, with actual ample geometry and all
directedness/class/function outputs produced internally. -/
theorem IsModuleTopologyPSH.exists_ample_ray_labeled_net
    {L : RationalPicardSpace X} {φ : BerkovichPoint p → EReal}
    (h : IsModuleTopologyPSH.{u} p L φ) :
    ∃ (η : NativeRealNumericalClasses.Space p) (E : DecreasingGFNet.{u} p)
      (level : E.I → ℕ),
      η∈NativeRealNumericalClasses.ampleCone p ∧ Tendsto level atTop atTop ∧
      (∀ i,(E.term i).numericalClass p=NativePicard.numericalClass p L+
        (perturbationCoefficient (level i):ℝ)•η) ∧
      ∀ v,Tendsto (fun i => (E.term i).eval p v) atTop (𝓝 (φ v)) := by
  obtain ⟨_,D,hDclass,hDlim⟩ := h
  obtain ⟨H,hH⟩ := NativeRealNumericalClasses.exists_geometric_ample_line p
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
  have hDamp := ampleTendsto_of_moduleTopology p hDclass
  choose iN hiN using fun N => eventually_atTop.mp (hDamp.eventually_sub_mem (hAmp N))
  let K := SimultaneousTails iN iN
  choose F hFclass hFeval using fun k : K =>
    exists_sourceGF_of_ample_gap p (D.term (first iN iN k)) (target (level iN iN k)) (by
      rw [hTarget]
      exact hiN _ _ (first_ge_threshold iN iN k))
  let E : DecreasingGFNet.{u} p := {
    I := K
    preorder := inferInstance
    nonempty := inferInstance
    directed := inferInstance
    term := F
    decreasing := fun v i j hij => by
      change (F j).eval p v ≤ (F i).eval p v
      rw [hFeval i v,hFeval j v]
      exact D.decreasing v (first_monotone iN iN hij) }
  refine ⟨η,E,level iN iN,hη,level_tendsto iN iN,?_,?_⟩
  · intro i
    rw [hFclass i,hTarget]
  · intro v
    have ht := (hDlim v).comp (first_tendsto iN iN)
    convert ht using 1
    funext i
    exact hFeval i v

end SGPT.NAPotential.BJ.Printed
