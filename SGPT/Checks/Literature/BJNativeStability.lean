import SGPT.Checks.Literature.BJFinitePresentation
import SGPT.Foundations.PublishedEnvelope.MainTheorem

/-! The original specific perturbation-family adapter to the EXISTING actual
standalone unibranch PSH2 theorem. No PSH2 or analytic foundation is reproved. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.NAPotential.BJ.ExternalClassStability
open AlgebraicGeometry CategoryTheory Filter Topology
open SGPT.Foundations.PublishedEnvelope SGPT.Foundations.PublishedEnvelope.NativeRealNumericalClasses
open scoped Classical
variable {X : Scheme.{0}} (p : X ⟶ Spec (.of ℂ)) [IsProjective p] [IsIntegral X]

/-- Literal SAME-function perturbation stability on an ACTUAL unibranch
projective scheme, by the genuine exported standalone EP theorem. -/
theorem nativePSH_of_all_positive_perturbations (hX : Variety.IsUnibranch X)
    {θ η : NativeRealNumericalClasses.Space p} {φ : Variety.An p → EReal}
    (h : ∀ m : ℕ, 0 < m → Variety.IsPSH p (θ + (1 / (m : ℝ)) • η) φ) :
    Variety.IsPSH p θ φ := by
  let Θ : Fin 2 → NativeRealNumericalClasses.Space p := ![θ,η]
  obtain ⟨r,d,q,hp,hq,a,ha⟩ := exists_simultaneous_presentation p Θ
  let := hq
  let := p.stalkAlgebra (genericPoint X)
  let P := FiniteProjectiveNativeFieldModels.model q p hp
  let F := NativeRealNumericalClasses.lineFamilyMap p (Variety.presentationFactorLine d q)
    (Variety.presentationFactorLine_isInvertible d q)
  let α := a 0
  let β := a 1
  let e := OriginalProjectiveDiagonalNativeComparison.originalNativeModelHomeomorph q p hp
  let ψ := φ ∘ e.symm
  have hα : F α=θ := (ha 0).symm
  have hβ : F β=η := (ha 1).symm
  have hF (t : ℝ) : F (α+t•β)=θ+t•η := by rw [map_add,map_smul,hα,hβ]
  have hModel (n : ℕ) : P.IsPSH (α+(1/((n:ℝ)+1))•β) ψ := by
    apply (Variety.isPSH_iff_presentation d q p hp (α+(1/((n:ℝ)+1))•β) φ).mp
    change Variety.IsPSH p (F (α+(1/((n:ℝ)+1))•β)) φ
    rw [hF]
    simpa only [Nat.cast_add,Nat.cast_one] using h (n+1) (Nat.succ_pos n)
  have hP : P.IsUnibranch := (Variety.isUnibranch_iff_presentation q p hp).mp hX
  have hCoeff : Tendsto (fun n : ℕ => α+(1/((n:ℝ)+1))•β) atTop (𝓝 α) := by
    simpa only [zero_smul,add_zero] using (tendsto_const_nhds (x := α)).add
      ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).smul_const β)
  have hLimit : P.IsPSH α ψ := MultiModel.isPSH_of_antitone_of_isUnibranch
    (ψ := fun _ : ℕ => ψ) hP hCoeff hModel
    (fun _ => antitone_const) (fun _ => by simp) ⟨P.triv,(hModel 0).apply_triv_ne_bot⟩
  rw [← hα]
  exact (Variety.isPSH_iff_presentation d q p hp α φ).mpr hLimit

end SGPT.NAPotential.BJ.ExternalClassStability
