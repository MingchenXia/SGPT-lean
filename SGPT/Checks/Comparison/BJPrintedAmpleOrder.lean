import SGPT.Checks.Comparison.BJNativeAmpleOrderGauge

/-! Direct consumer: actual original rational-GF approximants and their ALL
original-point infimum are retained while genuine ample-order class
convergence is now produced internally, without global finite dimension. -/
set_option autoImplicit false
noncomputable section
universe u
namespace SGPT.NAPotential.BJ.Printed
open AlgebraicGeometry CategoryTheory Filter Topology
open SGPT.NAPotential.Berkovich SGPT.NAPotential.BJ.NativePicard
open SGPT.Foundations.Envelope
variable {X : Scheme.{0}} (p : X ⟶ Spec (.of ℂ)) [IsProjective p] [IsIntegral X]

/-- Original rational sections/classes/points all retained, with actual EP
ample-order convergence internally produced from the explicit module topology.
This does not identify the stronger predicate with usual source convergence. -/
theorem IsModuleTopologyPSH.exists_original_ampleOrder_net
    {L : RationalPicardSpace X} {φ : BerkovichPoint p → EReal}
    (h : IsModuleTopologyPSH.{u} p L φ) :
    (∃ v,φ v≠⊥) ∧ ∃ D : DecreasingGFNet.{u} p,
      (∀ i,IsRationalGF p (D.term i).picardClass ((D.term i).eval p)) ∧
      Variety.AmpleTendsto p (fun i => (D.term i).numericalClass p) atTop
        (NativePicard.numericalClass p L) ∧
      ∀ v,φ v=⨅ i : D.I,(D.term i).eval p v := by
  obtain ⟨hne,D,hclass,hlim⟩ := h
  refine ⟨hne,D,fun i => isRationalGF_package p (D.term i),
    ampleTendsto_of_moduleTopology p hclass,?_⟩
  intro v
  exact congrFun (D.eq_limit_of_tendsto p hlim) v

end SGPT.NAPotential.BJ.Printed
