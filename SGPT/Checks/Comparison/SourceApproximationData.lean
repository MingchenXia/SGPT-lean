import SGPT.Checks.Comparison.BJCanonicalModuleTopology
import SGPT.Foundations.Envelope.AlgGeom.SchemeLineAmpleness

/-! Literal original approximation predicates, independent of promotion proofs.
These definitions alone assert no approximation theorem. -/
set_option autoImplicit false
noncomputable section
universe u
namespace SGPT.NAPotential.BJ.SourceApproximationData
open AlgebraicGeometry CategoryTheory Filter Topology SGPT.Foundations.Schemes
open SGPT.Foundations.Envelope Scheme.Modules
open SGPT.NAPotential.Berkovich
open SGPT.NAPotential.BJ.NativePicard SGPT.NAPotential.BJ.Printed
variable {X : Scheme.{0}} (p : X ⟶ Spec (.of ℂ)) [IsProjective p]

/-- Same original rational GF sequences and exact rational Picard classes. -/
def ApproximatingSequence {S : X.Modules} (hS : IsInvertible S) (L : RationalPicardSpace X)
    (φ : BerkovichPoint p → EReal) : Prop :=
  ∃ (ε : ℕ → ℚ) (ψ : ℕ → BerkovichPoint p → EReal),
    (∀ i, 0 < ε i) ∧ StrictAnti ε ∧ Tendsto (fun i => (ε i : ℝ)) atTop (𝓝 0) ∧
    (∀ i, IsRationalGF p (L + ε i • rationalPicardClass (atlasOfInvertible hS)) (ψ i)) ∧
    (∀ v, Antitone fun i => ψ i v) ∧
    ∀ v, Tendsto (fun i => ψ i v) atTop (𝓝 (φ v))

/-- Literal original approximation assertion; no proof is inserted as data. -/
def Statement : Prop :=
  ∀ (S : X.Modules) (hS : SchemeLineAmpleness.IsAmple p S) (L : RationalPicardSpace X)
    (φ : BerkovichPoint p → EReal), IsModuleTopologyPSH.{u} p L φ →
      ApproximatingSequence p hS.isInvertible L φ
end SGPT.NAPotential.BJ.SourceApproximationData
