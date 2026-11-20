import SGPT.Checks.Literature.BJDivisorial.OriginalDivisorialPSHTopology
import SGPT.Foundations.PublishedEnvelope.Source.Unibranch

/-! # The OPEN original envelope conjecture: exact proposition only

Source SGPT76fde3d1, chapter_NApotential.tex966--968, conj:env.
This defines the proposition on the actual original PSH space and its
actual divisorial pointwise topology. It does NOT prove or assume the
conjecture. The declaration convention matches
SGPT.OpenQuestions.naturalKahlerTraceExtensionStatement.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open AlgebraicGeometry Filter Topology
open scoped Classical Topology

universe u v
namespace SGPT.OpenQuestions
open SGPT.NAPotential.Berkovich SGPT.NAPotential.BJ.NativePicard
open SGPT.NAPotential.BJ.OriginalDivisorialTopology

variable {X : Scheme.{0}} [IsIntegral X]
  (p : X ⟶ Spec (.of ℂ)) [IsProjective p]

/-- The exact OPEN statement of source conj:env for an arbitrary original
rational target L on an actual unibranch projective variety. Every arbitrary
nonempty directed increasing net with a finite upper bound has an actual
PSH metric as a limit IN its actual divisorial pointwise topology.
A proposition statement only: no proof of the conjecture is asserted. -/
def originalEnvelopeIncreasingNetConvergenceStatement.{pshUniverse,indexUniverse}
    (_hX : SGPT.Foundations.PublishedEnvelope.Variety.IsUnibranch X) (L : RationalPicardSpace X) : Prop :=
  ∀ (ι : Type indexUniverse) [Preorder ι] [Nonempty ι] [IsDirected ι (· ≤ ·)]
    (F : ι → Space.{pshUniverse} p L),
    Monotone (fun i => (F i).1) → UniformlyBoundedAbove p L F →
      ∃ φ : Space.{pshUniverse} p L, Tendsto F atTop (𝓝 φ)

/-- A supporting exact topology dictionary for the OPEN proposition, not a
proof of it: its limit is still an actual original PSH metric, and exactly
the actual source divisorial values converge. -/
theorem originalEnvelopeStatement_iff_divisorial
    (hX : SGPT.Foundations.PublishedEnvelope.Variety.IsUnibranch X) (L : RationalPicardSpace X) :
    originalEnvelopeIncreasingNetConvergenceStatement.{u,v} p hX L ↔
      ∀ (ι : Type v) [Preorder ι] [Nonempty ι] [IsDirected ι (· ≤ ·)]
        (F : ι → Space.{u} p L),
        Monotone (fun i => (F i).1) → UniformlyBoundedAbove p L F →
          ∃ φ : Space.{u} p L, ∀ v ∈ sourceDivisorialSet p,
            Tendsto (fun i => (F i).1 v) atTop (𝓝 (φ.1 v)) := by
  constructor
  · intro h ι _ _ _ F hF hB
    obtain ⟨φ,hφ⟩ := h ι F hF hB
    exact ⟨φ,(tendsto_iff_divisorial p L F atTop φ).mp hφ⟩
  · intro h ι _ _ _ F hF hB
    obtain ⟨φ,hφ⟩ := h ι F hF hB
    exact ⟨φ,(tendsto_iff_divisorial p L F atTop φ).mpr hφ⟩

end SGPT.OpenQuestions
