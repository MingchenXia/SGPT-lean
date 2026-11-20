import SGPT.Checks.Literature.BJDivisorial.OriginalDivisorialComparison
import Mathlib.Topology.Constructions
import Mathlib.Topology.Separation.Hausdorff

/-! # The actual source PSH space and its divisorial pointwise topology

Source SGPT76fde3d1, chapter_NApotential.tex940--944,966--968.
The space consists of the unchanged original rational GF/net predicates on
ALL original Berkovich points. Its topology is induced by restriction to
the actual augmented positive-rational sourceDivisorialSet. Only supporting
topology and boundedness facts are proved; the envelope conjecture stays open.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open AlgebraicGeometry Filter Topology TopologicalSpace
open scoped Classical Topology

universe u v
namespace SGPT.NAPotential.BJ.OriginalDivisorialTopology
open SGPT.NAPotential.Berkovich SGPT.NAPotential.BJ.NativePicard
open SGPT.NAPotential.BJ.Printed

variable {X : Scheme.{0}} [IsIntegral X]
  (p : X ⟶ Spec (.of ℂ)) [IsProjective p] (L : RationalPicardSpace X)

/-- The actual original PSH space, retaining its ALL-point functions and
unchanged original rational GF and intrinsic numerical-topology predicate. -/
def Space : Type := {φ : BerkovichPoint p → EReal // IsModuleTopologyPSH.{u} p L φ}

/-- Restriction to the actual augmented source divisorial points. -/
def restriction (φ : Space.{u} p L) : sourceDivisorialSet p → EReal :=
  fun v => φ.1 v

/-- Exactly the book's topology of pointwise convergence on X^Div. -/
instance instTopologicalSpace : TopologicalSpace (Space.{u} p L) :=
  TopologicalSpace.induced (restriction p L) inferInstance

/-- No topology correspondence is an input: this topology is literally
induced by the actual source restriction map. -/
theorem restriction_isInducing : Topology.IsInducing (restriction.{u} p L) := ⟨rfl⟩

/-- Convergence IN the actual source PSH space is precisely convergence at
every actual source divisorial point, for arbitrary filters and index types. -/
theorem tendsto_iff_divisorial {ι : Type v} (F : ι → Space.{u} p L)
    (l : Filter ι) (φ : Space.{u} p L) :
    Tendsto F l (𝓝 φ) ↔ ∀ v ∈ sourceDivisorialSet p,
      Tendsto (fun i => (F i).1 v) l (𝓝 (φ.1 v)) := by
  rw [(restriction_isInducing p L).tendsto_nhds_iff, tendsto_pi_nhds]
  exact ⟨fun h v hv => h ⟨v,hv⟩, fun h v => h v v.2⟩

/-- Genuine source comparison DERIVES injectivity of the actual restriction
map. It is not assumed as part of the topology or conjecture statement. -/
theorem restriction_injective : Function.Injective (restriction.{u} p L) := by
  intro φ ψ h
  apply Subtype.ext
  apply le_antisymm
  · apply SGPT.NAPotential.BJ.Divisorial.original_le_of_sourceDivisorial_le p φ.2
      (ψ.2.upperSemicontinuous p)
    intro v hv
    exact (congrFun h ⟨v,hv⟩).le
  · apply SGPT.NAPotential.BJ.Divisorial.original_le_of_sourceDivisorial_le p ψ.2
      (φ.2.upperSemicontinuous p)
    intro v hv
    exact (congrFun h ⟨v,hv⟩).ge

/-- The original PSH space with its actual divisorial topology is Hausdorff,
by the proved comparison and the actual EReal product topology. -/
instance instT2Space : T2Space (Space.{u} p L) :=
  (show Topology.IsEmbedding (restriction.{u} p L) from
    ⟨restriction_isInducing p L, restriction_injective p L⟩).t2Space

/-- A finite real upper bound for the entire family at EVERY original point.
Using BddAbove in EReal here would be vacuous because EReal has a top. -/
def UniformlyBoundedAbove {ι : Type v} (F : ι → Space.{u} p L) : Prop :=
  ∃ C : ℝ, ∀ i v, (F i).1 v ≤ (C : EReal)

/-- The unrestricted pointwise finite bound formulation. -/
def PointwiseBoundedAbove {ι : Type v} (F : ι → Space.{u} p L) : Prop :=
  ∀ v, ∃ C : ℝ, ∀ i, (F i).1 v ≤ (C : EReal)

/-- A finite bound at the ACTUAL original trivial point suffices for a
uniform finite bound, by the actual original PSH trivial-point estimate. -/
theorem uniformlyBoundedAbove_iff_trivial {ι : Type v} (F : ι → Space.{u} p L) :
    UniformlyBoundedAbove p L F ↔
      ∃ C : ℝ, ∀ i, (F i).1 (BerkovichPoint.trivial p) ≤ (C : EReal) := by
  constructor
  · rintro ⟨C,hC⟩
    exact ⟨C, fun i => hC i (BerkovichPoint.trivial p)⟩
  · rintro ⟨C,hC⟩
    exact ⟨C, fun i v => ((F i).2.le_trivial p v).trans (hC i)⟩

/-- Pointwise finite boundedness and uniform finite boundedness have
EXACTLY the same scope for actual original PSH families; no narrowing. -/
theorem pointwiseBoundedAbove_iff_uniform {ι : Type v} (F : ι → Space.{u} p L) :
    PointwiseBoundedAbove p L F ↔ UniformlyBoundedAbove p L F := by
  constructor
  · intro h
    exact (uniformlyBoundedAbove_iff_trivial p L F).mpr (h (BerkovichPoint.trivial p))
  · rintro ⟨C,hC⟩ v
    exact ⟨C, fun i => hC i v⟩

end SGPT.NAPotential.BJ.OriginalDivisorialTopology
