import SGPT.Projective.SmoothComplexPointDomain
import SGPT.Projective.MinimalPrimeLocalDomain
import SGPT.Foundations.Schemes.NativeFanoAlgebraicFiniteness
import Mathlib.AlgebraicGeometry.IdealSheaf.IrreducibleComponent

/-! ALL actual original smooth projective scheme components are disjoint,
clopen, integral and genuinely smooth/projective, without component premises.
Blueprint: smooth-scheme-clopen-components.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.AlgebraicCurveDegree
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set TopologicalSpace
variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f]

include f n in
/-- ALL original smooth-scheme irreducible components are disjoint, from actual local domains. -/
theorem smoothScheme_components_pairwiseDisjoint : (irreducibleComponents X).Pairwise Disjoint := by
  intro C hC D hD hCD
  apply Set.disjoint_left.mpr
  intro x hxC hxD
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, _⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ x) isOpen_univ
  let z := hU.primeIdealOf (⟨x, hxU⟩ : U)
  have hz : hU.fromSpec z = x := hU.fromSpec_primeIdealOf _
  have hCrange : (C ∩ Set.range hU.fromSpec).Nonempty := ⟨x, hxC, z, hz⟩
  have hDrange : (D ∩ Set.range hU.fromSpec).Nonempty := ⟨x, hxD, z, hz⟩
  have hCpre := preimage_mem_irreducibleComponents hC hU.fromSpec.isOpenEmbedding hCrange
  have hDpre := preimage_mem_irreducibleComponents hD hU.fromSpec.isOpenEmbedding hDrange
  have hlocal := primeSpectrum_irreducibleComponents_pairwiseDisjoint
    (fun m hm => smoothAffineMaximalLocalization_isDomain f n hU m hm)
  have hzC : z ∈ hU.fromSpec ⁻¹' C := by change hU.fromSpec z ∈ C; rwa [hz]
  have hzD : z ∈ hU.fromSpec ⁻¹' D := by change hU.fromSpec z ∈ D; rwa [hz]
  have hpre : hU.fromSpec ⁻¹' C = hU.fromSpec ⁻¹' D := by
    by_contra hne
    exact Set.disjoint_left.mp (hlocal hCpre hDpre hne) hzC hzD
  have hclC := closure_image_preimage_of_isPreirreducible hU.fromSpec
    hU.fromSpec.isOpenEmbedding.isOpenMap C ⟨z, hzC⟩ hC.1.2
    (isClosed_of_mem_irreducibleComponents C hC)
  have hclD := closure_image_preimage_of_isPreirreducible hU.fromSpec
    hU.fromSpec.isOpenEmbedding.isOpenMap D ⟨z, hzD⟩ hD.1.2
    (isClosed_of_mem_irreducibleComponents D hD)
  exact hCD (hclC.symm.trans ((congrArg (fun S : Set (PrimeSpectrum Γ(X, U)) =>
    closure (hU.fromSpec '' S)) hpre).trans hclD))

include f n in
/-- Every actual original projective smooth component is genuinely open and closed. -/
theorem smoothProjective_component_isClopen (E : ClosedProjectiveEmbedding f)
    (C : Set X) (hC : C ∈ irreducibleComponents X) : IsClopen C := by
  let := E.isNoetherian
  have hfin : (irreducibleComponents X).Finite := NoetherianSpace.finite_irreducibleComponents
  have hclosed := isClosed_of_mem_irreducibleComponents C hC
  have hcompl : C = (⋃₀ (irreducibleComponents X \ {C}))ᶜ := by
    ext x
    constructor
    · intro hx hother
      obtain ⟨D, ⟨hD, hDC⟩, hxD⟩ := hother
      have hne : C ≠ D := fun h => hDC (Set.mem_singleton_iff.mpr h.symm)
      exact Set.disjoint_left.mp (smoothScheme_components_pairwiseDisjoint f n hC hD hne) hx hxD
    · intro hx
      have hxall : x ∈ ⋃₀ irreducibleComponents X := by rw [sUnion_irreducibleComponents]; trivial
      obtain ⟨D, hD, hxD⟩ := hxall
      by_cases hDC : D = C
      · exact hDC ▸ hxD
      · exact False.elim (hx ⟨D, ⟨hD, by simpa only [Set.mem_singleton_iff] using hDC⟩, hxD⟩)
  have hotherClosed : IsClosed (⋃₀ (irreducibleComponents X \ {C})) := by
    rw [Set.sUnion_eq_biUnion]
    exact hfin.sdiff.isClosed_biUnion (fun D hD => isClosed_of_mem_irreducibleComponents D hD.1)
  refine ⟨hclosed, ?_⟩
  rw [hcompl]
  exact hotherClosed.isOpen_compl

/-- SAME actual original component as its actual open scheme. -/
def smoothProjectiveComponentOpen (E : ClosedProjectiveEmbedding f)
    (C : Set X) (hC : C ∈ irreducibleComponents X) : X.Opens :=
  ⟨C, (smoothProjective_component_isClopen f n E C hC).2⟩

/-- Actual original component is integral, proved from entire reducedness and SAME irreducibility. -/
theorem smoothProjective_component_isIntegral (E : ClosedProjectiveEmbedding f)
    (C : Set X) (hC : C ∈ irreducibleComponents X) :
    IsIntegral (smoothProjectiveComponentOpen f n E C hC) := by
  let := smoothScheme_isReduced f n
  let : IrreducibleSpace (smoothProjectiveComponentOpen f n E C hC) :=
    isIrreducible_iff_irreducibleSpace.mp hC.1
  exact isIntegral_of_irreducibleSpace_of_isReduced _

/-- SAME actual original component inclusion is also a genuine closed immersion. -/
theorem smoothProjective_component_closedImmersion (E : ClosedProjectiveEmbedding f)
    (C : Set X) (hC : C ∈ irreducibleComponents X) :
    IsClosedImmersion (smoothProjectiveComponentOpen f n E C hC).ι := by
  apply IsClosedImmersion.of_isPreimmersion
  rw [Scheme.Opens.range_ι]
  change IsClosed C
  exact (smoothProjective_component_isClopen f n E C hC).1

/-- ACTUAL SAME component embedding retains ORIGINAL ambient projective space and structural map. -/
def smoothProjective_componentEmbedding (E : ClosedProjectiveEmbedding f)
    (C : Set X) (hC : C ∈ irreducibleComponents X) :
    ClosedProjectiveEmbedding ((smoothProjectiveComponentOpen f n E C hC).ι ≫ f) := by
  let := smoothProjective_component_closedImmersion f n E C hC
  exact {
    ambientDimension := E.ambientDimension
    map := (smoothProjectiveComponentOpen f n E C hC).ι ≫ E.map
    closedImmersion := inferInstance
    over_base := by rw [Category.assoc, E.over_base] }

/-- SAME literal original component structural morphism retains SAME original smooth dimension. -/
theorem smoothProjective_component_smoothDimension (E : ClosedProjectiveEmbedding f)
    (C : Set X) (hC : C ∈ irreducibleComponents X) :
    SmoothOfRelativeDimension n ((smoothProjectiveComponentOpen f n E C hC).ι ≫ f) := by
  simpa only [zero_add] using
    (inferInstance : SmoothOfRelativeDimension (0 + n) ((smoothProjectiveComponentOpen f n E C hC).ι ≫ f))

omit [IsSeparated f] [QuasiCompact f] in
/-- The ACTUAL whole original component index is finite, from original projectivity. -/
theorem smoothProjective_componentIndex_finite (E : ClosedProjectiveEmbedding f) :
    Finite ↥(irreducibleComponents X) := by
  let := E.isNoetherian
  exact NoetherianSpace.finite_irreducibleComponents.to_subtype

/-- ALL actual original component open schemes cover EVERY original point. -/
theorem smoothProjective_componentOpens_cover (E : ClosedProjectiveEmbedding f) (x : X) :
    ∃ C : ↥(irreducibleComponents X), x ∈ smoothProjectiveComponentOpen f n E C.val C.property := by
  refine ⟨⟨_root_.irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩, ?_⟩
  change x ∈ _root_.irreducibleComponent x
  exact mem_irreducibleComponent

/-- The actual original empty scheme has the genuinely empty original component index. -/
theorem irreducibleComponentIndex_isEmpty [IsEmpty X] : IsEmpty ↥(irreducibleComponents X) := by
  constructor
  intro C
  obtain ⟨x, _⟩ := C.property.1.nonempty
  exact isEmptyElim x

end SGPT.Projective.NumEq.AlgebraicCurveDegree
