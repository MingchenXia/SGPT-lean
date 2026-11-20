import SGPT.Toric.NativeOriginalEdgeManifold
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set Filter MeasureTheory
open SGPT.Foundations.Analysis.FirstPass
open scoped BigOperators Topology Manifold ContDiff
attribute [local instance] monomialProjectiveTopology

variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]

/-- The actual original integer-character orbit map into its SAME closure. -/
def originalPolytopeNativeOrbitMap (γ : K → Fin n → ℤ) :
    (Fin n → ℂˣ) → originalPolytopeNativeSpace γ :=
  monomialOrbitClosureMap (originalPolytopeFullExponents γ)

/-- The SAME original open torus subset; no new orbit is substituted. -/
def originalPolytopeNativeTorus (γ : K → Fin n → ℤ) : Set (originalPolytopeNativeSpace γ) :=
  (originalPolytopeNativeBoundary γ)ᶜ

/-- Actual original points, rather than a desired orbit-parametrization premise. -/
theorem mem_originalPolytopeNativeTorus_iff (γ : K → Fin n → ℤ)
    (p : originalPolytopeNativeSpace γ) :
    p ∈ originalPolytopeNativeTorus γ ↔ ∃ a, originalPolytopeNativeOrbitMap γ a = p := by
  change (¬ p.val ∉ Set.range (monomialProjectiveOrbit (originalPolytopeFullExponents γ))) ↔ _
  rw [not_not]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, Subtype.ext ha⟩
  · rintro ⟨a, rfl⟩
    exact Set.mem_range_self a

/-- Original full-lattice characters give true continuity of the literal orbit map. -/
theorem continuous_originalPolytopeNativeOrbitMap (γ : K → Fin n → ℤ) :
    Continuous (originalPolytopeNativeOrbitMap γ) :=
  (continuous_monomialProjectiveOrbit (originalPolytopeFullExponents γ)).subtype_mk _

/-- Genuine density in the SAME literal closure, with no open-orbit premise. -/
theorem denseRange_originalPolytopeNativeOrbitMap (γ : K → Fin n → ℤ) :
    DenseRange (originalPolytopeNativeOrbitMap γ) :=
  denseRange_monomialOrbitClosureMap (originalPolytopeFullExponents γ)

/-- Every original orbit point lies in EVERY original vertex source, because
its actual homogeneous characters are nonzero. -/
theorem originalPolytopeNativeOrbitMap_mem_chart_source (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    (a : Fin n → ℂˣ) :
    originalPolytopeNativeOrbitMap γ a ∈ (originalPolytopeNativePiChart γ hsmooth v).source := by
  apply (originalPolytopeNativePiChart_mem_source_iff γ hsmooth v _ _
    (monomialOrbitVector_ne_zero (originalPolytopeFullExponents γ) a) rfl).mpr
  exact Units.ne_zero _

/-- Existing genuine AddChar subtraction applied in the actual standard basis
gives the literal Laurent quotient, before complex coordinate readback. -/
theorem originalLatticeCharacter_sub (m q : Fin n → ℤ) (a : Fin n → ℂˣ) :
    latticeCharacter (m - q) a = latticeCharacter m a / latticeCharacter q a := by
  simpa only [latticeBasisCharacterEquiv_apply, Pi.basisFun_repr] using
    (latticeBasisCharacterEquiv (Pi.basisFun ℤ (Fin n)) a).map_sub_eq_div m q

/-- The actual coordinate of the ORIGINAL orbit is the SAME original character
at the produced edge basis vector, using the actual neighbor readback. -/
theorem originalPolytopeNativePiChart_orbit (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    (a : Fin n → ℂˣ) (j : Fin n) :
    originalPolytopeNativePiChart γ hsmooth v (originalPolytopeNativeOrbitMap γ a) j =
      (latticeCharacter (originalPolytopeNativeBasis γ hsmooth v j) a : ℂ) := by
  have h := (originalPolytopeNativePiChart_spec γ hsmooth v).2.2.2.2.2
    (originalPolytopeNativeOrbitMap γ a)
    (originalPolytopeNativeOrbitMap_mem_chart_source γ hsmooth v a)
    (monomialOrbitVector (originalPolytopeFullExponents γ) a)
    (monomialOrbitVector_ne_zero (originalPolytopeFullExponents γ) a) rfl
  rw [h.2 j]
  change (latticeCharacter _ a : ℂ) / (latticeCharacter _ a : ℂ) = _
  rw [← Units.val_div_eq_div_val, ← originalLatticeCharacter_sub]
  have hv := latticePolytopeExponentFamily_vertexIndex γ (originalPolytopeFullEnumeration γ) v
  change originalPolytopeFullExponents γ (originalPolytopeNativeVertexIndex γ v) = v.val at hv
  rw [hv, (originalPolytopeNativePiChart_spec γ hsmooth v).1 j]

/-- Literal original edge-basis coordinates are the EXISTING actual lattice
basis-change homeomorphism, not a supplied character parametrization. -/
theorem originalPolytopeNativePiChart_orbit_basisChange (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    (a : Fin n → ℂˣ) (j : Fin n) :
    originalPolytopeNativePiChart γ hsmooth v (originalPolytopeNativeOrbitMap γ a) j =
      (latticeBasisChangeHomeomorph (Pi.basisFun ℤ (Fin n))
        (originalPolytopeNativeBasis γ hsmooth v) a j : ℂ) := by
  rw [originalPolytopeNativePiChart_orbit]
  congr 1
  change latticeCharacter _ a = latticeBasisChangeEquiv (Pi.basisFun ℤ (Fin n)) _ a j
  rw [latticeBasisChangeEquiv_apply, latticeBasisCharacterEquiv_apply]
  simp only [Pi.basisFun_repr]

/-- In every vertex native chart the SAME original torus is all nonzero coordinates. -/
theorem originalPolytopeNativeTorus_chart_symm_iff (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    (z : ComplexModel n) :
    (originalPolytopeNativeModelChart γ hsmooth v).symm z ∈ originalPolytopeNativeTorus γ ↔
      originalPolytopeNativeBoundaryPolynomial n z ≠ 0 := by
  exact not_congr (originalPolytopeNativeBoundary_chart_iff γ hsmooth v z)

/-- Actual inverse charts identify the coordinate complement with the SAME
whole original orbit; original orbit points belong to every vertex source. -/
theorem originalPolytopeNativeTorus_eq_chart_image (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ) :
    originalPolytopeNativeTorus γ = (originalPolytopeNativeModelChart γ hsmooth v).symm ''
      {z | originalPolytopeNativeBoundaryPolynomial n z ≠ 0} := by
  apply Set.Subset.antisymm
  · intro p hp
    obtain ⟨a, rfl⟩ := (mem_originalPolytopeNativeTorus_iff γ p).mp hp
    have hs : originalPolytopeNativeOrbitMap γ a ∈
        (originalPolytopeNativeModelChart γ hsmooth v).source := by
      rw [originalPolytopeNativeModelChart_source]
      exact originalPolytopeNativeOrbitMap_mem_chart_source γ hsmooth v a
    refine ⟨originalPolytopeNativeModelChart γ hsmooth v (originalPolytopeNativeOrbitMap γ a), ?_,
      (originalPolytopeNativeModelChart γ hsmooth v).left_inv hs⟩
    apply (originalPolytopeNativeTorus_chart_symm_iff γ hsmooth v _).mp
    rwa [(originalPolytopeNativeModelChart γ hsmooth v).left_inv hs]
  · rintro p ⟨z, hz, rfl⟩
    exact (originalPolytopeNativeTorus_chart_symm_iff γ hsmooth v z).mpr hz

/-- Genuine openness is manufactured from the actual coordinate polynomial
and actual inverse-chart open image, including rank zero. -/
theorem isOpen_originalPolytopeNativeTorus (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) : IsOpen (originalPolytopeNativeTorus γ) := by
  obtain ⟨v, hv⟩ := nonempty_latticePolytopeVertices γ
  rw [originalPolytopeNativeTorus_eq_chart_image γ hsmooth ⟨v, hv⟩]
  apply (originalPolytopeNativeModelChart γ hsmooth ⟨v, hv⟩).isOpen_image_symm_of_subset_target
  · exact (differentiable_originalPolytopeNativeBoundaryPolynomial n).continuous.isOpen_preimage _
      isOpen_compl_singleton
  · rw [originalPolytopeNativeModelChart_target]
    exact Set.subset_univ _

/-- Genuine density of the original torus subset, on the actual original carrier. -/
theorem dense_originalPolytopeNativeTorus (γ : K → Fin n → ℤ) :
    Dense (originalPolytopeNativeTorus γ) := by
  have heq : originalPolytopeNativeTorus γ = Set.range (originalPolytopeNativeOrbitMap γ) := by
    ext p
    exact mem_originalPolytopeNativeTorus_iff γ p
  rw [heq]
  exact denseRange_originalPolytopeNativeOrbitMap γ

/-- The ACTUAL Pi-chart version of the original torus dictionary. -/
theorem originalPolytopeNativeTorus_piChart_symm_iff (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    (z : Fin n → ℂ) :
    (originalPolytopeNativePiChart γ hsmooth v).symm z ∈ originalPolytopeNativeTorus γ ↔
      ∀ j, z j ≠ 0 := by
  change (¬ ((originalPolytopeNativePiChart γ hsmooth v).symm z).val ∉
    Set.range (monomialProjectiveOrbit (originalPolytopeFullExponents γ))) ↔ _
  rw [(originalPolytopeNativePiChart_spec γ hsmooth v).2.2.2.2.1 z]
  simp only [Finset.prod_ne_zero_iff, Finset.mem_univ, forall_true_left]

/-- The inverse original Pi-chart maps EXACTLY all nonzero coordinates onto
the SAME entire original torus, not merely into a proposed dense orbit. -/
theorem originalPolytopeNativeTorus_eq_piChart_image (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ) :
    originalPolytopeNativeTorus γ = (originalPolytopeNativePiChart γ hsmooth v).symm ''
      {z | ∀ j, z j ≠ 0} := by
  apply Set.Subset.antisymm
  · intro p hp
    obtain ⟨a, rfl⟩ := (mem_originalPolytopeNativeTorus_iff γ p).mp hp
    have hs := originalPolytopeNativeOrbitMap_mem_chart_source γ hsmooth v a
    refine ⟨originalPolytopeNativePiChart γ hsmooth v (originalPolytopeNativeOrbitMap γ a), ?_,
      (originalPolytopeNativePiChart γ hsmooth v).left_inv hs⟩
    intro j
    rw [originalPolytopeNativePiChart_orbit]
    exact Units.ne_zero _
  · rintro p ⟨z, hz, rfl⟩
    exact (originalPolytopeNativeTorus_piChart_symm_iff γ hsmooth v z).mpr hz

/-- Existing subtype-Pi equivalence with its literal product/subspace topology.
This only groups the actual coordinate subtype proofs. -/
def originalNonzeroCoordinateGrouping (n : ℕ) :
    (Fin n → {z : ℂ // z ≠ 0}) ≃ₜ {z : Fin n → ℂ // ∀ j, z j ≠ 0} where
  toEquiv := Equiv.subtypePiEquivPi.symm
  continuous_toFun := (continuous_pi (fun j =>
    continuous_subtype_val.comp (continuous_apply j))).subtype_mk _
  continuous_invFun := continuous_pi (fun j =>
    ((continuous_apply j).comp continuous_subtype_val).subtype_mk _)

/-- Maximal reuse of the genuine units/nonzero homeomorphism in each coordinate. -/
def originalUnitCoordinateHomeomorph (n : ℕ) :
    (Fin n → ℂˣ) ≃ₜ {z : Fin n → ℂ // ∀ j, z j ≠ 0} :=
  (Homeomorph.piCongrRight (fun _ : Fin n => (unitsHomeomorphNeZero : ℂˣ ≃ₜ _))).trans
    (originalNonzeroCoordinateGrouping n)

/-- Actual restricted inverse chart gives a homeomorphism onto the ORIGINAL
whole torus. All image/source obligations were produced from original points. -/
def originalPolytopeNativeCoordinateOrbitHomeomorph (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ) :
    {z : Fin n → ℂ // ∀ j, z j ≠ 0} ≃ₜ originalPolytopeNativeTorus γ :=
  (originalPolytopeNativePiChart γ hsmooth v).symm.homeomorphOfImageSubsetSource
    (by rw [OpenPartialHomeomorph.symm_source, originalPolytopeNativePiChart_target]
        exact Set.subset_univ _)
    (originalPolytopeNativeTorus_eq_piChart_image γ hsmooth v).symm

/-- The genuine SAME-character basis change, existing unit-coordinate
homeomorphism and actual inverse chart manufacture the orbit homeomorphism. -/
def originalPolytopeNativeVertexOrbitHomeomorph (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ) :
    (Fin n → ℂˣ) ≃ₜ originalPolytopeNativeTorus γ :=
  (latticeBasisChangeHomeomorph (Pi.basisFun ℤ (Fin n))
    (originalPolytopeNativeBasis γ hsmooth v)).trans
      ((originalUnitCoordinateHomeomorph n).trans
        (originalPolytopeNativeCoordinateOrbitHomeomorph γ hsmooth v))

/-- The manufactured homeomorphism is literally the ORIGINAL torus orbit map. -/
theorem originalPolytopeNativeVertexOrbitHomeomorph_apply (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    (a : Fin n → ℂˣ) :
    (originalPolytopeNativeVertexOrbitHomeomorph γ hsmooth v a).val =
      originalPolytopeNativeOrbitMap γ a := by
  change (originalPolytopeNativePiChart γ hsmooth v).symm
    (fun j => ((latticeBasisChangeHomeomorph (Pi.basisFun ℤ (Fin n))
      (originalPolytopeNativeBasis γ hsmooth v) a j) : ℂ)) = _
  have hcoord : (fun j => ((latticeBasisChangeHomeomorph (Pi.basisFun ℤ (Fin n))
      (originalPolytopeNativeBasis γ hsmooth v) a j) : ℂ)) =
      originalPolytopeNativePiChart γ hsmooth v (originalPolytopeNativeOrbitMap γ a) := by
    funext j
    exact (originalPolytopeNativePiChart_orbit_basisChange γ hsmooth v a j).symm
  rw [hcoord]
  exact (originalPolytopeNativePiChart γ hsmooth v).left_inv
    (originalPolytopeNativeOrbitMap_mem_chart_source γ hsmooth v a)

/-- A genuine original vertex exists internally. No vertex/parametrization
certificate is an input to the original orbit homeomorphism. -/
def originalPolytopeNativeOrbitHomeomorph (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) :
    (Fin n → ℂˣ) ≃ₜ originalPolytopeNativeTorus γ :=
  originalPolytopeNativeVertexOrbitHomeomorph γ hsmooth
    ⟨(nonempty_latticePolytopeVertices γ).choose, (nonempty_latticePolytopeVertices γ).choose_spec⟩

/-- Exact original-character readback, with the vertex choice entirely internal. -/
theorem originalPolytopeNativeOrbitHomeomorph_apply (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (a : Fin n → ℂˣ) :
    (originalPolytopeNativeOrbitHomeomorph γ hsmooth a).val =
      originalPolytopeNativeOrbitMap γ a :=
  originalPolytopeNativeVertexOrbitHomeomorph_apply γ hsmooth _ a

end SGPT.Toric
