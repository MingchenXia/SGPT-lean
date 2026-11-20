import SGPT.Toric.LatticeCharacterCoordinates
import SGPT.Toric.NativeProjectivePointComparison
import SGPT.Foundations.Schemes.ProjectiveAnalyticRatioCharts

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric

open Set SGPT.Convex
open scoped BigOperators Topology
attribute [local instance] monomialProjectiveTopology

variable {n : ℕ} {M I : Type*} [AddCommGroup M]

/-- The actual integral vertex differences, read in an original integer basis.
Nonnegativity is an explicit raw combinatorial hypothesis, never geometry data. -/
def monomialVertexExponent (b : Module.Basis (Fin n) ℤ M) (β : I → M) (v i : I)
    (j : Fin n) : ℕ := (b.repr (β i - β v) j).toNat

/-- Literal polynomial homogeneous coordinates at the chosen original lattice vertex. -/
def monomialVertexVector (b : Module.Basis (Fin n) ℤ M) (β : I → M) (v : I)
    (z : Fin n → ℂ) : I → ℂ := fun i => ∏ j, z j ^ monomialVertexExponent b β v i j

/-- The chosen vertex coordinate is identically one, including the empty product. -/
theorem monomialVertexVector_vertex (b : Module.Basis (Fin n) ℤ M) (β : I → M)
    (v : I) (z : Fin n → ℂ) : monomialVertexVector b β v z v = 1 := by
  simp [monomialVertexVector, monomialVertexExponent]

/-- Original basis neighbors yield literal complex coordinate readback. -/
theorem monomialVertexVector_neighbor (b : Module.Basis (Fin n) ℤ M) (β : I → M)
    (v : I) (ν : Fin n → I) (hν : ∀ j, β (ν j) - β v = b j)
    (z : Fin n → ℂ) (j : Fin n) : monomialVertexVector b β v z (ν j) = z j := by
  classical
  simp only [monomialVertexVector, monomialVertexExponent, hν, Module.Basis.repr_self,
    Finsupp.single_apply]
  rw [Finset.prod_eq_single j]
  · simp
  · intro k _ hkj
    simp [Ne.symm hkj]
  · simp

/-- No basis neighbor equals the original vertex; this is derived from lattice
basis data before deleting the affine denominator coordinate. -/
theorem monomialVertexNeighbor_ne_vertex (b : Module.Basis (Fin n) ℤ M) (β : I → M)
    (v : I) (ν : Fin n → I) (hν : ∀ j, β (ν j) - β v = b j) (j : Fin n) :
    ν j ≠ v := by
  intro h
  have hz : b j = 0 := by simpa [h] using (hν j).symm
  exact b.ne_zero j hz

/-- Distinct original basis directions manufacture distinct exponent indices. -/
theorem monomialVertexNeighbor_injective (b : Module.Basis (Fin n) ℤ M) (β : I → M)
    (v : I) (ν : Fin n → I) (hν : ∀ j, β (ν j) - β v = b j) :
    Function.Injective ν := by
  intro j k h
  apply b.injective
  rw [← hν j, ← hν k, h]

/-- Genuine nonvanishing is proved before forming the original quotient point. -/
theorem monomialVertexVector_ne_zero (b : Module.Basis (Fin n) ℤ M) (β : I → M)
    (v : I) (z : Fin n → ℂ) : monomialVertexVector b β v z ≠ 0 := by
  intro h
  have he := congrFun h v
  rw [monomialVertexVector_vertex] at he
  exact one_ne_zero he

/-- The actual normalized polynomial projective point, on the whole complex target. -/
def monomialVertexPoint (b : Module.Basis (Fin n) ℤ M) (β : I → M) (v : I)
    (z : Fin n → ℂ) : Projectivization ℂ (I → ℂ) :=
  Projectivization.mk ℂ (monomialVertexVector b β v z) (monomialVertexVector_ne_zero b β v z)

/-- Actual finite polynomial coordinates are continuous on all of C^n. -/
theorem continuous_monomialVertexVector (b : Module.Basis (Fin n) ℤ M) (β : I → M) (v : I) :
    Continuous (monomialVertexVector b β v) := by
  exact continuous_pi (fun i => continuous_finsetProd _
    (fun j _ => (continuous_apply j).pow (monomialVertexExponent b β v i j)))

/-- Genuine normalized polynomial-point continuity in the ORIGINAL quotient topology. -/
theorem continuous_monomialVertexPoint (b : Module.Basis (Fin n) ℤ M) (β : I → M) (v : I) :
    Continuous (monomialVertexPoint b β v) := by
  exact continuous_quotient_mk'.comp
    ((continuous_monomialVertexVector b β v).subtype_mk (monomialVertexVector_ne_zero b β v))

/-- Nonnegative ORIGINAL lattice differences give the very same character quotient,
with no torus extension or desired coordinate identity assumed. -/
theorem monomialVertexVector_torus (b : Module.Basis (Fin n) ℤ M) (β : I → M) (v : I)
    (hpos : ∀ i j, 0 ≤ b.repr (β i - β v) j) (a : Fin n → ℂˣ) (i : I) :
    monomialVertexVector b β v (fun j => (a j : ℂ)) i =
      ((latticeBasisCharacterEquiv b a (β i) : ℂ) /
        (latticeBasisCharacterEquiv b a (β v) : ℂ)) := by
  rw [← Units.val_div_eq_div_val, ← AddChar.map_sub_eq_div,
    latticeBasisCharacterEquiv_apply]
  simp only [monomialVertexVector, monomialVertexExponent, latticeCharacter,
    MonoidHom.coe_mk, OneHom.coe_mk, Units.coe_prod, Units.val_zpow_eq_zpow_val]
  apply Finset.prod_congr rfl
  intro j _
  rw [← zpow_natCast, Int.toNat_of_nonneg (hpos i j)]

/-- The literal polynomial projective point is the SAME original torus orbit point. -/
theorem monomialVertexPoint_torus [Nonempty I] (b : Module.Basis (Fin n) ℤ M)
    (β : I → M) (v : I) (hpos : ∀ i j, 0 ≤ b.repr (β i - β v) j)
    (a : Fin n → ℂˣ) :
    monomialVertexPoint b β v (fun j => (a j : ℂ)) =
      monomialProjectiveOrbit (fun i j => b.repr (β i) j) a := by
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
  refine ⟨(latticeBasisCharacterEquiv b a (β v) : ℂ)⁻¹, ?_⟩
  funext i
  change (latticeBasisCharacterEquiv b a (β v) : ℂ)⁻¹ *
    (latticeCharacter (fun j => b.repr (β i) j) a : ℂ) = _
  rw [monomialVertexVector_torus b β v hpos,
    ← latticeBasisCharacterEquiv_apply b a (β i)]
  exact (div_eq_inv_mul _ _).symm

/-- Existing retract topology manufactures a genuine closed polynomial embedding
from the ACTUAL neighboring basis readbacks. -/
theorem isClosedEmbedding_monomialVertexVector (b : Module.Basis (Fin n) ℤ M)
    (β : I → M) (v : I) (ν : Fin n → I) (hν : ∀ j, β (ν j) - β v = b j) :
    Topology.IsClosedEmbedding (monomialVertexVector b β v) := by
  have hleft : Function.LeftInverse (fun r : I → ℂ => fun j => r (ν j))
      (monomialVertexVector b β v) := by
    intro z
    funext j
    exact monomialVertexVector_neighbor b β v ν hν z j
  exact hleft.isClosedEmbedding (continuous_pi (fun j => continuous_apply (ν j)))
    (continuous_monomialVertexVector b β v)

variable {d : ℕ}

/-- Literal polynomial coordinates in the EXISTING native ambient v-ratio chart. -/
def monomialVertexRatioVector (b : Module.Basis (Fin n) ℤ M)
    (β : Fin (d + 1) → M) (v : Fin (d + 1)) (z : Fin n → ℂ) : Fin d → ℂ :=
  fun k => monomialVertexVector b β v z (v.succAbove k)

/-- Actual affine deletion and insertion recover the SAME normalized homogeneous vector. -/
theorem insertNth_monomialVertexRatioVector (b : Module.Basis (Fin n) ℤ M)
    (β : Fin (d + 1) → M) (v : Fin (d + 1)) (z : Fin n → ℂ) :
    Fin.insertNth v 1 (monomialVertexRatioVector b β v z) = monomialVertexVector b β v z := by
  exact Fin.insertNth_eq_iff.mpr ⟨(monomialVertexVector_vertex b β v z).symm, rfl⟩

/-- Literal monomial affine coordinates are continuous by the existing product topology. -/
theorem continuous_monomialVertexRatioVector (b : Module.Basis (Fin n) ℤ M)
    (β : Fin (d + 1) → M) (v : Fin (d + 1)) :
    Continuous (monomialVertexRatioVector b β v) := by
  exact continuous_pi (fun k => (continuous_apply (v.succAbove k)).comp
    (continuous_monomialVertexVector b β v))

/-- The actual affine polynomial graph is closed embedded. Its inverse is
manufactured from the ORIGINAL neighboring exponent ratios. -/
theorem isClosedEmbedding_monomialVertexRatioVector (b : Module.Basis (Fin n) ℤ M)
    (β : Fin (d + 1) → M) (v : Fin (d + 1)) (ν : Fin n → Fin (d + 1))
    (hν : ∀ j, β (ν j) - β v = b j) :
    Topology.IsClosedEmbedding (monomialVertexRatioVector b β v) := by
  have hins : Continuous (fun r : Fin d → ℂ => (Fin.insertNth v (1 : ℂ) r : Fin (d + 1) → ℂ)) := by
    apply continuous_pi
    intro i
    refine Fin.succAboveCases v ?_ (fun k => ?_) i
    · simpa only [Fin.insertNth_apply_same] using (continuous_const : Continuous (fun _ : Fin d → ℂ => (1 : ℂ)))
    · simpa only [Fin.insertNth_apply_succAbove] using (continuous_apply k : Continuous (fun r : Fin d → ℂ => r k))
  have hleft : Function.LeftInverse
      (fun r : Fin d → ℂ => fun j => (Fin.insertNth v (1 : ℂ) r : Fin (d + 1) → ℂ) (ν j))
      (monomialVertexRatioVector b β v) := by
    intro z
    funext j
    change (Fin.insertNth v (1 : ℂ) (monomialVertexRatioVector b β v z) :
      Fin (d + 1) → ℂ) (ν j) = z j
    rw [insertNth_monomialVertexRatioVector]
    exact monomialVertexVector_neighbor b β v ν hν z j
  exact hleft.isClosedEmbedding
    (continuous_pi (fun j => (continuous_apply (ν j)).comp hins))
    (continuous_monomialVertexRatioVector b β v)

open SGPT.Foundations.Schemes

@[instance_reducible] private def vertexNativePointTopology (d : ℕ) :
    TopologicalSpace (SchemeComplexPoint (polynomialProjStructureMap ℂ d)) :=
  schemeAnalyticPointTopology (polynomialProjStructureMap ℂ d)
attribute [local instance] vertexNativePointTopology

/-- The EXISTING genuine native ratio open embedding, transported through the
actual original/native point homeomorphism, in the ORIGINAL quotient topology. -/
def monomialProjectiveRatioPoint (d : ℕ) (v : Fin (d + 1)) (r : Fin d → ℂ) :
    Projectivization ℂ (Fin (d + 1) → ℂ) :=
  (nativeProjectivePointHomeomorph d).symm (polynomialProjRatioPoint d v r)

/-- Existing native ratio geometry gives a genuine ambient original open embedding. -/
theorem isOpenEmbedding_monomialProjectiveRatioPoint (d : ℕ) (v : Fin (d + 1)) :
    Topology.IsOpenEmbedding (monomialProjectiveRatioPoint d v) := by
  exact (nativeProjectivePointHomeomorph d).symm.isOpenEmbedding.comp
    (polynomialProjRatioPoint_isOpenEmbedding d v)

/-- The native ratio point of the literal affine polynomial graph is the SAME
original projective point, on the whole complex target including the boundary. -/
theorem monomialProjectiveRatioPoint_vertex (b : Module.Basis (Fin n) ℤ M)
    (β : Fin (d + 1) → M) (v : Fin (d + 1)) (z : Fin n → ℂ) :
    monomialProjectiveRatioPoint d v (monomialVertexRatioVector b β v z) =
      monomialVertexPoint b β v z := by
  apply (nativeProjectivePointHomeomorph d).injective
  rw [monomialProjectiveRatioPoint, Homeomorph.apply_symm_apply,
    monomialVertexPoint, nativeProjectivePointHomeomorph_mk d
      ⟨monomialVertexVector b β v z, monomialVertexVector_ne_zero b β v z⟩,
    polynomialProjNonzeroVectorPoint_eq_chart d _ v
      (by simpa only [monomialVertexVector_vertex] using (one_ne_zero : (1 : ℂ) ≠ 0)),
    polynomialProjRatioPoint_eq_vector, insertNth_monomialVertexRatioVector]

/-- The actual original complex unit torus coordinates are dense in C^n.
Existing scalar punctured-density and product-density mothers include n=0. -/
theorem denseRange_latticeUnitCoordinates (n : ℕ) :
    DenseRange (fun a : Fin n → ℂˣ => (fun j => (a j : ℂ))) := by
  have hd : DenseRange (fun a : ℂˣ => (a : ℂ)) := by
    have hr : Set.range (fun a : ℂˣ => (a : ℂ)) = ({0} : Set ℂ)ᶜ := by
      ext z
      constructor
      · rintro ⟨a, rfl⟩
        exact Units.ne_zero a
      · intro hz
        exact ⟨Units.mk0 z hz, rfl⟩
    rw [DenseRange, hr]
    exact dense_compl_singleton 0
  change DenseRange (Pi.map (fun _ : Fin n => fun a : ℂˣ => (a : ℂ)))
  exact DenseRange.piMap (fun _ => hd)

/-- The existing ambient ratio chart sees precisely the SAME original unit
monomial graph, proved from actual point identities and genuine injectivity. -/
theorem monomialProjectiveRatioPoint_preimage_orbit (b : Module.Basis (Fin n) ℤ M)
    (β : Fin (d + 1) → M) (v : Fin (d + 1))
    (hpos : ∀ i j, 0 ≤ b.repr (β i - β v) j) :
    monomialProjectiveRatioPoint d v ⁻¹'
        Set.range (monomialProjectiveOrbit (fun i j => b.repr (β i) j)) =
      Set.range (fun a : Fin n → ℂˣ =>
        monomialVertexRatioVector b β v (fun j => (a j : ℂ))) := by
  ext r
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    apply (isOpenEmbedding_monomialProjectiveRatioPoint d v).injective
    rw [monomialProjectiveRatioPoint_vertex, monomialVertexPoint_torus b β v hpos]
    exact ha
  · rintro ⟨a, rfl⟩
    refine ⟨a, ?_⟩
    rw [monomialProjectiveRatioPoint_vertex, monomialVertexPoint_torus b β v hpos]

/-- Genuine closed-embedding and open-preimage closure mothers manufacture the
whole actual orbit-closure graph, without a chart or convergence certificate. -/
theorem monomialProjectiveRatioPoint_preimage_closure (b : Module.Basis (Fin n) ℤ M)
    (β : Fin (d + 1) → M) (v : Fin (d + 1)) (ν : Fin n → Fin (d + 1))
    (hpos : ∀ i j, 0 ≤ b.repr (β i - β v) j)
    (hν : ∀ j, β (ν j) - β v = b j) :
    monomialProjectiveRatioPoint d v ⁻¹'
        monomialProjectiveOrbitClosure (fun i j => b.repr (β i) j) =
      Set.range (monomialVertexRatioVector b β v) := by
  rw [monomialProjectiveOrbitClosure,
    (isOpenEmbedding_monomialProjectiveRatioPoint d v).isOpenMap.preimage_closure_eq_closure_preimage
      (isOpenEmbedding_monomialProjectiveRatioPoint d v).continuous,
    monomialProjectiveRatioPoint_preimage_orbit b β v hpos]
  change closure (Set.range ((monomialVertexRatioVector b β v) ∘
    (fun a : Fin n → ℂˣ => (fun j => (a j : ℂ))))) = _
  rw [Set.range_comp, (isClosedEmbedding_monomialVertexRatioVector b β v ν hν).closure_image_eq,
    (denseRange_latticeUnitCoordinates n).closure_eq, Set.image_univ]

/-- The full actual original vertex-point range is exactly the SAME orbit
closure intersected with the existing native ambient coordinate open. -/
theorem monomialVertexPoint_range (b : Module.Basis (Fin n) ℤ M)
    (β : Fin (d + 1) → M) (v : Fin (d + 1)) (ν : Fin n → Fin (d + 1))
    (hpos : ∀ i j, 0 ≤ b.repr (β i - β v) j)
    (hν : ∀ j, β (ν j) - β v = b j) :
    Set.range (monomialVertexPoint b β v) =
      monomialProjectiveOrbitClosure (fun i j => b.repr (β i) j) ∩
        Set.range (monomialProjectiveRatioPoint d v) := by
  calc
    _ = Set.range ((monomialProjectiveRatioPoint d v) ∘
        monomialVertexRatioVector b β v) := by
      congr 1
      funext z
      exact (monomialProjectiveRatioPoint_vertex b β v z).symm
    _ = monomialProjectiveRatioPoint d v '' Set.range (monomialVertexRatioVector b β v) :=
      Set.range_comp _ _
    _ = monomialProjectiveRatioPoint d v ''
        (monomialProjectiveRatioPoint d v ⁻¹'
          monomialProjectiveOrbitClosure (fun i j => b.repr (β i) j)) := by
      rw [monomialProjectiveRatioPoint_preimage_closure b β v ν hpos hν]
    _ = _ := Set.image_preimage_eq_inter_range

/-- Actual neighboring exponent readbacks manufacture injectivity and the
original topology of the vertex-point image. -/
theorem isEmbedding_monomialVertexPoint (b : Module.Basis (Fin n) ℤ M)
    (β : Fin (d + 1) → M) (v : Fin (d + 1)) (ν : Fin n → Fin (d + 1))
    (hν : ∀ j, β (ν j) - β v = b j) :
    Topology.IsEmbedding (monomialVertexPoint b β v) := by
  have hcomp : monomialVertexPoint b β v =
      (monomialProjectiveRatioPoint d v) ∘ monomialVertexRatioVector b β v := by
    funext z
    exact (monomialProjectiveRatioPoint_vertex b β v z).symm
  rw [hcomp]
  exact (isOpenEmbedding_monomialProjectiveRatioPoint d v).isEmbedding.comp
    (isClosedEmbedding_monomialVertexRatioVector b β v ν hν).isEmbedding

/-- Every full-target vertex point belongs to the ORIGINAL orbit closure,
produced from the actual integer configuration rather than assumed geometry. -/
theorem monomialVertexPoint_mem_closure (b : Module.Basis (Fin n) ℤ M)
    (β : Fin (d + 1) → M) (v : Fin (d + 1)) (ν : Fin n → Fin (d + 1))
    (hpos : ∀ i j, 0 ≤ b.repr (β i - β v) j)
    (hν : ∀ j, β (ν j) - β v = b j) (z : Fin n → ℂ) :
    monomialVertexPoint b β v z ∈ monomialProjectiveOrbitClosure (fun i j => b.repr (β i) j) := by
  have h : monomialVertexPoint b β v z ∈ Set.range (monomialVertexPoint b β v) := ⟨z, rfl⟩
  rw [monomialVertexPoint_range b β v ν hpos hν] at h
  exact h.1

/-- The actual original vertex point, now in the SAME original closure subtype. -/
def monomialVertexClosurePoint (b : Module.Basis (Fin n) ℤ M)
    (β : Fin (d + 1) → M) (v : Fin (d + 1)) (ν : Fin n → Fin (d + 1))
    (hpos : ∀ i j, 0 ≤ b.repr (β i - β v) j)
    (hν : ∀ j, β (ν j) - β v = b j) (z : Fin n → ℂ) :
    monomialProjectiveOrbitClosure (fun i j => b.repr (β i) j) :=
  ⟨monomialVertexPoint b β v z, monomialVertexPoint_mem_closure b β v ν hpos hν z⟩

/-- The produced closure chart has precisely the original ambient ratio-open source. -/
theorem monomialVertexClosurePoint_range (b : Module.Basis (Fin n) ℤ M)
    (β : Fin (d + 1) → M) (v : Fin (d + 1)) (ν : Fin n → Fin (d + 1))
    (hpos : ∀ i j, 0 ≤ b.repr (β i - β v) j)
    (hν : ∀ j, β (ν j) - β v = b j) :
    Set.range (monomialVertexClosurePoint b β v ν hpos hν) =
      Subtype.val ⁻¹' Set.range (monomialProjectiveRatioPoint d v) := by
  ext p
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨monomialVertexRatioVector b β v z, monomialProjectiveRatioPoint_vertex b β v z⟩
  · intro hp
    have h : p.val ∈ Set.range (monomialVertexPoint b β v) := by
      rw [monomialVertexPoint_range b β v ν hpos hν]
      exact ⟨p.property, hp⟩
    obtain ⟨z, hz⟩ := h
    exact ⟨z, Subtype.ext hz⟩

/-- The original integer configuration manufactures a genuine open embedding
onto the SAME orbit closure, without assuming any target chart data. -/
theorem isOpenEmbedding_monomialVertexClosurePoint (b : Module.Basis (Fin n) ℤ M)
    (β : Fin (d + 1) → M) (v : Fin (d + 1)) (ν : Fin n → Fin (d + 1))
    (hpos : ∀ i j, 0 ≤ b.repr (β i - β v) j)
    (hν : ∀ j, β (ν j) - β v = b j) :
    Topology.IsOpenEmbedding (monomialVertexClosurePoint b β v ν hpos hν) where
  toIsEmbedding := (isEmbedding_monomialVertexPoint b β v ν hν).codRestrict _
    (monomialVertexPoint_mem_closure b β v ν hpos hν)
  isOpen_range := by
    rw [monomialVertexClosurePoint_range b β v ν hpos hν]
    exact (isOpenEmbedding_monomialProjectiveRatioPoint d v).isOpen_range.preimage
      continuous_subtype_val

/-- The GENUINE original orbit-closure vertex chart, produced from integer data
through the existing native ratio chart. No smoothness or cover is assumed. -/
def monomialVertexChart (b : Module.Basis (Fin n) ℤ M)
    (β : Fin (d + 1) → M) (v : Fin (d + 1)) (ν : Fin n → Fin (d + 1))
    (hpos : ∀ i j, 0 ≤ b.repr (β i - β v) j)
    (hν : ∀ j, β (ν j) - β v = b j) :
    OpenPartialHomeomorph (monomialProjectiveOrbitClosure (fun i j => b.repr (β i) j))
      (Fin n → ℂ) :=
  ((isOpenEmbedding_monomialVertexClosurePoint b β v ν hpos hν).toOpenPartialHomeomorph
    (monomialVertexClosurePoint b β v ν hpos hν)).symm

/-- The true vertex chart has the WHOLE original C^n target, retaining n=0. -/
theorem monomialVertexChart_target (b : Module.Basis (Fin n) ℤ M)
    (β : Fin (d + 1) → M) (v : Fin (d + 1)) (ν : Fin n → Fin (d + 1))
    (hpos : ∀ i j, 0 ≤ b.repr (β i - β v) j)
    (hν : ∀ j, β (ν j) - β v = b j) :
    (monomialVertexChart b β v ν hpos hν).target = Set.univ := rfl

/-- The genuine inverse retains the SAME original normalized polynomial points. -/
theorem monomialVertexChart_symm (b : Module.Basis (Fin n) ℤ M)
    (β : Fin (d + 1) → M) (v : Fin (d + 1)) (ν : Fin n → Fin (d + 1))
    (hpos : ∀ i j, 0 ≤ b.repr (β i - β v) j)
    (hν : ∀ j, β (ν j) - β v = b j) :
    (monomialVertexChart b β v ν hpos hν).symm =
      monomialVertexClosurePoint b β v ν hpos hν :=
  Topology.IsOpenEmbedding.toOpenPartialHomeomorph_apply
    (monomialVertexClosurePoint b β v ν hpos hν)
    (isOpenEmbedding_monomialVertexClosurePoint b β v ν hpos hν)

/-- Actual orbit membership in the genuine vertex chart is precisely nonzero
original complex coordinates, proved before expressing the boundary polynomial. -/
theorem monomialVertexPoint_mem_orbit_iff (b : Module.Basis (Fin n) ℤ M)
    (β : Fin (d + 1) → M) (v : Fin (d + 1)) (ν : Fin n → Fin (d + 1))
    (hpos : ∀ i j, 0 ≤ b.repr (β i - β v) j)
    (hν : ∀ j, β (ν j) - β v = b j) (z : Fin n → ℂ) :
    monomialVertexPoint b β v z ∈ Set.range (monomialProjectiveOrbit (fun i j => b.repr (β i) j)) ↔
      ∀ j, z j ≠ 0 := by
  constructor
  · rintro ⟨a, ha⟩
    have hz : (fun j => (a j : ℂ)) = z := by
      apply (isEmbedding_monomialVertexPoint b β v ν hν).injective
      rw [monomialVertexPoint_torus b β v hpos]
      exact ha
    intro j
    rw [← congrFun hz j]
    exact Units.ne_zero (a j)
  · intro hz
    let a : Fin n → ℂˣ := fun j => Units.mk0 (z j) (hz j)
    refine ⟨a, ?_⟩
    exact (monomialVertexPoint_torus b β v hpos a).symm

/-- The original boundary is the literal coordinate-product zero locus in
this PRODUCED chart, including the empty product one in dimension zero. -/
theorem monomialVertexPoint_mem_orbit_iff_prod_ne_zero (b : Module.Basis (Fin n) ℤ M)
    (β : Fin (d + 1) → M) (v : Fin (d + 1)) (ν : Fin n → Fin (d + 1))
    (hpos : ∀ i j, 0 ≤ b.repr (β i - β v) j)
    (hν : ∀ j, β (ν j) - β v = b j) (z : Fin n → ℂ) :
    monomialVertexPoint b β v z ∈ Set.range (monomialProjectiveOrbit (fun i j => b.repr (β i) j)) ↔
      ∏ j, z j ≠ 0 := by
  rw [monomialVertexPoint_mem_orbit_iff b β v ν hpos hν]
  simp only [Finset.prod_ne_zero_iff, Finset.mem_univ, forall_const]

/-- The produced vertex chart source is the SAME original ambient coordinate open. -/
theorem monomialVertexChart_source (b : Module.Basis (Fin n) ℤ M)
    (β : Fin (d + 1) → M) (v : Fin (d + 1)) (ν : Fin n → Fin (d + 1))
    (hpos : ∀ i j, 0 ≤ b.repr (β i - β v) j)
    (hν : ∀ j, β (ν j) - β v = b j) :
    (monomialVertexChart b β v ν hpos hν).source =
      Subtype.val ⁻¹' Set.range (monomialProjectiveRatioPoint d v) := by
  calc
    _ = Set.range (monomialVertexClosurePoint b β v ν hpos hν) :=
      Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target
        (monomialVertexClosurePoint b β v ν hpos hν)
        (isOpenEmbedding_monomialVertexClosurePoint b β v ν hpos hν)
    _ = _ := monomialVertexClosurePoint_range b β v ν hpos hν

/-- Actual global chart coordinates read back the literal neighboring complex coordinates. -/
theorem monomialVertexChart_apply_point (b : Module.Basis (Fin n) ℤ M)
    (β : Fin (d + 1) → M) (v : Fin (d + 1)) (ν : Fin n → Fin (d + 1))
    (hpos : ∀ i j, 0 ≤ b.repr (β i - β v) j)
    (hν : ∀ j, β (ν j) - β v = b j) (z : Fin n → ℂ) :
    monomialVertexChart b β v ν hpos hν (monomialVertexClosurePoint b β v ν hpos hν z) = z := by
  rw [← monomialVertexChart_symm b β v ν hpos hν]
  exact (monomialVertexChart b β v ν hpos hν).right_inv (by
    rw [monomialVertexChart_target]
    trivial)

/-- For EVERY original homogeneous representative of an actual source point,
the manufactured chart is the literal neighbor/vertex ratio, with a genuinely
nonzero denominator proved from the original scalar fiber relation first. -/
theorem monomialVertexChart_ratio_readback (b : Module.Basis (Fin n) ℤ M)
    (β : Fin (d + 1) → M) (v : Fin (d + 1)) (ν : Fin n → Fin (d + 1))
    (hpos : ∀ i j, 0 ≤ b.repr (β i - β v) j)
    (hν : ∀ j, β (ν j) - β v = b j)
    (p : monomialProjectiveOrbitClosure (fun i j => b.repr (β i) j))
    (hp : p ∈ (monomialVertexChart b β v ν hpos hν).source)
    (w : Fin (d + 1) → ℂ) (hw : w ≠ 0)
    (hpw : p.val = Projectivization.mk ℂ w hw) :
    w v ≠ 0 ∧ ∀ j, monomialVertexChart b β v ν hpos hν p j = w (ν j) / w v := by
  let z := monomialVertexChart b β v ν hpos hν p
  have hz : monomialVertexClosurePoint b β v ν hpos hν z = p := by
    rw [← monomialVertexChart_symm b β v ν hpos hν]
    exact (monomialVertexChart b β v ν hpos hν).left_inv hp
  have heq : monomialVertexPoint b β v z = Projectivization.mk ℂ w hw :=
    (congrArg Subtype.val hz).trans hpw
  obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff ℂ _ _ _ _).mp heq
  have hv := congrFun hc v
  change (c : ℂ) * w v = monomialVertexVector b β v z v at hv
  rw [monomialVertexVector_vertex] at hv
  have hwv : w v ≠ 0 := by
    intro hzero
    simp [hzero] at hv
  refine ⟨hwv, ?_⟩
  intro j
  have hj := congrFun hc (ν j)
  change (c : ℂ) * w (ν j) = monomialVertexVector b β v z (ν j) at hj
  rw [monomialVertexVector_neighbor b β v ν hν] at hj
  change z j = w (ν j) / w v
  rw [← hj]
  apply (eq_div_iff hwv).mpr
  calc
    (c : ℂ) * w (ν j) * w v = w (ν j) * ((c : ℂ) * w v) := by ring
    _ = w (ν j) := by rw [hv, mul_one]

private theorem monomialInsertNth_one_ne_zero (d : ℕ) (v : Fin (d + 1)) (r : Fin d → ℂ) :
    (Fin.insertNth v (1 : ℂ) r : Fin (d + 1) → ℂ) ≠ 0 := by
  intro h
  have hv := congrFun h v
  exact one_ne_zero (by simpa only [Fin.insertNth_apply_same, Pi.zero_apply] using hv)

/-- Existing native ratio points have the SAME original normalized homogeneous
representatives, with their actual nonvanishing proved first. -/
theorem monomialProjectiveRatioPoint_eq_mk (d : ℕ) (v : Fin (d + 1)) (r : Fin d → ℂ) :
    monomialProjectiveRatioPoint d v r = Projectivization.mk ℂ (Fin.insertNth v (1 : ℂ) r)
      (monomialInsertNth_one_ne_zero d v r) := by
  apply (nativeProjectivePointHomeomorph d).injective
  rw [monomialProjectiveRatioPoint, Homeomorph.apply_symm_apply,
    nativeProjectivePointHomeomorph_mk d
      ⟨Fin.insertNth v (1 : ℂ) r, monomialInsertNth_one_ne_zero d v r⟩,
    polynomialProjNonzeroVectorPoint_eq_chart d _ v (by simp),
    polynomialProjRatioPoint_eq_vector]

/-- The actual existing ambient ratio open is EXACTLY original nonvanishing
of the v-coordinate, for every genuine original homogeneous representative. -/
theorem monomialProjectiveRatioPoint_mem_mk_iff (d : ℕ) (v : Fin (d + 1))
    (w : Fin (d + 1) → ℂ) (hw : w ≠ 0) :
    Projectivization.mk ℂ w hw ∈ Set.range (monomialProjectiveRatioPoint d v) ↔ w v ≠ 0 := by
  constructor
  · rintro ⟨r, hr⟩
    rw [monomialProjectiveRatioPoint_eq_mk] at hr
    obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff ℂ _ _ _ _).mp hr
    have hv := congrFun hc v
    change (c : ℂ) * w v = (Fin.insertNth v (1 : ℂ) r : Fin (d + 1) → ℂ) v at hv
    rw [Fin.insertNth_apply_same] at hv
    intro hzero
    simp [hzero] at hv
  · intro hwv
    refine ⟨fun k => w (v.succAbove k) / w v, ?_⟩
    rw [monomialProjectiveRatioPoint_eq_mk]
    apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
    refine ⟨(w v)⁻¹, ?_⟩
    funext i
    refine Fin.succAboveCases v ?_ (fun k => ?_) i
    · rw [Fin.insertNth_apply_same]
      change (w v)⁻¹ * w v = 1
      exact inv_mul_cancel₀ hwv
    · rw [Fin.insertNth_apply_succAbove]
      change (w v)⁻¹ * w (v.succAbove k) = w (v.succAbove k) / w v
      exact (div_eq_inv_mul _ _).symm

/-- The produced vertex source is LITERALLY the original v-coordinate
nonvanishing locus, including all original homogeneous representatives. -/
theorem monomialVertexChart_mem_source_iff (b : Module.Basis (Fin n) ℤ M)
    (β : Fin (d + 1) → M) (v : Fin (d + 1)) (ν : Fin n → Fin (d + 1))
    (hpos : ∀ i j, 0 ≤ b.repr (β i - β v) j)
    (hν : ∀ j, β (ν j) - β v = b j)
    (p : monomialProjectiveOrbitClosure (fun i j => b.repr (β i) j))
    (w : Fin (d + 1) → ℂ) (hw : w ≠ 0)
    (hpw : p.val = Projectivization.mk ℂ w hw) :
    p ∈ (monomialVertexChart b β v ν hpos hν).source ↔ w v ≠ 0 := by
  rw [monomialVertexChart_source]
  change p.val ∈ Set.range (monomialProjectiveRatioPoint d v) ↔ _
  rw [hpw]
  exact monomialProjectiveRatioPoint_mem_mk_iff d v w hw

/-- In the ACTUAL manufactured chart, the original torus boundary is exactly
the coordinate-product zero locus, with empty product one in rank zero. -/
theorem monomialVertexChart_boundary_iff (b : Module.Basis (Fin n) ℤ M)
    (β : Fin (d + 1) → M) (v : Fin (d + 1)) (ν : Fin n → Fin (d + 1))
    (hpos : ∀ i j, 0 ≤ b.repr (β i - β v) j)
    (hν : ∀ j, β (ν j) - β v = b j) (z : Fin n → ℂ) :
    ((monomialVertexChart b β v ν hpos hν).symm z).val ∉
        Set.range (monomialProjectiveOrbit (fun i j => b.repr (β i) j)) ↔
      ∏ j, z j = 0 := by
  rw [monomialVertexChart_symm]
  change monomialVertexPoint b β v z ∉
    Set.range (monomialProjectiveOrbit (fun i j => b.repr (β i) j)) ↔ _
  rw [monomialVertexPoint_mem_orbit_iff_prod_ne_zero b β v ν hpos hν]
  exact not_not

end SGPT.Toric
