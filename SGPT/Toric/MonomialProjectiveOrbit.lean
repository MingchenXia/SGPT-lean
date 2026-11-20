import SGPT.Convex.LaurentPolytope
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.LinearAlgebra.Pi
import Mathlib.Topology.Homeomorph.Lemmas

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set Filter SGPT.Convex
open scoped Topology BigOperators

/-- Original lattice coordinates interpreted as actual nonzero complex coordinates. -/
def latticeTorusPoint {n : ℕ} (a : Fin n → ℂˣ) : TorusPoint n :=
  ⟨fun j => (a j : ℂ), fun j => Units.ne_zero (a j)⟩

/-- The actual integral character, with its genuine multiplicative torus law. -/
def latticeCharacter {n : ℕ} (m : Fin n → ℤ) : (Fin n → ℂˣ) →* ℂˣ where
  toFun a := ∏ j, a j ^ m j
  map_one' := by simp
  map_mul' a b := by simp only [Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib]

/-- This character is the original existing Laurent monomial, with all integer exponents. -/
theorem latticeCharacter_eq_laurentMonomial {n : ℕ} (m : Fin n → ℤ) (a : Fin n → ℂˣ) :
    (latticeCharacter m a : ℂ) = laurentMonomial (latticeTorusPoint a) m := by
  simp [latticeCharacter, laurentMonomial, latticeTorusPoint]

/-- Actual characters are continuous on the original complex unit torus. -/
theorem continuous_latticeCharacter {n : ℕ} (m : Fin n → ℤ) : Continuous (latticeCharacter m) := by
  change Continuous (fun a : Fin n → ℂˣ => ∏ j, a j ^ m j)
  exact continuous_finsetProd _ (fun j _ => (continuous_apply j).zpow (m j))

/-- The original squared logarithm convention reads the precise integral pairing. -/
theorem latticeCharacter_log_norm_sq {n : ℕ} (m : Fin n → ℤ) (a : Fin n → ℂˣ) :
    Real.log (‖(latticeCharacter m a : ℂ)‖ ^ 2) =
      ∑ j, (m j : ℝ) * torusLogCoordinates (latticeTorusPoint a) j := by
  rw [Real.log_pow, latticeCharacter_eq_laurentMonomial, log_norm_laurentMonomial, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [torusLogCoordinates]
  ring

/-- The original native nonzero-vector quotient topology, explicitly named.
No smoothness, dimension or toric-variety identification is built into this object. -/
@[instance_reducible] def monomialProjectiveTopology (I : Type*) : TopologicalSpace (Projectivization ℂ (I → ℂ)) := by
  unfold Projectivization
  infer_instance
attribute [local instance] monomialProjectiveTopology

variable {n : ℕ} {I : Type*}

/-- The existing unit-scalar equivalences give the actual character diagonal. -/
def monomialDiagonal (β : I → Fin n → ℤ) (a : Fin n → ℂˣ) : (I → ℂ) ≃ₗ[ℂ] (I → ℂ) :=
  LinearEquiv.piCongrRight (fun i => LinearEquiv.smulOfUnit (latticeCharacter (β i) a))

theorem monomialDiagonal_apply (β : I → Fin n → ℤ) (a : Fin n → ℂˣ) (v : I → ℂ) (i : I) :
    monomialDiagonal β a v i = (latticeCharacter (β i) a : ℂ) * v i := rfl

/-- Actual quotient action, manufactured by native injective-linear projectivization. -/
def monomialProjectiveAction (β : I → Fin n → ℤ) (a : Fin n → ℂˣ) :
    Projectivization ℂ (I → ℂ) → Projectivization ℂ (I → ℂ) :=
  Projectivization.map (monomialDiagonal β a).toLinearMap (monomialDiagonal β a).injective

/-- Literal homogeneous-coordinate action on every genuine nonzero vector. -/
theorem monomialProjectiveAction_mk (β : I → Fin n → ℤ) (a : Fin n → ℂˣ)
    (v : I → ℂ) (hv : v ≠ 0) :
    monomialProjectiveAction β a (Projectivization.mk ℂ v hv) =
      Projectivization.mk ℂ (monomialDiagonal β a v)
        (by simpa only [map_zero] using (monomialDiagonal β a).injective.ne hv) := rfl

/-- Original torus identity, derived on actual representatives. -/
theorem monomialProjectiveAction_one (β : I → Fin n → ℤ) (p : Projectivization ℂ (I → ℂ)) :
    monomialProjectiveAction β 1 p = p := by
  induction p using Projectivization.ind with
  | h v hv =>
    rw [monomialProjectiveAction_mk]
    congr 1
    ext i
    simp only [monomialDiagonal_apply, map_one, Units.val_one, one_mul]

/-- Original multiplication law, without a supplied action certificate. -/
theorem monomialProjectiveAction_mul (β : I → Fin n → ℤ) (a b : Fin n → ℂˣ)
    (p : Projectivization ℂ (I → ℂ)) :
    monomialProjectiveAction β (a * b) p =
      monomialProjectiveAction β a (monomialProjectiveAction β b p) := by
  induction p using Projectivization.ind with
  | h v hv =>
    simp only [monomialProjectiveAction_mk]
    congr 1
    ext i
    simp only [monomialDiagonal_apply, map_mul, Units.val_mul, mul_assoc]

/-- Continuity is proved for the actual coinduced native quotient topology. -/
theorem continuous_monomialProjectiveAction (β : I → Fin n → ℤ) (a : Fin n → ℂˣ) :
    Continuous (monomialProjectiveAction β a) := by
  have hlin : Continuous (monomialDiagonal β a) := by
    exact continuous_pi (fun i => continuous_const.mul (continuous_apply i))
  have hsub : Continuous (fun v : {v : I → ℂ // v ≠ 0} =>
      (⟨monomialDiagonal β a v.val, by
        simpa only [map_zero] using (monomialDiagonal β a).injective.ne v.property⟩ :
        {v : I → ℂ // v ≠ 0})) := (hlin.comp continuous_subtype_val).subtype_mk _
  apply continuous_coinduced_dom.mpr
  exact continuous_quotient_mk'.comp hsub

/-- The actual inverse torus character gives the whole projective homeomorphism. -/
def monomialProjectiveHomeomorph (β : I → Fin n → ℤ) (a : Fin n → ℂˣ) :
    Projectivization ℂ (I → ℂ) ≃ₜ Projectivization ℂ (I → ℂ) where
  toFun := monomialProjectiveAction β a
  invFun := monomialProjectiveAction β a⁻¹
  left_inv p := by rw [← monomialProjectiveAction_mul, inv_mul_cancel, monomialProjectiveAction_one]
  right_inv p := by rw [← monomialProjectiveAction_mul, mul_inv_cancel, monomialProjectiveAction_one]
  continuous_toFun := continuous_monomialProjectiveAction β a
  continuous_invFun := continuous_monomialProjectiveAction β a⁻¹

variable [Nonempty I]

/-- The literal original character vector of a torus point. -/
def monomialOrbitVector (β : I → Fin n → ℤ) (a : Fin n → ℂˣ) : I → ℂ :=
  fun i => latticeCharacter (β i) a

/-- Actual nonempty exponent family prevents the original vector from vanishing. -/
theorem monomialOrbitVector_ne_zero (β : I → Fin n → ℤ) (a : Fin n → ℂˣ) :
    monomialOrbitVector β a ≠ 0 := by
  intro h
  exact Units.ne_zero (latticeCharacter (β (Classical.arbitrary I)) a) (congrFun h (Classical.arbitrary I))

/-- Genuine monomial projective orbit map, with nonvanishing proved before quotient descent. -/
def monomialProjectiveOrbit (β : I → Fin n → ℤ) (a : Fin n → ℂˣ) :
    Projectivization ℂ (I → ℂ) := Projectivization.mk ℂ (monomialOrbitVector β a) (monomialOrbitVector_ne_zero β a)

/-- Original character multiplication is precisely projective orbit equivariance. -/
theorem monomialProjectiveAction_orbit (β : I → Fin n → ℤ) (a b : Fin n → ℂˣ) :
    monomialProjectiveAction β a (monomialProjectiveOrbit β b) = monomialProjectiveOrbit β (a * b) := by
  unfold monomialProjectiveOrbit
  rw [monomialProjectiveAction_mk]
  congr 1
  ext i
  simp only [monomialDiagonal_apply, monomialOrbitVector, map_mul, Units.val_mul]

/-- The original torus orbit map is continuous, via actual character coordinates and quotient. -/
theorem continuous_monomialProjectiveOrbit (β : I → Fin n → ℤ) : Continuous (monomialProjectiveOrbit β) := by
  have hv : Continuous (monomialOrbitVector β) := by
    exact continuous_pi (fun i => Units.continuous_val.comp (continuous_latticeCharacter (β i)))
  exact continuous_quotient_mk'.comp (hv.subtype_mk (monomialOrbitVector_ne_zero β))

/-- Literal topological projective orbit closure; not yet identified with source X_Sigma. -/
def monomialProjectiveOrbitClosure (β : I → Fin n → ℤ) : Set (Projectivization ℂ (I → ℂ)) :=
  closure (range (monomialProjectiveOrbit β))

/-- The genuine original action maps the original orbit onto itself. -/
theorem monomialProjectiveAction_image_orbit (β : I → Fin n → ℤ) (a : Fin n → ℂˣ) :
    monomialProjectiveAction β a '' range (monomialProjectiveOrbit β) = range (monomialProjectiveOrbit β) := by
  ext p
  constructor
  · rintro ⟨_, ⟨b, rfl⟩, rfl⟩
    exact ⟨a * b, (monomialProjectiveAction_orbit β a b).symm⟩
  · rintro ⟨b, rfl⟩
    refine ⟨monomialProjectiveOrbit β (a⁻¹ * b), mem_range_self _, ?_⟩
    rw [monomialProjectiveAction_orbit, mul_inv_cancel_left]

/-- Genuine homeomorphism closure transport produces invariance of the actual closure. -/
theorem monomialProjectiveAction_image_closure (β : I → Fin n → ℤ) (a : Fin n → ℂˣ) :
    monomialProjectiveAction β a '' monomialProjectiveOrbitClosure β = monomialProjectiveOrbitClosure β := by
  change (monomialProjectiveHomeomorph β a) '' closure (range (monomialProjectiveOrbit β)) = _
  rw [Homeomorph.image_closure]
  change closure (monomialProjectiveAction β a '' range (monomialProjectiveOrbit β)) = _
  rw [monomialProjectiveAction_image_orbit]
  rfl

/-- Closure preservation in both directions, retaining the very same original closed set. -/
theorem monomialProjectiveAction_mem_closure_iff (β : I → Fin n → ℤ) (a : Fin n → ℂˣ)
    (p : Projectivization ℂ (I → ℂ)) :
    monomialProjectiveAction β a p ∈ monomialProjectiveOrbitClosure β ↔ p ∈ monomialProjectiveOrbitClosure β := by
  have hm (b : Fin n → ℂˣ) : MapsTo (monomialProjectiveAction β b)
      (monomialProjectiveOrbitClosure β) (monomialProjectiveOrbitClosure β) :=
    image_subset_iff.mp (monomialProjectiveAction_image_closure β b).le
  constructor
  · intro hp
    have h := hm a⁻¹ hp
    simpa only [← monomialProjectiveAction_mul, inv_mul_cancel, monomialProjectiveAction_one] using h
  · exact fun hp => hm a hp

/-- The actual torus action restricts to a genuine homeomorphism of its literal orbit closure. -/
def monomialOrbitClosureHomeomorph (β : I → Fin n → ℤ) (a : Fin n → ℂˣ) :
    monomialProjectiveOrbitClosure β ≃ₜ monomialProjectiveOrbitClosure β :=
  (monomialProjectiveHomeomorph β a).subtype (fun p => (monomialProjectiveAction_mem_closure_iff β a p).symm)

/-- Restricted original unit law, with no assumed effective action. -/
theorem monomialOrbitClosureHomeomorph_one (β : I → Fin n → ℤ) (p : monomialProjectiveOrbitClosure β) :
    monomialOrbitClosureHomeomorph β 1 p = p := by
  apply Subtype.ext
  exact monomialProjectiveAction_one β p.val

/-- Restricted original multiplication law on the actual orbit-closure subtype. -/
theorem monomialOrbitClosureHomeomorph_mul (β : I → Fin n → ℤ) (a b : Fin n → ℂˣ)
    (p : monomialProjectiveOrbitClosure β) :
    monomialOrbitClosureHomeomorph β (a * b) p =
      monomialOrbitClosureHomeomorph β a (monomialOrbitClosureHomeomorph β b p) := by
  apply Subtype.ext
  exact monomialProjectiveAction_mul β a b p.val

/-- The original monomial orbit map corestricted to its literal projective closure. -/
def monomialOrbitClosureMap (β : I → Fin n → ℤ) : (Fin n → ℂˣ) → monomialProjectiveOrbitClosure β :=
  Set.inclusion subset_closure ∘ Set.rangeFactorization (monomialProjectiveOrbit β)

/-- Existing density of a set in its closure applies to the actual native orbit map. -/
theorem denseRange_monomialOrbitClosureMap (β : I → Fin n → ℤ) : DenseRange (monomialOrbitClosureMap β) :=
  ((denseRange_inclusion_iff subset_closure).2 subset_rfl).comp
    Set.rangeFactorization_surjective.denseRange (continuous_inclusion subset_closure)

end SGPT.Toric
