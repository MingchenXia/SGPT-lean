import SGPT.Checks.Literature.BJDivisorial.DiscreteValuationRestriction
import SGPT.Checks.Literature.BJDivisorial.AbhyankarDVRFiniteness
import SGPT.Checks.Literature.BJDivisorial.DVRResidueDegreeBound
import SGPT.Foundations.PublishedEnvelope.Alterations.StableModification.ValuationRing.FibreDimension

/-!
# Restriction of an actual geometric DVR

A normalized geometric DVR restricted along an actual finitely generated
subfield is either trivial or again a genuine essentially finite type DVR.
The latter conclusion is derived from relative Abhyankar and the explicit
finite curve-field producer, not assumed as a dictionary certificate.
-/
noncomputable section
open IsLocalRing Cardinal

namespace SGPT.NAPotential.BJ.Divisorial
open SGPT.Foundations.PublishedEnvelope.Char0

universe u
variable {k K F : Type u} [Field k] [Field K] [Field F]
  [Algebra k K] [Algebra k F] [Algebra K F] [IsScalarTower k K F]
  (W : Subalgebra k F) [IsDiscreteValuationRing W] [IsFractionRing W F]

/-- The actual field embedding restricted to the actual inverse-image DVR. -/
def restrictedToRing : restrictedRing (K := K) W →ₐ[k] W :=
  (((IsScalarTower.toAlgHom k K F).comp (restrictedRing (K := K) W).val)).codRestrict W
    fun x => x.2

/-- The actual restricted inclusion is local; this follows from taking the
literal inverse image in a field, with no domination certificate supplied. -/
instance restrictedToRing_isLocalHom :
    IsLocalHom (restrictedToRing (K := K) W).toRingHom := by
  constructor
  intro x hx
  have hx0 : (x : K) ≠ 0 := by
    intro h
    apply hx.ne_zero
    apply Subtype.ext
    change algebraMap K F (x : K) = 0
    rw [h, map_zero]
  have hi : (x : K)⁻¹ ∈ restrictedRing (K := K) W := by
    change algebraMap K F (x : K)⁻¹ ∈ W
    rw [map_inv₀]
    have hunit : ((((hx.unit⁻¹ : Wˣ) : W)) : F) =
        (algebraMap K F (x : K))⁻¹ := by
      rw [coe_inv_unit, hx.unit_spec]
      rfl
    rw [← hunit]
    exact ((hx.unit⁻¹ : Wˣ) : W).2
  exact IsUnit.of_mul_eq_one (⟨(x : K)⁻¹, hi⟩ : restrictedRing (K := K) W)
    (Subtype.ext (mul_inv_cancel₀ hx0))

variable [CharZero k] [Algebra.EssFiniteType k K] [Algebra.EssFiniteType k W]

omit [CharZero k] [Algebra.EssFiniteType k K] in
/-- The nontrivial actual restriction has the exact divisorial residue degree.
The relative residue inequality is the existing fully proved native theorem. -/
theorem restrictedRing_residue_degree
    (h : (restrictedValuation (K := K) W).IsNontrivial) :
    letI := restrictedRing_isDVR W h
    Algebra.trdeg k (ResidueField (restrictedRing (K := K) W)) + 1 =
      Algebra.trdeg k K := by
  let V := restrictedRing (K := K) W
  let : IsDiscreteValuationRing V := restrictedRing_isDVR W h
  let : IsFractionRing V K := restrictedRing_isFractionRing W
  let φ := (restrictedToRing (K := K) W).toRingHom
  let : Algebra (ResidueField V) (ResidueField W) := (ResidueField.map φ).toAlgebra
  let : IsScalarTower k (ResidueField V) (ResidueField W) :=
    IsScalarTower.of_algebraMap_eq fun a => by
      change residue W (algebraMap k W a) =
        ResidueField.map φ (residue V (algebraMap k V a))
      rw [ResidueField.map_residue]
      exact congrArg (residue W) ((restrictedToRing (K := K) W).commutes a).symm
  have hrelative : Algebra.trdeg (ResidueField V) (ResidueField W) ≤
      Algebra.trdeg K F := by
    apply Alterations.StableModification.ValuationRing.trdeg_residueField_le
      φ V.val.toRingHom W.val.toRingHom (fun _ => rfl)
    intro x
    by_cases hx : x = 0
    · exact Or.inl ⟨0, by simp [hx]⟩
    rcases ValuationRing.isInteger_or_isInteger V x with ⟨a, ha⟩ | ⟨a, ha⟩
    · exact Or.inl ⟨a, ha⟩
    · refine Or.inr ⟨a, ?_⟩
      change algebraMap V K a * x = 1
      rw [ha]
      exact inv_mul_cancel₀ hx
  have : Algebra.EssFiniteType k F := essFiniteType_of_isFractionRing W
  have : Algebra.EssFiniteType K F := .of_comp k K F
  have hW := trdeg_residueField_add_one W
  have hineq : Algebra.trdeg k K + Algebra.trdeg K F ≤
      (Algebra.trdeg k (ResidueField V) + 1) + Algebra.trdeg K F := by
    calc
      _ = Algebra.trdeg k F := trdeg_add_eq k K
      _ = Algebra.trdeg k (ResidueField W) + 1 := hW.symm
      _ = (Algebra.trdeg k (ResidueField V) +
          Algebra.trdeg (ResidueField V) (ResidueField W)) + 1 := by
        rw [trdeg_add_eq k (ResidueField V)]
      _ ≤ (Algebra.trdeg k (ResidueField V) + Algebra.trdeg K F) + 1 := by
        exact _root_.add_le_add (_root_.add_le_add le_rfl hrelative) le_rfl
      _ = _ := by ac_rfl
  have hreverse := (Cardinal.add_le_add_iff_of_lt_aleph0 (trdeg_lt_aleph0 K F)).mp hineq
  exact le_antisymm (DVR_residue_degree_le V) hreverse

/-- The actual nontrivial restriction of a geometric DVR is genuinely
geometric: both discreteness and essential finiteness have been derived. -/
theorem restrictedRing_geometricDVR
    (h : (restrictedValuation (K := K) W).IsNontrivial) :
    IsDiscreteValuationRing (restrictedRing (K := K) W) ∧
      Algebra.EssFiniteType k (restrictedRing (K := K) W) := by
  have hd := restrictedRing_isDVR W h
  let : IsDiscreteValuationRing (restrictedRing (K := K) W) := hd
  let : IsFractionRing (restrictedRing (K := K) W) K := restrictedRing_isFractionRing W
  exact ⟨hd, geometricDVR_essFiniteType_of_residue_degree _
    (restrictedRing_residue_degree W h)⟩

end SGPT.NAPotential.BJ.Divisorial
