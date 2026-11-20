import SGPT.Checks.Comparison.BJPair3DivGeometricDVRFiniteness

-- Lane BJ-PAIR (R5/thm:pshdetbydiv bridge): ported from `SGPT.Checks.Literature/SGPT.Checks.Literature/BJDivisorial/AbhyankarDVRFiniteness.lean`
-- (that library pins another SGPT.Foundations.Envelope revision and cannot be imported here); only the
-- imports, the `Alterations` namespace (now `SGPT.Support.Alterations`) and this file's namespace
-- (`Divisorial` -> `Pair3Div`, `ExternalClassStability` -> `Pair3ClassStability`) are changed.

/-!
# Essential finiteness from actual divisorial residue degree

Lift an actual residue transcendence basis, use its coefficient field inside
V, and apply the finite curve-field producer. No finite-type hypothesis on V
is assumed. The numerical Abhyankar equality will be derived from the native
geometric DVR in the next restriction lemma; it is not a point dictionary.
-/

noncomputable section
open IsLocalRing Cardinal
open scoped IntermediateField

namespace SGPT.NAPotential.BJ.Pair3Div
open SGPT.Foundations.Envelope.Char0

universe u
variable {k K : Type u} [Field k] [Field K] [Algebra k K] [CharZero k]
  [Algebra.EssFiniteType k K]

/-- A DVR in a finitely generated field, with divisorial residue degree,
is genuinely essentially finite type over its original coefficient field. -/
theorem geometricDVR_essFiniteType_of_residue_degree
    (V : Subalgebra k K) [IsDiscreteValuationRing V] [IsFractionRing V K]
    (htr : Algebra.trdeg k (ResidueField V) + 1 = Algebra.trdeg k K) :
    Algebra.EssFiniteType k V := by
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis k (ResidueField V)
  choose u hu using fun x : s => residue_surjective (R := V) (x : ResidueField V)
  have hres : residue V ∘ u = ((↑) : s → ResidueField V) := funext hu
  have hb : IsTranscendenceBasis k (residue V ∘ u) := hres ▸ hs
  set E := IntermediateField.adjoin k (Set.range fun i => (u i : K))
  have hEV : E.toSubalgebra ≤ V := adjoin_le_of_algebraicIndependent_residue hb.1
  set V' := extendScalarsOfLE V E hEV
  have hindK := algebraicIndependent_coe_of_residue (K := K) hb.1
  have hE : Algebra.trdeg k E = #s := by
    have h := hindK.aevalEquivField.lift_trdeg_eq
    rw [trdeg_fractionRing_mvPolynomial, Cardinal.lift_lift] at h
    exact (Cardinal.lift_inj.1 h).symm
  have hκ : Algebra.trdeg k (ResidueField V) = #s := hs.cardinalMk_eq_trdeg.symm
  have hκfin : Algebra.trdeg k (ResidueField V) < Cardinal.aleph0 :=
    (le_self_add.trans_eq htr).trans_lt (trdeg_lt_aleph0 k K)
  have hEfin : Algebra.trdeg k E < Cardinal.aleph0 := by
    rwa [hE, ← hκ]
  have h1 : Algebra.trdeg E K = 1 := by
    apply (Cardinal.add_right_inj_of_lt_aleph0 hEfin).mp
    have ht := (trdeg_add_eq k E (A := K)).trans htr.symm
    simpa only [hE, hκ, add_comm] using ht
  have hsfin : s.Finite := Cardinal.lt_aleph0_iff_set_finite.mp (hκ ▸ hκfin)
  let : Finite s := hsfin.to_subtype
  have : Algebra.EssFiniteType k E := IntermediateField.essFiniteType_iff.mpr
    (IntermediateField.fg_adjoin_of_finite (Set.finite_range _))
  let : CharZero E := charZero_of_injective_algebraMap (algebraMap k E).injective
  have : Algebra.EssFiniteType E K := .of_comp k E K
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible V'
  let : Fact (Irreducible π) := ⟨hπ⟩
  have hi : AlgebraicIndependent E (fun _ : Unit => (π : K)) :=
    algebraicIndependent_unique_type_iff.mpr (transcendental_uniformizer V' π)
  have ht : IsTranscendenceBasis E (fun _ : Unit => (π : K)) := by
    apply hi.isTranscendenceBasis_of_lift_trdeg_le_of_finite
    simp [h1]
  have halg : Algebra.IsAlgebraic E⟮(π : K)⟯ K := by
    have h := ht.isAlgebraic_field
    rwa [Set.range_const] at h
  have : Algebra.EssFiniteType E⟮(π : K)⟯ K := .of_comp E _ K
  have : FiniteDimensional E⟮(π : K)⟯ K :=
    Algebra.finite_of_essFiniteType_of_isAlgebraic
  have : Algebra.EssFiniteType E V' :=
    geometricDVR_essFiniteType_of_finite_curveField V' π
  let : IsScalarTower k E V' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Algebra.EssFiniteType k V' := .comp k E V'
  exact (Algebra.EssFiniteType.iff_of_algEquiv (extendScalarsOfLEEquiv V E hEV)).mpr this

end SGPT.NAPotential.BJ.Pair3Div
