import SGPT.Checks.Comparison.BJPair3DivGeometricDVRRestriction

-- Lane BJ-PAIR (R5/thm:pshdetbydiv bridge): ported from `SGPT.Checks.Literature/SGPT.Checks.Literature/BJDivisorial/DVRLocalPresentation.lean`
-- (that library pins another SGPT.Foundations.Envelope revision and cannot be imported here); only the
-- imports, the `Alterations` namespace (now `SGPT.Support.Alterations`) and this file's namespace
-- (`Divisorial` -> `Pair3Div`, `ExternalClassStability` -> `Pair3ClassStability`) are changed.

/-! # A genuine local stalk containing the actual finite DVR presentation
This algebraic lemma is applied to the canonical local stalk map of the
constructed trait. The original DVR is the actual localization of its
finite-type presentation. Locality alone supplies the denominators inside
the stalk, hence surjectivity of that canonical map.
-/
noncomputable section

namespace SGPT.NAPotential.BJ.Pair3Div

variable {A R V : Type*} [CommRing A] [CommRing R] [CommRing V]
  [Algebra A R] [Algebra A V]

/-- A genuine local ring map whose source contains the actual presentation
of the localized target is surjective. No stalk equality certificate is used. -/
theorem localMap_surjective_of_localization (S : Submonoid A) [IsLocalization S V]
    (f : R →+* V) [IsLocalHom f]
    (hf : f.comp (algebraMap A R) = algebraMap A V) : Function.Surjective f := by
  have hu (s : S) : IsUnit (algebraMap A R s) := by
    apply isUnit_of_map_unit f
    have h := IsLocalization.map_units V s
    rw [← hf] at h
    exact h
  let ρ : V →+* R := IsLocalization.lift hu
  have hcomp : f.comp ρ = RingHom.id V := by
    apply IsLocalization.ringHom_ext S
    ext a
    change f (ρ (algebraMap A V a)) = algebraMap A V a
    rw [IsLocalization.lift_eq hu]
    exact RingHom.congr_fun hf a
  intro v
  exact ⟨ρ v, RingHom.congr_fun hcomp v⟩

end SGPT.NAPotential.BJ.Pair3Div
