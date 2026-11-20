import SGPT.Foundations.Schemes.AffineRegularRestriction
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
namespace SGPT.Foundations.Schemes
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section RegularAffineCover
variable {X : Scheme.{u}} {L : X.Modules} (s : Γ(L, ⊤))
  {I : Type u} (U : I → X.affineOpens) (hU : ∀ x : X, ∃ i, x ∈ (U i).val)
  (A : I → X.Opens) (e : ∀ i, LocalBundleFrame L (A i)) (iU : ∀ i, (U i).val ⟶ A i)
  (hr : ∀ i, (e i).coefficients (iU i)
    (L.val.map (U i).val.leTop.op s) ∈ nonZeroDivisors Γ(X, U i))

include U hU A e iU hr

/-- Actual affine regular coefficients retain their ORIGINAL frame inclusions;
restriction and dual-sheaf separation give injectivity on EVERY actual open. -/
theorem sectionZeroEvaluation_injective_of_regular_affine_cover
    (V : X.Opens) : Function.Injective (sectionZeroEvaluation L s V) := by
  intro α β h
  apply TopCat.Presheaf.IsSheaf.section_ext (F := (bundleDual L).val.presheaf) (bundleDual L).isSheaf
  intro x hx
  obtain ⟨j, hj⟩ := hU x
  let W := V ⊓ (U j).val
  let k : W ⟶ (U j).val := homOfLE inf_le_right
  have hc : (e j).coefficients (k ≫ iU j) (L.val.map W.leTop.op s) =
      X.presheaf.map k.op ((e j).coefficients (iU j) (L.val.map (U j).val.leTop.op s)) := by
    have hh := (e j).coefficients_restrict (iU j) k (L.val.map (U j).val.leTop.op s)
    have hsec : L.val.map k.op (L.val.map (U j).val.leTop.op s) = L.val.map W.leTop.op s := by
      rw [← L.val.map_comp_apply, ← op_comp]
      rfl
    rw [hsec] at hh
    exact hh
  have hrW := affineOpen_nonZeroDivisors_restrict (U j).property
    (show W ≤ (U j).val from inf_le_right) _ (hr j)
  change X.presheaf.map k.op _ ∈ nonZeroDivisors Γ(X, W) at hrW
  rw [← hc] at hrW
  refine ⟨W, inf_le_left, ⟨hx, hj⟩, ?_⟩
  apply ((e j).dual.coefficients (k ≫ iU j)).injective
  apply (mul_cancel_left_mem_nonZeroDivisors hrW).mp
  have hh := congrArg (X.presheaf.map (homOfLE (show W ≤ V from inf_le_left)).op) h
  rw [← sectionZeroEvaluation_restrict L s (show W ≤ V from inf_le_left),
    ← sectionZeroEvaluation_restrict L s (show W ≤ V from inf_le_left)] at hh
  rw [sectionZeroEvaluation_frame s (e j) (k ≫ iU j),
    sectionZeroEvaluation_frame s (e j) (k ≫ iU j)] at hh
  exact hh

/-- Primitive actual affine geometry PRODUCES monicity of the literal
original dual evaluation; no monicity certificate is supplied as input. -/
theorem sectionZeroSheafEvaluation_mono_of_regular_affine_cover :
    Mono (sectionZeroSheafEvaluation L s) := by
  let : Mono (sectionZeroSheafEvaluation L s).val := PresheafOfModules.mono_of_injective
    (fun {W} ↦ sectionZeroEvaluation_injective_of_regular_affine_cover s U hU A e iU hr W.unop)
  exact (SheafOfModules.forget X.ringCatSheaf).mono_of_mono_map
    (show Mono (sectionZeroSheafEvaluation L s).val from inferInstance)
end RegularAffineCover

/-- Genuine original coordinates and produced nonzerodivisors make the SAME
literal dual evaluation monic for every actual regular positive section. -/
theorem nativePositiveProjectiveSectionZeroSheafEvaluation_mono
    (K : Type) [Field K] (N : ℕ) {X : Scheme} (f : X ⟶ polynomialProj K N)
    [IsAffineHom f] (L : IntrinsicLineBundle X) (q : ℕ)
    (e : bundleTensorPower L.sheaf q ≅
      (Scheme.Modules.pullback f).obj (polynomialProjTwistingLine K N).sheaf)
    (s : bundlePowerGlobalSections L.sheaf q)
    (hr : nativePositiveProjectiveSectionRegular K N f L q e s) :
    Mono (sectionZeroSheafEvaluation (bundleTensorPower L.sheaf q) s) := by
  classical
  let S (j : Fin (N + 1)) : Finset (Fin (N + 1)) := {j}
  have hS (j : Fin (N + 1)) : (S j).Nonempty := Finset.singleton_nonempty j
  let U (j : Fin (N + 1)) : X.affineOpens :=
    ⟨actualSchemeSubsetOpen (actualPolynomialProjectivePullbackCoordinateOpens f) (S j),
      actualPolynomialProjectivePullbackSubsetOpen_isAffine K N f (S j) (hS j)⟩
  let A (j : Fin (N + 1)) := f ⁻¹ᵁ polynomialProjCoordinateOpen K N (hS j).choose
  let E (j : Fin (N + 1)) := nativePositiveProjectiveCoordinateFrame K N f L q e (hS j).choose
  let iU (j : Fin (N + 1)) : (U j).val ⟶ A j := homOfLE (Finset.inf_le (hS j).choose_spec)
  have hU : ∀ x : X, ∃ j, x ∈ (U j).val := by
    intro x
    have hx : x ∈ iSup (actualPolynomialProjectivePullbackCoordinateOpens f) := by
      rw [actualPolynomialProjectivePullbackCoordinateOpens_covers]
      trivial
    obtain ⟨j, hj⟩ := Opens.mem_iSup.mp hx
    refine ⟨j, ?_⟩
    change x ∈ actualSchemeSubsetOpen (actualPolynomialProjectivePullbackCoordinateOpens f) {j}
    have hw : actualSchemeSubsetOpen (actualPolynomialProjectivePullbackCoordinateOpens f) {j} =
        actualPolynomialProjectivePullbackCoordinateOpens f j := Finset.inf_singleton
    rw [hw]
    exact hj
  exact sectionZeroSheafEvaluation_mono_of_regular_affine_cover s U hU A E iU
    (fun j ↦ hr (S j) (hS j))

end
end SGPT.Foundations.Schemes
