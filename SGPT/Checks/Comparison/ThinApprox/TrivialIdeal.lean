import SGPT.NAPotential.BerkovichIdealValue
import Mathlib.AlgebraicGeometry.FunctionField

/-! Original generic-centre and ideal values of the actual trivial valuation.
No multiplier-ideal or analytification proof is imported.
Blueprint: thin-trivial-ideal.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.NAPotential.ThinApprox.TrivialIdeal
open Set Filter
open scoped Topology ENNReal
open AlgebraicGeometry CategoryTheory IsLocalRing
open SGPT.NAPotential.Berkovich
variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} [IsIntegral X]

/-- The generic point of `X` is a centre of the trivial valuation. -/
theorem isCenter_trivial :
    (BerkovichPoint.trivial f).IsCenter (genericPoint X) := by
  classical
  have hsp : (BerkovichPoint.trivial f).support ⤳ genericPoint X := by
    rw [BerkovichPoint.trivial_support]
  refine ⟨hsp, fun g => ?_, fun g hg => ?_⟩
  · by_cases h0 : (BerkovichPoint.specializationMap hsp).hom g = 0
    · rw [h0, BerkovichPoint.valAt_zero]
      exact le_top
    · exact le_of_eq (BerkovichPoint.trivial_valAt_of_ne_zero h0).symm
  · have hF : IsField (X.presheaf.stalk (genericPoint X)) :=
      Semifield.toIsField (X.presheaf.stalk (genericPoint X))
    have hg0 : g = 0 := by
      have hbot : maximalIdeal (X.presheaf.stalk (genericPoint X)) = ⊥ :=
        isField_iff_maximalIdeal_eq.mp hF
      rw [hbot] at hg
      exact hg
    rw [hg0, map_zero, BerkovichPoint.valAt_zero]
    exact lt_of_le_of_ne le_top WithTop.zero_ne_top

variable [IsProper f]

/-- The centre of the trivial valuation is the generic point of `X`. -/
theorem center_trivial :
    (BerkovichPoint.trivial f).center = genericPoint X :=
  (((BerkovichPoint.trivial f).isCenter_iff_eq_center _).mp isCenter_trivial).symm

/-- A nonzero ideal sheaf of the integral scheme `X` has a nonzero germ at the generic point. -/
theorem stalkIdeal_genericPoint_eq_top {𝔞 : X.IdealSheafData} (h𝔞 : 𝔞 ≠ ⊥) :
    stalkIdeal 𝔞 (genericPoint X) = ⊤ := by
  have hex : ∃ U : X.affineOpens, 𝔞.ideal U ≠ ⊥ := by
    by_contra hcon
    push Not at hcon
    apply h𝔞
    ext U : 2
    rw [hcon U, Scheme.IdealSheafData.ideal_bot]
    rfl
  obtain ⟨U, hU⟩ := hex
  obtain ⟨r, hr, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU
  have hne : ((U : X.Opens) : Set X).Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    have hsub : Subsingleton Γ(X, (U : X.Opens)) := by
      have hbot : (U : X.Opens) = ⊥ := TopologicalSpace.Opens.ext hemp
      rw [hbot]
      exact CommRingCat.subsingleton_of_isTerminal X.sheaf.isTerminalOfEmpty
    exact hr0 (Subsingleton.elim _ _)
  have hη : genericPoint X ∈ (U : X.Opens) :=
    ((genericPoint_spec X).mem_open_set_iff (U : X.Opens).isOpen).mpr
      (by simpa only [Set.univ_inter] using hne)
  have hgerm : (X.presheaf.germ U (genericPoint X) hη).hom r ≠ 0 := by
    intro h0
    exact hr0 (germ_injective_of_isIntegral X (genericPoint X) hη (h0.trans (map_zero _).symm))
  have hmem := germ_mem_stalkIdeal 𝔞 U hη hr
  have hF : IsField (X.presheaf.stalk (genericPoint X)) :=
    Semifield.toIsField (X.presheaf.stalk (genericPoint X))
  exact Ideal.eq_top_of_isUnit_mem _ hmem
    (isUnit_iff_ne_zero.mpr hgerm)

variable [IsLocallyNoetherian X]

/-- `v_triv(𝔞) = 0` for every nonzero ideal sheaf `𝔞`. -/
theorem trivial_idealVal_eq_zero {𝔞 : X.IdealSheafData} (h𝔞 : 𝔞 ≠ ⊥) :
    (BerkovichPoint.trivial f).idealVal 𝔞 = 0 := by
  rw [BerkovichPoint.idealVal_eq_zero_iff, center_trivial]
  exact stalkIdeal_genericPoint_eq_top h𝔞


end SGPT.NAPotential.ThinApprox.TrivialIdeal
