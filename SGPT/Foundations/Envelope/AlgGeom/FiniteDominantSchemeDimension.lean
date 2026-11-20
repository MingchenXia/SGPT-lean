import SGPT.Foundations.Envelope.AlgGeom.IntegralSchemeDimension
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # Actual finite dominant maps descend whole original scheme dimension -/
open AlgebraicGeometry CategoryTheory TopologicalSpace
noncomputable section
universe u
namespace SGPT.Foundations.Envelope.FiniteDominantSchemeDimension
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The SAME original finite dominant map DERIVES the WHOLE original target
dimension bound from the actual original source, using genuine original prime going-up.
No normality, flatness or target-dimension premise. -/
theorem target_dimension_le {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (p : Y ⟶ X) [IsFinite p] [IsDominant p] (d : ℕ)
    (hdim : topologicalKrullDim Y ≤ d) : topologicalKrullDim X ≤ d := by
  let : IsSchemeTheoreticallyDominant p := IsSchemeTheoreticallyDominant.of_isDominant p
  change Order.krullDim (IrreducibleCloseds X) ≤ d
  rw [Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X)),
    Order.krullDim_eq_iSup_coheight]
  refine iSup_le fun x => ?_
  obtain ⟨U, hU, hx, _hUtop⟩ := exists_isAffineOpen_mem_and_subset
    (show x ∈ (⊤ : X.Opens) from trivial)
  let V := p ⁻¹ᵁ U
  have hV : IsAffineOpen V := hU.preimage p
  let a : Spec Γ(X, U) := hU.primeIdealOf ⟨x, hx⟩
  have ha : hU.fromSpec a = x := hU.fromSpec_primeIdealOf ⟨x, hx⟩
  rw [← ha, coheight_eq_of_isOpenImmersion hU.fromSpec]
  have hB : ringKrullDim Γ(Y, V) ≤ d := by
    have h := hV.fromSpec.isOpenEmbedding.isEmbedding.isInducing.topologicalKrullDim_le.trans hdim
    change topologicalKrullDim (PrimeSpectrum Γ(Y, V)) ≤ d at h
    rwa [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim] at h
  have hA : ringKrullDim Γ(X, U) ≤ d :=
    (IntegralSchemeDimension.ringKrullDim_le_of_isIntegral_of_injective (p.app U).hom
      (p.isIntegral_app U hU) (p.app_injective U)).trans hB
  have ho : Order.krullDim (Spec Γ(X, U)) ≤ d := by
    rw [← Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := Spec Γ(X, U)))]
    change topologicalKrullDim (PrimeSpectrum Γ(X, U)) ≤ d
    rwa [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  exact (Order.coheight_le_krullDim a).trans ho

end SGPT.Foundations.Envelope.FiniteDominantSchemeDimension
