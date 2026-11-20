import SGPT.NAPotential.ProjectiveGraphStalkNaturality

/-!
# Actual generic pullback commutes with actual composition and restriction

The proof uses actual generic section representatives and native comp_app;
no function-field equivalence or pullback square is supplied as a certificate.
Blueprint: `projective-graph-pullback-composition.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.NAPotential.AlgPrimes3.ProjectiveGraphPullbackComposition

open CategoryTheory AlgebraicGeometry ProjectiveGraphStalkNaturality

variable {X M N : Scheme.{0}} [IsIntegral X] [IsIntegral M] [IsIntegral N]

/-- An actual original generic germ pulls back to the germ of the actual original pulled-back section. -/
theorem genericPullback_germ (ρ : M ⟶ X) (hρ : ρ (genericPoint M) = genericPoint X)
    (U : X.Opens) (hU : genericPoint X ∈ U) (a : Γ(X, U)) :
    genericPullback ρ hρ (X.presheaf.germ U (genericPoint X) hU a) =
      M.presheaf.germ (ρ ⁻¹ᵁ U) (genericPoint M) (show ρ (genericPoint M) ∈ U by rw [hρ]; exact hU)
        (ρ.app U a) := by
  have hcast : (X.presheaf.stalkCongr (.of_eq hρ.symm)).hom (X.presheaf.germ U (genericPoint X) hU a) =
      X.presheaf.germ U (ρ (genericPoint M)) (by rw [hρ]; exact hU) a :=
    X.presheaf.germ_stalkSpecializes_apply hU (Inseparable.of_eq hρ.symm).ge a
  change ρ.stalkMap (genericPoint M)
    ((X.presheaf.stalkCongr (.of_eq hρ.symm)).hom (X.presheaf.germ U (genericPoint X) hU a)) = _
  rw [hcast, Scheme.Hom.germ_stalkMap_apply]

/-- **Actual native generic pullback composition**, hence actual smooth-open restriction compatibility. -/
theorem genericPullback_comp (ρ : M ⟶ X) (ν : N ⟶ M)
    (hρ : ρ (genericPoint M) = genericPoint X) (hν : ν (genericPoint N) = genericPoint M) :
    genericPullback (ν ≫ ρ) (by change ρ (ν (genericPoint N)) = _; rw [hν, hρ]) =
      (genericPullback ν hν).comp (genericPullback ρ hρ) := by
  ext g
  obtain ⟨U, hU, a, ha⟩ := X.presheaf.exists_germ_eq g
  rw [← ha, RingHom.comp_apply, genericPullback_germ, genericPullback_germ, genericPullback_germ]
  simp only [Scheme.Hom.comp_app, CommRingCat.comp_apply, Scheme.Hom.comp_preimage]

end SGPT.NAPotential.AlgPrimes3.ProjectiveGraphPullbackComposition
