import SGPT.Projective.OriginalNormalizedCurveZero
import SGPT.Foundations.Schemes.DiscreteLineStalkSections
import SGPT.Foundations.Schemes.ArtinianProjectiveStalkLength

/-! Actual original open sections of an ENTIRE Artinian scheme are the
product of its SAME actual stalks, with literal original structural scalars.
Blueprint: original-artinian-open-stalks.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes TopologicalSpace Opposite
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Literal actual original open germ map, with original complex scalars. -/
def originalDiscreteOpenStalkLinear {Y : Scheme.{0}} [DiscreteTopology Y]
    (g : Y ⟶ Spec (.of ℂ)) (W : Y.Opens) :
    letI := affineChartAlgebra g W
    letI : ∀ z : W, Algebra ℂ (Y.presheaf.stalk z.val) :=
      fun z => schemeStalkGlobalConstantsAlgebra (schemeGlobalConstants g) z.val
    Γ(Y,W) →ₗ[ℂ] (∀ z : W,Y.presheaf.stalk z.val) := by
  let := affineChartAlgebra g W
  let : ∀ z : W, Algebra ℂ (Y.presheaf.stalk z.val) :=
    fun z => schemeStalkGlobalConstantsAlgebra (schemeGlobalConstants g) z.val
  exact {
    toFun := fun s z => Y.presheaf.germ W z.val z.property s
    map_add' := by intro s t; funext z; exact map_add _ _ _
    map_smul' := by
      intro c s
      funext z
      change Y.presheaf.germ W z.val z.property
        (Y.presheaf.map W.leTop.op (schemeGlobalConstants g c) * s) =
          Y.presheaf.Γgerm z.val (schemeGlobalConstants g c) *
            Y.presheaf.germ W z.val z.property s
      rw [map_mul,Y.presheaf.Γgerm_res_apply z.val z.property] }

/-- Actual singleton inverse germs and genuine original sheaf gluing prove
bijection on EVERY original open, including the empty open. -/
theorem originalDiscreteOpenStalkLinear_bijective {Y : Scheme.{0}} [DiscreteTopology Y]
    (g : Y ⟶ Spec (.of ℂ)) (W : Y.Opens) :
    letI := affineChartAlgebra g W
    letI : ∀ z : W, Algebra ℂ (Y.presheaf.stalk z.val) :=
      fun z => schemeStalkGlobalConstantsAlgebra (schemeGlobalConstants g) z.val
    Function.Bijective (originalDiscreteOpenStalkLinear g W) := by
  classical
  let := affineChartAlgebra g W
  let : ∀ z : W, Algebra ℂ (Y.presheaf.stalk z.val) :=
    fun z => schemeStalkGlobalConstantsAlgebra (schemeGlobalConstants g) z.val
  let S (z : W) := discreteSingletonOpen Y z.val
  have hSW (z : W) : S z ≤ W := by
    intro y hy
    have hyz : y = z.val := hy
    simpa only [hyz] using z.property
  let G (z : W) := (discreteSingletonGermIso Y z.val).commRingCatIsoToRingEquiv
  constructor
  · intro s t h
    apply TopCat.Presheaf.IsSheaf.section_ext Y.sheaf.property
    intro x hx
    let z : W := ⟨x,hx⟩
    refine ⟨S z,hSW z,Set.mem_singleton x,?_⟩
    apply (G z).injective
    change Y.presheaf.germ (S z) x (Set.mem_singleton x)
        (Y.presheaf.map (homOfLE (hSW z)).op s) =
      Y.presheaf.germ (S z) x (Set.mem_singleton x)
        (Y.presheaf.map (homOfLE (hSW z)).op t)
    rw [Y.presheaf.germ_res_apply,Y.presheaf.germ_res_apply]
    exact congrFun h z
  · intro v
    let l (z : W) : Γ(Y,S z) := (G z).symm (v z)
    have hcompat : TopCat.Presheaf.IsCompatible Y.presheaf S l := by
      intro z t
      by_cases hzt : z = t
      · subst t; rfl
      · have hval : z.val ≠ t.val := fun h => hzt (Subtype.ext h)
        have hbot : S z ⊓ S t = ⊥ := by
          apply bot_unique
          intro x hx
          exact (hval ((show x=z.val from hx.1).symm.trans (show x=t.val from hx.2))).elim
        let : Subsingleton Γ(Y,S z ⊓ S t) := CommRingCat.subsingleton_of_isTerminal
          (TopCat.Sheaf.isTerminalOfEqEmpty Y.sheaf hbot)
        exact Subsingleton.elim _ _
    have hcover : W ≤ iSup S := by
      intro x hx
      exact Opens.mem_iSup.mpr ⟨⟨x,hx⟩,Set.mem_singleton x⟩
    obtain ⟨s,hs,_⟩ := Y.sheaf.existsUnique_gluing' S W (fun z => homOfLE (hSW z)) hcover l hcompat
    refine ⟨s,?_⟩
    funext z
    change Y.presheaf.germ W z.val z.property s = v z
    calc
      Y.presheaf.germ W z.val z.property s =
          G z (Y.presheaf.map (homOfLE (hSW z)).op s) :=
        (Y.presheaf.germ_res_apply (homOfLE (hSW z)) z.val (Set.mem_singleton z.val) s).symm
      _ = G z (l z) := congrArg (G z) (hs z)
      _ = v z := (G z).apply_symm_apply (v z)

/-- Actual original germ algebra with its original structural scalars. -/
def originalDiscreteOpenStalkEquiv {Y : Scheme.{0}} [DiscreteTopology Y]
    (g : Y ⟶ Spec (.of ℂ)) (W : Y.Opens) :
    letI := affineChartAlgebra g W
    letI : ∀ z : W, Algebra ℂ (Y.presheaf.stalk z.val) :=
      fun z => schemeStalkGlobalConstantsAlgebra (schemeGlobalConstants g) z.val
    Γ(Y,W) ≃ₗ[ℂ] (∀ z : W,Y.presheaf.stalk z.val) := by
  let := affineChartAlgebra g W
  let : ∀ z : W, Algebra ℂ (Y.presheaf.stalk z.val) :=
    fun z => schemeStalkGlobalConstantsAlgebra (schemeGlobalConstants g) z.val
  exact LinearEquiv.ofBijective (originalDiscreteOpenStalkLinear g W)
    (originalDiscreteOpenStalkLinear_bijective g W)

/-- Actual Artinian finite-type singleton rings manufacture true finite
complex stalk dimension, without projective/source closed-embedding input. -/
theorem originalArtinianStalk_finite {Y : Scheme.{0}} [IsArtinianScheme Y]
    (g : Y ⟶ Spec (.of ℂ)) [LocallyOfFiniteType g] (z : Y) :
    letI := schemeStalkGlobalConstantsAlgebra (schemeGlobalConstants g) z
    Module.Finite ℂ (Y.presheaf.stalk z) := by
  let := schemeStalkGlobalConstantsAlgebra (schemeGlobalConstants g) z
  let U := discreteSingletonOpen Y z
  let := affineChartAlgebra g U
  have hU : IsAffineOpen U := IsAffineOpen.of_subsingleton Set.subsingleton_singleton
  let : Algebra.FiniteType ℂ Γ(Y,U) := affineChartAlgebra_finiteType g hU
  let : IsArtinianRing Γ(Y,U) := IsLocallyArtinian.isArtinianRing_presheaf_obj ⟨U,hU⟩
  let : Module.Finite ℂ Γ(Y,U) := Module.finite_of_isArtinianRing ℂ Γ(Y,U)
  exact Module.Finite.equiv (discreteSingletonGermAlgEquiv g z).toLinearEquiv

local instance originalArtinianOpenFinite {Y : Scheme.{0}} [IsArtinianScheme Y]
    (W : Y.Opens) : Finite W :=
  Finite.of_injective (fun z : W => (z:Y)) Subtype.val_injective

/-- ANY actual open's TRUE original section dimension is the FULL finite
sum of SAME original stalk dimensions, retaining all nilpotents/empty opens. -/
theorem originalArtinianOpen_finrank_eq_stalkSum {Y : Scheme.{0}} [IsArtinianScheme Y]
    (g : Y ⟶ Spec (.of ℂ)) [LocallyOfFiniteType g] (W : Y.Opens) :
    letI := affineChartAlgebra g W
    letI : Fintype W := Fintype.ofFinite W
    letI : ∀ z : W, Algebra ℂ (Y.presheaf.stalk z.val) :=
      fun z => schemeStalkGlobalConstantsAlgebra (schemeGlobalConstants g) z.val
    Module.finrank ℂ Γ(Y,W) = ∑ z : W, Module.finrank ℂ (Y.presheaf.stalk z.val) := by
  classical
  let := affineChartAlgebra g W
  let : Fintype W := Fintype.ofFinite W
  let : ∀ z : W, Algebra ℂ (Y.presheaf.stalk z.val) :=
    fun z => schemeStalkGlobalConstantsAlgebra (schemeGlobalConstants g) z.val
  let : ∀ z : W, Module.Finite ℂ (Y.presheaf.stalk z.val) := fun z => originalArtinianStalk_finite g z.val
  exact (originalDiscreteOpenStalkEquiv g W).finrank_eq.trans
    (Module.finrank_pi_fintype (R := ℂ) (ι := W) (M := fun z : W => Y.presheaf.stalk z.val))

/-- Actual original finite-type Artinian geometry gives TRUE finite section
modules on EVERY original open, not a junk finrank convention. -/
theorem originalArtinianOpen_sections_finite {Y : Scheme.{0}} [IsArtinianScheme Y]
    (g : Y ⟶ Spec (.of ℂ)) [LocallyOfFiniteType g] (W : Y.Opens) :
    letI := affineChartAlgebra g W
    Module.Finite ℂ Γ(Y,W) := by
  let := affineChartAlgebra g W
  let : Fintype W := Fintype.ofFinite W
  let : ∀ z : W, Algebra ℂ (Y.presheaf.stalk z.val) :=
    fun z => schemeStalkGlobalConstantsAlgebra (schemeGlobalConstants g) z.val
  let : ∀ z : W, Module.Finite ℂ (Y.presheaf.stalk z.val) := fun z => originalArtinianStalk_finite g z.val
  exact Module.Finite.equiv (originalDiscreteOpenStalkEquiv g W).symm

/-- Genuine actual open/stalk dimension reader, over ALL original points
with the LITERAL membership filter; empty opens/whole schemes retained. -/
theorem originalArtinianOpen_finrank_eq_filteredStalkSum {Y : Scheme.{0}} [IsArtinianScheme Y]
    (g : Y ⟶ Spec (.of ℂ)) [LocallyOfFiniteType g] (W : Y.Opens) :
    letI := affineChartAlgebra g W
    letI : Fintype Y := Fintype.ofFinite Y
    letI : ∀ z : Y, Algebra ℂ (Y.presheaf.stalk z) :=
      fun z => schemeStalkGlobalConstantsAlgebra (schemeGlobalConstants g) z
    Module.finrank ℂ Γ(Y,W) = ∑ z : Y, if z∈W then Module.finrank ℂ (Y.presheaf.stalk z) else 0 := by
  classical
  let := affineChartAlgebra g W
  let : Fintype Y := Fintype.ofFinite Y
  let : Fintype W := Fintype.ofFinite W
  let : ∀ z : Y, Algebra ℂ (Y.presheaf.stalk z) :=
    fun z => schemeStalkGlobalConstantsAlgebra (schemeGlobalConstants g) z
  have h := originalArtinianOpen_finrank_eq_stalkSum g W
  refine h.trans ?_
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype (Finset.univ.filter (fun z : Y => z∈W)) (by simp)
    (fun z : Y => Module.finrank ℂ (Y.presheaf.stalk z))).symm

/-- TRUE FULL actual local-ring length equals SAME original complex
stalk dimension, with residue-field scalar bijectivity manufactured. -/
theorem originalArtinianStalk_length_eq_finrank {Y : Scheme.{0}} [IsArtinianScheme Y]
    (g : Y ⟶ Spec (.of ℂ)) [LocallyOfFiniteType g] (z : Y) :
    letI := schemeStalkGlobalConstantsAlgebra (schemeGlobalConstants g) z
    Module.length (Y.presheaf.stalk z) (Y.presheaf.stalk z) =
      (Module.finrank ℂ (Y.presheaf.stalk z) : ℕ∞) := by
  let := schemeStalkGlobalConstantsAlgebra (schemeGlobalConstants g) z
  let := originalArtinianStalk_finite g z
  let : Module.Finite ℂ (IsLocalRing.ResidueField (Y.presheaf.stalk z)) :=
    Module.Finite.trans (Y.presheaf.stalk z) (IsLocalRing.ResidueField (Y.presheaf.stalk z))
  exact local_length_eq_finrank_of_residue_bijective
    (K := ℂ) (A := Y.presheaf.stalk z) (M := Y.presheaf.stalk z)
    IsAlgClosed.algebraMap_bijective_of_isIntegral

end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
