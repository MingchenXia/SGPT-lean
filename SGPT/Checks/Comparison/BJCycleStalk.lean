import SGPT.Checks.Comparison.BJProjRank
import SGPT.Foundations.Envelope.AlgGeom.SchemeLocalPointFrameSections
import SGPT.Support.Principalization.Scheme.Smooth.SubschemeStalk

/-!
# Lengths of stalks of sheaves of modules

Towards the cycle lower bound `CycleLowerBound` of `bjAppSeq_of_cycleLowerBound` (book
`thm:BJappseq`, [BJ22, Cor. 12.18]): the multiplicity of a coherent sheaf along a point `x` is the
length of its stalk over the local ring `𝒪_{X,x}`. Blueprint: `claude-bj-cycle.tex`.

Main results:

* `stalkLength M x`: the length of the stalk `M_x` as an `𝒪_{X,x}`-module;
* `stalkLength_shortExact`: it is additive in short exact sequences of quasi-coherent sheaves;
* `stalkLength_pushforward_eq_zero`: it vanishes for push-forwards from closed subschemes not
  containing `x`;
* `stalkLength_pushforward_le_one`: **the stalk of the push-forward of an invertible sheaf on an
  integral closed subscheme `Z`, at the generic point of `Z`, has length at most one** (it is a
  one-dimensional vector space over the residue field);
* `stalkLength_unit`: the stalk of `𝒪_X` has the length of the local ring `𝒪_{X,x}`;
* `length_stalk_subscheme`: for the closed subscheme `V(I)` and a point `z` of it, the local ring
  `𝒪_{V(I),z}` has the length of `𝒪_{X,x} / I_x` over `𝒪_{X,x}`, `x` the image of `z`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Scheme.Modules

universe u

namespace SGPT.NAPotential.BJCycle

open SGPT.Foundations.Envelope SGPT.Foundations.Envelope.SchemeModuleStalkLinearity SGPT.NAPotential.BJProj

variable {X : Scheme.{u}}

/-! ### The length of a stalk -/

/-- The length of the stalk `M_x` of a sheaf of modules over the local ring `𝒪_{X,x}`. -/
def stalkLength (M : X.Modules) (x : X) : ℕ∞ :=
  Module.length (X.presheaf.stalk x) (M.presheaf.stalk x)

/-- Lengths of stalks at equal points agree. -/
theorem stalkLength_congr (M : X.Modules) {x y : X} (h : x = y) :
    stalkLength M x = stalkLength M y := by
  subst h
  rfl

/-- The stalks of a zero sheaf have length zero. -/
theorem stalkLength_eq_zero_of_isZero (M : X.Modules) (hM : IsZero M) (x : X) :
    stalkLength M x = 0 := by
  have := stalk_subsingleton_of_isZero M hM x
  exact Module.length_eq_zero

/-- Isomorphic sheaves have stalks of the same length. -/
theorem stalkLength_of_iso {M N : X.Modules} (e : M ≅ N) (x : X) :
    stalkLength M x = stalkLength N x :=
  (stalkLinearEquiv e x).length_eq

/-- **Additivity of stalk lengths** in short exact sequences of quasi-coherent sheaves. -/
theorem stalkLength_shortExact (S : ShortComplex X.Modules) (hS : S.ShortExact)
    [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent] (x : X) :
    stalkLength S.X₂ x = stalkLength S.X₁ x + stalkLength S.X₃ x := by
  have := hS.mono_f
  have := hS.epi_g
  exact Module.length_eq_add_of_exact (stalkMapLinear S.f x) (stalkMapLinear S.g x)
    (stalkMapLinear_injective_of_mono S.f x) (stalkMapLinear_surjective_of_epi S.g x)
    (LinearMap.exact_iff.mpr (stalkMapLinear_exact S hS x))

/-- The stalk of a push-forward at a point outside the closed image has length zero. -/
theorem stalkLength_pushforward_eq_zero {Z : Scheme.{u}} (i : Z ⟶ X)
    (hi : IsClosed (Set.range i)) (T : Z.Modules) (x : X) (hx : x ∉ Set.range i) :
    stalkLength ((Scheme.Modules.pushforward i).obj T) x = 0 := by
  have := stalk_pushforward_subsingleton i hi T x hx
  exact Module.length_eq_zero

/-! ### Stalks of push-forwards from integral closed subschemes -/

/-- The comparison of the stalk of a push-forward with the stalk upstairs is semilinear along the
stalk map. -/
theorem stalkPushforward_smul {Z : Scheme.{u}} (i : Z ⟶ X) (T : Z.Modules) (z : Z)
    (a : X.presheaf.stalk (i z))
    (m : ((Scheme.Modules.pushforward i).obj T).presheaf.stalk (i z)) :
    T.presheaf.stalkPushforward AddCommGrpCat i.base z (a • m) =
      i.stalkMap z a • T.presheaf.stalkPushforward AddCommGrpCat i.base z m := by
  obtain ⟨U, hxU, r, rfl⟩ := X.presheaf.exists_germ_eq a
  obtain ⟨V, hVU, hxV, s, rfl⟩ :=
    ((Scheme.Modules.pushforward i).obj T).presheaf.exists_le_germ_eq m hxU
  rw [← X.presheaf.germ_res_apply (homOfLE hVU) (i z) hxV r]
  erw [← PresheafOfModules.germ_smul (R := X.presheaf)
    ((Scheme.Modules.pushforward i).obj T).val (i z) V hxV]
  erw [TopCat.Presheaf.stalkPushforward_germ_apply, TopCat.Presheaf.stalkPushforward_germ_apply,
    Scheme.Hom.germ_stalkMap_apply]
  erw [← PresheafOfModules.germ_smul (R := Z.presheaf) T.val z (i ⁻¹ᵁ V) hxV]
  rfl

/-- **The stalk at the generic point of a push-forward from an integral closed subscheme has
length at most one**: for `i : Z ⟶ X` a closed immersion with `Z` integral and `T` invertible on
`Z`, the stalk of `i_* T` at the image of the generic point of `Z` is a one-dimensional vector space
over the function field of `Z`, on which `𝒪_{X, i(η)}` acts through the surjection onto it. -/
theorem stalkLength_pushforward_le_one {Z : Scheme.{u}} [IsIntegral Z] (i : Z ⟶ X)
    [IsClosedImmersion i] (T : Z.Modules) (hT : IsInvertible T) :
    stalkLength ((Scheme.Modules.pushforward i).obj T) (i (genericPoint Z)) ≤ 1 := by
  let P := (Scheme.Modules.pushforward i).obj T
  let q := T.presheaf.stalkPushforward AddCommGrpCat i.base (genericPoint Z)
  have hq : IsIso q := TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing
    AddCommGrpCat i.isClosedEmbedding.isInducing T.presheaf (genericPoint Z)
  have hbij : Function.Bijective q := (ConcreteCategory.isIso_iff_bijective q).mp hq
  have hrank : Module.finrank Z.functionField (CanonicalGeometry.genericBundleFiber T) = 1 :=
    Module.finrank_eq_of_rank_eq (by
      rw [rank_genericFiber_of_isInvertible T hT]
      rfl)
  by_cases hsub : Subsingleton (P.presheaf.stalk (i (genericPoint Z)))
  · rw [stalkLength, Module.length_eq_zero]
    exact zero_le_one
  · rw [not_subsingleton_iff_nontrivial] at hsub
    have hsimple : IsSimpleModule (X.presheaf.stalk (i (genericPoint Z)))
        (P.presheaf.stalk (i (genericPoint Z))) := by
      refine isSimpleModule_iff_toSpanSingleton_surjective.mpr ⟨hsub, fun m hm w => ?_⟩
      have hqm : q m ≠ 0 := by
        intro h0
        apply hm
        apply hbij.1
        rw [h0, map_zero]
      obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (K := Z.functionField)
        (V := CanonicalGeometry.genericBundleFiber T) (q m) hqm).mp hrank (q w)
      obtain ⟨a, ha⟩ := i.stalkMap_surjective (genericPoint Z) c
      refine ⟨a, ?_⟩
      apply hbij.1
      change q (a • m) = q w
      rw [stalkPushforward_smul, ha]
      exact hc
    rw [stalkLength, Module.length_eq_one]

/-! ### The structure sheaf -/

/-- The stalk of the structure sheaf, as a module over the local ring, is the local ring. -/
def unitStalkLinearEquiv (x : X) :
    (unitObj X).presheaf.stalk x ≃ₗ[X.presheaf.stalk x] X.presheaf.stalk x where
  toFun m := (SchemeLocalPointFrameSections.unitStalkRingIso x).hom m
  invFun m := (SchemeLocalPointFrameSections.unitStalkRingIso x).inv m
  left_inv m := by
    change ((SchemeLocalPointFrameSections.unitStalkRingIso x).hom ≫
      (SchemeLocalPointFrameSections.unitStalkRingIso x).inv) m = m
    rw [Iso.hom_inv_id]
    rfl
  right_inv m := by
    change ((SchemeLocalPointFrameSections.unitStalkRingIso x).inv ≫
      (SchemeLocalPointFrameSections.unitStalkRingIso x).hom) m = m
    rw [Iso.inv_hom_id]
    rfl
  map_add' m m' := map_add _ m m'
  map_smul' a m := by
    obtain ⟨U, hxU, r, rfl⟩ := X.presheaf.exists_germ_eq a
    obtain ⟨V, hVU, hxV, s, rfl⟩ := (unitObj X).presheaf.exists_le_germ_eq m hxU
    rw [← X.presheaf.germ_res_apply (homOfLE hVU) x hxV r]
    erw [← PresheafOfModules.germ_smul (R := X.presheaf) (unitObj X).val x V hxV]
    erw [SchemeLocalPointFrameSections.unitStalkRingIso_germ,
      SchemeLocalPointFrameSections.unitStalkRingIso_germ]
    exact map_mul (X.presheaf.germ V x hxV).hom _ _

/-- The stalk of `𝒪_X` has the length of the local ring. -/
theorem stalkLength_unit (x : X) :
    stalkLength (unitObj X) x = Module.length (X.presheaf.stalk x) (X.presheaf.stalk x) :=
  (unitStalkLinearEquiv x).length_eq

/-- **The local ring of a closed subscheme**: for an ideal sheaf `I` and a point `z` of `V(I)`
over `x`, the length of `𝒪_{V(I),z}` (over itself) is the length of `𝒪_{X,x} / I_x` over
`𝒪_{X,x}`. -/
theorem length_stalk_subscheme (I : X.IdealSheafData) (z : I.subscheme) :
    Module.length (I.subscheme.presheaf.stalk z) (I.subscheme.presheaf.stalk z) =
      Module.length (X.presheaf.stalk (I.subschemeι z))
        (X.presheaf.stalk (I.subschemeι z) ⧸ I.stalkIdeal (I.subschemeι z)) := by
  let φ := (I.subschemeι.stalkMap z).hom
  have hφ : Function.Surjective φ := I.subschemeι.stalkMap_surjective z
  let : Algebra (X.presheaf.stalk (I.subschemeι z)) (I.subscheme.presheaf.stalk z) :=
    φ.toAlgebra
  let f : X.presheaf.stalk (I.subschemeι z) →ₐ[X.presheaf.stalk (I.subschemeι z)]
      I.subscheme.presheaf.stalk z := Algebra.ofId _ _
  have hf : Function.Surjective f := hφ
  have hker : RingHom.ker f = I.stalkIdeal (I.subschemeι z) := I.ker_stalkMap_subschemeι z
  let e := (Ideal.quotientEquivAlgOfEq (X.presheaf.stalk (I.subschemeι z)) hker.symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective hf)
  rw [e.toLinearEquiv.length_eq, Module.length_eq_of_surjective hφ]

end SGPT.NAPotential.BJCycle
