import SGPT.Checks.Comparison.BJIntersectCut
import SGPT.Foundations.Envelope.Vanishing.NadelAuxiliaryBranchSections
import SGPT.Foundations.Envelope.Vanishing.NadelBlowupCanonicalIdealProduct
import SGPT.Foundations.Envelope.Vanishing.NadelBlowupCanonicalIdealPowers
import SGPT.Foundations.Envelope.AlgGeom.LineSectionZeroIdealDual
import SGPT.Foundations.Envelope.AlgGeom.CartierDualEvaluation
import SGPT.Foundations.Envelope.AlgGeom.CurveLineZeroSections
import SGPT.Foundations.Envelope.AlgGeom.SchemeGlobalPullbackCartierRatio
import SGPT.Support.Principalization.Scheme.IdealSheaf.StalkLe

/-!
# Line bundles of Cartier divisors and their Picard classes

For an invertible ideal sheaf `I` (an effective Cartier divisor `E`) we construct the invertible
sheaf `𝒪(E) = cartierLine I` (the dual of `I`) with a section `cartierSection I` whose zero ideal
is exactly `I` (`zeroIdeal_cartierSection`). On an integral scheme, the Picard class of an
invertible sheaf `L` with a nonzero section `s` is determined by the zero ideal of `s`
(`lineCls_zeroIdeal_toModules`); when that ideal is `∏ I_j ^ d_j`, we get
`[L] = ∑ d_j [𝒪(E_j)]` in `Pic X` (`lineCls_eq_sum_cartierLine`) and in `Pic(X)_ℚ`
(`picQ_eq_sum_cartierLine`). We also record that the pull-back of `ℚ`-classes is computed by
pulling back representatives (`picPullbackQ_picQ`), and that a line bundle with a section not
vanishing on the image of a morphism is trivial after pull-back (`nonempty_pullback_iso_unit`).

These are steps (b) and the bookkeeping of the reduction of the Hodge-type inequality
(blueprint `claude-bj-hodge.tex`).
-/

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open Scheme.Modules TopologicalSpace
open scoped TensorProduct

universe u

namespace SGPT.NAPotential.BJHodge

open SGPT.Foundations.Envelope SGPT.NAPotential.BJIntersect
open SGPT.Foundations.Envelope.Vanishing.NadelAuxiliaryBranchSections

attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory

variable {X : Scheme.{u}}

/-! ### Zero ideals of nowhere vanishing sections -/

/-- The unit section of the structure sheaf vanishes nowhere. -/
theorem zeroIdeal_unitObj_id :
    LineSectionZeroIdeal.zeroIdeal (unitObj X) isInvertible_unit (𝟙 (unitObj X)) = ⊤ := by
  ext U : 2
  rw [LineSectionZeroIdeal.zeroIdeal_ideal_of_frame (unitObj X) isInvertible_unit
    (𝟙 (unitObj X)) U (Iso.refl _)]
  change Ideal.span {(1 : Γ(X, U.1))} = ⊤
  exact Ideal.span_singleton_one

/-- A section which is an isomorphism vanishes nowhere. -/
theorem zeroIdeal_eq_top_of_isIso (L : X.Modules) (hL : IsInvertible L)
    (s : unitObj X ⟶ L) [IsIso s] : LineSectionZeroIdeal.zeroIdeal L hL s = ⊤ := by
  rw [Vanishing.NadelBertiniFibreIdeals.zeroIdeal_iso L (unitObj X) hL isInvertible_unit
    (asIso s).symm s]
  simp only [Iso.symm_hom, asIso_inv, IsIso.hom_inv_id]
  exact zeroIdeal_unitObj_id

/-! ### The line bundle of a Cartier divisor -/

/-- The commutativity of the explicit tensor product of sheaves of modules. -/
def tensorObjComm (M N : X.Modules) : Scheme.Modules.tensorObj M N ≅ Scheme.Modules.tensorObj N M :=
  (SGPT.Support.ModularCurves.monoidalTensorObjIso M N).symm ≪≫ β_ M N ≪≫ SGPT.Support.ModularCurves.monoidalTensorObjIso N M

/-- The invertible sheaf `𝒪(E)` of an effective Cartier divisor `E` with ideal `I`: the dual of
`I`. -/
abbrev cartierLine (I : X.IdealSheafData) : X.Modules := dualObj I.toModules

/-- `𝒪(E)` is invertible. -/
theorem cartierLine_isInvertible {I : X.IdealSheafData} (hI : I.IsInvertible) :
    IsInvertible (cartierLine I) :=
  hI.isInvertibleModule_toModules.dual

/-- The canonical section of `𝒪(E)`. -/
def cartierSection (I : X.IdealSheafData) (hI : I.IsInvertible) : unitObj X ⟶ cartierLine I :=
  branchSection (cartierLine I) I
    (hI.isInvertibleModule_toModules.evaluationIso.inv ≫ (tensorObjComm _ _).hom)

/-- The canonical section of `𝒪(E)` cuts out `E`. -/
theorem zeroIdeal_cartierSection (I : X.IdealSheafData) (hI : I.IsInvertible) :
    LineSectionZeroIdeal.zeroIdeal (cartierLine I) (cartierLine_isInvertible hI)
      (cartierSection I hI) = I := by
  rw [cartierSection, zeroIdeal_branch (cartierLine I) (cartierLine_isInvertible hI) I hI,
    zeroIdeal_eq_top_of_isIso, ← Scheme.IdealSheafData.one_eq_top, mul_one]

/-! ### Picard classes -/

/-- `[M] + [M^∨] = 0` in `Pic X`. -/
theorem lineCls_add_dual {M : X.Modules} (hM : IsInvertible M) :
    lineCls ⟨M, hM⟩ + lineCls ⟨dualObj M, hM.dual⟩ = 0 := by
  have hMD : IsInvertible (M ⊗ dualObj M) :=
    (hM.tensorObj hM.dual).of_iso (SGPT.Support.ModularCurves.monoidalTensorObjIso M (dualObj M))
  rw [← lineCls_tensor hM hM.dual hMD, ← lineCls_unit (X := X)]
  exact lineCls_eq_of_iso _ _
    (hM.monoidalEvaluationIso ≪≫ SGPT.Support.ModularCurves.monoidalUnitObjIso X)

/-- The class of the zero ideal of a nonzero section is minus the class of the line bundle. -/
theorem lineCls_zeroIdeal_toModules [IsIntegral X] (L : X.Modules) (hL : IsInvertible L)
    (s : unitObj X ⟶ L) (hs : s ≠ 0) (h : IsInvertible (LineSectionZeroIdeal.zeroIdeal L hL s).toModules) :
    lineCls ⟨(LineSectionZeroIdeal.zeroIdeal L hL s).toModules, h⟩ = -lineCls ⟨L, hL⟩ := by
  rw [lineCls_eq_of_iso h hL.dual (LineSectionZeroIdeal.dualIso L hL s hs),
    eq_neg_iff_add_eq_zero, add_comm]
  exact lineCls_add_dual hL

/-- `[𝒪(E)] = -[I_E]` in `Pic X`. -/
theorem lineCls_cartierLine {I : X.IdealSheafData} (hI : I.IsInvertible) :
    lineCls ⟨cartierLine I, cartierLine_isInvertible hI⟩ =
      -lineCls ⟨I.toModules, hI.isInvertibleModule_toModules⟩ := by
  rw [eq_neg_iff_add_eq_zero, add_comm]
  exact lineCls_add_dual hI.isInvertibleModule_toModules

/-- `[I J] = [I] + [J]` in `Pic X` for invertible ideal sheaves. -/
theorem lineCls_toModules_mul {I J : X.IdealSheafData} (hI : I.IsInvertible)
    (hJ : J.IsInvertible) :
    lineCls ⟨(I * J).toModules, (hI.mul hJ).isInvertibleModule_toModules⟩ =
      lineCls ⟨I.toModules, hI.isInvertibleModule_toModules⟩ +
        lineCls ⟨J.toModules, hJ.isInvertibleModule_toModules⟩ := by
  have hIJ : IsInvertible (I.toModules ⊗ J.toModules) :=
    (hI.isInvertibleModule_toModules.tensorObj hJ.isInvertibleModule_toModules).of_iso
      (SGPT.Support.ModularCurves.monoidalTensorObjIso _ _)
  rw [← lineCls_tensor _ _ hIJ]
  exact lineCls_eq_of_iso _ _
    ((Vanishing.NadelBlowupCanonicalIdealProduct.tensorProductIso I hI J).symm ≪≫
      (SGPT.Support.ModularCurves.monoidalTensorObjIso _ _).symm)

/-- `[I ^ n] = n [I]` in `Pic X` for an invertible ideal sheaf. -/
theorem lineCls_toModules_pow {I : X.IdealSheafData} (hI : I.IsInvertible) (n : ℕ) :
    lineCls ⟨(I ^ n).toModules, (Scheme.IdealSheafData.isInvertible_pow hI n).isInvertibleModule_toModules⟩ =
      n • lineCls ⟨I.toModules, hI.isInvertibleModule_toModules⟩ := by
  rw [← lineCls_tensorPower hI.isInvertibleModule_toModules n]
  exact lineCls_eq_of_iso _ _
    (Vanishing.NadelBlowupCanonicalIdealPowers.tensorPowerIso I hI n).symm

/-- Finite products of powers of invertible ideal sheaves are invertible. -/
theorem isInvertible_prod_pow {ι : Type*} (s : Finset ι) (I : ι → X.IdealSheafData)
    (hI : ∀ j, (I j).IsInvertible) (d : ι → ℕ) : (∏ j ∈ s, I j ^ d j).IsInvertible := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Scheme.IdealSheafData.isInvertible_top
  | insert i s hi ih =>
    rw [Finset.prod_insert hi]
    exact (Scheme.IdealSheafData.isInvertible_pow (hI i) (d i)).mul ih

/-- `[∏ I_j ^ d_j] = ∑ d_j [I_j]` in `Pic X`. -/
theorem lineCls_toModules_prod {ι : Type*} (s : Finset ι) (I : ι → X.IdealSheafData)
    (hI : ∀ j, (I j).IsInvertible) (d : ι → ℕ) :
    lineCls ⟨(∏ j ∈ s, I j ^ d j).toModules,
      (isInvertible_prod_pow s I hI d).isInvertibleModule_toModules⟩ =
      ∑ j ∈ s, d j • lineCls ⟨(I j).toModules, (hI j).isInvertibleModule_toModules⟩ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, Finset.sum_empty]
    have h1 : (1 : X.IdealSheafData) = ⊤ := Scheme.IdealSheafData.one_eq_top
    have e : (1 : X.IdealSheafData).toModules ≅ unitObj X :=
      eqToIso (congrArg Scheme.IdealSheafData.toModules h1) ≪≫
        CurveLineZeroSections.topIdealModuleIso X
    rw [lineCls_eq_of_iso _ isInvertible_unit e]
    exact lineCls_unit
  | insert i s hi ih =>
    have hprod := isInvertible_prod_pow s I hI d
    have hpow := Scheme.IdealSheafData.isInvertible_pow (hI i) (d i)
    have heq : (∏ j ∈ insert i s, I j ^ d j) = I i ^ d i * ∏ j ∈ s, I j ^ d j :=
      Finset.prod_insert hi
    have e : (∏ j ∈ insert i s, I j ^ d j).toModules ≅ (I i ^ d i * ∏ j ∈ s, I j ^ d j).toModules :=
      eqToIso (congrArg Scheme.IdealSheafData.toModules heq)
    rw [lineCls_eq_of_iso _ (hpow.mul hprod).isInvertibleModule_toModules e,
      lineCls_toModules_mul hpow hprod, lineCls_toModules_pow (hI i), ih, Finset.sum_insert hi]

/-- **Classes of vertical line bundles.** On an integral scheme, if the zero ideal of a nonzero
section `s` of `L` is `∏ I_j ^ d_j` with each `I_j` invertible, then `[L] = ∑ d_j [𝒪(E_j)]`. -/
theorem lineCls_eq_sum_cartierLine [IsIntegral X] {ι : Type*} (s : Finset ι)
    (I : ι → X.IdealSheafData) (hI : ∀ j, (I j).IsInvertible) (d : ι → ℕ)
    (L : X.Modules) (hL : IsInvertible L) (σ : unitObj X ⟶ L) (hσ : σ ≠ 0)
    (hzero : LineSectionZeroIdeal.zeroIdeal L hL σ = ∏ j ∈ s, I j ^ d j) :
    lineCls ⟨L, hL⟩ = ∑ j ∈ s, d j • lineCls ⟨cartierLine (I j), cartierLine_isInvertible (hI j)⟩ := by
  have hZ : IsInvertible (LineSectionZeroIdeal.zeroIdeal L hL σ).toModules := by
    rw [hzero]
    exact (isInvertible_prod_pow s I hI d).isInvertibleModule_toModules
  have h1 := lineCls_zeroIdeal_toModules L hL σ hσ hZ
  have e : (LineSectionZeroIdeal.zeroIdeal L hL σ).toModules ≅ (∏ j ∈ s, I j ^ d j).toModules :=
    eqToIso (congrArg Scheme.IdealSheafData.toModules hzero)
  rw [lineCls_eq_of_iso hZ (isInvertible_prod_pow s I hI d).isInvertibleModule_toModules e,
    lineCls_toModules_prod s I hI d] at h1
  rw [← neg_neg (lineCls ⟨L, hL⟩), ← h1, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [lineCls_cartierLine (hI j), smul_neg]

/-- The `ℚ`-version of `lineCls_eq_sum_cartierLine`. -/
theorem picQ_eq_sum_cartierLine [IsIntegral X] {ι : Type*} (s : Finset ι)
    (I : ι → X.IdealSheafData) (hI : ∀ j, (I j).IsInvertible) (d : ι → ℕ)
    (L : X.Modules) (hL : IsInvertible L) (σ : unitObj X ⟶ L) (hσ : σ ≠ 0)
    (hzero : LineSectionZeroIdeal.zeroIdeal L hL σ = ∏ j ∈ s, I j ^ d j) :
    picQ ⟨L, hL⟩ = ∑ j ∈ s, (d j : ℚ) • picQ ⟨cartierLine (I j), cartierLine_isInvertible (hI j)⟩ := by
  unfold picQ
  rw [lineCls_eq_sum_cartierLine s I hI d L hL σ hσ hzero, TensorProduct.tmul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [TensorProduct.tmul_smul, ← Nat.cast_smul_eq_nsmul ℚ]

/-- Pull-back of `ℚ`-classes of invertible sheaves. -/
theorem picPullbackQ_picQ {Y : Scheme.{u}} (f : Y ⟶ X) (L : X.Modules) (hL : IsInvertible L) :
    picPullbackQ f (picQ ⟨L, hL⟩) = picQ ⟨(Scheme.Modules.pullback f).obj L, hL.pullback f⟩ := by
  unfold picQ
  rw [picPullbackQ_tmul]
  congr 1
  change Additive.ofMul (CurvePicardDegrees.picPullback f (CurvePicardDegrees.lineClass L hL)) = _
  rw [CurvePicardDegrees.picPullback_lineClass]
  rfl

/-! ### Triviality away from the zero locus -/

/-- On an integral scheme the zero locus of a nonzero section is not everything. -/
theorem exists_not_mem_support_zeroIdeal [IsIntegral X] (L : X.Modules) (hL : IsInvertible L)
    (s : unitObj X ⟶ L) (hs : s ≠ 0) :
    ∃ x : X, x ∉ (LineSectionZeroIdeal.zeroIdeal L hL s).support := by
  by_contra hall
  push Not at hall
  have htop : (LineSectionZeroIdeal.zeroIdeal L hL s).support = ⊤ :=
    eq_top_iff.mpr fun x _ => hall x
  rw [Scheme.IdealSheafData.support_eq_top_iff] at htop
  have hinv := LineSectionZeroIdeal.zeroIdeal_isInvertible_of_ne_zero L hL s hs
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  obtain ⟨g, hg0, hg⟩ := hinv.exists_ne_zero_stalkIdeal_eq_span x
  rw [htop, Scheme.IdealSheafData.stalkIdeal_bot] at hg
  exact hg0 (Ideal.span_singleton_eq_bot.mp hg.symm)

/-- **Triviality off the zero locus.** On an integral scheme, a line bundle with a nonzero section
which does not vanish on the image of a morphism `i` is trivial after pull-back by `i`. -/
theorem nonempty_pullback_iso_unit [IsIntegral X] (L : X.Modules) (hL : IsInvertible L)
    (s : unitObj X ⟶ L) (hs : s ≠ 0) {Z : Scheme.{u}} (i : Z ⟶ X)
    (hi : ∀ z, i z ∉ (LineSectionZeroIdeal.zeroIdeal L hL s).support) :
    Nonempty ((Scheme.Modules.pullback i).obj L ≅ unitObj Z) := by
  let D := LineSectionZeroIdeal.zeroIdeal L hL s
  let V : X.Opens := ⟨(D.support : Set X)ᶜ, D.support.isClosed.isOpen_compl⟩
  obtain ⟨x₀, hx₀⟩ := exists_not_mem_support_zeroIdeal L hL s hs
  have : Nonempty V := ⟨⟨x₀, hx₀⟩⟩
  have : IsIntegral V.toScheme := isIntegral_of_isOpenImmersion V.ι
  let sV := SchemeLineSectionEvaluation.pullbackSectionHom V.ι s
  have hsV : sV ≠ 0 :=
    SchemeGlobalPullbackCartierRatio.pullbackSection_ne_zero V.ι L hL s ⟨x₀, hx₀⟩ (by
      simpa using hx₀)
  have hDV : LineSectionZeroIdeal.zeroIdeal _ (hL.pullback V.ι) sV = ⊤ := by
    rw [← Vanishing.NadelBertiniFibreIdeals.zeroIdeal_comap, ← Scheme.IdealSheafData.support_eq_bot_iff]
    ext y
    simp only [Scheme.IdealSheafData.support_comap, Closeds.coe_preimage, Set.mem_preimage,
      SetLike.mem_coe, TopologicalSpace.Closeds.coe_bot, Set.mem_empty_iff_false, iff_false]
    exact y.2
  let eV := CurveLineZeroSections.trivializationOfZeroIdealTop _ (hL.pullback V.ι) sV hsV hDV
  have hrange : Set.range i ⊆ Set.range V.ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact hi z
  let i' := IsOpenImmersion.lift V.ι i hrange
  have hfac : i' ≫ V.ι = i := IsOpenImmersion.lift_fac V.ι i hrange
  refine ⟨?_⟩
  exact eqToIso (by rw [hfac]) ≪≫ ((Scheme.Modules.pullbackComp i' V.ι).app L).symm ≪≫
    (Scheme.Modules.pullback i').mapIso eV ≪≫ Scheme.Modules.pullbackUnitIso i'

end SGPT.NAPotential.BJHodge
