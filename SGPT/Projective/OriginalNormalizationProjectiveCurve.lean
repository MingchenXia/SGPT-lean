import SGPT.Okounkov.OF12SmoothProjectiveBirationalModel
import SGPT.BDivisor.BD7Birational
import SGPT.Projective.OriginalGenericPointNormalization
import SGPT.NAPotential.AlgPrimes2Normal
import SGPT.Foundations.Schemes.FiniteTypeDomainDimension
import Mathlib.Topology.NoetherianSpace
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI

open Algebra CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set TopologicalSpace
open SGPT.Okounkov.OF12
open scoped nonZeroDivisors

private theorem smooth_curve_coheight_le_one {Y : Scheme.{0}} [IsIntegral Y]
    (g : Y ⟶ Spec (.of ℂ)) [SmoothOfRelativeDimension 1 g] (y : Y) :
    Order.coheight y ≤ 1 := by
  let : Smooth g := SmoothOfRelativeDimension.smooth 1 g
  obtain ⟨_, ⟨V, hV, rfl⟩, hyV, _⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  let : Nonempty V := ⟨⟨y, hyV⟩⟩
  let := affineChartAlgebra g V
  let := schemeFunctionFieldAlgebra g
  let : IsScalarTower ℂ Γ(Y, V) Y.functionField := schemeFunctionField_affineChartScalarTower g V
  let : IsFractionRing Γ(Y, V) Y.functionField := functionField_isFractionRing_of_isAffineOpen Y V hV
  let : Algebra.FiniteType ℂ Γ(Y, V) := affineChartAlgebra_finiteType g hV
  let : Algebra.IsAlgebraic Γ(Y, V) Y.functionField :=
    IsLocalization.isAlgebraic Y.functionField (nonZeroDivisors Γ(Y, V))
  have ht : Algebra.trdeg ℂ Γ(Y, V) = 1 := by
    have h := trdeg_add_eq ℂ Γ(Y, V) (A := Y.functionField)
    rwa [trdeg_eq_zero (R := Γ(Y, V)) (A := Y.functionField), add_zero,
      nativeSmoothFunctionField_trdeg g 1] at h
  have hd : ringKrullDim Γ(Y, V) = 1 := finiteTypeDomain_ringKrullDim_of_trdeg ℂ Γ(Y, V) 1 ht
  let v := hV.primeIdealOf ⟨y, hyV⟩
  have hv : hV.fromSpec v = y := hV.fromSpec_primeIdealOf ⟨y, hyV⟩
  rw [← hv, coheight_eq_of_isOpenImmersion hV.fromSpec]
  rw [← Order.coheight_orderIso (specOrderIsoPrimeSpectrum Γ(Y, V)) v]
  apply WithBot.coe_le_coe.mp
  exact (Order.coheight_le_krullDim (specOrderIsoPrimeSpectrum Γ(Y, V) v)).trans (by
    rw [Order.krullDim_orderDual]
    exact hd.le)

private theorem curve_morphismRestrict_apply {X Y : Scheme.{0}} (ρ : Y ⟶ X)
    (U : X.Opens) (y : ρ ⁻¹ᵁ U) : ((ρ ∣_ U) y).val = ρ y.val := by
  have h := congrArg (fun k : (ρ ⁻¹ᵁ U).toScheme ⟶ X => k y) (morphismRestrict_ι ρ U)
  simpa only [Scheme.Hom.comp_apply, Scheme.Opens.ι_apply] using h

/-- A proper closed subset of a Noetherian integral scheme of dimension at most
one is finite, as a set of actual scheme points. -/
private theorem finite_closed_off_generic {Y : Scheme.{0}} [IsIntegral Y] [NoetherianSpace Y]
    (hY : ∀ y : Y, Order.coheight y ≤ 1)
    {D : Set Y} (hD : IsClosed D) (hgen : genericPoint Y ∉ D) : D.Finite := by
  obtain ⟨components, hfinite, hclosed, hirr, hunion⟩ :=
    NoetherianSpace.exists_finite_set_isClosed_irreducible hD
  rw [hunion]
  refine hfinite.sUnion fun C hC => ?_
  have hclosedC := hclosed C hC
  have hirrC := hirr C hC
  let η := hirrC.genericPoint
  have hη : η ∈ C := (hirrC.isGenericPoint_genericPoint hclosedC).mem
  have hCsub : C ⊆ D := fun y hy => hunion.symm ▸ mem_sUnion_of_mem hy hC
  have hne : η ≠ genericPoint Y := fun he => hgen (he ▸ hCsub hη)
  have hlt : η < genericPoint Y := by
    refine lt_of_le_not_ge (_root_.genericPoint_specializes η) ?_
    intro h
    exact hne ((show η ⤳ genericPoint Y from h).antisymm
      (_root_.genericPoint_specializes η)).eq
  have hηheight : 1 ≤ Order.coheight η := calc
    1 = (0 : ℕ∞) + 1 := (zero_add _).symm
    _ ≤ Order.coheight (genericPoint Y) + 1 := by
      gcongr
      exact zero_le
    _ ≤ Order.coheight η := Order.coheight_add_one_le hlt
  have heq : C = {η} := by
    ext y
    constructor
    · intro hy
      by_contra h
      have hyη : y ≠ η := fun he => h (mem_singleton_iff.mpr he)
      have hylt : y < η := by
        have hs : η ⤳ y := (hirrC.isGenericPoint_genericPoint hclosedC).specializes hy
        refine lt_of_le_not_ge hs ?_
        intro h
        exact hyη ((show y ⤳ η from h).antisymm hs).eq
      have hh : (1 : ℕ∞) + 1 ≤ 1 := calc
        _ ≤ Order.coheight η + 1 := by gcongr
        _ ≤ Order.coheight y := Order.coheight_add_one_le hylt
        _ ≤ 1 := hY y
      norm_num at hh
    · intro hy
      exact (mem_singleton_iff.mp hy).symm ▸ hη
  rw [heq]
  exact finite_singleton _

/-- The actual proper birational curve model is finite. Its fibres over the good
open are singletons, and all remaining fibres lie in one finite closed subset. -/
theorem isFinite_of_smoothProjectiveBirationalCurve {Y X : Scheme.{0}}
    [IsIntegral Y] [IsIntegral X] (f : X ⟶ Spec (.of ℂ)) (ρ : Y ⟶ X)
    (EY : ClosedProjectiveEmbedding (ρ ≫ f)) [SmoothOfRelativeDimension 1 (ρ ≫ f)]
    [IsProper ρ] [IsIso (ρ.stalkMap (genericPoint Y))] : IsFinite ρ := by
  let : LocallyOfFiniteType (ρ ≫ f) := EY.locallyOfFiniteType
  let : LocallyOfFiniteType ρ := locallyOfFiniteType_of_comp ρ f
  let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (ρ ≫ f)
  let : QuasiCompact (ρ ≫ f) := EY.quasiCompact
  let : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (ρ ≫ f)
  let : AlgebraicGeometry.IsNoetherian Y := AlgebraicGeometry.IsNoetherian.mk
  obtain ⟨U, hU, hIso⟩ := SGPT.BDivisor.BD7.exists_isIso_morphismRestrict_of_isIso_stalkMap ρ
  let := hIso
  let D : Set Y := ρ ⁻¹' (U : Set X)ᶜ
  have hgenU : ρ (genericPoint Y) ∈ U := by
    obtain ⟨x, hx⟩ := hU
    obtain ⟨y, _⟩ := (ρ ∣_ U).surjective ⟨x, hx⟩
    have hpre : ((ρ ⁻¹ᵁ U : Y.Opens) : Set Y).Nonempty := ⟨y.val, y.property⟩
    exact ((genericPoint_spec Y).mem_open_set_iff (ρ ⁻¹ᵁ U).isOpen).mpr (by simpa using hpre)
  have hDfin : D.Finite :=
    finite_closed_off_generic (smooth_curve_coheight_le_one (ρ ≫ f))
      (U.isOpen.isClosed_compl.preimage ρ.continuous) (by
        change ¬ ρ (genericPoint Y) ∉ (U : Set X)
        exact not_not_intro hgenU)
  let : LocallyQuasiFinite ρ := locallyQuasiFinite_iff_finite_preimage_singleton.mpr fun x => by
    by_cases hx : x ∈ U
    · refine (Set.Subsingleton.finite ?_)
      intro a ha b hb
      let a' : ρ ⁻¹ᵁ U := ⟨a, by change ρ a ∈ U; rwa [(show ρ a = x from ha)]⟩
      let b' : ρ ⁻¹ᵁ U := ⟨b, by change ρ b ∈ U; rwa [(show ρ b = x from hb)]⟩
      have h' : (ρ ∣_ U) a' = (ρ ∣_ U) b' := by
        apply Subtype.ext
        rw [curve_morphismRestrict_apply, curve_morphismRestrict_apply]
        exact (show ρ a = x from ha).trans (show ρ b = x from hb).symm
      exact congrArg Subtype.val ((ρ ∣_ U).isOpenEmbedding.injective h')
    · apply hDfin.subset
      intro y hy
      change ρ y ∉ (U : Set X)
      rwa [(show ρ y = x from hy)]
  exact IsFinite.of_isProper_of_locallyQuasiFinite ρ

/-- For an integral affine chart of a finite normal birational model, the
range of the actual generic-section map is its base integral closure. -/
theorem range_algebraMap_eq_integralClosure_of_finite_normal_birational
    {A B K : Type*} [CommRing A] [CommRing B] [IsDomain B] [Field K]
    [Algebra A B] [Algebra B K] [Algebra A K] [IsScalarTower A B K]
    [Algebra.IsIntegral A B] [IsFractionRing B K] [IsIntegrallyClosed B] :
    range (algebraMap B K) = (integralClosure A K : Set K) := by
  ext x
  constructor
  · rintro ⟨b, rfl⟩
    exact (Algebra.IsIntegral.isIntegral b).algebraMap
  · intro hx
    have h : IsIntegral A x := hx
    exact (IsIntegrallyClosed.isIntegral_iff (K := K)).mp h.tower_top

/-- The final normalization identification needed for the projectivity binding.
In affine terms this says that the actual comparison above is an isomorphism
when the finite birational source is smooth. -/
def IsCanonicalSmoothCurveModel : Prop :=
  ∀ {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Spec (.of ℂ)) (ρ : Y ⟶ X) [IsFinite ρ]
    [IsIso (ρ.stalkMap (genericPoint Y))] [SmoothOfRelativeDimension 1 (ρ ≫ f)],
    ∃ j : originalNormalizationScheme X ≅ Y, j.hom ≫ ρ = originalNormalizationMap X

private theorem curve_appLE_congr_morphism {A B : Scheme.{0}} {g g' : A ⟶ B}
    (hg : g = g') (V : B.Opens) (W : A.Opens)
    (h : W ≤ g ⁻¹ᵁ V) (h' : W ≤ g' ⁻¹ᵁ V) :
    g.appLE V W h = g'.appLE V W h' := by
  subst g'
  rfl

/-- A finite birational smooth curve is the actual relative normalization. -/
theorem canonicalSmoothCurveModel : IsCanonicalSmoothCurveModel := by
  intro X Y _ _ f ρ _ _ _
  obtain ⟨U, hU, hIso⟩ := SGPT.BDivisor.BD7.exists_isIso_morphismRestrict_of_isIso_stalkMap ρ
  let := hIso
  have hrange : (U : Set X) ⊆ range ρ := by
    intro x hx
    obtain ⟨y, hy⟩ := (ρ ∣_ U).surjective ⟨x, hx⟩
    exact ⟨y.val, (curve_morphismRestrict_apply ρ U y).symm.trans (congrArg Subtype.val hy)⟩
  have hdense : DenseRange ρ := (U.isOpen.dense hU).mono hrange
  have hη : ρ (genericPoint Y) = genericPoint X := by
    apply IsGenericPoint.eq _ (genericPoint_spec X)
    change closure ({ρ (genericPoint Y)} : Set X) = univ
    apply top_unique
    change univ ⊆ closure ({ρ (genericPoint Y)} : Set X)
    rw [← hdense.closure_range]
    apply closure_minimal _ isClosed_closure
    rintro _ ⟨y, rfl⟩
    exact ((_root_.genericPoint_specializes y).map ρ.continuous).mem_closure
  let t : X.functionField ⟶ Y.functionField :=
    eqToHom (congrArg (fun z : X => X.presheaf.stalk z) hη.symm) ≫ ρ.stalkMap (genericPoint Y)
  have : IsIso t := by dsimp only [t]; infer_instance
  have hpointTransport (a b : X) (h : a = b) :
      Spec.map (eqToHom (congrArg (fun z : X => X.presheaf.stalk z) h)) ≫
        X.fromSpecStalk a = X.fromSpecStalk b := by
    subst b
    simp
  have ht : Spec.map t ≫ originalGenericPointMap X =
      Y.fromSpecStalk (genericPoint Y) ≫ ρ := by
    dsimp only [t, originalGenericPointMap]
    rw [Spec.map_comp, Category.assoc,
      hpointTransport (genericPoint X) (ρ (genericPoint Y)) hη.symm,
      Scheme.SpecMap_stalkMap_fromSpecStalk]
  let i : Spec X.functionField ⟶ Y := Spec.map (inv t) ≫ Y.fromSpecStalk (genericPoint Y)
  have hi : originalGenericPointMap X = i ≫ ρ := calc
    originalGenericPointMap X =
        Spec.map (inv t) ≫ (Spec.map t ≫ originalGenericPointMap X) := by
      rw [← Category.assoc, ← Spec.map_comp, IsIso.hom_inv_id, Spec.map_id, Category.id_comp]
    _ = Spec.map (inv t) ≫ (Y.fromSpecStalk (genericPoint Y) ≫ ρ) :=
      congrArg (fun v => Spec.map (inv t) ≫ v) ht
    _ = i ≫ ρ := (Category.assoc _ _ _).symm
  let j := (originalGenericPointMap X).normalizationDesc i ρ hi
  have hj : j ≫ ρ = originalNormalizationMap X :=
    (originalGenericPointMap X).normalizationDesc_comp i ρ hi
  have hji : (originalGenericPointMap X).toNormalization ≫ j = i :=
    (originalGenericPointMap X).toNormalization_normalizationDesc i ρ hi
  let : IsIntegralHom j := inferInstance
  let I := {U : X.affineOpens // Nonempty (U : X.Opens)}
  have hcover : (⨆ U : I, ((U.val : X.Opens))) = ⊤ := by
    apply top_unique
    rw [← iSup_affineOpens_eq_top X]
    refine iSup_le fun U => ?_
    by_cases h : Nonempty (U : X.Opens)
    · exact le_iSup (fun W : I => (W.val : X.Opens)) ⟨U, h⟩
    · intro x hx
      exact (h ⟨⟨x, hx⟩⟩).elim
  have hjIso : IsIso j := by
    change (MorphismProperty.isomorphisms _) j
    rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := .isomorphisms _) _
      (ρ.iSup_preimage_eq_top hcover)]
    intro W
    let U : X.Opens := W.val
    let V : Y.Opens := ρ ⁻¹ᵁ U
    have hU : IsAffineOpen U := W.val.property
    have hV : IsAffineOpen V := hU.preimage ρ
    let : Nonempty U := W.property
    have hηU := ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr
      (by simpa using W.property)
    let : Nonempty V := ⟨⟨genericPoint Y, by change ρ (genericPoint Y) ∈ U; rwa [hη]⟩⟩
    apply (isIso_morphismRestrict_iff_isIso_app j hV).2
    let T := originalGenericPointMap X
    let N := originalNormalizationMap X
    let S := T ⁻¹ᵁ U
    let Q := N ⁻¹ᵁ U
    have hQ : Q = j ⁻¹ᵁ V := by
      change N ⁻¹ᵁ U = j ⁻¹ᵁ (ρ ⁻¹ᵁ U)
      rw [← Scheme.Hom.comp_preimage, hj]
    have hS : S = i ⁻¹ᵁ V := by
      change T ⁻¹ᵁ U = i ⁻¹ᵁ (ρ ⁻¹ᵁ U)
      rw [← Scheme.Hom.comp_preimage, ← hi]
    have hF : S ≤ T.toNormalization ⁻¹ᵁ Q := by
      change T ⁻¹ᵁ U ≤ T.toNormalization ⁻¹ᵁ (T.fromNormalization ⁻¹ᵁ U)
      rw [← Scheme.Hom.comp_preimage, Scheme.Hom.toNormalization_fromNormalization]
    let J := j.appLE V Q hQ.le
    let F := T.toNormalization.appLE Q S hF
    let G := i.appLE V S hS.le
    have hJG : J ≫ F = G := by
      dsimp only [J, F, G]
      rw [Scheme.Hom.appLE_comp_appLE]
      exact curve_appLE_congr_morphism hji V S _ hS.le
    let e := (originalGenericPointSectionsIso X U).hom
    have hGe : G ≫ e = Y.germToFunctionField V ≫ inv t := by
      have htop : (⊤ : (Spec X.functionField).Opens) ≤ i ⁻¹ᵁ V :=
        (originalGenericPointMap_preimage_top X U).ge.trans hS.le
      have htopY : (⊤ : (Spec Y.functionField).Opens) ≤
          (Y.fromSpecStalk (genericPoint Y)) ⁻¹ᵁ V :=
        (originalGenericPointMap_preimage_top Y V).ge
      have hGtop : G ≫ e = i.appLE V ⊤ htop ≫ (Scheme.ΓSpecIso X.functionField).hom := by
        let r := (Spec X.functionField).presheaf.map
          (eqToHom (originalGenericPointMap_preimage_top X U).symm).op
        let v := (Scheme.ΓSpecIso X.functionField).hom
        change G ≫ (r ≫ v) = i.appLE V ⊤ htop ≫ v
        rw [← Category.assoc]
        congr 1
      rw [hGtop]
      change ((Spec.map (inv t)) ≫ Y.fromSpecStalk (genericPoint Y)).appLE V ⊤ htop ≫ _ = _
      rw [← Scheme.Hom.appLE_comp_appLE (Spec.map (inv t))
        (Y.fromSpecStalk (genericPoint Y)) V ⊤ ⊤ htopY (by simp)]
      have hfY : (Y.fromSpecStalk (genericPoint Y)).appLE V ⊤ htopY =
          Y.germToFunctionField V ≫ (Scheme.ΓSpecIso Y.functionField).inv := by
        rw [Scheme.Hom.appLE, Scheme.fromSpecStalk_app (show genericPoint Y ∈ V from by
          change ρ (genericPoint Y) ∈ U
          rwa [hη])]
        simp only [Category.assoc, ← Functor.map_comp]
        rw [← Category.assoc]
        suffices (Spec Y.functionField).presheaf.map
            ((homOfLE (show Y.fromSpecStalk (genericPoint Y) ⁻¹ᵁ V ≤ ⊤ from le_top)).op ≫
              (homOfLE htopY).op) = 𝟙 Γ(Spec Y.functionField, ⊤) by rw [this, Category.comp_id]
        trans (Spec Y.functionField).presheaf.map
            (𝟙 (Opposite.op (⊤ : (Spec Y.functionField).Opens)))
        · congr 1
        · exact CategoryTheory.Functor.map_id _ _
      rw [hfY]
      have htopApp : (Spec.map (inv t)).appLE ⊤ ⊤ (by simp) =
          (Spec.map (inv t)).appTop :=
        (Spec.map (inv t)).appLE_eq_app
      rw [htopApp]
      simp only [Category.assoc, Scheme.ΓSpecIso_naturality,
        Iso.inv_hom_id_assoc]
    let G' := G ≫ e
    let := (ρ.app U).hom.toAlgebra
    let := (X.germToFunctionField U).hom.toAlgebra
    let := G'.hom.toAlgebra
    have hscalar : ρ.app U ≫ G = T.app U := by
      change ρ.app U ≫ i.appLE V S hS.le = T.app U
      rw [← Scheme.Hom.comp_appLE]
      exact (curve_appLE_congr_morphism hi.symm U S _ le_rfl).trans
        (Scheme.Hom.appLE_eq_app T)
    have hscalar' : ρ.app U ≫ G' = X.germToFunctionField U := by
      dsimp only [G']
      rw [← Category.assoc, hscalar]
      exact originalGenericPointMap_app_sectionsIso X U
    let : IsScalarTower Γ(X, U) Γ(Y, V) X.functionField :=
      IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom hscalar').symm
    let : Algebra.IsIntegral Γ(X, U) Γ(Y, V) :=
      ⟨fun b => ρ.isIntegral_app U hU b⟩
    have : IsIntegrallyClosed Γ(Y, V) := by
      let g := V.ι ≫ (ρ ≫ f)
      have : IsAffine V.toScheme := hV
      have : SmoothOfRelativeDimension 1 g :=
        inferInstanceAs (SmoothOfRelativeDimension (0 + 1) (V.ι ≫ (ρ ≫ f)))
      have : IsSeparated g := by dsimp only [g]; infer_instance
      have : QuasiCompact g := by dsimp only [g]; infer_instance
      have : Nonempty (⊤ : V.toScheme.Opens) := ⟨⟨⟨genericPoint Y, by
        change ρ (genericPoint Y) ∈ U
        rwa [hη]⟩, trivial⟩⟩
      have : IsIntegrallyClosed Γ(V.toScheme, ⊤) :=
        SGPT.NAPotential.AlgPrimes2.isIntegrallyClosed_sections g 1 (isAffineOpen_top _)
      exact IsIntegrallyClosed.of_equiv V.topIso.commRingCatIsoToRingEquiv
    let E : Y.functionField ≃+* X.functionField := (asIso (inv t)).commRingCatIsoToRingEquiv
    let EI : Y.functionField ≃ₐ[Γ(Y, V)] X.functionField :=
      { E with commutes' := fun b => (ConcreteCategory.congr_hom hGe b).symm }
    let := functionField_isFractionRing_of_isAffineOpen Y V hV
    let := IsFractionRing.of_algEquiv EI
    have hGinj : Function.Injective G := by
      intro a b hab
      exact IsFractionRing.injective Γ(Y, V) X.functionField (congrArg e hab)
    have hGrange' : range G' = (integralClosure Γ(X, U) X.functionField : Set _) :=
      range_algebraMap_eq_integralClosure_of_finite_normal_birational
    let := (T.app U).hom.toAlgebra
    let EA : Γ(Spec X.functionField, S) ≃ₐ[Γ(X, U)] X.functionField :=
      { (originalGenericPointSectionsIso X U).commRingCatIsoToRingEquiv with
        commutes' := fun a =>
          ConcreteCategory.congr_hom (originalGenericPointMap_app_sectionsIso X U) a }
    have hGrange : range G = (integralClosure Γ(X, U) Γ(Spec X.functionField, S) :
        Set Γ(Spec X.functionField, S)) := by
      ext x
      have hr : x ∈ range G ↔ EA x ∈ range G' := by
        constructor
        · rintro ⟨b, rfl⟩
          exact ⟨b, rfl⟩
        · rintro ⟨b, hb⟩
          exact ⟨b, EA.injective hb⟩
      rw [hr, hGrange']
      change IsIntegral Γ(X, U) (EA x) ↔ IsIntegral Γ(X, U) x
      constructor
      · intro hx
        simpa using IsIntegral.map EA.symm.toAlgHom hx
      · intro hx
        exact IsIntegral.map EA.toAlgHom hx
    have hFiso := T.normalizationObjIso_hom_val hU
    change (T.normalizationObjIso hU).hom ≫
      CommRingCat.ofHom (Subalgebra.val _).toRingHom = F at hFiso
    have hFinj : Function.Injective F := by
      rw [← hFiso]
      exact Subtype.val_injective.comp ((T.normalizationObjIso hU).commRingCatIsoToRingEquiv.injective)
    have hFrange : range F = range G := by
      rw [hGrange, ← hFiso]
      ext x
      constructor
      · rintro ⟨a, rfl⟩
        exact ((T.normalizationObjIso hU).hom a).property
      · intro hx
        let normalized : integralClosure Γ(X, U) Γ(Spec X.functionField, S) := ⟨x, hx⟩
        refine ⟨(T.normalizationObjIso hU).inv normalized, ?_⟩
        change ((T.normalizationObjIso hU).hom ((T.normalizationObjIso hU).inv normalized)).val = x
        exact congrArg Subtype.val (ConcreteCategory.congr_hom
          (T.normalizationObjIso hU).inv_hom_id normalized)
    have hJ : Function.Bijective J := by
      constructor
      · intro a b hab
        apply hGinj
        simpa only [← ConcreteCategory.congr_hom hJG, CommRingCat.comp_apply] using congrArg F hab
      · intro x
        obtain ⟨b, hb⟩ := hFrange.le (show F x ∈ range F from ⟨x, rfl⟩)
        exact ⟨b, hFinj ((ConcreteCategory.congr_hom hJG b).trans hb)⟩
    have hJiso : IsIso J := by
      change IsIso (RingEquiv.ofBijective J.hom hJ).toCommRingCatIso.hom
      infer_instance
    have hJapp : J = j.app V ≫ (originalNormalizationScheme X).presheaf.map (eqToHom hQ).op := by
      unfold J Scheme.Hom.appLE
      congr 2
    let : IsIso ((originalNormalizationScheme X).presheaf.map (eqToHom hQ).op) := by
      infer_instance
    rw [hJapp] at hJiso
    exact (isIso_comp_right_iff _ _).mp hJiso
  let := hjIso
  exact ⟨asIso j, hj⟩

/-- Transport the actual closed embedding along the canonical normalization
isomorphism, retaining its structural morphism over the original base. -/
theorem originalNormalization_exists_closedProjectiveEmbedding_of_curve
    {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ))
    (E : ClosedProjectiveEmbedding f)
    (hcurve : let := schemeFunctionFieldAlgebra f; Algebra.trdeg ℂ X.functionField = 1) :
    Nonempty (ClosedProjectiveEmbedding (originalNormalizationMap X ≫ f)) := by
  let := schemeFunctionFieldAlgebra f
  obtain ⟨Y, hY, ρ, hproper, n, hsm, EY, hn, hbir, -, -⟩ :=
    exists_smooth_projective_birational_model E
  have hn' : n = 1 := by exact_mod_cast hn.symm.trans hcurve
  subst n
  let := hY
  let := hproper
  let := hsm
  let := hbir
  let : IsFinite ρ := isFinite_of_smoothProjectiveBirationalCurve f ρ EY
  obtain ⟨j, hj⟩ := canonicalSmoothCurveModel f ρ
  refine ⟨⟨EY.ambientDimension, j.hom ≫ EY.map, inferInstance, ?_⟩⟩
  rw [Category.assoc, EY.over_base, ← Category.assoc, hj]

end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
