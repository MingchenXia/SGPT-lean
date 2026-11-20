import SGPT.Checks.Comparison.BJModel3Vertical
import SGPT.Foundations.Envelope.AlgGeom.DominantCartierPullback
import SGPT.Support.Principalization.Scheme.BlowUp.Descent
import SGPT.Support.Principalization.Scheme.BlowUp.AffineBlowUp.Universal.Membership
import SGPT.Support.Principalization.Scheme.IdealSheaf.Invertible
import Mathlib.RingTheory.MvPolynomial.Ideal
import SGPT.Foundations.Envelope.AlgGeom.CartierAdmissibleModulePullback
import SGPT.Foundations.Envelope.AlgGeom.ProjectiveGeneratedLineClasses

/-!
# The central fibre is a Cartier divisor (lane BJ-MODEL3, step (R4a) of `claude-bj-model3:plan`)

Source: [BJ22] (`references/bj22-trivval`), §1.2 and §2.1: the central fibre `𝒳₀ = div(t)` of a
test configuration is a Cartier divisor. Towards `thm:BJappseq` of `chapter_NApotential.tex`.
Blueprint: `claude-bj-model3.tex`, node `claude-bj-model3:central-cartier`.

* `ker_evalZero`: the kernel of evaluation at `0` on the chart ring `k[t]` of `D₊(x₀)` is `(t)`;
* `zeroIdeal_comap_lineChart`: on the chart `D₊(x₀) = Spec k[t]` the ideal sheaf of `0 ∈ ℙ¹` is
  the principal ideal sheaf `(t)`;
* `zeroIdeal_isInvertible`: the ideal sheaf of `0 ∈ ℙ¹` is invertible;
* `centralIdeal_isInvertible`: the ideal sheaf `𝓘` of `X × {0}` is invertible on `X × ℙ¹`;
* `isInvertible_comap_centralIdeal`, `dominates_monomial_zero_one`: on every blow-up model of a
  flag ideal, `𝒳₀ = 𝓘 · 𝒪` is a Cartier divisor, so every model is good
  (`isGoodModel_of_isWeightBound`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.NAPotential.BJ

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open SGPT.Support.Alterations SGPT.Support.Alterations.Geometry
open SGPT.Foundations.Envelope SGPT.NAPotential.Berkovich SGPT.NAPotential.BJIntersect
open SGPT.NAPotential.BJModel FlagIdealBound

section chart

variable (k : Type) [Field k]

/-- The chart coordinate `t = x₁/x₀` of `D₊(x₀)`. -/
abbrev chartT : ProjectiveIdeal.CoordinateRing k (0 : Fin 2) := MvPolynomial.X ⟨1, by decide⟩

/-- **The kernel of evaluation at `0` on `k[t]` is `(t)`.** -/
theorem ker_evalZero : RingHom.ker (evalZero k) = Ideal.span {chartT k} := by
  have hX : (MvPolynomial.X '' (Set.univ : Set (ProjectiveIdeal.ChartIndex
      (n := 1) (0 : Fin 2))) : Set (ProjectiveIdeal.CoordinateRing k (0 : Fin 2))) = {chartT k} := by
    ext f
    simp only [Set.image_univ, Set.mem_range, Set.mem_singleton_iff]
    constructor
    · rintro ⟨⟨i, hi⟩, rfl⟩
      congr 1
      apply Subtype.ext
      revert hi
      revert i
      decide
    · rintro rfl
      exact ⟨_, rfl⟩
  ext f
  rw [RingHom.mem_ker, evalZero, MvPolynomial.eval_zero', ← hX, MvPolynomial.mem_ideal_span_X_image]
  constructor
  · intro h m hm
    by_contra hne
    push Not at hne
    have hm0 : m = 0 := by
      ext i
      exact hne i (Set.mem_univ i)
    subst hm0
    exact (MvPolynomial.mem_support_iff.mp hm) (by rwa [← MvPolynomial.constantCoeff_eq])
  · intro h
    rw [MvPolynomial.constantCoeff_eq]
    by_contra hne
    obtain ⟨i, -, hi⟩ := h 0 (MvPolynomial.mem_support_iff.mpr hne)
    exact hi rfl

/-- **On the chart `D₊(x₀) = Spec k[t]`, the ideal sheaf of `0 ∈ ℙ¹` is `(t)`.** -/
theorem zeroIdeal_comap_lineChart :
    (zeroIdeal k).comap (lineChart k) = Scheme.IdealSheafData.ofIdealTop
      (Ideal.span {(Scheme.ΓSpecIso (.of (ProjectiveIdeal.CoordinateRing k (0 : Fin 2)))).inv
        (chartT k)}) := by
  let j := lineChart k
  let κ : Spec (.of k) ⟶ Spec (.of (ProjectiveIdeal.CoordinateRing k (0 : Fin 2))) :=
    Spec.map (CommRingCat.ofHom (evalZero k))
  have hzp : zeroPoint k = κ ≫ j := rfl
  have hfst : pullback.fst j (zeroPoint k) = pullback.snd j (zeroPoint k) ≫ κ := by
    rw [← cancel_mono j, Category.assoc, pullback.condition]
    rfl
  have hiso : IsIso (pullback.snd j (zeroPoint k)) := by
    rw [hzp]
    infer_instance
  rw [zeroIdeal, ← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion, hfst,
    Scheme.Hom.ker_comp_of_isIso, Scheme.ker_of_isAffine]
  congr 1
  have hnat : κ.appTop = (Scheme.ΓSpecIso _).hom ≫ CommRingCat.ofHom (evalZero k) ≫
      (Scheme.ΓSpecIso _).inv := by
    show (Spec.map (CommRingCat.ofHom (evalZero k))).appTop = _
    rw [Scheme.ΓSpecIso_inv_naturality, Iso.hom_inv_id_assoc]
  ext σ
  rw [RingHom.mem_ker, hnat]
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom]
  constructor
  · intro h
    have h' : evalZero k ((Scheme.ΓSpecIso _).hom.hom σ) = 0 := by
      have := congrArg (Scheme.ΓSpecIso (.of k)).hom.hom h
      rwa [ΓSpecIso_hom_inv_apply, map_zero] at this
    have hmem : (Scheme.ΓSpecIso _).hom.hom σ ∈ Ideal.span {chartT k} := by
      rw [← ker_evalZero]; exact h'
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hmem
    refine Ideal.mem_span_singleton'.mpr ⟨(Scheme.ΓSpecIso _).inv.hom a, ?_⟩
    have := congrArg (Scheme.ΓSpecIso (.of (ProjectiveIdeal.CoordinateRing k (0 : Fin 2)))).inv.hom ha
    rw [map_mul] at this
    rw [this]
    exact congrArg (fun φ => φ.hom σ) (Scheme.ΓSpecIso _).hom_inv_id
  · intro h
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp h
    rw [map_mul, ΓSpecIso_hom_inv_apply, map_mul]
    have : evalZero k (chartT k) = 0 := by simp [evalZero]
    rw [this, mul_zero, map_zero]

/-- SGPT's stalk ideal (`SGPT.NAPotential.Berkovich.stalkIdeal`) is Hironaka's. -/
theorem berkovich_stalkIdeal_eq {Y : Scheme.{0}} (J : Y.IdealSheafData) (y : Y) :
    SGPT.NAPotential.Berkovich.stalkIdeal J y = J.stalkIdeal y := rfl

instance projectiveSpace_isLocallyNoetherian : IsLocallyNoetherian (projectiveSpace k 1) :=
  let : IsProjective (projectiveSpaceStructure k 1) :=
    SGPT.Foundations.Envelope.NativeProjectivityFromPolynomialFactorization.of_isProjectiveFactorization _
      (projectiveSpaceStructure_isProjectiveFactorization k 1)
  isLocallyNoetherian_of_isProjective (projectiveSpaceStructure k 1)

/-- **The ideal sheaf of `0 ∈ ℙ¹` is invertible** (a Cartier divisor): its stalk at `0` is
generated by the germ of the chart coordinate `t`, and it is the unit ideal elsewhere. -/
theorem zeroIdeal_isInvertible : (zeroIdeal k).IsInvertible := by
  let := projectiveSpace_isIntegral k 1
  apply Scheme.IdealSheafData.isInvertible_of_forall_stalkIdeal_eq_span
  intro x
  by_cases hx : x ∈ (zeroIdeal k).support
  · have hx' : x ∈ Set.range (zeroPoint k) := by
      rw [← support_zeroIdeal]; exact hx
    obtain ⟨z, hz⟩ := hx'
    let A := ProjectiveIdeal.CoordinateRing k (0 : Fin 2)
    let c : Spec (.of A) := Spec.map (CommRingCat.ofHom (evalZero k)) z
    have hxc : x = lineChart k c := by
      rw [← hz, zeroPoint, Scheme.Hom.comp_apply]
    subst hxc
    let g : Γ(Spec (.of A), ⊤) := (Scheme.ΓSpecIso (.of A)).inv (chartT k)
    have hstalk := stalkIdeal_comap (lineChart k) (zeroIdeal k) c
    rw [berkovich_stalkIdeal_eq, berkovich_stalkIdeal_eq] at hstalk
    rw [zeroIdeal_comap_lineChart, AlgebraicGeometry.stalkIdeal_ofIdealTop, Ideal.map_span,
      Set.image_singleton] at hstalk
    let e := asIso ((lineChart k).stalkMap c)
    have hI : (zeroIdeal k).stalkIdeal (lineChart k c) =
        Ideal.span {e.inv.hom ((Spec (.of A)).presheaf.germ ⊤ c trivial g)} := by
      have h2 := congrArg (Ideal.map e.inv.hom) hstalk
      rw [Ideal.map_span, Set.image_singleton, Ideal.map_map, ← CommRingCat.hom_comp,
        show (lineChart k).stalkMap c ≫ e.inv = 𝟙 _ from e.hom_inv_id, CommRingCat.hom_id,
        Ideal.map_id] at h2
      exact h2.symm
    have hg : g ≠ 0 := by
      intro h0
      have := congrArg (Scheme.ΓSpecIso (.of A)).hom.hom h0
      rw [ΓSpecIso_hom_inv_apply, map_zero] at this
      exact MvPolynomial.X_ne_zero _ this
    have hgerm : (Spec (.of A)).presheaf.germ ⊤ c trivial g ≠ 0 := by
      intro h0
      apply hg
      exact germ_injective_of_isIntegral (U := ⊤) _ c trivial (h0.trans (map_zero _).symm)
    refine ⟨e.inv.hom ((Spec (.of A)).presheaf.germ ⊤ c trivial g), ?_, hI⟩
    apply mem_nonZeroDivisors_of_ne_zero
    intro h0
    apply hgerm
    have := congrArg e.hom.hom h0
    rwa [← CommRingCat.comp_apply, e.inv_hom_id, CommRingCat.id_apply, map_zero] at this
  · exact ⟨1, one_mem _, by
      rw [Scheme.IdealSheafData.stalkIdeal_eq_top_of_notMem_support _ hx, Ideal.span_singleton_one]⟩

/-- The chart `D₊(x₀)` as an affine open of `ℙ¹`. -/
abbrev chartOpen : (projectiveSpace k 1).affineOpens :=
  ⟨lineChart k ''ᵁ ⊤, (isAffineOpen_top _).image_of_isOpenImmersion (lineChart k)⟩

/-- **The ideal of `0` on the chart is principal**, generated by a nonzerodivisor (the coordinate
`t`). -/
theorem exists_zeroIdeal_ideal_chartOpen :
    ∃ g ∈ nonZeroDivisors Γ(projectiveSpace k 1, (chartOpen k).1),
      (zeroIdeal k).ideal (chartOpen k) = Ideal.span {g} := by
  let := projectiveSpace_isIntegral k 1
  let A := ProjectiveIdeal.CoordinateRing k (0 : Fin 2)
  let g : Γ(Spec (.of A), ⊤) := (Scheme.ΓSpecIso (.of A)).inv (chartT k)
  have hle : (⊤ : (Spec (.of A)).Opens) ≤ lineChart k ⁻¹ᵁ (chartOpen k).1 :=
    (Scheme.Hom.preimage_image_eq (lineChart k) ⊤).ge
  have h := Scheme.IdealSheafData.comap_ideal_of_affine_opens (zeroIdeal k) (lineChart k)
    ⟨⊤, isAffineOpen_top _⟩ (chartOpen k) hle
  rw [zeroIdeal_comap_lineChart, AlgebraicGeometry.ofIdealTop_ideal_top] at h
  let e := ((lineChart k).appIso ⊤).commRingCatIsoToRingEquiv
  have he : ((lineChart k).appLE (chartOpen k).1 ⊤ hle).hom = e.toRingHom := by
    rw [← Scheme.Hom.appIso_hom']
    rfl
  rw [he] at h
  have hI : (zeroIdeal k).ideal (chartOpen k) = Ideal.span {e.symm g} := by
    have h2 := Ideal.map_of_equiv e (I := (zeroIdeal k).ideal (chartOpen k))
    rw [RingEquiv.toRingHom_eq_coe] at h
    rw [← h, Ideal.map_span, Set.image_singleton] at h2
    exact h2.symm
  refine ⟨e.symm g, ?_, hI⟩
  have : Nonempty (chartOpen k).1 := by
    obtain ⟨x⟩ : Nonempty (Spec (.of A)) := inferInstance
    exact ⟨⟨lineChart k x, x, trivial, rfl⟩⟩
  apply mem_nonZeroDivisors_of_ne_zero
  intro h0
  have hg : g = 0 := by
    have := congrArg e h0
    rwa [RingEquiv.apply_symm_apply, map_zero] at this
  have := congrArg (Scheme.ΓSpecIso (.of A)).hom.hom hg
  rw [ΓSpecIso_hom_inv_apply, map_zero] at this
  exact MvPolynomial.X_ne_zero _ this

end chart

/-! ### The central fibre -/

section central

variable {k : Type} [Field k] {X : Scheme.{0}} (p : X ⟶ Spec (.of k))

/-- **The ideal `𝓘` of the central fibre `X × {0}` is invertible** on `X × ℙ¹` (pull-back of the
Cartier divisor `0 ∈ ℙ¹` along the dominant projection). -/
theorem centralIdeal_isInvertible [IsIntegral X] [IsProjective p] :
    (centralIdeal p).IsInvertible := by
  let := productLine_isIntegral_of_isProjective p
  let := projectiveSpace_isIntegral k 1
  have : IsDominant (productSnd p) := ⟨(productSnd_surjective p).denseRange⟩
  exact (zeroIdeal_isInvertible k).comap_of_dominant_integral (productSnd p)

/-- The blow-down of a flag model is dominant. -/
theorem flagModelπ_isDominant [IsIntegral X] [IsProjective p] (𝔞 : FlagIdeal X) (b : ℤ) :
    IsDominant (flagModelπ p 𝔞 b) := by
  let := productLine_isIntegral_of_isProjective p
  obtain ⟨h1, -⟩ := flagModelπ_genericPoint p 𝔞 b
  constructor
  rw [DenseRange, Dense]
  intro x
  have hcl : x ∈ closure ({genericPoint (productLine p)} : Set (productLine p)) := by
    rw [(genericPoint_spec (productLine p)).def]; trivial
  exact closure_mono (Set.singleton_subset_iff.mpr (Set.mem_range.mpr ⟨_, h1⟩)) hcl

/-- **The central fibre `𝒳₀ = 𝓘 · 𝒪` is a Cartier divisor on every blow-up model.** -/
theorem isInvertible_comap_centralIdeal [IsIntegral X] [IsProjective p] (𝔞 : FlagIdeal X)
    (b : ℤ) : ((centralIdeal p).comap (flagModelπ p 𝔞 b)).IsInvertible := by
  let := productLine_isIntegral_of_isProjective p
  have := flagModelπ_isDominant p 𝔞 b
  exact (centralIdeal_isInvertible p).comap_of_dominant_integral (flagModelπ p 𝔞 b)

/-- **Every blow-up model dominates the model of `((t^0), 1)`**, i.e. of the central fibre
(universal property of the blow-up). -/
theorem dominates_monomial_zero_one [IsIntegral X] [IsProjective p] (𝔞 : FlagIdeal X) (b : ℤ) :
    Dominates p 𝔞 b (FlagIdeal.monomial X 0) 1 := by
  have hinv : ((flagSheaf p (FlagIdeal.monomial X 0) 1).comap (flagModelπ p 𝔞 b)).IsInvertible := by
    have h : flagSheaf p (FlagIdeal.monomial X 0) 1 = centralIdeal p := by
      rw [flagSheaf_monomial p (show (0 : ℤ) ≤ 1 by norm_num)]
      simp
    rw [h]
    exact isInvertible_comap_centralIdeal p 𝔞 b
  exact ⟨hinv, Scheme.IdealSheafData.blowUp.lift _ _ hinv,
    Scheme.IdealSheafData.blowUp.lift_π _ _ _⟩

end central

/-! ### The central fibre has degree `0` on central curves -/

section degree

variable {X : Scheme.{0}} (p : X ⟶ Spec (.of ℂ)) [IsProjective p] [IsIntegral X]

/-- The projection `𝒳 ⟶ ℙ¹` of a blow-up model. -/
abbrev modelLine (𝔞 : FlagIdeal X) (b : ℤ) : flagModel p 𝔞 b ⟶ projectiveSpace ℂ 1 :=
  flagModelπ p 𝔞 b ≫ productSnd p

omit [IsProjective p] [IsIntegral X] in
theorem comap_centralIdeal_eq (𝔞 : FlagIdeal X) (b : ℤ) :
    (centralIdeal p).comap (flagModelπ p 𝔞 b) = (zeroIdeal ℂ).comap (modelLine p 𝔞 b) := by
  rw [centralIdeal, ← Scheme.IdealSheafData.comap_comp]

/-- The invertible sheaf `𝓘 · 𝒪 = 𝒪(-𝒳₀)` of the central fibre of a model. -/
def centralLine (𝔞 : FlagIdeal X) (b : ℤ) :
    {L : (flagModel p 𝔞 b).Modules // Scheme.Modules.IsInvertible L} :=
  ⟨((centralIdeal p).comap (flagModelπ p 𝔞 b)).toModules,
    (isInvertible_comap_centralIdeal p 𝔞 b).isInvertibleModule_toModules⟩

/-- **The central fibre has degree `0` on every closed integral curve inside it**: the map of the
curve to `ℙ¹` factors through the chart `D₊(x₀)`, on which the ideal of `0` is trivialized by
`t`. -/
theorem degree_centralLine_eq_zero (𝔞 : FlagIdeal X) (b : ℤ)
    (C : NativeClosedCurveDegrees.ClosedIntegralCurve (flagModel p 𝔞 b))
    (hC : Set.range C.inclusion ⊆ centralFibre p 𝔞 b) :
    letI : IsClosedImmersion C.inclusion := C.closed
    letI : CompactSpace C.carrier := QuasiCompact.compactSpace_of_compactSpace C.inclusion
    CurveLineDegrees.degree (C.inclusion ≫ flagModelStructure p 𝔞 b)
      ((Scheme.Modules.pullback C.inclusion).obj (centralLine p 𝔞 b).1) = 0 := by
  let : IsClosedImmersion C.inclusion := C.closed
  let : CompactSpace C.carrier := QuasiCompact.compactSpace_of_compactSpace C.inclusion
  let := productLine_isIntegral_of_isProjective p
  let := projectiveSpace_isIntegral ℂ 1
  have : IsDominant (flagModelπ p 𝔞 b) := flagModelπ_isDominant p 𝔞 b
  have : IsDominant (productSnd p) := ⟨(productSnd_surjective p).denseRange⟩
  let q := modelLine p 𝔞 b
  let Z := zeroIdeal ℂ
  have hiso : IsIso (Z.toModulesComapPullbackMap q) :=
    (zeroIdeal_isInvertible ℂ).toModulesComapPullbackMap_isIso_of_dominant_integral q
  obtain ⟨g, hg, hZU⟩ := exists_zeroIdeal_ideal_chartOpen ℂ
  let U := chartOpen ℂ
  let eU := Z.regularGeneratorPullbackModuleIso U g hg hZU
  have hrange : Set.range (C.inclusion ≫ q) ⊆ Set.range (U.1.ι) := by
    rintro _ ⟨x, rfl⟩
    have hx : flagModelπ p 𝔞 b (C.inclusion x) ∈ ((centralIdeal p).support : Set _) := hC ⟨x, rfl⟩
    rw [support_centralIdeal] at hx
    obtain ⟨z, hz⟩ := hx
    rw [Scheme.Opens.range_ι]
    refine ⟨Spec.map (CommRingCat.ofHom (evalZero ℂ)) z, trivial, ?_⟩
    change lineChart ℂ _ = (C.inclusion ≫ flagModelπ p 𝔞 b ≫ productSnd p) x
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, ← hz, zeroPoint, Scheme.Hom.comp_apply]
  let h := IsOpenImmersion.lift U.1.ι (C.inclusion ≫ q) hrange
  have hfac : h ≫ U.1.ι = C.inclusion ≫ q := IsOpenImmersion.lift_fac _ _ _
  have hK : (centralLine p 𝔞 b).1 = (Z.comap q).toModules := by
    rw [show (centralLine p 𝔞 b).1 = ((centralIdeal p).comap (flagModelπ p 𝔞 b)).toModules from rfl,
      comap_centralIdeal_eq]
  let E : (Scheme.Modules.pullback C.inclusion).obj (centralLine p 𝔞 b).1 ≅
      Scheme.Modules.unitObj C.carrier :=
    eqToIso (by rw [hK]) ≪≫
      (Scheme.Modules.pullback C.inclusion).mapIso (asIso (Z.toModulesComapPullbackMap q)).symm ≪≫
      (Scheme.Modules.pullbackComp C.inclusion q).app Z.toModules ≪≫
      eqToIso (by rw [hfac]) ≪≫
      ((Scheme.Modules.pullbackComp h U.1.ι).app Z.toModules).symm ≪≫
      (Scheme.Modules.pullback h).mapIso eU ≪≫
      Scheme.Modules.pullbackUnitIso h
  rw [CurveLineDegrees.degree_eq_of_iso _ E, CurveLineDegrees.degree_unit]

/-- The central fibre `𝓘 · 𝒪` is nef on the central fibre. -/
theorem isNefOn_centralLine (𝔞 : FlagIdeal X) (b : ℤ) :
    IsNefOn (flagModelStructure p 𝔞 b) (centralLine p 𝔞 b).1 (centralFibre p 𝔞 b) :=
  fun C hC => (degree_centralLine_eq_zero p 𝔞 b C hC).ge

attribute [local instance] Scheme.Modules.monoidalCategory in
/-- The dual `𝒪(𝒳₀)` of the central fibre is nef on the central fibre. -/
theorem isNefOn_dual_centralLine (𝔞 : FlagIdeal X) (b : ℤ) :
    IsNefOn (flagModelStructure p 𝔞 b) (Scheme.Modules.dualObj (centralLine p 𝔞 b).1)
      (centralFibre p 𝔞 b) := by
  intro C hC
  let : IsClosedImmersion C.inclusion := C.closed
  let : IsIntegral C.carrier := C.integral
  let : CompactSpace C.carrier := QuasiCompact.compactSpace_of_compactSpace C.inclusion
  have hp : IsProjectiveFactorization (C.inclusion ≫ flagModelStructure p 𝔞 b) :=
    (SGPT.Foundations.Envelope.ProjectiveFactorizationRingIso.of_isProjective
      (flagModelStructure p 𝔞 b)).comp_isClosedImmersion C.inclusion C.closed
  have h0 := degree_centralLine_eq_zero p 𝔞 b C hC
  have h1 := CurvePicardDegrees.curveDegreeHom_lineClass _ hp C.dimension.le C.inclusion
    (centralLine p 𝔞 b).1 (centralLine p 𝔞 b).2
  have h2 := CurvePicardDegrees.curveDegreeHom_lineClass _ hp C.dimension.le C.inclusion
    (Scheme.Modules.dualObj (centralLine p 𝔞 b).1) (centralLine p 𝔞 b).2.dual
  rw [SGPT.Foundations.Envelope.ProjectiveGeneratedLineClasses.lineClass_dual (centralLine p 𝔞 b).1
    (centralLine p 𝔞 b).2, map_inv, toAdd_inv] at h2
  have : CurveLineDegrees.degree (C.inclusion ≫ flagModelStructure p 𝔞 b)
      ((Scheme.Modules.pullback C.inclusion).obj
        (Scheme.Modules.dualObj (centralLine p 𝔞 b).1)) = 0 := by
    rw [← h2, h1, h0, neg_zero]
  exact this.ge

/-- `±[𝒪(𝒳₀)]` are relatively nef: the class of `𝓘 · 𝒪` and its negative lie in the relatively
nef cone of the central fibre. -/
theorem picQ_centralLine_mem_relNefCone (𝔞 : FlagIdeal X) (b : ℤ) :
    picQ (centralLine p 𝔞 b) ∈ relNefCone (flagModelStructure p 𝔞 b) (centralFibre p 𝔞 b) :=
  picQ_mem_relNefCone _ _ (isNefOn_centralLine p 𝔞 b)

theorem neg_picQ_centralLine_mem_relNefCone (𝔞 : FlagIdeal X) (b : ℤ) :
    -picQ (centralLine p 𝔞 b) ∈ relNefCone (flagModelStructure p 𝔞 b) (centralFibre p 𝔞 b) := by
  have h := picQ_mem_relNefCone (flagModelStructure p 𝔞 b)
    ⟨Scheme.Modules.dualObj (centralLine p 𝔞 b).1, (centralLine p 𝔞 b).2.dual⟩
    (isNefOn_dual_centralLine p 𝔞 b)
  convert h using 1
  simp only [picQ, lineCls]
  rw [SGPT.Foundations.Envelope.ProjectiveGeneratedLineClasses.lineClass_dual (centralLine p 𝔞 b).1
    (centralLine p 𝔞 b).2, ofMul_inv, TensorProduct.tmul_neg]

/-- The vertical divisor `𝒳₀` has the class `[𝒪(𝒳₀)] = -[𝓘 · 𝒪]`. -/
theorem picQ_centralVert_line {𝔞 : FlagIdeal X} {b : ℤ}
    (h0 : Dominates p 𝔞 b (FlagIdeal.monomial X 0) 1) :
    picQ (centralVert h0).line = picQ (centralLine p 𝔞 b) := by
  have hI : (centralVert h0).ideal = (centralIdeal p).comap (flagModelπ p 𝔞 b) := by
    simp only [centralVert, flagVert, flagSheaf_monomial_zero_one]
  unfold VertCartier.line centralLine
  congr 2
  rw [hI]

end degree

/-! ### `ω`-psh PL functions are stable under adding constants -/

/-- **`ω`-psh PL functions are stable under adding rational constants** ([BJ22, §3.1]):
`φ_{D + q 𝒳₀} = φ_D + q` and `±[𝒪(𝒳₀)]` are relatively nef. -/
theorem IsOmegaPshPL.add_const {X : Scheme.{0}} {p : X ⟶ Spec (.of ℂ)} [IsProjective p]
    [IsIntegral X] {ω : PicQ X} {φ : BerkovichPoint p → ℝ} (h : IsOmegaPshPL ω φ) (q : ℚ) :
    IsOmegaPshPL ω (φ + fun _ => (q : ℝ)) := by
  obtain ⟨𝔠, c, hgood, D, rfl, hD⟩ := h
  refine ⟨𝔠, c, hgood, D + Finsupp.single (centralVert hgood.2) q, ?_, ?_⟩
  · rw [map_add, fn_single_centralVert]
  · rw [map_add, VDiv.cls_single, picQ_centralVert_line, ← add_assoc]
    refine add_mem hD ?_
    rcases le_or_gt 0 q with hq | hq
    · exact Submodule.smul_mem _ (⟨q, hq⟩ : {r : ℚ // 0 ≤ r})
        (neg_picQ_centralLine_mem_relNefCone p 𝔠 c)
    · rw [show q • -picQ (centralLine p 𝔠 c) = (-q) • picQ (centralLine p 𝔠 c) by
        rw [smul_neg, neg_smul]]
      exact Submodule.smul_mem _ (⟨-q, by linarith⟩ : {r : ℚ // 0 ≤ r})
        (picQ_centralLine_mem_relNefCone p 𝔠 c)

/-- **`0` is `ω`-psh when `ω` is nef** (a nonnegative combination of classes of nef invertible
sheaves on `X`): `π^*ω` is relatively nef on every model. -/
theorem isOmegaPshPL_zero {X : Scheme.{0}} {p : X ⟶ Spec (.of ℂ)} [IsProjective p] [IsIntegral X]
    [CompactSpace X] {ω : PicQ X} (hω : ω ∈ relNefCone p Set.univ) :
    IsOmegaPshPL ω (0 : BerkovichPoint p → ℝ) := by
  obtain ⟨b, hb⟩ := FlagIdealBound.exists_isWeightBound (FlagIdeal.monomial X 0)
  refine ⟨_, _, ⟨hb, dominates_monomial_zero_one p _ _⟩, 0, map_zero _, ?_⟩
  rw [map_zero, add_zero]
  have hcomp : (flagModelπ p (FlagIdeal.monomial X 0) b ≫ productFst p) ≫ p =
      flagModelStructure p (FlagIdeal.monomial X 0) b := by
    rw [flagModelStructure, Category.assoc]
  have : IsProjective ((flagModelπ p (FlagIdeal.monomial X 0) b ≫ productFst p) ≫ p) := by
    rw [hcomp]; infer_instance
  have h := picPullbackQ_mem_relNefCone p (flagModelπ p (FlagIdeal.monomial X 0) b ≫ productFst p) hω
  rw [Set.preimage_univ] at h
  have h' := relNefCone_mono ((flagModelπ p (FlagIdeal.monomial X 0) b ≫ productFst p) ≫ p)
    (Set.subset_univ (centralFibre p (FlagIdeal.monomial X 0) b)) h
  rw [hcomp] at h'
  exact h'

/-- **Every model with a weight bound is good.** -/
theorem isGoodModel_of_isWeightBound {X : Scheme.{0}} (p : X ⟶ Spec (.of ℂ)) [IsProjective p]
    [IsIntegral X] {𝔠 : FlagIdeal X} {c : ℤ} (hc : IsWeightBound 𝔠 c) : IsGoodModel p 𝔠 c :=
  ⟨hc, dominates_monomial_zero_one p 𝔠 c⟩

end SGPT.NAPotential.BJ
