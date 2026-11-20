import SGPT.Okounkov.AlgebraicBodyBound
import SGPT.LineBundle.FiltrationSectionPotentials
import SGPT.IGood.SectionMinimalMultiplier
import SGPT.Okounkov.PartialBodyGeneral
import SGPT.Okounkov.TranscendentalCoreAlgebra
import SGPT.Okounkov.TranscendentalCoreValuationBounded
import SGPT.Okounkov.TranscendentalBodySingDecrease

/-!
# Multiplier section spaces, their valuative points and normalized section potentials

Infrastructure for the asymptotic Riemann–Roch formula `thm:DXmain1` (chapter *`𝓘`-good
singularities*, Section *The volumes of Hermitian pseudo-effective line bundles*), blueprint
chapter `claude-dxmain`.

## Formal setting

As in the algebraic Okounkov chapters: `X` is an integral smooth projective complex scheme of
dimension `n` (structure morphism `f`, closed projective embedding `E`), viewed through its
analytic point manifold `SchemeComplexPoint f`; `L` is a line bundle with a rank-one atlas `a`,
`H⁰(X, L^k) = SGPT.LineBundle.SectionSpace f L k`, and `s ∈ H⁰(X, L^k ⊗ 𝓘(kφ))` is the existing
condition `SGPT.Okounkov.IsMultiplierSection` (the coefficient of `s` in every local frame lies
in `𝓘(kφ)`, with `𝓘(0·φ) = 𝒪_X`).

## Main results

* `multiplierSubmodule`: for quasi-psh `φ`, the multiplier sections form a complex subspace
  `H⁰(X, L^k ⊗ 𝓘(kφ)) ⊆ H⁰(X, L^k)`; `multiplierH0` is its dimension
  `h⁰(X, L^k ⊗ 𝓘(kφ))`.
* `card_sectionValues_eq_finrank`: for a smooth flag `Y•` of the analytic manifold and every
  subspace `V ⊆ H⁰(X, L^k)`, the number of flag valuations `ν(s)`, `s ∈ V \ {0}`, is `dim V`
  (one-dimensional leaves, `[LM09, Lemma 1.3]`).
* `normalizedPotential`: `ψ_s = k⁻¹ log |s|²_{H^k}` for a smooth metric `H`; it is `θ`-psh
  (`θ = c₁(L, H)`), has analytic singularities, defines a Kähler current in `θ + t ω` for
  `t > 0`, and `ν(ψ_s) = k⁻¹ ν(s)`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.IGood.DXMain

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set Filter MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Okounkov SGPT.LineBundle
open scoped Topology ENNReal

section Integrability

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [MeasurableSpace V]

/-- Multiplier integrability is preserved by constant multiples: `g ∈ 𝓘(φ) ⇒ b g ∈ 𝓘(φ)`. -/
theorem multiplierIntegrableAt_const_mul {φ : V → EReal} {c : ℝ} {g : V → ℂ} {x : V}
    {μ : Measure V} (hg : MultiplierIntegrableAt φ c g x μ) (b : ℂ) :
    MultiplierIntegrableAt φ c (fun y => b * g y) x μ := by
  obtain ⟨hc, U, hU, hxU, hhol, hmeas, hint⟩ := hg
  have hden : multiplierDensity φ c (fun y => b * g y) =
      fun y => ENNReal.ofReal (‖b‖ ^ 2) * multiplierDensity φ c g y := by
    funext y
    simp only [multiplierDensity, norm_mul, mul_pow]
    rw [ENNReal.ofReal_mul (sq_nonneg _), mul_assoc]
  refine ⟨hc, U, hU, hxU, hhol.const_mul b, ?_, ?_⟩
  · rw [hden]
    exact hmeas.const_mul _
  · rw [hden, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hint

end Integrability

variable {X : Scheme} (f : X ⟶ Spec (.of ℂ)) (n : ℕ) [SmoothOfRelativeDimension n f]
  (E : ClosedProjectiveEmbedding f)

local instance dxSectionsTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance dxSectionsCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance dxSectionsManifold [IsSeparated f] [QuasiCompact f] :
    IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n

section Coefficients

variable {L : X.Modules}

/-- Frame coefficients are additive on the frame domain. -/
theorem sectionFrameCoefficient_add {U : X.Opens} (α : LocalBundleFrame L U) (k : ℕ)
    (s t : bundlePowerGlobalSections L k) {p : SchemeComplexPoint f}
    (hp : schemeComplexPointImage f p ∈ U) :
    sectionFrameCoefficient f n E α k (s + t) p =
      sectionFrameCoefficient f n E α k s p + sectionFrameCoefficient f n E α k t p := by
  unfold sectionFrameCoefficient
  rw [map_add, map_add]
  exact schemeOpenRegularFunction_add f n E U _ _ hp

/-- Frame coefficients are `ℂ`-homogeneous on the frame domain. -/
theorem sectionFrameCoefficient_smul {U : X.Opens} (α : LocalBundleFrame L U) (k : ℕ) (c : ℂ)
    (s : SectionSpace f L k) {p : SchemeComplexPoint f}
    (hp : schemeComplexPointImage f p ∈ U) :
    sectionFrameCoefficient f n E α k (c • s : SectionSpace f L k) p =
      c * sectionFrameCoefficient f n E α k s p := by
  let := E.isSeparated
  let := E.quasiCompact
  have hco : (α.tensorPower k).coefficients (𝟙 U)
      ((bundleTensorPower L k).val.map (homOfLE le_top).op (c • s : SectionSpace f L k)) =
      X.sheaf.obj.map (homOfLE (le_top : U ≤ ⊤)).op (schemeGlobalConstants f c) *
        (α.tensorPower k).coefficients (𝟙 U)
          ((bundleTensorPower L k).val.map (homOfLE le_top).op s) := by
    have h := (bundleTensorPower L k).val.map_smul (homOfLE (le_top : U ≤ ⊤)).op
      (schemeGlobalConstants f c) s
    exact (congrArg ((α.tensorPower k).coefficients (𝟙 _)) h).trans
      (((α.tensorPower k).coefficients (𝟙 _)).map_smul _ _)
  unfold sectionFrameCoefficient
  rw [hco, schemeOpenRegularFunction_mul f n E U _ _ hp]
  beta_reduce
  congr 1
  rw [schemeOpenRegularFunction_apply f n E U _ p hp]
  have hg := TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE (le_top : U ≤ ⊤))
    (schemeComplexPointImage f p) hp (schemeGlobalConstants f c)
  erw [hg]
  exact schemeNativeStalkGerm_eval_const f n p c

end Coefficients

section Submodule

variable {L : X.Modules}

/-- Sums of multiplier sections are multiplier sections (for quasi-psh weights). -/
theorem isMultiplierSection_add {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      ManifoldQuasiPlurisubharmonic (n := n) φ)
    {k : ℕ} {s t : bundlePowerGlobalSections L k} (hs : IsMultiplierSection f n E φ k s)
    (ht : IsMultiplierSection f n E φ k t) : IsMultiplierSection f n E φ k (s + t) := by
  let := E.isSeparated
  let := E.quasiCompact
  rcases hs with h0 | hs
  · exact Or.inl h0
  rcases ht with h0 | ht
  · exact Or.inl h0
  right
  intro U α p hp
  obtain ⟨-, hsi⟩ := hs U α p hp
  obtain ⟨-, hti⟩ := ht U α p hp
  set e := complexChartAt (n := n) p
  have hpe : p ∈ e.val.source := mem_complexChartAt_source p
  have hz := e.val.map_source hpe
  have hD : IsOpen (e.val.target ∩ e.val.symm ⁻¹' (schemeComplexPointImage f ⁻¹' U)) :=
    e.val.isOpen_inter_preimage_symm (U.isOpen.preimage (schemeComplexPointImage_continuous f))
  have hz0D : e.val p ∈ e.val.target ∩ e.val.symm ⁻¹' (schemeComplexPointImage f ⁻¹' U) := by
    refine ⟨hz, ?_⟩
    change schemeComplexPointImage f (e.val.symm (e.val p)) ∈ U
    rw [e.val.left_inv hpe]
    exact hp
  refine ⟨schemeOpenRegularFunction_holomorphicAt f n E U _ p hp, ?_⟩
  refine (multiplierIntegrableAt_add (hφ e _ hz) hsi hti).congr
    (Filter.EventuallyEq.refl _ _) ?_
  filter_upwards [hD.mem_nhds hz0D] with z hz'
  exact (sectionFrameCoefficient_add f n E α k s t hz'.2).symm

/-- Complex multiples of multiplier sections are multiplier sections. -/
theorem isMultiplierSection_smul {φ : SchemeComplexPoint f → EReal} {k : ℕ} (c : ℂ)
    {s : SectionSpace f L k} (hs : IsMultiplierSection f n E φ k s) :
    IsMultiplierSection f n E φ k (c • s : SectionSpace f L k) := by
  let := E.isSeparated
  let := E.quasiCompact
  rcases hs with h0 | hs
  · exact Or.inl h0
  right
  intro U α p hp
  obtain ⟨-, hsi⟩ := hs U α p hp
  set e := complexChartAt (n := n) p
  have hpe : p ∈ e.val.source := mem_complexChartAt_source p
  have hz := e.val.map_source hpe
  have hD : IsOpen (e.val.target ∩ e.val.symm ⁻¹' (schemeComplexPointImage f ⁻¹' U)) :=
    e.val.isOpen_inter_preimage_symm (U.isOpen.preimage (schemeComplexPointImage_continuous f))
  have hz0D : e.val p ∈ e.val.target ∩ e.val.symm ⁻¹' (schemeComplexPointImage f ⁻¹' U) := by
    refine ⟨hz, ?_⟩
    change schemeComplexPointImage f (e.val.symm (e.val p)) ∈ U
    rw [e.val.left_inv hpe]
    exact hp
  refine ⟨schemeOpenRegularFunction_holomorphicAt f n E U _ p hp, ?_⟩
  refine (multiplierIntegrableAt_const_mul hsi c).congr (Filter.EventuallyEq.refl _ _) ?_
  filter_upwards [hD.mem_nhds hz0D] with z hz'
  exact (sectionFrameCoefficient_smul f n E α k c s hz'.2).symm

/-- **`H⁰(X, L^k ⊗ 𝓘(kφ))`** (the section spaces of `thm:DXmain1`): for a quasi-psh weight `φ`,
the sections of `L^k` whose coefficients in every local frame lie in `𝓘(kφ)` form a complex
subspace of `H⁰(X, L^k)`. -/
def multiplierSubmodule {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      ManifoldQuasiPlurisubharmonic (n := n) φ) (L : X.Modules) (k : ℕ) :
    Submodule ℂ (SectionSpace f L k) where
  carrier := {s | IsMultiplierSection f n E φ k s}
  zero_mem' := isMultiplierSection_zero (f := f) (n := n) (E := E) φ k
  add_mem' := fun hs ht => isMultiplierSection_add f n E hφ hs ht
  smul_mem' := fun c _ hs => isMultiplierSection_smul f n E c hs

theorem mem_multiplierSubmodule {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      ManifoldQuasiPlurisubharmonic (n := n) φ) (L : X.Modules) (k : ℕ)
    (s : SectionSpace f L k) :
    s ∈ multiplierSubmodule f n E hφ L k ↔ IsMultiplierSection f n E φ k s := by
  rfl

/-- **`h⁰(X, L^k ⊗ 𝓘(kφ))`**, the dimension of the multiplier section space. -/
def multiplierH0 {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      ManifoldQuasiPlurisubharmonic (n := n) φ) (L : X.Modules) (k : ℕ) : ℕ :=
  Module.finrank ℂ (multiplierSubmodule f n E hφ L k)

/-- `h⁰(X, L^k ⊗ 𝓘(kφ)) ≤ h⁰(X, L^k)`. -/
theorem multiplierH0_le_h0 {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      ManifoldQuasiPlurisubharmonic (n := n) φ) {L : X.Modules} (a : LineBundleAtlas L)
    (k : ℕ) : multiplierH0 f n E hφ L k ≤ h0 f L k := by
  have := SectionSpace.finiteDimensional f E a k
  exact Submodule.finrank_le _

end Submodule

section Values

variable [IsIntegral X] (Y : Fin (n + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y)
  {L : X.Modules} (a : LineBundleAtlas L)

/-- The flag vectors `ν(s) ∈ ℕⁿ` of the nonzero sections `s` of a subspace `V ⊆ H⁰(X, L^k)`. -/
def sectionValues (k : ℕ) (V : Submodule ℂ (SectionSpace f L k)) : Set (Fin n → ℕ) :=
  {v | ∃ (s : SectionSpace f L k) (hs : s ≠ 0), s ∈ V ∧
    schemeFubiniStudySectionVector f n E Y hY a k s hs = v}

/-- **Valuative points count dimensions** (`[LM09, Lemma 1.3]`): for every subspace
`V ⊆ H⁰(X, L^k)`, `#{ν(s) : s ∈ V \ {0}} = dim V`. -/
theorem card_sectionValues_eq_finrank (k : ℕ) (V : Submodule ℂ (SectionSpace f L k)) :
    Nat.card (sectionValues f n E Y hY a k V) = Module.finrank ℂ V := by
  let := E.isSeparated
  let := E.quasiCompact
  let ω := schemeProjectiveTNKahlerBackground f n E
  let F := schemeProjectiveOriginalFlagGeometry f n E ω Y hY
  let x := schemeProjectiveOriginalFlagPoint f n E ω Y hY
  let := schemeNativeFractionComplexAlgebra f n x.val
  let G : SectionSpace f L k →ₗ[ℂ] FractionRing (NativeHolGerm n (SchemeComplexPoint f) x.val) :=
    schemePointPowerGlobalSectionsGerm f n x.val a k
  have hinj : Function.Injective G := schemePointPowerGlobalSectionsGerm_injective f n x.val a k
  let W := V.map G
  have := SectionSpace.finiteDimensional f E a k
  have hfdW : FiniteDimensional ℂ W := inferInstance
  have hW : Module.finrank ℂ W = Module.finrank ℂ V :=
    (Submodule.equivMapOfInjective G hinj V).finrank_eq.symm
  have hcard := @originalFlagGermFractionValues_card_eq_finrank n F x W hfdW
  let ι : (Fin n → ℕ) → WithTop (Lex (Fin n → ℤ)) :=
    fun v => ((toLex (fun i => (v i : ℤ)) : Lex (Fin n → ℤ)) : WithTop (Lex (Fin n → ℤ)))
  have hι : Function.Injective ι := by
    intro v w h
    have h1 := WithTop.coe_injective h
    have h2 := toLex_inj.mp h1
    funext i
    exact_mod_cast congrFun h2 i
  have hval : ∀ (s : SectionSpace f L k) (hs : s ≠ 0),
      originalFlagGermFractionValuation F x (G s) =
        ι (schemeFubiniStudySectionVector f n E Y hY a k s hs) := by
    intro s hs
    have h := schemeFubiniStudySectionValue_vector f n E Y hY a k s hs
    exact h
  have hset : ι '' sectionValues f n E Y hY a k V = originalFlagGermFractionValues F x W := by
    ext v
    change _ ↔ ∃ w : W, w ≠ 0 ∧ originalFlagGermFractionValuation F x (W.subtype w) = v
    constructor
    · rintro ⟨_, ⟨s, hs, hsV, rfl⟩, rfl⟩
      refine ⟨⟨G s, s, hsV, rfl⟩, ?_, hval s hs⟩
      intro h0
      apply hs
      apply hinj
      have := congrArg Subtype.val h0
      simpa using this
    · rintro ⟨⟨w, s, hsV, rfl⟩, hw, rfl⟩
      have hs : s ≠ 0 := by
        rintro rfl
        apply hw
        apply Subtype.ext
        simp
      exact ⟨_, ⟨s, hs, hsV, rfl⟩, (hval s hs).symm⟩
  calc Nat.card (sectionValues f n E Y hY a k V)
      = Nat.card (ι '' sectionValues f n E Y hY a k V) :=
        (Nat.card_image_of_injective hι _).symm
    _ = Nat.card (originalFlagGermFractionValues F x W) := by rw [hset]
    _ = Module.finrank ℂ W := hcard
    _ = Module.finrank ℂ V := hW

end Values

section Potentials

variable [IsIntegral X] {L : X.Modules} (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f n E L)

/-- **The normalized potential** `ψ_s = k⁻¹ log |s|²_{H^k}` of a section `s ∈ H⁰(X, L^k)`; for
`s ≠ 0`, `θ + dd^c ψ_s = k⁻¹ [div s]`. -/
def normalizedPotential (k : ℕ) (s : bundlePowerGlobalSections L k) :
    SchemeComplexPoint f → EReal :=
  fun p => (((k : ℝ)⁻¹ : ℝ) : EReal) * H.sectionLogNormSq a k s p

theorem isThetaPshPotential_normalizedPotential {k : ℕ} (hk : 0 < k)
    {s : bundlePowerGlobalSections L k} (hs : s ≠ 0) :
    letI := E.isSeparated
    letI := E.quasiCompact
    IsThetaPshPotential (H.curvature a).val (normalizedPotential f n E a H k s) :=
  H.isThetaPshPotential_normalized_sectionLogNormSq a k hk s hs

theorem hasManifoldAnalyticSingularityType_normalizedPotential {k : ℕ}
    {s : bundlePowerGlobalSections L k} (hs : s ≠ 0) :
    letI := E.isSeparated
    letI := E.quasiCompact
    QuasiEquisingularApproximation.HasManifoldAnalyticSingularityType (n := n)
      (normalizedPotential f n E a H k s) := by
  let := E.isSeparated
  let := E.quasiCompact
  have h := (H.sectionLogNormSq_hasAnalyticSingularities a k s hs).hasManifoldAnalyticSingularityType
  have h' := TranscendentalCore.hasManifoldAnalyticSingularityType_nonneg_rat_smul h
    (r := ((k : ℚ))⁻¹) (by positivity)
  have hcast : ((((k : ℚ))⁻¹ : ℚ) : ℝ) = (k : ℝ)⁻¹ := by push_cast; ring
  have hfun : normalizedPotential f n E a H k s =
      fun x => (((((k : ℚ))⁻¹ : ℚ) : ℝ) : EReal) * H.sectionLogNormSq a k s x := by
    funext x
    rw [hcast]
    rfl
  rw [hfun]
  exact h'

theorem normalizedPotential_mem_analyticCurrents {k : ℕ} (hk : 0 < k)
    {s : bundlePowerGlobalSections L k} (hs : s ≠ 0)
    (θ' : letI := E.isSeparated; letI := E.quasiCompact; ClosedRealOneOneForm n (SchemeComplexPoint f))
    (hle : letI := E.isSeparated; letI := E.quasiCompact; (θ' - H.curvature a).val.IsSemipositive) :
    letI := E.isSeparated
    letI := E.quasiCompact
    normalizedPotential f n E a H k s ∈ TranscendentalCore.analyticCurrents θ' := by
  let := E.isSeparated
  let := E.quasiCompact
  exact ⟨TranscendentalBody.isThetaPshPotential_of_le
      (isThetaPshPotential_normalizedPotential f n E a H hk hs) hle,
    hasManifoldAnalyticSingularityType_normalizedPotential f n E a H hs⟩

theorem isKahlerCurrentPotential_normalizedPotential {k : ℕ} (hk : 0 < k)
    {s : bundlePowerGlobalSections L k} (hs : s ≠ 0)
    (ω : letI := E.isSeparated; letI := E.quasiCompact;
      FirstPass.PositiveClasses.KahlerBackground n (SchemeComplexPoint f)) {t : ℝ} (ht : 0 < t) :
    letI := E.isSeparated
    letI := E.quasiCompact
    AnalyticGluingData.IsKahlerCurrentPotential (H.curvature a + t • ω.form)
      (normalizedPotential f n E a H k s) := by
  let := E.isSeparated
  let := E.quasiCompact
  exact PartialBody.isKahlerCurrentPotential_add_smul
    (isThetaPshPotential_normalizedPotential f n E a H hk hs) ω ht

end Potentials

section PotentialValuation

variable [IsIntegral X] {m : ℕ} [SmoothOfRelativeDimension (m + 1) f]
  (Y : Fin (m + 1 + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y)
  {L : X.Modules} (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f (m + 1) E L)

/-- `ν(ψ_s) = k⁻¹ ν(s)`. -/
theorem flagValuation_normalizedPotential {k : ℕ}
    (s : bundlePowerGlobalSections L k) (hs : s ≠ 0) :
    TranscendentalCore.flagValuation (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY)
        (normalizedPotential f (m + 1) E a H k s) =
      (k : ℝ)⁻¹ • (fun i => (schemeFubiniStudySectionVector f (m + 1) E Y hY a k s hs i : ℝ)) := by
  let := E.isSeparated
  let := E.quasiCompact
  have hu := H.isThetaPshPotential_sectionLogNormSq a k s hs
  have hkR : (0 : ℝ) ≤ (k : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg k)
  have h := TranscendentalCore.flagValuation_smul
    (F := schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) hu hkR
  rw [schemeFubiniStudySectionVector_eq_flagValuation f m E Y hY a H k s hs]
  exact h

end PotentialValuation

end SGPT.IGood.DXMain
