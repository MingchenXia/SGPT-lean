import SGPT.GAGA.H0LSections
import SGPT.IGood.DXLow2DXMain
import SGPT.IGood.DXMainStatement
import SGPT.TestCurve.SkodaRWNMultiplier

/-!
# The lower bound of `thm:DXmain1` for algebraic sections


Source `thm:DXmain1` (chapter *`𝓘`-good singularities*), in the projective-scheme form of lane
DXMAIN (`SGPT.IGood.DXMain.DXMainLowerBound`): for an integral smooth projective complex scheme
`X` of dimension `n = m + 1` with connected analytic space, a line bundle `L` with atlas `a` and
smooth metric `H`, `θ = c₁(L, H)` and `φ ∈ PSH(X, θ)`,

`vol θ_φ ≤ liminf_k n! h⁰(X, L^k ⊗ 𝓘(kφ)) / kⁿ`,

`h⁰` counting the *algebraic* sections `σ ∈ H⁰(X, L^k)` whose coefficients in every local frame
lie in `𝓘(kφ)` (`SGPT.IGood.DXMain.multiplierH0`).

* `algSectionLinear`: by GAGA (`SGPT.GAGA.H0L.exists_isAnalytificationOf`), every holomorphic
  section `s` of `((L, H)^an)^{⊗ k}` has a unique algebraic section `σ` with `σ^an = s`; the map
  `s ↦ σ` is `ℂ`-linear and injective.
* `isMultiplierSection_algSection`: if `∫ |s|² e^{-kφ} dμ < ∞` (`s` in the literal section space
  `LiteralTwistedMultiplierSections` of `def:Bergman:L778`, in its `L²` description), then
  `σ ∈ H⁰(X, L^k ⊗ 𝓘(kφ))`.  Hence `finrank_literal_le_multiplierH0`:
  `dim Γ(X, L^k ⊗ 𝓘(kφ))^{an} ≤ h⁰(X, L^k ⊗ 𝓘(kφ))` (equality holds; only `≤` is needed).
* `iVolume_congr_geometricallyEq`: the `𝓘`-volume only depends on the background form up to
  geometric equality; the Chern form of the analytification `(L, H)^an` is geometrically equal to
  `H.curvature a`, so the analytic volume `sourceIVolume` is the scheme volume `iVolume`.
* **`dxMainLowerBound`**: `DXMainLowerBound` for every `(X, L, H, φ)` (`X` with connected analytic
  space), from the analytic lower bound `riemannRochLowerBound_of_kahler`; with the
  proved upper bound, **`dxMain1Holds`** (`thm:DXmain1`, `T = 𝒪_X`) on `X` with a smooth flag.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.GAGA.H0L

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Filter Set Bundle MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.IEnvelope SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Okounkov SGPT.NAPotential.FSPos SGPT.NAPotential.GAGAMult SGPT.GAGA.H0S SGPT.LineBundle
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle
open SGPT.Bergman.MultiplierSectionsDraft SGPT.Bergman.PolynomialH0Growth
open SGPT.Bergman.NativeHermitianMetric SGPT.PSH.VariableComplexAtlas
open scoped Topology Manifold ENNReal

/-! ### The `𝓘`-volume depends on the background only up to geometric equality -/

section Geometric

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- The `𝓘`-envelope `P_θ[φ]_𝓘` only depends on `θ` up to geometric equality. -/
theorem iSingularityEnvelope_geometricallyEq {θ η : SmoothRealForm n M 2}
    (h : θ.GeometricallyEq η) (φ : M → EReal) :
    iSingularityEnvelope θ φ = iSingularityEnvelope η φ := by
  unfold iSingularityEnvelope iSingularitySupremum iSingularityCompetitors
  rw [thetaPshCompetitors_geometricallyEq h]

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [Nonempty M]

/-- **The `𝓘`-volume `vol θ_φ` only depends on `θ` up to geometric equality.** -/
theorem iVolume_congr_geometricallyEq {θ η : ClosedRealOneOneForm n M}
    (h : θ.val.GeometricallyEq η.val) (hθ : HasSmoothLocalPotentials θ.val)
    (hη : HasSmoothLocalPotentials η.val) (φ : M → EReal) (hφθ : IsThetaPshPotential θ.val φ)
    (hφη : IsThetaPshPotential η.val φ) :
    iVolume θ hθ φ hφθ = iVolume η hη φ hφη := by
  unfold iVolume
  have he := iSingularityEnvelope_geometricallyEq h φ
  have key : ∀ (u v : M → EReal), u = v → ∀ (hu : IsThetaPshPotential η.val u)
      (hv : IsThetaPshPotential η.val v),
      DiagonalMass.diagonalPotentialMass η u hu = DiagonalMass.diagonalPotentialMass η v hv := by
    rintro u v rfl hu hv
    rfl
  have h1 : IsThetaPshPotential η.val (iSingularityEnvelope θ.val φ) := by
    rw [he]
    exact iSingularityEnvelope_isThetaPshPotential η.val η.property.1 η.property.2 hη φ hφη
  rw [ModificationMassInvariance.diagonalPotentialMass_congr_geometricallyEq h _ h1]
  exact key _ _ he _ _

end Geometric

/-! ### The algebraic section of a holomorphic section -/

section Scheme

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} {E : ClosedProjectiveEmbedding f} {n : ℕ}
  [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f]

local instance h0lDXTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance h0lDXCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance h0lDXManifold : IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n
local instance h0lDXMeasurable : MeasurableSpace (SchemeComplexPoint f) := borel _
local instance h0lDXBorel : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩

omit [IsSeparated f] [QuasiCompact f] in
/-- The analytic function of a complex constant is constant. -/
theorem schemeOpenRegularFunction_globalConstant (U : X.Opens) (c : ℂ) {p : SchemeComplexPoint f}
    (hp : schemeComplexPointImage f p ∈ U) :
    schemeOpenRegularFunction f n E U
      (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (schemeGlobalConstants f c)) p = c := by
  let := E.isSeparated
  let := E.quasiCompact
  rw [schemeOpenRegularFunction_restrict f n E U ⊤ le_top _ hp,
    schemeOpenRegularFunction_apply f n E ⊤ _ p trivial, ← NativeHolGerm.eval_chartEquiv]
  have h2 := stalkToModel_constants f n p c
  change HolGerm.eval (stalkToModel f n p _) = c
  rw [h2]
  rfl

variable {L : X.Modules} (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f n E L) {k : ℕ}

/-- `(s + t)^alg = s^alg + t^alg`. -/
theorem isAnalytificationOf_add {s t : twistedSections (schemeHermitianLineBundle f n E a H) unit k}
    {σ τ : SectionSpace f L k} (hs : IsAnalytificationOf f n E a H s σ)
    (ht : IsAnalytificationOf f n E a H t τ) :
    IsAnalytificationOf f n E a H (s + t) (σ + τ : SectionSpace f L k) := by
  intro i p hp
  have hadd : algCoef (a.frame i) k (σ + τ : SectionSpace f L k) =
      algCoef (a.frame i) k σ + algCoef (a.frame i) k τ := by
    simp only [algCoef, map_add]
  rw [hadd, schemeOpenRegularFunction_add f n E _ _ _ hp]
  beta_reduce
  rw [← hs i p hp, ← ht i p hp, ContMDiffSection.coe_add, Pi.add_apply, map_add]

/-- `(c • s)^alg = c • s^alg`. -/
theorem isAnalytificationOf_smul (c : ℂ)
    {s : twistedSections (schemeHermitianLineBundle f n E a H) unit k}
    {σ : SectionSpace f L k} (hs : IsAnalytificationOf f n E a H s σ) :
    IsAnalytificationOf f n E a H (c • s) (c • σ : SectionSpace f L k) := by
  intro i p hp
  have hsm : algCoef (a.frame i) k (c • σ : SectionSpace f L k) =
      X.presheaf.map (homOfLE (le_top : a.opens i ≤ ⊤)).op (schemeGlobalConstants f c) *
        algCoef (a.frame i) k σ :=
    SectionSpace.atlasPowerGlobalCoefficients_smul_const f a k i c σ
  rw [hsm, schemeOpenRegularFunction_mul' f E n _ _ _ hp,
    schemeOpenRegularFunction_globalConstant (a.opens i) c hp, ← hs i p hp,
    ContMDiffSection.coe_smul, Pi.smul_apply, map_smul, smul_eq_mul]

variable [CompactSpace (SchemeComplexPoint f)]

/-- **The algebraic section of a holomorphic section** of `((L, H)^an)^{⊗ k}` (GAGA). -/
def algSection (s : twistedSections (schemeHermitianLineBundle f n E a H) unit k) :
    SectionSpace f L k :=
  Classical.choose (exists_isAnalytificationOf a H s)

theorem isAnalytificationOf_algSection
    (s : twistedSections (schemeHermitianLineBundle f n E a H) unit k) :
    IsAnalytificationOf f n E a H s (algSection a H s) :=
  Classical.choose_spec (exists_isAnalytificationOf a H s)

/-- The GAGA map `s ↦ s^alg` is `ℂ`-linear. -/
def algSectionLinear :
    twistedSections (schemeHermitianLineBundle f n E a H) unit k →ₗ[ℂ] SectionSpace f L k where
  toFun := algSection a H
  map_add' s t := eq_of_isAnalytificationOf (isAnalytificationOf_algSection a H (s + t))
    (isAnalytificationOf_add a H (isAnalytificationOf_algSection a H s)
      (isAnalytificationOf_algSection a H t))
  map_smul' c s := eq_of_isAnalytificationOf (isAnalytificationOf_algSection a H (c • s))
    (isAnalytificationOf_smul a H c (isAnalytificationOf_algSection a H s))

/-- The GAGA map `s ↦ s^alg` is injective. -/
theorem algSectionLinear_injective : Function.Injective (algSectionLinear a H (k := k)) := by
  rw [injective_iff_map_eq_zero]
  intro s hs
  have h0 : IsAnalytificationOf f n E a H s (0 : SectionSpace f L k) :=
    hs ▸ isAnalytificationOf_algSection a H s
  apply ContMDiffSection.ext
  intro p
  obtain ⟨i, hi⟩ := a.covers (schemeComplexPointImage f p)
  set e := twistedFrame f n E a H (a.frame i) k
  have he : p ∈ e.val.baseSet := mem_twistedFrame_baseSet f n E a H _ k hi
  have hc := h0 i p hi
  have halg0 : algCoef (a.frame i) k (0 : SectionSpace f L k) = 0 := by
    simp only [algCoef, map_zero]
  rw [halg0, schemeOpenRegularFunction_zero' f E n _ p hi,
    ← Trivialization.coe_continuousLinearEquivAt_eq e.val he] at hc
  rw [ContMDiffSection.coe_zero, Pi.zero_apply]
  exact (e.val.continuousLinearEquivAt ℂ p he).map_eq_zero_iff.mp hc

/-- If `∫_X |s|² e^{-kφ} dμ < ∞` (`μ` a smooth positive volume, `φ` `θ`-psh), the algebraic
section `s^alg` is a section of `L^k ⊗ 𝓘(kφ)`. -/
theorem isMultiplierSection_algSection {φ : SchemeComplexPoint f → EReal}
    (hφ : IsThetaPshPotential (H.curvature a).val φ) {μ : Measure (SchemeComplexPoint f)}
    (hμ : IsSmoothPositiveVolume (n := n) μ)
    {s : twistedSections (schemeHermitianLineBundle f n E a H) unit k}
    (hs : ∫⁻ x, originalSectionDensity (n := n)
      (twistedPower (schemeHermitianLineBundle f n E a H) unit k).Fiber φ k s x ∂μ < ⊤) :
    IsMultiplierSection f n E φ k (algSection a H s) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact Or.inl rfl
  refine SGPT.TestCurve.SkodaRWN.isMultiplierSection_of_lintegral_lt_top (a := a) H hμ
    hφ.1.quasiPlurisubharmonic.upperSemicontinuous.measurable hk _ ?_
  have hn := SGPT.TestCurve.SkodaRWN.norm_sq_eq_sectionNormSq_of_isAnalytificationOf H a
    (isAnalytificationOf_algSection a H s)
  simp only [originalSectionDensity, hn] at hs
  exact hs

/-- **`dim Γ(X, L^k ⊗ 𝓘(kφ))^{an} ≤ h⁰(X, L^k ⊗ 𝓘(kφ))`**: the literal analytic section space
of `def:Bergman:L778` for `(L, H)^an` injects into the algebraic multiplier sections. -/
theorem finrank_literal_le_multiplierH0 {φ : SchemeComplexPoint f → EReal}
    (hφ : IsThetaPshPotential (H.curvature a).val φ) (k : ℕ) :
    Module.finrank ℂ (LiteralTwistedMultiplierSections (schemeHermitianLineBundle f n E a H)
      unit k φ) ≤ SGPT.IGood.DXMain.multiplierH0 f n E hφ.1.quasiPlurisubharmonic L k := by
  let ωb := schemeProjectiveTNKahlerBackground f n E
  let μ := IntegrationCurrent.kahlerVolume ωb
  have hμ : IsSmoothPositiveVolume (n := n) μ :=
    KahlerVolumeSmoothPositive.isSmoothPositiveVolume_kahlerVolume ωb
  have hq : IsGlobalQuasiPshPotential (n := n) φ := ⟨hφ.1.quasiPlurisubharmonic, hφ.2⟩
  rw [(literalTwistedMultiplierL2Equiv _ unit k hq μ hμ).finrank_eq]
  let W := twistedMultiplierL2Submodule (schemeHermitianLineBundle f n E a H) unit k hq μ hμ
  let Φ : W →ₗ[ℂ] SGPT.IGood.DXMain.multiplierSubmodule f n E hφ.1.quasiPlurisubharmonic L k :=
    ((algSectionLinear a H).domRestrict W).codRestrict _
      (fun s => isMultiplierSection_algSection a H hφ hμ s.2)
  have : FiniteDimensional ℂ (SectionSpace f L k) := SectionSpace.finiteDimensional f E a k
  refine LinearMap.finrank_le_finrank_of_injective (f := Φ) fun s t hst => ?_
  apply Subtype.ext
  apply algSectionLinear_injective a H
  exact congrArg Subtype.val hst

end Scheme

/-! ### The lower bound of `thm:DXmain1` -/

section Lower

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} {E : ClosedProjectiveEmbedding f} {m : ℕ}
  [SmoothOfRelativeDimension (m + 1) f]

local instance h0lLowTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance h0lLowCharts : ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (m + 1)
local instance h0lLowManifold [IsSeparated f] [QuasiCompact f] :
    IsComplexManifold (m + 1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (m + 1)
local instance h0lLowMeasurable : MeasurableSpace (SchemeComplexPoint f) := borel _
local instance h0lLowBorel : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩

variable {L : X.Modules} (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f (m + 1) E L)

/-- The normalized analytic dimensions are at most the algebraic ones:
`n!/kⁿ dim Γ(X, L^k ⊗ 𝓘(kφ))^{an} ≤ n! h⁰(X, L^k ⊗ 𝓘(kφ)) / kⁿ` for `k ≥ 1`. -/
theorem normalizedH0_le_normalizedMultiplierH0 {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val φ) {k : ℕ} (hk : 1 ≤ k) :
    letI := E.isSeparated
    letI := E.quasiCompact
    SGPT.Bergman.Quant2.normalizedH0 (schemeHermitianLineBundle f (m + 1) E a H) unit φ k ≤
      SGPT.IGood.DXMain.normalizedMultiplierH0 f E a H hφ k := by
  let := E.isSeparated
  let := E.quasiCompact
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  have hle := finrank_literal_le_multiplierH0 a H hφ k
  unfold SGPT.Bergman.Quant2.normalizedH0 SGPT.IGood.DXMain.normalizedMultiplierH0
  have hkpos : (0 : ℝ) < (k : ℝ) ^ (m + 1) := pow_pos (by exact_mod_cast hk) _
  rw [div_mul_eq_mul_div, ENNReal.ofReal_div_of_pos hkpos, ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_natCast, ENNReal.ofReal_natCast, ENNReal.ofReal_pow (Nat.cast_nonneg _),
    ENNReal.ofReal_natCast]
  gcongr

/-- **The lower bound of `thm:DXmain1`** (`DXMainLowerBound`, the half left open by lane DXMAIN):
for every integral smooth projective complex scheme `X` of dimension `m + 1` with connected
analytic space, every line bundle `L` with atlas `a` and smooth metric `H` (`θ = c₁(L, H)`) and
every `φ ∈ PSH(X, θ)`, `vol θ_φ ≤ liminf_k n! h⁰(X, L^k ⊗ 𝓘(kφ)) / kⁿ`.  Proof: lane DX-LOW2's
analytic lower bound for `(L, H)^an` (`riemannRochLowerBound_of_kahler`), the identification of
the volumes (`iVolume_congr_geometricallyEq`) and of the section spaces through GAGA
(`normalizedH0_le_normalizedMultiplierH0`). -/
theorem dxMainLowerBound [Nonempty (SchemeComplexPoint f)] [ConnectedSpace (SchemeComplexPoint f)]
    {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val φ) :
    SGPT.IGood.DXMain.DXMainLowerBound f E a H hφ := by
  let := E.isSeparated
  let := E.quasiCompact
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  set Lan := schemeHermitianLineBundle f (m + 1) E a H with hLan
  have hL := isSourceSmoothHermitianMetric_schemeHermitianLineBundle f (m + 1) E a H
  have hgeq : (sourceNativeFirstChernForm Lan hL).val.GeometricallyEq (H.curvature a).val :=
    sourceNativeFirstChernForm_geometricallyEq Lan hL
      (isOwnFirstChernForm_schemeHermitianLineBundle f (m + 1) E a H)
  have hφ' : (ofFixedModel (m + 1) (SchemeComplexPoint f)).IsThetaPSH
      (SGPT.Bergman.Quant2.chernForm Lan hL) φ :=
    (isThetaPSH_iff_nativeThetaPotential _ φ).mpr (by
      rw [SGPT.Bergman.Quant2.chernForm, sourceNativeAtlasForm_roundTrip]
      exact (hgeq.thetaPshPotential_iff φ).mpr hφ)
  obtain ⟨hφ'', hRR⟩ := SGPT.IGood.DXLow2.riemannRochLowerBound_of_kahler
    (schemeProjectiveTNKahlerBackground f (m + 1) E) hL SGPT.PSH.GlobalL2.isSourceSmoothHermitianMetric_unit hφ'
  have hvol : iVolume (H.curvature a) (LocalPotentials.closedRealOneOne_hasLocalPotentials _) φ hφ =
      sourceIVolume (SGPT.Bergman.Quant2.chernForm Lan hL) φ hφ'' := by
    rw [sourceIVolume_eq_native _ φ hφ'' (LocalPotentials.closedRealOneOne_hasLocalPotentials _)]
    have hgeq' : (H.curvature a).val.GeometricallyEq
        (atlasClosedFormToNative (SGPT.Bergman.Quant2.chernForm Lan hL)).val := by
      rw [SGPT.Bergman.Quant2.chernForm, sourceNativeAtlasForm_roundTrip]
      exact hgeq.symm
    exact iVolume_congr_geometricallyEq hgeq' _ _ φ hφ _
  unfold SGPT.IGood.DXMain.DXMainLowerBound
  rw [hvol]
  refine hRR.trans (liminf_le_liminf ?_)
  filter_upwards [eventually_ge_atTop 1] with k hk
  exact normalizedH0_le_normalizedMultiplierH0 a H hφ hk

/-- **Source `thm:DXmain1` with `T = 𝒪_X`, projective setting**: on an integral smooth projective
complex scheme `X` of dimension `m + 1` carrying a smooth flag `Y`, for every line bundle `L` with
a smooth metric `H` and every `φ ∈ PSH(X, c₁(L, H))`,
`lim_k n! h⁰(X, L^k ⊗ 𝓘(kφ)) / kⁿ = vol θ_φ`. -/
theorem dxMain1Holds [IsIntegral X] (Y : Fin (m + 1 + 1) → Set (SchemeComplexPoint f))
    (hY : IsSmoothFlag Y) [Nonempty (SchemeComplexPoint f)] {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val φ) :
    SGPT.IGood.DXMain.DXMain1Holds f E a H hφ := by
  let := E.isSeparated
  let := E.quasiCompact
  have : ConnectedSpace (SchemeComplexPoint f) := schemeSmoothFlag_connectedSpace f (m + 1) Y hY
  exact SGPT.IGood.DXMain.dxMain1Holds_of_lowerBound f E a H Y hY hφ (dxMainLowerBound a H hφ)

end Lower

end SGPT.GAGA.H0L
