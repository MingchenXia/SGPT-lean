import SGPT.GAGA.OkoCloseTwisted

/-!
# `thm:DXmain1` for an arbitrary twist `T`, and `X(ℂ)` connected for integral `X`


Setting of lane DXMAIN: `X` an integral smooth projective complex scheme of dimension `n = m + 1`
(closed projective embedding `E`), line bundles `T`, `L` with rank-one atlases, a smooth metric
`H` on `L`, `θ = c₁(L, H)`, `φ ∈ PSH(X, θ)`.

* **`connectedSpace_of_isIntegral`**: `X(ℂ)` is connected (for `X(ℂ) ≠ ∅`). Proof by GAGA for
  functions: the indicator function of a clopen subset of `X(ℂ)` is holomorphic, hence (the
  coefficient family of degree `0` of the trivial bundle, `exists_regular_of_holomorphic`) the
  analytic function of a global regular function `r`; then `r² = r` in the domain `Γ(X, 𝒪_X)`, so
  `r ∈ {0, 1}`.
* `dxMainLowerBound_of_isIntegral`: the lower bound `SGPT.GAGA.H0L.dxMainLowerBound`
  without the connectedness hypothesis.
* **`dxMainTwistedLowerBound`** (`DXMainTwistedLowerBound`, the lower bound of `thm:DXmain1` for
  every twist `T`): `vol θ_φ ≤ liminf_k n! h⁰(X, T ⊗ L^k ⊗ 𝓘(kφ)) / kⁿ`, from the analytic
  lower bound for `(L^an, T^an)` and GAGA for `T ⊗ L^k` (`finrank_literal_le_twistedMultiplierH0`).
* **`dxMain1TwistedHolds`**: `thm:DXmain1` for every `T` on `X` carrying a smooth flag.
* `SmoothFlagsExist` (the existence of a smooth flag on every integral smooth projective
  `X`, a consequence of Bertini's theorem) and **`dxMain1Statement_of_smoothFlagsExist`**,
  `dxMain1UntwistedStatement_of_smoothFlagsExist`: the projective statements of `thm:DXmain1`
  for all `X` reduce exactly to `SmoothFlagsExist`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.GAGA.OkoClose

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Filter Set Bundle MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.IEnvelope SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Okounkov SGPT.NAPotential.GAGAMult SGPT.GAGA.H0S SGPT.GAGA.H0L SGPT.LineBundle
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle
open SGPT.Bergman.MultiplierSectionsDraft SGPT.Bergman.PolynomialH0Growth
open SGPT.Bergman.NativeHermitianMetric SGPT.PSH.VariableComplexAtlas
open scoped Topology Manifold ENNReal

/-! ### `X(ℂ)` is connected for integral `X` -/

section Connected

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} {E : ClosedProjectiveEmbedding f} {n : ℕ}
  [SmoothOfRelativeDimension n f]

local instance okoConTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance okoConCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n

variable (f E n) in
/-- **GAGA for functions**: every holomorphic function on the compact complex manifold `X(ℂ)` is
the analytic function of a global regular function on `X`. (The degree-`0` coefficient family
of the trivial line bundle.) -/
theorem exists_regular_of_holomorphic [IsSeparated f] [QuasiCompact f]
    [CompactSpace (SchemeComplexPoint f)] {c : SchemeComplexPoint f → ℂ}
    (hc : ∀ p, letI := schemeAnalyticTN_isComplexManifold f n; HolomorphicAt n c p) :
    ∃ r : Γ(X, ⊤), ∀ p : SchemeComplexPoint f, c p = schemeOpenRegularFunction f n E ⊤ r p := by
  let := schemeAnalyticTN_isComplexManifold f n
  let a := (trivialIntrinsicLineBundle X).atlas
  have hfam : IsHolomorphicCoefficientFamily f E n a 0 (fun _ => c) :=
    ⟨fun _ p _ => hc p, fun _ _ p _ _ => by rw [pow_zero, one_mul]⟩
  obtain ⟨r, hr⟩ := isRegularOn_of_isHolomorphicCoefficientFamily hfam PUnit.unit
  exact ⟨r, fun p => hr p trivial⟩

variable (f E n) in
include E n in
/-- **`X(ℂ)` is connected for an integral smooth projective complex scheme `X`** (with
`X(ℂ) ≠ ∅`). -/
theorem connectedSpace_of_isIntegral [IsIntegral X] [Nonempty (SchemeComplexPoint f)] :
    ConnectedSpace (SchemeComplexPoint f) := by
  let := E.isSeparated
  let := E.quasiCompact
  let := schemeAnalyticTN_isComplexManifold f n
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  rw [connectedSpace_iff_clopen]
  refine ⟨inferInstance, fun A hA => ?_⟩
  classical
  set c : SchemeComplexPoint f → ℂ := fun p => if p ∈ A then 1 else 0 with hcdef
  have hhol : ∀ p, HolomorphicAt n c p := by
    intro p
    by_cases hp : p ∈ A
    · refine (holomorphicAt_const (n := n) (1 : ℂ)).congr ?_
      filter_upwards [hA.isOpen.mem_nhds hp] with q hq
      simp [hcdef, hq]
    · refine (holomorphicAt_const (n := n) (0 : ℂ)).congr ?_
      filter_upwards [hA.compl.isOpen.mem_nhds hp] with q hq
      simp only [hcdef, if_neg (show q ∉ A from hq)]
  obtain ⟨r, hr⟩ := exists_regular_of_holomorphic f E n hhol
  have hcc : ∀ p, c p * c p = c p := fun p => by
    by_cases hp : p ∈ A <;> simp [hcdef, hp]
  have hrr : r * r = r := eq_of_schemeOpenRegularFunction_eq f E n _ _ fun p hp => by
    rw [schemeOpenRegularFunction_mul' f E n _ _ _ hp, ← hr p, hcc]
  obtain ⟨p₀⟩ := ‹Nonempty (SchemeComplexPoint f)›
  have : Nonempty (⊤ : X.Opens) := ⟨⟨schemeComplexPointImage f p₀, trivial⟩⟩
  rcases (IsIdempotentElem.iff_eq_zero_or_one.mp hrr) with h0 | h1
  · left
    ext p
    simp only [mem_empty_iff_false, iff_false]
    intro hp
    have h := hr p
    rw [h0, schemeOpenRegularFunction_zero' f E n ⊤ p (show schemeComplexPointImage f p ∈ (⊤ : X.Opens) from trivial)] at h
    simp [hcdef, hp] at h
  · right
    ext p
    simp only [mem_univ, iff_true]
    by_contra hp
    have h := hr p
    rw [h1, schemeOpenRegularFunction_one f n E ⊤ (show schemeComplexPointImage f p ∈ (⊤ : X.Opens) from trivial)] at h
    simp [hcdef, hp] at h

end Connected

/-! ### The lower bound of `thm:DXmain1` for every twist -/

section Lower

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} {E : ClosedProjectiveEmbedding f} {m : ℕ}
  [SmoothOfRelativeDimension (m + 1) f]

local instance okoLowTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance okoLowCharts : ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (m + 1)
local instance okoLowManifold [IsSeparated f] [QuasiCompact f] :
    IsComplexManifold (m + 1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (m + 1)
local instance okoLowMeasurable : MeasurableSpace (SchemeComplexPoint f) := borel _
local instance okoLowBorel : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩

variable {L : X.Modules} (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f (m + 1) E L)

/-- **The lower bound of `thm:DXmain1` (`T = 𝒪_X`) on every integral `X`**: lane H0-GAGA3's
`SGPT.GAGA.H0L.dxMainLowerBound`, whose connectedness hypothesis holds by
`connectedSpace_of_isIntegral`. -/
theorem dxMainLowerBound_of_isIntegral [IsIntegral X] [Nonempty (SchemeComplexPoint f)]
    {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val φ) :
    SGPT.IGood.DXMain.DXMainLowerBound f E a H hφ := by
  have : ConnectedSpace (SchemeComplexPoint f) := connectedSpace_of_isIntegral f E (m + 1)
  exact dxMainLowerBound a H hφ

/-- The normalized analytic twisted dimensions are at most the algebraic ones:
`n!/kⁿ dim Γ(X, T ⊗ L^k ⊗ 𝓘(kφ))^{an} ≤ n! h⁰(X, T ⊗ L^k ⊗ 𝓘(kφ)) / kⁿ` for `k ≥ 1`. -/
theorem normalizedH0_le_normalizedTwistedH0 [IsIntegral X] {T : X.Modules} (aT : LineBundleAtlas T)
    (HT : SchemeLineBundleMetric f (m + 1) E T) {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val φ) {k : ℕ} (hk : 1 ≤ k) :
    letI := E.isSeparated
    letI := E.quasiCompact
    SGPT.Bergman.Quant2.normalizedH0 (schemeHermitianLineBundle f (m + 1) E a H)
        (schemeHermitianLineBundle f (m + 1) E aT HT) φ k ≤
      SGPT.IGood.DXMain.normalizedTwistedH0 f E a H T hφ k := by
  let := E.isSeparated
  let := E.quasiCompact
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  have hle := finrank_literal_le_twistedMultiplierH0 aT HT a H hφ k
  unfold SGPT.Bergman.Quant2.normalizedH0 SGPT.IGood.DXMain.normalizedTwistedH0
  have hkpos : (0 : ℝ) < (k : ℝ) ^ (m + 1) := pow_pos (by exact_mod_cast hk) _
  rw [div_mul_eq_mul_div, ENNReal.ofReal_div_of_pos hkpos, ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_natCast, ENNReal.ofReal_natCast, ENNReal.ofReal_pow (Nat.cast_nonneg _),
    ENNReal.ofReal_natCast]
  gcongr

/-- **The lower bound of `thm:DXmain1` for every twist `T`** (`DXMainTwistedLowerBound`): for
every integral smooth projective complex scheme `X` of dimension `m + 1`, all line bundles `T`,
`L` (with atlases), every smooth metric `H` on `L` (`θ = c₁(L, H)`) and every `φ ∈ PSH(X, θ)`,
`vol θ_φ ≤ liminf_k n! h⁰(X, T ⊗ L^k ⊗ 𝓘(kφ)) / kⁿ`. Proof: the analytic lower bound
for `(L, H)^an` twisted by `(T, H_T)^an` (any smooth metric `H_T` on `T`), the identification of
the volumes, and GAGA for `T ⊗ L^k` (`normalizedH0_le_normalizedTwistedH0`). -/
theorem dxMainTwistedLowerBound [IsIntegral X] [Nonempty (SchemeComplexPoint f)] {T : X.Modules}
    (aT : LineBundleAtlas T) {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val φ) :
    SGPT.IGood.DXMain.DXMainTwistedLowerBound f E a H T hφ := by
  let := E.isSeparated
  let := E.quasiCompact
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  have : ConnectedSpace (SchemeComplexPoint f) := connectedSpace_of_isIntegral f E (m + 1)
  let HT : SchemeLineBundleMetric f (m + 1) E T := schemeLineBundleMetric f (m + 1) E aT
  set Lan := schemeHermitianLineBundle f (m + 1) E a H with hLan
  set Tan := schemeHermitianLineBundle f (m + 1) E aT HT with hTan
  have hL := isSourceSmoothHermitianMetric_schemeHermitianLineBundle f (m + 1) E a H
  have hT := isSourceSmoothHermitianMetric_schemeHermitianLineBundle f (m + 1) E aT HT
  have hgeq : (sourceNativeFirstChernForm Lan hL).val.GeometricallyEq (H.curvature a).val :=
    sourceNativeFirstChernForm_geometricallyEq Lan hL
      (isOwnFirstChernForm_schemeHermitianLineBundle f (m + 1) E a H)
  have hφ' : (ofFixedModel (m + 1) (SchemeComplexPoint f)).IsThetaPSH
      (SGPT.Bergman.Quant2.chernForm Lan hL) φ :=
    (isThetaPSH_iff_nativeThetaPotential _ φ).mpr (by
      rw [SGPT.Bergman.Quant2.chernForm, sourceNativeAtlasForm_roundTrip]
      exact (hgeq.thetaPshPotential_iff φ).mpr hφ)
  obtain ⟨hφ'', hRR⟩ := SGPT.IGood.DXLow2.riemannRochLowerBound_of_kahler
    (T := Tan) (schemeProjectiveTNKahlerBackground f (m + 1) E) hL hT hφ'
  have hvol : iVolume (H.curvature a) (LocalPotentials.closedRealOneOne_hasLocalPotentials _) φ hφ =
      sourceIVolume (SGPT.Bergman.Quant2.chernForm Lan hL) φ hφ'' := by
    rw [sourceIVolume_eq_native _ φ hφ'' (LocalPotentials.closedRealOneOne_hasLocalPotentials _)]
    have hgeq' : (H.curvature a).val.GeometricallyEq
        (atlasClosedFormToNative (SGPT.Bergman.Quant2.chernForm Lan hL)).val := by
      rw [SGPT.Bergman.Quant2.chernForm, sourceNativeAtlasForm_roundTrip]
      exact hgeq.symm
    exact iVolume_congr_geometricallyEq hgeq' _ _ φ hφ _
  unfold SGPT.IGood.DXMain.DXMainTwistedLowerBound
  rw [hvol]
  refine hRR.trans (liminf_le_liminf ?_)
  filter_upwards [eventually_ge_atTop 1] with k hk
  exact normalizedH0_le_normalizedTwistedH0 a H aT HT hφ hk

/-- **Source `thm:DXmain1` for every twist `T`, projective setting**: on an integral smooth
projective complex scheme `X` of dimension `m + 1` carrying a smooth flag, for all line bundles
`T`, `L` (with atlases), every smooth metric `H` on `L` and every `φ ∈ PSH(X, c₁(L, H))`,
`lim_k n! h⁰(X, T ⊗ L^k ⊗ 𝓘(kφ)) / kⁿ = vol θ_φ`. -/
theorem dxMain1TwistedHolds [IsIntegral X] (Y : Fin (m + 1 + 1) → Set (SchemeComplexPoint f))
    (hY : IsSmoothFlag Y) [Nonempty (SchemeComplexPoint f)] {T : X.Modules}
    (aT : LineBundleAtlas T) {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val φ) :
    SGPT.IGood.DXMain.DXMain1TwistedHolds f E a H T hφ :=
  SGPT.IGood.DXMain.dxMain1TwistedHolds_of_lowerBound f E Y hY a H aT hφ
    (dxMainTwistedLowerBound a H aT hφ)

end Lower

/-! ### The statements for all `X` reduce to the existence of smooth flags -/

/-- **Existence of smooth flags** (Bertini): every integral smooth projective complex scheme `X`
of dimension `m + 1` with `X(ℂ) ≠ ∅` carries a smooth flag `X(ℂ) = Y₀ ⊇ Y₁ ⊇ ⋯ ⊇ Y_{m+1}` of
closed connected complex submanifolds, `dim Yᵢ = m + 1 - i` (`SGPT.Okounkov.IsSmoothFlag`). Not
proved here: it is the only remaining input of `DXMain1Statement` and
`DXMain1UntwistedStatement`. -/
def SmoothFlagsExist : Prop :=
  ∀ (X : Scheme.{0}) (f : X ⟶ Spec (.of ℂ)) (_ : ClosedProjectiveEmbedding f) [IsIntegral X]
    (m : ℕ) [SmoothOfRelativeDimension (m + 1) f] [Nonempty (SchemeComplexPoint f)],
    letI := schemeAnalyticPointTopology f
    letI := schemeAnalyticTNChartedSpace f (m + 1)
    ∃ Y : Fin (m + 1 + 1) → Set (SchemeComplexPoint f), IsSmoothFlag Y

/-- **`thm:DXmain1` (projective statement, every twist `T`, every integral `X`) holds as soon as
smooth flags exist.** -/
theorem dxMain1Statement_of_smoothFlagsExist (h : SmoothFlagsExist) :
    SGPT.IGood.DXMain.DXMain1Statement := by
  intro X f E _ m _ _ T L aT a H φ hφ
  obtain ⟨Y, hY⟩ := h X f E m
  exact dxMain1TwistedHolds a H Y hY aT hφ

/-- **`thm:DXmain1` with `T = 𝒪_X` (projective statement, every integral `X`) holds as soon as
smooth flags exist.** -/
theorem dxMain1UntwistedStatement_of_smoothFlagsExist (h : SmoothFlagsExist) :
    SGPT.IGood.DXMain.DXMain1UntwistedStatement := by
  intro X f E _ m _ _ L a H φ hφ
  obtain ⟨Y, hY⟩ := h X f E m
  exact dxMain1Holds a H Y hY hφ

end SGPT.GAGA.OkoClose
