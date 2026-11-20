import SGPT.Okounkov.OkoTowerCoef
import SGPT.GAGA.H0LOkounkov
import SGPT.GAGA.TowerAlgKahler
import SGPT.GAGA.ChowBlEmbed
import SGPT.PSH.SourceBimeromorphicMixedIVolume

/-!
# `prop:birinvO`: partial Okounkov bodies are invariant under modifications

Lane OKO-TOWER, blueprint `claude-oko-tower.tex`, nodes `claude-oko-tower:dx-tower`,
`claude-oko-tower:birinv`.  Source: chapter *The theory of Okounkov bodies*, `prop:birinvO`:
*let `π : Y → X` be a modification; then `Δ_ν(π^*L, π^*h) = Δ_ν(L, h)`.*

Setting of lanes OKO-A / H0-GAGA3 / OKO-CLOSE: `X` an integral smooth projective complex scheme of
dimension `m + 1` with a smooth flag `Y•` (`ν = ν_{Y•}`, the valuation convention under which
`prop:suba`, `prop:res`, `thm:Okoucont` are verified), `L` a line bundle with atlas `a` and smooth
metric `H`, `θ = c₁(L, H)`, `φ ∈ PSH(X, θ)` with `vol θ_φ > 0` (standing assumption of
`sec:PoB`).  The modification is a finite sequence of blow-ups with smooth centres
`π : Z → X(ℂ)` (the book's definition of a modification), or more generally an analytic
modification from a compact Kähler manifold.

## Proof

The route is the inclusion + equal-volume argument (the book reduces to analytic singularities
and to `rmk:DeltaanaW0`, which is not available on non-algebraic models).

* `Γ(π^*θ, π^*φ) ⊆ Γ(θ, φ)` (descent `π_* 𝓘(k π^*φ) ⊆ 𝓘(kφ)`,
  `pullbackMultiplierSectionSet_subset`), so the normalized points of `Γ(π^*θ, π^*φ)` accumulate in
  `Δ_{Y•}(θ_φ)` (`SGPT.Okounkov.AlgPOB.multiplierConeSubset_upper`).
* **`iVolume_le_liminf_pullbackMultiplierH0`** (the lower bound of `thm:DXmain1` on `Z`):
  `vol θ_φ ≤ liminf_k n!/kⁿ h⁰(Z, π^*L^k ⊗ 𝓘(k π^*φ))`.  On the compact Kähler manifold `Z`
  apply the analytic lower bound `SGPT.IGood.DXLow2.riemannRochLowerBound_of_kahler` to
  `π^*(L, H)^an` and `π^*φ`; `vol (π^*θ)_{π^*φ} = vol θ_φ`
  (`SGPT.PSH.VariableComplexAtlas.sourceIVolume_modification_pullback`); the literal analytic
  sections on `Z` inject into `H⁰(Z, π^*L^k ⊗ 𝓘(k π^*φ)) ⊆ H⁰(X, L^k)`
  (`finrank_literal_le_pullbackMultiplier`: descent of holomorphic sections and GAGA).
* `#Γ_k(π^*θ, π^*φ) = h⁰(Z, π^*L^k ⊗ 𝓘(k π^*φ))` (one-dimensional leaves), so by the counting
  criterion `SGPT.Okounkov.AlgPOB.bodyExtension_eq_of_fills`, `Γ(π^*θ, π^*φ)` is an almost
  semigroup whose Okounkov body is `Δ_{Y•}(θ_φ) = Δ_{Y•}(L, h)` (`cor:transalgPOB`).

## Main results

* **`pullbackPartialOkounkovBody_eq_of_kahler`**: `prop:birinvO` for an analytic modification
  `π : Z → X(ℂ)` from a compact Kähler manifold.
* **`pullbackPartialOkounkovBody_eq_of_isBlowupSequence`**: `prop:birinvO` for every finite
  sequence of blow-ups with smooth centres (no Kähler hypothesis: such a `Z` is projective,
  `SGPT.GAGA.ChowBl.exists_isHolomorphicEmbedding_of_isBlowupSequence`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.Okounkov.OkoTower

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set Filter MeasureTheory Metric
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
open SGPT.Foundations.Analysis.Pending.AnalyticModificationStrongPullback
open SGPT.Okounkov SGPT.LineBundle SGPT.NAPotential.GAGAMult SGPT.GAGA.H0L
open SGPT.Trace.RestVol SGPT.PSH SGPT.PSH.VariableComplexAtlas SGPT.Bergman.Quant2
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle
open SGPT.AlmostSemigroup SGPT.AlmostSemigroup.Class SGPT.AlmostSemigroup.OkounkovExtension
open SGPT.Okounkov.AlgPOB
open scoped Topology Manifold ContDiff ENNReal

/-! ### `𝓘`-volumes only depend on the form and the potential -/

section Volume

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [Nonempty M]

theorem iVolume_congr_of_eq {θ₁ θ₂ : ClosedRealOneOneForm n M} (hθ : θ₁ = θ₂)
    {u₁ u₂ : M → EReal} (hu : u₁ = u₂) (h₁ : HasSmoothLocalPotentials θ₁.val)
    (h₂ : HasSmoothLocalPotentials θ₂.val) (hv₁ : IsThetaPshPotential θ₁.val u₁)
    (hv₂ : IsThetaPshPotential θ₂.val u₂) :
    iVolume θ₁ h₁ u₁ hv₁ = iVolume θ₂ h₂ u₂ hv₂ := by
  subst hθ hu
  exact iVolume_proof_independent _ _ _ _ _ _

end Volume

/-! ### The lower bound of `thm:DXmain1` on the modification -/

section Lower

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} {E : ClosedProjectiveEmbedding f} {m : ℕ}
  [SmoothOfRelativeDimension (m + 1) f] [IsSeparated f] [QuasiCompact f]

local instance okoTowerBirTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance okoTowerBirCharts : ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (m + 1)
local instance okoTowerBirManifold : IsComplexManifold (m + 1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (m + 1)
local instance okoTowerBirMeasurable : MeasurableSpace (SchemeComplexPoint f) := borel _
local instance okoTowerBirBorel : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩

variable {L : X.Modules} (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f (m + 1) E L)
  {Z : Type} [TopologicalSpace Z] [ChartedSpace (ComplexModel (m + 1)) Z]
  [IsComplexManifold (m + 1) Z]
  {π : Z → SchemeComplexPoint f} (hπ : IsAnalyticModification (n := m + 1) π)

include hπ in
/-- `π^*φ` is quasi-psh for `φ ∈ PSH(X, θ)`. -/
theorem quasiPsh_comp {φ : SchemeComplexPoint f → EReal}
    (hφ : IsThetaPshPotential (H.curvature a).val φ) :
    ManifoldQuasiPlurisubharmonic (n := m + 1) (fun w => φ (π w)) :=
  (isThetaPshPotential_comp_of_isAnalyticModification hπ (H.curvature a) hφ).1.quasiPlurisubharmonic

/-- **`h⁰(Z, π^*L^k ⊗ 𝓘(k π^*φ))`**. -/
def pullbackMultiplierH0 {φ : SchemeComplexPoint f → EReal}
    (hφ : IsThetaPshPotential (H.curvature a).val φ) (k : ℕ) : ℕ :=
  Module.finrank ℂ (pullbackMultiplierSubmodule f E hπ.1.continuous (quasiPsh_comp a H hπ hφ) L k)

variable [IsIntegral X] [CompactSpace (SchemeComplexPoint f)]
  [ConnectedSpace (SchemeComplexPoint f)] [Nonempty (SchemeComplexPoint f)]

/-- **The lower bound of `thm:DXmain1` for the pulled-back bundle on a Kähler modification**:
`vol θ_φ ≤ liminf_k n!/kⁿ h⁰(Z, π^*L^k ⊗ 𝓘(k π^*φ))`. -/
theorem iVolume_le_liminf_pullbackMultiplierH0 (ωZ : KahlerBackground (m + 1) Z)
    {φ : SchemeComplexPoint f → EReal} (hφ : IsThetaPshPotential (H.curvature a).val φ) :
    iVolume (H.curvature a) (LocalPotentials.closedRealOneOne_hasLocalPotentials _) φ hφ ≤
      liminf (fun k : ℕ => ENNReal.ofReal (((m + 1).factorial : ℝ) / (k : ℝ) ^ (m + 1) *
        (pullbackMultiplierH0 a H hπ hφ k : ℝ))) atTop := by
  let : MeasurableSpace Z := borel Z
  have : BorelSpace Z := ⟨rfl⟩
  have : CompactSpace Z := compactSpace_of_isAnalyticModification hπ
  have : ConnectedSpace Z := SGPT.Okounkov.connectedSpace_source_of_isAnalyticModification hπ
  have : Nonempty Z := ⟨(AnalyticModificationStrongPullback.surjective_of_isAnalyticModification
    hπ (Classical.arbitrary _)).choose⟩
  set Lan := schemeHermitianLineBundle f (m + 1) E a H with hLan
  have hL := isSourceSmoothHermitianMetric_schemeHermitianLineBundle f (m + 1) E a H
  set θL := SGPT.Bergman.NativeHermitianMetric.sourceNativeFirstChernForm Lan hL with hθL
  have hgeq : θL.val.GeometricallyEq (H.curvature a).val :=
    SGPT.Bergman.NativeHermitianMetric.sourceNativeFirstChernForm_geometricallyEq Lan hL
      (isOwnFirstChernForm_schemeHermitianLineBundle f (m + 1) E a H)
  have hφL : IsThetaPshPotential θL.val φ := (hgeq.thetaPshPotential_iff φ).mpr hφ
  set η := ClosedRealOneOneForm.pullback hπ.1 θL with hη
  have hφη : IsThetaPshPotential η.val (fun w => φ (π w)) :=
    isThetaPshPotential_comp_of_isAnalyticModification hπ θL hφL
  have hLZ := restrictBundle_smooth hL (towerMap hπ)
  have hTZ := restrictBundle_smooth SGPT.PSH.GlobalL2.isSourceSmoothHermitianMetric_unit
    (towerMap hπ)
  have hgeoZ := restrictBundle_chern_geometricallyEq hL (towerMap hπ)
  have hTr : (ofFixedModel (m + 1) Z).IsThetaPSH (chernForm (towerBundle a H hπ) hLZ)
      (fun w => φ (π w)) := (isThetaPSH_chernForm_iff hgeoZ _).mpr hφη
  obtain ⟨hTr', hRR⟩ := SGPT.IGood.DXLow2.riemannRochLowerBound_of_kahler ωZ hLZ hTZ hTr
  -- the volume on `Z` is the volume on `X`
  have hvolZ := sourceIVolume_chernForm_eq_iVolume hgeoZ hTr' hφη
  set θ' := nativeClosedFormToAtlas θL with hθ'
  have hθ'n : atlasClosedFormToNative θ' = θL := sourceNativeAtlasForm_roundTrip θL
  have hφ' : (ofFixedModel (m + 1) (SchemeComplexPoint f)).IsThetaPSH θ' φ :=
    (isThetaPSH_iff_nativeThetaPotential θ' φ).mpr (by rw [hθ'n]; exact hφL)
  have hpull := sourceIVolume_modification_pullback hπ θ' φ hφ'
  rw [sourceIVolume_eq_native _ _ _ (LocalPotentials.closedRealOneOne_hasLocalPotentials _),
    sourceIVolume_eq_native _ _ _ (LocalPotentials.closedRealOneOne_hasLocalPotentials _)] at hpull
  have hvolP : iVolume η (LocalPotentials.closedRealOneOne_hasLocalPotentials _)
      (fun w => φ (π w)) hφη =
      iVolume θL (LocalPotentials.closedRealOneOne_hasLocalPotentials _) φ hφL := by
    refine (iVolume_congr_of_eq ?_ rfl _ _ _ _).trans (hpull.trans (iVolume_congr_of_eq hθ'n rfl _ _ _ _))
    rw [sourceNativeAtlasForm_roundTrip, hθ'n]
  have hvolX := iVolume_congr_geometricallyEq hgeq
    (LocalPotentials.closedRealOneOne_hasLocalPotentials _)
    (LocalPotentials.closedRealOneOne_hasLocalPotentials _) φ hφL hφ
  rw [← hvolX, ← hvolP, ← hvolZ]
  refine hRR.trans (liminf_le_liminf ?_)
  filter_upwards [eventually_ge_atTop 1] with k hk
  unfold normalizedH0
  refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ (by positivity))
  exact_mod_cast finrank_literal_le_pullbackMultiplier a H hπ (φ := φ) ⟨hφη.1.quasiPlurisubharmonic, hφη.2⟩ k

end Lower

/-! ### The comparison -/

section Comparison

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (E : ClosedProjectiveEmbedding f)
  [IsIntegral X] {m : ℕ} [SmoothOfRelativeDimension (m + 1) f]

local instance okoTowerCmpTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance okoTowerCmpCharts : ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (m + 1)
local instance okoTowerCmpManifold [IsSeparated f] [QuasiCompact f] :
    IsComplexManifold (m + 1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (m + 1)

variable (Y : Fin (m + 1 + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y)
  {L : X.Modules} (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f (m + 1) E L)
  {Z : Type} [TopologicalSpace Z] [ChartedSpace (ComplexModel (m + 1)) Z]
  [IsComplexManifold (m + 1) Z]

/-- `Γ(π^*θ, π^*φ)` as a lattice subset of an admissible cone containing it. -/
def pullbackConeSubset {C : AdmissibleCone (m + 1)} (π : Z → SchemeComplexPoint f)
    (φ : SchemeComplexPoint f → EReal)
    (hsub : pullbackMultiplierSectionSet f E Y hY a π φ ⊆ (latticePoints C.cone : Set _)) :
    ConeSubset C :=
  ⟨_, hsub⟩

/-- **The lower counting hypothesis on the modification**: for every `ε > 0` and all `k ≫ 0`,
`k⁻ⁿ #Γ_k(π^*θ, π^*φ) ≥ vol Δ_{Y•}(θ_φ) - ε`. -/
theorem pullbackConeSubset_lower [Nonempty (SchemeComplexPoint f)] {C : AdmissibleCone (m + 1)}
    {π : Z → SchemeComplexPoint f}
    (hπ : letI := E.isSeparated; letI := E.quasiCompact;
      IsAnalyticModification (n := m + 1) π)
    (ωZ : KahlerBackground (m + 1) Z) {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val φ)
    (hsub : pullbackMultiplierSectionSet f E Y hY a π φ ⊆ (latticePoints C.cone : Set _))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, volume.real
        (PartialBody.generalPartialBody (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY)
          (H.curvature a) φ) - ε ≤
      (pullbackConeSubset f E Y hY a π φ hsub).normalizedCardinality k := by
  let := E.isSeparated
  let := E.quasiCompact
  let : MeasurableSpace (SchemeComplexPoint f) := borel _
  have : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  have : ConnectedSpace (SchemeComplexPoint f) := schemeSmoothFlag_connectedSpace f (m + 1) Y hY
  set 𝔽 := schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY with h𝔽
  set θ := H.curvature a with hθ
  have hφZ := quasiPsh_comp a H hπ hφ
  have hcard : ∀ k : ℕ, (pullbackConeSubset f E Y hY a π φ hsub).normalizedCardinality k =
      (k : ℝ)⁻¹ ^ (m + 1) * pullbackMultiplierH0 a H hπ hφ k := by
    intro k
    have h := Nat.card_eq_card_finite_toFinset
      ((pullbackConeSubset f E Y hY a π φ hsub).finite_slice k)
    rw [ConeSubset.normalizedCardinality, pullbackMultiplierH0,
      ← card_slice_pullbackMultiplierSectionSet f E Y hY a hπ.1.continuous hφZ k]
    rw [show ((pullbackConeSubset f E Y hY a π φ hsub).slices k).card =
      Nat.card (slice (pullbackMultiplierSectionSet f E Y hY a π φ) (k : ℤ)) from h.symm]
  set V := iVolume θ (LocalPotentials.closedRealOneOne_hasLocalPotentials θ) φ hφ with hVdef
  have hVtop : V ≠ ⊤ := by
    have hfin := ((PartialBody.convex_isCompact_generalPartialBody (F := 𝔽) hφ).2.measure_lt_top
      (μ := (volume : Measure (Fin (m + 1) → ℝ)))).ne
    rw [PartialBody.volume_generalPartialBody_uncond (F := 𝔽) hφ] at hfin
    intro htop
    apply hfin
    rw [← hVdef, htop]
    exact ENNReal.top_div_of_ne_top (ENNReal.natCast_ne_top _)
  set N : ℝ := ((m + 1).factorial : ℝ) with hNdef
  have hN : 0 < N := by rw [hNdef]; exact_mod_cast Nat.factorial_pos (m + 1)
  have hvolK : volume.real (PartialBody.generalPartialBody 𝔽 θ φ) = V.toReal / N := by
    rw [measureReal_def, PartialBody.volume_generalPartialBody_uncond (F := 𝔽) hφ,
      ENNReal.toReal_div, ENNReal.toReal_natCast]
  rw [hvolK]
  by_cases hcase : V.toReal / N - ε ≤ 0
  · refine Eventually.of_forall fun k => hcase.trans ?_
    rw [hcard k]
    positivity
  push Not at hcase
  have hpos : 0 < V.toReal - N * ε := by
    have := mul_lt_mul_of_pos_left hcase hN
    rw [mul_sub, mul_div_cancel₀ _ hN.ne', mul_zero] at this
    exact this
  have hVpos : 0 < V.toReal := by linarith [mul_pos hN hε]
  have hb : ENNReal.ofReal (V.toReal - N * ε) < V :=
    calc ENNReal.ofReal (V.toReal - N * ε) < ENNReal.ofReal V.toReal :=
          (ENNReal.ofReal_lt_ofReal_iff hVpos).mpr (by linarith [mul_pos hN hε])
      _ = V := ENNReal.ofReal_toReal hVtop
  have hlow := iVolume_le_liminf_pullbackMultiplierH0 a H hπ ωZ hφ
  have hev := Filter.eventually_lt_of_lt_liminf (hb.trans_le hlow)
  filter_upwards [hev, eventually_gt_atTop 0] with k hk hk0
  rw [hcard k]
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk0
  have hk' := (ENNReal.ofReal_lt_ofReal_iff'.mp hk).1
  have hinv : (k : ℝ)⁻¹ ^ (m + 1) * (pullbackMultiplierH0 a H hπ hφ k : ℝ) =
      (pullbackMultiplierH0 a H hπ hφ k : ℝ) / (k : ℝ) ^ (m + 1) := by
    rw [inv_pow, inv_mul_eq_div]
  rw [hinv]
  have h1 : V.toReal - N * ε < N * ((pullbackMultiplierH0 a H hπ hφ k : ℝ) / (k : ℝ) ^ (m + 1)) := by
    have : N / (k : ℝ) ^ (m + 1) * (pullbackMultiplierH0 a H hπ hφ k : ℝ) =
        N * ((pullbackMultiplierH0 a H hπ hφ k : ℝ) / (k : ℝ) ^ (m + 1)) := by ring
    rw [← this]
    exact hk'
  rw [div_sub' hN.ne', div_le_iff₀ hN]
  linarith

/-- **Source `prop:birinvO`, for an analytic modification from a compact Kähler manifold**: for
every large cube cone and every `φ ∈ PSH(X, θ)` with `vol θ_φ > 0`,
`Δ_ν(π^*L, π^*h) = Δ_ν(L, h)`: `Γ(π^*θ, π^*φ)` is an almost semigroup and its Okounkov body is the
partial Okounkov body of `(L, h)`. -/
theorem pullbackPartialOkounkovBody_eq_of_kahler [Nonempty (SchemeComplexPoint f)]
    {π : Z → SchemeComplexPoint f}
    (hπ : letI := E.isSeparated; letI := E.quasiCompact;
      IsAnalyticModification (n := m + 1) π)
    (hK : Nonempty (KahlerBackground (m + 1) Z)) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ C : ℝ, C₀ ≤ C → ∀ φ : SchemeComplexPoint f → EReal,
      (letI := E.isSeparated; letI := E.quasiCompact;
        IsThetaPshPotential (H.curvature a).val φ) →
      0 < volume.real (PartialBody.generalPartialBody
        (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) (H.curvature a) φ) →
      pullbackPartialOkounkovBody f E Y hY a (cubeCone C) π φ =
        partialOkounkovBody f (m + 1) E Y hY (cubeCone C) a φ := by
  obtain ⟨ωZ⟩ := hK
  obtain ⟨C₀, hC₀, hC⟩ := exists_cubeCone_contains f E Y hY a H
  refine ⟨C₀, hC₀, fun C hC' φ hφ hpos => ?_⟩
  let := E.isSeparated
  let := E.quasiCompact
  obtain ⟨hsubX, hKC⟩ := hC C hC' φ hφ
  have hφq : ManifoldQuasiPlurisubharmonic (n := m + 1) φ := hφ.1.quasiPlurisubharmonic
  have hsubZ : pullbackMultiplierSectionSet f E Y hY a π φ ⊆
      (latticePoints (cubeCone (n := m + 1) C).cone : Set _) :=
    (pullbackMultiplierSectionSet_subset f E Y hY a hπ hφq).trans hsubX
  obtain ⟨hKv, hKc⟩ := PartialBody.convex_isCompact_generalPartialBody
    (F := schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) hφ
  set S := pullbackConeSubset f E Y hY a π φ hsubZ with hS
  have hup : ∀ η : ℝ, 0 < η → ∀ᶠ k : ℕ in atTop, ∀ x ∈ S.slices k,
      ((k : ℝ))⁻¹ • Counting.integerCast x ∈ cthickening η
        (PartialBody.generalPartialBody (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY)
          (H.curvature a) φ) := by
    intro η hη
    filter_upwards [multiplierConeSubset_upper f E Y hY a H hφ hsubX hη] with k hk x hx
    refine hk x ((ConeSubset.mem_slices _ k x).mpr ?_)
    exact pullbackMultiplierSectionSet_subset f E Y hY a hπ hφq ((ConeSubset.mem_slices _ k x).mp hx)
  have hlow : ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop,
      volume.real (PartialBody.generalPartialBody
        (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) (H.curvature a) φ) - ε ≤
        S.normalizedCardinality k :=
    fun ε hε => pullbackConeSubset_lower f E Y hY a H hπ ωZ hφ hsubZ hε
  have hmem := (mem_almostSemigroupLocus_of_fills _ hKc hKv hKC S hpos hup hlow).1
  rw [pullbackPartialOkounkovBody_eq f E Y hY a π φ hsubZ hmem,
    partialOkounkovBody_eq_generalPartialBody f E Y hY a H hφ hpos hsubX hKC]
  exact bodyExtension_eq_of_fills _ hKc hKv hKC S hpos hup hlow hmem

/-- **Source `prop:birinvO`** (a modification is a finite sequence of blow-ups with smooth centres):
for every finite sequence of blow-ups with smooth centres `π : Z → X(ℂ)`, every large cube cone and
every `φ ∈ PSH(X, θ)` with `vol θ_φ > 0`, `Δ_ν(π^*L, π^*h) = Δ_ν(L, h)`. -/
theorem pullbackPartialOkounkovBody_eq_of_isBlowupSequence [Nonempty (SchemeComplexPoint f)]
    {π : Z → SchemeComplexPoint f}
    (hπ : letI := E.isSeparated; letI := E.quasiCompact;
      BlowupSequences.IsBlowupSequence (m + 1) (SchemeComplexPoint f) Z π) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ C : ℝ, C₀ ≤ C → ∀ φ : SchemeComplexPoint f → EReal,
      (letI := E.isSeparated; letI := E.quasiCompact;
        IsThetaPshPotential (H.curvature a).val φ) →
      0 < volume.real (PartialBody.generalPartialBody
        (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) (H.curvature a) φ) →
      pullbackPartialOkounkovBody f E Y hY a (cubeCone C) π φ =
        partialOkounkovBody f (m + 1) E Y hY (cubeCone C) a φ := by
  let := E.isSeparated
  let := E.quasiCompact
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  have hmod : IsAnalyticModification (n := m + 1) π :=
    HironakaChowLemma.isAnalyticModification_of_isBlowupSequence hπ
  obtain ⟨-, N', Ψ', hΨ'⟩ := SGPT.GAGA.ChowBl.exists_isHolomorphicEmbedding_of_isBlowupSequence
    (SGPT.GAGA.H0S.isHolomorphicEmbedding_projectivePoint f E (m + 1)) hπ
  exact pullbackPartialOkounkovBody_eq_of_kahler f E Y hY a H hmod
    (SGPT.GAGA.TowerAlg.nonempty_kahlerBackground_of_isHolomorphicEmbedding hΨ')

end Comparison

end SGPT.Okounkov.OkoTower

end
