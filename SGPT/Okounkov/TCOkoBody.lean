import SGPT.Okounkov.TCOkoSeries
import SGPT.NAPotential.NANSTestConfigVolume
import SGPT.TestCurve.TCLinMain
import SGPT.Okounkov.ValuativeTestCurve
import SGPT.Foundations.Analysis.Pending.StrongOpennessEnvelope
import SGPT.Foundations.Analysis.Pending.StrongOpennessRegularRoute
import SGPT.Foundations.Analysis.Pending.PluripolarCapacityDichotomy
import SGPT.TestCurve.MiscMArbitraryMetric

/-!
# The partial Okounkov bodies of the test curve of a test configuration

Source: `rmk:Okounkov:L2335` (chapter *The theory of Okounkov bodies*, section *Okounkov test
curves*):

*"Suppose that `Γ` is the test curve induced by a test configuration as in `ex:RWN` and
`rmk:PhongSturm`, then for any `τ < Γ_max`, `Δ_{Y•}(θ, Γ_τ)` is the Okounkov body of a graded
linear series `⊕_{k ≥ 0} 𝓕^{kτ}_k`, where `𝓕` is the filtration induced by the test
configuration. See [Xia21, Theorem 5.28] for the details. In particular, in this case, our
theory of partial Okounkov bodies recovers the Okounkov bodies of the filtered linear series in
the sense of [BC11]."*

Lane TC-OKO, blueprint `claude-tc-oko`.

## Formal statement

`X` is an integral smooth projective complex scheme of dimension `n = m + 1` with a smooth flag
`Y•`, `L` a line bundle with atlas `a` and a smooth metric `h` (`H`), `θ = c₁(L, h)`,
`Γ^𝓕_τ = P_θ[ψ_τ]` the test curve of a filtration `𝓕` (`ex:RWN`, `testCurvePotential`, `ψ_τ` the
obstacle `usc sup_k k⁻¹ Γ^{𝓕,k}_τ`), `Γ_max = τ(𝓕)`, `Δ_{Y•}(θ, Γ_τ)` the partial Okounkov body
of the current `θ_{Γ_τ}` (`def:generalPOB`, `PartialBody.generalPartialBody` on the flag
geometry of `X`), and `Δ_{Y•}(⊕_k 𝓕^{kτ}_k)` the Okounkov body of the filtered linear series
(`seriesBody (filtrationSeries 𝓕 τ)`, [LM09], [BC11]).

* `seriesBody_filtrationSeries_eq`: for every filtration `𝓕` satisfying the Skoda inclusion
  (`SkodaInclusionIdeal`: `H⁰(X, L^k ⊗ 𝓘(kψ_τ)) ⊆ 𝓕^{kτ'}_k` for `τ' < τ < τ(𝓕)`, `k ≫ 0`),
  `{θ}` big and `τ < τ(𝓕)`: `Δ_{Y•}(⊕_k 𝓕^{kτ}_k) = Δ_{Y•}(θ, Γ^𝓕_τ)`.
* `seriesBody_filtrationSeries_eq_of_finitelyGenerated`: the same for the filtration of every
  finitely generated normalized `ℤ`-filtration and `θ = c₁(L, h)` Kähler (Skoda inclusion by
  lanes SKODA-INC, GLOBAL-SKODA, H0-GAGA3).
* `testConfiguration_seriesBody_eq`: the same for every test configuration whose
  induced filtration is finitely generated, any smooth `h` with `{c₁(L, h)}` a Hodge class.
* **`linearized_seriesBody_eq`** (`rmk:Okounkov:L2335`): for every ample test configuration of
  `(X, L)` with a `𝔾_m`-linearized `𝓛` ([BHJ17, Def. 2.1–2.3], lane TC-LIN, whose induced
  filtration is finitely generated, [BHJ17, Prop. 2.15]), every smooth metric `h` on `L` and
  `θ = c₁(L, h)` with `{θ}` a Hodge class (the Skoda inclusion for an arbitrary smooth `h`:
  lane MISC-M, `MiscM.skodaInclusionIdeal_inducedFiltration_of_kahler`).

## Proof ([Xia21, Thm. 5.28])

* `⊆`: every `s ∈ 𝓕^{kτ}_k` lies in `H⁰(X, L^k ⊗ 𝓘(kψ_τ))`, so the normalized valuative points
  `k⁻¹ ν(s)` lie in `Δ_{Y•}(θ, ψ_τ)` (`seriesBody_subset_generalPartialBody`).
* volumes: `Δ(⊕ 𝓕^{kτ}_k)` is compact convex with `dim 𝓕^{kτ}_k ≤ #(k Δ ∩ ℤⁿ)`, so
  `n! vol Δ(⊕ 𝓕^{kτ}_k) ≥ liminf n! dim 𝓕^{kτ}_k / kⁿ ≥ vol(θ, ψ_{τ''}) = n! vol Δ(θ, ψ_{τ''})`
  for `τ < τ'' < τ(𝓕)` (the Skoda sandwich of lane NA-NS and `thm:pobmain` (1)); concavity of
  `τ ↦ ψ_τ` and `thm:pobmain` (2), (6) give
  `Δ(θ, ψ_{aτ₁ + (1-a)τ}) ⊇ a p + (1 - a) Δ(θ, ψ_τ)`, so `vol Δ(θ, ψ_{τ''}) → vol Δ(θ, ψ_τ)` as
  `τ'' ↘ τ` from below by `(1 - a)ⁿ vol Δ(θ, ψ_τ)`.
* a closed subset of a convex body of the same (positive) volume is the whole body.
* `Δ(θ, ψ_τ) = Δ(θ, Γ_τ)`: `ψ_τ ≤ Γ_τ = P_θ[ψ_τ]` and `P_θ[ψ_τ] ⪯_𝓘 ψ_τ` (strong openness).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.Okounkov.TCOko

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set Filter MeasureTheory Metric
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.FirstPass.IEnvelope
open SGPT.Foundations.Analysis.Pending.DiagonalMass SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending.ThetaPshConvexCombination
open SGPT.Okounkov SGPT.LineBundle SGPT.AlmostSemigroup
open scoped Topology ENNReal Pointwise

/-! ### Convex bodies -/

section Convex

variable {n : ℕ}

/-- A convex set of positive volume in `ℝⁿ` has nonempty interior. -/
theorem interior_nonempty_of_volume_pos {P : Set (Fin n → ℝ)} (hP : Convex ℝ P)
    (hpos : 0 < volume P) : (interior P).Nonempty := by
  by_contra h
  rw [not_nonempty_iff_eq_empty] at h
  have hfront := hP.addHaar_frontier volume
  have hsub : P ⊆ frontier P := by
    intro x hx
    rw [frontier, h, sdiff_empty]
    exact subset_closure hx
  exact absurd (measure_mono_null hsub hfront) hpos.ne'

/-- **A closed subset of a convex body of at least the same finite positive volume is the whole
body.** -/
theorem eq_of_subset_of_volume_le {K P : Set (Fin n → ℝ)} (hKP : K ⊆ P) (hK : IsClosed K)
    (hP : Convex ℝ P) (hpos : 0 < volume P) (hfin : volume P ≠ ⊤)
    (hvol : volume P ≤ volume K) : K = P := by
  have hint := interior_nonempty_of_volume_pos hP hpos
  apply le_antisymm hKP
  intro p hp
  by_contra hpK
  have hcl : p ∈ closure (interior P) := by
    rw [hP.closure_interior_eq_closure_of_nonempty_interior hint]
    exact subset_closure hp
  obtain ⟨q, hqK, hqint⟩ := mem_closure_iff.mp hcl Kᶜ hK.isOpen_compl hpK
  have hopen : IsOpen (Kᶜ ∩ interior P) := hK.isOpen_compl.inter isOpen_interior
  have hqpos : 0 < volume (Kᶜ ∩ interior P) := hopen.measure_pos volume ⟨q, hqK, hqint⟩
  have hdisj : Disjoint K (Kᶜ ∩ interior P) := disjoint_compl_right.mono_right inter_subset_left
  have hunion : K ∪ (Kᶜ ∩ interior P) ⊆ P :=
    union_subset hKP (inter_subset_right.trans interior_subset)
  have hle := measure_mono (μ := MeasureTheory.volume) hunion
  rw [measure_union hdisj hopen.measurableSet] at hle
  have hKfin : volume K ≠ ⊤ := ne_top_of_le_ne_top hfin (measure_mono hKP)
  have := (ENNReal.lt_add_right hKfin hqpos.ne').trans_le (hle.trans hvol)
  exact lt_irrefl _ this

/-- The image of `A` under `y ↦ c + r • y` has volume `|r|ⁿ vol A`. -/
theorem volume_image_affine (A : Set (Fin n → ℝ)) (c : Fin n → ℝ) (r : ℝ) :
    volume ((fun y => c + r • y) '' A) = ENNReal.ofReal (|r| ^ n) * volume A := by
  have himg : (fun y => c + r • y) '' A = c +ᵥ (r • A) := by
    rw [← Set.image_smul, ← Set.image_vadd, Set.image_image]
    rfl
  rw [himg, measure_vadd, Measure.addHaar_smul, Module.finrank_fin_fun, abs_pow]

end Convex

/-! ### The scheme setting -/

variable {X : Scheme} {f : X ⟶ Spec (.of ℂ)} {E : ClosedProjectiveEmbedding f}
  [IsIntegral X] {m : ℕ} [SmoothOfRelativeDimension (m + 1) f]

local instance tcOkoBodyTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance tcOkoBodyCharts : ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (m + 1)
local instance tcOkoBodyManifold [IsSeparated f] [QuasiCompact f] :
    IsComplexManifold (m + 1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (m + 1)
local instance tcOkoBodyMeasurable : MeasurableSpace (SchemeComplexPoint f) := borel _
local instance tcOkoBodyBorel : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩

variable (Y : Fin (m + 1 + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y)
  {L : X.Modules} {a : LineBundleAtlas L} (H : SchemeLineBundleMetric f (m + 1) E L)

/-- **`Δ(W) ⊆ Δ_{Y•}(θ, φ)` for a graded linear series of multiplier sections**: if every
`s ∈ W_k` lies in `H⁰(X, L^k ⊗ 𝓘(kφ))`, `φ ∈ PSH(X, θ)`, then the Okounkov body of `W` lies in
the partial Okounkov body of `θ_φ`. -/
theorem seriesBody_subset_generalPartialBody (W : GradedLinearSeries f a)
    {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val φ)
    (hW : ∀ (k : ℕ) (s : SectionSpace f L k), s ∈ W.piece k →
      IsMultiplierSection f (m + 1) E φ k s) :
    letI := E.isSeparated
    letI := E.quasiCompact
    seriesBody f (m + 1) E Y hY W ⊆ PartialBody.generalPartialBody
      (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) (H.curvature a) φ := by
  let := E.isSeparated
  let := E.quasiCompact
  set Δ := PartialBody.generalPartialBody (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY)
    (H.curvature a) φ with hΔ
  have hΔc : IsClosed Δ := PartialBody.isClosed_generalPartialBody _ _
  have hΔv : Convex ℝ Δ := (PartialBody.convex_isCompact_generalPartialBody hφ).1
  rw [← hΔc.closure_eq, closure_eq_iInter_cthickening]
  refine subset_iInter₂ fun η hη => ?_
  obtain ⟨k₀, -, h⟩ := AlgebraicDX.eventually_normalized_mem_thickening f E Y hY a H hφ hη
  refine AlgebraicDX.body_subset_of_normalized_mem _ isClosed_cthickening (hΔv.cthickening η) ?_
  intro z hz
  have hz' := hz
  obtain ⟨k, s, hs, hsW, rfl⟩ := hz'
  refine ⟨by simp, fun h0 => ?_, fun hpos => ?_⟩
  · have hk0 : k = 0 := by
      change ((k : ℕ) : ℤ) = 0 at h0
      exact_mod_cast h0
    subst hk0
    rw [schemeFubiniStudySectionVector_degree_zero f m E Y hY a s hs]
    funext i
    simp
  · have hkpos : 0 < k := by
      change (0 : ℤ) < ((k : ℕ) : ℤ) at hpos
      exact_mod_cast hpos
    have hpow := AlgebraicBody.succ_nsmul_mem (seriesSemigroup f (m + 1) E Y hY W) hz k₀
    obtain ⟨d, t, ht, htW, hdt⟩ := hpow
    simp only [Prod.smul_mk] at hdt
    obtain ⟨hv, hd⟩ := Prod.mk.inj hdt
    have hdk : (d : ℤ) = (k₀ + 1 : ℕ) * (k : ℤ) := by rw [← hd, nsmul_eq_mul]
    have hdk' : d = (k₀ + 1) * k := by exact_mod_cast hdk
    have hdge : k₀ ≤ d := by rw [hdk']; nlinarith
    have hmt := h d hdge t ht (hW d t htW)
    refine thickening_subset_cthickening η Δ ?_
    convert hmt using 1
    funext i
    have hvi := congrFun hv i
    simp only [Pi.smul_apply, nsmul_eq_mul] at hvi
    have hvi' : ((k₀ + 1 : ℕ) : ℝ) *
        (schemeFubiniStudySectionVector f (m + 1) E Y hY a k s hs i : ℝ) =
        (schemeFubiniStudySectionVector f (m + 1) E Y hY a d t ht i : ℝ) := by
      exact_mod_cast hvi
    simp only [Pi.smul_apply, smul_eq_mul, Counting.integerCast]
    rw [← hvi', hdk']
    push_cast
    have hk1 : ((k₀ : ℝ) + 1) ≠ 0 := by positivity
    have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hkpos.ne'
    field_simp

/-! ### The filtered linear series of a filtration -/

section Main

variable (F : SectionFiltration f a)

/-- **`Δ(⊕_k 𝓕^{kτ}_k) ⊆ Δ_{Y•}(θ, ψ_τ)`**: every `s ∈ 𝓕^{kτ}_k` lies in
`H⁰(X, L^k ⊗ 𝓘(kψ_τ))` (`ex:RWN`), `ψ_τ` the obstacle of `Γ^𝓕_τ = P_θ[ψ_τ]`. -/
theorem seriesBody_filtrationSeries_subset {τ : ℝ} (hτ : (τ : EReal) < F.slope) :
    letI := E.isSeparated
    letI := E.quasiCompact
    seriesBody f (m + 1) E Y hY (filtrationSeries F τ) ⊆ PartialBody.generalPartialBody
      (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) (H.curvature a)
      (F.obstacle H τ) :=
  seriesBody_subset_generalPartialBody Y hY H _ (F.obstacle_isThetaPshPotential H hτ)
    fun _ _ hs => SGPT.TestCurve.RWN.isMultiplierSection_obstacle F H hτ hs

/-- **`Δ_{Y•}(θ, ψ_τ) = Δ_{Y•}(θ, Γ^𝓕_τ)`** for `τ < τ(𝓕)`, `{θ}` big: `ψ_τ ≤ P_θ[ψ_τ]` and
`P_θ[ψ_τ] ⪯_𝓘 ψ_τ` (strong openness), with `thm:pobmain` (2). -/
theorem generalPartialBody_obstacle_eq [Nonempty (SchemeComplexPoint f)]
    (hbig : letI := E.isSeparated; letI := E.quasiCompact;
      IsBigClass (RealBottChern.ofRepresentative (H.curvature a)))
    {τ : ℝ} (hτ : (τ : EReal) < F.slope) :
    letI := E.isSeparated
    letI := E.quasiCompact
    PartialBody.generalPartialBody (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY)
        (H.curvature a) (F.obstacle H τ) =
      PartialBody.generalPartialBody (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY)
        (H.curvature a) (F.testCurvePotential H τ) := by
  let := E.isSeparated
  let := E.quasiCompact
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  have hψ := F.obstacle_isThetaPshPotential H hτ
  have hΓ := F.testCurvePotential_isThetaPshPotential H hτ
  have hle : F.obstacle H τ ≤ F.testCurvePotential H τ := by
    have hc := F.obstacle_mem_singularityCompetitors H hτ
    exact le_singularityEnvelope hc.1.1 hc.1.2 hc.2
  have hI : IOrderOnManifold (n := m + 1) (F.testCurvePotential H τ) (F.obstacle H τ) :=
    iOrderOnManifold_singularityEnvelope_self_of_strongOpenness
      (increasingStrongOpenness_ofRegularRoute (m + 1))
      (LocalPotentials.closedRealOneOne_hasLocalPotentials _) hψ
  have hbig' := (SGPT.PSH.BookCurrent.isBig_iff_isBigClass _).mpr hbig
  exact (PartialBody.generalPartialBody_subset_of_pointwise_le hψ hΓ hle hbig).1.antisymm
    (PartialBody.generalPartialBody_subset_of_iOrder hΓ hψ hI hbig').1

/-- `vol Δ_{Y•}(θ, ψ_τ) > 0` for `τ < τ(𝓕)` (`{θ}` big): the obstacle has positive mass. -/
theorem volume_generalPartialBody_obstacle_pos
    (hbig : letI := E.isSeparated; letI := E.quasiCompact;
      IsBigClass (RealBottChern.ofRepresentative (H.curvature a)))
    {τ : ℝ} (hτ : (τ : EReal) < F.slope) :
    letI := E.isSeparated
    letI := E.quasiCompact
    0 < volume (PartialBody.generalPartialBody
      (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) (H.curvature a)
      (F.obstacle H τ)) := by
  let := E.isSeparated
  let := E.quasiCompact
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  have : Nonempty (SchemeComplexPoint f) := SGPT.GAGA.H0L.nonempty_of_smoothFlag Y hY
  have hψ := F.obstacle_isThetaPshPotential H hτ
  have : ConnectedSpace (SchemeComplexPoint f) := schemeSmoothFlag_connectedSpace f (m + 1) Y hY
  have hgw := SGPT.NAPotential.NANS.TestConfig.iGoodWith_obstacle F H Y hY hbig hτ
  rw [PartialBody.volume_generalPartialBody_uncond
    (F := schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) hψ]
  exact ENNReal.div_pos ((hgw.positiveMass).trans_le
    (PartialBody.diagonalPotentialMass_le_iVolume (X := SchemeComplexPoint f)
      (schemeProjectiveTNKahlerBackground f (m + 1) E) hψ)).ne'
    (ENNReal.natCast_ne_top _)

/-- **The volume bound from the Skoda sandwich**: for `τ < τ'' < τ(𝓕)`,
`vol Δ_{Y•}(θ, ψ_{τ''}) ≤ vol Δ(⊕_k 𝓕^{kτ}_k)` (`thm:pobmain` (1), [Xia21, Thm. 5.28] lower
bound, and the lattice point count of `Δ(⊕_k 𝓕^{kτ}_k)`). -/
theorem volume_generalPartialBody_obstacle_le [Nonempty (SchemeComplexPoint f)]
    (hSk : SGPT.TestCurve.SkodaRWN.SkodaInclusionIdeal F H) {τ τ'' : ℝ} (hlt : τ < τ'')
    (hτ'' : (τ'' : EReal) < F.slope)
    (hc : IsCompact (seriesBody f (m + 1) E Y hY (filtrationSeries F τ))) :
    letI := E.isSeparated
    letI := E.quasiCompact
    volume (PartialBody.generalPartialBody (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY)
      (H.curvature a) (F.obstacle H τ'')) ≤
        volume (seriesBody f (m + 1) E Y hY (filtrationSeries F τ)) := by
  let := E.isSeparated
  let := E.quasiCompact
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  have hψ := F.obstacle_isThetaPshPotential H hτ''
  have hsand := SGPT.NAPotential.NANS.TestConfig.iVolume_le_liminf_normalizedPieceDim
    F H hSk hlt hτ''
  have hlim : liminf (SGPT.NAPotential.NANS.TestConfig.normalizedPieceDim F (m + 1) τ) atTop ≤
      ((m + 1).factorial : ℝ≥0∞) * volume (seriesBody f (m + 1) E Y hY (filtrationSeries F τ)) :=
    liminf_le_seriesBody (filtrationSeries F τ) hc
  rw [PartialBody.volume_generalPartialBody_uncond
    (F := schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) hψ]
  refine ENNReal.div_le_of_le_mul ?_
  rw [mul_comm]
  exact hsand.trans hlim

/-- **`rmk:Okounkov:L2335` for filtrations with the Skoda inclusion** ([Xia21, Thm. 5.28]): let
`𝓕` be a filtration of `R(X, L)` satisfying the Skoda inclusion
(`H⁰(X, L^k ⊗ 𝓘(kψ_τ)) ⊆ 𝓕^{kτ'}_k` for `τ' < τ < τ(𝓕)`, `k ≫ 0`), `{θ}` big, `X` with a smooth
flag `Y•`. Then for every `τ < τ(𝓕) = Γ_max`, the partial Okounkov body `Δ_{Y•}(θ, Γ^𝓕_τ)` is
the Okounkov body of the graded linear series `⊕_k 𝓕^{kτ}_k`. -/
theorem seriesBody_filtrationSeries_eq [Nonempty (SchemeComplexPoint f)]
    (hSk : SGPT.TestCurve.SkodaRWN.SkodaInclusionIdeal F H)
    (hbig : letI := E.isSeparated; letI := E.quasiCompact;
      IsBigClass (RealBottChern.ofRepresentative (H.curvature a)))
    {τ : ℝ} (hτ : (τ : EReal) < F.slope) :
    letI := E.isSeparated
    letI := E.quasiCompact
    seriesBody f (m + 1) E Y hY (filtrationSeries F τ) = PartialBody.generalPartialBody
      (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) (H.curvature a)
      (F.testCurvePotential H τ) := by
  let := E.isSeparated
  let := E.quasiCompact
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  set 𝔽 := schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY with h𝔽
  rw [← generalPartialBody_obstacle_eq Y hY H F hbig hτ]
  set K := seriesBody f (m + 1) E Y hY (filtrationSeries F τ) with hK
  set P := PartialBody.generalPartialBody 𝔽 (H.curvature a) (F.obstacle H τ) with hP
  have hψτ := F.obstacle_isThetaPshPotential H hτ
  have hKP : K ⊆ P := seriesBody_filtrationSeries_subset Y hY H F hτ
  have hPcc := PartialBody.convex_isCompact_generalPartialBody (F := 𝔽) hψτ
  have hKc : IsClosed K := isClosed_seriesBody _
  have hKcpt : IsCompact K := hPcc.2.of_isClosed_subset hKc hKP
  have hPfin : volume P ≠ ⊤ := hPcc.2.measure_lt_top.ne
  have hPpos : 0 < volume P := volume_generalPartialBody_obstacle_pos Y hY H F hbig hτ
  -- an auxiliary level `τ < τ₁ < τ(𝓕)` and a point of `Δ(θ, ψ_{τ₁})`
  obtain ⟨τ₁, hττ₁, hτ₁⟩ := EReal.lt_iff_exists_real_btwn.mp hτ
  have hττ₁' : τ < τ₁ := EReal.coe_lt_coe_iff.mp hττ₁
  have hψτ₁ := F.obstacle_isThetaPshPotential H hτ₁
  obtain ⟨p, hp⟩ := nonempty_of_measure_ne_zero
    (volume_generalPartialBody_obstacle_pos Y hY H F hbig hτ₁).ne'
  -- `(1 - q)ⁿ vol Δ(θ, ψ_τ) ≤ vol Δ(⊕ 𝓕^{kτ}_k)` for rational `q ∈ (0, 1)`
  have hkey : ∀ q : ℚ, 0 < q → q < 1 →
      ENNReal.ofReal ((1 - (q : ℝ)) ^ (m + 1)) * volume P ≤ volume K := by
    intro q hq0 hq1
    have hq0R : (0 : ℝ) < q := by exact_mod_cast hq0
    have hq1R : (q : ℝ) < 1 := by exact_mod_cast hq1
    have hτlt : τ < (q : ℝ) * τ₁ + (1 - (q : ℝ)) * τ := by nlinarith
    have hτa₁ : (q : ℝ) * τ₁ + (1 - (q : ℝ)) * τ < τ₁ := by nlinarith
    have hτaslope : (((q : ℝ) * τ₁ + (1 - (q : ℝ)) * τ : ℝ) : EReal) < F.slope :=
      (EReal.coe_lt_coe_iff.mpr hτa₁).trans hτ₁
    have hψa := F.obstacle_isThetaPshPotential H hτaslope
    have hsub : (fun y => (q : ℝ) • p + (1 - (q : ℝ)) • y) '' P ⊆
        PartialBody.generalPartialBody 𝔽 (H.curvature a)
          (F.obstacle H ((q : ℝ) * τ₁ + (1 - (q : ℝ)) * τ)) := by
      rintro _ ⟨y, hy, rfl⟩
      have h1 := Valuative.convexComb_mem_generalPartialBody (F := 𝔽) (θ := H.curvature a)
        hψτ₁ hψτ hq0 hq1 hp hy
      have hcc := F.obstacle_concave H hττ₁' hτ₁ hq0R hq1R
      exact (PartialBody.generalPartialBody_subset_of_pointwise_le (F := 𝔽)
        (θ := H.curvature a) (isThetaPshPotential_convexComb hψτ₁ hψτ hq0R hq1R) hψa hcc
        hbig).1 h1
    have hvol1 : volume ((fun y => (q : ℝ) • p + (1 - (q : ℝ)) • y) '' P) =
        ENNReal.ofReal ((1 - (q : ℝ)) ^ (m + 1)) * volume P := by
      rw [volume_image_affine, abs_of_pos (by linarith)]
    have hvolA := volume_generalPartialBody_obstacle_le Y hY H F hSk hτlt hτaslope hKcpt
    calc ENNReal.ofReal ((1 - (q : ℝ)) ^ (m + 1)) * volume P
        = volume ((fun y => (q : ℝ) • p + (1 - (q : ℝ)) • y) '' P) := hvol1.symm
      _ ≤ _ := measure_mono hsub
      _ ≤ volume K := hvolA
  -- letting `q → 0`
  have hle : volume P ≤ volume K := by
    have hseq : Tendsto (fun j : ℕ => (((1 / ((j : ℚ) + 2) : ℚ) : ℝ))) atTop (𝓝 0) := by
      have h2 : Tendsto (fun j : ℕ => (j : ℝ) + 2) atTop atTop :=
        tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
      refine h2.inv_tendsto_atTop.congr fun j => ?_
      simp
    have h1 : Tendsto (fun j : ℕ => (1 - (((1 / ((j : ℚ) + 2) : ℚ) : ℝ))) ^ (m + 1)) atTop
        (𝓝 1) := by
      have := (tendsto_const_nhds (x := (1 : ℝ))).sub hseq
      simpa using this.pow (m + 1)
    have htend := ENNReal.Tendsto.mul_const (b := volume P) (ENNReal.tendsto_ofReal h1)
      (Or.inr hPfin)
    rw [ENNReal.ofReal_one, one_mul] at htend
    refine le_of_tendsto' htend fun j => hkey _ (by positivity) ?_
    rw [div_lt_one (by positivity)]
    have : (0 : ℚ) ≤ j := Nat.cast_nonneg j
    linarith
  exact eq_of_subset_of_volume_le hKP hKc hPcc.1 hPpos hPfin hle

/-- **`rmk:Okounkov:L2335` for finitely generated filtrations**: for the filtration `𝓕` of a
finitely generated normalized `ℤ`-filtration of `R(X, L)` (the encoding of test configurations of
lane TESTCONF2, [BHJ17, Prop. 2.15]), `θ = c₁(L, h)` Kähler (`{θ}` big), `X` with a smooth flag
and `τ < τ(𝓕)`: `Δ_{Y•}(⊕_k 𝓕^{kτ}_k) = Δ_{Y•}(θ, Γ^𝓕_τ)`. -/
theorem seriesBody_filtrationSeries_eq_of_finitelyGenerated
    (G : SGPT.TestCurve.TestConfig.SectionZFiltration f a) (hG : G.IsFinitelyGenerated)
    (h0 : G.piece 0 0 = ⊤)
    (hK : letI := E.isSeparated; letI := E.quasiCompact; (H.curvature a).val.IsKahler)
    (hbig : letI := E.isSeparated; letI := E.quasiCompact;
      IsBigClass (RealBottChern.ofRepresentative (H.curvature a)))
    {τ : ℝ} (hτ : (τ : EReal) < (G.fgFiltration hG h0).slope) :
    letI := E.isSeparated
    letI := E.quasiCompact
    seriesBody f (m + 1) E Y hY (filtrationSeries (G.fgFiltration hG h0) τ) =
      PartialBody.generalPartialBody (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY)
        (H.curvature a) ((G.fgFiltration hG h0).testCurvePotential H τ) := by
  let := E.isSeparated
  let := E.quasiCompact
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  have : Nonempty (SchemeComplexPoint f) := SGPT.GAGA.H0L.nonempty_of_smoothFlag Y hY
  have hgaga : ∀ᶠ j in atTop,
      SGPT.NAPotential.GAGAMult.SchemeSectionsAlgebraic f (m + 1) E a H j :=
    Eventually.of_forall fun j => SGPT.GAGA.H0L.schemeSectionsAlgebraic a H j
  have hSk :=
    SGPT.TestCurve.SkodaInc.skodaInclusionIdeal_of_sectionsAlgebraic_of_globalSkodaDivision
      G hG h0 H hK hgaga
      (SGPT.TestCurve.GlobalSkoda.globalSkodaDivision_of_sectionsAlgebraic H a hgaga)
  exact seriesBody_filtrationSeries_eq Y hY H _ hSk hbig hτ

end Main

/-! ### Test configurations -/

section TestConfiguration

open SGPT.TestCurve.TCEnc SGPT.TestCurve.TCLin

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} {E : ClosedProjectiveEmbedding f}
  [IsIntegral X] {m : ℕ} [SmoothOfRelativeDimension (m + 1) f]
  (Y : Fin (m + 1 + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y)
  {L : X.Modules} {a : LineBundleAtlas L} (H : SchemeLineBundleMetric f (m + 1) E L)

/-- **`rmk:Okounkov:L2335` for test configurations with finitely generated filtration** (lane
TC-ENC's `TestConfiguration`, no action or linearization used): for every smooth metric `h` on `L`
with `{c₁(L, h)}` a Hodge class and every `τ < τ(𝓕)`,
`Δ_{Y•}(⊕_k 𝓕^{kτ}_k) = Δ_{Y•}(θ, Γ^𝓕_τ)`. -/
theorem testConfiguration_seriesBody_eq (T : TestConfiguration f a)
    (hfg : T.FiltrationFinitelyGenerated E)
    (hHodge : letI := E.isSeparated; letI := E.quasiCompact;
      ∃ ω : ClosedRealOneOneForm (m + 1) (SchemeComplexPoint f), ω.val.IsKahler ∧
        RealBottChern.ofRepresentative ω = RealBottChern.ofRepresentative (H.curvature a))
    {τ : ℝ} (hτ : (τ : EReal) < (T.inducedFiltration E hfg).slope) :
    letI := E.isSeparated
    letI := E.quasiCompact
    seriesBody f (m + 1) E Y hY (filtrationSeries (T.inducedFiltration E hfg) τ) =
      PartialBody.generalPartialBody (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY)
        (H.curvature a) ((T.inducedFiltration E hfg).testCurvePotential H τ) := by
  let := E.isSeparated
  let := E.quasiCompact
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  have : Nonempty (SchemeComplexPoint f) := SGPT.GAGA.H0L.nonempty_of_smoothFlag Y hY
  obtain ⟨H₀, hK₀⟩ := SGPT.TestCurve.MiscM.exists_kahler_metric_of_hodge H a hHodge
  have hSk := SGPT.TestCurve.MiscM.skodaInclusionIdeal_inducedFiltration_of_kahler H T hfg hK₀
  have hbig : IsBigClass (RealBottChern.ofRepresentative (H.curvature a)) := by
    obtain ⟨ω, hω, hcl⟩ := hHodge
    rw [← hcl]
    exact PluripolarCapacityDichotomy.isBigClass_kahler ⟨ω, hω⟩
  exact seriesBody_filtrationSeries_eq Y hY H _ hSk hbig hτ

/-- **Source `rmk:Okounkov:L2335`**: let `(𝓧, 𝓛)` be an ample test configuration of `(X, L)` in
the sense of [BHJ17, Def. 2.1–2.3] (`𝔾_m`-action, `𝔾_m`-linearized `𝓛`, `𝓛` relatively ample;
`TCLin.LinearizedTestConfiguration`, as in `ex:RWN` and `rmk:PhongSturm`), `𝓕` the induced
filtration of `R(X, L)` (finitely generated, [BHJ17, Prop. 2.15]), `h` any smooth metric on `L`,
`θ = c₁(L, h)` with `{θ}` a Hodge class (it contains a Kähler form, e.g. `L` ample), `Γ = Γ^𝓕`
the test curve of `ex:RWN` built with `h` and `Y•` a smooth flag of `X`. Then for every
`τ < Γ_max = τ(𝓕)`, `Δ_{Y•}(θ, Γ_τ)` is the Okounkov body of the graded linear series
`⊕_k 𝓕^{kτ}_k` ([LM09], [BC11]). -/
theorem linearized_seriesBody_eq (T : LinearizedTestConfiguration f a) (hA : T.IsAmple)
    (hHodge : letI := E.isSeparated; letI := E.quasiCompact;
      ∃ ω : ClosedRealOneOneForm (m + 1) (SchemeComplexPoint f), ω.val.IsKahler ∧
        RealBottChern.ofRepresentative ω = RealBottChern.ofRepresentative (H.curvature a))
    {τ : ℝ} (hτ : (τ : EReal) <
      (T.inducedFiltration E (T.filtrationFinitelyGenerated E hA)).slope) :
    letI := E.isSeparated
    letI := E.quasiCompact
    seriesBody f (m + 1) E Y hY
        (filtrationSeries (T.inducedFiltration E (T.filtrationFinitelyGenerated E hA)) τ) =
      PartialBody.generalPartialBody (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY)
        (H.curvature a)
        ((T.inducedFiltration E (T.filtrationFinitelyGenerated E hA)).testCurvePotential H τ) :=
  testConfiguration_seriesBody_eq Y hY H T.toTestConfiguration _ hHodge hτ

/-- `rmk:Okounkov:L2335` for a metric `h` of Kähler curvature (a special case of
`linearized_seriesBody_eq`). -/
theorem linearized_seriesBody_eq_of_kahler (T : LinearizedTestConfiguration f a)
    (hA : T.IsAmple)
    (hK : letI := E.isSeparated; letI := E.quasiCompact; (H.curvature a).val.IsKahler)
    {τ : ℝ} (hτ : (τ : EReal) <
      (T.inducedFiltration E (T.filtrationFinitelyGenerated E hA)).slope) :
    letI := E.isSeparated
    letI := E.quasiCompact
    seriesBody f (m + 1) E Y hY
        (filtrationSeries (T.inducedFiltration E (T.filtrationFinitelyGenerated E hA)) τ) =
      PartialBody.generalPartialBody (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY)
        (H.curvature a)
        ((T.inducedFiltration E (T.filtrationFinitelyGenerated E hA)).testCurvePotential H τ) :=
  linearized_seriesBody_eq Y hY H T hA ⟨H.curvature a, hK, rfl⟩ hτ

end TestConfiguration

end SGPT.Okounkov.TCOko
