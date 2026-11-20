import SGPT.Okounkov.AlgPOBCounting
import SGPT.Okounkov.AlgebraicDXBody
import SGPT.IGood.DXMainStatement
import SGPT.Okounkov.PartialBodyDS
import SGPT.LineBundle.OkounkovVolume

/-!
# Algebraic partial Okounkov bodies from the asymptotic Riemann–Roch formula

Source: chapter *The theory of Okounkov bodies*, Section *Algebraic partial Okounkov bodies*:
`thm:Gammaasg` (`Γ(θ, φ)` is an almost semigroup), `def:Okounkov:L687` (the partial Okounkov body
`Δ_{Y•}(θ, φ) = Δ(Γ(θ, φ))`), `cor:POBvolume` (`vol Δ_{Y•}(θ, φ) = vol θ_φ / n!`) and
`cor:transalgPOB` (`Δ_{Y•}(dd^c h) = Δ_{Y•}(L, h)`), and Section *The Hausdorff convergence
property* (`thm:HCP` for `T = 𝒪_X`).

## Route

The source proves `thm:Gammaasg` and `cor:POBvolume` by approximating `Γ(θ, φ)` in `d_sg` by the
semigroups `Γ^∞` of analytic approximations, computing every distance with the asymptotic
Riemann–Roch formula `thm:DXmain1`. Here we use the transcendental theory instead (it is complete:
`thm:pobmain`, `thm:Okounkovtranmain`), together with the following two facts about the normalized
valuative points `k⁻¹ ν(s)`, `s ∈ H⁰(X, L^k ⊗ 𝓘(kφ)) \ {0}`:

* (**upper**, proved: `SGPT.Okounkov.AlgebraicDX.eventually_normalized_mem_thickening`) for every
  `η > 0` and all `k ≫ 0` they lie in the `η`-neighbourhood of the transcendental partial body
  `K = Δ_{Y•}(θ_φ)` (`def:generalPOB`);
* (**lower**) `liminf_k k⁻ⁿ #Γ_k(θ, φ) = liminf_k k⁻ⁿ h⁰(X, L^k ⊗ 𝓘(kφ)) ≥ vol K = vol θ_φ / n!`:
  this is the lower bound of `thm:DXmain1` (`SGPT.IGood.DXMain.DXMainLowerBound`), which is
  **not** proved in the workspace; it is the hypothesis `hlow` of the results below.

By the counting criterion `SGPT.Okounkov.AlgPOB.mem_almostSemigroupLocus_of_fills`, the two facts
give `d_sg(Γ(θ, φ), R(K)) = 0` for the saturated semigroup `R(K)` of `K`, hence `Γ(θ, φ)` is an
almost semigroup with Okounkov body `K`: the algebraic and the transcendental partial bodies
coincide, and the volume formula and the Hausdorff convergence follow.

## Formal setting

As in `SGPT.Okounkov.AlgebraicSectionBodies` and `SGPT.Okounkov.AlgebraicDXBody`: `X` an integral
smooth projective complex scheme of dimension `n = m + 1`, `Y•` a smooth flag of its analytic
manifold (`ν = ν_{Y•}`), `L` a line bundle with atlas `a` and smooth metric `H`,
`θ = c₁(L, H)`, `φ ∈ PSH(X, θ)`, `vol θ_φ = iVolume θ φ`; the admissible ambient cones are the cones
`C([0, C]ⁿ)` over cubes (`cubeCone`), which contain `Γ(θ, φ)` for `C ≫ 0`
(`exists_multiplierSectionSet_subset_cubeCone`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.Okounkov.AlgPOB

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set Filter MeasureTheory Metric
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.LineBundle SGPT.PSH SGPT.AlmostSemigroup SGPT.AlmostSemigroup.Class
  SGPT.AlmostSemigroup.OkounkovExtension SGPT.IGood.DXMain
open scoped Topology ENNReal NNReal Pointwise

/-! ### Cubes -/

/-- The cone over a larger cube contains the cone over a smaller one. -/
theorem latticePoints_cubeCone_mono {n : ℕ} {C C' : ℝ} (h : C ≤ C') :
    latticePoints (cubeCone (n := n) C).cone ≤ latticePoints (cubeCone (n := n) C').cone := by
  rintro z ⟨h2, h1⟩
  exact ⟨h2, fun i => ⟨(h1 i).1, (h1 i).2.trans (mul_le_mul_of_nonneg_right h h2)⟩⟩

/-! ### The scheme setting -/

variable {X : Scheme} (f : X ⟶ Spec (.of ℂ)) (E : ClosedProjectiveEmbedding f)
  [IsIntegral X] {m : ℕ} [SmoothOfRelativeDimension (m + 1) f]

local instance algPOBTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance algPOBCharts : ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (m + 1)
local instance algPOBManifold [IsSeparated f] [QuasiCompact f] :
    IsComplexManifold (m + 1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (m + 1)

variable (Y : Fin (m + 1 + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y)
  {L : X.Modules} (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f (m + 1) E L)

/-- The degree-`k` slice of `Γ(θ, φ)` consists of the valuative vectors of the nonzero sections of
`L^k ⊗ 𝓘(kφ)`. -/
theorem mem_slice_multiplierSectionSet (φ : SchemeComplexPoint f → EReal) (k : ℕ)
    (x : Fin (m + 1) → ℤ) :
    x ∈ slice (multiplierSectionSet f (m + 1) E Y hY a φ) (k : ℤ) ↔
      ∃ (s : bundlePowerGlobalSections L k) (hs : s ≠ 0), IsMultiplierSection f (m + 1) E φ k s ∧
        x = fun i => (schemeFubiniStudySectionVector f (m + 1) E Y hY a k s hs i : ℤ) := by
  constructor
  · rintro ⟨k', s, hs, hP, hz⟩
    have hk : k' = k := by
      have h2 := congrArg Prod.snd hz
      simp only at h2
      exact_mod_cast h2.symm
    subst hk
    exact ⟨s, hs, hP, congrArg Prod.fst hz⟩
  · rintro ⟨s, hs, hP, rfl⟩
    exact ⟨k, s, hs, hP, rfl⟩

/-- **`#Γ_k(θ, φ) = h⁰(X, L^k ⊗ 𝓘(kφ))`** (one-dimensional leaves, `[LM09, Lemma 1.3]`). -/
theorem card_slice_multiplierSectionSet {φ : SchemeComplexPoint f → EReal}
    (hφq : letI := E.isSeparated; letI := E.quasiCompact;
      ManifoldQuasiPlurisubharmonic (n := m + 1) φ) (k : ℕ) :
    Nat.card (slice (multiplierSectionSet f (m + 1) E Y hY a φ) (k : ℤ)) =
      multiplierH0 f (m + 1) E hφq L k := by
  rw [multiplierH0, ← card_sectionValues_eq_finrank f (m + 1) E Y hY a k
    (multiplierSubmodule f (m + 1) E hφq L k)]
  have hset : slice (multiplierSectionSet f (m + 1) E Y hY a φ) (k : ℤ) =
      (fun v : Fin (m + 1) → ℕ => fun i => (v i : ℤ)) ''
        sectionValues f (m + 1) E Y hY a k (multiplierSubmodule f (m + 1) E hφq L k) := by
    ext x
    rw [mem_slice_multiplierSectionSet]
    constructor
    · rintro ⟨s, hs, hP, rfl⟩
      exact ⟨_, ⟨s, hs, hP, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨s, hs, hP, rfl⟩, rfl⟩
      exact ⟨s, hs, hP, rfl⟩
  rw [hset]
  refine Nat.card_image_of_injective (fun v w hvw => ?_) _
  funext i
  exact_mod_cast congrFun hvw i

/-- `Γ(θ, φ)` as a lattice subset of an admissible cone containing it. -/
def multiplierConeSubset {C : AdmissibleCone (m + 1)} (φ : SchemeComplexPoint f → EReal)
    (hsub : multiplierSectionSet f (m + 1) E Y hY a φ ⊆ (latticePoints C.cone : Set _)) :
    ConeSubset C :=
  ⟨_, hsub⟩

/-- The normalized cardinalities of `Γ(θ, φ)` are `k⁻ⁿ h⁰(X, L^k ⊗ 𝓘(kφ))`. -/
theorem normalizedCardinality_multiplierConeSubset {C : AdmissibleCone (m + 1)}
    {φ : SchemeComplexPoint f → EReal}
    (hφq : letI := E.isSeparated; letI := E.quasiCompact;
      ManifoldQuasiPlurisubharmonic (n := m + 1) φ)
    (hsub : multiplierSectionSet f (m + 1) E Y hY a φ ⊆ (latticePoints C.cone : Set _)) (k : ℕ) :
    (multiplierConeSubset f E Y hY a φ hsub).normalizedCardinality k =
      (k : ℝ)⁻¹ ^ (m + 1) * multiplierH0 f (m + 1) E hφq L k := by
  have h := Nat.card_eq_card_finite_toFinset
    ((multiplierConeSubset f E Y hY a φ hsub).finite_slice k)
  rw [ConeSubset.normalizedCardinality, ← card_slice_multiplierSectionSet f E Y hY a hφq k]
  rw [show ((multiplierConeSubset f E Y hY a φ hsub).slices k).card =
    Nat.card (slice (multiplierSectionSet f (m + 1) E Y hY a φ) (k : ℤ)) from h.symm]

/-- **The upper hypothesis** (from the proved Okounkov upper bound of `thm:DXmain1`): for every
`η > 0` and all `k ≫ 0`, the normalized points of `Γ_k(θ, φ)` lie in the closed
`η`-neighbourhood of `Δ_{Y•}(θ_φ)`. -/
theorem multiplierConeSubset_upper {C : AdmissibleCone (m + 1)} {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val φ)
    (hsub : multiplierSectionSet f (m + 1) E Y hY a φ ⊆ (latticePoints C.cone : Set _))
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ k : ℕ in atTop, ∀ x ∈ (multiplierConeSubset f E Y hY a φ hsub).slices k,
      ((k : ℝ))⁻¹ • Counting.integerCast x ∈ cthickening η
        (PartialBody.generalPartialBody (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY)
          (H.curvature a) φ) := by
  obtain ⟨k₀, -, h⟩ := AlgebraicDX.eventually_normalized_mem_thickening f E Y hY a H hφ hη
  filter_upwards [eventually_ge_atTop k₀] with k hk x hx
  obtain ⟨s, hs, hP, rfl⟩ := (mem_slice_multiplierSectionSet f E Y hY a φ k x).mp
    ((ConeSubset.mem_slices _ k x).mp hx)
  have hcast : Counting.integerCast
      (fun i => (schemeFubiniStudySectionVector f (m + 1) E Y hY a k s hs i : ℤ)) =
      fun i => (schemeFubiniStudySectionVector f (m + 1) E Y hY a k s hs i : ℝ) := by
    funext i
    simp [Counting.integerCast]
  rw [hcast]
  exact thickening_subset_cthickening _ _ (h k hk s hs hP)

/-- **The lower hypothesis from the lower bound of `thm:DXmain1`**: if
`vol θ_φ ≤ liminf_k n! h⁰(X, L^k ⊗ 𝓘(kφ)) / kⁿ` (`DXMainLowerBound`), then for every `ε > 0` and
all `k ≫ 0`, `k⁻ⁿ #Γ_k(θ, φ) ≥ vol Δ_{Y•}(θ_φ) - ε`. -/
theorem multiplierConeSubset_lower {C : AdmissibleCone (m + 1)} {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val φ)
    (hsub : multiplierSectionSet f (m + 1) E Y hY a φ ⊆ (latticePoints C.cone : Set _))
    [Nonempty (SchemeComplexPoint f)] (hlow : DXMainLowerBound f E a H hφ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, volume.real
        (PartialBody.generalPartialBody (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY)
          (H.curvature a) φ) - ε ≤
      (multiplierConeSubset f E Y hY a φ hsub).normalizedCardinality k := by
  let := E.isSeparated
  let := E.quasiCompact
  let : MeasurableSpace (SchemeComplexPoint f) := borel _
  have : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  set 𝔽 := schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY with h𝔽
  set θ := H.curvature a with hθ
  have hφq : ManifoldQuasiPlurisubharmonic (n := m + 1) φ := hφ.1.quasiPlurisubharmonic
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
    rw [normalizedCardinality_multiplierConeSubset f E Y hY a hφq hsub k]
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
  have hev := Filter.eventually_lt_of_lt_liminf (hb.trans_le hlow)
  filter_upwards [hev, eventually_gt_atTop 0] with k hk hk0
  rw [normalizedCardinality_multiplierConeSubset f E Y hY a hφq hsub k]
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk0
  have hu : normalizedMultiplierH0 f E a H hφ k =
      ENNReal.ofReal (N * (multiplierH0 f (m + 1) E hφq L k : ℝ) / (k : ℝ) ^ (m + 1)) := by
    rw [normalizedMultiplierH0, ENNReal.ofReal_div_of_pos (by positivity),
      ENNReal.ofReal_mul hN.le, hNdef, ENNReal.ofReal_natCast, ENNReal.ofReal_natCast,
      ENNReal.ofReal_pow hkR.le, ENNReal.ofReal_natCast]
  rw [hu] at hk
  have hk' := (ENNReal.ofReal_lt_ofReal_iff'.mp hk).1
  have hinv : (k : ℝ)⁻¹ ^ (m + 1) * (multiplierH0 f (m + 1) E hφq L k : ℝ) =
      (multiplierH0 f (m + 1) E hφq L k : ℝ) / (k : ℝ) ^ (m + 1) := by
    rw [inv_pow, inv_mul_eq_div]
  rw [hinv]
  have h1 : V.toReal - N * ε < N * ((multiplierH0 f (m + 1) E hφq L k : ℝ) / (k : ℝ) ^ (m + 1)) := by
    rw [mul_div_assoc] at hk'
    exact hk'
  rw [div_sub' hN.ne', div_le_iff₀ hN]
  linarith

/-- `Δ_{Y•}(θ_φ)` lies in a cube `[0, C]ⁿ`, uniformly in `φ ∈ PSH(X, θ)` (general flag
geometry; from `Δ_{Y•}(θ_φ) ⊆ Δ_{Y•}(θ + ω)`). -/
theorem _root_.SGPT.Okounkov.PartialBody.exists_generalPartialBody_subset_Icc
    {F : OriginalFlagGeometry (m + 1)} (θ : ClosedRealOneOneForm (m + 1) F.carrier) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ φ : F.carrier → EReal, IsThetaPshPotential θ.val φ →
      PartialBody.generalPartialBody F θ φ ⊆ Icc (0 : Fin (m + 1) → ℝ) (fun _ => C) := by
  obtain ⟨C, hC0, hC⟩ := TranscendentalBody.exists_tradOkounkovBody_subset_Icc (F := F)
    (θ + (((0 : ℕ) : ℝ) + 1)⁻¹ • F.omega.form)
  refine ⟨C, hC0, fun φ hφ => ?_⟩
  have hK0 := PartialBody.isKahlerCurrentPotential_add_smul hφ F.omega
    (t := (((0 : ℕ) : ℝ) + 1)⁻¹) (by positivity)
  exact (iInter_subset _ 0).trans ((PartialBody.kahlerPartialBody_convexBody hK0).2.2.2.trans hC)

/-- **One cube cone for all `Γ(θ, φ)` and `Δ_{Y•}(θ_φ)`**: there is `C₀` such that for all
`C ≥ C₀` and all `φ ∈ PSH(X, θ)`, `Γ(θ, φ) ⊆ C([0, C]ⁿ)` and `Δ_{Y•}(θ_φ) ⊆ [0, C]ⁿ`. -/
theorem exists_cubeCone_contains :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ C : ℝ, C₀ ≤ C → ∀ φ : SchemeComplexPoint f → EReal,
      (letI := E.isSeparated; letI := E.quasiCompact;
        IsThetaPshPotential (H.curvature a).val φ) →
      multiplierSectionSet f (m + 1) E Y hY a φ ⊆
          (latticePoints (cubeCone (n := m + 1) C).cone : Set _) ∧
        PartialBody.generalPartialBody (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY)
          (H.curvature a) φ ⊆ heightOne (cubeCone (n := m + 1) C).cone := by
  obtain ⟨C₁, hC₁, hΓ⟩ := exists_multiplierSectionSet_subset_cubeCone f (m + 1) E Y hY a
  obtain ⟨C₂, hC₂, hK⟩ := PartialBody.exists_generalPartialBody_subset_Icc
    (F := schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) (H.curvature a)
  refine ⟨max C₁ C₂, le_max_of_le_left hC₁, fun C hC φ hφ => ⟨fun z hz => ?_, fun x hx => ?_⟩⟩
  · exact latticePoints_cubeCone_mono ((le_max_left _ _).trans hC) (hΓ φ hz)
  · rw [heightOne_cubeCone]
    obtain ⟨h0, h1⟩ := hK φ hφ hx
    exact ⟨h0, fun i => (h1 i).trans ((le_max_right _ _).trans hC)⟩

/-! ### The comparison theorem -/

omit [IsIntegral X] in
/-- `vol Δ_{Y•}(θ_φ) = vol θ_φ / n!` in real form. -/
theorem volume_real_generalPartialBody {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val φ) :
    letI := E.isSeparated
    letI := E.quasiCompact
    letI : MeasurableSpace (SchemeComplexPoint f) := borel _
    haveI : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
    haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    haveI : Nonempty (SchemeComplexPoint f) :=
      PartialBody.nonempty_carrier (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY)
    volume.real (PartialBody.generalPartialBody
        (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) (H.curvature a) φ) =
      (iVolume (H.curvature a) (LocalPotentials.closedRealOneOne_hasLocalPotentials _) φ hφ).toReal /
        ((m + 1).factorial : ℝ) := by
  let := E.isSeparated
  let := E.quasiCompact
  let : MeasurableSpace (SchemeComplexPoint f) := borel _
  have : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  rw [measureReal_def, PartialBody.volume_generalPartialBody_uncond
    (F := schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) hφ,
    ENNReal.toReal_div, ENNReal.toReal_natCast]

omit [IsIntegral X] in
/-- `vol θ_φ > 0` gives `vol Δ_{Y•}(θ_φ) > 0`. -/
theorem volume_real_generalPartialBody_pos {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val φ)
    (hpos : letI := E.isSeparated; letI := E.quasiCompact;
      letI : MeasurableSpace (SchemeComplexPoint f) := borel _;
      haveI : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩;
      haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact;
      haveI : Nonempty (SchemeComplexPoint f) :=
        PartialBody.nonempty_carrier (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY);
      0 < iVolume (H.curvature a) (LocalPotentials.closedRealOneOne_hasLocalPotentials _) φ hφ) :
    0 < volume.real (PartialBody.generalPartialBody
        (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) (H.curvature a) φ) := by
  let := E.isSeparated
  let := E.quasiCompact
  let : MeasurableSpace (SchemeComplexPoint f) := borel _
  have : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  set 𝔽 := schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY with h𝔽
  have hfin := ((PartialBody.convex_isCompact_generalPartialBody (F := 𝔽) hφ).2.measure_lt_top
      (μ := (volume : Measure (Fin (m + 1) → ℝ)))).ne
  rw [measureReal_def]
  refine ENNReal.toReal_pos ?_ hfin
  rw [PartialBody.volume_generalPartialBody_uncond (F := 𝔽) hφ]
  exact (ENNReal.div_pos hpos.ne' (ENNReal.natCast_ne_top _)).ne'

/-- **Source `thm:Gammaasg`, conditional on the lower bound of `thm:DXmain1`**: if
`vol θ_φ > 0` and `vol θ_φ ≤ liminf_k n! h⁰(X, L^k ⊗ 𝓘(kφ)) / kⁿ` (`DXMainLowerBound`), then for
every cube cone `C([0, C]ⁿ)` containing `Γ(θ, φ)` and `Δ_{Y•}(θ_φ)`, `Γ(θ, φ)` is an almost
semigroup: `Γ(θ, φ) ∈ 𝒮'(C)‾_{>0}`, with `vol Γ(θ, φ) = vol Δ_{Y•}(θ_φ) = vol θ_φ / n!`. -/
theorem multiplierConeSubset_mem_almostSemigroupLocus_of_lowerBound
    [Nonempty (SchemeComplexPoint f)] {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val φ)
    (hpos : 0 < volume.real (PartialBody.generalPartialBody
        (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) (H.curvature a) φ))
    (hlow : DXMainLowerBound f E a H hφ) {C : ℝ}
    (hsub : multiplierSectionSet f (m + 1) E Y hY a φ ⊆
      (latticePoints (cubeCone (n := m + 1) C).cone : Set _))
    (hKC : PartialBody.generalPartialBody (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY)
      (H.curvature a) φ ⊆ heightOne (cubeCone (n := m + 1) C).cone) :
    multiplierConeSubset f E Y hY a φ hsub ∈ almostSemigroupLocus (cubeCone (n := m + 1) C) ∧
      (multiplierConeSubset f E Y hY a φ hsub).volume =
        volume.real (PartialBody.generalPartialBody
          (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) (H.curvature a) φ) := by
  let := E.isSeparated
  let := E.quasiCompact
  obtain ⟨hKv, hKc⟩ := PartialBody.convex_isCompact_generalPartialBody
    (F := schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) hφ
  exact mem_almostSemigroupLocus_of_fills _ hKc hKv hKC _ hpos
    (fun η hη => multiplierConeSubset_upper f E Y hY a H hφ hsub hη)
    (fun ε hε => multiplierConeSubset_lower f E Y hY a H hφ hsub hlow hε)

/-- **Source `cor:transalgPOB` (with `def:Okounkov:L687`), conditional on the lower bound of
`thm:DXmain1`**: under the hypotheses of
`multiplierConeSubset_mem_almostSemigroupLocus_of_lowerBound`, the algebraic partial Okounkov body
`Δ_{Y•}(L, h) = Δ(Γ(θ, φ))` is the transcendental partial Okounkov body `Δ_{Y•}(dd^c h)` of the
current `θ_φ` (`def:generalPOB`), in Euclidean coordinates. -/
theorem partialOkounkovBody_eq_generalPartialBody_of_lowerBound
    [Nonempty (SchemeComplexPoint f)] {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val φ)
    (hpos : 0 < volume.real (PartialBody.generalPartialBody
        (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) (H.curvature a) φ))
    (hlow : DXMainLowerBound f E a H hφ) {C : ℝ}
    (hsub : multiplierSectionSet f (m + 1) E Y hY a φ ⊆
      (latticePoints (cubeCone (n := m + 1) C).cone : Set _))
    (hKC : PartialBody.generalPartialBody (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY)
      (H.curvature a) φ ⊆ heightOne (cubeCone (n := m + 1) C).cone) :
    partialOkounkovBody f (m + 1) E Y hY (cubeCone C) a φ =
      (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm '' PartialBody.generalPartialBody
        (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) (H.curvature a) φ := by
  let := E.isSeparated
  let := E.quasiCompact
  obtain ⟨hKv, hKc⟩ := PartialBody.convex_isCompact_generalPartialBody
    (F := schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) hφ
  have hmem := (multiplierConeSubset_mem_almostSemigroupLocus_of_lowerBound f E Y hY a H hφ hpos
    hlow hsub hKC).1
  rw [partialOkounkovBody_eq a φ hsub hmem]
  exact bodyExtension_eq_of_fills _ hKc hKv hKC _ hpos
    (fun η hη => multiplierConeSubset_upper f E Y hY a H hφ hsub hη)
    (fun ε hε => multiplierConeSubset_lower f E Y hY a H hφ hsub hlow hε) hmem

/-- **Source `thm:HCP` for `T = 𝒪_X`, conditional on the lower bound of `thm:DXmain1`**: the
polytopes `Δ_k(θ, φ)` (`def:Okounkov:L484`) converge in the Hausdorff metric to the partial
Okounkov body `Δ_{Y•}(θ, φ)` (equivalently, to the transcendental body `Δ_{Y•}(θ_φ)`). -/
theorem tendsto_hausdorffDist_multiplierDegreePolytope_of_lowerBound
    [Nonempty (SchemeComplexPoint f)] {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val φ)
    (hpos : 0 < volume.real (PartialBody.generalPartialBody
        (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) (H.curvature a) φ))
    (hlow : DXMainLowerBound f E a H hφ) {C : ℝ}
    (hsub : multiplierSectionSet f (m + 1) E Y hY a φ ⊆
      (latticePoints (cubeCone (n := m + 1) C).cone : Set _))
    (hKC : PartialBody.generalPartialBody (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY)
      (H.curvature a) φ ⊆ heightOne (cubeCone (n := m + 1) C).cone) :
    Tendsto (fun k => hausdorffDist
        ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm '' multiplierDegreePolytope f (m + 1) E Y hY a φ k)
        (partialOkounkovBody f (m + 1) E Y hY (cubeCone C) a φ)) atTop (𝓝 0) := by
  let := E.isSeparated
  let := E.quasiCompact
  obtain ⟨hKv, hKc⟩ := PartialBody.convex_isCompact_generalPartialBody
    (F := schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) hφ
  rw [partialOkounkovBody_eq_generalPartialBody_of_lowerBound f E Y hY a H hφ hpos hlow hsub hKC]
  exact tendsto_hausdorffDist_of_fills _ hKc hKv hKC (multiplierConeSubset f E Y hY a φ hsub) hpos
    (fun η hη => multiplierConeSubset_upper f E Y hY a H hφ hsub hη)
    (fun ε hε => multiplierConeSubset_lower f E Y hY a H hφ hsub hlow hε)

/-! ### The Okounkov body of a big line bundle -/

/-- A big line bundle is pseudo-effective: `V_θ ∈ PSH(X, θ)` (from a normalized `log |s|²`). -/
theorem isThetaPshPotential_thetaPshSupremum_of_isBig [Nonempty (SchemeComplexPoint f)]
    (hbig : IsBig f L (m + 1)) :
    letI := E.isSeparated
    letI := E.quasiCompact
    IsThetaPshPotential (H.curvature a).val (thetaPshSupremum (H.curvature a).val) := by
  let := E.isSeparated
  let := E.quasiCompact
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  obtain ⟨k, ⟨s, hs⟩, hk⟩ := ((hbig.eventually_exists_ne_zero).and (eventually_gt_atTop 0)).exists
  set θ := H.curvature a with hθ
  exact FirstPass.thetaPshSupremum_isThetaPshPotential θ.val θ.2.1 θ.2.2
    (LocalPotentials.closedRealOneOne_hasLocalPotentials θ)
    ⟨_, isThetaPshPotential_normalizedPotential f (m + 1) E a H hk hs⟩

/-- For a big line bundle, `vol Δ_{Y•}(θ, V_θ) > 0` (from `vol L ≤ vol θ_{V_θ}`, the proved upper
bound of `cor:volbigL`). -/
theorem volume_real_generalPartialBody_thetaPshSupremum_pos (hbig : IsBig f L (m + 1))
    (hV : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val (thetaPshSupremum (H.curvature a).val)) :
    0 < volume.real (PartialBody.generalPartialBody
        (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) (H.curvature a)
          (thetaPshSupremum (H.curvature a).val)) := by
  let := E.isSeparated
  let := E.quasiCompact
  let : MeasurableSpace (SchemeComplexPoint f) := borel _
  have : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  exact volume_real_generalPartialBody_pos f E Y hY a H hV
    ((hbig.volume_pos).trans_le (volume_le_iVolume_thetaPshSupremum f E a H Y hY hV))

/-- The cone subset `Γ(θ, V_θ) = Γ(L)`, with its count limit, under the lower bound of
`cor:volbigL` (`DXMainLowerBound` for `V_θ`): `k⁻ⁿ h⁰(X, L^k) → vol Δ_{Y•}(θ, V_θ)`. -/
theorem tendsto_normalizedCardinality_sectionSemigroup_of_lowerBound
    [Nonempty (SchemeComplexPoint f)]
    (hV : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val (thetaPshSupremum (H.curvature a).val))
    (hlow : DXMainLowerBound f E a H hV) {C : ℝ}
    (hS : schemeProjectiveSectionSemigroup f (m + 1) E Y hY a ≤
      latticePoints (cubeCone (n := m + 1) C).cone)
    (hKC : PartialBody.generalPartialBody (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY)
      (H.curvature a) (thetaPshSupremum (H.curvature a).val) ⊆
        heightOne (cubeCone (n := m + 1) C).cone) :
    Tendsto (SGPT.AlmostSemigroup.Okounkov.sourceSubset (cubeCone (n := m + 1) C) _ hS).normalizedCardinality atTop
      (𝓝 (volume.real (PartialBody.generalPartialBody
        (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) (H.curvature a)
          (thetaPshSupremum (H.curvature a).val)))) := by
  let := E.isSeparated
  let := E.quasiCompact
  have hΓ := SGPT.IGood.multiplierSectionSet_thetaPshSupremum (f := f) (n := m + 1) (E := E) Y hY H a a
  have hsub : multiplierSectionSet f (m + 1) E Y hY a (thetaPshSupremum (H.curvature a).val) ⊆
      (latticePoints (cubeCone (n := m + 1) C).cone : Set _) := by
    rw [hΓ]
    exact hS
  have heq : SGPT.AlmostSemigroup.Okounkov.sourceSubset (cubeCone (n := m + 1) C) _ hS =
      multiplierConeSubset f E Y hY a _ hsub := Subtype.ext hΓ.symm
  obtain ⟨hKv, hKc⟩ := PartialBody.convex_isCompact_generalPartialBody
    (F := schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) hV
  rw [heq]
  exact tendsto_normalizedCardinality_of_fills _ hKc hKv hKC _
    (fun η hη => multiplierConeSubset_upper f E Y hY a H hV hsub hη)
    (fun ε hε => multiplierConeSubset_lower f E Y hY a H hV hsub hlow hε)

/-- **Source `prop:Okounbiglbdl`, Step 2, conditional on the lower bound of `cor:volbigL`**: for a
big line bundle `L`, if `vol θ_{V_θ} ≤ liminf_k n! h⁰(X, L^k) / kⁿ` (`DXMainLowerBound` for the
potential `V_θ` of minimal singularities), then `Γ(L)` generates `ℤⁿ⁺¹`. -/
theorem generatedGroup_sectionSemigroup_eq_top_of_lowerBound
    [Nonempty (SchemeComplexPoint f)] (hbig : IsBig f L (m + 1))
    (hV : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val (thetaPshSupremum (H.curvature a).val))
    (hlow : DXMainLowerBound f E a H hV) :
    LatticeSlices.generatedGroup (schemeProjectiveSectionSemigroup f (m + 1) E Y hY a) = ⊤ := by
  let := E.isSeparated
  let := E.quasiCompact
  obtain ⟨C₀, -, hC⟩ := exists_cubeCone_contains f E Y hY a H
  obtain ⟨hsub, hKC⟩ := hC C₀ le_rfl _ hV
  have hΓ := SGPT.IGood.multiplierSectionSet_thetaPshSupremum (f := f) (n := m + 1) (E := E) Y hY H a a
  have hS : schemeProjectiveSectionSemigroup f (m + 1) E Y hY a ≤
      latticePoints (cubeCone (n := m + 1) C₀).cone := by
    intro z hz
    exact hsub (hΓ.symm ▸ hz)
  obtain ⟨hKv, hKc⟩ := PartialBody.convex_isCompact_generalPartialBody
    (F := schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) hV
  exact Intersection.generatedGroup_eq_top_of_full_count_limit _ _ hS hKc
    (AlgebraicDX.lineBundleOkounkovBody_subset_generalPartialBody f E Y hY a H ⟨_, hV⟩)
    (volume_real_generalPartialBody_thetaPshSupremum_pos f E Y hY a H hbig hV)
    (tendsto_normalizedCardinality_sectionSemigroup_of_lowerBound f E Y hY a H hV hlow hS hKC)

/-- **Source `prop:Okounbiglbdl`, conditional on the lower bound of `cor:volbigL`**: there is a
convex body `Δ = [0, C]ⁿ` with `Γ(L) ∈ 𝒮'(Δ)` (an additive semigroup in the cone `C(Δ)`
generating `ℤⁿ⁺¹`). -/
theorem exists_sectionSemigroup_mem_fullSemigroupLocus_of_lowerBound
    [Nonempty (SchemeComplexPoint f)] (hbig : IsBig f L (m + 1))
    (hV : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val (thetaPshSupremum (H.curvature a).val))
    (hlow : DXMainLowerBound f E a H hV) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ hS : schemeProjectiveSectionSemigroup f (m + 1) E Y hY a ≤
      latticePoints (cubeCone (n := m + 1) C).cone,
      SGPT.AlmostSemigroup.Okounkov.sourceSubset (cubeCone (n := m + 1) C) _ hS ∈ fullSemigroupLocus (cubeCone (n := m + 1) C) := by
  obtain ⟨C, hC0, hS⟩ := exists_schemeProjectiveSectionSemigroup_le_cubeCone f (m + 1) E Y hY a
  exact ⟨C, hC0, hS, sourceSubset_mem_fullSemigroupLocus _ _ hS
    (generatedGroup_sectionSemigroup_eq_top_of_lowerBound f E Y hY a H hbig hV hlow)⟩

/-- **The algebraic Okounkov body is the transcendental one (`def:Okobd`, `cor:transalgPOB` for
minimal singularities), conditional on the lower bound of `cor:volbigL`**: for a big line bundle,
`Δ_{Y•}(L) = Δ_{Y•}(θ, V_θ)`. -/
theorem lineBundleOkounkovBody_eq_generalPartialBody_of_lowerBound
    [Nonempty (SchemeComplexPoint f)] (hbig : IsBig f L (m + 1))
    (hV : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val (thetaPshSupremum (H.curvature a).val))
    (hlow : DXMainLowerBound f E a H hV) :
    lineBundleOkounkovBody f (m + 1) E Y hY a =
      PartialBody.generalPartialBody (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY)
        (H.curvature a) (thetaPshSupremum (H.curvature a).val) := by
  let := E.isSeparated
  let := E.quasiCompact
  obtain ⟨C₀, -, hC⟩ := exists_cubeCone_contains f E Y hY a H
  obtain ⟨hsub, hKC⟩ := hC C₀ le_rfl _ hV
  have hΓ := SGPT.IGood.multiplierSectionSet_thetaPshSupremum (f := f) (n := m + 1) (E := E) Y hY H a a
  have hS : schemeProjectiveSectionSemigroup f (m + 1) E Y hY a ≤
      latticePoints (cubeCone (n := m + 1) C₀).cone := by
    intro z hz
    exact hsub (hΓ.symm ▸ hz)
  obtain ⟨hKv, hKc⟩ := PartialBody.convex_isCompact_generalPartialBody
    (F := schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) hV
  have hpos := volume_real_generalPartialBody_thetaPshSupremum_pos f E Y hY a H hbig hV
  have hG := generatedGroup_sectionSemigroup_eq_top_of_lowerBound f E Y hY a H hbig hV hlow
  have hsubK := AlgebraicDX.lineBundleOkounkovBody_subset_generalPartialBody f E Y hY a H ⟨_, hV⟩
  have hvolB : volume.real (lineBundleOkounkovBody f (m + 1) E Y hY a) =
      volume.real (PartialBody.generalPartialBody
        (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) (H.curvature a)
          (thetaPshSupremum (H.curvature a).val)) := by
    change volume.real (SGPT.AlmostSemigroup.Okounkov.body _) = _
    rw [← BodyGeometry.volume_source_eq_body _ _ hS hG]
    exact (tendsto_normalizedCardinality_sectionSemigroup_of_lowerBound f E Y hY a H hV hlow
      hS hKC).limsup_eq
  refine hsubK.antisymm (Intersection.subset_of_volume_inter_eq hKc
    (lineBundleOkounkovBody_isClosed_convex a).1 hKv
    (interior_nonempty_of_positive_volume hKc.isClosed hKv hpos) ?_)
  rw [Set.inter_eq_right.mpr hsubK, hvolB]

/-- **Source `cor:Okounvol`, conditional on the lower bound of `cor:volbigL`**: for a big line
bundle, `vol L = n! vol Δ_{Y•}(L)` (and the `limsup` defining `vol L` is a limit). -/
theorem volume_eq_factorial_mul_okounkovBody_of_lowerBound
    [Nonempty (SchemeComplexPoint f)] (hbig : IsBig f L (m + 1))
    (hV : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val (thetaPshSupremum (H.curvature a).val))
    (hlow : DXMainLowerBound f E a H hV) :
    SGPT.LineBundle.volume f L (m + 1) = ENNReal.ofReal (((m + 1).factorial : ℝ) *
      volume.real (lineBundleOkounkovBody f (m + 1) E Y hY a)) := by
  obtain ⟨C, -, hS⟩ := exists_schemeProjectiveSectionSemigroup_le_cubeCone f (m + 1) E Y hY a
  exact SGPT.LineBundle.volume_eq_factorial_mul_okounkovBody f (m + 1) E Y hY a (cubeCone C) hS
    (generatedGroup_sectionSemigroup_eq_top_of_lowerBound f E Y hY a H hbig hV hlow)

/-- **Source `prop:Deltaconvtwisted` for `T = 𝒪_X`, conditional on the lower bound of
`cor:volbigL`**: `Δ_k(L) → Δ_{Y•}(L)` in the Hausdorff metric. -/
theorem tendsto_hausdorffDist_lineBundleDegreeBody_of_lowerBound
    [Nonempty (SchemeComplexPoint f)] (hbig : IsBig f L (m + 1))
    (hV : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val (thetaPshSupremum (H.curvature a).val))
    (hlow : DXMainLowerBound f E a H hV) :
    Tendsto (fun k => hausdorffDist (schemeProjectiveSectionDegreeBody f (m + 1) E Y hY a k)
      ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm '' lineBundleOkounkovBody f (m + 1) E Y hY a))
      atTop (𝓝 0) :=
  tendsto_hausdorffDist_lineBundleDegreeBody_of_generates f (m + 1) E Y hY a
    (generatedGroup_sectionSemigroup_eq_top_of_lowerBound f E Y hY a H hbig hV hlow)

end SGPT.Okounkov.AlgPOB
