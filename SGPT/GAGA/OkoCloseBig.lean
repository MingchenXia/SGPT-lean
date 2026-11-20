import SGPT.GAGA.OkoCloseHCP
import SGPT.Foundations.Analysis.Pending.BoucksomMassBigness
import SGPT.Okounkov.OkoLelongMin

/-!
# Big line bundles: `L` big ⟹ `{c₁(L)}` big, `thm:Okoucont` for big `L`, and
`prop:Deltaconvtwisted` for every twist


Setting of lane OKO-A / DXMAIN: `X` an integral smooth projective complex scheme of dimension
`n = m + 1` carrying a smooth flag `Y•`, `L` a line bundle with atlas `a` and smooth metric `H`,
`θ = c₁(L, H)`.

* **`isBigClass_of_isBig`**: if `L` is big (`h⁰(X, L^k) ≥ c kⁿ` for `k ≫ 0`), the class `{θ}` is
  big: `0 < vol L ≤ vol θ_{V_θ}` (the upper bound of `cor:volbigL`), and a class with a potential
  of positive non-pluripolar mass is big (Boucksom). With lane H0-GAGA3's
  `SGPT.GAGA.H0L.volume_pos` (the converse), `L` big ⟺ `{c₁(L)}` big.
* **`exists_continuous_partialOkounkovBody_of_isBig`**: `thm:Okoucont` with the book's hypothesis
  "`L` big".
* **`tendsto_hausdorffDist_twistedDegreePolytope`** (`prop:Deltaconvtwisted` for every `T`):
  `Δ_{k,T}(L) → Δ_{Y•}(L)` in the Hausdorff metric. Upper half: for a nonzero
  `s ∈ H⁰(X, T ⊗ L^k)` the potential `k⁻¹ log |s|²` is `(θ + k⁻¹ c₁(T, h_T))`-psh with analytic
  singularities, so `k⁻¹ ν(s) ∈ Δ(θ + δ ω)` for `k ≥ k(δ)`, and `Δ(θ + δ ω) ↓ Δ(θ) = Δ_{Y•}(L)`
  (`thm:Okounkovtranmain` (4)); lower half: `H⁰(X, T ⊗ L^k ⊗ 𝓘(k V_θ)) ⊆ H⁰(X, T ⊗ L^k)` and the
  twisted lower bound.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.GAGA.OkoClose

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set Filter MeasureTheory Metric
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Okounkov SGPT.Okounkov.AlgPOB SGPT.LineBundle SGPT.PSH SGPT.AlmostSemigroup
open SGPT.AlmostSemigroup.Class
open SGPT.Okounkov.TranscendentalCore SGPT.Okounkov.TranscendentalPartial
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus SGPT.Foundations.Analysis.Pending.DiagonalMass
  SGPT.Foundations.Analysis.Pending.ThetaPshL1Topology
  SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityDistance
open scoped Topology ENNReal NNReal Pointwise

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (E : ClosedProjectiveEmbedding f)
  [IsIntegral X] {m : ℕ} [SmoothOfRelativeDimension (m + 1) f]

local instance okoBigTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance okoBigCharts : ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (m + 1)
local instance okoBigManifold [IsSeparated f] [QuasiCompact f] :
    IsComplexManifold (m + 1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (m + 1)

variable (Y : Fin (m + 1 + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y)
  {L : X.Modules} (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f (m + 1) E L)

include Y hY in
/-- **A big line bundle has a big first Chern class**: if `L` is big, then `{c₁(L, H)}` is a big
class (on `X` with a smooth flag). -/
theorem isBigClass_of_isBig (hbig : IsBig f L (m + 1)) :
    letI := E.isSeparated
    letI := E.quasiCompact
    haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    IsBigClass (RealBottChern.ofRepresentative (H.curvature a)) := by
  let := E.isSeparated
  let := E.quasiCompact
  let : MeasurableSpace (SchemeComplexPoint f) := borel _
  have : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  have : Nonempty (SchemeComplexPoint f) :=
    PartialBody.nonempty_carrier (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY)
  have : ConnectedSpace (SchemeComplexPoint f) := schemeSmoothFlag_connectedSpace f (m + 1) Y hY
  have hV := isThetaPshPotential_thetaPshSupremum_of_isBig f E a H hbig
  have hle := SGPT.IGood.DXMain.volume_le_iVolume_thetaPshSupremum f E a H Y hY hV
  have hpos := (hbig.volume_pos).trans_le hle
  unfold iVolume at hpos
  exact BoucksomMassBigness.isBigClass_of_diagonalPotentialMass_pos (Nat.succ_pos m)
    (schemeProjectiveTNKahlerBackground f (m + 1) E) (H.curvature a) _ hpos

/-- **Source `thm:Okoucont`** with the book's hypothesis: for a big line bundle `L`, for every
large cube cone the partial Okounkov body map `(PSH(X, θ)_{>0}, d_S) → (𝒦ₙ, d_Haus)`,
`φ ↦ Δ_{Y•}(θ, φ)`, is continuous. -/
theorem exists_continuous_partialOkounkovBody_of_isBig [Nonempty (SchemeComplexPoint f)]
    (hbig : IsBig f L (m + 1)) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ C : ℝ, C₀ ≤ C →
      letI := E.isSeparated
      letI := E.quasiCompact
      letI : MeasurableSpace (SchemeComplexPoint f) := borel _
      haveI : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
      haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
      haveI : ConnectedSpace (SchemeComplexPoint f) :=
        schemeSmoothFlag_connectedSpace f (m + 1) Y hY
      letI : TopologicalSpace (ThetaPshL1 (H.curvature a).val) :=
        (singularityPseudoMetricSpace (schemeProjectiveTNKahlerBackground f (m + 1) E)
          (H.curvature a) (isBigClass_of_isBig f E Y hY a H hbig)).toUniformSpace.toTopologicalSpace
      ∃ G : {v : ThetaPshL1 (H.curvature a).val //
          HasPositivePotentialMass (H.curvature a) v.val v.property} →
          ConvexBody (EuclideanSpace ℝ (Fin (m + 1))),
        Continuous G ∧ ∀ v, (G v : Set (EuclideanSpace ℝ (Fin (m + 1)))) =
          partialOkounkovBody f (m + 1) E Y hY (cubeCone C) a v.val.val :=
  SGPT.GAGA.H0L.exists_continuous_partialOkounkovBody f E Y hY a H
    (isBigClass_of_isBig f E Y hY a H hbig)

/-! ### `prop:Deltaconvtwisted` for every twist -/

omit [IsIntegral X] in
/-- A lattice point `x ≥ 0` with `k⁻¹ x ∈ K^1` (`K ⊆ [0, C]ⁿ`) lies in the cone over `[0, C + 1]ⁿ`. -/
theorem mem_latticePoints_cubeCone_of_mem_thickening {n : ℕ} {C : ℝ} {K : Set (Fin n → ℝ)}
    (hKC : K ⊆ heightOne (cubeCone (n := n) C).cone) {x : Fin n → ℤ} (hx0 : ∀ i, 0 ≤ x i)
    {k : ℕ} (hk : 0 < k) (h : ((k : ℝ))⁻¹ • Counting.integerCast x ∈ thickening 1 K) :
    (x, (k : ℤ)) ∈ (latticePoints (cubeCone (n := n) (C + 1)).cone : Set _) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  obtain ⟨y, hyK, hdy⟩ := mem_thickening_iff.mp h
  have hyC := hKC hyK
  change (y, (1 : ℝ)) ∈ (cubeCone (n := n) C).cone at hyC
  obtain ⟨-, hy⟩ := hyC
  change (0 : ℝ) ≤ ((k : ℤ) : ℝ) ∧ ∀ i, (0 : ℝ) ≤ (x i : ℝ) ∧ (x i : ℝ) ≤ (C + 1) * ((k : ℤ) : ℝ)
  push_cast
  refine ⟨hkpos.le, fun i => ⟨by exact_mod_cast hx0 i, ?_⟩⟩
  have hdi : |((k : ℝ))⁻¹ * (x i : ℝ) - y i| < 1 := by
    have h1 := (dist_le_pi_dist (((k : ℝ))⁻¹ • Counting.integerCast x) y i).trans_lt hdy
    rw [Real.dist_eq] at h1
    simpa [Counting.integerCast] using h1
  have hyi := (hy i).2
  rw [mul_one] at hyi
  have h2 : ((k : ℝ))⁻¹ * (x i : ℝ) < C + 1 := by linarith [(abs_lt.mp hdi).2]
  rw [inv_mul_lt_iff₀ hkpos] at h2
  linarith

variable {T : X.Modules} (aT : LineBundleAtlas T)

/-- The lattice values `ν(s)` of all nonzero sections `s ∈ H⁰(X, T ⊗ L^k)` (the points of
`Δ_{k,T}(L)`, `def:DeltakT`). -/
def twistedSectionValues (k : ℕ) (b : LineBundleAtlas (bundleTensor T (bundleTensorPower L k))) :
    Set (Fin (m + 1) → ℤ) :=
  {x | ∃ (s : bundlePowerGlobalSections (bundleTensor T (bundleTensorPower L k)) 1) (hs : s ≠ 0),
    x = fun i => (schemeFubiniStudySectionVector f (m + 1) E Y hY b 1 s hs i : ℤ)}

theorem twistedSectionValues_atlas_independent (k : ℕ)
    (b b' : LineBundleAtlas (bundleTensor T (bundleTensorPower L k))) :
    twistedSectionValues f E Y hY k b = twistedSectionValues f E Y hY k b' := by
  let := E.isSeparated
  let := E.quasiCompact
  have hv (s : bundlePowerGlobalSections (bundleTensor T (bundleTensorPower L k)) 1) (hs : s ≠ 0) :
      schemeFubiniStudySectionVector f (m + 1) E Y hY b 1 s hs =
        schemeFubiniStudySectionVector f (m + 1) E Y hY b' 1 s hs :=
    schemeOriginalFlagSectionVector_atlas_independent f (m + 1) E
      (schemeProjectiveTNKahlerBackground f (m + 1) E) Y hY b b' 1 s hs
  ext x
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨s, hs, by rw [hv]⟩
  · rintro ⟨s, hs, rfl⟩
    exact ⟨s, hs, by rw [hv]⟩

/-- **Twisted sections and the Kähler perturbations of `{θ}`**: for every `δ > 0` and `k ≫ 0`,
`k⁻¹ ν(s) ∈ Δ(θ + δ ω)` for every nonzero `s ∈ H⁰(X, T ⊗ L^k)`. -/
theorem eventually_twistedSection_mem_tradOkounkovBody {δ : ℝ} (hδ : 0 < δ) :
    letI := E.isSeparated
    letI := E.quasiCompact
    ∃ k₀ : ℕ, 0 < k₀ ∧ ∀ k : ℕ, k₀ ≤ k →
      ∀ (s : bundlePowerGlobalSections (bundleTensor T (bundleTensorPower L k)) 1) (hs : s ≠ 0),
        (k : ℝ)⁻¹ • (fun i => (schemeFubiniStudySectionVector f (m + 1) E Y hY
            (SGPT.IGood.DXMain.twistAtlas aT a k) 1 s hs i : ℝ)) ∈
          tradOkounkovBody (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY)
            (H.curvature a + δ • (schemeProjectiveTNKahlerBackground f (m + 1) E).form) := by
  let := E.isSeparated
  let := E.quasiCompact
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  let HT : SchemeLineBundleMetric f (m + 1) E T := schemeLineBundleMetric f (m + 1) E aT
  set 𝔽 := schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY with h𝔽
  set ω := schemeProjectiveTNKahlerBackground f (m + 1) E with hω
  set θ := H.curvature a with hθ
  obtain ⟨CT, hCT, hCTsemi⟩ :=
    KahlerDomination.exists_pos_isSemipositive_add_smul ω (-(HT.curvature aT))
  refine ⟨⌈4 * CT / δ⌉₊ + 1, Nat.succ_pos _, fun k hk s hs => ?_⟩
  have hkpos : 0 < k := lt_of_lt_of_le (Nat.succ_pos _) hk
  have hkR : (0 : ℝ) < k := by exact_mod_cast hkpos
  have hk2 : 4 * CT / δ ≤ k := by
    calc 4 * CT / δ ≤ ⌈4 * CT / δ⌉₊ := Nat.le_ceil _
      _ ≤ (k : ℝ) := by exact_mod_cast (Nat.le_succ _).trans hk
  have hpsh := SGPT.IGood.DXMain.isThetaPshPotential_twistedPotential f E aT HT a H hkpos hs
  have hpsh2 : IsThetaPshPotential (θ + (δ / 2) • ω.form).val
      (SGPT.IGood.DXMain.twistedPotential f E aT HT a H k s) := by
    refine TranscendentalBody.isThetaPshPotential_of_le hpsh ?_
    have hkinv : (k : ℝ)⁻¹ * CT ≤ δ / 2 := by
      rw [inv_mul_le_iff₀ hkR]
      rw [div_le_iff₀ hδ] at hk2
      nlinarith
    have heq : θ + (δ / 2) • ω.form - (θ + (k : ℝ)⁻¹ • HT.curvature aT) =
        (k : ℝ)⁻¹ • (-(HT.curvature aT) + CT • ω.form) + (δ / 2 - (k : ℝ)⁻¹ * CT) • ω.form := by
      module
    rw [heq]
    exact UniformPerturbedKahlerLowerBound.isSemipositive_add
      (KahlerDomination.isSemipositive_smul hCTsemi (inv_nonneg.mpr hkR.le))
      (KahlerDomination.isSemipositive_smul ω.isSemipositive (by linarith))
  have hθ2 : θ + (δ / 2) • ω.form + (δ / 2) • ω.form = θ + δ • ω.form := by
    rw [add_assoc, ← add_smul, add_halves]
  have hK : IsKahlerCurrentPotential (θ + δ • ω.form)
      (SGPT.IGood.DXMain.twistedPotential f E aT HT a H k s) := by
    have h := PartialBody.isKahlerCurrentPotential_add_smul hpsh2 ω (by positivity : (0 : ℝ) < δ / 2)
    rwa [hθ2] at h
  have hA : SGPT.IGood.DXMain.twistedPotential f E aT HT a H k s ∈
      analyticCurrents (θ + δ • ω.form) := by
    refine ⟨TranscendentalBody.isThetaPshPotential_of_le hpsh2 ?_,
      SGPT.IGood.DXMain.hasManifoldAnalyticSingularityType_twistedPotential f E aT HT a H k hs⟩
    have heq : θ + δ • ω.form - (θ + (δ / 2) • ω.form) = (δ / 2) • ω.form := by module
    rw [heq]
    exact KahlerDomination.isSemipositive_smul ω.isSemipositive (by positivity)
  have hmem := partialOkounkovBody_subset_tradOkounkovBody _ _
    (flagValuation_self_mem_partialOkounkovBody_of_analytic (F := 𝔽) hK hA)
  rw [SGPT.IGood.DXMain.flagValuation_twistedPotential f E Y hY aT HT a H k s hs] at hmem
  exact hmem

include Y hY in
/-- **The Kähler perturbations `Δ(θ + δ ω)` decrease to `Δ_{Y•}(L)`**: for a big line bundle and
every `η > 0` there is `δ > 0` with `Δ(θ + δ ω) ⊆ Δ_{Y•}(θ, V_θ)^η` (`thm:Okounkovtranmain` (4),
compactness). -/
theorem exists_tradOkounkovBody_subset_thickening [Nonempty (SchemeComplexPoint f)]
    (hbig : IsBig f L (m + 1)) {η : ℝ} (hη : 0 < η) :
    letI := E.isSeparated
    letI := E.quasiCompact
    ∃ δ : ℝ, 0 < δ ∧
      tradOkounkovBody (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY)
          (H.curvature a + δ • (schemeProjectiveTNKahlerBackground f (m + 1) E).form) ⊆
        thickening η (PartialBody.generalPartialBody
          (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) (H.curvature a)
          (thetaPshSupremum (H.curvature a).val)) := by
  let := E.isSeparated
  let := E.quasiCompact
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  set 𝔽 := schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY with h𝔽
  set θ := H.curvature a with hθ
  have hV := isThetaPshPotential_thetaPshSupremum_of_isBig f E a H hbig
  have hbigC := isBigClass_of_isBig f E Y hY a H hbig
  have hbigB : SGPT.PSH.BookCurrent.IsBig (RealBottChern.ofRepresentative θ) :=
    (SGPT.PSH.BookCurrent.isBig_iff_isBigClass _).mpr hbigC
  have hmin : ∀ ψ : SchemeComplexPoint f → EReal, IsThetaPshPotential θ.val ψ →
      SingularityLE ψ (thetaPshSupremum θ.val) := fun ψ hψ =>
    FirstPass.thetaPshSupremum_minimalSingularities θ.val θ.2.1 θ.2.2
      (LocalPotentials.closedRealOneOne_hasLocalPotentials θ) ⟨_, hV⟩ ψ hψ
  have hKeq : PartialBody.generalPartialBody 𝔽 θ (thetaPshSupremum θ.val) = tradOkounkovBody 𝔽 θ :=
    PartialBody.generalPartialBody_eq_tradOkounkovBody_of_minimal (F := 𝔽) hbigB hV hmin
  set ω := schemeProjectiveTNKahlerBackground f (m + 1) E with hω
  set V : ℕ → Set (Fin (m + 1) → ℝ) :=
    fun j => tradOkounkovBody 𝔽 (θ + ((j : ℝ) + 1)⁻¹ • ω.form) with hVdef
  have hInter : ⋂ j, V j = tradOkounkovBody 𝔽 θ :=
    PartialBody.iInter_tradOkounkovBody_nat_eq (F := 𝔽) hbigB
  have hcpt : ∀ j, IsCompact (V j) := fun j => by
    obtain ⟨C, -, hC⟩ := TranscendentalBody.exists_tradOkounkovBody_subset_Icc (F := 𝔽)
      (θ + ((j : ℝ) + 1)⁻¹ • ω.form)
    exact isCompact_Icc.of_isClosed_subset (isClosed_tradOkounkovBody _) hC
  have hanti : Antitone V := by
    intro j j' hjj'
    refine PartialBody.tradOkounkovBody_subset_of_le (F := 𝔽) ?_
    have heq : θ + ((j : ℝ) + 1)⁻¹ • ω.form - (θ + ((j' : ℝ) + 1)⁻¹ • ω.form) =
        (((j : ℝ) + 1)⁻¹ - ((j' : ℝ) + 1)⁻¹) • ω.form := by module
    rw [heq]
    refine KahlerDomination.isSemipositive_smul ω.isSemipositive (sub_nonneg.mpr ?_)
    have : (j : ℝ) ≤ j' := by exact_mod_cast hjj'
    gcongr
  obtain ⟨j, hj⟩ := exists_subset_nhds_of_isCompact' hanti.directed_ge hcpt
    (fun j => isClosed_tradOkounkovBody _)
    (U := thickening η (PartialBody.generalPartialBody 𝔽 θ (thetaPshSupremum θ.val)))
    (fun x hx => isOpen_thickening.mem_nhds
      (self_subset_thickening hη _ (by rw [hKeq, ← hInter]; exact hx)))
  exact ⟨((j : ℝ) + 1)⁻¹, by positivity, hj⟩

include Y hY in
/-- **Upper half of `prop:Deltaconvtwisted`**: for a big line bundle, every `η > 0` and `k ≫ 0`,
`k⁻¹ ν(s) ∈ Δ_{Y•}(θ, V_θ)^η` for every nonzero `s ∈ H⁰(X, T ⊗ L^k)`. -/
theorem eventually_twistedSectionValues_mem_thickening [Nonempty (SchemeComplexPoint f)]
    (hbig : IsBig f L (m + 1)) {η : ℝ} (hη : 0 < η) :
    letI := E.isSeparated
    letI := E.quasiCompact
    ∃ k₀ : ℕ, 0 < k₀ ∧ ∀ k : ℕ, k₀ ≤ k →
      ∀ x ∈ twistedSectionValues f E Y hY k (SGPT.IGood.DXMain.twistAtlas aT a k),
        ((k : ℝ))⁻¹ • Counting.integerCast x ∈ thickening η (PartialBody.generalPartialBody
          (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) (H.curvature a)
          (thetaPshSupremum (H.curvature a).val)) := by
  let := E.isSeparated
  let := E.quasiCompact
  obtain ⟨δ, hδ, hsub⟩ := exists_tradOkounkovBody_subset_thickening f E Y hY a H hbig hη
  obtain ⟨k₀, hk₀, h⟩ := eventually_twistedSection_mem_tradOkounkovBody f E Y hY a H aT hδ
  refine ⟨k₀, hk₀, fun k hk x hx => ?_⟩
  obtain ⟨s, hs, rfl⟩ := hx
  have hcast : Counting.integerCast (fun i =>
      (schemeFubiniStudySectionVector f (m + 1) E Y hY (SGPT.IGood.DXMain.twistAtlas aT a k)
        1 s hs i : ℤ)) =
      fun i => (schemeFubiniStudySectionVector f (m + 1) E Y hY
        (SGPT.IGood.DXMain.twistAtlas aT a k) 1 s hs i : ℝ) := by
    funext i
    simp [Counting.integerCast]
  rw [hcast]
  exact hsub (h k hk s hs)

/-- The lattice set `{(ν(s), k) : k ≥ k₀, s ∈ H⁰(X, T ⊗ L^k) \ {0}}`. -/
def twistedAllValueSet (k₀ : ℕ) : Set ((Fin (m + 1) → ℤ) × ℤ) :=
  {z | ∃ k : ℕ, k₀ ≤ k ∧ z.2 = (k : ℤ) ∧
    z.1 ∈ twistedSectionValues f E Y hY k (SGPT.IGood.DXMain.twistAtlas aT a k)}

theorem slice_twistedAllValueSet {k₀ k : ℕ} (hk : k₀ ≤ k) :
    slice (twistedAllValueSet f E Y hY a aT k₀) (k : ℤ) =
      twistedSectionValues f E Y hY k (SGPT.IGood.DXMain.twistAtlas aT a k) := by
  ext x
  constructor
  · rintro ⟨k', -, hk', hx⟩
    have : k' = k := by
      have h' : (k' : ℤ) = (k : ℤ) := hk'.symm
      exact_mod_cast h'
    subst this
    exact hx
  · intro hx
    exact ⟨k, hk, rfl, hx⟩

include Y hY aT in
/-- **Source `prop:Deltaconvtwisted` for every twisting line bundle `T`** (flag valuations): for
a big line bundle `L`, the polytopes `Δ_{k,T}(L) = Conv {k⁻¹ ν(s) : s ∈ H⁰(X, T ⊗ L^k) \ {0}}`
(`def:DeltakT`, for any atlases `b_k` of `T ⊗ L^k`) converge in the Hausdorff metric to the
Okounkov body `Δ_{Y•}(L)` (`def:Okobd`). -/
theorem tendsto_hausdorffDist_twistedDegreePolytope [Nonempty (SchemeComplexPoint f)]
    (hbig : IsBig f L (m + 1))
    (b : ∀ k : ℕ, LineBundleAtlas (bundleTensor T (bundleTensorPower L k))) :
    Tendsto (fun k => hausdorffDist
        ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm ''
          twistedDegreePolytope f (m + 1) E Y hY k (b k))
        ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm '' lineBundleOkounkovBody f (m + 1) E Y hY a))
      atTop (𝓝 0) := by
  let := E.isSeparated
  let := E.quasiCompact
  -- an auxiliary smooth metric on `L`
  let H : SchemeLineBundleMetric f (m + 1) E L := schemeLineBundleMetric f (m + 1) E a
  set 𝔽 := schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY with h𝔽
  set θ := H.curvature a with hθ
  have hV := isThetaPshPotential_thetaPshSupremum_of_isBig f E a H hbig
  set K := PartialBody.generalPartialBody 𝔽 θ (thetaPshSupremum θ.val) with hKdef
  rw [SGPT.GAGA.H0L.lineBundleOkounkovBody_eq_generalPartialBody f E Y hY a H hbig]
  have hpos : 0 < volume.real K := volume_real_generalPartialBody_thetaPshSupremum_pos f E Y hY a H hbig hV
  obtain ⟨C₀, -, hC⟩ := exists_cubeCone_contains f E Y hY a H
  obtain ⟨-, hKC⟩ := hC C₀ le_rfl _ hV
  obtain ⟨-, hKC'⟩ := hC (C₀ + 1) (by linarith) _ hV
  obtain ⟨hKv, hKc⟩ := PartialBody.convex_isCompact_generalPartialBody (F := 𝔽) hV
  -- the cone subset of all twisted values
  obtain ⟨k₁, hk₁, h₁⟩ := eventually_twistedSectionValues_mem_thickening f E Y hY a H aT hbig one_pos
  have hsubA : twistedAllValueSet f E Y hY a aT k₁ ⊆
      (latticePoints (cubeCone (n := m + 1) (C₀ + 1)).cone : Set _) := by
    rintro ⟨x, z⟩ ⟨k, hk, hz, hx⟩
    simp only at hz hx
    subst hz
    have hx0 : ∀ i, 0 ≤ x i := by
      obtain ⟨s, hs, rfl⟩ := hx
      intro i
      positivity
    exact mem_latticePoints_cubeCone_of_mem_thickening hKC hx0 (lt_of_lt_of_le hk₁ hk) (h₁ k hk x hx)
  set S : ConeSubset (cubeCone (n := m + 1) (C₀ + 1)) := ⟨_, hsubA⟩ with hS
  -- the multiplier values at `V_θ`
  obtain ⟨k₂, -, hsubM, -⟩ := exists_twistedValueSet_subset f E Y hY a H aT hV hKC
  set SM := twistedConeSubset f E Y hY a aT hsubM with hSM
  have hup : ∀ η : ℝ, 0 < η → ∀ᶠ k : ℕ in atTop, ∀ x ∈ S.slices k,
      ((k : ℝ))⁻¹ • Counting.integerCast x ∈ cthickening η K := by
    intro η hη
    obtain ⟨k₃, -, h₃⟩ := eventually_twistedSectionValues_mem_thickening f E Y hY a H aT hbig hη
    filter_upwards [eventually_ge_atTop k₃, eventually_ge_atTop k₁] with k hk hk' x hx
    have hx' : x ∈ slice (twistedAllValueSet f E Y hY a aT k₁) (k : ℤ) :=
      (ConeSubset.mem_slices S k x).mp hx
    rw [slice_twistedAllValueSet f E Y hY a aT hk'] at hx'
    exact thickening_subset_cthickening _ _ (h₃ k hk x hx')
  have hlow : ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop, volume.real K - ε ≤ S.normalizedCardinality k := by
    intro ε hε
    filter_upwards [twistedConeSubset_lower f E Y hY a H aT hV hsubM hε, eventually_ge_atTop k₁,
      eventually_ge_atTop k₂] with k hk hk₁' hk₂'
    refine hk.trans ?_
    rw [ConeSubset.normalizedCardinality, ConeSubset.normalizedCardinality]
    gcongr
    intro x hx
    rw [ConeSubset.mem_slices] at hx ⊢
    have hx' : x ∈ slice (twistedValueSet f E Y hY a aT k₂ (thetaPshSupremum θ.val)) (k : ℤ) := hx
    rw [slice_twistedValueSet f E Y hY a aT hk₂'] at hx'
    have hx'' : x ∈ slice (twistedAllValueSet f E Y hY a aT k₁) (k : ℤ) := by
      rw [slice_twistedAllValueSet f E Y hY a aT hk₁']
      obtain ⟨s, hs, -, rfl⟩ := hx'
      exact ⟨s, hs, rfl⟩
    exact hx''
  have hfill := tendsto_hausdorffDist_of_fills (cubeCone (n := m + 1) (C₀ + 1)) hKc hKv hKC' S hpos
    hup hlow
  refine hfill.congr' ?_
  filter_upwards [eventually_ge_atTop k₁] with k hk
  congr 1
  unfold euclideanDegreePolytope
  rw [hS]
  change (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm '' convexHull ℝ
      ((fun x => ((k : ℝ))⁻¹ • Counting.integerCast x) ''
        slice (twistedAllValueSet f E Y hY a aT k₁) (k : ℤ)) = _
  rw [slice_twistedAllValueSet f E Y hY a aT hk,
    twistedSectionValues_atlas_independent f E Y hY k (SGPT.IGood.DXMain.twistAtlas aT a k) (b k)]
  rfl

/-! ### `thm:nuOk` for the algebraic partial Okounkov body -/

/-- **Source `thm:nuOk`** (smooth flags, the algebraic partial Okounkov body
`Δ_{Y•}(θ, φ) = Δ(Γ(θ, φ))` of `def:Okounkov:L687`): there is `C₀` such that for every cube cone
`C([0, C]ⁿ)`, `C ≥ C₀`, and every `φ ∈ PSH(X, θ)` with `vol θ_φ > 0`,
`ν(φ, Y₁) = min_{x ∈ Δ_{Y•}(θ, φ)} x₁` (`ν(φ, Y₁)` the generic Lelong number along `Y₁`). -/
theorem isLeast_firstCoordinate_partialOkounkovBody [Nonempty (SchemeComplexPoint f)] :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ C : ℝ, C₀ ≤ C → ∀ φ : SchemeComplexPoint f → EReal,
      (letI := E.isSeparated; letI := E.quasiCompact;
        IsThetaPshPotential (H.curvature a).val φ) →
      0 < volume.real (PartialBody.generalPartialBody
        (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) (H.curvature a) φ) →
      IsLeast ((fun x : EuclideanSpace ℝ (Fin (m + 1)) => x 0) ''
          partialOkounkovBody f (m + 1) E Y hY (cubeCone C) a φ)
        (SGPT.Okounkov.OkoLelong.firstFlagLelong f Y φ) := by
  obtain ⟨C₀, hC₀, hC⟩ := SGPT.GAGA.H0L.exists_partialOkounkovBody_eq f E Y hY a H
  refine ⟨C₀, hC₀, fun C hC' φ hφ hpos => ?_⟩
  let := E.isSeparated
  let := E.quasiCompact
  rw [hC C hC' φ hφ hpos, TranscendentalMain.euclideanImage, Set.image_image]
  exact SGPT.Okounkov.OkoLelong.isLeast_firstCoordinate_generalPartialBody
    (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) hφ

/-! ### `cor:transalgPOB`: the `ℚ`-class definition `eq:DeltanuTalgebraic1` -/

omit [IsIntegral X] [SmoothOfRelativeDimension (m + 1) f] in
/-- **Homogeneity of the partial Okounkov body of a current**: for rational `q > 0`,
`Δ_{Y•}(qθ + dd^c(qφ)) = q Δ_{Y•}(θ + dd^c φ)`. -/
theorem generalPartialBody_rat_smul {F : OriginalFlagGeometry (m + 1)}
    {θ : ClosedRealOneOneForm (m + 1) F.carrier} {φ : F.carrier → EReal}
    (hφ : IsThetaPshPotential θ.val φ) {q : ℚ} (hq : 0 < q) :
    PartialBody.generalPartialBody F ((q : ℝ) • θ) (fun x => ((q : ℝ) : EReal) * φ x) =
      (q : ℝ) • PartialBody.generalPartialBody F θ φ := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  refine Subset.antisymm ?_ (Valuative.smul_generalPartialBody_subset hφ hq)
  have hφq := isThetaPshPotential_nonneg_smul hφ hq'.le
  have h := Valuative.smul_generalPartialBody_subset hφq (inv_pos.mpr hq)
  have hθ : ((q⁻¹ : ℚ) : ℝ) • ((q : ℝ) • θ) = θ := by
    rw [smul_smul]
    push_cast
    rw [inv_mul_cancel₀ hq'.ne', one_smul]
  have hfun : (fun x => (((q⁻¹ : ℚ) : ℝ) : EReal) * (((q : ℝ) : EReal) * φ x)) = φ := by
    funext x
    have h1 : ((q⁻¹ : ℚ) : ℝ) * (q : ℝ) = 1 := by
      push_cast
      exact inv_mul_cancel₀ hq'.ne'
    rw [← mul_assoc, ← EReal.coe_mul, h1, EReal.coe_one, one_mul]
  rw [hθ, hfun] at h
  intro y hy
  refine ⟨((q : ℝ))⁻¹ • y, ?_, ?_⟩
  · have hy' := h ⟨y, hy, rfl⟩
    push_cast at hy'
    exact hy'
  · show (q : ℝ) • ((q : ℝ)⁻¹ • y) = y
    rw [smul_smul, mul_inv_cancel₀ hq'.ne', one_smul]

/-- **Source `cor:transalgPOB`, last sentence** ("the definition `eq:DeltanuTalgebraic1` is
compatible with `def:generalPOB`"): let `S = θ + dd^c φ` be a current (`φ ∈ PSH(X, θ)`,
`vol θ_φ > 0`) such that `aS` is a current in `c₁(L)` for a positive integer `a`
(`a θ = c₁(L, H)`, `aS = c₁(L, H) + dd^c(aφ)`). Then `a⁻¹ Δ_ν(aS) = Δ_{Y•}(S)`, where `Δ_ν(aS)` is
the algebraic partial Okounkov body of `(L, H e^{-aφ})` (`def:Okounkov:L687`, for all large cube
cones) and `Δ_{Y•}(S)` the partial Okounkov body of the current `S` (`def:generalPOB`). In
particular `a⁻¹ Δ_ν(aS)` does not depend on `a`. -/
theorem inv_smul_partialOkounkovBody_eq_generalPartialBody [Nonempty (SchemeComplexPoint f)] :
    letI := E.isSeparated
    letI := E.quasiCompact
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ C : ℝ, C₀ ≤ C → ∀ (q : ℕ), 0 < q →
      ∀ (θ : ClosedRealOneOneForm (m + 1) (SchemeComplexPoint f)) (φ : SchemeComplexPoint f → EReal),
      (q : ℝ) • θ = H.curvature a → IsThetaPshPotential θ.val φ →
      0 < volume.real (PartialBody.generalPartialBody
        (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) θ φ) →
      ((q : ℝ))⁻¹ • partialOkounkovBody f (m + 1) E Y hY (cubeCone C) a
          (fun x => ((q : ℝ) : EReal) * φ x) =
        TranscendentalMain.euclideanImage (PartialBody.generalPartialBody
          (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) θ φ) := by
  let := E.isSeparated
  let := E.quasiCompact
  obtain ⟨C₀, hC₀, hC⟩ := SGPT.GAGA.H0L.exists_partialOkounkovBody_eq f E Y hY a H
  refine ⟨C₀, hC₀, fun C hC' q hq θ φ hθ hφ hpos => ?_⟩
  have hqQ : (0 : ℚ) < q := by exact_mod_cast hq
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hcast : (((q : ℚ)) : ℝ) = (q : ℝ) := by push_cast; rfl
  have hφq : IsThetaPshPotential (H.curvature a).val (fun x => ((q : ℝ) : EReal) * φ x) := by
    rw [← hθ]
    exact isThetaPshPotential_nonneg_smul hφ hqR.le
  have hhom : PartialBody.generalPartialBody
      (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) (H.curvature a) (fun x => ((q : ℝ) : EReal) * φ x) =
      (q : ℝ) • PartialBody.generalPartialBody
      (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) θ φ := by
    have h := generalPartialBody_rat_smul (F := schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) hφ hqQ
    rw [hcast] at h
    rw [← hθ]
    exact h
  have hposq : 0 < volume.real (PartialBody.generalPartialBody
      (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) (H.curvature a)
      (fun x => ((q : ℝ) : EReal) * φ x)) := by
    rw [hhom, Measure.real, MeasureTheory.Measure.addHaar_smul, Module.finrank_fin_fun,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _)]
    exact mul_pos (abs_pos.mpr (pow_ne_zero _ hqR.ne')) hpos
  have key : ∀ K : Set (Fin (m + 1) → ℝ), ((q : ℝ))⁻¹ • TranscendentalMain.euclideanImage
      ((q : ℝ) • K) = TranscendentalMain.euclideanImage K := by
    intro K
    rw [TranscendentalMain.euclideanImage, TranscendentalMain.euclideanImage, ← Set.image_smul,
      Set.image_image, ← Set.image_smul, Set.image_image]
    congr 1
    funext x
    rw [map_smul, smul_smul, inv_mul_cancel₀ hqR.ne', one_smul]
  rw [hC C hC' _ hφq hposq]
  erw [hhom]
  exact key _

/-! ### `thm:Gammaasg` with the ambient cone `C(Δ_ν(L))` -/

omit [IsIntegral X] [SmoothOfRelativeDimension (m + 1) f] in
/-- **The cone over a compact convex set** `C(K) = {(t x, t) : t ≥ 0, x ∈ K}` as an admissible cone
(closed, in the upper half space, pointed at height `0`). -/
def coneOver {n : ℕ} (K : Set (Fin n → ℝ)) (hKc : IsCompact K) (hKv : Convex ℝ K) :
    AdmissibleCone n where
  cone :=
    { carrier := {z | 0 ≤ z.2 ∧ ∃ x ∈ K, z.1 = z.2 • x}
      smul_mem' := by
        rintro c hc z ⟨hz2, x, hx, hz1⟩
        refine ⟨by simpa using mul_nonneg hc.le hz2, x, hx, ?_⟩
        simp only [Prod.smul_fst, Prod.smul_snd, hz1, smul_smul, smul_eq_mul]
      add_mem' := by
        rintro z ⟨hz2, x, hx, hz1⟩ w ⟨hw2, y, hy, hw1⟩
        refine ⟨by simp only [Prod.snd_add]; positivity, ?_⟩
        simp only [Prod.fst_add, Prod.snd_add, hz1, hw1]
        rcases (add_nonneg hz2 hw2).lt_or_eq with hpos | hzero
        · refine ⟨(z.2 / (z.2 + w.2)) • x + (w.2 / (z.2 + w.2)) • y,
            hKv hx hy (div_nonneg hz2 hpos.le) (div_nonneg hw2 hpos.le) ?_, ?_⟩
          · rw [← add_div, div_self hpos.ne']
          · rw [smul_add, smul_smul, smul_smul, mul_div_cancel₀ _ hpos.ne',
              mul_div_cancel₀ _ hpos.ne']
        · have h1 : z.2 = 0 := by linarith
          have h2 : w.2 = 0 := by linarith
          exact ⟨x, hx, by rw [h1, h2, zero_smul, zero_smul, add_zero, zero_add, zero_smul]⟩ }
  closed := by
    apply IsSeqClosed.isClosed
    intro u z hu hlim
    choose hu2 x hx hu1 using hu
    have h2 : Tendsto (fun j => (u j).2) atTop (𝓝 z.2) := (continuous_snd.tendsto z).comp hlim
    obtain ⟨y, hy, φ, hφ, hxy⟩ := hKc.tendsto_subseq hx
    refine ⟨ge_of_tendsto' h2 hu2, y, hy, ?_⟩
    have h1 : Tendsto (fun j => (u (φ j)).1) atTop (𝓝 z.1) :=
      ((continuous_fst.tendsto z).comp hlim).comp hφ.tendsto_atTop
    have h1' : Tendsto (fun j => (u (φ j)).2 • x (φ j)) atTop (𝓝 (z.2 • y)) :=
      (h2.comp hφ.tendsto_atTop).smul hxy
    exact tendsto_nhds_unique (h1.congr fun j => hu1 (φ j)) h1'
  nonnegativeHeight := fun _ hz => hz.1
  zeroHeight := by
    rintro x ⟨-, y, -, hx⟩
    simpa using hx

omit [IsIntegral X] [SmoothOfRelativeDimension (m + 1) f] in
theorem heightOne_coneOver {n : ℕ} {K : Set (Fin n → ℝ)} (hKc : IsCompact K) (hKv : Convex ℝ K) :
    heightOne (coneOver K hKc hKv).cone = K := by
  ext x
  constructor
  · rintro ⟨-, y, hy, hxy⟩
    simp only [one_smul] at hxy
    exact hxy ▸ hy
  · intro hx
    exact ⟨zero_le_one, x, hx, by simp⟩

/-- **Source `thm:Gammaasg` with the book's ambient cone** (flag valuations): for a big line
bundle `L`, `Δ_ν(L)` is a convex body and for every `φ ∈ PSH(X, θ)` with `vol θ_φ > 0`,
`Γ(θ, φ) ⊆ C(Δ_ν(L))` and `Γ(θ, φ) ∈ 𝒮'(C(Δ_ν(L)))‾_{>0}` (the closure of the full semigroups of
the cone over `Δ_ν(L)`, with positive volume `vol Γ(θ, φ) = vol Δ_{Y•}(θ_φ) = vol θ_φ / n!`). -/
theorem multiplierConeSubset_mem_almostSemigroupLocus_coneOver [Nonempty (SchemeComplexPoint f)]
    (hbig : IsBig f L (m + 1)) :
    ∃ (hKc : IsCompact (lineBundleOkounkovBody f (m + 1) E Y hY a))
      (hKv : Convex ℝ (lineBundleOkounkovBody f (m + 1) E Y hY a)),
      ∀ φ : SchemeComplexPoint f → EReal,
      (letI := E.isSeparated; letI := E.quasiCompact;
        IsThetaPshPotential (H.curvature a).val φ) →
      0 < volume.real (PartialBody.generalPartialBody
        (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) (H.curvature a) φ) →
      ∃ hsub : multiplierSectionSet f (m + 1) E Y hY a φ ⊆
          (latticePoints (coneOver _ hKc hKv).cone : Set _),
        multiplierConeSubset f E Y hY a φ hsub ∈ almostSemigroupLocus (coneOver _ hKc hKv) ∧
          (multiplierConeSubset f E Y hY a φ hsub).volume =
            volume.real (PartialBody.generalPartialBody
              (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) (H.curvature a) φ) := by
  let := E.isSeparated
  let := E.quasiCompact
  have hV := isThetaPshPotential_thetaPshSupremum_of_isBig f E a H hbig
  have hKeq := SGPT.GAGA.H0L.lineBundleOkounkovBody_eq_generalPartialBody f E Y hY a H hbig
  obtain ⟨hKv, hKc⟩ := PartialBody.convex_isCompact_generalPartialBody
    (F := schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) hV
  rw [← hKeq] at hKv hKc
  refine ⟨hKc, hKv, fun φ hφ hpos => ?_⟩
  obtain ⟨C₀, -, hC⟩ := exists_cubeCone_contains f E Y hY a H
  obtain ⟨hsubC, -⟩ := hC C₀ le_rfl φ hφ
  obtain ⟨C₁, -, hC₁⟩ := SGPT.GAGA.H0L.partialOkounkovBody_subset_lineBundleOkounkovBody
    f E Y hY a H hbig
  obtain ⟨C₂, -, hC₂⟩ := SGPT.GAGA.H0L.exists_partialOkounkovBody_eq f E Y hY a H
  have hK1 := hC₁ (max C₁ C₂) (le_max_left _ _) φ hφ hpos
  rw [hC₂ (max C₁ C₂) (le_max_right _ _) φ hφ hpos] at hK1
  have hKsub : PartialBody.generalPartialBody (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY)
      (H.curvature a) φ ⊆ lineBundleOkounkovBody f (m + 1) E Y hY a := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hK1 ⟨x, hx, rfl⟩
    exact (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm.injective hxy ▸ hy
  obtain ⟨y₀, hy₀⟩ : (lineBundleOkounkovBody f (m + 1) E Y hY a).Nonempty := by
    obtain ⟨x, hx⟩ := MeasureTheory.nonempty_of_measure_ne_zero
      (ne_of_gt ((ENNReal.toReal_pos_iff.mp hpos).1))
    exact ⟨x, hKsub hx⟩
  have hsub : multiplierSectionSet f (m + 1) E Y hY a φ ⊆
      (latticePoints (coneOver _ hKc hKv).cone : Set _) := by
    rintro ⟨x, k⟩ hz
    have hzC := hsubC hz
    obtain ⟨k', s, hs, -, hzs⟩ := hz
    simp only [Prod.mk.injEq] at hzs
    obtain ⟨rfl, rfl⟩ := hzs
    change (0 : ℝ) ≤ ((k' : ℤ) : ℝ) ∧ ∃ y ∈ lineBundleOkounkovBody f (m + 1) E Y hY a,
      (fun i => (((schemeFubiniStudySectionVector f (m + 1) E Y hY a k' s hs i : ℕ) : ℤ) : ℝ)) =
        ((k' : ℤ) : ℝ) • y
    push_cast
    refine ⟨Nat.cast_nonneg _, ?_⟩
    rcases Nat.eq_zero_or_pos k' with hk0 | hkpos
    · -- degree zero: the cube cone forces `ν(s) = 0`
      subst hk0
      refine ⟨y₀, hy₀, ?_⟩
      funext i
      have hi := ((hzC.2 i).2)
      simp only [latticeCast, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Int.cast_natCast,
        Nat.cast_zero, Int.cast_zero, mul_zero] at hi
      simp only [Nat.cast_zero, zero_smul, Pi.zero_apply]
      exact le_antisymm hi (Nat.cast_nonneg _)
    · have hkR : (0 : ℝ) < k' := by exact_mod_cast hkpos
      refine ⟨((k' : ℝ))⁻¹ • (fun i => (schemeFubiniStudySectionVector f (m + 1) E Y hY a k' s hs i
        : ℝ)), ?_, ?_⟩
      · have hmem : ((fun i => (schemeFubiniStudySectionVector f (m + 1) E Y hY a k' s hs i : ℤ)),
            (k' : ℤ)) ∈ schemeProjectiveSectionSemigroup f (m + 1) E Y hY a := ⟨k', s, hs, rfl⟩
        have hc := SGPT.AlmostSemigroup.Okounkov.mem_closedCone_of_mem _ hmem
        have hc' := (SGPT.AlmostSemigroup.Okounkov.closedCone
          (schemeProjectiveSectionSemigroup f (m + 1) E Y hY a)).smul_mem
          (inv_pos.mpr hkR).le hc
        change ((k' : ℝ))⁻¹ • (fun i => (schemeFubiniStudySectionVector f (m + 1) E Y hY a k' s hs i
          : ℝ)) ∈ heightOne (SGPT.AlmostSemigroup.Okounkov.closedCone
            (schemeProjectiveSectionSemigroup f (m + 1) E Y hY a) : ConvexCone ℝ _)
        have hc'' : ((k' : ℝ))⁻¹ • latticeCast (m + 1)
            ((fun i => (schemeFubiniStudySectionVector f (m + 1) E Y hY a k' s hs i : ℤ)),
              (k' : ℤ)) ∈ (SGPT.AlmostSemigroup.Okounkov.closedCone
                (schemeProjectiveSectionSemigroup f (m + 1) E Y hY a) :
                  ConvexCone ℝ ((Fin (m + 1) → ℝ) × ℝ)) := hc'
        show (((k' : ℝ))⁻¹ • (fun i => (schemeFubiniStudySectionVector f (m + 1) E Y hY a k' s hs i
          : ℝ)), (1 : ℝ)) ∈ (SGPT.AlmostSemigroup.Okounkov.closedCone
            (schemeProjectiveSectionSemigroup f (m + 1) E Y hY a) :
              ConvexCone ℝ ((Fin (m + 1) → ℝ) × ℝ))
        convert hc'' using 1
        simp only [latticeCast, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Prod.smul_mk,
          Int.cast_natCast]
        refine Prod.ext ?_ ?_
        · funext i
          simp
        · simp [inv_mul_cancel₀ hkR.ne']
      · rw [smul_smul, mul_inv_cancel₀ hkR.ne', one_smul]
  refine ⟨hsub, ?_⟩
  obtain ⟨hKv', hKc'⟩ := PartialBody.convex_isCompact_generalPartialBody
    (F := schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) hφ
  have hKC : PartialBody.generalPartialBody (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY)
      (H.curvature a) φ ⊆ heightOne (coneOver _ hKc hKv).cone := by
    rw [heightOne_coneOver]
    exact hKsub
  exact mem_almostSemigroupLocus_of_fills _ hKc' hKv' hKC _ hpos
    (fun η hη => multiplierConeSubset_upper f E Y hY a H hφ hsub hη)
    (fun ε hε => multiplierConeSubset_lower f E Y hY a H hφ hsub
      (SGPT.GAGA.H0L.dxMainLowerBound_of_smoothFlag f E Y hY a H hφ) hε)

end SGPT.GAGA.OkoClose
