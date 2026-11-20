import SGPT.IGood.DXMainTwisted

/-!
# `thm:DXmain1` for an arbitrary twist `T`: the upper bound

Source `thm:DXmain1`: `limsup_{k → ∞} n! h⁰(X, T ⊗ L^k ⊗ 𝓘(kφ)) / kⁿ ≤ vol θ_φ` for every holomorphic
line bundle `T` (here: every line bundle with a rank-one atlas on the projective `X`, holomorphic
line bundles being algebraic by GAGA). Blueprint `claude-dxmain:twisted`.

* `limsup_le_iVolume_of_latticeCount`: the counting and volume part of the upper bound, for any
  sequence `h_k` that is eventually bounded by the lattice counts of the scaled DRWNXZ bodies
  `(1 - q) Δ(θ + ε ω; ψ)` (`ψ` an analytic Kähler approximant of `φ`).
* **`limsup_twistedMultiplierH0_le`**: the twisted upper bound.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.IGood.DXMain

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set Filter MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Okounkov SGPT.LineBundle SGPT.PSH
open SGPT.Okounkov.TranscendentalCore SGPT.Okounkov.TranscendentalPartial
open scoped Topology ENNReal NNReal Pointwise

variable {X : Scheme} (f : X ⟶ Spec (.of ℂ)) (E : ClosedProjectiveEmbedding f)
  [IsIntegral X] {m : ℕ} [SmoothOfRelativeDimension (m + 1) f]

local instance dxTwUTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance dxTwUCharts : ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (m + 1)
local instance dxTwUManifold [IsSeparated f] [QuasiCompact f] :
    IsComplexManifold (m + 1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (m + 1)

variable (Y : Fin (m + 1 + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y)
  {L : X.Modules} (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f (m + 1) E L)

omit [IsIntegral X] in
/-- **The counting part of the Okounkov upper bound**: if a sequence `h_k` is, for every analytic
Kähler approximant `ψ` of `φ` in `θ + ε ω` and every admissible rational `q`, eventually bounded by
the number of lattice points of `k (1 - q) Δ(θ + ε ω; ψ)`, then
`limsup n! h_k / kⁿ ≤ vol θ_φ`. -/
theorem limsup_le_iVolume_of_latticeCount {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val φ) (h : ℕ → ℕ)
    (hcount : letI := E.isSeparated; letI := E.quasiCompact;
      ∀ (ε : ℝ) (ψ : SchemeComplexPoint f → EReal), 0 < ε →
        ψ ∈ globalAnalyticCurrents (H.curvature a +
          ε • (schemeProjectiveTNKahlerBackground f (m + 1) E).form) →
        SingularityLE φ ψ → ∀ C : ℝ, 0 ≤ C →
        (-(H.curvature a + (ε / 2) • (schemeProjectiveTNKahlerBackground f (m + 1) E).form) +
          C • (schemeProjectiveTNKahlerBackground f (m + 1) E).form).val.IsSemipositive →
        ∀ q : ℚ, 0 < q → q ≤ 1 / 2 → 2 * (q : ℝ) * C ≤ ε / 2 →
        ∀ᶠ k in atTop, h k ≤ SGPT.AlmostSemigroup.Counting.integerLatticeCount
          ((1 - (q : ℝ)) • partialOkounkovBody (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY)
            (H.curvature a + ε • (schemeProjectiveTNKahlerBackground f (m + 1) E).form) ψ) k) :
    letI := E.isSeparated
    letI := E.quasiCompact
    letI : MeasurableSpace (SchemeComplexPoint f) := borel _
    haveI : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
    haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    haveI : Nonempty (SchemeComplexPoint f) :=
      PartialBody.nonempty_carrier (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY)
    limsup (fun k : ℕ => (((m + 1).factorial : ℝ≥0∞) * (h k : ℝ≥0∞)) /
          (k : ℝ≥0∞) ^ (m + 1)) atTop ≤
      iVolume (H.curvature a) (LocalPotentials.closedRealOneOne_hasLocalPotentials _) φ hφ := by
  let := E.isSeparated
  let := E.quasiCompact
  let : MeasurableSpace (SchemeComplexPoint f) := borel _
  have : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  set 𝔽 := schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY with h𝔽
  have : Nonempty (SchemeComplexPoint f) := PartialBody.nonempty_carrier 𝔽
  set ω := schemeProjectiveTNKahlerBackground f (m + 1) E with hω
  set θ := H.curvature a with hθ
  set u : ℕ → ℝ≥0∞ := fun k => (((m + 1).factorial : ℝ≥0∞) * (h k : ℝ≥0∞)) /
    (k : ℝ≥0∞) ^ (m + 1) with hu
  set N : ℝ≥0∞ := ((m + 1).factorial : ℝ≥0∞) with hN
  have hN0 : N ≠ 0 := by
    rw [hN]
    exact_mod_cast (Nat.factorial_pos (m + 1)).ne'
  have hNtop : N ≠ ⊤ := ENNReal.natCast_ne_top _
  set V := volume (PartialBody.generalPartialBody 𝔽 θ φ) with hVdef
  have hV : V = iVolume θ (LocalPotentials.closedRealOneOne_hasLocalPotentials θ) φ hφ / N :=
    PartialBody.volume_generalPartialBody_uncond (F := 𝔽) hφ
  have key : ∀ η : ℝ≥0∞, 0 < η → limsup u atTop ≤ N * (V + η) := by
    intro η hη
    obtain ⟨ε, ψ, hε, hψ, -, hle, hvol⟩ := exists_approximant (F := 𝔽) hφ hη
    obtain ⟨C, hC, hCsemi⟩ :=
      KahlerDomination.exists_pos_isSemipositive_add_smul ω (-(θ + (ε / 2) • ω.form))
    have hpos : (0 : ℝ) < min (1 / 2) (ε / (4 * C)) := lt_min (by norm_num) (by positivity)
    obtain ⟨q, hq0, hqlt⟩ := exists_pos_rat_lt hpos
    have hq1 : q ≤ 1 / 2 := by
      have h' : (q : ℝ) ≤ 1 / 2 := hqlt.le.trans (min_le_left _ _)
      exact (Rat.cast_le (K := ℝ)).mp (by push_cast; exact h')
    have hqC : 2 * (q : ℝ) * C ≤ ε / 2 := by
      have h' : (q : ℝ) ≤ ε / (4 * C) := hqlt.le.trans (min_le_right _ _)
      rw [le_div_iff₀ (by positivity)] at h'
      linarith
    have hev0 := hcount ε ψ hε hψ hle C hC.le hCsemi q hq0 hq1 hqC
    set P := partialOkounkovBody 𝔽 (θ + ε • ω.form) ψ with hP
    set K : Set (Fin (m + 1) → ℝ) := (1 - (q : ℝ)) • P with hK
    have hKc : IsCompact K := (isCompact_partialOkounkovBody _ _).smul _
    have hKconv : Convex ℝ K := (convex_partialOkounkovBody _ _).smul _
    have hq1R : (q : ℝ) ≤ 1 / 2 := by
      have h' := (Rat.cast_le (K := ℝ)).mpr hq1
      push_cast at h'
      exact h'
    have hq0R : (0 : ℝ) < q := by exact_mod_cast hq0
    have hvolK : volume K ≤ V + η := by
      rw [hK, MeasureTheory.Measure.addHaar_smul, Module.finrank_fin_fun]
      calc ENNReal.ofReal |(1 - (q : ℝ)) ^ (m + 1)| * volume P ≤ 1 * volume P := by
            gcongr
            rw [ENNReal.ofReal_le_one, abs_of_nonneg (pow_nonneg (by linarith) _)]
            exact pow_le_one₀ (by linarith) (by linarith)
        _ = volume P := one_mul _
        _ ≤ V + η := hvol
    have hev : ∀ᶠ k in atTop, u k ≤ N * ENNReal.ofReal ((k : ℝ)⁻¹ ^ (m + 1) *
        (SGPT.AlmostSemigroup.Counting.integerLatticeCount K k : ℝ)) := by
      filter_upwards [hev0, eventually_gt_atTop 0] with k hcnt hkpos
      have hkR : (0 : ℝ) < k := by exact_mod_cast hkpos
      rw [hu]
      dsimp only
      rw [mul_div_assoc]
      gcongr
      have hpow : ((k : ℝ≥0∞) ^ (m + 1)) = ENNReal.ofReal ((k : ℝ) ^ (m + 1)) := by
        rw [ENNReal.ofReal_pow (Nat.cast_nonneg k), ENNReal.ofReal_natCast]
      have hcnt' : (h k : ℝ≥0∞) ≤
          ENNReal.ofReal (SGPT.AlmostSemigroup.Counting.integerLatticeCount K k : ℝ) := by
        rw [ENNReal.ofReal_natCast]
        exact_mod_cast hcnt
      calc (h k : ℝ≥0∞) / (k : ℝ≥0∞) ^ (m + 1)
          ≤ ENNReal.ofReal (SGPT.AlmostSemigroup.Counting.integerLatticeCount K k : ℝ) /
              ENNReal.ofReal ((k : ℝ) ^ (m + 1)) := by
            rw [hpow]
            exact ENNReal.div_le_div_right hcnt' _
        _ = ENNReal.ofReal ((k : ℝ)⁻¹ ^ (m + 1) *
              (SGPT.AlmostSemigroup.Counting.integerLatticeCount K k : ℝ)) := by
            rw [← ENNReal.ofReal_div_of_pos (pow_pos hkR _), inv_pow, div_eq_inv_mul]
    have hlim := ENNReal.Tendsto.const_mul (a := N)
      (ENNReal.tendsto_ofReal (SGPT.AlmostSemigroup.Counting.tendsto_integer_lattice_count hKc hKconv))
      (Or.inr hNtop)
    calc limsup u atTop ≤ limsup (fun k : ℕ => N * ENNReal.ofReal ((k : ℝ)⁻¹ ^ (m + 1) *
          (SGPT.AlmostSemigroup.Counting.integerLatticeCount K k : ℝ))) atTop :=
          Filter.limsup_le_limsup hev
      _ = N * ENNReal.ofReal (volume.real K) := hlim.limsup_eq
      _ = N * volume K := by
          rw [measureReal_def, ENNReal.ofReal_toReal hKc.measure_lt_top.ne]
      _ ≤ N * (V + η) := by gcongr
  have hfinal : limsup u atTop ≤ N * V := by
    refine ENNReal.le_of_forall_pos_le_add fun δ hδ _ => ?_
    have hδ' : (0 : ℝ≥0∞) < (δ : ℝ≥0∞) / N :=
      ENNReal.div_pos (by exact_mod_cast hδ.ne') hNtop
    calc limsup u atTop ≤ N * (V + (δ : ℝ≥0∞) / N) := key _ hδ'
      _ = N * V + (δ : ℝ≥0∞) := by rw [mul_add, ENNReal.mul_div_cancel hN0 hNtop]
  calc limsup u atTop ≤ N * V := hfinal
    _ = iVolume θ (LocalPotentials.closedRealOneOne_hasLocalPotentials θ) φ hφ := by
        rw [hV, ENNReal.mul_div_cancel hN0 hNtop]

/-- **Source `thm:DXmain1`, the upper bound, for every twist `T`** (blueprint
`claude-dxmain:twisted`): on an integral smooth projective complex scheme of dimension
`n = m + 1` carrying a smooth flag, for line bundles `T`, `L` (with atlases), a smooth metric `H`
on `L` (`θ = c₁(L, H)`) and `φ ∈ PSH(X, θ)`,
`limsup_{k → ∞} n! h⁰(X, T ⊗ L^k ⊗ 𝓘(kφ)) / kⁿ ≤ vol θ_φ`. -/
theorem limsup_twistedMultiplierH0_le {T : X.Modules} (aT : LineBundleAtlas T)
    {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val φ) :
    letI := E.isSeparated
    letI := E.quasiCompact
    letI : MeasurableSpace (SchemeComplexPoint f) := borel _
    haveI : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
    haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    haveI : Nonempty (SchemeComplexPoint f) :=
      PartialBody.nonempty_carrier (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY)
    limsup (fun k : ℕ => (((m + 1).factorial : ℝ≥0∞) *
        (twistedMultiplierH0 f (m + 1) E hφ.1.quasiPlurisubharmonic T L k : ℝ≥0∞)) /
          (k : ℝ≥0∞) ^ (m + 1)) atTop ≤
      iVolume (H.curvature a) (LocalPotentials.closedRealOneOne_hasLocalPotentials _) φ hφ := by
  let := E.isSeparated
  let := E.quasiCompact
  refine limsup_le_iVolume_of_latticeCount f E Y hY a H hφ _ ?_
  intro ε ψ hε hψ hle C hC0 hC q hq0 hq1 hqC
  obtain ⟨k₀, hk₀, hcont⟩ := eventually_twisted_mem_smul_partialOkounkovBody f E Y hY aT a H
    hε hψ hle hC0 hC hq0 hq1 hqC
  have hKc : IsCompact ((1 - (q : ℝ)) • partialOkounkovBody
      (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY)
      (H.curvature a + ε • (schemeProjectiveTNKahlerBackground f (m + 1) E).form) ψ) :=
    (isCompact_partialOkounkovBody _ _).smul _
  filter_upwards [eventually_ge_atTop k₀] with k hk
  have hkpos : 0 < k := lt_of_lt_of_le hk₀ hk
  exact finrank_le_integerLatticeCount f (m + 1) E Y hY (twistAtlas aT a k)
    (twistedMultiplierSubmodule f (m + 1) E hφ.1.quasiPlurisubharmonic T L k) hKc hkpos
    (fun s hs hsV => hcont k hk s hs hsV)

/-! ### The statement of `thm:DXmain1` with a twist -/

/-- The normalized dimensions `n! h⁰(X, T ⊗ L^k ⊗ 𝓘(kφ)) / kⁿ`. -/
def normalizedTwistedH0 (T : X.Modules) {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val φ) (k : ℕ) : ℝ≥0∞ :=
  letI := E.isSeparated
  letI := E.quasiCompact
  (((m + 1).factorial : ℝ≥0∞) *
    (twistedMultiplierH0 f (m + 1) E hφ.1.quasiPlurisubharmonic T L k : ℝ≥0∞)) /
      (k : ℝ≥0∞) ^ (m + 1)

/-- **The conclusion of `thm:DXmain1`** for `(X, T, L, H, φ)`:
`lim_k n! h⁰(X, T ⊗ L^k ⊗ 𝓘(kφ)) / kⁿ = vol θ_φ`. -/
def DXMain1TwistedHolds [Nonempty (SchemeComplexPoint f)] (T : X.Modules)
    {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val φ) : Prop :=
  letI := E.isSeparated
  letI := E.quasiCompact
  letI : MeasurableSpace (SchemeComplexPoint f) := borel _
  haveI : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
  haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  Tendsto (normalizedTwistedH0 f E a H T hφ) atTop
    (𝓝 (iVolume (H.curvature a) (LocalPotentials.closedRealOneOne_hasLocalPotentials _) φ hφ))

/-- **The lower bound of `thm:DXmain1`** with a twist (open). -/
def DXMainTwistedLowerBound [Nonempty (SchemeComplexPoint f)] (T : X.Modules)
    {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val φ) : Prop :=
  letI := E.isSeparated
  letI := E.quasiCompact
  letI : MeasurableSpace (SchemeComplexPoint f) := borel _
  haveI : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
  haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  iVolume (H.curvature a) (LocalPotentials.closedRealOneOne_hasLocalPotentials _) φ hφ ≤
    liminf (normalizedTwistedH0 f E a H T hφ) atTop

include Y hY in
/-- **`thm:DXmain1` (twisted) follows from its lower bound** on `X` carrying a smooth flag. -/
theorem dxMain1TwistedHolds_of_lowerBound [Nonempty (SchemeComplexPoint f)] {T : X.Modules}
    (aT : LineBundleAtlas T) {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val φ)
    (hlow : DXMainTwistedLowerBound f E a H T hφ) : DXMain1TwistedHolds f E a H T hφ :=
  tendsto_of_le_liminf_of_limsup_le hlow (limsup_twistedMultiplierH0_le f E Y hY a H aT hφ)

include Y hY in
/-- **`thm:DXmain1` (twisted) for currents of zero volume**. -/
theorem dxMain1TwistedHolds_of_iVolume_eq_zero [Nonempty (SchemeComplexPoint f)] {T : X.Modules}
    (aT : LineBundleAtlas T) {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val φ)
    (h0 : letI := E.isSeparated; letI := E.quasiCompact;
      letI : MeasurableSpace (SchemeComplexPoint f) := borel _;
      haveI : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩;
      haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact;
      iVolume (H.curvature a) (LocalPotentials.closedRealOneOne_hasLocalPotentials _) φ hφ = 0) :
    DXMain1TwistedHolds f E a H T hφ := by
  refine dxMain1TwistedHolds_of_lowerBound f E Y hY a H aT hφ ?_
  unfold DXMainTwistedLowerBound
  rw [h0]
  exact zero_le

/-- **Source `thm:DXmain1`, projective setting** (statement only): for every integral smooth
projective complex scheme `X` of positive dimension, all line bundles `T`, `L`, every smooth
Hermitian metric `H` on `L` and every `φ ∈ PSH(X, c₁(L, H))`,
`lim_k n! h⁰(X, T ⊗ L^k ⊗ 𝓘(kφ)) / kⁿ = vol θ_φ`. Upper bound: `limsup_twistedMultiplierH0_le`
(for `X` with a smooth flag); lower bound open. -/
def DXMain1Statement : Prop :=
  ∀ (X : Scheme.{0}) (f : X ⟶ Spec (.of ℂ)) (E : ClosedProjectiveEmbedding f) [IsIntegral X]
    (m : ℕ) [SmoothOfRelativeDimension (m + 1) f] [Nonempty (SchemeComplexPoint f)]
    (T L : X.Modules) (_ : LineBundleAtlas T) (a : LineBundleAtlas L)
    (H : SchemeLineBundleMetric f (m + 1) E L) (φ : SchemeComplexPoint f → EReal)
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val φ),
    DXMain1TwistedHolds f E a H T hφ

end SGPT.IGood.DXMain
