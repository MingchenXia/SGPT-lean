import SGPT.Foundations.Analysis.Pending.MixedNonPluripolar

/-!
# Dinew's inequality against a common measure: the coordinate statements

Xia, *Foundations of pluripotential theory* (FPT), `thm:bounded-multifactor-common-measure`:
let `Ω ⊆ ℂⁿ` be open, `n ≥ 1`, `u₁, …, uₙ` locally bounded plurisubharmonic on `Ω`, `μ` a
positive Radon measure on `Ω` and `f₁, …, fₙ ≥ 0` Borel functions with `(ddᶜuᵢ)ⁿ ≥ fᵢ μ`. Then
`ddᶜu₁ ∧ ⋯ ∧ ddᶜuₙ ≥ (∏ᵢ fᵢ^{1/n}) μ`.

* `BoundedMultifactorCommonMeasure n` is this statement, for the bounded mixed Bedford–Taylor
  measure of TN (`canonicalMixedBedfordTaylorMeasure`, the vague limit of the smooth mixed
  Monge–Ampère measures along decreasing smooth approximations). It is a **statement**: its
  proof in FPT needs the Dirichlet problem `(ddᶜU)ⁿ = α` on balls for compactly supported
  measures dominated by Monge–Ampère measures of bounded functions (Kołodziej), the canonical
  cube-average approximants, their convergence in capacity with bounded energies, and the
  continuity of mixed products along such sequences, none of which is available in the project.
  The densities take values in `[0, ∞]` (values `∞` can only occur on a `μ`-null set, because the
  Bedford–Taylor measures are finite on compact subsets of `Ω`).
* `boundedMultifactorCommonMeasure_one`: for `n = 1` the assertion is the hypothesis.
* `mixedTruncationLimitMeasure_ge_withDensity_prod`: the coordinate form of FPT
  `prop:nonpluripolar-multifactor-common-measure`, for arbitrary (possibly unbounded,
  extended-real) plurisubharmonic `uᵢ` and TN's non-pluripolar products
  (`mixedTruncationLimitMeasure`), deduced from `BoundedMultifactorCommonMeasure n` by FPT's
  argument: on the common strict locus `Gⱼ = ⋂ᵢ {uᵢ > -j}` the truncated bounded products agree
  with the non-pluripolar ones (plurifine locality of the truncations), the bounded inequality
  applies to the densities `𝟙_{Gⱼ} fᵢ`, and `fᵢ = 0` `μ`-almost everywhere on the pole set of
  `uᵢ` (the non-pluripolar product of `uᵢ` does not charge it), so the product density vanishes
  `μ`-almost everywhere off `⋃ⱼ Gⱼ`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal

namespace SGPT.Envelopes.DinewMeasure

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere SGPT.Foundations.Analysis.FirstPass.MixedMongeAmpere
open SGPT.Foundations.Analysis.FirstPass.MixedNonPluripolar
open SGPT.Foundations.Analysis.Pending.MixedMongeAmpere SGPT.Foundations.Analysis.Pending.MixedNonPluripolar

variable {n : ℕ}

/-- **Dinew's inequality for bounded plurisubharmonic functions against a common measure**
(statement of Xia, *Foundations of pluripotential theory*, `thm:bounded-multifactor-common-measure`):
for `n ≥ 1`, an open `Ω ⊆ ℂⁿ`, locally bounded plurisubharmonic `u₁, …, uₙ` on `Ω`, a measure `μ`
finite on compact subsets of `Ω` (a positive Radon measure on `Ω`) and measurable `fᵢ ≥ 0` with
`(ddᶜuᵢ)ⁿ ≥ fᵢ μ` on `Ω`, the mixed Bedford–Taylor measure satisfies
`ddᶜu₁ ∧ ⋯ ∧ ddᶜuₙ ≥ (∏ᵢ fᵢ^{1/n}) μ` on `Ω`. -/
def BoundedMultifactorCommonMeasure (n : ℕ) : Prop :=
  0 < n → ∀ (Ω : Opens (ComplexModel n)) (u : Fin n → ComplexModel n → ℝ)
    (hu : IsLocallyBoundedMixedPshOn Ω u) (μ : Measure (ComplexModel n)),
    (∀ K : Set (ComplexModel n), IsCompact K → K ⊆ Ω → μ K < ∞) →
    ∀ f : Fin n → ComplexModel n → ℝ≥0∞, (∀ i, Measurable (f i)) →
    (∀ i, (μ.withDensity (f i)).restrict Ω ≤
        canonicalMixedBedfordTaylorMeasure Ω (fun _ => u i) (fun _ => hu i)) →
    (μ.withDensity (fun z => ∏ i, f i z ^ ((n : ℝ)⁻¹))).restrict Ω ≤
      canonicalMixedBedfordTaylorMeasure Ω u hu

theorem canonicalMixedBedfordTaylorMeasure_congr {Ω : Opens (ComplexModel n)}
    {u v : Fin n → ComplexModel n → ℝ} (h : u = v) (hu : IsLocallyBoundedMixedPshOn Ω u)
    (hv : IsLocallyBoundedMixedPshOn Ω v) :
    canonicalMixedBedfordTaylorMeasure Ω u hu = canonicalMixedBedfordTaylorMeasure Ω v hv := by
  subst h
  rfl

/-- In dimension `1` the inequality is the hypothesis (FPT: "For `n = 1` the assertion is the
hypothesis"). -/
theorem boundedMultifactorCommonMeasure_one : BoundedMultifactorCommonMeasure 1 := by
  intro _ Ω u hu μ _ f _ h
  have hu0 : u = fun _ => u 0 := funext fun i => by rw [Subsingleton.elim i 0]
  have hdens : (fun z => ∏ i : Fin 1, f i z ^ (((1 : ℕ) : ℝ)⁻¹)) = f 0 := by
    funext z
    simp
  rw [hdens, canonicalMixedBedfordTaylorMeasure_congr hu0 hu (fun _ => hu 0)]
  exact h 0

/-- For `n > 0`, the product of the `n`-th roots vanishes as soon as one factor vanishes. -/
theorem prod_rpow_inv_eq_zero (hn : 0 < n) {a : Fin n → ℝ≥0∞} {i : Fin n} (hi : a i = 0) :
    ∏ j, a j ^ ((n : ℝ)⁻¹) = 0 :=
  Finset.prod_eq_zero (Finset.mem_univ i) (by
    rw [hi, ENNReal.zero_rpow_of_pos (inv_pos.mpr (Nat.cast_pos.mpr hn))])

/-- Products of `n`-th roots commute with indicators. -/
theorem prod_rpow_inv_indicator (hn : 0 < n) (G : Set (ComplexModel n))
    (f : Fin n → ComplexModel n → ℝ≥0∞) (z : ComplexModel n) :
    ∏ i, (G.indicator (f i) z) ^ ((n : ℝ)⁻¹) = G.indicator (fun z => ∏ i, f i z ^ ((n : ℝ)⁻¹)) z := by
  by_cases hz : z ∈ G
  · simp only [indicator_of_mem hz]
  · rw [indicator_of_notMem hz]
    exact prod_rpow_inv_eq_zero (i := ⟨0, hn⟩) hn (indicator_of_notMem hz _)

/-- The diagonal common strict locus of one component contains the common strict locus of the
whole tuple. -/
theorem commonStrictLocus_subset_diagonal {Ω : Opens (ComplexModel n)}
    (u : Fin n → ComplexModel n → EReal) (k : ℕ) (i : Fin n) :
    commonStrictLocus Ω u k ⊆ commonStrictLocus Ω (fun _ => u i) k :=
  fun _ hz => ⟨hz.1, fun _ => hz.2 i⟩

/-- `μ.withDensity (𝟙_G f)` restricted to `Ω ⊇ G` is `(μ.withDensity f).restrict G`. -/
theorem withDensity_indicator_restrict {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {G Ω : Set X} (hG : MeasurableSet G) (hGΩ : G ⊆ Ω) (f : X → ℝ≥0∞) :
    (μ.withDensity (G.indicator f)).restrict Ω = (μ.withDensity f).restrict G := by
  rw [withDensity_indicator hG, ← restrict_withDensity hG, Measure.restrict_restrict' hG,
    inter_eq_right.mpr hGΩ]

/-- **Dinew's inequality for non-pluripolar products against a common measure, in
coordinates** (FPT `prop:nonpluripolar-multifactor-common-measure` on an open set of `ℂⁿ`,
conditional on the bounded case `BoundedMultifactorCommonMeasure n`): for plurisubharmonic
`u₁, …, uₙ` on `Ω` (possibly unbounded), a measure `μ` finite on compact subsets of `Ω` and
measurable `fᵢ ≥ 0` with `⟨(ddᶜuᵢ)ⁿ⟩ ≥ fᵢ μ` on `Ω`,
`⟨ddᶜu₁ ∧ ⋯ ∧ ddᶜuₙ⟩ ≥ (∏ᵢ fᵢ^{1/n}) μ` on `Ω`. -/
theorem mixedTruncationLimitMeasure_ge_withDensity_prod (hB : BoundedMultifactorCommonMeasure n)
    (hn : 0 < n) {Ω : Opens (ComplexModel n)} {u : Fin n → ComplexModel n → EReal}
    (hu : ∀ i, PlurisubharmonicOn (u i) Ω) (μ : Measure (ComplexModel n))
    (hμ : ∀ K : Set (ComplexModel n), IsCompact K → K ⊆ Ω → μ K < ∞)
    (f : Fin n → ComplexModel n → ℝ≥0∞) (hf : ∀ i, Measurable (f i))
    (h : ∀ i, (μ.withDensity (f i)).restrict Ω ≤
      mixedTruncationLimitMeasure Ω (fun _ => u i) (fun _ => hu i)) :
    (μ.withDensity (fun z => ∏ i, f i z ^ ((n : ℝ)⁻¹))).restrict Ω ≤
      mixedTruncationLimitMeasure Ω u hu := by
  set Pd : ComplexModel n → ℝ≥0∞ := fun z => ∏ i, f i z ^ ((n : ℝ)⁻¹) with hPd
  set G : ℕ → Set (ComplexModel n) := commonStrictLocus Ω u with hG
  have hGm : ∀ k, MeasurableSet (G k) := measurableSet_commonStrictLocus hu
  have hGΩ : ∀ k, G k ⊆ Ω := fun k => commonStrictLocus_subset k
  have hΩm : MeasurableSet (Ω : Set (ComplexModel n)) := Ω.isOpen.measurableSet
  -- Step 1: the truncated bounded functions keep the lower bounds `𝟙_{G k} fᵢ μ`
  have hstep1 : ∀ k i, (μ.withDensity ((G k).indicator (f i))).restrict Ω ≤
      canonicalMixedBedfordTaylorMeasure Ω (fun _ => mixedTruncationReal u k i)
        (fun _ => mixedTruncationReal_isLocallyBounded hu k i) := by
    intro k i
    have hsub : G k ⊆ commonStrictLocus Ω (fun _ => u i) k :=
      commonStrictLocus_subset_diagonal u k i
    rw [withDensity_indicator_restrict μ (hGm k) (hGΩ k)]
    calc (μ.withDensity (f i)).restrict (G k)
        = ((μ.withDensity (f i)).restrict Ω).restrict (G k) :=
          (Measure.restrict_restrict_of_subset (hGΩ k)).symm
      _ ≤ (mixedTruncationLimitMeasure Ω (fun _ => u i) (fun _ => hu i)).restrict (G k) :=
          Measure.restrict_mono subset_rfl (h i)
      _ = ((mixedTruncationLimitMeasure Ω (fun _ => u i) (fun _ => hu i)).restrict
            (commonStrictLocus Ω (fun _ => u i) k)).restrict (G k) :=
          (Measure.restrict_restrict_of_subset hsub).symm
      _ = (mixedTruncationMeasure Ω (fun _ => u i) (fun _ => hu i) k).restrict (G k) := by
          rw [mixedTruncationLimitMeasure_restrict_commonStrictLocus]
      _ = (canonicalMixedBedfordTaylorMeasure Ω (fun _ => mixedTruncationReal u k i)
            (fun _ => mixedTruncationReal_isLocallyBounded hu k i)).restrict (G k) := by
          rw [mixedTruncationMeasure, Measure.restrict_restrict_of_subset hsub]
          rfl
      _ ≤ _ := Measure.restrict_le_self
  -- Step 2: the bounded inequality on each `G k`
  have hstep2 : ∀ k, (μ.withDensity Pd).restrict (G k) ≤ mixedTruncationLimitMeasure Ω u hu := by
    intro k
    have hb := hB hn Ω (mixedTruncationReal u k) (mixedTruncationReal_isLocallyBounded hu k) μ hμ
      (fun i => (G k).indicator (f i)) (fun i => (hf i).indicator (hGm k)) (hstep1 k)
    have hdens : (fun z => ∏ i, (G k).indicator (f i) z ^ ((n : ℝ)⁻¹)) = (G k).indicator Pd :=
      funext fun z => prod_rpow_inv_indicator hn (G k) f z
    rw [hdens, withDensity_indicator_restrict μ (hGm k) (hGΩ k)] at hb
    calc (μ.withDensity Pd).restrict (G k) = ((μ.withDensity Pd).restrict (G k)).restrict (G k) :=
          (Measure.restrict_restrict_of_subset subset_rfl).symm
      _ ≤ (canonicalMixedBedfordTaylorMeasure Ω (mixedTruncationReal u k)
            (mixedTruncationReal_isLocallyBounded hu k)).restrict (G k) :=
          Measure.restrict_mono subset_rfl hb
      _ = mixedTruncationMeasure Ω u hu k := rfl
      _ ≤ _ := mixedTruncationMeasure_le_limit hu k
  -- Step 3: the product density vanishes `μ`-a.e. on the pole sets
  have hpole : ∀ i, (μ.withDensity Pd) ((Ω : Set (ComplexModel n)) ∩
      componentPoleSet (fun _ : Fin n => u i)) = 0 := by
    intro i
    set E : Set (ComplexModel n) := (Ω : Set (ComplexModel n)) ∩
      componentPoleSet (fun _ : Fin n => u i) with hE
    have hEm : MeasurableSet E := by
      have : E = (Ω : Set (ComplexModel n)) \ ⋃ k, commonStrictLocus Ω (fun _ => u i) k := by
        rw [sdiff_eq, compl_iUnion_commonStrictLocus, hE]
        ext z
        simp only [mem_inter_iff, mem_union, mem_compl_iff]
        tauto
      rw [this]
      exact hΩm.diff (MeasurableSet.iUnion fun k =>
        measurableSet_commonStrictLocus (fun _ => hu i) k)
    have hfE : (μ.withDensity (f i)) E = 0 := by
      have h1 := h i E
      rw [Measure.restrict_apply hEm, inter_eq_left.mpr inter_subset_left] at h1
      refine le_antisymm (h1.trans ?_) zero_le
      exact (measure_mono inter_subset_right).trans
        (mixedTruncationLimitMeasure_poleSet (fun _ => hu i)).le
    rw [withDensity_apply _ hEm, lintegral_eq_zero_iff (hf i)] at hfE
    rw [withDensity_apply _ hEm]
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    filter_upwards [hfE] with z hz
    exact prod_rpow_inv_eq_zero hn hz
  have hpole' : (μ.withDensity Pd) ((Ω : Set (ComplexModel n)) ∩ componentPoleSet u) = 0 := by
    refine measure_mono_null ?_ (measure_iUnion_null hpole)
    rintro z ⟨hzΩ, j, hj⟩
    exact mem_iUnion.mpr ⟨j, hzΩ, ⟨⟨0, hn⟩, hj⟩⟩
  -- Step 4: assemble
  refine Measure.le_iff.mpr fun s hs => ?_
  rw [Measure.restrict_apply hs]
  have hcover : s ∩ (Ω : Set (ComplexModel n)) ⊆
      (⋃ k, s ∩ G k) ∪ ((Ω : Set (ComplexModel n)) ∩ componentPoleSet u) := by
    rintro z ⟨hzs, hzΩ⟩
    by_cases hz : z ∈ ⋃ k, G k
    · obtain ⟨k, hk⟩ := mem_iUnion.mp hz
      exact Or.inl (mem_iUnion.mpr ⟨k, hzs, hk⟩)
    · right
      have hz' : z ∈ (⋃ k, G k)ᶜ := hz
      rw [hG, compl_iUnion_commonStrictLocus] at hz'
      rcases hz' with h' | h'
      · exact absurd hzΩ h'
      · exact ⟨hzΩ, h'⟩
  have hmono : Monotone fun k => s ∩ G k :=
    fun k l hkl => inter_subset_inter_right _ (commonStrictLocus_mono Ω u hkl)
  calc (μ.withDensity Pd) (s ∩ Ω)
      ≤ (μ.withDensity Pd) ((⋃ k, s ∩ G k) ∪ ((Ω : Set (ComplexModel n)) ∩ componentPoleSet u)) :=
        measure_mono hcover
    _ ≤ (μ.withDensity Pd) (⋃ k, s ∩ G k) +
          (μ.withDensity Pd) ((Ω : Set (ComplexModel n)) ∩ componentPoleSet u) :=
        measure_union_le _ _
    _ = ⨆ k, (μ.withDensity Pd) (s ∩ G k) := by
        rw [hpole', add_zero, hmono.measure_iUnion]
    _ ≤ mixedTruncationLimitMeasure Ω u hu s := by
        refine iSup_le fun k => ?_
        have := hstep2 k s
        rwa [Measure.restrict_apply hs] at this

end SGPT.Envelopes.DinewMeasure
