import SGPT.NPP.NonPluripolarCurrent5Fibre

/-!
# Measurability of fibre integrals of Bedford–Taylor products

Source: `chapter_npp.tex`, proof of `lma:boundedfibrefubini`, second paragraph (the functions
`F_χ(z) = ∫_U χ M_z` are Borel measurable, and the two functional monotone class arguments).

Let `Ω ⊆ ℂⁿ⁺ᵐ = ℂⁿ × ℂᵐ` be open, `ν` the Bedford–Taylor limit (`BedfordTaylor.IsBTLimit`) of a
tuple `u` of locally bounded psh functions on `Ω` and `μ_z` the Bedford–Taylor limits of the fibre
tuples `x ↦ u_i(x, z)`, `i < n`, on the fibres `Ω_z`.  For a continuous `χ` with compact support in
`Ω` and every bounded Borel `F`,

`z ↦ ∫ χ(x, z) F(x, z) dμ_z(x)`

is almost everywhere strongly measurable on `ℂᵐ` (`aestronglyMeasurable_fibreIntegral_mul`).

* For a continuous test function `g` (`aestronglyMeasurable_fibreIntegral_of_continuous`) the fibre
  integral is the pointwise limit of `z ↦ ∫ g(x, z) D_l(x, z) dx`, `D_l` the mixed density of the
  fibre restrictions of decreasing smooth psh approximations (Bedford–Taylor convergence on every
  fibre, `IsBTLimit.tendstoMixed`); these are integrable in `z` by Fubini, since
  `(x, z) ↦ g(x, z) D_l(x, z)` is continuous with compact support (the complex Hessian of a
  fibre restriction is a block of the complex Hessian, `complexHessian_fibreRestrictM`).
* The functional monotone class argument of the source (FPT `lem:measurable-fibre-family`) is
  run, as in TN's `BedfordTaylorBorelFibreSlicing`, on indicators of open sets (thickened
  indicators), then all Borel sets (`MeasurableSet.induction_on_open`: complements and countable
  disjoint unions), simple functions and bounded Borel functions (`approxBounded`), using dominated
  convergence on each fibre.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory TopologicalSpace Metric
open scoped Topology ContDiff

namespace SGPT.NPP.FibreSlicing

open SGPT.Foundations.Analysis
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.FirstPass.MixedMongeAmpere
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.BedfordTaylor
open SGPT.Foundations.Analysis.Pending.ProductComplexManifold

variable {n m : ℕ}

/-- The fibre integral `z ↦ ∫ g(x, z) dμ_z(x)`. -/
def fibreIntegral (μ : ComplexModel m → Measure (ComplexModel n))
    (g : ComplexModel (n + m) → ℝ) (z : ComplexModel m) : ℝ :=
  ∫ x, g (fibreMapM n m z x) ∂(μ z)

variable {Ω : Opens (ComplexModel (n + m))} {u : Fin (n + m) → ComplexModel (n + m) → ℝ}
  {ν : Measure (ComplexModel (n + m))} {μ : ComplexModel m → Measure (ComplexModel n)}

/-! ### Continuous test functions -/

/-- **Fibre integrals of continuous test functions are measurable.** -/
theorem aestronglyMeasurable_fibreIntegral_of_continuous (hν : IsBTLimit Ω u ν)
    (hμ : ∀ z, IsBTLimit (fibreOpensM Ω z) (fibreTupleM u z) (μ z))
    {g : ComplexModel (n + m) → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    (hgΩ : tsupport g ⊆ Ω) :
    AEStronglyMeasurable (fibreIntegral μ g) volume := by
  obtain ⟨U, hUo, hKU, hUΩ, hUc⟩ := exists_open_between_and_isCompact_closure hgc Ω.isOpen hgΩ
  set UO : Opens (ComplexModel (n + m)) := ⟨U, hUo⟩ with hUOdef
  have hUrc : RelativelyCompactIn UO Ω := ⟨hUc, hUΩ⟩
  obtain ⟨F, hF, -⟩ := hν.2.2 UO hUrc
  -- the block density
  set Φ : ℕ → ComplexModel (n + m) → ℝ := fun l q =>
    (mixedCoefficient fun i => (complexHessian (F (Fin.castAdd m i) l) q).submatrix
      (Fin.castAdd m) (Fin.castAdd m)).re / Real.pi ^ n with hΦdef
  have hΦc (l : ℕ) : ContinuousOn (Φ l) UO := by
    have hC : ContinuousOn (fun q => mixedCoefficient fun i =>
        (complexHessian (F (Fin.castAdd m i) l) q).submatrix (Fin.castAdd m) (Fin.castAdd m))
        UO := by
      unfold mixedCoefficient
      refine continuousOn_finsetSum _ fun σ _ => ?_
      have : ContinuousOn (fun q => (Matrix.of fun j k =>
          (complexHessian (F (Fin.castAdd m (σ j)) l) q).submatrix (Fin.castAdd m)
            (Fin.castAdd m) j k)) UO :=
        continuousOn_pi.2 fun j => continuousOn_pi.2 fun k =>
          IsSmoothPsdOn.continuousOn_complexHessian ((hF.1 _).1 l).1 _ _
      exact continuous_id.matrix_det.comp_continuousOn this
    exact (Complex.continuous_re.comp_continuousOn hC).div_const _
  have hΦfib (l : ℕ) (z : ComplexModel m) (x : ComplexModel n) (hx : fibreMapM n m z x ∈ UO) :
      mixedDensity (fun i => fibreRestrictM (F (Fin.castAdd m i) l) z) x =
        Φ l (fibreMapM n m z x) := by
    simp only [mixedDensity, hΦdef]
    congr 3
    funext i
    exact complexHessian_fibreRestrictM UO.isOpen ((hF.1 _).1 l).1 hx
  have hgint (l : ℕ) : Integrable (fun q => g q * Φ l q) :=
    BedfordTaylor.integrable_mul_of_continuousOn (hΦc l) hg hgc hKU
  have hGl (l : ℕ) : Integrable (fun z : ComplexModel m =>
      ∫ x, g (fibreMapM n m z x) * Φ l (fibreMapM n m z x)) := by
    have hmp := ProductMixedMeasure.measurePreserving_prodModelEquiv n m
    have hemb : MeasurableEmbedding (prodModelEquiv n m) :=
      (prodModelEquiv n m).toHomeomorph.measurableEmbedding
    have hint : Integrable ((fun q => g q * Φ l q) ∘ prodModelEquiv n m)
        (volume.prod volume) := (hmp.integrable_comp_emb hemb).2 (hgint l)
    exact hint.integral_prod_right
  have hlim (z : ComplexModel m) : Tendsto (fun l =>
      ∫ x, g (fibreMapM n m z x) * Φ l (fibreMapM n m z x)) atTop
      (𝓝 (fibreIntegral μ g z)) := by
    have hT := (hμ z).tendstoMixed (relativelyCompactIn_fibreOpensM hUrc z)
      (IsAdmissible.fibreM hF z)
    have h := hT (fibreRestrictM g z) (hg.comp (continuous_fibreMapM z))
      (hasCompactSupport_fibreRestrictM hgc z)
      (fun x hx => hKU (tsupport_fibreRestrictM_subset g z hx))
    refine h.congr' (Eventually.of_forall fun l => integral_congr_ae
      (Eventually.of_forall fun x => ?_))
    by_cases hx : fibreMapM n m z x ∈ UO
    · simp only [fibreRestrictM]
      rw [hΦfib l z x hx]
    · have h0 : g (fibreMapM n m z x) = 0 := image_eq_zero_of_notMem_tsupport fun h => hx (hKU h)
      simp [fibreRestrictM, h0]
  exact aestronglyMeasurable_of_tendsto_ae atTop (fun l => (hGl l).aestronglyMeasurable)
    (Eventually.of_forall hlim)

/-! ### Bounded Borel weights -/

section Borel

variable {χ : ComplexModel (n + m) → ℝ}

theorem integrable_fibre_test
    (hμ : ∀ z, IsBTLimit (fibreOpensM Ω z) (fibreTupleM u z) (μ z))
    (hχ : Continuous χ) (hχc : HasCompactSupport χ) (hχΩ : tsupport χ ⊆ Ω) (z : ComplexModel m) :
    Integrable (fibreRestrictM χ z) (μ z) := by
  have hsupp := tsupport_fibreRestrictM_subset χ z
  exact VaguePortmanteau.integrable_of_tsupport_subset (hμ z).2.1
    (hχ.comp (continuous_fibreMapM z)) (hasCompactSupport_fibreRestrictM hχc z)
    (fun x hx => hχΩ (hsupp hx))

theorem integrable_fibre_test_mul
    (hμ : ∀ z, IsBTLimit (fibreOpensM Ω z) (fibreTupleM u z) (μ z))
    (hχ : Continuous χ) (hχc : HasCompactSupport χ) (hχΩ : tsupport χ ⊆ Ω)
    {F : ComplexModel (n + m) → ℝ} (hFm : Measurable F) {C : ℝ}
    (hFb : ∀ q, ‖F q‖ ≤ C) (z : ComplexModel m) :
    Integrable (fun x => χ (fibreMapM n m z x) * F (fibreMapM n m z x)) (μ z) :=
  (integrable_fibre_test hμ hχ hχc hχΩ z).mul_bdd
    (hFm.comp (continuous_fibreMapM z).measurable).aestronglyMeasurable
    (Eventually.of_forall fun x => hFb (fibreMapM n m z x))

private theorem meas_sub
    (hμ : ∀ z, IsBTLimit (fibreOpensM Ω z) (fibreTupleM u z) (μ z))
    (hχ : Continuous χ) (hχc : HasCompactSupport χ) (hχΩ : tsupport χ ⊆ Ω)
    {F G : ComplexModel (n + m) → ℝ} (hFm : Measurable F) (hGm : Measurable G)
    {C D : ℝ} (hFb : ∀ q, ‖F q‖ ≤ C) (hGb : ∀ q, ‖G q‖ ≤ D)
    (hF : AEStronglyMeasurable (fibreIntegral μ fun q => χ q * F q) volume)
    (hG : AEStronglyMeasurable (fibreIntegral μ fun q => χ q * G q) volume) :
    AEStronglyMeasurable (fibreIntegral μ fun q => χ q * (F - G) q) volume := by
  have hout : (fibreIntegral μ fun q => χ q * (F - G) q) =
      fun z => fibreIntegral μ (fun q => χ q * F q) z - fibreIntegral μ (fun q => χ q * G q) z := by
    funext z
    simp only [fibreIntegral, Pi.sub_apply, mul_sub]
    exact integral_sub (integrable_fibre_test_mul hμ hχ hχc hχΩ hFm hFb z)
      (integrable_fibre_test_mul hμ hχ hχc hχΩ hGm hGb z)
  rw [hout]
  exact hF.sub hG

private theorem meas_of_bounded_limit
    (hμ : ∀ z, IsBTLimit (fibreOpensM Ω z) (fibreTupleM u z) (μ z))
    (hχ : Continuous χ) (hχc : HasCompactSupport χ) (hχΩ : tsupport χ ⊆ Ω)
    {F : ComplexModel (n + m) → ℝ} {Fk : ℕ → ComplexModel (n + m) → ℝ} {C : ℝ}
    (hFkm : ∀ k, Measurable (Fk k)) (hFkb : ∀ k q, ‖Fk k q‖ ≤ C)
    (hlim : ∀ q, Tendsto (fun k => Fk k q) atTop (𝓝 (F q)))
    (hk : ∀ k, AEStronglyMeasurable (fibreIntegral μ fun q => χ q * Fk k q) volume) :
    AEStronglyMeasurable (fibreIntegral μ fun q => χ q * F q) volume := by
  have hnorm (k : ℕ) (q : ComplexModel (n + m)) : ‖χ q * Fk k q‖ ≤ C * ‖χ q‖ := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left (hFkb k q) (norm_nonneg _)).trans_eq (mul_comm _ _)
  have hJlim (z : ComplexModel m) : Tendsto (fun k => fibreIntegral μ (fun q => χ q * Fk k q) z)
      atTop (𝓝 (fibreIntegral μ (fun q => χ q * F q) z)) := by
    apply tendsto_integral_of_dominated_convergence
      (fun x => C * ‖χ (fibreMapM n m z x)‖)
    · intro k
      exact ((hχ.comp (continuous_fibreMapM z)).measurable.mul
        ((hFkm k).comp (continuous_fibreMapM z).measurable)).aestronglyMeasurable
    · exact (integrable_fibre_test hμ hχ hχc hχΩ z).norm.const_mul C
    · intro k
      exact Eventually.of_forall fun x => hnorm k (fibreMapM n m z x)
    · exact Eventually.of_forall fun x => tendsto_const_nhds.mul (hlim (fibreMapM n m z x))
  exact aestronglyMeasurable_of_tendsto_ae atTop hk (Eventually.of_forall hJlim)

private theorem meas_finsetSum {ι : Type*} (s : Finset ι)
    (hμ : ∀ z, IsBTLimit (fibreOpensM Ω z) (fibreTupleM u z) (μ z))
    (hχ : Continuous χ) (hχc : HasCompactSupport χ) (hχΩ : tsupport χ ⊆ Ω)
    {F : ι → ComplexModel (n + m) → ℝ} {C : ι → ℝ}
    (hFm : ∀ i ∈ s, Measurable (F i)) (hFb : ∀ i ∈ s, ∀ q, ‖F i q‖ ≤ C i)
    (hF : ∀ i ∈ s, AEStronglyMeasurable (fibreIntegral μ fun q => χ q * F i q) volume) :
    AEStronglyMeasurable (fibreIntegral μ fun q => χ q * ∑ i ∈ s, F i q) volume := by
  have hout : (fibreIntegral μ fun q => χ q * ∑ i ∈ s, F i q) =
      fun z => ∑ i ∈ s, fibreIntegral μ (fun q => χ q * F i q) z := by
    funext z
    simp only [fibreIntegral, Finset.mul_sum]
    exact integral_finsetSum s (fun i hi =>
      integrable_fibre_test_mul hμ hχ hχc hχΩ (hFm i hi) (hFb i hi) z)
  rw [hout]
  exact Finset.aestronglyMeasurable_fun_sum s fun i hi => hF i hi

private theorem meas_open_indicator (hν : IsBTLimit Ω u ν)
    (hμ : ∀ z, IsBTLimit (fibreOpensM Ω z) (fibreTupleM u z) (μ z))
    (hχ : Continuous χ) (hχc : HasCompactSupport χ) (hχΩ : tsupport χ ⊆ Ω)
    {E : Set (ComplexModel (n + m))} (hE : IsOpen E) :
    AEStronglyMeasurable (fibreIntegral μ fun q => χ q * E.indicator (fun _ => (1 : ℝ)) q)
      volume := by
  have hδ (k : ℕ) : 0 < (1 : ℝ) / ((k : ℝ) + 1) := by positivity
  let Fk : ℕ → ComplexModel (n + m) → ℝ :=
    fun k q => 1 - (thickenedIndicator (hδ k) Eᶜ q : ℝ)
  have hFc (k : ℕ) : Continuous (Fk k) :=
    continuous_const.sub (NNReal.continuous_coe.comp (thickenedIndicator (hδ k) Eᶜ).continuous)
  have hFb (k : ℕ) (q : ComplexModel (n + m)) : ‖Fk k q‖ ≤ 1 := by
    have hlo : 0 ≤ (thickenedIndicator (hδ k) Eᶜ q : ℝ) := NNReal.coe_nonneg _
    have hup : (thickenedIndicator (hδ k) Eᶜ q : ℝ) ≤ 1 := by
      exact_mod_cast thickenedIndicator_le_one (hδ k) Eᶜ q
    change ‖1 - (thickenedIndicator (hδ k) Eᶜ q : ℝ)‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hup)]
    linarith
  have hFlim (q : ComplexModel (n + m)) :
      Tendsto (fun k => Fk k q) atTop (𝓝 (E.indicator (fun _ => (1 : ℝ)) q)) := by
    have hs := thickenedIndicator_tendsto_indicator_closure hδ
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)) Eᶜ
    have hq := (NNReal.continuous_coe.tendsto _).comp ((tendsto_pi_nhds.mp hs) q)
    have ht := (tendsto_const_nhds (x := (1 : ℝ))).sub hq
    by_cases h : q ∈ E
    · simpa [Fk, hE.isClosed_compl.closure_eq, h] using ht
    · simpa [Fk, hE.isClosed_compl.closure_eq, h] using ht
  apply meas_of_bounded_limit hμ hχ hχc hχΩ (fun k => (hFc k).measurable) hFb hFlim
  intro k
  have hsupp : tsupport (fun q => χ q * Fk k q) ⊆ tsupport χ := tsupport_mul_subset_left
  have hc : HasCompactSupport (fun q => χ q * Fk k q) :=
    hχc.of_isClosed_subset (isClosed_tsupport _) hsupp
  exact aestronglyMeasurable_fibreIntegral_of_continuous hν hμ (hχ.mul (hFc k)) hc
    (hsupp.trans hχΩ)

private theorem meas_indicator (hν : IsBTLimit Ω u ν)
    (hμ : ∀ z, IsBTLimit (fibreOpensM Ω z) (fibreTupleM u z) (μ z))
    (hχ : Continuous χ) (hχc : HasCompactSupport χ) (hχΩ : tsupport χ ⊆ Ω)
    {E : Set (ComplexModel (n + m))} (hE : MeasurableSet E) :
    AEStronglyMeasurable (fibreIntegral μ fun q => χ q * E.indicator (fun _ => (1 : ℝ)) q)
      volume := by
  classical
  let W : Set (ComplexModel (n + m)) → ComplexModel (n + m) → ℝ :=
    fun S => S.indicator (fun _ => 1)
  have hWb (S : Set (ComplexModel (n + m))) (q : ComplexModel (n + m)) : ‖W S q‖ ≤ 1 := by
    by_cases h : q ∈ S <;> simp [W, h]
  have hWm (S : Set (ComplexModel (n + m))) (hS : MeasurableSet S) : Measurable (W S) :=
    measurable_const.indicator hS
  let P : Set (ComplexModel (n + m)) → Prop := fun S =>
    AEStronglyMeasurable (fibreIntegral μ fun q => χ q * W S q) volume
  change P E
  refine MeasurableSet.induction_on_open (C := fun S _ => P S) ?_ ?_ ?_ E hE
  · intro S hS
    exact meas_open_indicator hν hμ hχ hχc hχΩ hS
  · intro S hS ih
    have htotal : AEStronglyMeasurable (fibreIntegral μ fun q => χ q * (fun _ => (1 : ℝ)) q)
        volume := by
      simpa only [mul_one] using
        aestronglyMeasurable_fibreIntegral_of_continuous hν hμ hχ hχc hχΩ
    have hcomp : W Sᶜ = (fun _ => (1 : ℝ)) - W S := by
      funext q
      by_cases h : q ∈ S <;> simp [W, h]
    dsimp only [P]
    rw [hcomp]
    exact meas_sub (C := 1) (D := 1) hμ hχ hχc hχΩ measurable_const (hWm S hS)
      (fun _ => by simp) (hWb S) htotal ih
  · intro S hd hS ih
    let H : ℕ → Set (ComplexModel (n + m)) := fun k => ⋃ i ∈ Finset.range k, S i
    have hHm (k : ℕ) : MeasurableSet (H k) :=
      MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun _ => hS i
    have hHlim (q : ComplexModel (n + m)) :
        Tendsto (fun k => W (H k) q) atTop (𝓝 (W (⋃ i, S i) q)) := by
      by_cases hq : q ∈ ⋃ i, S i
      · obtain ⟨i, hi⟩ := mem_iUnion.mp hq
        have hevent : ∀ᶠ k : ℕ in atTop, W (H k) q = 1 := by
          filter_upwards [eventually_ge_atTop (i + 1)] with k hk
          have hmem : q ∈ H k := mem_iUnion.mpr ⟨i, mem_iUnion.mpr
            ⟨Finset.mem_range.mpr (by omega), hi⟩⟩
          simp only [W, indicator_of_mem hmem]
        simpa only [W, indicator_of_mem hq] using
          (tendsto_const_nhds (x := (1 : ℝ))).congr' (hevent.mono fun _ hk => hk.symm)
      · have hnot (k : ℕ) : q ∉ H k := by
          intro hy
          obtain ⟨i, hi⟩ := mem_iUnion.mp hy
          obtain ⟨_, hqi⟩ := mem_iUnion.mp hi
          exact hq (mem_iUnion.mpr ⟨i, hqi⟩)
        have heq : (fun k => W (H k) q) = fun _ => (0 : ℝ) := by
          funext k
          simp only [W, indicator_of_notMem (hnot k)]
        rw [heq]
        simpa only [W, indicator_of_notMem hq] using tendsto_const_nhds (x := (0 : ℝ))
    apply meas_of_bounded_limit hμ hχ hχc hχΩ (fun k => hWm (H k) (hHm k))
      (fun k q => hWb (H k) q) hHlim
    intro k
    have hs : (↑(Finset.range k) : Set ℕ).PairwiseDisjoint S := by
      intro i _ j _ hij
      exact hd hij
    have hsum : W (H k) = fun q => ∑ i ∈ Finset.range k, W (S i) q := by
      funext q
      exact Finset.indicator_biUnion_apply (Finset.range k) S hs q
    rw [hsum]
    exact meas_finsetSum (Finset.range k) hμ hχ hχc hχΩ
      (fun i _ => hWm (S i) (hS i)) (fun i _ q => hWb (S i) q) (fun i _ => ih i)

private theorem meas_simpleFunc (hν : IsBTLimit Ω u ν)
    (hμ : ∀ z, IsBTLimit (fibreOpensM Ω z) (fibreTupleM u z) (μ z))
    (hχ : Continuous χ) (hχc : HasCompactSupport χ) (hχΩ : tsupport χ ⊆ Ω)
    (sf : SimpleFunc (ComplexModel (n + m)) ℝ) :
    AEStronglyMeasurable (fibreIntegral μ fun q => χ q * sf q) volume := by
  classical
  let F : ℝ → ComplexModel (n + m) → ℝ :=
    fun c q => c * (sf ⁻¹' {c}).indicator (fun _ => (1 : ℝ)) q
  have hFm (c : ℝ) : Measurable (F c) :=
    measurable_const.mul (measurable_const.indicator (sf.measurableSet_preimage {c}))
  have hFb (c : ℝ) (q : ComplexModel (n + m)) : ‖F c q‖ ≤ ‖c‖ := by
    by_cases h : q ∈ sf ⁻¹' {c} <;> simp [F, h]
  have hF (c : ℝ) : AEStronglyMeasurable (fibreIntegral μ fun q => χ q * F c q) volume := by
    have hout : (fibreIntegral μ fun q => χ q * F c q) = fun z =>
        c * fibreIntegral μ (fun q => χ q * (sf ⁻¹' {c}).indicator (fun _ => (1 : ℝ)) q) z := by
      funext z
      simp only [fibreIntegral, F]
      rw [← integral_const_mul]
      congr 1
      funext x
      ring
    rw [hout]
    exact (meas_indicator hν hμ hχ hχc hχΩ (sf.measurableSet_preimage {c})).const_mul c
  have hsum : (fun q => ∑ c ∈ sf.range, F c q) = sf := by
    funext q
    rw [Finset.sum_eq_single (sf q)]
    · simp [F]
    · intro c _ hne
      have hnot : q ∉ sf ⁻¹' {c} := by simpa only [mem_preimage, mem_singleton_iff] using hne.symm
      simp [F, hnot]
    · intro hn
      exact (hn (sf.mem_range_self q)).elim
  have hs := meas_finsetSum sf.range hμ hχ hχc hχΩ (fun c _ => hFm c) (fun c _ q => hFb c q)
    (fun c _ => hF c)
  have hsum_apply (q : ComplexModel (n + m)) : (∑ c ∈ sf.range, F c q) = sf q :=
    congrFun hsum q
  simpa only [hsum_apply] using hs

/-- **Measurability of fibre integrals with bounded Borel weights** (`lma:boundedfibrefubini`,
the two monotone class arguments): for a continuous `χ` with compact support in `Ω` and a bounded
Borel `F`, `z ↦ ∫ χ(x, z) F(x, z) dμ_z(x)` is a.e. strongly measurable on `ℂᵐ`. -/
theorem aestronglyMeasurable_fibreIntegral_mul (hν : IsBTLimit Ω u ν)
    (hμ : ∀ z, IsBTLimit (fibreOpensM Ω z) (fibreTupleM u z) (μ z))
    (hχ : Continuous χ) (hχc : HasCompactSupport χ) (hχΩ : tsupport χ ⊆ Ω)
    {F : ComplexModel (n + m) → ℝ} (hFm : Measurable F) {C : ℝ} (hFb : ∀ q, ‖F q‖ ≤ C) :
    AEStronglyMeasurable (fibreIntegral μ fun q => χ q * F q) volume := by
  have hC : 0 ≤ C := (norm_nonneg (F 0)).trans (hFb 0)
  have hFs := hFm.stronglyMeasurable
  exact meas_of_bounded_limit hμ hχ hχc hχΩ
    (fun k => (hFs.approxBounded C k).measurable)
    (fun k q => hFs.norm_approxBounded_le hC k q)
    (fun q => hFs.tendsto_approxBounded_of_norm_le (hFb q))
    (fun k => meas_simpleFunc hν hμ hχ hχc hχΩ (hFs.approxBounded C k))

end Borel

end SGPT.NPP.FibreSlicing
