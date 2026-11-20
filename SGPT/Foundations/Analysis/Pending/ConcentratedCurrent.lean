import SGPT.Foundations.Analysis.Pending.NefCoreKahlerCurrent

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The concentrated current of Boucksom's Lemma 4.12, with an explicit constant

Source: Boucksom, Lemma 4.12 and its proof (`bou02-volume:4.12`); Demailly--Păun, Proposition 2.6
(`dp04-kahler-cone:2.6`).  Blueprint `bou:concentrated-current` (with
`bou:concentrated-current-integration`).  TN.4 plan, step (P-a) of "(P) SCOPING"
.

Let `(M, W)` be a compact Kähler manifold of dimension `N = d + p`.  For every `k` let `A k` be a
smooth closed real `(1,1)`-form, `α_k = A k + ddᶜ g_k` a Kähler form, `ω_k = W + ddᶜ f_k ≥ W/2`, with
`α_k^N = c_k ω_k^N` pointwise (Yau's theorem supplies such `g_k`, `c_k`; here they are DATA, so this
module is Yau-free), and `S k` sets with `∫_{S k} ω_k^p ∧ W^d ≥ δ`.  If `∫ (A k)^N ≥ P₀` and
`∫ (A k)^d ∧ W^p ≤ M₀`, then (`le_mixedMeasure_concentrated`)

`∫_{S k} α_k^p ∧ W^d ≥ (P₀ / vol W) · δ² / (4 · 2^d · N! · M₀)`,

a constant which depends only on `P₀`, `vol W`, `δ`, `M₀` (not on `k`, not on the forms).  This
explicitness is what the uniformity in the resolution step of Boucksom 4.8 (`bou02-volume:4.10`)
needs.  The currents `[M] ∧ α_k^p` then have a weak limit `Θ`, closed and positive, along an
ultrafilter, whose trace measure keeps the same lower bound on `⋂ F_j` for closed `F_j ⊇ S k`
(`exists_concentratedCurrent`).

* `mul_vol_eq_slotIntegral` — the Yau constant is the volume ratio: `c · vol W = ∫ Aᴺ`.
* `le_mixedMeasure_concentrated` — one level, explicit constant.
* `le_traceMeasure_smoothCurrent` — the same bound for the trace measure of `[M] ∧ α_k^p`.
* `exists_concentratedCurrent` — the weak limit (`bou:concentrated-current`).

The nef core `NefCoreKahlerCurrent.exists_kahlerCurrent_of_nef` is the case `M = X × X`,
`p = d = n`, `A k = p₁^*(b + ε_k ω) + p₂^*(b + ε_k ω)`.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal

namespace SGPT.Foundations.Analysis.Pending.ConcentratedCurrent

open FirstPass FirstPass.MongeAmpere FirstPass.PositiveClasses ProductTestForms
  PositiveProductCurrents IntegrationCurrent TopDegreeDensity SmoothCurrentTraceMeasure
  ManifoldTubePositivity MixedMassClassInvariance NefMixedMass GlobalNonPluripolar
  NefCoreKahlerCurrent

/-! ### The Yau constant is the volume ratio -/

section Volume

variable {N : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel N) M]
  [IsComplexManifold N M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]

/-- **The Yau constant is the volume ratio**: if `(A + ddᶜg)^N = c (W + ddᶜf)^N` pointwise, then
`c · vol W = ∫ Aᴺ` (class invariance of top-degree integrals on both sides). -/
theorem mul_vol_eq_slotIntegral (W : KahlerBackground N M) (A : ClosedRealOneOneForm N M)
    {g : M → ℝ} (hg : ChartSmooth (n := N) g) {f : M → ℝ} (hf : ChartSmooth (n := N) f) {c : ℝ}
    (hMA : ∀ (e : ComplexChart N M) (z : ComplexModel N), z ∈ e.val.target →
      actualTopPowerDensity ((A + ddcClosedForm g hg).val.coeff e z) =
        c * actualTopPowerDensity ((W.form + ddcClosedForm f hf).val.coeff e z)) :
    c * (kahlerVolume W).real univ = slotIntegral W fun _ => A := by
  have h1 := integral_congr_ae (μ := kahlerVolume W)
    (Eventually.of_forall (topRatio_formPow_eq_mul W hMA))
  rw [integral_const_mul] at h1
  have hL : ∫ x, topRatio W.form.val (formPow (A + ddcClosedForm g hg).val N) x
      ∂(kahlerVolume W) = slotIntegral W fun _ => A := by
    simp_rw [topRatio_formPow_eq_slotForm']
    rw [← slotIntegral, slotIntegral_add_ddc W (fun _ => A) (fun _ => g) (fun _ => hg)]
  have hR : ∫ x, topRatio W.form.val (formPow (W.form + ddcClosedForm f hf).val N) x
      ∂(kahlerVolume W) = (kahlerVolume W).real univ := by
    simp_rw [topRatio_formPow_eq_slotForm']
    rw [← slotIntegral, slotIntegral_add_ddc W (fun _ => _) (fun _ => f) (fun _ => hf),
      slotIntegral]
    simp_rw [← topRatio_formPow_eq_slotForm', topRatio_formPow W.isKahler.1]
    simp [integral_const]
  rw [hL, hR] at h1
  exact h1.symm

end Volume

/-! ### One concentrated level -/

section Level

variable {d p : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel (d + p)) M]
  [IsComplexManifold (d + p) M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]

/-- `W + ddᶜf ≥ W/2` makes `W + ddᶜf` Kähler. -/
theorem isKahler_of_half (W : KahlerBackground (d + p) M) {f : M → ℝ}
    (hf : ChartSmooth (n := d + p) f)
    (hhalf : ((1 / 2 : ℝ) • W.form + ddcClosedForm f hf).val.IsSemipositive) :
    (W.form + ddcClosedForm f hf).val.IsKahler := by
  have h := isKahler_add_smul_of_isSemipositive W hhalf (t := 1 / 2) (by norm_num)
  have heq : (1 / 2 : ℝ) • W.form + ddcClosedForm f hf + (1 / 2 : ℝ) • W.form =
      W.form + ddcClosedForm f hf := by
    module
  rwa [heq] at h

/-- **One level of the concentrated current, with an explicit constant** (Boucksom 4.12,
dp04 2.6): if `α = A + ddᶜg` is Kähler with `α^N = c (W + ddᶜf)^N`, `W + ddᶜf ≥ W/2`,
`∫_S (W + ddᶜf)^p ∧ W^d ≥ δ`, `∫ Aᴺ ≥ P₀` and `∫ A^d ∧ W^p ≤ M₀`, then
`∫_S α^p ∧ W^d ≥ (P₀ / vol W) δ² / (4 · 2^d · N! · M₀)`. -/
theorem le_mixedMeasure_concentrated (W : KahlerBackground (d + p) M)
    (A : ClosedRealOneOneForm (d + p) M) {g : M → ℝ} (hg : ChartSmooth (n := d + p) g)
    {f : M → ℝ} (hf : ChartSmooth (n := d + p) f)
    (hαK : (A + ddcClosedForm g hg).val.IsKahler)
    (hhalf : ((1 / 2 : ℝ) • W.form + ddcClosedForm f hf).val.IsSemipositive)
    {c : ℝ} (hc : 0 < c)
    (hMA : ∀ (e : ComplexChart (d + p) M) (z : ComplexModel (d + p)), z ∈ e.val.target →
      actualTopPowerDensity ((A + ddcClosedForm g hg).val.coeff e z) =
        c * actualTopPowerDensity ((W.form + ddcClosedForm f hf).val.coeff e z))
    {S : Set M} {δ P₀ M₀ : ℝ} (hδ : 0 < δ) (hM₀ : 0 < M₀)
    (h₁ : ∀ i, ThetaPlurisubharmonic ((fun i : Fin (d + p) =>
      if (i : ℕ) < p then W.form + ddcClosedForm f hf else W.form) i).val (fun _ => 0))
    (h₂ : ∀ i, ThetaPlurisubharmonic ((fun i : Fin (d + p) =>
      if (i : ℕ) < p then A + ddcClosedForm g hg else W.form) i).val (fun _ => 0))
    (hconc : ENNReal.ofReal δ ≤ globalMixedMeasure (fun i : Fin (d + p) =>
      if (i : ℕ) < p then W.form + ddcClosedForm f hf else W.form) (fun _ _ => 0) h₁ S)
    (hvol : P₀ ≤ slotIntegral W fun _ => A)
    (hmass : slotIntegral W (fun i : Fin (d + p) => if (i : ℕ) < d then A else W.form) ≤ M₀) :
    ENNReal.ofReal (P₀ / (kahlerVolume W).real univ * δ ^ 2 /
        (4 * 2 ^ d * (d + p).factorial * M₀)) ≤
      globalMixedMeasure (fun i : Fin (d + p) =>
        if (i : ℕ) < p then A + ddcClosedForm g hg else W.form) (fun _ _ => 0) h₂ S := by
  have hωεK := isKahler_of_half W hf hhalf
  have hαpsh : ThetaPlurisubharmonic (A + ddcClosedForm g hg).val (fun _ => 0) :=
    (LocalPotentials.thetaPlurisubharmonic_zero_iff _).mpr
      (KahlerBackground.isSemipositive ⟨_, hαK⟩)
  have hωεpsh : ThetaPlurisubharmonic (W.form + ddcClosedForm f hf).val (fun _ => 0) :=
    (LocalPotentials.thetaPlurisubharmonic_zero_iff _).mpr
      (KahlerBackground.isSemipositive ⟨_, hωεK⟩)
  have h₃ : ∀ i : Fin (d + p), ThetaPlurisubharmonic
      ((fun i : Fin (d + p) => if (i : ℕ) < d + p - p then A + ddcClosedForm g hg
        else W.form + ddcClosedForm f hf) i).val (fun _ => 0) := by
    intro i
    dsimp only
    split_ifs
    · exact hαpsh
    · exact hωεpsh
  have hup : globalMixedMeasure (fun i : Fin (d + p) =>
      if (i : ℕ) < d + p - p then A + ddcClosedForm g hg else W.form + ddcClosedForm f hf)
        (fun _ _ => 0) h₃ S ≤ ENNReal.ofReal M₀ := by
    have := ProductMixedMeasure.isFiniteMeasure_globalMixedMeasure h₃
    refine (measure_mono (subset_univ _)).trans ?_
    rw [← ofReal_measureReal (measure_ne_top _ _)]
    apply ENNReal.ofReal_le_ofReal
    rw [globalMixedMeasure_real_univ_eq_integral W _ h₃, ← slotIntegral]
    have hfam : slotIntegral W (fun i : Fin (d + p) =>
        if (i : ℕ) < d + p - p then A + ddcClosedForm g hg else W.form + ddcClosedForm f hf) =
          slotIntegral W (fun i : Fin (d + p) => if (i : ℕ) < d then A else W.form) := by
      simp only [Nat.add_sub_cancel]
      exact slotIntegral_ite_add_ddc W d A W.form hg hf
    rw [hfam]
    exact hmass
  have hωε : ((W.form + ddcClosedForm f hf) - (1 / 2 : ℝ) • W.form).val.IsSemipositive := by
    have heq : W.form + ddcClosedForm f hf - (1 / 2 : ℝ) • W.form =
        (1 / 2 : ℝ) • W.form + ddcClosedForm f hf := by
      module
    rw [heq]
    exact hhalf
  have hmain := ConcentrationMassComparison.le_mixedMeasure_of_mongeAmpere W
    (W.form + ddcClosedForm f hf) (A + ddcClosedForm g hg) hωε hαK hc hMA (p := p) (by omega)
    h₁ h₂ h₃ hδ hM₀ hconc hup
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) hmain
  rw [Nat.add_sub_cancel]
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  have hcv := mul_vol_eq_slotIntegral W A hg hf hMA
  rcases (measureReal_nonneg : 0 ≤ (kahlerVolume W).real univ).eq_or_lt with h0 | hpos
  · rw [← h0, div_zero]
    exact hc.le
  · rw [div_le_iff₀ hpos]
    linarith

/-- The slots `(α, …, α, W, …, W)` of the current `[M] ∧ α^p`. -/
def concentratedSlots (W : KahlerBackground (d + p) M) (α : ClosedRealOneOneForm (d + p) M) :
    Fin (d + p) → ClosedRealOneOneForm (d + p) M :=
  fun i => if (i : ℕ) < p then α else W.form

theorem thetaPlurisubharmonic_concentratedSlots (W : KahlerBackground (d + p) M)
    {α : ClosedRealOneOneForm (d + p) M} (hα : ThetaPlurisubharmonic α.val (fun _ => 0)) (i : Fin (d + p)) :
    ThetaPlurisubharmonic (concentratedSlots W α i).val (fun _ => 0) := by
  simp only [concentratedSlots]
  split_ifs
  · exact hα
  · exact (LocalPotentials.thetaPlurisubharmonic_zero_iff _).mpr W.isSemipositive

/-- The trace measure of `[M] ∧ α^p` is the global mixed measure of `(α, …, α, W, …, W)`. -/
theorem traceMeasure_smoothCurrent_eq (W : KahlerBackground (d + p) M)
    {α : ClosedRealOneOneForm (d + p) M} (hα : ThetaPlurisubharmonic α.val (fun _ => 0)) :
    CurrentTraceMeasure.traceMeasure W (smoothCurrent W fun _ : Fin p => α)
        (isPositive_smoothCurrent W _ fun _ => hα) =
      globalMixedMeasure (concentratedSlots W α) (fun _ _ => 0)
        (thetaPlurisubharmonic_concentratedSlots W hα) := by
  have hcongr : ∀ (S S' : ProductCurrent (d + p) M d) (hS : IsPositive S) (hS' : IsPositive S'),
      S = S' → CurrentTraceMeasure.traceMeasure W S hS = CurrentTraceMeasure.traceMeasure W S' hS' := by
    rintro S S' hS hS' rfl
    rfl
  have h := traceMeasure_smoothCurrent_eq_of_slots W (concentratedSlots W α)
    (thetaPlurisubharmonic_concentratedSlots W hα) fun i hi => by
      simp only [concentratedSlots]
      rw [if_neg (by omega)]
  rw [← h]
  refine hcongr _ _ _ _ ?_
  congr 1
  funext j
  simp only [concentratedSlots]
  rw [if_pos (by rw [Fin.val_castLE]; exact j.isLt)]

/-- The mass of `[M] ∧ (A + ddᶜg)^p` is `∫ A^p ∧ W^d` (class invariance). -/
theorem mass_smoothCurrent_eq (W : KahlerBackground (d + p) M) (A : ClosedRealOneOneForm (d + p) M)
    {g : M → ℝ} (hg : ChartSmooth (n := d + p) g)
    (hα : ThetaPlurisubharmonic (A + ddcClosedForm g hg).val (fun _ => 0)) :
    mass W (smoothCurrent W fun _ : Fin p => A + ddcClosedForm g hg) =
      slotIntegral W (fun i : Fin (d + p) => if (i : ℕ) < p then A else W.form) := by
  rw [← CurrentTraceMeasure.traceMeasure_real_univ W _ (isPositive_smoothCurrent W _ fun _ => hα),
    traceMeasure_smoothCurrent_eq W hα,
    globalMixedMeasure_real_univ_eq_integral W _ (thetaPlurisubharmonic_concentratedSlots W hα),
    ← slotIntegral]
  have h0 := slotIntegral_ite_add_ddc W p A W.form hg (f := fun _ => (0 : ℝ))
    (fun _ => contDiffOn_const)
  rw [ddcClosedForm_zero, add_zero] at h0
  rw [← h0]
  rfl

/-- **The trace measure of one concentrated current** `[M] ∧ α^p` on `S`, with the explicit
constant of `le_mixedMeasure_concentrated`. -/
theorem le_traceMeasure_smoothCurrent (W : KahlerBackground (d + p) M)
    (A : ClosedRealOneOneForm (d + p) M) {g : M → ℝ} (hg : ChartSmooth (n := d + p) g)
    {f : M → ℝ} (hf : ChartSmooth (n := d + p) f)
    (hαK : (A + ddcClosedForm g hg).val.IsKahler)
    (hhalf : ((1 / 2 : ℝ) • W.form + ddcClosedForm f hf).val.IsSemipositive)
    {c : ℝ} (hc : 0 < c)
    (hMA : ∀ (e : ComplexChart (d + p) M) (z : ComplexModel (d + p)), z ∈ e.val.target →
      actualTopPowerDensity ((A + ddcClosedForm g hg).val.coeff e z) =
        c * actualTopPowerDensity ((W.form + ddcClosedForm f hf).val.coeff e z))
    {S : Set M} {δ P₀ M₀ : ℝ} (hδ : 0 < δ) (hM₀ : 0 < M₀)
    (h₁ : ∀ i, ThetaPlurisubharmonic ((fun i : Fin (d + p) =>
      if (i : ℕ) < p then W.form + ddcClosedForm f hf else W.form) i).val (fun _ => 0))
    (hconc : ENNReal.ofReal δ ≤ globalMixedMeasure (fun i : Fin (d + p) =>
      if (i : ℕ) < p then W.form + ddcClosedForm f hf else W.form) (fun _ _ => 0) h₁ S)
    (hvol : P₀ ≤ slotIntegral W fun _ => A)
    (hmass : slotIntegral W (fun i : Fin (d + p) => if (i : ℕ) < d then A else W.form) ≤ M₀)
    (hα : ThetaPlurisubharmonic (A + ddcClosedForm g hg).val (fun _ => 0)) :
    ENNReal.ofReal (P₀ / (kahlerVolume W).real univ * δ ^ 2 /
        (4 * 2 ^ d * (d + p).factorial * M₀)) ≤
      CurrentTraceMeasure.traceMeasure W (smoothCurrent W fun _ : Fin p => A + ddcClosedForm g hg)
        (isPositive_smoothCurrent W _ fun _ => hα) S := by
  rw [traceMeasure_smoothCurrent_eq W hα]
  exact le_mixedMeasure_concentrated W A hg hf hαK hhalf hc hMA hδ hM₀ h₁
    (thetaPlurisubharmonic_concentratedSlots W hα) hconc hvol hmass

end Level

/-! ### The weak limit -/

section Limit

variable {d p : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel (d + p)) M]
  [IsComplexManifold (d + p) M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]

/-- **The concentrated current** (`bou:concentrated-current`; Boucksom 4.12, dp04 2.6): for
Kähler forms `α_k = A k + ddᶜ g_k` with `α_k^N = c_k (W + ddᶜ f_k)^N`, `W + ddᶜ f_k ≥ W/2`,
`∫_{S k} (W + ddᶜ f_k)^p ∧ W^d ≥ δ`, `∫ (A k)^N ≥ P₀`, `∫ (A k)^d ∧ W^p ≤ M₀` and
`∫ (A k)^p ∧ W^d ≤ M₁`, and closed sets `F j` decreasing with `S k ⊆ F j` for `j ≤ k`, the
currents `[M] ∧ α_k^p` converge along an ultrafilter finer than `atTop` to a closed positive
current `Θ` of mass `≤ M₁` with
`σ_Θ(⋂ F_j) ≥ (P₀ / vol W) δ² / (4 · 2^d · N! · M₀)`. -/
theorem exists_concentratedCurrent (W : KahlerBackground (d + p) M)
    (A : ℕ → ClosedRealOneOneForm (d + p) M) (g : ℕ → M → ℝ)
    (hg : ∀ k, ChartSmooth (n := d + p) (g k)) (f : ℕ → M → ℝ)
    (hf : ∀ k, ChartSmooth (n := d + p) (f k))
    (hαK : ∀ k, (A k + ddcClosedForm (g k) (hg k)).val.IsKahler)
    (hhalf : ∀ k, ((1 / 2 : ℝ) • W.form + ddcClosedForm (f k) (hf k)).val.IsSemipositive)
    (c : ℕ → ℝ) (hc : ∀ k, 0 < c k)
    (hMA : ∀ k (e : ComplexChart (d + p) M) (z : ComplexModel (d + p)), z ∈ e.val.target →
      actualTopPowerDensity ((A k + ddcClosedForm (g k) (hg k)).val.coeff e z) =
        c k * actualTopPowerDensity ((W.form + ddcClosedForm (f k) (hf k)).val.coeff e z))
    (S : ℕ → Set M) {δ P₀ M₀ M₁ : ℝ} (hδ : 0 < δ) (hM₀ : 0 < M₀)
    (h₁ : ∀ k i, ThetaPlurisubharmonic ((fun i : Fin (d + p) =>
      if (i : ℕ) < p then W.form + ddcClosedForm (f k) (hf k) else W.form) i).val (fun _ => 0))
    (hconc : ∀ k, ENNReal.ofReal δ ≤ globalMixedMeasure (fun i : Fin (d + p) =>
      if (i : ℕ) < p then W.form + ddcClosedForm (f k) (hf k) else W.form) (fun _ _ => 0)
        (h₁ k) (S k))
    (hvol : ∀ k, P₀ ≤ slotIntegral W fun _ => A k)
    (hmass : ∀ k,
      slotIntegral W (fun i : Fin (d + p) => if (i : ℕ) < d then A k else W.form) ≤ M₀)
    (hmassp : ∀ k,
      slotIntegral W (fun i : Fin (d + p) => if (i : ℕ) < p then A k else W.form) ≤ M₁)
    {F : ℕ → Set M} (hF : ∀ j, IsClosed (F j)) (hanti : Antitone F)
    (hSF : ∀ j k, j ≤ k → S k ⊆ F j) :
    ∃ (U : Ultrafilter ℕ) (Θ : ProductCurrent (d + p) M d) (hΘ : IsPositive Θ),
      (U : Filter ℕ) ≤ atTop ∧ ClosedProductCurrents.IsClosedCurrent Θ ∧ mass W Θ ≤ M₁ ∧
      (∀ φ, Tendsto (fun k => smoothCurrent W (fun _ : Fin p => A k + ddcClosedForm (g k) (hg k)) φ)
        (U : Filter ℕ) (𝓝 (Θ φ))) ∧
      P₀ / (kahlerVolume W).real univ * δ ^ 2 / (4 * 2 ^ d * (d + p).factorial * M₀) ≤
        (CurrentTraceMeasure.traceMeasure W Θ hΘ).real (⋂ j, F j) := by
  set δ' : ℝ := P₀ / (kahlerVolume W).real univ * δ ^ 2 / (4 * 2 ^ d * (d + p).factorial * M₀)
    with hδ'def
  have hαpsh : ∀ k, ThetaPlurisubharmonic (A k + ddcClosedForm (g k) (hg k)).val (fun _ => 0) :=
    fun k => (LocalPotentials.thetaPlurisubharmonic_zero_iff _).mpr
      (KahlerBackground.isSemipositive ⟨_, hαK k⟩)
  set T : ℕ → ProductCurrent (d + p) M d := fun k =>
    smoothCurrent W fun _ : Fin p => A k + ddcClosedForm (g k) (hg k) with hTdef
  have hTpos : ∀ k, IsPositive (T k) := fun k => isPositive_smoothCurrent W _ fun _ => hαpsh k
  have hTclosed : ∀ k, ClosedProductCurrents.IsClosedCurrent (T k) := fun k =>
    SmoothCurrentClosedness.isClosedCurrent_smoothCurrent W _
  have hTmass : ∀ k, mass W (T k) ≤ M₁ := fun k => by
    rw [hTdef, mass_smoothCurrent_eq W (A k) (hg k) (hαpsh k)]
    exact hmassp k
  obtain ⟨U, Θ, hUle, hΘpos, hΘmass, hlim⟩ :=
    exists_ultrafilter_tendsto W (atTop : Filter ℕ) T hTpos (Eventually.of_forall hTmass)
  have hΘc : ClosedProductCurrents.IsClosedCurrent Θ :=
    ClosedProductCurrents.isClosedCurrent_of_tendsto hTclosed hlim
  have hlow : ∀ k, ENNReal.ofReal δ' ≤ CurrentTraceMeasure.traceMeasure W (T k) (hTpos k) (S k) :=
    fun k => le_traceMeasure_smoothCurrent W (A k) (hg k) (hf k) (hαK k) (hhalf k) (hc k) (hMA k)
      hδ hM₀ (h₁ k) (hconc k) (hvol k) (hmass k) (hαpsh k)
  have hδF : ∀ j, ∀ᶠ k in (U : Filter ℕ),
      δ' ≤ (CurrentTraceMeasure.traceMeasure W (T k) (hTpos k)).real (F j) := by
    intro j
    filter_upwards [hUle (eventually_ge_atTop j)] with k hk
    rcases le_or_gt δ' 0 with hneg | hpos
    · exact hneg.trans measureReal_nonneg
    rw [measureReal_def, ← ENNReal.toReal_ofReal hpos.le]
    exact ENNReal.toReal_mono (measure_ne_top _ _) ((hlow k).trans (measure_mono (hSF j k hk)))
  have hΔ := DiagonalSupport.le_traceMeasure_iInter_of_tendsto W hTpos hΘpos
    (Eventually.of_forall hTmass) hlim hF hanti hδF
  exact ⟨U, Θ, hΘpos, hUle, hΘc, hΘmass, hlim, hΔ⟩

end Limit

end SGPT.Foundations.Analysis.Pending.ConcentratedCurrent
