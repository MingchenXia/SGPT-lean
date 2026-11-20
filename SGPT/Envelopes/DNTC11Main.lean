import SGPT.Envelopes.DNTC11Contact
import Mathlib.MeasureTheory.Measure.Decomposition.IntegralRNDeriv

/-!
# The Monge–Ampère measure of a `C^{1,1̄}` obstacle and the contact formula

Lane S53 (`claude-dnt-c11`).  On a compact complex manifold `X` of dimension `n` with a Kähler form
`ω`, for a closed real `(1,1)`-form `θ` and a continuous `f` with bounded complex Hessian:

* `c11TopMeasure ω θ f` (`θ_fⁿ`, positive part): the measure `ρ_f ωⁿ` where the density `ρ_f` is the
  value at `t = 0` of the polynomial `t ↦ d⟨(θ + tω + ddᶜf)ⁿ⟩/dωⁿ`, read off by Lagrange
  interpolation at `t = T, …, T + n` from the Monge–Ampère measures of the `(θ + tω)`-psh function
  `f` (`exists_isThetaPshPotential_add_smul`).  `DNTC11Density` proves that `ρ_f ωⁿ` is
  `(n!/πⁿ) det(ρ + f)_{j k̄}` in every chart (`c11TopMeasure_image_eq`), i.e. the measure of the
  `L^∞` density of the distributional complex Hessian, and that it is the non-pluripolar
  Monge–Ampère measure when `f` is `θ`-psh.
* `diagonalPotentialMeasure_restrict_contact_eq` (**`thm:DNTcontact`**, diagonal case, for
  obstacles with bounded complex Hessian): `φ ∈ PSH(X, θ)`, `φ ≤ f`, `E = {φ = f}`:
  `𝟙_E θ_φⁿ = 𝟙_E θ_fⁿ`.

## Proof of the contact formula

For `t ≥ T` the obstacle `f` is `(θ + tω)`-psh, and the contact formula for psh obstacles
(`DNTC11Contact`) gives `⟨(θ + tω + ddᶜφ)ⁿ⟩(A) = ⟨(θ + tω + ddᶜf)ⁿ⟩(A)` for `A ⊆ E`.  Both sides are
polynomials of degree `≤ n` in `t` (multilinearity of non-pluripolar products in the background,
`diagonalPotentialMeasure_add_smul_toReal_eq_sum`), so their Lagrange extrapolations to `t = 0`
coincide: `∫_A ρ_f ωⁿ = θ_φⁿ(A)` for every `A ⊆ E`.  Hence `ρ_f ≥ 0` almost everywhere on `E` and
`θ_fⁿ = ρ_f⁺ ωⁿ` agrees with `θ_φⁿ` on `E`.  This replaces the book's Steps 2–3 (which use the
`C^{1,1̄}` regularity of envelopes `prop:DR16_C11bar` and `lma:DNTroof`) by the polynomial trick of
its Step 2.2 applied with the psh obstacles `f` in the classes `θ + tω`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory TopologicalSpace Metric
open scoped Topology ContDiff ENNReal

namespace SGPT.Envelopes.DNTC11

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.GlobalPotentialPatches
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.MongeAmpere
open SGPT.Foundations.Analysis.Pending.GlobalNonPluripolar
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Foundations.Analysis.Pending.IntegrationCurrent
open SGPT.Foundations.Analysis.Pending.ProductTestForms
open SGPT.Foundations.Analysis.Pending.TopDegreeDensity
open SGPT.Foundations.Analysis.Pending.ManifoldTubePositivity
open SGPT.Foundations.Analysis.Pending.SmoothMixedMeasureDensity
open SGPT.Okounkov.TranscendentalWNReg

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-! ### Absolute continuity -/

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
/-- The Kähler volume has a positive chart density. -/
theorem chartDensity_kahler_pos (w : KahlerBackground n M) (e : ComplexChart n M)
    {z : ComplexModel n} (hz : z ∈ e.val.target) :
    0 < chartDensity (fun _ : Fin n => w.form) e z := by
  have hden : topDensity ((formPow w.form.val n).coeff e z) =
      actualMixedTopDensity fun _ : Fin n => w.form.val.coeff e z := by
    rw [formPow_coeff, topDensity_formPower, actualMixedTopDensity_const]
  have hpos := topDensity_formPow_pos w.isKahler.1 hz
  rw [hden] at hpos
  exact ENNReal.ofReal_pos.mpr hpos

/-- **The Monge–Ampère measure of a psh obstacle with bounded complex Hessian is absolutely
continuous** with respect to `ωⁿ`. -/
theorem diagonalPotentialMeasure_absolutelyContinuous (w : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) {f : M → ℝ} (hf : HasBoundedComplexHessian (n := n) f)
    (hfpsh : IsThetaPshPotential θ.val (fun x => (f x : EReal))) :
    diagonalPotentialMeasure θ (fun x => (f x : EReal)) hfpsh ≪ kahlerVolume w := by
  classical
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h1 : diagonalPotentialMeasure θ (fun x => (f x : EReal)) hfpsh = kahlerVolume w :=
      AmbientMassBackgroundMonotone.globalMixedMeasure_congr_tuples (Subsingleton.elim _ _)
        (Subsingleton.elim _ _) _ (fun _ =>
          ((LocalPotentials.isThetaPshPotential_zero_iff w.form).mpr w.isSemipositive).1)
    rw [h1]
  refine Measure.AbsolutelyContinuous.mk fun S hS hS0 => ?_
  have hω : ∀ _ : Fin n, ThetaPlurisubharmonic w.form.val (fun _ => 0) := fun _ =>
    ((LocalPotentials.isThetaPshPotential_zero_iff w.form).mpr w.isSemipositive).1
  have hvol : kahlerVolume w = globalMixedMeasure (fun _ : Fin n => w.form) (fun _ _ => 0) hω := rfl
  have hloc : ∀ x : M, ∃ N : Set M, IsOpen N ∧ x ∈ N ∧
      diagonalPotentialMeasure θ (fun x => (f x : EReal)) hfpsh (S ∩ N) = 0 := by
    intro x
    set e := complexChartAt (n := n) x with he
    have hxe : x ∈ e.val.source := mem_complexChartAt_source x
    have hz₀ : e.val x ∈ e.val.target := e.val.map_source hxe
    obtain ⟨W, ρ, hz₀W, hρ⟩ :=
      Pending.LocalPotentials.closedRealOneOne_hasLocalPotentials θ e (e.val x) hz₀
    obtain ⟨h, hh⟩ := hf.exists_density_add e hρ.1 hρ.2.1 hρ.2.2.1
    set N := e.val.source ∩ e.val ⁻¹' W with hN
    refine ⟨N, e.val.isOpen_inter_preimage hρ.1, ⟨hxe, hz₀W⟩, ?_⟩
    have hSN : S ∩ N ⊆ e.val.source := fun y hy => hy.2.1
    set K := e.val '' (S ∩ N) with hK
    have hKeq : K = e.val.target ∩ e.val.symm ⁻¹' (S ∩ N) :=
      e.val.image_eq_target_inter_inv_preimage hSN
    have hKm : MeasurableSet K := by
      rw [hKeq]
      exact measurableSet_inter_preimage_of_continuousOn e.val.open_target.measurableSet
        e.val.continuousOn_symm (hS.inter (e.val.isOpen_inter_preimage hρ.1).measurableSet)
    have hKW : K ⊆ W := by
      rintro _ ⟨y, hy, rfl⟩
      exact hy.2.2
    have hKt : K ⊆ e.val.target := hKW.trans hρ.2.1
    have hSK : S ∩ N = e.val.symm '' K := (e.val.symm_image_image_of_subset_source hSN).symm
    -- `K` is Lebesgue-null
    have hvolK : volume K = 0 := by
      have h0 : kahlerVolume w (e.val.symm '' K) = 0 :=
        measure_mono_null (hSK ▸ inter_subset_left) hS0
      have hint := setLIntegral_image_eq hω e hKm hKt (g := fun _ => (1 : ℝ≥0∞)) measurable_const
      rw [← hvol, setLIntegral_const, one_mul, h0] at hint
      simp only [mul_one] at hint
      have hae : (fun z => chartDensity (fun _ : Fin n => w.form) e z) =ᵐ[volume.restrict K] 0 :=
        (lintegral_eq_zero_iff' (((continuousOn_chartDensity _ e).mono hKt).aemeasurable hKm)).mp
          hint.symm
      rw [measure_eq_zero_iff_ae_notMem]
      filter_upwards [(ae_restrict_iff' hKm).mp hae] with z hz hzK
      have h1 := hz hzK
      simp only [Pi.zero_apply] at h1
      exact (chartDensity_kahler_pos w e (hKt hzK)).ne' h1
    rw [hSK, diagonalPotentialMeasure_image_eq_density hn θ hfpsh hρ hh hKW]
    exact setLIntegral_measure_zero K _ hvolK
  choose N hNo hxN hN using hloc
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover N hNo
    (fun x _ => mem_iUnion.mpr ⟨x, hxN x⟩)
  refine measure_mono_null (show S ⊆ ⋃ x ∈ s, S ∩ N x from fun y hy => ?_)
    ((measure_biUnion_null_iff s.countable_toSet).mpr fun x _ => hN x)
  obtain ⟨x, hx, hyx⟩ := mem_iUnion₂.mp (hs (mem_univ y))
  exact mem_iUnion₂.mpr ⟨x, hx, hy, hyx⟩


/-! ### The Monge–Ampère measure of an obstacle with bounded complex Hessian -/

/-- A threshold `T ≥ 1` beyond which `f` is `(θ + tω)`-psh (`1` if there is none). -/
def c11Threshold (w : KahlerBackground n M) (θ : ClosedRealOneOneForm n M) (f : M → ℝ) : ℝ := by
  classical
  exact if h : ∃ T : ℝ, 1 ≤ T ∧ ∀ t : ℝ, T ≤ t →
      IsThetaPshPotential (θ + t • w.form).val (fun x => (f x : EReal)) then
    Classical.choose h else 1

omit [MeasurableSpace M] [BorelSpace M] in
theorem c11Threshold_spec (w : KahlerBackground n M) (θ : ClosedRealOneOneForm n M) {f : M → ℝ}
    (hf : HasBoundedComplexHessian (n := n) f) :
    1 ≤ c11Threshold w θ f ∧ ∀ t : ℝ, c11Threshold w θ f ≤ t →
      IsThetaPshPotential (θ + t • w.form).val (fun x => (f x : EReal)) := by
  have h := exists_isThetaPshPotential_add_smul w θ hf
  unfold c11Threshold
  rw [dif_pos h]
  exact Classical.choose_spec h

/-- `⟨(θ + tω + ddᶜf)ⁿ⟩` when `f` is `(θ + tω)`-psh, `0` otherwise. -/
def bumpMeasure (w : KahlerBackground n M) (θ : ClosedRealOneOneForm n M) (f : M → ℝ) (t : ℝ) :
    Measure M := by
  classical
  exact if h : IsThetaPshPotential (θ + t • w.form).val (fun x => (f x : EReal)) then
    diagonalPotentialMeasure (θ + t • w.form) _ h else 0

omit [BorelSpace M] in
theorem bumpMeasure_eq (w : KahlerBackground n M) (θ : ClosedRealOneOneForm n M) {f : M → ℝ}
    {t : ℝ} (h : IsThetaPshPotential (θ + t • w.form).val (fun x => (f x : EReal))) :
    bumpMeasure w θ f t = diagonalPotentialMeasure (θ + t • w.form) _ h := by
  unfold bumpMeasure
  rw [dif_pos h]

instance isFiniteMeasure_bumpMeasure (w : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (f : M → ℝ) (t : ℝ) : IsFiniteMeasure (bumpMeasure w θ f t) := by
  unfold bumpMeasure
  split_ifs with h
  · exact GlobalNonPluripolar.globalMixedMeasure_isFiniteMeasure w fun _ : Fin n => h.1
  · infer_instance

theorem integrable_toReal_rnDeriv_bumpMeasure (w : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) (f : M → ℝ) (t : ℝ) :
    Integrable (fun x => ((bumpMeasure w θ f t).rnDeriv (kahlerVolume w) x).toReal)
      (kahlerVolume w) :=
  Measure.integrable_toReal_rnDeriv

/-- **The density `(θ + ddᶜf)ⁿ/ωⁿ`** of an obstacle with bounded complex Hessian: the value at
`t = 0` of the polynomial `t ↦ d⟨(θ + tω + ddᶜf)ⁿ⟩/dωⁿ`, computed by Lagrange interpolation from
`t = T, …, T + n`, `T = c11Threshold ω θ f`.  In every chart it is
`det(Θ + ddᶜf)/det Ω`, the ratio of the densities of the distributional complex Hessians
(`DNTC11Density`). -/
def c11Ratio (w : KahlerBackground n M) (θ : ClosedRealOneOneForm n M) (f : M → ℝ) (x : M) : ℝ :=
  ∑ k : Fin (n + 1), lagWeight (c11Threshold w θ f) k *
    ((bumpMeasure w θ f (lagNode (c11Threshold w θ f) k)).rnDeriv (kahlerVolume w) x).toReal

/-- **The Monge–Ampère measure `θ_fⁿ = (θ + ddᶜf)ⁿ`** of an obstacle `f` with bounded complex
Hessian: the measure `max((θ + ddᶜf)ⁿ/ωⁿ, 0) ωⁿ` (the positive part of the absolutely continuous
signed measure; on contact sets it is the measure itself, see
`diagonalPotentialMeasure_restrict_contact_eq`). -/
def c11TopMeasure (w : KahlerBackground n M) (θ : ClosedRealOneOneForm n M) (f : M → ℝ) :
    Measure M :=
  (kahlerVolume w).withDensity fun x => ENNReal.ofReal (c11Ratio w θ f x)

omit [BorelSpace M] in
theorem measurable_c11Ratio (w : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (f : M → ℝ) : Measurable (c11Ratio w θ f) :=
  Finset.measurable_sum _ fun _ _ =>
    measurable_const.mul (Measure.measurable_rnDeriv _ _).ennreal_toReal

theorem integrable_c11Ratio (w : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (f : M → ℝ) : Integrable (c11Ratio w θ f) (kahlerVolume w) :=
  integrable_finsetSum _ fun _ _ =>
    (integrable_toReal_rnDeriv_bumpMeasure w θ f _).const_mul _

/-- On subsets of the contact set, `∫_A (θ + ddᶜf)ⁿ/ωⁿ ωⁿ = θ_φⁿ(A)`. -/
theorem setIntegral_c11Ratio_eq (w : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    {u : M → EReal} (hu : IsThetaPshPotential θ.val u) {f : M → ℝ}
    (hf : HasBoundedComplexHessian (n := n) f) (hle : ∀ x, u x ≤ (f x : EReal)) {A : Set M}
    (hA : MeasurableSet A) (hAE : A ⊆ {x | u x = (f x : EReal)}) :
    ∫ x in A, c11Ratio w θ f x ∂kahlerVolume w = (diagonalPotentialMeasure θ u hu A).toReal := by
  classical
  obtain ⟨hT1, hT⟩ := c11Threshold_spec w θ hf
  set T := c11Threshold w θ f with hTdef
  have hnode : ∀ k : Fin (n + 1), T ≤ lagNode T k := fun k => by
    simp only [lagNode]
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ (k : ℕ))]
  have hpos : ∀ k : Fin (n + 1), 0 < lagNode T k := fun k => by linarith [hnode k]
  have hfk : ∀ k : Fin (n + 1), IsThetaPshPotential (θ + lagNode T k • w.form).val
      (fun x => (f x : EReal)) := fun k => hT _ (hnode k)
  have huk : ∀ k : Fin (n + 1), IsThetaPshPotential (θ + lagNode T k • w.form).val u := fun k =>
    ⟨NefBoundedMixedMass.thetaPlurisubharmonic_add_of_isSemipositive hu.1
      (NefBoundedMixedMass.isSemipositive_smul w.isSemipositive (hpos k).le), hu.2⟩
  have hint : ∀ k : Fin (n + 1), Integrable
      (fun x => ((bumpMeasure w θ f (lagNode T k)).rnDeriv (kahlerVolume w) x).toReal)
      (kahlerVolume w) := fun k => integrable_toReal_rnDeriv_bumpMeasure w θ f _
  -- the contact formula at the nodes
  have hcontact : ∀ k : Fin (n + 1),
      bumpMeasure w θ f (lagNode T k) A =
        diagonalPotentialMeasure (θ + lagNode T k • w.form) u (huk k) A := by
    intro k
    rw [bumpMeasure_eq w θ (hfk k)]
    rcases Nat.eq_zero_or_pos n with hn0 | hn
    · subst hn0
      exact congrArg (fun μ : Measure M => μ A)
        (AmbientMassBackgroundMonotone.globalMixedMeasure_congr_tuples (Subsingleton.elim _ _)
          (Subsingleton.elim _ _) _ _)
    · have h := diagonalPotentialMeasure_restrict_contact_eq_of_psh w hn _ (huk k) hf (hfk k) hle
      have h2 := congrArg (fun μ : Measure M => μ A) h
      simp only [Measure.restrict_apply hA, inter_eq_left.mpr hAE] at h2
      exact h2.symm
  have hrn : ∀ k : Fin (n + 1),
      ∫ x in A, ((bumpMeasure w θ f (lagNode T k)).rnDeriv (kahlerVolume w) x).toReal
          ∂kahlerVolume w = (bumpMeasure w θ f (lagNode T k) A).toReal := by
    intro k
    have hac : bumpMeasure w θ f (lagNode T k) ≪ kahlerVolume w := by
      rw [bumpMeasure_eq w θ (hfk k)]
      exact diagonalPotentialMeasure_absolutelyContinuous w _ hf (hfk k)
    rw [Measure.setIntegral_toReal_rnDeriv hac A, measureReal_def]
  simp only [c11Ratio]
  rw [integral_finsetSum _ fun k _ => (hint k).integrableOn.const_mul _]
  simp_rw [integral_const_mul]
  simp_rw [hrn, hcontact]
  have hexp : ∀ k : Fin (n + 1),
      (diagonalPotentialMeasure (θ + lagNode T k • w.form) u (huk k) A).toReal =
        ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset, lagNode T k ^ S.card *
          (globalMixedMeasure (slotForm w θ ∅ S 1) (slotPot u S)
            (slot_thetaPlurisubharmonic w θ hu.1 ∅ S zero_le_one) A).toReal := fun k =>
    diagonalPotentialMeasure_add_smul_toReal_eq_sum w θ hu (hpos k) (huk k) A
  simp_rw [hexp]
  rw [sum_lagWeight_mul_sum_pow T, slotMeasure_empty w θ hu A]

/-- **The Di Nezza–Trapani contact formula** (book `thm:DNTcontact`, diagonal case
`θᵢ = θ`, `φᵢ = φ`, `fᵢ = f`) for obstacles with bounded complex Hessian.  Let `X` be a compact
complex manifold with a Kähler form `ω`, `θ` a closed real `(1,1)`-form, `φ ∈ PSH(X, θ)` and `f`
continuous with bounded complex Hessian, `φ ≤ f`, `E = {φ = f}`.  Then
`𝟙_E ⟨(θ + ddᶜφ)ⁿ⟩ = 𝟙_E (θ + ddᶜf)ⁿ`; moreover the density of `(θ + ddᶜf)ⁿ` is nonnegative
almost everywhere on `E`, so no positive part is taken there. -/
theorem diagonalPotentialMeasure_restrict_contact_eq (w : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) {u : M → EReal} (hu : IsThetaPshPotential θ.val u) {f : M → ℝ}
    (hf : HasBoundedComplexHessian (n := n) f) (hle : ∀ x, u x ≤ (f x : EReal)) :
    (diagonalPotentialMeasure θ u hu).restrict {x | u x = (f x : EReal)} =
      (c11TopMeasure w θ f).restrict {x | u x = (f x : EReal)} := by
  set E := {x | u x = (f x : EReal)} with hE
  have hEm : MeasurableSet E := (isClosed_contact_of_continuous hu.1 hf.1 hle).measurableSet
  have hgi := integrable_c11Ratio w θ f
  have hnn : ∀ᵐ x ∂(kahlerVolume w).restrict E, 0 ≤ c11Ratio w θ f x := by
    refine ae_nonneg_of_forall_setIntegral_nonneg hgi.integrableOn fun s hs _ => ?_
    rw [Measure.restrict_restrict hs, setIntegral_c11Ratio_eq w θ hu hf hle (hs.inter hEm)
      inter_subset_right]
    exact ENNReal.toReal_nonneg
  ext A hA
  rw [Measure.restrict_apply hA, Measure.restrict_apply hA, c11TopMeasure,
    withDensity_apply _ (hA.inter hEm), ← ofReal_integral_eq_lintegral_ofReal hgi.integrableOn
      (ae_restrict_of_ae_restrict_of_subset inter_subset_right hnn),
    setIntegral_c11Ratio_eq w θ hu hf hle (hA.inter hEm) inter_subset_right]
  have hfin : diagonalPotentialMeasure θ u hu (A ∩ E) ≠ ⊤ :=
    (GlobalNonPluripolar.globalMixedMeasure_apply_lt_top w (fun _ : Fin n => hu.1) (A ∩ E)).ne
  exact (ENNReal.ofReal_toReal hfin).symm

/-- The density of `(θ + ddᶜf)ⁿ` is nonnegative almost everywhere on the contact set. -/
theorem ae_c11Ratio_nonneg_of_contact (w : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    {u : M → EReal} (hu : IsThetaPshPotential θ.val u) {f : M → ℝ}
    (hf : HasBoundedComplexHessian (n := n) f) (hle : ∀ x, u x ≤ (f x : EReal)) :
    ∀ᵐ x ∂(kahlerVolume w).restrict {x | u x = (f x : EReal)}, 0 ≤ c11Ratio w θ f x := by
  have hEm : MeasurableSet {x | u x = (f x : EReal)} :=
    (isClosed_contact_of_continuous hu.1 hf.1 hle).measurableSet
  refine ae_nonneg_of_forall_setIntegral_nonneg (integrable_c11Ratio w θ f).integrableOn
    fun s hs _ => ?_
  rw [Measure.restrict_restrict hs, setIntegral_c11Ratio_eq w θ hu hf hle (hs.inter hEm)
    inter_subset_right]
  exact ENNReal.toReal_nonneg

end SGPT.Envelopes.DNTC11
