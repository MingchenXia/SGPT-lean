import SGPT.Okounkov.TranscendentalWNDeformationMetric
import SGPT.Okounkov.TranscendentalSliceClasses
import SGPT.Foundations.Analysis.Pending.BlowupKahler
import SGPT.Foundations.Analysis.Pending.HolomorphicBoundedQuotient
import SGPT.Foundations.Analysis.Pending.MeteredDivisorPositivity

/-!
# Metrics of the exceptional divisor and the Kähler class `μ^*{ω} - t{ℰ}`

Blueprint `tok-wn-def:divisor-class` and `tok-wn-def:kahler-class` (`claude-tok-wn-def`); the
input `tok:ext-blowup-kahler` (Blanchard) of the route `tok-wn-def:beta-big-route`.

* `support_eq_of_isDivisorMetric`: the support (pole set of the weight) of a metric of an
  effective divisor `D` is the support of `D`.
* `bottChernRel_curvature_of_isDivisorMetric`: two metrics `E₁`, `E₂` of the same effective
  divisor whose support is closed with empty interior have cohomologous curvatures,
  `Θ_{E₂} = Θ_{E₁} + dd^c f` with `f = ψ_{E₂} - ψ_{E₁}` smooth.  This generalizes SLICE's
  `TranscendentalSlice.ofRepresentative_curvature_eq_of_divisorMetric` (stated for closed
  *connected* submanifolds) to supports that are only closed with empty interior, which is what the
  exceptional divisor of a blow-up provides; the proof is the same (local generators differ by
  holomorphic units, density of the complement of the support).
* `eventually_blanchardWeight_le`, `eventually_le_blanchardWeight`: for a blow-up `π : Y → M`
  along `C` and the Blanchard weight `U` of `C`, `U ∘ π ≍ |σ|²` near every point of `π⁻¹ C`, for a
  local generator `σ` of the exceptional ideal `π^* 𝓘_C` (the flattening coordinates of `C`
  lie in `𝓘_C`, and generate it by Hadamard's lemma).
* `isDivisorMetric_blanchard`: hence (Riemann extension of the bounded quotient) the metered
  divisor `div (U ∘ π)` of any factorization of `U ∘ π` is a metric of the exceptional divisor.
* `exists_kahler_bottChernRel`: for a compact Kähler `(M, ω)`, a compact blow-up `π : Y → M` and
  ANY metric `E` of the exceptional divisor, there are a Kähler form `κ` on `Y` and `t > 0` with
  `κ = π^*ω - t Θ_E + dd^c h` (Blanchard's form `π^*ω + ε Θ_{div U}`, with
  `Θ_{div U} = -Θ_E + dd^c (·)` by the comparison of the two metrics).
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalWN

open Set Filter
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.FirstPass.NumericalRestrictedVolumeScaffold
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.BlanchardWeight
open SGPT.Foundations.Analysis.Pending.BlowupFlatCoordinates
open SGPT.Foundations.Analysis.Pending.FactorizedWeightForm

/-! ### The support of a divisor metric -/

section Support

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

omit [IsComplexManifold n M] in
/-- A holomorphic germ lies in the principal ideal it generates. -/
theorem isInSpanAt_self {g : M → ℂ} {x : M} (hg : HolomorphicAt n g x) :
    IsInSpanAt (n := n) (· = g) x g :=
  isInSpanAt_of_eq_mul rfl hg (holomorphicAt_const 1) (Eventually.of_forall fun _ => by simp)

/-- **The support of a metric of `D` is the support of `D`.** -/
theorem support_eq_of_isDivisorMetric {D : EffectiveDivisor n M}
    {E : MeteredEffectiveQDivisor n M} (hE : DivisorMetric.IsDivisorMetric D E) :
    E.support = D.support := by
  ext x
  obtain ⟨V, hV, hxV, g, hgd, hgen, h, -, hw⟩ := hE x
  have hhol : HolomorphicAt n g x := by
    filter_upwards [hV.mem_nhds hxV] with y hy
    exact (hgd y hy).mdifferentiableAt (hV.mem_nhds hy)
  have hgx : E.weight x = ⊥ ↔ g x = 0 := by
    rw [hw x hxV]
    constructor
    · intro h0
      have : generatorLog (fun _ : Fin 1 => g) x = ⊥ := by
        by_contra hne
        exact (EReal.add_ne_bot_iff.mpr ⟨hne, EReal.coe_ne_bot _⟩) h0
      simpa using this
    · intro h0
      have : generatorLog (fun _ : Fin 1 => g) x = ⊥ := by simp [h0]
      rw [this, EReal.bot_add]
  change E.weight x = ⊥ ↔ ∀ f, D.ideal.mem x f → f x = 0
  rw [hgx]
  constructor
  · intro h0 f hf
    obtain ⟨-, a, -, ha⟩ := isInSpanAt_eq_iff.mp ((hgen x hxV f).mp hf)
    have hfx : f x = a x * g x := ha.self_of_nhds
    rw [hfx, h0, mul_zero]
  · intro hall
    exact hall g ((hgen x hxV g).mpr (isInSpanAt_self hhol))

end Support

/-! ### Two metrics of the same divisor -/

section Comparison

variable {N : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (N + 1)) M] [IsComplexManifold (N + 1) M]

/-- **Local form of the difference of two divisor weights**: near every point the weights of two
metrics of the same divisor differ by a chart-smooth real function (the local generators differ
by a holomorphic unit). -/
theorem exists_local_weight_difference' {W : Set M} (hint : interior W = ∅)
    {D : EffectiveDivisor (N + 1) M}
    {E₁ E₂ : MeteredEffectiveQDivisor (N + 1) M} (hE₁W : E₁.support = W)
    (h₁ : DivisorMetric.IsDivisorMetric D E₁) (h₂ : DivisorMetric.IsDivisorMetric D E₂)
    (x : M) :
    ∃ V : Set M, IsOpen V ∧ x ∈ V ∧ ∃ F : M → ℝ,
      (∀ e : ComplexChart (N + 1) M,
        ContDiffOn ℝ ∞ (fun z => F (e.val.symm z)) (e.val.target ∩ e.val.symm ⁻¹' V)) ∧
      ∀ y ∈ V, E₂.weight y = E₁.weight y + (F y : EReal) := by
  obtain ⟨V₁, hV₁, hxV₁, g₁, hg₁d, hgen₁, k₁, hk₁, hw₁⟩ := h₁ x
  obtain ⟨V₂, hV₂, hxV₂, g₂, hg₂d, hgen₂, k₂, hk₂, hw₂⟩ := h₂ x
  have hg₁nz : ∀ O : Set M, IsOpen O → O ⊆ V₁ → O.Nonempty → ∃ y ∈ O, g₁ y ≠ 0 := by
    intro O hO hOV hne
    have hnot : ¬ O ⊆ W := by
      intro hsub
      obtain ⟨y, hy⟩ := hne
      have : y ∈ interior W := interior_mono hsub (hO.interior_eq.symm ▸ hy)
      rw [hint] at this
      exact this
    obtain ⟨y, hyO, hyW⟩ := not_subset.mp hnot
    refine ⟨y, hyO, fun h0 => hyW ?_⟩
    rw [← hE₁W]
    show E₁.weight y = ⊥
    rw [hw₁ y (hOV hyO)]
    have : generatorLog (fun _ : Fin 1 => g₁) y = ⊥ :=
      (MeteredDivisorSingleGenerator.singleLog_eq_bot_iff g₁ y).mpr h0
    rw [this, EReal.bot_add]
  obtain ⟨V, u, hV, hxV, hVsub, hud, hu0, hgu⟩ :=
    DivisorMetric.exists_unit_of_generators hV₁ hV₂ hg₁d hg₂d hg₁nz hgen₁ hgen₂ hxV₁ hxV₂
  refine ⟨V, hV, hxV, fun y => Real.log (‖u y‖ ^ 2) + k₂ y - k₁ y, ?_, ?_⟩
  · intro e
    have hudiff : MDifferentiableOn 𝓘(ℂ, ComplexModel (N + 1)) 𝓘(ℂ, ℂ) u V :=
      fun y hy => (hud y hy).mdifferentiableWithinAt
    have hU : IsOpen (e.val.target ∩ e.val.symm ⁻¹' V) := e.val.isOpen_inter_preimage_symm hV
    have hlog : ContDiffOn ℝ ∞ (fun z => Real.log (‖u (e.val.symm z)‖ ^ 2))
        (e.val.target ∩ e.val.symm ⁻¹' V) := by
      intro z hz
      have h := MeteredDivisorSmoothOffSupport.contDiffAt_log_normSq hU
        (MeteredDivisorPositivity.differentiableOn_comp_chartSymm e hudiff) hz (hu0 _ hz.2)
      refine (h.congr_of_eventuallyEq ?_).contDiffWithinAt
      filter_upwards with w
      rw [Complex.normSq_eq_norm_sq]
    have hk₁' := (hk₁ e).mono (inter_subset_inter_right _ (preimage_mono
      (hVsub.trans inter_subset_left)))
    have hk₂' := (hk₂ e).mono (inter_subset_inter_right _ (preimage_mono
      (hVsub.trans inter_subset_right)))
    exact (hlog.add hk₂').sub hk₁'
  · intro y hy
    have hy₁ := (hVsub hy).1
    have hy₂ := (hVsub hy).2
    rw [hw₂ y hy₂, hw₁ y hy₁]
    have hprod : generatorLog (fun _ : Fin 1 => g₂) y =
        ((Real.log (‖u y‖ ^ 2) : ℝ) : EReal) + generatorLog (fun _ : Fin 1 => g₁) y := by
      have hval : generatorLog (fun _ : Fin 1 => g₂) y =
          MeteredDivisorSingleGenerator.singleLog (u * g₁) y := by
        show MeteredDivisorSingleGenerator.singleLog g₂ y = _
        rw [MeteredDivisorSingleGenerator.singleLog_eq_log,
          MeteredDivisorSingleGenerator.singleLog_eq_log, hgu y hy]
        rfl
      rw [hval, MeteredDivisorSingleGenerator.singleLog_mul,
        MeteredDivisorSingleGenerator.singleLog]
      congr 1
      exact MeteredDivisorWeightBounds.generatorLog_single_eq_coe (hu0 y hy)
    rw [hprod]
    exact TranscendentalSlice.ereal_coe_add_add_coe _ _ _ _

/-- **The two weights differ by a global chart-smooth function**: `ψ₂ = ψ₁ + f`. -/
theorem exists_chartSmooth_weight_difference' {W : Set M} (hint : interior W = ∅)
    {D : EffectiveDivisor (N + 1) M}
    {E₁ E₂ : MeteredEffectiveQDivisor (N + 1) M} (hE₁W : E₁.support = W)
    (h₁ : DivisorMetric.IsDivisorMetric D E₁) (h₂ : DivisorMetric.IsDivisorMetric D E₂) :
    ∃ f : M → ℝ, ChartSmooth (n := N + 1) f ∧
      ∀ x, E₂.weight x = E₁.weight x + (f x : EReal) := by
  classical
  choose V hV hxV F hF hFw using exists_local_weight_difference' hint hE₁W h₁ h₂
  have hcont : ∀ x, ∀ y ∈ V x, ContinuousAt (F x) y := fun x y hy =>
    MeteredDivisorWeightBounds.continuousAt_of_chartContDiffOn (hV x) (hF x) hy
  have hagree : ∀ x, ∀ y ∈ V x, F y y = F x y := by
    intro x y hy
    refine TranscendentalSlice.eq_of_continuousAt_of_eventuallyEq_off hint (hcont y y (hxV y))
      (hcont x y hy) ?_
    filter_upwards [(hV y).mem_nhds (hxV y), (hV x).mem_nhds hy] with z hz1 hz2 hzW
    have hzE : z ∉ E₁.support := by rw [hE₁W]; exact hzW
    obtain ⟨G, -, hGeq⟩ :=
      MeteredDivisorWeightBounds.exists_real_continuousAt_eventuallyEq_of_notMem_support E₁ hzE
    have hG := Filter.Eventually.self_of_nhds hGeq
    have e1 := hFw y z hz1
    have e2 := hFw x z hz2
    rw [e1, hG, ← EReal.coe_add, ← EReal.coe_add, EReal.coe_eq_coe_iff] at e2
    linarith
  refine ⟨fun x => F x x, ?_, fun x => by rw [hFw x x (hxV x)]⟩
  intro e
  refine contDiffOn_of_locally_contDiffOn fun z hz => ?_
  refine ⟨e.val.target ∩ e.val.symm ⁻¹' V (e.val.symm z),
    e.val.isOpen_inter_preimage_symm (hV _), ⟨hz, hxV _⟩, ?_⟩
  refine ((hF (e.val.symm z) e).mono inter_subset_right).congr fun w hw => ?_
  exact hagree _ _ hw.2.2

/-- **Two metrics of the same divisor have cohomologous curvatures**:
`Θ₁ = Θ₂ + dd^c f` with `f = ψ₂ - ψ₁`, provided the common support is closed with empty
interior. -/
theorem bottChernRel_curvature_of_isDivisorMetric {W : Set M} (hWc : IsClosed W)
    (hint : interior W = ∅) {D : EffectiveDivisor (N + 1) M}
    {E₁ E₂ : MeteredEffectiveQDivisor (N + 1) M} (hE₁W : E₁.support = W)
    (hE₂W : E₂.support = W)
    (h₁ : DivisorMetric.IsDivisorMetric D E₁) (h₂ : DivisorMetric.IsDivisorMetric D E₂) :
    ClosedRealOneOneForm.BottChernRel E₂.curvature E₁.curvature := by
  obtain ⟨f, hf, hfw⟩ := exists_chartSmooth_weight_difference' hint hE₁W h₁ h₂
  refine ⟨f, hf, fun e z hz => ?_⟩
  have hoff : EqOn (fun z => E₁.curvature.val.coeff e z)
      (fun z => E₂.curvature.val.coeff e z + smoothDDC (fun y => f (e.val.symm y)) z)
      (e.val.target ∩ e.val.symm ⁻¹' Wᶜ) := by
    rintro z₀ ⟨hz₀, hz₀W⟩
    have hx : e.val.symm z₀ ∈ e.val.source := e.val.map_target hz₀
    have hx₁ : e.val.symm z₀ ∉ E₁.support := by rw [hE₁W]; exact hz₀W
    have hx₂ : e.val.symm z₀ ∉ E₂.support := by rw [hE₂W]; exact hz₀W
    obtain ⟨W₁, hzW₁, hpot₁⟩ :=
      MeteredDivisorSmoothOffSupport.exists_isSmoothLocalPotential_neg_curvature E₁ hx₁ e hx
    obtain ⟨W₂, hzW₂, hpot₂⟩ :=
      MeteredDivisorSmoothOffSupport.exists_isSmoothLocalPotential_neg_curvature E₂ hx₂ e hx
    rw [e.val.right_inv hz₀] at hzW₁ hzW₂
    have hO : IsOpen (W₁ ∩ W₂) := hpot₁.1.inter hpot₂.1
    have hloc : (fun y => f (e.val.symm y)) =ᶠ[𝓝 z₀]
        fun ζ => (E₂.weight (e.val.symm ζ)).toReal - (E₁.weight (e.val.symm ζ)).toReal := by
      filter_upwards [(e.val.isOpen_inter_preimage_symm hWc.isOpen_compl).mem_nhds
        ⟨hz₀, hz₀W⟩] with ζ hζ
      have hζE : e.val.symm ζ ∉ E₁.support := by rw [hE₁W]; exact hζ.2
      obtain ⟨G, -, hGeq⟩ :=
        MeteredDivisorWeightBounds.exists_real_continuousAt_eventuallyEq_of_notMem_support E₁ hζE
      have hG := Filter.Eventually.self_of_nhds hGeq
      rw [hfw, hG, ← EReal.coe_add, EReal.toReal_coe, EReal.toReal_coe]
      ring
    have hsub := smoothDDC_sub hO (hpot₂.2.2.1.mono inter_subset_right)
      (hpot₁.2.2.1.mono inter_subset_left) (z := z₀) ⟨hzW₁, hzW₂⟩
    have hd₁ := hpot₁.2.2.2 hzW₁
    have hd₂ := hpot₂.2.2.2 hzW₂
    simp only [ClosedRealOneOneForm.coeff_neg] at hd₁ hd₂
    show E₁.curvature.val.coeff e z₀ =
      E₂.curvature.val.coeff e z₀ + smoothDDC (fun y => f (e.val.symm y)) z₀
    rw [smoothDDC_congr hloc, hsub, hd₁, hd₂]
    abel
  exact hoff.of_subset_closure ((E₁.curvature.val.smooth e).continuousOn)
    (((E₂.curvature.val.smooth e).continuousOn).add
      ((LogWeightFactorization.smoothDDC_contDiffOn e.val.open_target (hf e)).continuousOn))
    inter_subset_left (TranscendentalSlice.chart_target_subset_closure hint e) hz

end Comparison

/-! ### The Blanchard weight of the centre is comparable with the exceptional generator -/

section Blanchard

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y] {C : Set M} {π : Y → M}

/-- Pullbacks of germs of `𝓘_C` lie in the exceptional ideal `π^* 𝓘_C`. -/
theorem mem_pullback_vanishingIdeal (hπ : IsBlowupAlong n C π) {y : Y} {f : M → ℂ}
    (hf : (vanishingIdeal (n := n) C).mem (π y) f) :
    (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C)).mem y (f ∘ π) :=
  ⟨hf.1.comp_contMDiff (Eventually.of_forall fun _ => hπ.contMDiff.contMDiffAt), 1,
    fun _ => f ∘ π, fun _ => 1, fun _ => ⟨f, hf, rfl⟩, fun _ => holomorphicAt_const 1,
    Eventually.of_forall fun y => by simp⟩

theorem blanchard_χ_le_one (D : BlanchardData n C) (a : Fin D.m) (y : M) : D.χ a y ≤ 1 := by
  have h := Finset.single_le_sum (f := fun b => D.χ b y) (fun b _ => D.nonneg b y)
    (Finset.mem_univ a)
  rwa [D.sum_one] at h

theorem blanchard_χ_mul_normalWeight_le_weight (D : BlanchardData n C) (a : Fin D.m)
    (y : M) : D.χ a y * D.normalWeight a y ≤ D.weight y :=
  Finset.single_le_sum (f := fun b => D.χ b y * D.normalWeight b y)
    (fun b _ => mul_nonneg (D.nonneg b y) (D.normalWeight_nonneg b y)) (Finset.mem_univ a)

/-- **Upper bound**: `U ∘ π ≤ A |σ|²` near a point of `π⁻¹ C`, `σ` a local generator of the
exceptional ideal. -/
theorem eventually_blanchardWeight_le (hπ : IsBlowupAlong n C π) (D : BlanchardData n C)
    {x : Y} (hx : π x ∈ C) {U : Set Y} (hxU : x ∈ U) {σ : Y → ℂ}
    (hσgen : ∀ y ∈ U, ∀ f, (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C)).mem y f ↔
      IsInSpanAt (n := n) (· = σ) y f) :
    ∃ A : ℝ, ∀ᶠ y in 𝓝 x, D.weight (π y) ≤ A * ‖σ y‖ ^ 2 := by
  classical
  have hπc : ContinuousAt π x := hπ.contMDiff.continuous.continuousAt
  have key : ∀ a : Fin D.m, ∃ A : ℝ, ∀ᶠ y in 𝓝 x,
      D.χ a (π y) * D.normalWeight a (π y) ≤ A * ‖σ y‖ ^ 2 := by
    intro a
    by_cases ha : π x ∈ tsupport (D.χ a)
    · cases hc : D.center a with
      | none => exact absurd hx (D.supp_none a hc ha)
      | some p =>
        have hq : π x ∈ flatDomain (D.flat p) := D.supp_some a p hc ha
        have hcoord : ∀ i : Fin n, ∃ B : ℝ, ∀ᶠ y in 𝓝 x,
            (if D.kdim p ≤ i.1 then Complex.normSq (flatCoord (D.flat p) i (π y)) else 0) ≤
              B * ‖σ y‖ ^ 2 := by
          intro i
          by_cases hi : D.kdim p ≤ i.1
          · have hmem := flatCoord_mem_vanishingIdeal (D.flat p) (D.flat_eq p) hi hq
            obtain ⟨α, hα, hαeq⟩ := exists_eq_mul_of_isInSpanAt
              ((hσgen x hxU _).mp (mem_pullback_vanishingIdeal hπ hmem))
            refine ⟨(‖α x‖ + 1) ^ 2, ?_⟩
            filter_upwards [hαeq, hα.continuousAt.norm.eventually
              (gt_mem_nhds (lt_add_one ‖α x‖))] with y hy hyα
            rw [if_pos hi]
            simp only [Function.comp_apply] at hy
            rw [Complex.normSq_eq_norm_sq, hy, norm_mul, mul_pow]
            gcongr
          · exact ⟨0, Eventually.of_forall fun y => by simp [hi]⟩
        choose B hB using hcoord
        refine ⟨∑ i, B i, ?_⟩
        filter_upwards [eventually_all.mpr hB] with y hy
        have hN : D.normalWeight a (π y) ≤ (∑ i, B i) * ‖σ y‖ ^ 2 := by
          simp only [BlanchardData.normalWeight, hc]
          rw [Finset.sum_mul]
          exact Finset.sum_le_sum fun i _ => hy i
        calc D.χ a (π y) * D.normalWeight a (π y) ≤ 1 * D.normalWeight a (π y) :=
              mul_le_mul_of_nonneg_right (blanchard_χ_le_one D a _) (D.normalWeight_nonneg a _)
          _ ≤ (∑ i, B i) * ‖σ y‖ ^ 2 := by rw [one_mul]; exact hN
    · refine ⟨0, ?_⟩
      have : ∀ᶠ y in 𝓝 x, π y ∉ tsupport (D.χ a) :=
        hπc.eventually ((isClosed_tsupport _).isOpen_compl.mem_nhds ha)
      filter_upwards [this] with y hy
      rw [D.χ_eq_zero_of_notMem hy]
      simp
  choose A hA using key
  refine ⟨∑ a, A a, ?_⟩
  filter_upwards [eventually_all.mpr hA] with y hy
  unfold BlanchardData.weight
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun a _ => hy a

/-- Cauchy--Schwarz for a finite sum of products of complex numbers, with the second factor
supported on a subset of the indices. -/
theorem norm_sum_mul_sq_le {ι : Type*} [Fintype ι] (P : ι → Prop) [DecidablePred P]
    (γ ζ : ι → ℂ) (hγ : ∀ i, ¬ P i → γ i = 0) :
    ‖∑ i, γ i * ζ i‖ ^ 2 ≤
      (∑ i, ‖γ i‖ ^ 2) * ∑ i, (if P i then Complex.normSq (ζ i) else 0) := by
  have h1 : ‖∑ i, γ i * ζ i‖ ≤ ∑ i, ‖γ i‖ * (if P i then ‖ζ i‖ else 0) := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    by_cases hi : P i
    · rw [if_pos hi, norm_mul]
    · rw [if_neg hi, hγ i hi]
      simp
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => ‖γ i‖)
    (fun i => if P i then ‖ζ i‖ else 0)
  have h3 : ∀ i, (if P i then ‖ζ i‖ else 0) ^ 2 = if P i then Complex.normSq (ζ i) else 0 := by
    intro i
    split_ifs
    · rw [Complex.normSq_eq_norm_sq]
    · simp
  simp only [h3] at h2
  calc ‖∑ i, γ i * ζ i‖ ^ 2 ≤ (∑ i, ‖γ i‖ * (if P i then ‖ζ i‖ else 0)) ^ 2 := by
        gcongr
    _ ≤ _ := h2

omit [IsComplexManifold n Y] in
/-- **Lower bound**: `|σ|² ≤ A U ∘ π` near a point of `π⁻¹ C` (Hadamard's lemma in flattening
coordinates). -/
theorem eventually_le_blanchardWeight (hπ : IsBlowupAlong n C π) (D : BlanchardData n C)
    {x : Y} (hx : π x ∈ C) {U : Set Y} (hxU : x ∈ U) {σ : Y → ℂ}
    (hσhol : HolomorphicAt n σ x)
    (hσgen : ∀ y ∈ U, ∀ f, (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C)).mem y f ↔
      IsInSpanAt (n := n) (· = σ) y f) :
    ∃ A : ℝ, ∀ᶠ y in 𝓝 x, ‖σ y‖ ^ 2 ≤ A * D.weight (π y) := by
  classical
  have hπc : ContinuousAt π x := hπ.contMDiff.continuous.continuousAt
  -- `σ` is a combination of pullbacks of germs of `𝓘_C`
  obtain ⟨-, K, s, c, hs, hc, hsum⟩ := (hσgen x hxU σ).mpr (isInSpanAt_self hσhol)
  choose f hf hsf using hs
  -- a partition function positive at `π x`
  obtain ⟨a₀, -, ha₀⟩ : ∃ a ∈ Finset.univ, 0 < D.χ a (π x) := by
    by_contra h
    push Not at h
    have : ∑ a, D.χ a (π x) ≤ 0 := Finset.sum_nonpos fun a _ => h a (Finset.mem_univ a)
    rw [D.sum_one] at this
    exact absurd this (by norm_num)
  cases hc₀ : D.center a₀ with
  | none => exact absurd hx (D.supp_none a₀ hc₀ (subset_tsupport _ ha₀.ne'))
  | some p =>
  have hq : π x ∈ flatDomain (D.flat p) := D.supp_some a₀ p hc₀ (subset_tsupport _ ha₀.ne')
  -- Hadamard's lemma for each `f l`
  choose β hβ0 hβhol hβeq using fun l =>
    exists_eq_sum_flatCoord (D.flat p) (D.flat_src p) (D.flat_eq p) hq (hf l)
  set γ : Fin n → Y → ℂ := fun i y => ∑ l, c l y * β l i (π y) with hγ
  have hγc : ∀ i, ContinuousAt (γ i) x := fun i =>
    tendsto_finsetSum Finset.univ fun l _ => (hc l).continuousAt.mul
      ((hβhol l i).continuousAt.comp hπc)
  have hχc : ContinuousAt (fun y => D.χ a₀ (π y)) x :=
    (MeteredDivisorWeightBounds.continuousAt_of_chartContDiffOn (U := univ) isOpen_univ
      (fun e => ((D.smooth a₀) e).mono inter_subset_left) (mem_univ _)).comp hπc
  set G : ℝ := ∑ i, (‖γ i x‖ + 1) ^ 2 with hG
  refine ⟨G * (2 / D.χ a₀ (π x)), ?_⟩
  have hexp : ∀ᶠ y in 𝓝 x, σ y = ∑ i, γ i y * flatCoord (D.flat p) i (π y) := by
    have hall : ∀ᶠ y in 𝓝 x, ∀ l, f l (π y) = ∑ i, β l i (π y) * flatCoord (D.flat p) i (π y) :=
      eventually_all.mpr fun l => hπc.eventually (hβeq l)
    filter_upwards [hsum, hall] with y hy hall'
    rw [hy]
    simp only [hγ, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hsf l, Function.comp_apply, hall' l, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  filter_upwards [hexp, eventually_all.mpr fun i => (hγc i).norm.eventually
      (gt_mem_nhds (lt_add_one ‖γ i x‖)),
    hχc.eventually (lt_mem_nhds (half_lt_self ha₀))] with y hy hyγ hyχ
  have hCS := norm_sum_mul_sq_le (fun i : Fin n => D.kdim p ≤ i.1) (fun i => γ i y)
    (fun i => flatCoord (D.flat p) i (π y)) (fun i hi => by
      simp only [hγ]
      refine Finset.sum_eq_zero fun l _ => ?_
      rw [hβ0 l i (not_le.mp hi)]
      simp)
  have hN : (∑ i : Fin n, if D.kdim p ≤ i.1 then Complex.normSq (flatCoord (D.flat p) i (π y))
      else 0) = D.normalWeight a₀ (π y) := by
    simp only [BlanchardData.normalWeight, hc₀]
  rw [hN] at hCS
  have hγb : ∑ i, ‖γ i y‖ ^ 2 ≤ G :=
    Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hyγ i).le 2
  have hNw := blanchard_χ_mul_normalWeight_le_weight D a₀ (π y)
  have hNn := D.normalWeight_nonneg a₀ (π y)
  have hχpos : 0 < D.χ a₀ (π x) / 2 := half_pos ha₀
  have hGn : 0 ≤ G := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hN2 : D.normalWeight a₀ (π y) ≤ (2 / D.χ a₀ (π x)) * D.weight (π y) := by
    have h1 : D.χ a₀ (π x) / 2 * D.normalWeight a₀ (π y) ≤ D.weight (π y) :=
      le_trans (mul_le_mul_of_nonneg_right hyχ.le hNn) hNw
    rw [div_mul_eq_mul_div, le_div_iff₀ ha₀]
    nlinarith
  calc ‖σ y‖ ^ 2 = ‖∑ i, γ i y * flatCoord (D.flat p) i (π y)‖ ^ 2 := by rw [hy]
    _ ≤ (∑ i, ‖γ i y‖ ^ 2) * D.normalWeight a₀ (π y) := hCS
    _ ≤ G * D.normalWeight a₀ (π y) := mul_le_mul_of_nonneg_right hγb hNn
    _ ≤ G * ((2 / D.χ a₀ (π x)) * D.weight (π y)) := mul_le_mul_of_nonneg_left hN2 hGn
    _ = G * (2 / D.χ a₀ (π x)) * D.weight (π y) := by ring

/-- `a ≤ √K b` from `a² ≤ K b²` (`a, b ≥ 0`). -/
theorem le_sqrt_mul_of_sq_le {a b K : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ 2 ≤ K * b ^ 2) :
    a ≤ Real.sqrt K * b :=
  calc a = Real.sqrt (a ^ 2) := (Real.sqrt_sq ha).symm
    _ ≤ Real.sqrt (K * b ^ 2) := Real.sqrt_le_sqrt h
    _ = Real.sqrt K * b := by rw [Real.sqrt_mul' K (sq_nonneg b), Real.sqrt_sq hb]

omit [IsComplexManifold n M] [IsComplexManifold n Y] in
/-- Off the centre the exceptional ideal is the unit ideal, generated by `1`. -/
theorem pullback_vanishingIdeal_mem_iff_of_notMem (hπ : IsBlowupAlong n C π) {y : Y}
    (hy : π y ∉ C) (f : Y → ℂ) :
    (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C)).mem y f ↔
      IsInSpanAt (n := n) (· = fun _ => (1 : ℂ)) y f := by
  constructor
  · intro hf
    exact isInSpanAt_of_eq_mul rfl hf.1 hf.1 (Eventually.of_forall fun _ => by simp)
  · intro hf
    have hone : (vanishingIdeal (n := n) C).mem (π y) (fun _ => 1) := by
      refine ⟨holomorphicAt_const 1, ?_⟩
      filter_upwards [hπ.1.1.isOpen_compl.mem_nhds hy] with z hz hzC
      exact absurd hzC hz
    exact isInSpanAt_of_eq_mul (s := fun _ => 1) (S := fun s => ∃ a,
      (vanishingIdeal (n := n) C).mem (π y) a ∧ s = a ∘ π)
      ⟨fun _ => 1, hone, rfl⟩ hf.1 hf.1 (Eventually.of_forall fun _ => by simp)

omit [TopologicalSpace Y] in
/-- `log (|σ|² P) = log |σ|² + log P` for `P > 0`, in `EReal`. -/
theorem log_normSq_mul_eq {σ : Y → ℂ} {y : Y} {P : ℝ} (hP : 0 < P) :
    ENNReal.log (ENNReal.ofReal (Complex.normSq (σ y) * P)) =
      generatorLog (fun _ : Fin 1 => σ) y + (Real.log P : EReal) := by
  rw [generatorLog_eq_log_sum, ENNReal.ofReal_mul (Complex.normSq_nonneg _), ENNReal.log_mul_add,
    ENNReal.log_ofReal_of_pos hP]
  simp [Complex.normSq_eq_norm_sq]

/-- **The metric `div (U ∘ π)` of the Blanchard weight is a metric of the exceptional
divisor.**  Near a point of `π⁻¹ C`, the generator `h` of a factorization `U ∘ π = |h|² U'`
satisfies `|h| ≤ K |σ|` (`eventually_blanchardWeight_le`), so `h = w σ` with `w` holomorphic
(Riemann extension, `HolomorphicBoundedQuotient`), and `|σ|² ≤ A U ∘ π`
(`eventually_le_blanchardWeight`) forces `w(x) ≠ 0`. -/
theorem isDivisorMetric_blanchard (hπ : IsBlowupAlong n C π) (D : BlanchardData n C)
    (Fb : WeightFactorization n (fun y => D.weight (π y))) :
    DivisorMetric.IsDivisorMetric (BlowupExceptionalDivisor.exceptionalDivisor hπ)
      (ExceptionalMetricProof.ofWeightFactorization Fb 1 one_pos) := by
  intro x
  have hwt : ∀ y, (ExceptionalMetricProof.ofWeightFactorization Fb 1 one_pos).weight y =
      ENNReal.log (ENNReal.ofReal (D.weight (π y))) := fun y => by
    show (((1 : ℚ) : ℝ) : EReal) * FactorizedWeightPsh.logWeight _ y = _
    simp [FactorizedWeightPsh.logWeight]
  by_cases hx : π x ∈ C
  swap
  · -- off the centre: the generator `1`
    have hO : IsOpen (π ⁻¹' Cᶜ) := hπ.1.1.isOpen_compl.preimage hπ.contMDiff.continuous
    refine ⟨π ⁻¹' Cᶜ, hO, hx, fun _ => 1, fun y _ => mdifferentiableWithinAt_const,
      fun y hy f => pullback_vanishingIdeal_mem_iff_of_notMem hπ hy f,
      fun y => Real.log (D.weight (π y)), fun e => ?_, fun y hy => ?_⟩
    · exact ((BlanchardForm.contDiffOn_chartSmooth_comp hπ.contMDiff D.chartSmooth_weight e).mono
        inter_subset_left).log fun u hu => (D.weight_pos_of_notMem hu.2).ne'
    · have hpos := D.weight_pos_of_notMem hy
      have h1 : generatorLog (fun _ : Fin 1 => (fun _ : Y => (1 : ℂ))) y = 0 := by
        simp [generatorLog_eq_log_sum]
      rw [hwt, h1, zero_add, ENNReal.log_ofReal_of_pos hpos]
  -- over the centre
  obtain ⟨U1, hU1, hxU1, σ, hσd, hσne, hσgen⟩ := hπ.2.2.2.1 x
  have hσhol : HolomorphicAt n σ x := by
    filter_upwards [hU1.mem_nhds hxU1] with y hy
    exact (hσd y hy).mdifferentiableAt (hU1.mem_nhds hy)
  obtain ⟨A₁, hA₁⟩ := eventually_blanchardWeight_le hπ D hx hxU1 hσgen
  obtain ⟨A₂, hA₂⟩ := eventually_le_blanchardWeight hπ D hx hxU1 hσhol hσgen
  set g := Fb.gen x with hg_def
  set s := Fb.smoothPart x with hs_def
  have hxd : x ∈ Fb.domain x := Fb.mem_domain x
  have hsx : 0 < s x := Fb.pos x x hxd
  have hsc : ContinuousAt s x :=
    MeteredDivisorWeightBounds.continuousAt_of_chartContDiffOn (Fb.isOpen_domain x)
      (Fb.smooth x) hxd
  have hghol : HolomorphicAt n g x := by
    filter_upwards [(Fb.isOpen_domain x).mem_nhds hxd] with y hy
    exact Fb.gen_mdifferentiable x y hy
  -- `|g| ≤ K |σ|`
  have hbdd : ∃ K : ℝ, ∀ᶠ y in 𝓝 x, ‖g y‖ ≤ K * ‖σ y‖ := by
    refine ⟨Real.sqrt (2 * |A₁| / s x), ?_⟩
    filter_upwards [hA₁, hsc.eventually (lt_mem_nhds (half_lt_self hsx)),
      (Fb.isOpen_domain x).mem_nhds hxd] with y hy hys hyd
    have hf := Fb.factor x y hyd
    rw [Complex.normSq_eq_norm_sq] at hf
    refine le_sqrt_mul_of_sq_le (norm_nonneg _) (norm_nonneg _) ?_
    have h1 : ‖g y‖ ^ 2 * s y ≤ |A₁| * ‖σ y‖ ^ 2 :=
      (hf ▸ hy).trans (mul_le_mul_of_nonneg_right (le_abs_self A₁) (sq_nonneg _))
    rw [div_mul_eq_mul_div, le_div_iff₀ hsx]
    nlinarith [sq_nonneg ‖g y‖]
  obtain ⟨w, hw, hwe⟩ := HolomorphicBoundedQuotient.exists_holomorphicAt_eventuallyEq_mul hU1 hxU1
    hghol hσhol hσne hbdd
  -- `w(x) ≠ 0`
  have hwx : w x ≠ 0 := by
    intro hw0
    set K₂ : ℝ := |A₂| * (2 * s x) + 1 with hK₂
    have hK₂pos : 0 < K₂ := by positivity
    have hwsmall : ∀ᶠ y in 𝓝 x, ‖w y‖ ^ 2 < 1 / K₂ := by
      have hc : ContinuousAt (fun y => ‖w y‖ ^ 2) x := hw.continuousAt.norm.pow 2
      have : ‖w x‖ ^ 2 < 1 / K₂ := by
        rw [hw0, norm_zero]
        simpa using one_div_pos.mpr hK₂pos
      exact hc.eventually (gt_mem_nhds this)
    have hev : ∀ᶠ y in 𝓝 x, y ∈ U1 ∧ ‖σ y‖ ^ 2 ≤ A₂ * D.weight (π y) ∧
        ‖w y‖ ^ 2 < 1 / K₂ ∧ s y < 2 * s x ∧ g y = w y * σ y ∧ y ∈ Fb.domain x := by
      filter_upwards [hU1.mem_nhds hxU1, hA₂, hwsmall,
        hsc.eventually (gt_mem_nhds (by linarith : s x < 2 * s x)), hwe,
        (Fb.isOpen_domain x).mem_nhds hxd] with y h1 h2 h3 h4 h5 h6
      exact ⟨h1, h2, h3, h4, h5, h6⟩
    obtain ⟨O, hOsub, hO, hxO⟩ := mem_nhds_iff.mp hev
    obtain ⟨y, hyO, hy0⟩ := hσne O hO (fun z hz => (hOsub hz).1) ⟨x, hxO⟩
    obtain ⟨-, h2, h3, h4, h5, h6⟩ := hOsub hyO
    have hf := Fb.factor x y h6
    rw [← hg_def, ← hs_def, Complex.normSq_eq_norm_sq, h5, norm_mul, mul_pow] at hf
    have hσpos : 0 < ‖σ y‖ ^ 2 := by positivity
    have hsy : 0 < s y := Fb.pos x y h6
    rw [hf] at h2
    have hle : A₂ * (‖w y‖ ^ 2 * ‖σ y‖ ^ 2 * s y) ≤
        |A₂| * (‖w y‖ ^ 2 * ‖σ y‖ ^ 2 * s y) :=
      mul_le_mul_of_nonneg_right (le_abs_self A₂) (by positivity)
    have hlt : |A₂| * (‖w y‖ ^ 2 * ‖σ y‖ ^ 2 * s y) < ‖σ y‖ ^ 2 := by
      have hw2 : ‖w y‖ ^ 2 * K₂ < 1 := by
        rw [lt_div_iff₀ hK₂pos] at h3; linarith
      have hA : 0 ≤ |A₂| := abs_nonneg _
      have hww : 0 ≤ ‖w y‖ ^ 2 := sq_nonneg _
      have e1 : |A₂| * (‖w y‖ ^ 2 * ‖σ y‖ ^ 2 * s y) ≤
          |A₂| * (‖w y‖ ^ 2 * ‖σ y‖ ^ 2 * (2 * s x)) := by
        gcongr
      have e2 : |A₂| * (‖w y‖ ^ 2 * ‖σ y‖ ^ 2 * (2 * s x)) =
          ‖σ y‖ ^ 2 * (‖w y‖ ^ 2 * (|A₂| * (2 * s x))) := by ring
      have e3 : ‖w y‖ ^ 2 * (|A₂| * (2 * s x)) < 1 := by
        have : ‖w y‖ ^ 2 * (|A₂| * (2 * s x)) ≤ ‖w y‖ ^ 2 * K₂ := by
          rw [hK₂]; nlinarith
        linarith
      calc _ ≤ _ := e1
        _ = _ := e2
        _ < ‖σ y‖ ^ 2 * 1 := by gcongr
        _ = _ := mul_one _
    linarith
  -- the open set
  have hev : ∀ᶠ y in 𝓝 x, y ∈ U1 ∧ y ∈ Fb.domain x ∧ g y = w y * σ y ∧
      MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) w y ∧ w y ≠ 0 := by
    filter_upwards [hU1.mem_nhds hxU1, (Fb.isOpen_domain x).mem_nhds hxd, hwe, hw,
      hw.continuousAt.eventually_ne hwx] with y h1 h2 h3 h4 h5
    exact ⟨h1, h2, h3, h4, h5⟩
  obtain ⟨V, hVsub, hV, hxV⟩ := mem_nhds_iff.mp hev
  refine ⟨V, hV, hxV, σ, hσd.mono fun y hy => (hVsub hy).1, fun y hy f => hσgen y (hVsub hy).1 f,
    fun y => Real.log (s y) + Real.log (‖w y‖ ^ 2), fun e => ?_, fun y hy => ?_⟩
  · have hS : IsOpen (e.val.target ∩ e.val.symm ⁻¹' V) := e.val.isOpen_inter_preimage_symm hV
    have hsub : e.val.target ∩ e.val.symm ⁻¹' V ⊆ e.val.target ∩ e.val.symm ⁻¹' Fb.domain x :=
      fun z hz => ⟨hz.1, (hVsub hz.2).2.1⟩
    have h1 : ContDiffOn ℝ ∞ (fun z => Real.log (s (e.val.symm z)))
        (e.val.target ∩ e.val.symm ⁻¹' V) :=
      (((Fb.smooth x) e).log fun u hu => (Fb.pos x _ hu.2).ne').mono hsub
    have hwd : MDifferentiableOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) w V :=
      fun y hy => ((hVsub hy).2.2.2.1).mdifferentiableWithinAt
    have h2 : ContDiffOn ℝ ∞ (fun z => Real.log (‖w (e.val.symm z)‖ ^ 2))
        (e.val.target ∩ e.val.symm ⁻¹' V) := by
      intro z hz
      have h := MeteredDivisorSmoothOffSupport.contDiffAt_log_normSq hS
        (MeteredDivisorPositivity.differentiableOn_comp_chartSymm e hwd) hz
        (hVsub hz.2).2.2.2.2
      refine (h.congr_of_eventuallyEq ?_).contDiffWithinAt
      filter_upwards with w'
      rw [Complex.normSq_eq_norm_sq]
    exact h1.add h2
  · obtain ⟨-, h2, h3, -, h5⟩ := hVsub hy
    have hsy : 0 < s y := Fb.pos x y h2
    have hP : 0 < ‖w y‖ ^ 2 * s y := by positivity
    have hf : D.weight (π y) = Complex.normSq (σ y) * (‖w y‖ ^ 2 * s y) := by
      rw [Fb.factor x y h2, ← hg_def, ← hs_def, h3, Complex.normSq_mul, Complex.normSq_eq_norm_sq]
      ring
    rw [hwt, hf, log_normSq_mul_eq hP, Real.log_mul (by positivity) hsy.ne']
    simp only [EReal.coe_add]
    rw [add_comm (Real.log (‖w y‖ ^ 2) : EReal)]

end Blanchard

/-! ### The Kähler class `π^*{ω} - t {ℰ}` -/

section Kahler

variable {N : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel (N + 1)) M]
  [IsComplexManifold (N + 1) M] {Y : Type u} [TopologicalSpace Y]
  [ChartedSpace (ComplexModel (N + 1)) Y] [IsComplexManifold (N + 1) Y] {C : Set M} {π : Y → M}

/-- **The support of any metric of the exceptional divisor is `π⁻¹ C`.** -/
theorem support_eq_of_isDivisorMetric_exceptional {n : ℕ} {M Y : Type u} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [TopologicalSpace Y]
    [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y] {C : Set M} {π : Y → M}
    (hπ : IsBlowupAlong n C π) {E : MeteredEffectiveQDivisor n Y}
    (hE : DivisorMetric.IsDivisorMetric (BlowupExceptionalDivisor.exceptionalDivisor hπ) E) :
    E.support = π ⁻¹' C := by
  rw [support_eq_of_isDivisorMetric hE, BlowupExceptionalDivisor.support_exceptionalDivisor hπ]

/-- **Two metrics of the exceptional divisor have cohomologous curvatures.** -/
theorem bottChernRel_curvature_exceptional (hπ : IsBlowupAlong (N + 1) C π)
    {E₁ E₂ : MeteredEffectiveQDivisor (N + 1) Y}
    (h₁ : DivisorMetric.IsDivisorMetric (BlowupExceptionalDivisor.exceptionalDivisor hπ) E₁)
    (h₂ : DivisorMetric.IsDivisorMetric (BlowupExceptionalDivisor.exceptionalDivisor hπ) E₂) :
    ClosedRealOneOneForm.BottChernRel E₂.curvature E₁.curvature := by
  have hint : interior (π ⁻¹' C) = ∅ := by
    rw [← BlowupExceptionalDivisor.support_exceptionalDivisor hπ]
    exact BlowupExceptionalDivisor.interior_support_exceptionalDivisor hπ
  exact bottChernRel_curvature_of_isDivisorMetric (hπ.1.1.preimage hπ.contMDiff.continuous) hint
    (support_eq_of_isDivisorMetric_exceptional hπ h₁)
    (support_eq_of_isDivisorMetric_exceptional hπ h₂) h₁ h₂

/-- **The Kähler class `π^*{ω} - t{ℰ}`** (Blanchard, `tok:ext-blowup-kahler`): for a compact
Kähler manifold `(M, ω)`, a compact blow-up `π : Y → M` and every metric `E` of the exceptional
divisor, there are a Kähler form `κ` and `t > 0` with `κ = π^*ω - t Θ_E + dd^c h`. -/
theorem exists_kahler_bottChernRel [CompactSpace M] [CompactSpace Y]
    (hπ : IsBlowupAlong (N + 1) C π) (omega : KahlerBackground (N + 1) M)
    {E : MeteredEffectiveQDivisor (N + 1) Y}
    (hE : DivisorMetric.IsDivisorMetric (BlowupExceptionalDivisor.exceptionalDivisor hπ) E) :
    ∃ (κ : KahlerBackground (N + 1) Y) (t : ℝ), 0 < t ∧
      ClosedRealOneOneForm.BottChernRel
        (ClosedRealOneOneForm.pullback hπ.contMDiff omega.form - t • E.curvature) κ.form := by
  obtain ⟨D⟩ := exists_blanchardData hπ.1
  obtain ⟨Fb, ε, hε, hK⟩ := BlowupKahler.exists_isKahler_pullback_add omega hπ D
  have hB := isDivisorMetric_blanchard hπ D Fb
  obtain ⟨f, hf, hfeq⟩ := bottChernRel_curvature_exceptional hπ hE hB
  refine ⟨⟨_, hK⟩, ε, hε, fun y => ε * f y, fun e => (hf e).const_smul ε, fun e z hz => ?_⟩
  have h1 := hfeq e z hz
  have hcoeff :
      (ExceptionalMetricProof.ofWeightFactorization Fb 1 one_pos).curvature.val.coeff e z =
      -Fb.closedForm.val.coeff e z := by
    show ((-((1 : ℚ) : ℝ)) • Fb.closedForm).val.coeff e z = _
    rw [ClosedRealOneOneForm.coeff_smul]
    simp only [Rat.cast_one]
    exact neg_one_smul ℝ (Fb.closedForm.val.coeff e z)
  rw [hcoeff] at h1
  change (ClosedRealOneOneForm.pullback hπ.contMDiff omega.form + ε • Fb.closedForm).val.coeff e z =
    _ + smoothDDC (fun y => ε • f (e.val.symm y)) z
  rw [smoothDDC_smul e.val.open_target (hf e) ε hz, ClosedRealOneOneForm.coeff_add,
    ClosedRealOneOneForm.coeff_smul, BlowupBigPullback.coeff_sub, ClosedRealOneOneForm.coeff_smul]
  have h2 : Fb.closedForm.val.coeff e z =
      smoothDDC (fun y => f (e.val.symm y)) z - E.curvature.val.coeff e z := by
    rw [h1]
    abel
  rw [h2, smul_sub]
  abel

end Kahler

end SGPT.Okounkov.TranscendentalWN
