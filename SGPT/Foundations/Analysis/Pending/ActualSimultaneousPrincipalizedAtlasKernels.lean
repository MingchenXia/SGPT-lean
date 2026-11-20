import SGPT.Foundations.Analysis.Pending.ActualAtlasBergmanOriginalPullbackIdeal
import SGPT.Foundations.Analysis.Pending.ActualHilbertEvaluationPrincipalNormalization
import SGPT.Foundations.Analysis.Pending.GlobalQuasiPshMultiplierPrincipalization
import SGPT.Foundations.Analysis.Pending.SNCSupportedDivisorFixedChartNormalForm
import SGPT.Foundations.Analysis.Pending.ManifoldFiniteSpanChartTransport

set_option autoImplicit false

/-! # One original divisor equation normalizes every actual atlas kernel -/

noncomputable section
open Set Filter Metric MeasureTheory TopologicalSpace
open scoped Topology Manifold ContDiff ENNReal

universe u

namespace SGPT.Foundations.Analysis.Pending.ActualSimultaneousPrincipalizedAtlasKernels

open FirstPass FirstPass.HolomorphicIdealSheaves FirstPass.BlowupSequences
  NormalCrossings HironakaAdmissibleSequence BergmanKernelSmooth InvertibleIdealQuotient
  ActualBergmanEvaluationMultiplierPullbackIdeal ActualAtlasBergmanOriginalPullbackIdeal
  QuantitativeRegularizationChartBranch

private def adaptedInverse {n : ℕ} {Y : Type*} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel n) Y] (y : Y)
    (Φ : LocalHolomorphicEquivAt (n := n) ((complexChartAt (n := n) y).val y)) :
    ComplexModel n → Y := fun z => (complexChartAt (n := n) y).val.symm (Φ.invFun z)

private theorem adaptedInverse_zero {n : ℕ} {Y : Type*} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel n) Y] (y : Y)
    (Φ : LocalHolomorphicEquivAt (n := n) ((complexChartAt (n := n) y).val y))
    (h0 : Φ.toFun ((complexChartAt (n := n) y).val y) = 0) :
    adaptedInverse y Φ 0 = y := by
  dsimp only [adaptedInverse]
  rw [← h0, Φ.left_inv _ Φ.center_mem_source]
  exact (complexChartAt (n := n) y).val.left_inv (mem_complexChartAt_source y)

private theorem adaptedInverse_tendsto {n : ℕ} {Y : Type*} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel n) Y] (y : Y)
    (Φ : LocalHolomorphicEquivAt (n := n) ((complexChartAt (n := n) y).val y))
    (hsrc : Φ.source ⊆ (complexChartAt (n := n) y).val.target)
    (h0 : Φ.toFun ((complexChartAt (n := n) y).val y) = 0) :
    Tendsto (adaptedInverse y Φ) (𝓝 0) (𝓝 y) := by
  have ht : (0 : ComplexModel n) ∈ Φ.target := by
    rw [← h0]; exact Φ.mapsTo_toFun Φ.center_mem_source
  have hcont := ((complexChartAt (n := n) y).val.continuousAt_symm
    (hsrc (Φ.mapsTo_invFun ht))).comp
    ((Φ.invFun_holomorphic.differentiableAt (Φ.isOpen_target.mem_nhds ht)).continuousAt)
  have ht' : Tendsto (adaptedInverse y Φ) (𝓝 0) (𝓝 (adaptedInverse y Φ 0)) := hcont.tendsto
  simpa only [adaptedInverse_zero y Φ h0] using ht'

private theorem adapted_holomorphic {n : ℕ} {Y : Type*} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y] (y : Y)
    (Φ : LocalHolomorphicEquivAt (n := n) ((complexChartAt (n := n) y).val y))
    (h0 : Φ.toFun ((complexChartAt (n := n) y).val y) = 0)
    {b : Y → ℂ} (hb : HolomorphicAt n b y) :
    ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (fun z => b (adaptedInverse y Φ z)) z := by
  have h := (ManifoldFiniteSpanChartTransport.isInSpanAt_comp_adapted_iff
    y Φ h0 (fun _ : Fin 1 => b) b).mp (isInSpanAt_self ⟨0, rfl⟩ hb)
  exact h.1.mono fun _ hz => hz.differentiableAt

private theorem atlas_pullback_holomorphic {n : ℕ} {X Y : Type*}
    [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
    {f : Y → X} (y : Y)
    (hf : ∀ t, ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f t)
    (Φ : LocalHolomorphicEquivAt (n := n) ((complexChartAt (n := n) y).val y))
    (hsrc : Φ.source ⊆ (complexChartAt (n := n) y).val.target)
    (h0 : Φ.toFun ((complexChartAt (n := n) y).val y) = 0)
    (e : ComplexChart n X) (hx : f y ∈ e.val.source) :
    ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ
      (fun z => e.val (f (adaptedInverse y Φ z))) z := by
  have ht : (0 : ComplexModel n) ∈ Φ.target := by
    rw [← h0]; exact Φ.mapsTo_toFun Φ.center_mem_source
  have hT := adaptedInverse_tendsto y Φ hsrc h0
  have hnear : ∀ᶠ z in 𝓝 0, f (adaptedInverse y Φ z) ∈ e.val.source :=
    ((hf y).continuousAt.tendsto.comp hT).eventually (e.val.open_source.mem_nhds hx)
  filter_upwards [Φ.isOpen_target.mem_nhds ht, hnear] with z hz hzX
  have hdInv := (Φ.invFun_holomorphic.differentiableAt
    (Φ.isOpen_target.mem_nhds hz)).mdifferentiableAt
  have hdT := (HolomorphicBoundedQuotient.mdifferentiableAt_chartAt_symm
    (hsrc (Φ.mapsTo_invFun hz))).comp z hdInv
  have hdf := ((hf (adaptedInverse y Φ z)).mdifferentiableAt (by simp)).comp z hdT
  exact ((mdifferentiableAt_atlas (I := 𝓘(ℂ, ComplexModel n))
    e.property hzX).comp z hdf).differentiableAt

private theorem original_pullback_span_eq {n : ℕ} {X Y : Type*}
    [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
    {u : X → EReal} {c : ℝ} {f : Y → X} (y : Y)
    (hf : ∀ t, ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f t)
    (D : EffectiveDivisor n Y)
    (hpb : GermIdeal.pullback (m := n) f (multiplierIdeal (n := n) c u) = D.ideal)
    (Φ : LocalHolomorphicEquivAt (n := n) ((complexChartAt (n := n) y).val y))
    (hsrc : Φ.source ⊆ (complexChartAt (n := n) y).val.target)
    (h0 : Φ.toFun ((complexChartAt (n := n) y).val y) = 0)
    {g : Y → ℂ} (hg : HolomorphicAt n g y)
    (hgen : ∀ a : Y → ℂ, D.ideal.mem y a ↔ IsInSpanAt (n := n) (· = g) y a)
    (e : ComplexChart n X) (hx : f y ∈ e.val.source)
    (α : ComplexModel n → ComplexModel n)
    (hαe : α = fun z => e.val (f (adaptedInverse y Φ z)))
    (hα : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ α z) (hyT : α 0 ∈ e.val.target) :
    Ideal.span (range (originalChartPullbackGerm (u := u) (c := c) e α hα hyT)) =
      Ideal.span {HolGerm.mk (fun z => g (adaptedInverse y Φ z))
        (adapted_holomorphic y Φ h0 hg)} := by
  classical
  let T := adaptedInverse y Φ
  have hT := adaptedInverse_tendsto y Φ hsrc h0
  have hα0 : α 0 = e.val (f y) := by
    simp only [hαe, adaptedInverse_zero y Φ h0]
  have hcenter : e.val.symm (α 0) = f y := by rw [hα0, e.val.left_inv hx]
  have hnear : ∀ᶠ z in 𝓝 0, f (T z) ∈ e.val.source :=
    ((hf y).continuousAt.tendsto.comp hT).eventually (e.val.open_source.mem_nhds hx)
  let G : ComplexModel n → ℂ := fun z => g (T z)
  have hG := adapted_holomorphic y Φ h0 hg
  apply le_antisymm
  · refine Ideal.span_le.mpr ?_
    rintro _ ⟨a, rfl⟩
    have ha : (multiplierIdeal (n := n) c u).mem (f y) a.val :=
      Eq.mp (congrArg (fun p => (multiplierIdeal (n := n) c u).mem p a.val) hcenter) a.property
    have haf : HolomorphicAt n (a.val ∘ f) y :=
      ha.1.comp_contMDiff (Eventually.of_forall hf)
    have hDmem : D.ideal.mem y (a.val ∘ f) := by
      rw [← hpb]
      change IsInSpanAt (n := n)
        (fun s => ∃ b, (multiplierIdeal (n := n) c u).mem (f y) b ∧ s = b ∘ f)
        y (a.val ∘ f)
      exact isInSpanAt_self ⟨a.val, ha, rfl⟩ haf
    obtain ⟨_, b, hb, he⟩ := isInSpanAt_eq_iff.mp ((hgen _).mp hDmem)
    have hbT := adapted_holomorphic y Φ h0 hb
    have hEq : originalChartPullbackGerm (u := u) (c := c) e α hα hyT a =
        HolGerm.mk (fun z => b (T z)) hbT * HolGerm.mk G hG := by
      apply (HolGerm.mk_eq_mk_iff.mpr ?_).trans
        (HolGerm.mk_mul (fun z => b (T z)) G hbT hG)
      filter_upwards [hT.eventually he, hnear] with z hz hzX
      change f (adaptedInverse y Φ z) ∈ e.val.source at hzX
      simpa only [hαe, T, e.val.left_inv hzX, Function.comp_apply, G] using hz
    rw [hEq]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span (mem_singleton _))
  · refine Ideal.span_le.mpr ?_
    intro q hq
    obtain rfl := mem_singleton_iff.mp hq
    have hgD := (hgen g).mpr (isInSpanAt_self rfl hg)
    rw [← hpb] at hgD
    obtain ⟨_, N, s, b, hs, hb, he⟩ := hgD
    choose a ha hsa using hs
    let C (i : Fin N) : ComplexModel n → ℂ := fun z => b i (T z)
    let B (i : Fin N) : ComplexModel n → ℂ := fun z => a i (f (T z))
    have hC (i : Fin N) : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (C i) z :=
      adapted_holomorphic y Φ h0 (hb i)
    have hB (i : Fin N) : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (B i) z :=
      adapted_holomorphic y Φ h0
      ((ha i).1.comp_contMDiff (Eventually.of_forall hf))
    have hprod (i : Fin N) :
        ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (fun z => C i z * B i z) z :=
      eventually_differentiableAt_mul (hC i) (hB i)
    let A (i : Fin N) : {a : X → ℂ //
        (multiplierIdeal (n := n) c u).mem (e.val.symm (α 0)) a} :=
      ⟨a i, Eq.mpr (congrArg (fun p => (multiplierIdeal (n := n) c u).mem p (a i)) hcenter)
        (ha i)⟩
    have heq : G =ᶠ[𝓝 0] fun z => ∑ i, C i z * B i z := by
      filter_upwards [hT.eventually he] with z hz
      change g (T z) = _
      rw [hz]
      exact Finset.sum_congr rfl fun i _ => by
        dsimp only [C, B]; rw [hsa i]; rfl
    have hBgerm (i : Fin N) : HolGerm.mk (B i) (hB i) =
        originalChartPullbackGerm (u := u) (c := c) e α hα hyT (A i) := by
      apply HolGerm.mk_eq_mk_iff.mpr
      filter_upwards [hnear] with z hz
      change f (adaptedInverse y Φ z) ∈ e.val.source at hz
      simp only [B, A, hαe, T, e.val.left_inv hz]
    have hgerm : HolGerm.mk G hG =
        ∑ i, HolGerm.mk (C i) (hC i) *
          originalChartPullbackGerm (u := u) (c := c) e α hα hyT (A i) := by
      calc
        _ = HolGerm.mk (fun z => ∑ i, C i z * B i z)
            (eventually_differentiableAt_sum Finset.univ hprod) := HolGerm.mk_eq_mk_iff.mpr heq
        _ = _ := by
          rw [HolGerm.mk_sum Finset.univ (fun i z => C i z * B i z) hprod]
          apply Finset.sum_congr rfl
          intro i _
          rw [HolGerm.mk_mul (C i) (B i) (hC i) (hB i), hBgerm i]
    rw [hgerm]
    exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨A i, rfl⟩)

private theorem eval_comp_holomorphic {n : ℕ} {K : Set (ComplexModel n)}
    {w : ComplexModel n → ℝ≥0∞} (hBw : BergmanWeight K w)
    (hEval : DifferentiableOn ℂ (evalCLM hBw) K)
    {α : ComplexModel n → ComplexModel n}
    (hα : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ α z) (hyK : α 0 ∈ K) :
    ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (fun z => evalCLM hBw (α z)) z := by
  have ht := hα.self_of_nhds.continuousAt.tendsto
  filter_upwards [hα, ht.eventually (hBw.isOpen.mem_nhds hyK)] with z hz hzK
  exact DifferentiableAt.comp (𝕜 := ℂ) (E := ComplexModel n) (F := ComplexModel n)
    (G := StrongDual ℂ (bergmanSubspace K w)) z
    (hEval.differentiableAt (hBw.isOpen.mem_nhds hzK)) hz

/-- The original multiplier ideal internally supplies one resolution and
one divisor equation before every actual atlas kernel at each point. -/
theorem exists_principalization_all_atlas_smooth_positive_kernels {m : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X]
    [IsComplexManifold (m + 1) X] [CompactSpace X]
    {θ : SmoothRealForm (m + 1) X 2} {u : X → EReal}
    (hu : IsThetaPshPotential θ u) {c : ℝ} (hc : 0 < c) :
    ∃ (Y : Type u) (_ : TopologicalSpace Y) (_ : ChartedSpace (ComplexModel (m + 1)) Y)
      (_ : IsComplexManifold (m + 1) Y) (f : Y → X) (D : EffectiveDivisor (m + 1) Y)
      (E : List (Set Y)),
      IsAdmissibleBlowupSequence (m + 1) X [] (multiplierIdeal (n := m + 1) c u).zeroLocus Y f E ∧
      GermIdeal.pullback (m := m + 1) f (multiplierIdeal (n := m + 1) c u) = D.ideal ∧
      IsSNCDivisor (m + 1) E ∧ D.support = ⋃ H ∈ E, H ∧
      D.support = f ⁻¹' (multiplierIdeal (n := m + 1) c u).zeroLocus ∧
      IsIsomorphismOver (m + 1) f (multiplierIdeal (n := m + 1) c u).zeroLocusᶜ ∧
      ∀ y : Y, ∃ (S : Fin E.length → Finset (Fin (m + 1)))
        (Φ : LocalHolomorphicEquivAt (n := m + 1) ((complexChartAt (n := m + 1) y).val y)),
        Φ.source ⊆ (complexChartAt (n := m + 1) y).val.target ∧
        Φ.toFun ((complexChartAt (n := m + 1) y).val y) = 0 ∧
        (∀ i, y ∈ E.get i → (S i).card = 1) ∧ Set.InjOn S {i | y ∈ E.get i} ∧
        (∀ i, y ∈ E.get i → ∀ {t : Y}, t ∈ (complexChartAt (n := m + 1) y).val.source →
          (complexChartAt (n := m + 1) y).val t ∈ Φ.source →
          (t ∈ E.get i ↔ Φ.toFun ((complexChartAt (n := m + 1) y).val t) ∈ coordSubspace (S i))) ∧
        ∃ g : Y → ℂ, HolomorphicAt (m + 1) g y ∧
          (∀ a : Y → ℂ, D.ideal.mem y a ↔ IsInSpanAt (n := m + 1) (· = g) y a) ∧
          let T : ComplexModel (m + 1) → Y := fun z =>
            (complexChartAt (n := m + 1) y).val.symm (Φ.invFun z)
          ∀ (e : ComplexChart (m + 1) X), f y ∈ e.val.source →
            ∀ (Ω : Set (ComplexModel (m + 1))) (ρ : ComplexModel (m + 1) → ℝ),
              IsSmoothLocalPotential θ e Ω ρ →
              ∀ (L : Set (ComplexModel (m + 1))), IsOpen L → Convex ℝ L →
                Bornology.IsBounded L → closure L ⊆ Ω →
                ∀ (K : Set (ComplexModel (m + 1))), IsOpen K → closure K ⊆ L →
                  e.val (f y) ∈ K →
                  ∃ hBw : BergmanWeight K (fun z => multiplierWeight c (correctedWeight e ρ u z)),
                    ∃ (Q : ComplexModel (m + 1) → StrongDual ℂ
                      (bergmanSubspace K (fun z => multiplierWeight c (correctedWeight e ρ u z))))
                      (r : ℝ), 0 < r ∧ DifferentiableOn ℂ Q (ball 0 r) ∧
                      ContDiffOn ℝ ∞ (fun z => ‖Q z‖ ^ 2) (ball 0 r) ∧
                      ∀ z ∈ ball 0 r, 0 < ‖Q z‖ ^ 2 ∧
                        evalCLM hBw (e.val (f (T z))) = g (T z) • Q z ∧
                        ‖evalCLM hBw (e.val (f (T z)))‖ ^ 2 = ‖g (T z)‖ ^ 2 * ‖Q z‖ ^ 2 := by
  classical
  have hqu : IsGlobalQuasiPshPotential (n := m + 1) u := ⟨hu.1.quasiPlurisubharmonic, hu.2⟩
  obtain ⟨Y, tY, chY, cmY, f, D, E, hπ, hpb, hE, hsupp, hzero, hiso⟩ :=
    GlobalQuasiPshMultiplierPrincipalization.exists_principalization_of_isGlobalQuasiPshPotential
      (Nat.zero_lt_succ m) hqu hc
  let := tY
  let := chY
  let := cmY
  have hf := fun t => hπ.isBlowupSequence.contMDiff t
  refine ⟨Y, tY, chY, cmY, f, D, E, hπ, hpb, hE, hsupp, hzero, hiso, ?_⟩
  intro y
  obtain ⟨S, ⟨Φ, hsrc, h0, hflat⟩, hcard, hinj⟩ := hE.2 y
  obtain ⟨U, hU, hyU, g, hg, _, hgen, hG, hzeroG, _, _⟩ :=
    SNCSupportedDivisorFixedChartNormalForm.exists_unit_monomial_generator_in_adapted_coordinates
      D E hE hsupp.subset y S Φ hsrc h0 hcard hflat
  have hgy : HolomorphicAt (m + 1) g y := holomorphicAt_of_mdifferentiableOn hU hg hyU
  refine ⟨S, Φ, hsrc, h0, hcard, hinj, hflat, g, hgy, hgen y hyU, ?_⟩
  dsimp only
  intro e hx Ω ρ hρ L hLo hLc hLb hLΩ K hKo hKL hyK
  obtain ⟨hBw, hEval, hSpan⟩ := exists_full_evaluation_original_pullback_span
    hu.1 e hρ hc hLo hLc hLb hLΩ hKo hKL
  let T := adaptedInverse y Φ
  let α : ComplexModel (m + 1) → ComplexModel (m + 1) := fun z => e.val (f (T z))
  have hα : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ α z :=
    atlas_pullback_holomorphic y hf Φ hsrc h0 e hx
  have hα0 : α 0 = e.val (f y) := by
    dsimp only [α, T]; rw [adaptedInverse_zero y Φ h0]
  have hyK' : α 0 ∈ K := by rw [hα0]; exact hyK
  have hyT : α 0 ∈ e.val.target := by rw [hα0]; exact e.val.map_source hx
  have hPrincipal : Ideal.span (range (evaluationGerm hBw α hα hyK')) =
      Ideal.span {HolGerm.mk (fun z => g (T z)) hG} :=
    (hSpan (m + 1) α hα hyK').trans
      (original_pullback_span_eq y hf D hpb Φ hsrc h0 hgy (hgen y hyU) e hx α rfl hα hyT)
  have hA := eval_comp_holomorphic hBw hEval hα hyK'
  have : CompleteSpace (bergmanSubspace K
      (fun z => multiplierWeight c (correctedWeight e ρ u z))) :=
    completeSpace_coe_iff_isComplete.mpr (isClosed_bergmanSubspace hBw).isComplete
  obtain ⟨Q, r, hr, hQ, hsmooth, heq⟩ :=
    ActualHilbertEvaluationPrincipalNormalization.exists_smooth_positive_principal_quotient
      hA hG hPrincipal hzeroG
  exact ⟨hBw, Q, r, hr, hQ, hsmooth, heq⟩

end SGPT.Foundations.Analysis.Pending.ActualSimultaneousPrincipalizedAtlasKernels
