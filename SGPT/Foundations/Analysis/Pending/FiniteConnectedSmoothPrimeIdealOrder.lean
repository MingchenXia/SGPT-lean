import SGPT.Foundations.Analysis.Pending.RawConnectedSmoothPrimeIdealOrder
import SGPT.Foundations.Analysis.Pending.ZeroDimensionalQuasiPshMultiplierIdeals

set_option autoImplicit false

/-! # The original finite-modification prime test, with actual finite geometry retained -/

open Set Filter Metric MeasureTheory
open scoped Topology Manifold ENNReal ContDiff

universe u

namespace SGPT.Foundations.Analysis.Pending.FiniteConnectedSmoothPrimeIdealOrder

open FirstPass FirstPass.HolomorphicMaps FirstPass.HolomorphicIdealSheaves
  FirstPass.IEnvelope FirstPass.NonKahlerLocus FirstPass.BlowupSequences
  DivisorialChangeOfVariables DemaillyApproximantDivisorialLelong
  NormalCrossings InvertibleIdealQuotient
  GermIdealOrder IdealWeightPowers RestrictedIdealExtension
  AnalyticModificationLocalDiscrepancy

noncomputable section

private theorem holomorphic_adapted {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    (x : X) (Φ : LocalHolomorphicEquivAt (n := n) ((chartAt (ComplexModel n) x) x))
    (h0 : Φ.toFun ((chartAt (ComplexModel n) x) x) = 0)
    {F : X → ℂ} (hF : HolomorphicAt n F x) :
    ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ
      (fun w => F ((chartAt (ComplexModel n) x).symm (Φ.invFun w))) z := by
  have hs := (ManifoldFiniteSpanChartTransport.isInSpanAt_comp_adapted_iff
    x Φ h0 (fun _ : Fin 1 => F) F).mp (isInSpanAt_self ⟨0, rfl⟩ hF)
  exact hs.1.mono fun _ hz => hz.differentiableAt

private theorem psh_generatorLog_of_near_holomorphic {n s : ℕ}
    (G : Fin s → ComplexModel n → ℂ) {p : ComplexModel n}
    (hG : ∀ i, ∀ᶠ z in 𝓝 p, DifferentiableAt ℂ (G i) z) :
    PlurisubharmonicAt (generatorLog G) p := by
  obtain ⟨U, hsub, hU, hpU⟩ := _root_.mem_nhds_iff.mp (eventually_all.mpr hG)
  have hgen : HolomorphicGeneratorsAt G p :=
    ⟨U, hU, hpU, fun i z hz => (hsub hz i).differentiableWithinAt⟩
  simpa only [EReal.coe_one, one_mul] using
    plurisubharmonicAt_scaled_generatorLog hgen zero_lt_one


/-- Natural original raw data internally give every complete original
truncation family and its analytic-target integral, on same-source modifications. -/
private theorem exists_full_family_with_all_truncation_integrals
    {m : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
    {u v : X → EReal} (hu : ManifoldQuasiPlurisubharmonic (n := m + 1) u)
    (hv : ManifoldQuasiPlurisubharmonic (n := m + 1) v) (x : X)
    {p : ℕ} (hp : 0 < p) {q₀ q₁ : ℝ} (hq₁ : 0 < q₁) (hgap : q₁ < q₀)
    (horder : ∀ (Y : Type u) [TopologicalSpace Y]
      [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y] (π : Y → X),
      AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := m + 1) π →
      IsBlowupSequence (m + 1) X Y π →
      ∀ V : ClosedIrreducibleAnalyticSubvariety (m + 1) Y,
        V.dim = m → (∀ z ∈ V.carrier, RegularAtDim (n := m + 1) V.carrier z m) →
        (∀ z ∈ V.carrier, π z = x) →
          (⨅ z ∈ V.carrier, lelongNumber (n := m + 1) (fun w => v (π w)) z) ≤
            ⨅ z ∈ V.carrier, lelongNumber (n := m + 1) (fun w => u (π w)) z)
    {F : X → ℂ} (hFnon : ∃ᶠ z in 𝓝 x, F z ≠ 0)
    (hint : (multiplierIdeal (n := m + 1) q₀ u).mem x F) :
    ∃ (s : ℕ) (G : Fin s → X → ℂ),
      (∀ i, HolomorphicAt (m + 1) (G i) x) ∧
      (∀ H : X → ℂ, (multiplierIdeal (n := m + 1) p v).mem x H ↔
        IsInSpanAt (n := m + 1) (· ∈ range G) x H) ∧
      (∀ (c δ : ℝ), 0 < c → 0 < δ → 2 * (c * (1 + δ)) / δ ≤ (p : ℝ) →
        ∀ H : X → ℂ,
          (multiplierIdeal (n := m + 1) (c * (1 + δ) / p) (generatorLog G)).mem x H →
          (multiplierIdeal (n := m + 1) c v).mem x H) ∧
      ∀ N : ℕ,
        let 𝔟 := sumIdeal (multiplierIdeal (n := m + 1) p v)
          (idealPow (pointIdeal (m + 1) x) N)
        ∃ (t : ℕ) (Q : Fin t → X → ℂ),
          (∀ i, HolomorphicAt (m + 1) (Q i) x) ∧
          (∀ H : X → ℂ, 𝔟.mem x H ↔ IsInSpanAt (n := m + 1) (· ∈ range Q) x H) ∧
          (∀ i, 𝔟.mem x (Q i)) ∧
          (multiplierIdeal (n := m + 1) (q₁ / p) (generatorLog Q)).mem x F := by
  classical
  have hpr : (0 : ℝ) < p := by exact_mod_cast hp
  obtain ⟨s, G, hG, hfull, C, hC, hdom, _, hreverse⟩ :=
    RawManifoldFullMultiplierFamily.exists_full_family_before_all_whole_fiber_bounds.{u, u} hv x hp
  have hcoh := GlobalQuasiPshMultiplierCoherence.isCoherent_multiplierIdeal_of_manifoldQuasiPlurisubharmonic
    (Nat.zero_lt_succ m) hv hpr
  refine ⟨s, G, hG, hfull, hreverse, ?_⟩
  intro N
  dsimp only
  let 𝔟 := sumIdeal (multiplierIdeal (n := m + 1) p v)
    (idealPow (pointIdeal (m + 1) x) N)
  have hcohB : 𝔟.IsCoherent :=
    (PointSupportedIdealPrincipalization.truncation_properties x hcoh N).1
  obtain ⟨U, hU, hxU, t, Q, hQon, hQfull⟩ := hcohB x
  have hQ (i : Fin t) : HolomorphicAt (m + 1) (Q i) x := by
    filter_upwards [hU.mem_nhds hxU] with z hz
    exact (hQon i z hz).mdifferentiableAt (hU.mem_nhds hz)
  have hQmem (i : Fin t) : 𝔟.mem x (Q i) :=
    (hQfull x hxU (Q i)).mpr
      (InvertibleIdealQuotient.isInSpanAt_self ⟨i, rfl⟩ (hQ i))
  have hGspan (i : Fin s) : IsInSpanAt (n := m + 1) (· ∈ range Q) x (G i) := by
    have hGmem := (hfull (G i)).mpr
      (InvertibleIdealQuotient.isInSpanAt_self ⟨i, rfl⟩ (hG i))
    exact (hQfull x hxU (G i)).mp (le_sumIdeal_left hcoh x (G i) hGmem)
  obtain ⟨B, hB, hBdom⟩ :=
    IdealWeightComparison.exists_nhds_generatorNormSq_le_of_forall_isInSpanAt hGspan
  have hC' : C * ENNReal.ofReal B ≠ ⊤ := ENNReal.mul_ne_top hC ENNReal.ofReal_ne_top
  have hdomQ : ∀ᶠ z in 𝓝 x, EReal.exp (((p : ℝ) : EReal) * v z) ≤
      (C * ENNReal.ofReal B) * ∑ i, ENNReal.ofReal (‖Q i z‖ ^ 2) := by
    filter_upwards [hdom, hBdom] with z hz hBz
    have hBE : (∑ i, ENNReal.ofReal (‖G i z‖ ^ 2)) ≤
        ENNReal.ofReal B * ∑ i, ENNReal.ofReal (‖Q i z‖ ^ 2) := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _),
        ← ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _),
        ← ENNReal.ofReal_mul hB.le]
      exact ENNReal.ofReal_le_ofReal hBz
    calc
      _ ≤ C * ∑ i, ENNReal.ofReal (‖G i z‖ ^ 2) := hz
      _ ≤ C * (ENNReal.ofReal B * ∑ i, ENNReal.ofReal (‖Q i z‖ ^ 2)) :=
        by simpa only [mul_comm] using mul_le_mul_right hBE C
      _ = _ := (mul_assoc _ _ _).symm
  obtain ⟨_hz, Y, tY, cY, mY, π, D, E, hseq, hmod, hhol, _hproper, _hsurj,
      hpull, hE, hs, _hpre, _hiso, hreaders⟩ :=
    RawMultiplierGlobalModification.exists_principalization_with_global_modification hv x hpr N
  let _ := tY
  let _ := cY
  let _ := mY
  have hcomponents : ∀ y : Y, π y = x → ∀ i : Fin E.length, y ∈ E.get i →
      ∃ V : ClosedIrreducibleAnalyticSubvariety (m + 1) Y,
        V.dim = m ∧ (∀ z ∈ V.carrier, RegularAtDim (n := m + 1) V.carrier z m) ∧
        y ∈ V.carrier ∧ (∀ z ∈ V.carrier, π z = x) ∧
        ∃ O : Set Y, IsOpen O ∧ y ∈ O ∧ E.get i ∩ O = V.carrier ∩ O := by
    intro y _hy i hyE
    obtain ⟨V, hdim, _hcomp, hyV, _hsub, _hconn, hreg, hlocal, hcenter, _hreader⟩ :=
      hreaders i y hyE
    exact ⟨V, hdim, hreg, hyV, hcenter, hlocal y hyV⟩
  have hgen : ∀ y : Y, π y = x → ∀ H : Y → ℂ, D.ideal.mem y H ↔
      IsInSpanAt (n := m + 1) (· ∈ range (fun i z => Q i (π z))) y H := by
    intro y hy H
    have hQy (i : Fin t) : HolomorphicAt (m + 1) (Q i) (π y) := hy ▸ hQ i
    have hfully (a : X → ℂ) : 𝔟.mem (π y) a ↔
        IsInSpanAt (n := m + 1) (· ∈ range Q) (π y) a := by
      rw [hy]
      exact hQfull x hxU a
    have h := FiniteGermIdealPullbackGenerators.mem_pullback_iff_of_finite_generation
      (Eventually.of_forall fun _ => hhol.contMDiffAt) 𝔟 Q hQy hfully H
    have hpull' : GermIdeal.pullback (m := m + 1) π 𝔟 = D.ideal := hpull
    simpa only [hpull', Function.comp_def] using h
  have htarget :=
    AnalyticModificationNumericalMultiplierDescent.multiplierIdeal_mem_of_principalized_raw_prime_comparison
      hmod x D E hE hs hcomponents Q hQ hgen hu hpr hq₁ hgap hC' hdomQ
        (horder Y π hmod hseq.isBlowupSequence) hFnon hint
  exact ⟨t, Q, hQ, hQfull x hxU, hQmem, htarget⟩

/-- Actual whole-prime order on every same-source global modification returns
every original raw multiplier ideal inclusion, with no target certificate. -/
theorem multiplierIdeal_le_of_all_finite_global_prime_orders
    {m : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
    {u v : X → EReal} (hu : ManifoldQuasiPlurisubharmonic (n := m + 1) u)
    (hv : ManifoldQuasiPlurisubharmonic (n := m + 1) v)
    (horder : ∀ (Y : Type u) [TopologicalSpace Y]
      [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y] (π : Y → X),
      AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := m + 1) π →
      IsBlowupSequence (m + 1) X Y π →
      ∀ V : ClosedIrreducibleAnalyticSubvariety (m + 1) Y,
        V.dim = m → (∀ z ∈ V.carrier, RegularAtDim (n := m + 1) V.carrier z m) →
          (⨅ z ∈ V.carrier, lelongNumber (n := m + 1) (fun w => v (π w)) z) ≤
            ⨅ z ∈ V.carrier, lelongNumber (n := m + 1) (fun w => u (π w)) z)
    {c : ℝ} (hc : 0 < c) :
    (multiplierIdeal (n := m + 1) c u).Le (multiplierIdeal (n := m + 1) c v) := by
  intro x F hint
  classical
  let e := complexChartAt (n := m + 1) x
  have he : e.val x ∈ e.val.target := e.val.map_source (mem_complexChartAt_source x)
  by_cases hFnon : ∃ᶠ z in 𝓝 x, F z ≠ 0
  · obtain ⟨q₀, hcq₀, hq₀F⟩ :=
      RawQuasiPshUniformStrictGenericNecessity.exists_gt_multiplierIntegrableAt
        (hu e (e.val x) he) hint.2
    let q₁ := (c + q₀) / 2
    let q₂ := (c + q₁) / 2
    have hcq₁ : c < q₁ := by dsimp [q₁]; linarith
    have hq₁q₀ : q₁ < q₀ := by dsimp [q₁]; linarith
    have hcq₂ : c < q₂ := by dsimp [q₂]; linarith
    have hq₂q₁ : q₂ < q₁ := by dsimp [q₂]; linarith
    have hq₁ : 0 < q₁ := hc.trans hcq₁
    have hq₂ : 0 < q₂ := hc.trans hcq₂
    let δ := q₂ / c - 1
    have hδ : 0 < δ := by
      have h : 1 < q₂ / c := (lt_div_iff₀ hc).mpr (by simpa using hcq₂)
      dsimp [δ]
      linarith
    have hq₂eq : c * (1 + δ) = q₂ := by
      dsimp [δ]
      field_simp
      ring
    obtain ⟨p, hpbig⟩ := exists_nat_gt (max (2 * q₂ / δ) 1)
    have hpr : (0 : ℝ) < p := lt_trans zero_lt_one ((le_max_right _ _).trans_lt hpbig)
    have hp : 0 < p := by exact_mod_cast hpr
    have hpbound : 2 * (c * (1 + δ)) / δ ≤ (p : ℝ) := by
      rw [hq₂eq]
      exact ((le_max_left _ _).trans_lt hpbig).le
    have hint₀ : (multiplierIdeal (n := m + 1) q₀ u).mem x F := ⟨hint.1, hq₀F⟩
    obtain ⟨s, G, hG, hfull, hreverse, htrunc⟩ :=
      exists_full_family_with_all_truncation_integrals
        hu hv x hp hq₁ hq₁q₀ (fun Y _ _ _ π hπ hseq V hdim hreg _hcenter =>
          horder Y π hπ hseq V hdim hreg) hFnon hint₀
    obtain ⟨Φ, _hsrc, h0⟩ := NormalCrossings.exists_centred_coordinates (n := m + 1) x
    let T : ComplexModel (m + 1) → X := fun z => e.val.symm (Φ.invFun z)
    let GT : Fin s → ComplexModel (m + 1) → ℂ := fun i z => G i (T z)
    let FT : ComplexModel (m + 1) → ℂ := fun z => F (T z)
    have hGT (i : Fin s) : ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)),
        DifferentiableAt ℂ (GT i) z := holomorphic_adapted x Φ h0 (hG i)
    have hqq : q₂ / p < q₁ / p := (div_lt_div_iff_of_pos_right hpr).mpr hq₂q₁
    have hintGT : MultiplierIntegrableAt (generatorLog GT) (q₂ / p) FT 0 volume := by
      apply FiniteFamilyStrictTruncationStability.multiplierIntegrableAt_of_all_truncations
        GT hGT (div_pos hq₂ hpr) hqq
      intro N
      obtain ⟨t, Q, hQ, _hQfull, hQmem, hQtarget⟩ := htrunc N
      let QT : Fin t → ComplexModel (m + 1) → ℂ := fun i z => Q i (T z)
      have hQT (i : Fin t) : ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)),
          DifferentiableAt ℂ (QT i) z := holomorphic_adapted x Φ h0 (hQ i)
      refine ⟨t, QT, hQT, ?_, ?_⟩
      · intro i
        obtain ⟨_hQi, _hGi, hm⟩ :=
          ManifoldPointTruncationCoordinateMembership.mem_coordinate_truncation_of_original_membership
            x Φ h0 (multiplierIdeal (n := m + 1) p v) G hG hfull N (hQmem i)
        exact hm
      · let QP : Fin t → ComplexModel (m + 1) → ℂ := fun i z => Q i (e.val.symm z)
        have hQP (i : Fin t) : ∀ᶠ z in 𝓝 (e.val x), DifferentiableAt ℂ (QP i) z :=
          MultiplierIdealBergmanNadelManifold.eventually_differentiableAt_comp_chart_symm
            (mem_complexChartAt_source x) (hQ i)
        have hpsh := (psh_generatorLog_of_near_holomorphic QP hQP).quasiPlurisubharmonicAt
        have hcov := LocalHolomorphicMultiplierGermCovariance.multiplierIntegrableAt_comp_inv_iff
          Φ (f := fun z => F (e.val.symm z)) (c := q₁ / p) hpsh
        have hweq : (fun z => generatorLog QP (Φ.invFun z)) = generatorLog QT := by
          funext z
          simp only [generatorLog_eq_log_sum]
          rfl
        have hintP : MultiplierIntegrableAt (generatorLog QP) (q₁ / p)
            (fun z => F (e.val.symm z)) (e.val x) volume := by
          convert hQtarget.2 using 1
          funext z
          simp only [chartFunction, generatorLog_eq_log_sum]
          rfl
        have h := hcov.mpr hintP
        simpa only [h0, hweq] using h
    let GP : Fin s → ComplexModel (m + 1) → ℂ := fun i z => G i (e.val.symm z)
    have hGP (i : Fin s) : ∀ᶠ z in 𝓝 (e.val x), DifferentiableAt ℂ (GP i) z :=
      MultiplierIdealBergmanNadelManifold.eventually_differentiableAt_comp_chart_symm
        (mem_complexChartAt_source x) (hG i)
    have hpsh := (psh_generatorLog_of_near_holomorphic GP hGP).quasiPlurisubharmonicAt
    have hcov := LocalHolomorphicMultiplierGermCovariance.multiplierIntegrableAt_comp_inv_iff
      Φ (f := fun z => F (e.val.symm z)) (c := q₂ / p) hpsh
    have hweq : (fun z => generatorLog GP (Φ.invFun z)) = generatorLog GT := by
      funext z
      simp only [generatorLog_eq_log_sum]
      rfl
    have hintGP : MultiplierIntegrableAt (generatorLog GP) (q₂ / p)
        (fun z => F (e.val.symm z)) (e.val x) volume := by
      apply hcov.mp
      simpa only [h0, hweq] using hintGT
    have hintG : (multiplierIdeal (n := m + 1) (c * (1 + δ) / p) (generatorLog G)).mem x F := by
      refine ⟨hint.1, ?_⟩
      rw [hq₂eq]
      convert hintGP using 1
      funext z
      simp only [chartFunction, generatorLog_eq_log_sum]
      rfl
    exact hreverse c δ hc hδ hpbound F hintG
  · have hzero : ∀ᶠ z in 𝓝 x, F z = 0 := by
      simpa only [Filter.Frequently, not_not, not_ne_iff] using hFnon
    have ht : Tendsto e.val.symm (𝓝 (e.val x)) (𝓝 x) := by
      have h := (e.val.symm.continuousAt he).tendsto
      simpa only [e.val.left_inv (mem_complexChartAt_source x)] using h
    refine ⟨hint.1, ?_⟩
    have hzeroP : (fun z => F (e.val.symm z)) =ᶠ[𝓝 (e.val x)] (fun _ => 0) :=
      ht.eventually hzero
    exact (multiplierIntegrableAt_zero (chartFunction v e) hc (e.val x) volume).congr
      EventuallyEq.rfl hzeroP.symm

private theorem iOrder_of_multiplierIdeals_le
    {m : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
    {u v : X → EReal} (hu : ManifoldQuasiPlurisubharmonic (n := m + 1) u)
    (hv : ManifoldQuasiPlurisubharmonic (n := m + 1) v)
    (hpreferred : ∀ c : ℝ, 0 < c →
      (multiplierIdeal (n := m + 1) c u).Le (multiplierIdeal (n := m + 1) c v)) :
    IOrderOnManifold (n := m + 1) u v := by
  intro c hc d z hz g _ hint'
  have hint : MultiplierIntegrableAt (chartFunction u d) c g z volume :=
    (QuasiEquisingularApproximationDemailly.multiplierIntegrableAt_ambient_iff_borel
      _ _ _ _).mpr hint'
  let x := d.val.symm z
  let F : X → ℂ := fun t => g (d.val t)
  have hx : x ∈ d.val.source := d.val.map_target hz
  have hxz : d.val x = z := d.val.right_inv hz
  have hgnear : ∀ᶠ t in 𝓝 z, DifferentiableAt ℂ g t := by
    obtain ⟨_, U, hU, hzU, hgd, _⟩ := hint
    filter_upwards [hU.mem_nhds hzU] with t ht
    exact (hgd t ht).differentiableAt (hU.mem_nhds ht)
  have hFhol : HolomorphicAt (m + 1) F x := by
    have hgnear' : ∀ᶠ t in 𝓝 (d.val x), DifferentiableAt ℂ g t := by rwa [hxz]
    filter_upwards [d.val.open_source.mem_nhds hx,
      (d.val.continuousAt hx).eventually hgnear'] with t ht hgt
    exact hgt.mdifferentiableAt.comp t
      (mdifferentiableAt_atlas (I := 𝓘(ℂ, ComplexModel (m + 1))) d.property ht)
  have hgF : g =ᶠ[𝓝 z] fun t => F (d.val.symm t) := by
    filter_upwards [d.val.open_target.mem_nhds hz] with t ht
    simp only [F, d.val.right_inv ht]
  have hdInt : MultiplierIntegrableAt (chartFunction u d) c
      (fun t => F (d.val.symm t)) (d.val x) volume := by
    rw [hxz]
    exact hint.congr (EventuallyEq.refl _ _) hgF
  let e := complexChartAt (n := m + 1) x
  have hue : UpperSemicontinuousOn (chartFunction u e) (ChartWeightedL2.overlapDomain e d) :=
    (hu e).upperSemicontinuousOn.mono fun _ ht => ht.1
  have hFmem : (multiplierIdeal (n := m + 1) c u).mem x F :=
    ⟨hFhol, ChartWeightedL2.multiplierIntegrableAt_chart (μ := volume)
      e d (mem_complexChartAt_source x) hx hue hc.ne' hdInt⟩
  have hVmem := hpreferred c hc x F hFmem
  have hvd : UpperSemicontinuousOn (chartFunction v d) (ChartWeightedL2.overlapDomain d e) :=
    (hv d).upperSemicontinuousOn.mono fun _ ht => ht.1
  have hVInt := ChartWeightedL2.multiplierIntegrableAt_chart (μ := volume)
    d e hx (mem_complexChartAt_source x) hvd hc.ne' hVmem.2
  rw [hxz] at hVInt
  apply (QuasiEquisingularApproximationDemailly.multiplierIntegrableAt_ambient_iff_borel
    _ _ _ _).mp
  exact hVInt.congr (EventuallyEq.refl _ _) hgF.symm


/-- Original raw all-chart order is exactly comparison on every genuine connected
smooth whole prime over the same original manifold. -/
theorem iOrder_iff_all_finite_connected_smooth_prime_orders
    {m : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
    {u v : X → EReal} (hu : ManifoldQuasiPlurisubharmonic (n := m + 1) u)
    (hv : ManifoldQuasiPlurisubharmonic (n := m + 1) v) :
    IOrderOnManifold (n := m + 1) u v ↔
      ∀ (Y : Type u) [TopologicalSpace Y]
        [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y] (π : Y → X),
        AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := m + 1) π →
        IsBlowupSequence (m + 1) X Y π →
        ∀ E : Set Y, IsClosed E → IsConnected E →
          (∀ z ∈ E, RegularAtDim (n := m + 1) E z m) →
            (⨅ z ∈ E, lelongNumber (n := m + 1) (fun w => v (π w)) z) ≤
              ⨅ z ∈ E, lelongNumber (n := m + 1) (fun w => u (π w)) z := by
  constructor
  · intro hI Y _ _ _ π hπ _hseq E hclosed hconn hreg
    exact (RawConnectedSmoothPrimeIdealOrder.iOrder_iff_all_connected_smooth_prime_orders
      hu hv).mp hI Y π hπ E hclosed hconn hreg
  · intro horder
    apply iOrder_of_multiplierIdeals_le hu hv
    intro c hc
    apply multiplierIdeal_le_of_all_finite_global_prime_orders hu hv
    · intro Y _ _ _ π hπ hseq V _hdim hreg
      have hconn : IsConnected V.carrier :=
        ⟨V.nonempty, CodimOneSupport.isPreconnected_of_isComplexAnalyticallyIrreducible
          V.irreducible_carrier⟩
      exact horder Y π hπ hseq V.carrier V.isClosed_carrier hconn hreg
    · exact hc

/-- The source's genuine right potential domain supplies the zero-dimensional
case internally; positive dimension retains the exact raw smooth-prime criterion. -/
theorem iOrder_iff_all_finite_connected_smooth_prime_orders_of_genuine_right
    {n : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    {u v : X → EReal} (hu : ManifoldQuasiPlurisubharmonic (n := n) u)
    (hv : IsGlobalQuasiPshPotential (n := n) v) :
    IOrderOnManifold (n := n) u v ↔
      ∀ (Y : Type u) [TopologicalSpace Y]
        [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y] (π : Y → X),
        IsAnalyticModification (n := n) π →
        IsBlowupSequence n X Y π →
        ∀ E : Set Y, IsClosed E → IsConnected E →
          (∃ k : ℕ, k + 1 = n ∧ ∀ z ∈ E, RegularAtDim (n := n) E z k) →
            (⨅ z ∈ E, lelongNumber (n := n) (fun w => v (π w)) z) ≤
              ⨅ z ∈ E, lelongNumber (n := n) (fun w => u (π w)) z := by
  cases n with
  | zero =>
    constructor
    · intro _hI Y _ _ _ π _hπ _hseq E _hclosed _hconn hhyper
      obtain ⟨k, hk, _hreg⟩ := hhyper
      omega
    · intro _horder
      exact ZeroDimensionalQuasiPshMultiplierIdeals.iOrderOnManifold_of_genuine_right u hv
  | succ m =>
    constructor
    · intro hI Y _ _ _ π hπ hseq E hclosed hconn hhyper
      obtain ⟨k, hk, hreg⟩ := hhyper
      have hkm : k = m := by omega
      subst k
      exact (iOrder_iff_all_finite_connected_smooth_prime_orders
        hu hv.1).mp hI Y π hπ hseq E hclosed hconn hreg
    · intro horder
      apply (iOrder_iff_all_finite_connected_smooth_prime_orders
        hu hv.1).mpr
      intro Y _ _ _ π hπ hseq E hclosed hconn hreg
      exact horder Y π hπ hseq E hclosed hconn ⟨m, rfl, hreg⟩

end
end SGPT.Foundations.Analysis.Pending.FiniteConnectedSmoothPrimeIdealOrder
