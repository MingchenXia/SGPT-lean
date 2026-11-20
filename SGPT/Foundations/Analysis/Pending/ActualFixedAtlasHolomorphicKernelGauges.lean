import SGPT.Foundations.Analysis.Pending.ActualGlobalSquaredBergmanDensity
import SGPT.Foundations.Analysis.Pending.FiniteBergmanOverlapLogSumCocycle
import SGPT.Foundations.Analysis.FirstPass.LocalPotentialPullback

set_option autoImplicit false

/-! # Actual common theta gauges of the original fixed squared kernels -/
noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology Manifold ContDiff ENNReal Classical
namespace SGPT.Foundations.Analysis.Pending.ActualFixedAtlasHolomorphicKernelGauges
open FirstPass FirstPass.PositiveClasses FirstPass.HolomorphicMaps
  FirstPass.LocalPotentialPullback QuantitativeRegularizationFixedCover
  QuantitativeRegularizationChartBranch ActualGlobalSquaredBergmanDensity
  BergmanKernelSmooth BergmanSupWeight GlobalTubeFunction

variable {n : ℕ} {X : Type*} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

private theorem local_gauges (F : FixedChartCover n X)
    {θ : ClosedRealOneOneForm n X} {ρ : F.t → ComplexModel n → ℝ}
    (hρ : ∀ j, IsSmoothLocalPotential θ.val (F.chart j)
      (ball (F.center j) (F.potentialRadius j)) (ρ j)) (x : X) :
    ∃ i : F.t, x ∈ F.cover.U i ∧
      ∃ (r : ℝ) (g : {j : F.t // x ∈ closure (F.cover.V j)} → ComplexModel n → ℂ),
        0 < r ∧ ball ((F.chart i).val x) r ⊆ (F.chart i).val.target ∧
        (∀ z ∈ ball ((F.chart i).val x) r, (F.chart i).val.symm z ∈ F.cover.U i) ∧
        (∀ j, DifferentiableOn ℂ (g j) (ball ((F.chart i).val x) r) ∧
          ∀ z ∈ ball ((F.chart i).val x) r,
            (g j z).re = ρ i z - ρ j.val ((F.chart j.val).val ((F.chart i).val.symm z)) ∧
            z ∈ coordinateDomain (id : X → X) (F.chart i) (F.chart j.val) ∧
            coordinateMap (id : X → X) (F.chart i) (F.chart j.val) z ∈
              ball (F.center j.val) (F.bergmanRadius j.val)) ∧
        (∀ j : F.t, x ∉ closure (F.cover.V j) →
          ∀ z ∈ ball ((F.chart i).val x) r, (F.chart i).val.symm z ∉ F.cover.V j) := by
  classical
  obtain ⟨i, hxi⟩ := F.cover.cover x
  let e := F.chart i
  let z₀ := e.val x
  let J := {j : F.t // x ∈ closure (F.cover.V j)}
  have hxiV := F.cover.U_subset_V i hxi
  have hxpatch := F.closure_V_subset_chartPatch i (subset_closure hxiV)
  have hzT : z₀ ∈ e.val.target := e.val.map_source hxpatch.1
  have hsymm : e.val.symm z₀ = x := e.val.left_inv hxpatch.1
  let D : F.t → Set (ComplexModel n) := fun j =>
    if x ∈ closure (F.cover.V j) then
      potentialDomain (id : X → X) e (F.chart j) (ball (F.center j) (F.bergmanRadius j))
    else e.val.target ∩ e.val.symm ⁻¹' (closure (F.cover.V j))ᶜ
  have hDo : ∀ j, IsOpen (D j) := by
    intro j
    dsimp only [D]
    split_ifs
    · exact potentialDomain_isOpen contMDiff_id e (F.chart j) isOpen_ball
    · exact e.val.isOpen_inter_preimage_symm isClosed_closure.isOpen_compl
  have hzD : ∀ j, z₀ ∈ D j := by
    intro j
    dsimp only [D]
    split_ifs with hj
    · have hxj := F.closure_V_subset_chartPatch j hj
      exact ⟨mem_coordinateDomain hxpatch.1 hxj.1, by
        change (F.chart j).val (e.val.symm z₀) ∈ ball (F.center j) (F.bergmanRadius j)
        rw [hsymm]
        exact hxj.2⟩
    · exact ⟨hzT, by simpa only [mem_preimage, mem_compl_iff, hsymm] using hj⟩
  let V := (e.val.target ∩ ball (F.center i) (F.potentialRadius i)) ∩
    (e.val.target ∩ e.val.symm ⁻¹' F.cover.U i) ∩ ⋂ j, D j
  have hVo : IsOpen V :=
    (e.val.open_target.inter isOpen_ball).inter
      (e.val.isOpen_inter_preimage_symm (F.cover.isOpen_U i)) |>.inter
      (isOpen_iInter_of_finite hDo)
  have hzV : z₀ ∈ V := by
    refine ⟨⟨⟨hzT, ?_⟩, hzT, ?_⟩, mem_iInter.mpr hzD⟩
    · exact ball_subset_ball (F.bergmanRadius_lt_potentialRadius i).le hxpatch.2
    · simpa only [mem_preimage, hsymm] using hxi
  obtain ⟨t, ht, htV⟩ := Metric.isOpen_iff.mp hVo z₀ hzV
  have hσ : IsSmoothLocalPotential θ.val e (ball z₀ t) (ρ i) :=
    (hρ i).mono isOpen_ball (fun z hz => (htV hz).1.1.2)
  have hlocal : ∀ j : J, IsSmoothLocalPotential θ.val e (ball z₀ t)
      (ρ j.val ∘ coordinateMap (id : X → X) e (F.chart j.val)) := by
    intro j
    have hpull := isSmoothLocalPotential_pullback (f := (id : X → X))
      contMDiff_id e (hρ j.val)
    have hsame := (SmoothRealForm.pullback_id_geometricallyEq θ.val).localPotential_iff
      e _ _ |>.mp hpull
    apply hsame.mono isOpen_ball
    intro z hz
    have hD : z ∈ potentialDomain (id : X → X) e (F.chart j.val)
        (ball (F.center j.val) (F.bergmanRadius j.val)) := by
      have h := mem_iInter.mp (htV hz).2 j.val
      simpa only [D, if_pos j.property] using h
    have hmap : coordinateMap (id : X → X) e (F.chart j.val) z ∈
        ball (F.center j.val) (F.potentialRadius j.val) :=
      ball_subset_ball (F.bergmanRadius_lt_potentialRadius j.val).le hD.2
    exact ⟨hD.1, hmap⟩
  choose g hg hre using fun j : J =>
    FiniteBergmanOverlapLogSumCocycle.exists_holomorphic_additiveTransition_of_localPotentialsOnBall
      e ht (hlocal j) hσ
  have hsub : ball z₀ (t / 2) ⊆ ball z₀ t := ball_subset_ball (by linarith)
  refine ⟨i, hxi, t / 2, g, by positivity, ?_, ?_, ?_, ?_⟩
  · exact fun z hz => (htV (hsub hz)).1.1.1
  · exact fun z hz => (htV (hsub hz)).1.2.2
  · intro j
    refine ⟨hg j, fun z hz => ?_⟩
    have hD : z ∈ potentialDomain (id : X → X) e (F.chart j.val)
        (ball (F.center j.val) (F.bergmanRadius j.val)) := by
      have h := mem_iInter.mp (htV (hsub hz)).2 j.val
      simpa only [D, if_pos j.property] using h
    exact ⟨by simpa only [Function.comp_apply, coordinateMap, id_eq] using hre j z hz,
      hD.1, hD.2⟩
  · intro j hj z hz
    have hD := mem_iInter.mp (htV (hsub hz)).2 j
    dsimp only [D] at hD
    rw [if_neg hj] at hD
    exact fun h => hD.2 (subset_closure h)

private theorem original_weight (F : FixedChartCover n X)
    {θ : ClosedRealOneOneForm n X} {ρ : F.t → ComplexModel n → ℝ}
    (hρ : ∀ j, IsSmoothLocalPotential θ.val (F.chart j)
      (ball (F.center j) (F.potentialRadius j)) (ρ j))
    {u : X → EReal} (hu : IsThetaPshPotential θ.val u)
    {k : ℕ} (hk : 0 < k) (j : F.t) :
    BergmanWeight (ball (F.center j) (F.bergmanRadius j))
      (fun z => multiplierWeight k (correctedWeight (F.chart j) (ρ j) u z)) := by
  let B := ball (F.center j) (F.bergmanRadius j)
  let Ω := ball (F.center j) (F.potentialRadius j)
  let Ψ := correctedWeight (F.chart j) (ρ j) u
  have hBΩ : B ⊆ Ω := ball_subset_ball (F.bergmanRadius_lt_potentialRadius j).le
  have hΨ : PlurisubharmonicOn Ψ Ω := F.plurisubharmonicOn_correctedWeight hρ hu.1 j
  have hkR : 0 < (k : ℝ) := Nat.cast_pos.mpr hk
  refine ⟨isOpen_ball, DemaillyApproximation.aemeasurable_multiplierWeight_restrict
    isOpen_ball (hΨ.upperSemicontinuousOn.mono hBΩ) hkR.ne', ?_⟩
  intro z hz
  obtain ⟨ε, hε, hεB⟩ := Metric.isOpen_iff.mp isOpen_ball z hz
  have hcb : closedBall z (ε / 2) ⊆ B :=
    (closedBall_subset_ball (by linarith)).trans hεB
  obtain ⟨C, _, hC⟩ := hΨ.exists_nonnegative_compact_upper_bound
    (isCompact_closedBall z (ε / 2)) (hcb.trans hBΩ)
  refine ⟨Real.exp (-(k * C)), Real.exp_pos _, ε / 2, by positivity, hcb, fun t ht => ?_⟩
  rw [← multiplierWeight_coe]
  exact multiplierWeight_antitone hkR.le (hC t ht)

private theorem norm_sq_exponential_smul {H : Type*} [NormedAddCommGroup H]
    [NormedSpace ℂ H] (k : ℕ) (g : ℂ) (A : H) :
    ‖Complex.exp (((k : ℝ) / 2 : ℝ) * g) • A‖ ^ 2 =
      Real.exp ((k : ℝ) * g.re) * ‖A‖ ^ 2 := by
  rw [norm_smul, mul_pow, Complex.norm_exp, pow_two, ← Real.exp_add]
  have he : ((((k : ℝ) / 2 : ℝ) : ℂ) * g).re +
      ((((k : ℝ) / 2 : ℝ) : ℂ) * g).re = (k : ℝ) * g.re := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    ring
  rw [he]

/-- For the actual prescribed potentials, ONE ball/gauges before ALL u and k,
with the very same squared density on every chart. -/
theorem all_level_holomorphic_kernel_gauges
    (F : FixedChartCover n X) (θ : ClosedRealOneOneForm n X)
    (ρ : F.t → ComplexModel n → ℝ)
    (hρ : ∀ j, IsSmoothLocalPotential θ.val (F.chart j)
      (ball (F.center j) (F.potentialRadius j)) (ρ j)) :
    ∀ x : X, ∃ i : F.t, x ∈ F.cover.U i ∧
        ∃ (r : ℝ) (g : {j : F.t // x ∈ closure (F.cover.V j)} → ComplexModel n → ℂ),
          0 < r ∧ ball ((F.chart i).val x) r ⊆ (F.chart i).val.target ∧
          (∀ z ∈ ball ((F.chart i).val x) r, (F.chart i).val.symm z ∈ F.cover.U i) ∧
          (∀ j, DifferentiableOn ℂ (g j) (ball ((F.chart i).val x) r) ∧
            ∀ z ∈ ball ((F.chart i).val x) r,
              (g j z).re = ρ i z - ρ j.val ((F.chart j.val).val ((F.chart i).val.symm z)) ∧
              z ∈ coordinateDomain (id : X → X) (F.chart i) (F.chart j.val) ∧
              coordinateMap (id : X → X) (F.chart i) (F.chart j.val) z ∈
                ball (F.center j.val) (F.bergmanRadius j.val)) ∧
          ∀ (u : X → EReal), IsThetaPshPotential θ.val u → ∀ k : ℕ, 0 < k →
            ∃ hBw : ∀ j, BergmanWeight (ball (F.center j) (F.bergmanRadius j))
              (fun z => multiplierWeight k (correctedWeight (F.chart j) (ρ j) u z)),
              (∀ j : {j : F.t // x ∈ closure (F.cover.V j)}, DifferentiableOn ℂ
                (fun z => Complex.exp (((k : ℝ) / 2 : ℝ) * g j z) •
                  evalCLM (hBw j.val) ((F.chart j.val).val ((F.chart i).val.symm z)))
                (ball ((F.chart i).val x) r)) ∧
              ∀ z ∈ ball ((F.chart i).val x) r,
                density F ρ u k ((F.chart i).val.symm z) =
                  Real.exp (-(k : ℝ) * ρ i z) *
                    ∑ j : {j : F.t // x ∈ closure (F.cover.V j)},
                      F.cover.χ j.val ((F.chart i).val.symm z) ^ 2 *
                        ‖Complex.exp (((k : ℝ) / 2 : ℝ) * g j z) •
                          evalCLM (hBw j.val) ((F.chart j.val).val ((F.chart i).val.symm z))‖ ^ 2 := by
  classical
  intro x
  obtain ⟨i, hxi, r, g, hr, htarget, hcore, hg, hinactive⟩ := local_gauges F hρ x
  refine ⟨i, hxi, r, g, hr, htarget, hcore, hg, fun u hu k hk => ?_⟩
  let hBw := fun j => original_weight F hρ hu hk j
  refine ⟨hBw, ?_, ?_⟩
  · intro j
    have hT : DifferentiableOn ℂ
        (coordinateMap (id : X → X) (F.chart i) (F.chart j.val))
        (ball ((F.chart i).val x) r) :=
      ((coordinateMap_contDiffOn contMDiff_id (F.chart i) (F.chart j.val)).differentiableOn
        (by simp)).mono (fun z hz => (hg j).2 z hz |>.2.1)
    have hA := DifferentiableOn.comp (𝕜 := ℂ) (E := ComplexModel n)
      (F := ComplexModel n)
      (G := StrongDual ℂ (bergmanSubspace
        (ball (F.center j.val) (F.bergmanRadius j.val))
        (fun z => multiplierWeight k (correctedWeight (F.chart j.val) (ρ j.val) u z))))
      (differentiableOn_evalCLM (hBw j.val)) hT
      (fun z hz => ((hg j).2 z hz).2.2)
    have hexp := Complex.differentiable_exp.comp_differentiableOn
      ((hg j).1.const_mul (((k : ℝ) / 2 : ℝ) : ℂ))
    convert hexp.smul hA using 1 <;> first
    | rfl
    | exact IsBoundedSMul.of_norm_smul_le (fun (a : ℂ)
        (b : StrongDual ℂ (bergmanSubspace
          (ball (F.center j.val) (F.bergmanRadius j.val))
          (fun z => multiplierWeight k
            (correctedWeight (F.chart j.val) (ρ j.val) u z)))) =>
          ContinuousLinearMap.opNorm_smul_le a b)
  · intro z hz
    let y := (F.chart i).val.symm z
    let J := {j : F.t // x ∈ closure (F.cover.V j)}
    have heq (j : J) :
        bumpExtend (F.cover.V j.val) (fun t => F.cover.χ j.val t * F.cover.χ j.val t)
          (localDensity F ρ u k j.val) y =
        Real.exp (-(k : ℝ) * ρ i z) *
          (F.cover.χ j.val y ^ 2 *
            ‖Complex.exp (((k : ℝ) / 2 : ℝ) * g j z) •
              evalCLM (hBw j.val) ((F.chart j.val).val y)‖ ^ 2) := by
      by_cases hyV : y ∈ F.cover.V j.val
      · rw [bumpExtend_of_mem hyV]
        dsimp only [localDensity]
        rw [bergmanSup_eq_ofReal_norm_evalCLM_sq (hBw j.val)
          (show (F.chart j.val).val y ∈ ball (F.center j.val) (F.bergmanRadius j.val)
            from ((hg j).2 z hz).2.2), ENNReal.toReal_ofReal (sq_nonneg _)]
        have hn := norm_sq_exponential_smul k (g j z)
          (evalCLM (hBw j.val) ((F.chart j.val).val y))
        rw [hn, ((hg j).2 z hz).1]
        have hex : Real.exp (-(k : ℝ) * ρ i z) *
            Real.exp ((k : ℝ) * (ρ i z - ρ j.val ((F.chart j.val).val y))) =
            Real.exp (-(k : ℝ) * ρ j.val ((F.chart j.val).val y)) := by
          rw [← Real.exp_add]
          congr 1
          ring
        calc
          _ = (F.cover.χ j.val y ^ 2 *
                (Real.exp (-(k : ℝ) * ρ i z) *
                  Real.exp ((k : ℝ) * (ρ i z - ρ j.val ((F.chart j.val).val y))))) *
                ‖evalCLM (hBw j.val) ((F.chart j.val).val y)‖ ^ 2 := by rw [hex]; ring
          _ = _ := by ring
      · have hχ : F.cover.χ j.val y = 0 :=
          image_eq_zero_of_notMem_tsupport (fun h => hyV (F.cover.tsupport_χ_subset j.val h))
        rw [bumpExtend_of_notMem hyV, hχ]
        simp
    have hzsum : ∑ j : F.t,
        bumpExtend (F.cover.V j) (fun t => F.cover.χ j t * F.cover.χ j t)
          (localDensity F ρ u k j) y =
        ∑ j : J, bumpExtend (F.cover.V j.val)
          (fun t => F.cover.χ j.val t * F.cover.χ j.val t) (localDensity F ρ u k j.val) y := by
      have hfull : (∑ j : F.t, if hj : x ∈ closure (F.cover.V j) then
          bumpExtend (F.cover.V j) (fun t => F.cover.χ j t * F.cover.χ j t)
            (localDensity F ρ u k j) y else 0) =
          ∑ j : F.t, bumpExtend (F.cover.V j) (fun t => F.cover.χ j t * F.cover.χ j t)
            (localDensity F ρ u k j) y := by
        apply Finset.sum_congr rfl
        intro j _
        split_ifs with hj
        · rfl
        · exact (bumpExtend_of_notMem (hinactive j hj z hz)).symm
      rw [← hfull]
      rw [Finset.sum_dite]
      simp only [Finset.sum_const_zero, add_zero]
      exact (Equiv.subtypeEquivRight (by simp)).sum_comp
        (fun j : J => bumpExtend (F.cover.V j.val)
          (fun t => F.cover.χ j.val t * F.cover.χ j.val t)
          (localDensity F ρ u k j.val) y)
    change (∑ j : F.t, bumpExtend (F.cover.V j) (fun t => F.cover.χ j t * F.cover.χ j t)
      (localDensity F ρ u k j) y) = _
    rw [hzsum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => heq j

/-- Natural fixed-cover theta potentials and ONE local ball/gauges before
ALL original potentials and levels, with the literal squared density unchanged. -/
theorem exists_fixed_potentials_all_level_holomorphic_kernel_gauges
    (F : FixedChartCover n X) (θ : ClosedRealOneOneForm n X) :
    ∃ ρ : F.t → ComplexModel n → ℝ,
      (∀ j, IsSmoothLocalPotential θ.val (F.chart j)
        (ball (F.center j) (F.potentialRadius j)) (ρ j)) ∧
      ∀ x : X, ∃ i : F.t, x ∈ F.cover.U i ∧
        ∃ (r : ℝ) (g : {j : F.t // x ∈ closure (F.cover.V j)} → ComplexModel n → ℂ),
          0 < r ∧ ball ((F.chart i).val x) r ⊆ (F.chart i).val.target ∧
          (∀ z ∈ ball ((F.chart i).val x) r, (F.chart i).val.symm z ∈ F.cover.U i) ∧
          (∀ j, DifferentiableOn ℂ (g j) (ball ((F.chart i).val x) r) ∧
            ∀ z ∈ ball ((F.chart i).val x) r,
              (g j z).re = ρ i z - ρ j.val ((F.chart j.val).val ((F.chart i).val.symm z)) ∧
              z ∈ coordinateDomain (id : X → X) (F.chart i) (F.chart j.val) ∧
              coordinateMap (id : X → X) (F.chart i) (F.chart j.val) z ∈
                ball (F.center j.val) (F.bergmanRadius j.val)) ∧
          ∀ (u : X → EReal), IsThetaPshPotential θ.val u → ∀ k : ℕ, 0 < k →
            ∃ hBw : ∀ j, BergmanWeight (ball (F.center j) (F.bergmanRadius j))
              (fun z => multiplierWeight k (correctedWeight (F.chart j) (ρ j) u z)),
              (∀ j : {j : F.t // x ∈ closure (F.cover.V j)}, DifferentiableOn ℂ
                (fun z => Complex.exp (((k : ℝ) / 2 : ℝ) * g j z) •
                  evalCLM (hBw j.val) ((F.chart j.val).val ((F.chart i).val.symm z)))
                (ball ((F.chart i).val x) r)) ∧
              ∀ z ∈ ball ((F.chart i).val x) r,
                density F ρ u k ((F.chart i).val.symm z) =
                  Real.exp (-(k : ℝ) * ρ i z) *
                    ∑ j : {j : F.t // x ∈ closure (F.cover.V j)},
                      F.cover.χ j.val ((F.chart i).val.symm z) ^ 2 *
                        ‖Complex.exp (((k : ℝ) / 2 : ℝ) * g j z) •
                          evalCLM (hBw j.val) ((F.chart j.val).val ((F.chart i).val.symm z))‖ ^ 2 := by
  obtain ⟨ρ, hρ⟩ := F.exists_potentials θ
  exact ⟨ρ, hρ, all_level_holomorphic_kernel_gauges F θ ρ hρ⟩

end SGPT.Foundations.Analysis.Pending.ActualFixedAtlasHolomorphicKernelGauges
