import SGPT.Foundations.Analysis.Pending.CalibratedCurrentWeakACLimit

set_option autoImplicit false

/-! Fixed-density calibration under an arbitrary nontrivial filter.
Boucksom Lemma 3.5's mollifier argument is used before the scalar filter
limit, without arbitrary-filter Fatou or uncountable null-set intersections.
Full mathematical blueprint and entire proofs precede Lean. -/

noncomputable section
open Set Filter MeasureTheory TopologicalSpace Metric
open scoped Topology ENNReal
namespace SGPT.Foundations.Analysis.Pending.FilterCalibratedCurrentACLimit
open FirstPass FirstPass.MongeAmpere FirstPass.PositiveClasses
  StronglyPositiveForms LocalProductCurrents LocalCurrentLebesgue
  LocalCurrentSemicontinuity LocalCurrentDeterminant PositiveCurrentACTopMeasure

private theorem ae_le_acInf_of_mol_bound {n q : ℕ} {U : Opens (ComplexModel n)}
    {T : LocalProductCurrent n U q} (hT : IsPositive T)
    {D : Set (formSpan n q)} (hDc : D.Countable) (hDne : D.Nonempty)
    (hDP : D ⊆ posCone n q) {G : ComplexModel n → ℝ≥0∞} (hGm : Measurable G)
    (hfatou : ∀ (z : ComplexModel n) (m : ℕ)
      (h : closedBall z (bump n m).rOut ⊆ U), ∀ c ∈ D,
      ∫⁻ y, ENNReal.ofReal (mol n m z y) * G y ≤
        ENNReal.ofReal (T c (bumpTest U m z h))) :
    ∀ᵐ x, x ∈ U → G x ≤ acInf hT D x := by
  obtain ⟨c₀, hc₀⟩ := hDne
  have hGloc : ∀ z ∈ (U : Set (ComplexModel n)), ∃ r > 0, ∫⁻ y in closedBall z r, G y ≠ ⊤ := by
    intro z hz
    obtain ⟨m, hm⟩ := (eventually_closedBall_subset (n := n) hz).exists
    refine ⟨(bump n m).rIn, (bump n m).rIn_pos, ?_⟩
    set a : ℝ := 1 / ∫ y, (bump n m) y ∂(volume : Measure (ComplexModel n)) with hadef
    have ha : 0 < a := one_div_pos.mpr (bump n m).integral_pos
    have hmol : ∀ y ∈ closedBall z (bump n m).rIn, mol n m z y = a := by
      intro y hy
      rw [mol, ContDiffBump.normed_def, (bump n m).one_of_mem_closedBall, hadef]
      rw [mem_closedBall, dist_zero_right, ← dist_eq_norm, dist_comm]
      exact mem_closedBall.mp hy
    have h0 : ENNReal.ofReal a ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr ha
    refine ne_top_of_le_ne_top (b := (ENNReal.ofReal a)⁻¹ * ENNReal.ofReal (T c₀ (bumpTest U m z hm)))
      (ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr h0) ENNReal.ofReal_ne_top) ?_
    calc ∫⁻ y in closedBall z (bump n m).rIn, G y
        ≤ ∫⁻ y in closedBall z (bump n m).rIn, (ENNReal.ofReal a)⁻¹ * (ENNReal.ofReal (mol n m z y) * G y) := by
          refine setLIntegral_mono' measurableSet_closedBall fun y hy => ?_
          rw [hmol y hy, ← mul_assoc, ENNReal.inv_mul_cancel h0 ENNReal.ofReal_ne_top, one_mul]
      _ ≤ ∫⁻ y, (ENNReal.ofReal a)⁻¹ * (ENNReal.ofReal (mol n m z y) * G y) := setLIntegral_le_lintegral _ _
      _ = (ENNReal.ofReal a)⁻¹ * ∫⁻ y, ENNReal.ofReal (mol n m z y) * G y :=
          lintegral_const_mul _ ((ENNReal.measurable_ofReal.comp (continuous_mol m z).measurable).mul hGm)
      _ ≤ (ENNReal.ofReal a)⁻¹ * ENNReal.ofReal (T c₀ (bumpTest U m z hm)) := by
          gcongr
          exact hfatou z m hm c₀ hc₀
  choose! r hr hGr using hGloc
  -- almost everywhere on `U`: `G` is finite, and its mollifications converge to it
  have hGfin : ∀ᵐ x, x ∈ U → G x < ⊤ := by
    refine ae_of_forall_ball fun z hz => ⟨r z, hr z hz, ?_⟩
    have h := ae_lt_top hGm (hGr z hz)
    rw [ae_restrict_iff' measurableSet_closedBall] at h
    filter_upwards [h] with x hx hxz
    exact hx (ball_subset_closedBall hxz)
  have hGconv := ae_tendsto_integral_mol_mul (n := n) (U := (U : Set (ComplexModel n))) (g := fun y => (G y).toReal)
    fun z hz => ⟨r z, hr z hz, integrable_toReal_of_lintegral_ne_top hGm.aemeasurable (hGr z hz)⟩
  have hTconv : ∀ᵐ x, ∀ c ∈ D, x ∈ U → Tendsto (fun m => (∫ y, mol n m x y * (acWeight hT y * densityForm hT y c)) +
      ∫ y, mol n m x y * densityForm hT y c ∂(sgMeasure hT)) atTop (𝓝 (acWeight hT x * densityForm hT x c)) :=
    (ae_ball_iff hDc).mpr fun c _ => ae_tendsto_apply_bumpTest hT c
  filter_upwards [hGfin, hGconv, hTconv] with x hfin hconvG hconvT hx
  refine le_iInf₂ fun c hc => ?_
  show G x ≤ _
  rw [← ENNReal.ofReal_toReal (hfin hx).ne]
  refine ENNReal.ofReal_le_ofReal (le_of_tendsto_of_tendsto (hconvG hx) (hconvT c hc hx) ?_)
  filter_upwards [eventually_closedBall_subset (n := n) hx] with m hm
  have hpos : 0 ≤ T c (bumpTest U m x hm) :=
    hT.positiveDistribution (hDP hc) _ fun y => mol_nonneg m x y
  have hlin : ∫⁻ y, ENNReal.ofReal (mol n m x y) * G y ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hfatou x m hm c hc)
  rw [← apply_bumpTest hT c hm]
  calc ∫ y, mol n m x y * (G y).toReal
      = (∫⁻ y, ENNReal.ofReal (mol n m x y * (G y).toReal)).toReal :=
        integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun y => mul_nonneg (mol_nonneg m x y)
          ENNReal.toReal_nonneg) ((continuous_mol m x).measurable.mul hGm.ennreal_toReal).aestronglyMeasurable
    _ ≤ (∫⁻ y, ENNReal.ofReal (mol n m x y) * G y).toReal := by
        refine ENNReal.toReal_mono hlin (lintegral_mono fun y => ?_)
        rw [ENNReal.ofReal_mul (mol_nonneg m x y)]
        exact mul_le_mul_right ENNReal.ofReal_toReal_le _
    _ ≤ (ENNReal.ofReal (T c (bumpTest U m x hm))).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top (hfatou x m hm c hc)
    _ = T c (bumpTest U m x hm) := ENNReal.toReal_ofReal hpos


/-- Actual fixed reference infimum calibration survives every nontrivial
filter weak limit. Each index null set is used only inside its integral. -/
theorem ae_scaled_acInf_le_of_calibrated_filter
    {n q : ℕ} {U : Opens (ComplexModel n)} {ι : Type*} {l : Filter ι} [l.NeBot]
    {T : ι → LocalProductCurrent n U q} {T₀ R : LocalProductCurrent n U q}
    (hT : ∀ i, IsPositive (T i)) (hT₀ : IsPositive T₀) (hR : IsPositive R)
    (hconv : ∀ γ φ, Tendsto (fun i => T i γ φ) l (𝓝 (T₀ γ φ)))
    {c : ι → ℝ} {a : ℝ} (hc : ∀ i, 0 ≤ c i) (hca : Tendsto c l (𝓝 a))
    {C : Set (formSpan n q)} (hC : C ⊆ posCone n q)
    (hcal : ∀ i, ∀ᵐ x ∂volume.restrict U,
      acInf (hT i) C x = ENNReal.ofReal (c i) * acInf hR C x) :
    0 ≤ a ∧ ∀ᵐ x, x ∈ U → ENNReal.ofReal a * acInf hR C x ≤ acInf hT₀ C x := by
  classical
  refine ⟨ge_of_tendsto hca (Eventually.of_forall hc), ?_⟩
  rcases C.eq_empty_or_nonempty with rfl | hCne
  · exact Eventually.of_forall fun x _ => by simp [acInf]
  obtain ⟨D, hDC, hDc, hCD⟩ := (IsSeparable.of_separableSpace C).exists_countable_dense_subset
  have hDne : D.Nonempty := by
    obtain ⟨γ, hγ⟩ := hCne
    by_contra hD
    rw [not_nonempty_iff_eq_empty] at hD
    simpa only [hD, closure_empty, mem_empty_iff_false] using hCD hγ
  have hDP : D ⊆ posCone n q := hDC.trans hC
  simp_rw [acInf_eq_of_subset_closure _ hDC hCD] at hcal ⊢
  let G : ComplexModel n → ℝ≥0∞ := fun y => ENNReal.ofReal a * acInf hR D y
  have hGm : Measurable G := measurable_const.mul (measurable_acInf hR hDc)
  apply ae_le_acInf_of_mol_bound hT₀ hDc hDne hDP hGm
  intro z j hj γ hγ
  let I : ℝ≥0∞ := ∫⁻ y, ENNReal.ofReal (mol n j z y) * acInf hR D y
  have hI : I ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (lintegral_mol_mul_acInf_le hR hDP hγ hj)
  have hi (i : ι) : ENNReal.ofReal (c i) * I ≤
      ENNReal.ofReal (T i γ (bumpTest U j z hj)) := by
    calc ENNReal.ofReal (c i) * I
        = ∫⁻ y, ENNReal.ofReal (mol n j z y) *
            (ENNReal.ofReal (c i) * acInf hR D y) := by
          dsimp only [I]
          rw [← lintegral_const_mul' (ENNReal.ofReal (c i))
            (fun y => ENNReal.ofReal (mol n j z y) * acInf hR D y) ENNReal.ofReal_ne_top]
          congr 1
          funext y
          ring
      _ = ∫⁻ y, ENNReal.ofReal (mol n j z y) * acInf (hT i) D y := by
          apply lintegral_congr_ae
          filter_upwards [(ae_restrict_iff' U.isOpen.measurableSet).mp (hcal i)] with y hy
          by_cases hmol : mol n j z y = 0
          · simp only [hmol, ENNReal.ofReal_zero, zero_mul]
          · rw [hy (hj (mem_closedBall.mpr (dist_lt_of_mol_ne_zero hmol).le))]
      _ ≤ ENNReal.ofReal (T i γ (bumpTest U j z hj)) :=
          lintegral_mol_mul_acInf_le (hT i) hDP hγ hj
  have hleft : Tendsto (fun i => ENNReal.ofReal (c i) * I) l
      (𝓝 (ENNReal.ofReal a * I)) :=
    ((ENNReal.continuous_mul_const hI).tendsto _).comp
      ((ENNReal.continuous_ofReal.tendsto _).comp hca)
  have hright := (ENNReal.continuous_ofReal.tendsto _).comp
    (hconv γ (bumpTest U j z hj))
  have hlim := le_of_tendsto_of_tendsto hleft hright (Eventually.of_forall hi)
  calc ∫⁻ y, ENNReal.ofReal (mol n j z y) * G y
      = ENNReal.ofReal a * I := by
        dsimp only [G,I]
        rw [← lintegral_const_mul' (ENNReal.ofReal a)
          (fun y => ENNReal.ofReal (mol n j z y) * acInf hR D y) ENNReal.ofReal_ne_top]
        congr 1
        funext y
        ring
    _ ≤ ENNReal.ofReal (T₀ γ (bumpTest U j z hj)) := hlim

private theorem topDensity_eq_det {m : ℕ} {U : Opens (ComplexModel (m+1))}
    {S : LocalProductCurrent (m+1) U m} (hS : IsPositive S) (x : ComplexModel (m+1)) :
    actualTopPowerDensity (acForm hS x) =
      ((m+1).factorial : ℝ) / Real.pi ^ (m+1) * (acMatrix hS x).det.re := by
  rw [actualTopPowerDensity_eq_normalizedTopPowerDensity _ (isOneOne_acForm hS x),
    normalizedTopPowerDensity, complexTopCoefficient_eq]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rfl

/-- Actual top-density calibration of each positive original current implies
complete measure domination for any nontrivial filter weak limit. -/
theorem acTopMeasure_le_of_calibrated_filter
    {m : ℕ} {U : Opens (ComplexModel (m+1))} {ι : Type*} {l : Filter ι} [l.NeBot]
    {T : ι → LocalProductCurrent (m+1) U m}
    {T₀ R : LocalProductCurrent (m+1) U m}
    (hT : ∀ i, IsPositive (T i)) (hT₀ : IsPositive T₀) (hR : IsPositive R)
    (hconv : ∀ γ φ, Tendsto (fun i => T i γ φ) l (𝓝 (T₀ γ φ)))
    {c : ι → ℝ} {a : ℝ} (hc : ∀ i, 0 ≤ c i) (hca : Tendsto c l (𝓝 a))
    (hcal : ∀ i, ∀ᵐ x ∂volume.restrict U,
      actualTopPowerDensity (acForm (hT i) x) =
        c i * actualTopPowerDensity (acForm hR x)) :
    ENNReal.ofReal a • acTopMeasure hR ≤ acTopMeasure hT₀ := by
  have ha : 0 ≤ a := ge_of_tendsto hca (Eventually.of_forall hc)
  let N : ℝ := ((m+1).factorial : ℝ) / Real.pi ^ (m+1)
  let r : ℝ := ((m+1 : ℕ) : ℝ)⁻¹
  have hN : 0 < N := by dsimp [N]; positivity
  have hr : 0 < r := by dsimp [r]; positivity
  have hrootcal (i : ι) : ∀ᵐ x ∂volume.restrict U,
      acInf (hT i) (detCone m) x =
        ENNReal.ofReal (c i ^ r) * acInf hR (detCone m) x := by
    filter_upwards [hcal i, ae_restrict_of_ae (ae_acInf_detCone_eq_acMatrix (hT i)),
      ae_restrict_of_ae (ae_acInf_detCone_eq_acMatrix hR),
      ae_restrict_of_ae (ae_posSemidef_acMatrix hR)] with x hx hxi hxr hxpsd
    rw [topDensity_eq_det, topDensity_eq_det] at hx
    have hd : (acMatrix (hT i) x).det.re = c i * (acMatrix hR x).det.re := by
      apply mul_left_cancel₀ hN.ne'
      calc N * (acMatrix (hT i) x).det.re
          = c i * (N * (acMatrix hR x).det.re) := hx
        _ = N * (c i * (acMatrix hR x).det.re) := by ring
    rw [hxi, hxr, hd, Real.mul_rpow (hc i) (MinkowskiDeterminant.re_det_nonneg hxpsd)]
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (hc i) r)]
    congr 1
    ring
  have hroots := (ae_scaled_acInf_le_of_calibrated_filter hT hT₀ hR hconv
    (fun i => Real.rpow_nonneg (hc i) r)
    ((continuous_id.rpow_const (fun _ => Or.inr hr.le)).tendsto a |>.comp hca)
    detCone_subset_posCone hrootcal).2
  have hbound : ∀ᵐ x ∂volume.restrict U,
      a * actualTopPowerDensity (acForm hR x) ≤ actualTopPowerDensity (acForm hT₀ x) := by
    filter_upwards [ae_restrict_of_ae hroots,
      ae_restrict_of_ae (ae_acInf_detCone_eq_acMatrix hR),
      ae_restrict_of_ae (ae_acInf_detCone_eq_acMatrix hT₀),
      ae_restrict_of_ae (ae_posSemidef_acMatrix hR),
      ae_restrict_of_ae (ae_posSemidef_acMatrix hT₀),
      ae_restrict_mem U.isOpen.measurableSet] with x hx hxR hxT hxRpos hxTpos hxU
    have hle := hx hxU
    rw [hxR, hxT] at hle
    change ENNReal.ofReal (a ^ r) *
      ENNReal.ofReal (N * (acMatrix hR x).det.re ^ r) ≤
      ENNReal.ofReal (N * (acMatrix hT₀ x).det.re ^ r) at hle
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg ha r)] at hle
    have hle' : N * (a * (acMatrix hR x).det.re) ^ r ≤
        N * (acMatrix hT₀ x).det.re ^ r := by
      have h := (ENNReal.ofReal_le_ofReal_iff
        (mul_nonneg hN.le (Real.rpow_nonneg (MinkowskiDeterminant.re_det_nonneg hxTpos) r))).mp hle
      simpa only [N,r,Real.mul_rpow ha (MinkowskiDeterminant.re_det_nonneg hxRpos),
        mul_left_comm, mul_assoc] using h
    have hbase := (Real.rpow_le_rpow_iff
      (mul_nonneg ha (MinkowskiDeterminant.re_det_nonneg hxRpos))
      (MinkowskiDeterminant.re_det_nonneg hxTpos) hr).mp
        ((mul_le_mul_iff_right₀ hN).mp hle')
    rw [topDensity_eq_det, topDensity_eq_det]
    change a * (N * (acMatrix hR x).det.re) ≤ N * (acMatrix hT₀ x).det.re
    calc a * (N * (acMatrix hR x).det.re) = N * (a * (acMatrix hR x).det.re) := by ring
      _ ≤ N * (acMatrix hT₀ x).det.re := mul_le_mul_of_nonneg_left hbase hN.le
  unfold acTopMeasure
  rw [← Measure.restrict_smul, ← withDensity_smul' _ _ ENNReal.ofReal_ne_top,
    restrict_withDensity U.isOpen.measurableSet, restrict_withDensity U.isOpen.measurableSet]
  apply withDensity_mono
  filter_upwards [hbound] with x hx
  change ENNReal.ofReal a * ENNReal.ofReal _ ≤ ENNReal.ofReal _
  rw [← ENNReal.ofReal_mul ha]
  exact ENNReal.ofReal_le_ofReal hx

end SGPT.Foundations.Analysis.Pending.FilterCalibratedCurrentACLimit
