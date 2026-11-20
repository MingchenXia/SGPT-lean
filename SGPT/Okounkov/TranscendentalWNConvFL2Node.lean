import SGPT.Okounkov.TranscendentalWNConvFL2Small
import SGPT.Okounkov.TranscendentalWNKeyLSCExcLocal
import SGPT.Okounkov.TranscendentalCoreSiuLocal

/-!
# Small fibre volumes near the node `X' ∩ ℰ`

Blueprint `claude-tok-wn-fl2`, nodes `tok-wn-fl2:node-param`, `tok-wn-fl2:node-local`; source
WN21 §7, estimate (eqeq) (`references/wn21-restricted-volume`).

At `q ∈ X' ∩ ℰ` the monomial chart is `j = m` (`w_m = z₁`, `τ = w_m w_{m+1}`), with
`w_m(q) = w_{m+1}(q) = 0`.  The fibre `X_τ` (`τ ≠ 0`) is `{w_m w_{m+1} = t}` in the chart.  At
each of its points `|w_m|² ≥ |t|` or `|w_{m+1}|² ≥ |t|`; accordingly it is parametrized by
`y = (w', w_m)` through `Λ₁(t, y) = (y, t / y_m)` or by `y = (w', w_{m+1})` through
`Λ₂(t, y) = swap(y, t / y_m)`, and in both cases `|∂_y Λ| ≤ ‖splitL‖` on the relevant region
`|t| ≤ |y_m|²`.  Hence, in the polydisc `U_R = {ν_i(W) ∈ B(a, ρ), |w_m|, |w_{m+1}| < R}`, the fibre
volume is at most `2 M · vol{y ∈ B(a, ρ) : |y_m| < R}` for every `t ≠ 0`, which tends to `0`
with `R` (the hyperplane `y_m = 0` is null): `node_local`.
-/

set_option autoImplicit false

noncomputable section

universe u

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology Manifold ContDiff ENNReal

namespace SGPT.Okounkov.TranscendentalWN.FL2

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.ProductTestForms
open SGPT.Foundations.Analysis.Pending.BlowupMonomialCharts
open SGPT.Foundations.Analysis.Pending.BlowupFlatCoordinates
open SGPT.Foundations.Analysis.Pending.ProductComplexManifold
open scoped SGPT.Foundations.Analysis.Pending.ProductComplexManifold
open SGPT.Okounkov.TranscendentalMain
open SGPT.Okounkov.TranscendentalWN
open SGPT.Okounkov.TranscendentalWN.LSC

/-! ### The two parametrizations of the node -/

section Param

variable {m : ℕ}

/-- `y ↦ t / y_m`. -/
def nodeQuot (t : ComplexModel 1) (y : ComplexModel (m + 1)) : ComplexModel 1 :=
  (y (Fin.last m))⁻¹ • t

/-- The derivative of `y ↦ t / y_m`. -/
def nodeQuotDeriv (t : ComplexModel 1) (y : ComplexModel (m + 1)) :
    ComplexModel (m + 1) →L[ℂ] ComplexModel 1 :=
  ((ContinuousLinearMap.toSpanSingleton ℂ (-((y (Fin.last m)) ^ 2)⁻¹)).comp
    (EuclideanSpace.proj (𝕜 := ℂ) (Fin.last m) : ComplexModel (m + 1) →L[ℂ] ℂ)).smulRight t

theorem hasFDerivAt_nodeQuot (t : ComplexModel 1) {y : ComplexModel (m + 1)}
    (hy : y (Fin.last m) ≠ 0) : HasFDerivAt (nodeQuot t) (nodeQuotDeriv t y) y := by
  have hp : HasFDerivAt (fun y : ComplexModel (m + 1) => y (Fin.last m))
      (EuclideanSpace.proj (𝕜 := ℂ) (Fin.last m) : ComplexModel (m + 1) →L[ℂ] ℂ) y :=
    (EuclideanSpace.proj (𝕜 := ℂ) (Fin.last m) : ComplexModel (m + 1) →L[ℂ] ℂ).hasFDerivAt
  exact ((hasFDerivAt_inv hy).comp y hp).smul_const t

theorem norm_nodeQuotDeriv_le (t : ComplexModel 1) {y : ComplexModel (m + 1)}
    (hy : y (Fin.last m) ≠ 0) (ht : ‖t‖ ≤ ‖y (Fin.last m)‖ ^ 2) : ‖nodeQuotDeriv t y‖ ≤ 1 := by
  rw [nodeQuotDeriv, ContinuousLinearMap.norm_smulRight_apply]
  have hproj : ‖(EuclideanSpace.proj (𝕜 := ℂ) (Fin.last m) : ComplexModel (m + 1) →L[ℂ] ℂ)‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by
      rw [one_mul]
      exact PiLp.norm_apply_le v _
  have hpos : 0 < ‖y (Fin.last m)‖ ^ 2 := by
    have := norm_pos_iff.mpr hy
    positivity
  have hc : ‖(ContinuousLinearMap.toSpanSingleton ℂ (-((y (Fin.last m)) ^ 2)⁻¹)).comp
      (EuclideanSpace.proj (𝕜 := ℂ) (Fin.last m) : ComplexModel (m + 1) →L[ℂ] ℂ)‖ ≤
      (‖y (Fin.last m)‖ ^ 2)⁻¹ := by
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    rw [ContinuousLinearMap.norm_toSpanSingleton, norm_neg, norm_inv, norm_pow]
    calc (‖y (Fin.last m)‖ ^ 2)⁻¹ *
          ‖(EuclideanSpace.proj (𝕜 := ℂ) (Fin.last m) : ComplexModel (m + 1) →L[ℂ] ℂ)‖
        ≤ (‖y (Fin.last m)‖ ^ 2)⁻¹ * 1 := by gcongr
      _ = _ := mul_one _
  calc _ ≤ (‖y (Fin.last m)‖ ^ 2)⁻¹ * ‖y (Fin.last m)‖ ^ 2 :=
        mul_le_mul hc ht (norm_nonneg _) (by positivity)
    _ = 1 := inv_mul_cancel₀ hpos.ne'

/-- The parametrization `y ↦ P(y, t / y_m)` of the fibre `{w_m w_{m+1} = t}`. -/
def nodeParam (P : ComplexModel (m + 1 + 1) ≃L[ℂ] ComplexModel (m + 1 + 1)) (t : ComplexModel 1)
    (y : ComplexModel (m + 1)) : ComplexModel (m + 1 + 1) :=
  P (splitL m (y, nodeQuot t y))

theorem hasFDerivAt_nodeParam (P : ComplexModel (m + 1 + 1) ≃L[ℂ] ComplexModel (m + 1 + 1))
    (t : ComplexModel 1) {y : ComplexModel (m + 1)} (hy : y (Fin.last m) ≠ 0) :
    HasFDerivAt (nodeParam P t)
      (((P : ComplexModel (m + 1 + 1) →L[ℂ] ComplexModel (m + 1 + 1)).comp
        (splitL m : (ComplexModel (m + 1) × ComplexModel 1) →L[ℂ] ComplexModel (m + 1 + 1))).comp
        ((ContinuousLinearMap.id ℂ (ComplexModel (m + 1))).prod (nodeQuotDeriv t y))) y := by
  have h := (hasFDerivAt_id y).prodMk (hasFDerivAt_nodeQuot t hy)
  exact ((P : ComplexModel (m + 1 + 1) →L[ℂ] ComplexModel (m + 1 + 1)).comp
    (splitL m : (ComplexModel (m + 1) × ComplexModel 1) →L[ℂ] ComplexModel (m + 1 + 1))
    ).hasFDerivAt.comp y h

theorem contDiffAt_nodeParam (P : ComplexModel (m + 1 + 1) ≃L[ℂ] ComplexModel (m + 1 + 1))
    (t : ComplexModel 1) {y : ComplexModel (m + 1)} (hy : y (Fin.last m) ≠ 0) :
    ContDiffAt ℂ ∞ (nodeParam P t) y := by
  have h1 : ContDiffAt ℂ ∞ (fun y : ComplexModel (m + 1) => (y (Fin.last m))⁻¹) y :=
    ((EuclideanSpace.proj (Fin.last m) : ComplexModel (m + 1) →L[ℂ] ℂ).contDiff.contDiffAt).inv hy
  have h2 : ContDiffAt ℂ ∞ (fun y : ComplexModel (m + 1) => (y, nodeQuot t y)) y :=
    contDiffAt_id.prodMk (h1.smul contDiffAt_const)
  exact (((P : ComplexModel (m + 1 + 1) →L[ℂ] ComplexModel (m + 1 + 1)).comp
    (splitL m : (ComplexModel (m + 1) × ComplexModel 1) →L[ℂ] ComplexModel (m + 1 + 1))
    ).contDiff.contDiffAt).comp y h2

theorem norm_fderiv_nodeParam_le (P : ComplexModel (m + 1 + 1) ≃L[ℂ] ComplexModel (m + 1 + 1))
    (hP : ‖(P : ComplexModel (m + 1 + 1) →L[ℂ] ComplexModel (m + 1 + 1))‖ ≤ 1)
    (t : ComplexModel 1) {y : ComplexModel (m + 1)} (hy : y (Fin.last m) ≠ 0)
    (ht : ‖t‖ ≤ ‖y (Fin.last m)‖ ^ 2) :
    ‖(((P : ComplexModel (m + 1 + 1) →L[ℂ] ComplexModel (m + 1 + 1)).comp
        (splitL m : (ComplexModel (m + 1) × ComplexModel 1) →L[ℂ] ComplexModel (m + 1 + 1))).comp
        ((ContinuousLinearMap.id ℂ (ComplexModel (m + 1))).prod (nodeQuotDeriv t y)))‖ ≤
      ‖(splitL m : (ComplexModel (m + 1) × ComplexModel 1) →L[ℂ] ComplexModel (m + 1 + 1))‖ := by
  set S := (splitL m : (ComplexModel (m + 1) × ComplexModel 1) →L[ℂ] ComplexModel (m + 1 + 1))
  have hprod : ‖(ContinuousLinearMap.id ℂ (ComplexModel (m + 1))).prod (nodeQuotDeriv t y)‖ ≤ 1 := by
    rw [ContinuousLinearMap.opNorm_prod, Prod.norm_def]
    exact max_le ContinuousLinearMap.norm_id_le (norm_nodeQuotDeriv_le t hy ht)
  calc _ ≤ ‖(P : ComplexModel (m + 1 + 1) →L[ℂ] ComplexModel (m + 1 + 1)).comp S‖ *
        ‖(ContinuousLinearMap.id ℂ (ComplexModel (m + 1))).prod (nodeQuotDeriv t y)‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (‖(P : ComplexModel (m + 1 + 1) →L[ℂ] ComplexModel (m + 1 + 1))‖ * ‖S‖) * 1 := by
        gcongr
        exact ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (1 * ‖S‖) * 1 := by gcongr
    _ = ‖S‖ := by ring

/-- The fibre coordinate of the first parametrization. -/
theorem tau_nodeParam_one (t : ComplexModel 1) {y : ComplexModel (m + 1)}
    (hy : y (Fin.last m) ≠ 0) :
    ((splitL m).symm (monomial m (idxZ m) (nodeParam (ContinuousLinearEquiv.refl ℂ _) t y))).2 = t := by
  rw [splitL_symm_snd_eq]
  ext i
  fin_cases i
  simp only [nodeParam, nodeQuot, ContinuousLinearEquiv.refl_apply, monomial_apply]
  rw [if_pos ⟨by simp, idxZ_ne_idxT.symm⟩]
  simp only [Fin.isValue, splitL_last, PiLp.smul_apply, smul_eq_mul, Fin.zero_eta,
    PiLp.single_apply, if_true]
  rw [show idxZ m = Fin.castSucc (Fin.last m) from rfl, splitL_castSucc]
  field_simp

/-- The fibre coordinate of the second parametrization. -/
theorem tau_nodeParam_two (t : ComplexModel 1) {y : ComplexModel (m + 1)}
    (hy : y (Fin.last m) ≠ 0) :
    ((splitL m).symm (monomial m (idxZ m) (nodeParam (swapNormal m) t y))).2 = t := by
  rw [nodeParam, monomial_idxZ_swapNormal, monomial_idxT_split, splitL_symm_snd_eq]
  ext i
  fin_cases i
  simp only [swapNormal_apply, Equiv.swap_apply_right]
  simp only [Fin.isValue, splitL_castSucc, scaleLast, if_true, nodeQuot, PiLp.smul_apply,
    smul_eq_mul, Fin.zero_eta, PiLp.single_apply]
  exact mul_inv_cancel_left₀ hy _

/-- The left inverse of the first parametrization. -/
theorem nodeParam_one_eq {t : ComplexModel 1} {w : ComplexModel (m + 1 + 1)}
    (hwZ : w (idxZ m) ≠ 0) (hτ : w (idxT m) * w (idxZ m) = t 0) :
    nodeParam (ContinuousLinearEquiv.refl ℂ _) t ((splitL m).symm w).1 = w := by
  simp only [nodeParam, ContinuousLinearEquiv.refl_apply]
  rw [SliceCoords.splitL_eq_iff]
  refine ⟨rfl, ?_⟩
  simp only [nodeQuot, PiLp.smul_apply, smul_eq_mul, splitL_symm_fst]
  rw [show Fin.castSucc (Fin.last m) = idxZ m from rfl, ← hτ]
  field_simp

/-- The left inverse of the second parametrization. -/
theorem nodeParam_two_eq {t : ComplexModel 1} {w : ComplexModel (m + 1 + 1)}
    (hwT : w (idxT m) ≠ 0) (hτ : w (idxT m) * w (idxZ m) = t 0) :
    nodeParam (swapNormal m) t (SliceCoords.nuZ m w) = w := by
  have hν : SliceCoords.nuZ m w (Fin.last m) = w (idxT m) := by
    rw [SliceCoords.nuZ_apply, splitL_symm_fst]
    simp [Equiv.swap_apply_left]
  simp only [nodeParam]
  apply (swapNormal m).symm.injective
  rw [ContinuousLinearEquiv.symm_apply_apply, swapNormal_symm_apply, SliceCoords.splitL_eq_iff]
  refine ⟨by rw [← SliceCoords.nuZ_apply], ?_⟩
  simp only [nodeQuot, hν, PiLp.smul_apply, smul_eq_mul, swapNormal_apply, Equiv.swap_apply_right]
  rw [← hτ]
  field_simp

theorem nodeParam_one_left (t : ComplexModel 1) (y : ComplexModel (m + 1)) :
    ((splitL m).symm (nodeParam (ContinuousLinearEquiv.refl ℂ _) t y)).1 = y := by
  simp [nodeParam]

theorem nodeParam_two_left (t : ComplexModel 1) (y : ComplexModel (m + 1)) :
    SliceCoords.nuZ m (nodeParam (swapNormal m) t y) = y := by
  simp [nodeParam, SliceCoords.nuZ_apply]

theorem norm_swapNormal_le :
    ‖(swapNormal m : ComplexModel (m + 1 + 1) →L[ℂ] ComplexModel (m + 1 + 1))‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun w => by
    rw [one_mul]
    exact ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
      (Equiv.swap (idxZ m) (idxT m))).norm_map w).le

/-- The volume of `{y ∈ B(a, ρ) : |y_m| < R}` tends to `0` with `R`. -/
theorem exists_volume_slab_lt (a : ComplexModel (m + 1)) (ρ : ℝ) {η : ℝ≥0∞} (hη : 0 < η) :
    ∃ R : ℝ, 0 < R ∧ volume (ball a ρ ∩ {y | ‖y (Fin.last m)‖ < R}) < η := by
  set A : ℕ → Set (ComplexModel (m + 1)) :=
    fun k => ball a ρ ∩ {y | ‖y (Fin.last m)‖ < 1 / ((k : ℝ) + 1)} with hA
  have hAo : ∀ k, IsOpen (A k) := fun k =>
    isOpen_ball.inter (isOpen_lt ((continuous_norm.comp (PiLp.continuous_apply 2 _ _)))
      continuous_const)
  have hAm : Antitone A := by
    intro k l hkl y hy
    refine ⟨hy.1, ?_⟩
    have h2 : ‖y (Fin.last m)‖ < 1 / ((l : ℝ) + 1) := hy.2
    show ‖y (Fin.last m)‖ < 1 / ((k : ℝ) + 1)
    refine h2.trans_le ?_
    gcongr
  have hfin : ∃ k, volume (A k) ≠ (⊤ : ℝ≥0∞) :=
    ⟨0, ((measure_mono inter_subset_left).trans_lt measure_ball_lt_top).ne⟩
  have hlim := tendsto_measure_iInter_atTop (fun k => (hAo k).measurableSet.nullMeasurableSet)
    hAm hfin
  have h0 : volume (⋂ k, A k) = 0 := by
    refine measure_mono_null ?_ (SGPT.Okounkov.TranscendentalCore.volume_last_coordinate_hyperplane m)
    intro y hy
    simp only [mem_iInter] at hy
    show y (Fin.last m) = 0
    rw [← norm_eq_zero]
    refine le_antisymm (le_of_forall_pos_lt_add fun δ hδ => ?_) (norm_nonneg _)
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hδ
    rw [zero_add]
    exact (hy k).2.trans hk
  rw [h0] at hlim
  obtain ⟨k, hk⟩ := (hlim.eventually (gt_mem_nhds hη)).exists
  exact ⟨1 / ((k : ℝ) + 1), by positivity, hk⟩

theorem norm_complexModel_one (t : ComplexModel 1) : ‖t‖ = ‖t 0‖ := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_one, Real.sqrt_sq (norm_nonneg _)]

end Param

/-! ### The local estimate at the node -/

variable {m : ℕ} {F : OriginalFlagGeometry.{u} (m + 1)}

variable {𝒳 : Type u} [TopologicalSpace 𝒳] [ChartedSpace (ComplexModel (m + 1 + 1)) 𝒳]
  [IsComplexManifold (m + 1 + 1) 𝒳] {μ : 𝒳 → F.carrier × ProjectiveLine}

/-- **`tok-wn-fl2:node-local`**: near a point of `X' ∩ ℰ`, the set `X' ∩ ℰ` has open
neighbourhoods with arbitrarily small fibre volumes. -/
theorem node_local (hμ : IsNormalConeDeformation F μ) (Θ : ClosedRealOneOneForm (m + 1 + 1) 𝒳)
    {q : 𝒳} (hqE : q ∈ exceptionalSet F μ) (hqX : q ∈ strictCentralFibre F μ) :
    ∃ O : Set 𝒳, IsOpen O ∧ q ∈ O ∧ ∀ ε : ℝ≥0∞, 0 < ε →
      ∃ U : Set 𝒳, IsOpen U ∧ (strictCentralFibre F μ ∩ exceptionalSet F μ) ∩ O ⊆ U ∧
        FibreSmall F μ Θ U ε := by
  classical
  have hμc : Continuous μ := hμ.continuous
  obtain ⟨C⟩ := nonempty_excChart F hμ hqE
  have hj : C.j = idxZ m := by
    rcases C.hj with h | h
    · exact h
    · exfalso
      have h0 := C.inter_strict_eq_empty h
      have : q ∈ C.O ∩ strictCentralFibre F μ := ⟨C.hqO, hqX⟩
      rw [h0] at this
      exact this
  set w₀ : ComplexModel (m + 1 + 1) := C.W q with hw₀
  have hw₀Z : w₀ (idxZ m) = 0 := by
    have := (C.mem_exceptional_iff C.hqO).mp hqE
    rwa [hj] at this
  have hw₀T : w₀ (idxT m) = 0 := C.W_idxT_eq_zero_of_mem_strict hj C.hqO hqX
  set D := monomialDomain C.Ψ m C.j with hD
  have hw₀D : w₀ ∈ D := C.W_mem_monomialDomain C.hqO
  set p₀ : LiftedOpen.{u} D := LiftedOpen.mk D w₀ hw₀D with hp₀
  set ℓ' : ComplexModel (m + 1 + 1) → 𝒳 := fun w => C.ℓ (liftMk D p₀ w) with hℓ'
  have hℓ'sm : ∀ w ∈ D, ContMDiffAt 𝓘(ℂ, ComplexModel (m + 1 + 1))
      𝓘(ℂ, ComplexModel (m + 1 + 1)) ∞ ℓ' w := fun w hw =>
    (C.hℓ _).comp w (contMDiffAt_liftMk p₀ hw)
  have hℓ'c : ContinuousOn ℓ' D := fun w hw => (hℓ'sm w hw).continuousAt.continuousWithinAt
  have hℓ'q : ℓ' w₀ = q := C.ℓ_W C.hqO
  set c₀ := zeroChart with hc₀
  set c : ComplexModel 1 := c₀ projectiveZero with hc
  -- the fibre coordinate of `ℓ' w`
  have hℓτ : ∀ w ∈ D, (μ (ℓ' w)).2 ∈ c₀.source ∧
      c₀ (μ (ℓ' w)).2 = ((splitL m).symm (monomial m C.j w)).2 + c := by
    intro w hw
    have hf := C.μ_ℓ_mem_flatDomain (liftMk D p₀ w)
    have h1 := C.hΨτ _ hf
    rw [C.μ_ℓ, C.flat_monomialChart, toModel_liftMk p₀ hw] at h1
    have hsrc : (μ (ℓ' w)).2 ∈ c₀.source := by
      have := hf.1
      simp only [chartAt_prod, prodChart_source, mem_prod] at this
      exact this.2
    refine ⟨hsrc, ?_⟩
    rw [C.μ_ℓ] at hsrc ⊢
    rw [h1, sub_add_cancel]
  set eX : ComplexChart (m + 1) F.carrier := complexChartAt C.x₀ with heX
  have hℓX : ∀ w ∈ D, (μ (ℓ' w)).1 ∈ eX.val.source := by
    intro w _
    have := (C.μ_ℓ_mem_flatDomain (liftMk D p₀ w)).1
    simp only [chartAt_prod, prodChart_source, mem_prod] at this
    exact this.1
  -- the chart of `𝒳` and the good set
  set d : ComplexChart (m + 1 + 1) 𝒳 := complexChartAt q with hd
  have hqd : q ∈ d.val.source := mem_complexChartAt_source _
  set G : Set (ComplexModel (m + 1 + 1)) := D ∩ ℓ' ⁻¹' (d.val.source ∩ C.O) with hG
  have hGo : IsOpen G := hℓ'c.isOpen_inter_preimage D.isOpen (d.val.open_source.inter C.hO)
  have hw₀G : w₀ ∈ G := ⟨hw₀D, by simp only [mem_preimage, hℓ'q]; exact ⟨hqd, C.hqO⟩⟩
  set a : ComplexModel (m + 1) := ((splitL m).symm w₀).1 with ha
  have hsplit₀ : splitL m (a, 0) = w₀ := by
    rw [SliceCoords.splitL_eq_iff]
    exact ⟨rfl, by simpa using hw₀T.symm⟩
  have hsw₀ : swapNormal m w₀ = w₀ := by
    ext i
    rw [swapNormal_apply]
    by_cases hZ : i = idxZ m
    · rw [hZ, Equiv.swap_apply_left, hw₀T, hw₀Z]
    · by_cases hT : i = idxT m
      · rw [hT, Equiv.swap_apply_right, hw₀T, hw₀Z]
      · rw [Equiv.swap_apply_of_ne_of_ne hZ hT]
  have hνZ₀ : SliceCoords.nuZ m w₀ = a := by rw [SliceCoords.nuZ_apply, hsw₀]
  -- the boxes of the two parametrizations
  set G₁ : Set (ComplexModel (m + 1) × ComplexModel 1) := (fun p => splitL m p) ⁻¹' G with hG₁
  set G₂ : Set (ComplexModel (m + 1) × ComplexModel 1) :=
    (fun p => swapNormal m (splitL m p)) ⁻¹' G with hG₂
  have hG₁o : IsOpen G₁ := hGo.preimage (splitL m).continuous
  have hG₂o : IsOpen G₂ := hGo.preimage ((swapNormal m).continuous.comp (splitL m).continuous)
  obtain ⟨ρ₁, hρ₁, hbox₁⟩ := exists_closedBall_prod_subset hG₁o
    (show (a, (0 : ComplexModel 1)) ∈ G₁ by simp only [hG₁, mem_preimage, hsplit₀]; exact hw₀G)
  obtain ⟨ρ₂, hρ₂, hbox₂⟩ := exists_closedBall_prod_subset hG₂o
    (show (a, (0 : ComplexModel 1)) ∈ G₂ by
      simp only [hG₂, mem_preimage, hsplit₀, hsw₀]; exact hw₀G)
  set ρ : ℝ := min ρ₁ ρ₂ with hρ
  have hρ0 : 0 < ρ := lt_min hρ₁ hρ₂
  set Kc := closedBall a ρ ×ˢ closedBall (0 : ComplexModel 1) ρ with hKc
  have hKcc : IsCompact Kc := (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)
  have hKc₁ : Kc ⊆ G₁ := fun p hp => hbox₁ ⟨closedBall_subset_closedBall (min_le_left _ _) hp.1,
    closedBall_subset_closedBall (min_le_left _ _) hp.2⟩
  have hKc₂ : Kc ⊆ G₂ := fun p hp => hbox₂ ⟨closedBall_subset_closedBall (min_le_right _ _) hp.1,
    closedBall_subset_closedBall (min_le_right _ _) hp.2⟩
  set Kw : Set (ComplexModel (m + 1 + 1)) :=
    (fun p => splitL m p) '' Kc ∪ (fun p => swapNormal m (splitL m p)) '' Kc with hKw
  have hKwc : IsCompact Kw := (hKcc.image (splitL m).continuous).union
    (hKcc.image ((swapNormal m).continuous.comp (splitL m).continuous))
  have hKwG : Kw ⊆ G := by
    rintro _ (⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩)
    · exact hKc₁ hp
    · exact hKc₂ hp
  -- the bounds
  set F₂ : ComplexModel (m + 1 + 1) → ComplexModel (m + 1 + 1) := fun w => d.val (ℓ' w) with hF₂
  have hF₂sm : ∀ w ∈ G, ContDiffAt ℝ ∞ F₂ w := fun w hw =>
    (contDiffAt_chart_comp (hℓ'sm w hw.1) d hw.2.1).restrict_scalars ℝ
  obtain ⟨C₂, hC₂0, hC₂⟩ := exists_bound_fderiv hGo hF₂sm hKwc hKwG
  have hF₂c : ContinuousOn F₂ Kw := fun w hw =>
    (hF₂sm w (hKwG hw)).continuousAt.continuousWithinAt
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_bound_comp hKwc hF₂c
    (fun w hw => d.val.map_source (hKwG hw).2.1) ((formPow Θ.val (m + 1)).smooth d).continuousOn
  set C₃ : ℝ :=
    ‖(splitL m : (ComplexModel (m + 1) × ComplexModel 1) →L[ℂ] ComplexModel (m + 1 + 1))‖ with hC₃
  set M : ℝ := max (C₁ * (C₂ * C₃) ^ (2 * (m + 1))) 1 with hM
  have hM1 : 1 ≤ M := le_max_right _ _
  -- the neighbourhood
  set νW₁ : 𝒳 → ComplexModel (m + 1) := fun z => ((splitL m).symm (C.W z)).1 with hνW₁
  set νW₂ : 𝒳 → ComplexModel (m + 1) := fun z => SliceCoords.nuZ m (C.W z) with hνW₂
  have hνW₁c : ContinuousOn νW₁ C.O := fun z hz =>
    ((continuous_fst.comp (splitL m).symm.continuous).continuousAt.comp
      (C.hW z hz).continuousAt).continuousWithinAt
  have hνW₂c : ContinuousOn νW₂ C.O := fun z hz =>
    ((SliceCoords.nuZ m).continuous.continuousAt.comp (C.hW z hz).continuousAt).continuousWithinAt
  set O : Set 𝒳 := (C.O ∩ νW₁ ⁻¹' ball a ρ) ∩ νW₂ ⁻¹' ball a ρ with hO
  have hO₁ : IsOpen (C.O ∩ νW₁ ⁻¹' ball a ρ) := hνW₁c.isOpen_inter_preimage C.hO isOpen_ball
  have hOo : IsOpen O := by
    have h2 := hνW₂c.isOpen_inter_preimage C.hO (isOpen_ball (x := a) (ε := ρ))
    have : O = (C.O ∩ νW₁ ⁻¹' ball a ρ) ∩ (C.O ∩ νW₂ ⁻¹' ball a ρ) := by
      ext z
      simp only [hO, mem_inter_iff, mem_preimage]
      tauto
    rw [this]
    exact hO₁.inter h2
  have hqO : q ∈ O := by
    refine ⟨⟨C.hqO, ?_⟩, ?_⟩
    · show ((splitL m).symm w₀).1 ∈ ball a ρ
      exact mem_ball_self hρ0
    · show SliceCoords.nuZ m w₀ ∈ ball a ρ
      rw [hνZ₀]
      exact mem_ball_self hρ0
  refine ⟨O, hOo, hqO, fun ε hε => ?_⟩
  set η : ℝ≥0∞ := ε / ENNReal.ofReal M with hη
  have hη0 : 0 < η := div_ofReal_pos hε
  obtain ⟨R₀, hR₀, hslab⟩ := exists_volume_slab_lt a ρ (ENNReal.half_pos hη0.ne')
  set R : ℝ := min R₀ ρ with hR
  have hR0 : 0 < R := lt_min hR₀ hρ0
  set Ucoord : Set 𝒳 := {z | ‖C.W z (idxZ m)‖ < R ∧ ‖C.W z (idxT m)‖ < R} with hUcoord
  set U : Set 𝒳 := O ∩ Ucoord with hU
  have hUo : IsOpen U := by
    have hc1 : ContinuousOn (fun z => ‖C.W z (idxZ m)‖) C.O := fun z hz =>
      (continuous_norm.continuousAt.comp ((PiLp.continuous_apply 2 _ (idxZ m)).continuousAt.comp
        (C.hW z hz).continuousAt)).continuousWithinAt
    have hc2 : ContinuousOn (fun z => ‖C.W z (idxT m)‖) C.O := fun z hz =>
      (continuous_norm.continuousAt.comp ((PiLp.continuous_apply 2 _ (idxT m)).continuousAt.comp
        (C.hW z hz).continuousAt)).continuousWithinAt
    have h1 := hc1.isOpen_inter_preimage C.hO (isOpen_Iio (a := R))
    have h2 := hc2.isOpen_inter_preimage C.hO (isOpen_Iio (a := R))
    have : U = O ∩ ((C.O ∩ (fun z => ‖C.W z (idxZ m)‖) ⁻¹' Iio R) ∩
        (C.O ∩ (fun z => ‖C.W z (idxT m)‖) ⁻¹' Iio R)) := by
      ext z
      simp only [hU, hO, hUcoord, mem_inter_iff, mem_preimage, mem_ofPred_eq, mem_Iio]
      tauto
    rw [this]
    exact hOo.inter (h1.inter h2)
  refine ⟨U, hUo, ?_, ?_⟩
  · -- `X' ∩ ℰ` near `q` lies in `U`
    rintro z ⟨⟨hzX, hzE⟩, hzO⟩
    have hzC : z ∈ C.O := hzO.1.1
    have hZ : C.W z (idxZ m) = 0 := by
      have := (C.mem_exceptional_iff hzC).mp hzE
      rwa [hj] at this
    have hT : C.W z (idxT m) = 0 := C.W_idxT_eq_zero_of_mem_strict hj hzC hzX
    refine ⟨hzO, ?_, ?_⟩
    · show ‖C.W z (idxZ m)‖ < R
      rw [hZ, norm_zero]
      exact hR0
    · show ‖C.W z (idxT m)‖ < R
      rw [hT, norm_zero]
      exact hR0
  · -- the fibre volumes
    obtain ⟨r, hr, hrτ⟩ := exists_radius_chart 1 one_pos
    refine ⟨r, hr, fun τ hτ hτr s hs hsμ => ?_⟩
    let _ : MeasurableSpace F.carrier := borel F.carrier
    have _ : BorelSpace F.carrier := ⟨rfl⟩
    set p := affineLinePoint τ with hp
    have hp0 : p ≠ projectiveZero := affineLinePoint_ne_projectiveZero hτ
    have hpc : p ∈ c₀.source := (hrτ τ hτr).1
    set t : ComplexModel 1 := c₀ p - c with ht
    have ht0 : t ≠ 0 := by
      intro h
      exact hp0 (c₀.injOn hpc (mem_chart_source _ _) (sub_eq_zero.mp h))
    have htpos : 0 < ‖t‖ := norm_pos_iff.mpr ht0
    set Y : Set (ComplexModel (m + 1)) := (ball a ρ ∩ {y | ‖y (Fin.last m)‖ < R}) ∩
      {y | ‖t‖ ≤ ‖y (Fin.last m)‖ ^ 2} with hY
    have hYm : MeasurableSet Y := by
      refine ((isOpen_ball.inter (isOpen_lt ((continuous_norm.comp (PiLp.continuous_apply 2 _ _)))
        continuous_const)).measurableSet).inter ?_
      exact (isClosed_le continuous_const
        ((continuous_norm.comp (PiLp.continuous_apply 2 _ _)).pow 2)).measurableSet
    -- the estimate for one parametrization
    have piece : ∀ (P : ComplexModel (m + 1 + 1) ≃L[ℂ] ComplexModel (m + 1 + 1))
        (ν : ComplexModel (m + 1 + 1) → ComplexModel (m + 1)),
        ‖(P : ComplexModel (m + 1 + 1) →L[ℂ] ComplexModel (m + 1 + 1))‖ ≤ 1 →
        (∀ y, ν (nodeParam P t y) = y) →
        (∀ y : ComplexModel (m + 1), y (Fin.last m) ≠ 0 →
          ((splitL m).symm (monomial m (idxZ m) (nodeParam P t y))).2 = t) →
        (∀ p ∈ Kc, P (splitL m p) ∈ Kw) →
        topFormMeasure F.omega (formPow (ClosedRealOneOneForm.pullback hs Θ).val (m + 1))
          ((fun y => (μ (ℓ' (nodeParam P t y))).1) '' Y) ≤ ENNReal.ofReal M * volume Y := by
      intro P ν hP hν hτP hPK
      set Oy : Set (ComplexModel (m + 1)) := ball a ρ ∩ {y | ‖t‖ < ρ * ‖y (Fin.last m)‖}
        with hOy
      have hOyo : IsOpen Oy := isOpen_ball.inter (isOpen_lt continuous_const
        (continuous_const.mul (continuous_norm.comp (PiLp.continuous_apply 2 _ _))))
      have hOyl : ∀ y ∈ Oy, y (Fin.last m) ≠ 0 := by
        intro y hy h0
        have h := hy.2
        simp only [mem_ofPred_eq, h0, norm_zero, mul_zero] at h
        exact absurd h (not_lt.mpr (norm_nonneg t))
      have hOyK : ∀ y ∈ Oy, (y, nodeQuot t y) ∈ Kc := by
        intro y hy
        refine ⟨ball_subset_closedBall hy.1, ?_⟩
        rw [mem_closedBall, dist_zero_right, nodeQuot, norm_smul, norm_inv]
        have hpos : 0 < ‖y (Fin.last m)‖ := norm_pos_iff.mpr (hOyl y hy)
        rw [inv_mul_le_iff₀ hpos]
        exact (hy.2 : ‖t‖ < ρ * ‖y (Fin.last m)‖).le.trans_eq (mul_comm _ _)
      have hOyG : ∀ y ∈ Oy, nodeParam P t y ∈ G := fun y hy => hKwG (hPK _ (hOyK y hy))
      have hYOy : Y ⊆ Oy := by
        intro y hy
        refine ⟨hy.1.1, ?_⟩
        have h1 : ‖y (Fin.last m)‖ < R := hy.1.2
        have h2 : ‖t‖ ≤ ‖y (Fin.last m)‖ ^ 2 := hy.2
        have hpos : 0 < ‖y (Fin.last m)‖ := by
          by_contra h
          have h0 : ‖y (Fin.last m)‖ = 0 := le_antisymm (not_lt.mp h) (norm_nonneg _)
          rw [h0] at h2
          linarith
        show ‖t‖ < ρ * ‖y (Fin.last m)‖
        calc ‖t‖ ≤ ‖y (Fin.last m)‖ * ‖y (Fin.last m)‖ := by rw [← sq]; exact h2
          _ < ρ * ‖y (Fin.last m)‖ := by
            gcongr
            exact h1.trans_le (min_le_right _ _)
      -- `μ(ℓ'(Λ(t, y)))` lies over `p`
      have hpy : ∀ y ∈ Oy, (μ (ℓ' (nodeParam P t y))).2 = p := by
        intro y hy
        obtain ⟨hsrc, heq⟩ := hℓτ _ (hOyG y hy).1
        rw [hj, hτP y (hOyl y hy), ht, sub_add_cancel] at heq
        exact c₀.injOn hsrc hpc heq
      have hsg : ∀ y ∈ Oy, s (μ (ℓ' (nodeParam P t y))).1 = ℓ' (nodeParam P t y) := by
        intro y hy
        have hnot : μ (ℓ' (nodeParam P t y)) ∉ deformationCentre F := fun h =>
          hp0 ((hpy y hy).symm.trans ((mem_deformationCentre_iff F).mp h).2)
        refine (eq_of_map_eq_of_notMem F hμ hnot ?_).symm
        rw [hsμ]
        exact Prod.ext rfl (hpy y hy)
      refine topFormMeasure_image_le F.omega hs Θ eX d hOyo
        (γ := fun y => (μ (ℓ' (nodeParam P t y))).1) (g := fun y => ℓ' (nodeParam P t y))
        (fun y hy => ?_) (fun y hy => hℓX _ (hOyG y hy).1) hsg (fun y hy => (hOyG y hy).2.1)
        hYm hYOy ?_ (fun y hy => ?_)
      · have h1 : ContMDiffAt 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1 + 1)) ∞
            (nodeParam P t) y := (contDiffAt_nodeParam P t (hOyl y hy)).contMDiffAt
        have h2 := ContMDiffAt.comp (g := ℓ') y (hℓ'sm _ (hOyG y hy).1) h1
        exact ProductComplexManifold.contMDiff_fst.contMDiffAt.comp y
          ((hμ.contMDiff.contMDiffAt).comp y h2)
      · -- injectivity
        intro y hy y' hy' h
        have h1 : ℓ' (nodeParam P t y) = ℓ' (nodeParam P t y') := by
          rw [← hsg y (hYOy hy), ← hsg y' (hYOy hy')]
          exact congrArg s h
        have h2 : nodeParam P t y = nodeParam P t y' := by
          rw [← C.W_ℓ (hOyG y (hYOy hy)).1 (hOyG y (hYOy hy)).2.2,
            ← C.W_ℓ (hOyG y' (hYOy hy')).1 (hOyG y' (hYOy hy')).2.2]
          exact congrArg C.W h1
        have h3 := congrArg ν h2
        rwa [hν, hν] at h3
      · -- the bound of the integrand
        have hyO := hYOy hy
        have hwK : nodeParam P t y ∈ Kw := hPK _ (hOyK y hyO)
        have h1 : ‖(formPow Θ.val (m + 1)).coeff d (d.val (ℓ' (nodeParam P t y)))‖ ≤ C₁ :=
          hC₁ _ hwK
        have hD := hasFDerivAt_nodeParam P t (hOyl y hyO)
        have hF₂D : HasFDerivAt F₂ (fderiv ℝ F₂ (nodeParam P t y)) (nodeParam P t y) :=
          ((hF₂sm _ (hKwG hwK)).differentiableAt (by simp)).hasFDerivAt
        have hcomp := hF₂D.comp y (hD.restrictScalars ℝ)
        have h2 : ‖fderiv ℝ (fun y => d.val (ℓ' (nodeParam P t y))) y‖ ≤ C₂ * C₃ := by
          rw [show (fun y => d.val (ℓ' (nodeParam P t y))) = F₂ ∘ nodeParam P t from rfl,
            hcomp.fderiv]
          refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
          rw [ContinuousLinearMap.norm_restrictScalars]
          exact mul_le_mul (hC₂ _ hwK) (norm_fderiv_nodeParam_le P hP t (hOyl y hyO) hy.2)
            (norm_nonneg _) hC₂0
        calc ‖(formPow Θ.val (m + 1)).coeff d (d.val (ℓ' (nodeParam P t y)))‖ *
              ‖fderiv ℝ (fun y => d.val (ℓ' (nodeParam P t y))) y‖ ^ (2 * (m + 1))
            ≤ C₁ * (C₂ * C₃) ^ (2 * (m + 1)) := by gcongr
          _ ≤ M := le_max_left _ _
    have hpiece₁ := piece (ContinuousLinearEquiv.refl ℂ _) (fun w => ((splitL m).symm w).1)
      ContinuousLinearMap.norm_id_le (nodeParam_one_left t) (fun y hy => tau_nodeParam_one t hy)
      (fun p hp => Or.inl ⟨p, hp, rfl⟩)
    have hpiece₂ := piece (swapNormal m) (SliceCoords.nuZ m) norm_swapNormal_le
      (nodeParam_two_left t) (fun y hy => tau_nodeParam_two t hy) (fun p hp => Or.inr ⟨p, hp, rfl⟩)
    -- the fibre near `q` is covered by the two parametrizations
    have hsub : s ⁻¹' U ⊆
        (fun y => (μ (ℓ' (nodeParam (ContinuousLinearEquiv.refl ℂ _) t y))).1) '' Y ∪
          (fun y => (μ (ℓ' (nodeParam (swapNormal m) t y))).1) '' Y := by
      intro x hx
      have hxU : s x ∈ U := hx
      have hzC : s x ∈ C.O := hxU.1.1.1
      set w := C.W (s x) with hw
      have hτw : ((splitL m).symm (monomial m C.j w)).2 = t := by
        rw [C.tau_eq hzC, hsμ x]
      have hτ0 : w (idxT m) * w (idxZ m) = t 0 := by
        have h := congrArg (fun v : ComplexModel 1 => v 0) hτw
        simp only [splitL_symm_snd, monomial_apply, hj] at h
        rwa [if_pos ⟨by simp, idxZ_ne_idxT.symm⟩] at h
      have hnt : ‖t‖ = ‖w (idxT m)‖ * ‖w (idxZ m)‖ := by
        rw [norm_complexModel_one, ← hτ0, norm_mul]
      have hℓw : ℓ' w = s x := C.ℓ_W hzC
      have hRZ : ‖w (idxZ m)‖ < R := hxU.2.1
      have hRT : ‖w (idxT m)‖ < R := hxU.2.2
      by_cases hcase : ‖t‖ ≤ ‖w (idxZ m)‖ ^ 2
      · -- parametrize by `w_m`
        left
        have hwZ : w (idxZ m) ≠ 0 := by
          intro h0
          rw [h0, norm_zero] at hcase
          linarith
        set y := ((splitL m).symm w).1 with hy
        have hyl : y (Fin.last m) = w (idxZ m) := by rw [hy, splitL_symm_fst]
        refine ⟨y, ⟨⟨hxU.1.1.2, ?_⟩, ?_⟩, ?_⟩
        · show ‖y (Fin.last m)‖ < R
          rw [hyl]
          exact hRZ
        · show ‖t‖ ≤ ‖y (Fin.last m)‖ ^ 2
          rw [hyl]
          exact hcase
        · show (μ (ℓ' (nodeParam (ContinuousLinearEquiv.refl ℂ _) t y))).1 = x
          rw [hy, nodeParam_one_eq hwZ hτ0, hℓw, hsμ]
      · -- parametrize by `w_{m+1}`
        right
        push Not at hcase
        have hwZ : w (idxZ m) ≠ 0 := by
          intro h0
          rw [h0, norm_zero, mul_zero] at hnt
          exact ht0 (norm_eq_zero.mp hnt)
        have hZpos : 0 < ‖w (idxZ m)‖ := norm_pos_iff.mpr hwZ
        have hZT : ‖w (idxZ m)‖ < ‖w (idxT m)‖ := by
          rw [hnt, sq] at hcase
          exact lt_of_mul_lt_mul_right hcase hZpos.le
        have hcase2 : ‖t‖ ≤ ‖w (idxT m)‖ ^ 2 := by
          rw [hnt, sq]
          exact mul_le_mul_of_nonneg_left hZT.le (norm_nonneg _)
        have hwT : w (idxT m) ≠ 0 := by
          intro h0
          rw [h0, norm_zero] at hZT
          exact absurd hZT (not_lt.mpr (norm_nonneg _))
        set y := SliceCoords.nuZ m w with hy
        have hyl : y (Fin.last m) = w (idxT m) := by
          rw [hy, SliceCoords.nuZ_apply, splitL_symm_fst]
          simp [Equiv.swap_apply_left]
        refine ⟨y, ⟨⟨hxU.1.2, ?_⟩, ?_⟩, ?_⟩
        · show ‖y (Fin.last m)‖ < R
          rw [hyl]
          exact hRT
        · show ‖t‖ ≤ ‖y (Fin.last m)‖ ^ 2
          rw [hyl]
          exact hcase2
        · show (μ (ℓ' (nodeParam (swapNormal m) t y))).1 = x
          rw [hy, nodeParam_two_eq hwT hτ0, hℓw, hsμ]
    -- the total
    have hvol : volume Y < η / 2 := (measure_mono fun y hy =>
      (⟨hy.1.1, (hy.1.2 : ‖y (Fin.last m)‖ < R).trans_le (min_le_left _ _)⟩ :
        y ∈ ball a ρ ∩ {y | ‖y (Fin.last m)‖ < R₀})).trans_lt hslab
    calc _ ≤ topFormMeasure F.omega (formPow (ClosedRealOneOneForm.pullback hs Θ).val (m + 1))
          ((fun y => (μ (ℓ' (nodeParam (ContinuousLinearEquiv.refl ℂ _) t y))).1) '' Y ∪
            (fun y => (μ (ℓ' (nodeParam (swapNormal m) t y))).1) '' Y) := measure_mono hsub
      _ ≤ ENNReal.ofReal M * volume Y + ENNReal.ofReal M * volume Y :=
          (measure_union_le _ _).trans (add_le_add hpiece₁ hpiece₂)
      _ = ENNReal.ofReal M * (volume Y + volume Y) := (mul_add _ _ _).symm
      _ ≤ ε := by
          refine ofReal_mul_le_of_lt_div hM1 ?_
          calc volume Y + volume Y < η / 2 + η / 2 := ENNReal.add_lt_add hvol hvol
            _ = η := ENNReal.add_halves η

end SGPT.Okounkov.TranscendentalWN.FL2
