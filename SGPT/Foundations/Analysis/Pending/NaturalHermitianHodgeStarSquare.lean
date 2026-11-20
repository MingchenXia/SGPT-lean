import SGPT.Foundations.Analysis.Pending.NaturalHermitianFormRieszContraction
import SGPT.Foundations.Analysis.Pending.NaturalHermitianHodgeStar
import SGPT.Foundations.Analysis.Pending.NaturalOriginalGradedExteriorProduct

set_option autoImplicit false

/-! The actual original Hodge square and metric isometry, with literal degree transports. -/

noncomputable section

open Set Filter Equiv
open scoped Topology ContDiff BigOperators

namespace SGPT.Foundations.Analysis.Pending.NaturalHermitianHodgeStarSquare

open FirstPass FirstPass.MongeAmpere NaturalHermitianMetricCoefficients
  NaturalHermitianOriginalFormMetric NaturalHermitianSmoothFormMetric
  NaturalHermitianFormRieszContraction NaturalHermitianHodgeStar
  NaturalOriginalComplementaryWedgeDuality NaturalOriginalGradedExteriorProduct
  NaturalHermitianUnitVolume ConstantFormProducts
  _root_.SGPT.Foundations.Analysis.LocalCurrents

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

local instance formNormedAddCommGroup (q : ℕ) : NormedAddCommGroup (FormCoefficients n q) :=
  ContinuousAlternatingMap.instNormedAddCommGroup

local instance formNormedSpace (q : ℕ) : NormedSpace ℝ (FormCoefficients n q) :=
  ContinuousAlternatingMap.instNormedSpace

/-- The same actual original star, with only its output dimension equality transported. -/
def degreeStar (w : SmoothRealForm n M 2) (e : ComplexChart n M)
    (z : ComplexModel n) (q : ℕ) : FormCoefficients n q →L[ℝ] FormCoefficients n (2 * n - q) :=
  ((castForm (n := n) (show Module.finrank ℝ (ComplexModel n) - q = 2 * n - q by
    rw [complexModel_real_finrank])).toContinuousLinearMap).comp
      (allDegreeStarCoefficients w e z q)

/-- Literal bounded-branch calibration to the already constructed original star. -/
theorem degreeStar_below (w : SmoothRealForm n M 2) (e : ComplexChart n M)
    (z : ComplexModel n) (q : ℕ) (hq : q ≤ 2 * n) (η : FormCoefficients n q) :
    degreeStar w e z q η =
      castForm (show Module.finrank ℝ (ComplexModel n) - q = 2 * n - q by
        rw [complexModel_real_finrank])
        (starCoefficients w e z ⟨q, by rw [complexModel_real_finrank]; omega⟩ η) := by
  change castForm _ (allDegreeStarCoefficients w e z q η) = _
  unfold allDegreeStarCoefficients
  rw [dif_pos (show q ≤ Module.finrank ℝ (ComplexModel n) by
    simpa only [complexModel_real_finrank] using hq)]

/-- Whole wedge identity for the same original star in natural output degrees. -/
theorem degreeStar_wedge_identity (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (e : ComplexChart n M) (z : ComplexModel n) (hz : z ∈ e.val.target)
    (q : ℕ) (hq : q ≤ 2 * n) (ξ η : FormCoefficients n q) :
    wedgeTo (Nat.add_sub_of_le hq) ξ (degreeStar w e z q η) =
      formMetricCoefficients w e z q ξ η • metricVolumeCoefficients w e z := by
  rw [degreeStar_below w e z q hq]
  rw [wedgeTo_castForm_right _ _ (show q + (Module.finrank ℝ (ComplexModel n) - q) = 2 * n by
    rw [complexModel_real_finrank]; omega)]
  exact star_wedge_identity w hw e z hz ⟨q, by rw [complexModel_real_finrank]; omega⟩ ξ η

/-- Genuine whole split-frame evaluation, with its actual volume scalar and original contraction. -/
theorem degreeStar_split_evaluation (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (e : ComplexChart n M) (z : ComplexModel n) (hz : z ∈ e.val.target)
    {q k : ℕ} (h : q + k = 2 * n)
    (b : Module.Basis (Fin q ⊕ Fin k) ℝ (ComplexModel n)) (η : FormCoefficients n q)
    (v : Fin k → ComplexModel n) :
    castForm (show 2 * n - q = k by omega) (degreeStar w e z q η) v =
      metricVolumeCoefficients w e z
        (fun i => b (finSumFinEquiv.symm (Fin.cast h.symm i))) *
      formMetricCoefficients w e z q η (rightVolumeContraction (basisVolume b) v) := by
  let S : FormCoefficients n k := castForm (show 2 * n - q = k by omega)
    (degreeStar w e z q η)
  let frame : Fin (2 * n) → ComplexModel n :=
    fun i => b (finSumFinEquiv.symm (Fin.cast h.symm i))
  let c := metricVolumeCoefficients w e z frame
  have hv : (fun i => b (finSumFinEquiv.symm i)) = frame ∘ Fin.cast h := by
    funext i
    dsimp only [frame, Function.comp_apply]
    congr 1
  have hp : complementaryWedgeEquiv b S = c • formMetricCoefficients w e z q η := by
    ext ξ
    change scalarShufflePairingCLM b S ξ = c * formMetricCoefficients w e z q η ξ
    rw [scalarShufflePairingCLM_eq_coordinateWedge, hv, ← wedgeTo_apply]
    have hξ : wedgeTo h ξ S =
        formMetricCoefficients w e z q ξ η • metricVolumeCoefficients w e z := by
      rw [wedgeTo_castForm_right _ _ (Nat.add_sub_of_le (show q ≤ 2 * n by omega))]
      exact degreeStar_wedge_identity w hw e z hz q (by omega) ξ η
    rw [hξ, ContinuousAlternatingMap.smul_apply, smul_eq_mul]
    rw [(formMetricCoefficients_positive w hw e z hz q).1 ξ η]
    exact mul_comm _ _
  have hinv := congrArg (complementaryWedgeEquiv b).symm hp
  rw [ContinuousLinearEquiv.symm_apply_apply, map_smul] at hinv
  have hval := congrArg (fun F : FormCoefficients n k => F v) hinv
  change S v = c * formMetricCoefficients w e z q η
    (rightVolumeContraction (basisVolume b) v)
  simp only [ContinuousAlternatingMap.smul_apply, smul_eq_mul] at hval
  change S v = c * scalarWedgeInverseCLM b (formMetricCoefficients w e z q η) v at hval
  rw [scalarWedgeInverseCLM_apply] at hval
  exact hval

/-- Metric ON specialization still follows the original whole Riesz/contraction producer. -/
theorem degreeStar_split_orthonormal_evaluation (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (e : ComplexChart n M) (z : ComplexModel n) (hz : z ∈ e.val.target)
    {q k : ℕ} (h : q + k = 2 * n)
    (b : Module.Basis (Fin q ⊕ Fin k) ℝ (ComplexModel n))
    (hb : ∀ i j, associatedMetricCLM (w.coeff e z) (b i) (b j) = if i = j then 1 else 0)
    (η : FormCoefficients n q) :
    castForm (show 2 * n - q = k by omega) (degreeStar w e z q η)
      (fun j => b (Sum.inr j)) =
      metricVolumeCoefficients w e z
        (fun i => b (finSumFinEquiv.symm (Fin.cast h.symm i))) * η (fun i => b (Sum.inl i)) := by
  rw [degreeStar_split_evaluation w hw e z hz h b]
  rw [formMetricCoefficients_eq_original w hw e z hz]
  rw [form_metric_volume_contraction_evaluation (w.coeff e z) (hw e z hz).1 (hw e z hz).2 b hb]

/-- Actual chart metric internally gives a unit-volume ON basis in the literal top degree. -/
theorem exists_unit_metric_basis (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (e : ComplexChart n M) (z : ComplexModel n) (hz : z ∈ e.val.target) :
    ∃ b : Module.Basis (Fin (2 * n)) ℝ (ComplexModel n),
      (∀ i j, associatedMetricCLM (w.coeff e z) (b i) (b j) = if i = j then 1 else 0) ∧
      (metricVolumeCoefficients w e z).toAlternatingMap = b.det := by
  obtain ⟨b₀, hb₀, ho⟩ := exists_positive_metric_orthonormal_basis (hw e z hz).1 (hw e z hz).2
  let f : Fin (n * 2) ≃ Fin (2 * n) := finCongr (Nat.mul_comm n 2)
  let b := b₀.reindex f
  have hread : b ∘ Fin.cast (Nat.mul_comm n 2) = b₀ := by
    funext i
    simp only [Function.comp_apply, b, Module.Basis.reindex_apply]
    congr 1
  refine ⟨b, ?_, ?_⟩
  · intro i j
    simp only [b, Module.Basis.reindex_apply]
    rw [hb₀]
    simp only [Equiv.apply_eq_iff_eq]
  · have hvalue : metricVolumeCoefficients w e z b = 1 := by
      rw [metricVolumeCoefficients, castForm_apply, hread]
      exact ((original_chart_unit_volume w hw e z hz).2 b₀ hb₀ ho b₀).trans b₀.det_self
    have h := (metricVolumeCoefficients w e z).toAlternatingMap.eq_smul_basis_det b
    simp only [ContinuousAlternatingMap.coe_toAlternatingMap] at h
    rw [hvalue, one_smul] at h
    exact h

/-- Actual ordered block volume sign, for every entire original top tensor. -/
theorem split_volume_swap {q k : ℕ} (h : k + q = 2 * n)
    (b : Module.Basis (Fin k ⊕ Fin q) ℝ (ComplexModel n)) (ν : FormCoefficients n (2 * n)) :
    ν (fun i => (b.reindex (Equiv.sumComm (Fin k) (Fin q)))
      (finSumFinEquiv.symm (Fin.cast (show q + k = 2 * n by omega).symm i))) =
      (-1 : ℝ) ^ (q * k) * ν (fun i => b (finSumFinEquiv.symm (Fin.cast h.symm i))) := by
  let h' : q + k = 2 * n := by omega
  let f : Fin (q + k) ≃ Fin (2 * n) := finCongr h'
  let τ := f.permCongr (blockFlip q k)
  let old : Fin (2 * n) → ComplexModel n :=
    fun i => b (finSumFinEquiv.symm (Fin.cast h.symm i))
  have hFin (x : Fin q ⊕ Fin k) :
      Fin.cast h.symm (f (blockFlip q k (finSumFinEquiv x))) =
        finSumFinEquiv ((Equiv.sumComm (Fin q) (Fin k)) x) := by
    apply Fin.ext
    rcases x with i | i
    · simp [f, blockFlip, finSumFinEquiv_apply_left]
    · simp [f, blockFlip, finSumFinEquiv_apply_right]
  have hframe : (fun i => (b.reindex (Equiv.sumComm (Fin k) (Fin q)))
      (finSumFinEquiv.symm (Fin.cast h'.symm i))) = old ∘ τ := by
    funext i
    obtain ⟨x, rfl⟩ := (finSumFinEquiv.trans f).surjective i
    simp only [Function.comp_apply, Module.Basis.reindex_apply, Equiv.trans_apply]
    have hcast : Fin.cast h'.symm (f (finSumFinEquiv x)) = finSumFinEquiv x := by
      apply Fin.ext
      rfl
    rw [hcast, Equiv.symm_apply_apply]
    change b ((Equiv.sumComm (Fin k) (Fin q)).symm x) =
      b (finSumFinEquiv.symm (Fin.cast h.symm (τ (f (finSumFinEquiv x)))))
    dsimp only [τ]
    rw [Equiv.permCongr_apply, Equiv.symm_apply_apply, hFin, Equiv.symm_apply_apply]
    rfl
  change ν _ = (-1 : ℝ) ^ (q * k) * ν old
  rw [hframe, form_map_perm]
  simp only [τ, Perm.sign_permCongr, blockFlip_sign]

/-- Both actual star evaluations on an ON split frame, before its internally produced unit normalization. -/
theorem degreeStar_double_split_evaluation (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (e : ComplexChart n M) (z : ComplexModel n) (hz : z ∈ e.val.target)
    {q k : ℕ} (h : k + q = 2 * n)
    (b : Module.Basis (Fin k ⊕ Fin q) ℝ (ComplexModel n))
    (hb : ∀ i j, associatedMetricCLM (w.coeff e z) (b i) (b j) = if i = j then 1 else 0)
    (η : FormCoefficients n q) :
    castForm (show 2 * n - k = q by omega)
      (degreeStar w e z k
        (castForm (show 2 * n - q = k by omega) (degreeStar w e z q η)))
      (fun j => b (Sum.inr j)) =
      (-1 : ℝ) ^ (q * k) *
        (metricVolumeCoefficients w e z
          (fun i => b (finSumFinEquiv.symm (Fin.cast h.symm i)))) ^ 2 *
      η (fun j => b (Sum.inr j)) := by
  let bs := b.reindex (Equiv.sumComm (Fin k) (Fin q))
  have hbs : ∀ i j, associatedMetricCLM (w.coeff e z) (bs i) (bs j) =
      if i = j then 1 else 0 := by
    intro i j
    simp only [bs, Module.Basis.reindex_apply]
    rw [hb]
    simp only [Equiv.apply_eq_iff_eq]
  rw [degreeStar_split_orthonormal_evaluation w hw e z hz h b hb]
  have hi := degreeStar_split_orthonormal_evaluation w hw e z hz
    (show q + k = 2 * n by omega) bs hbs η
  simp only [bs, Module.Basis.reindex_apply, Equiv.sumComm_symm, Equiv.sumComm_apply,
    Sum.swap_inl, Sum.swap_inr] at hi
  rw [hi]
  have hswap := split_volume_swap h b (metricVolumeCoefficients w e z)
  simp only [Module.Basis.reindex_apply, Equiv.sumComm_symm, Equiv.sumComm_apply] at hswap
  rw [hswap]
  ring

/-- The actual original squared star on every entire coefficient tensor. -/
theorem degreeStar_square (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (e : ComplexChart n M) (z : ComplexModel n) (hz : z ∈ e.val.target)
    (q : ℕ) (hq : q ≤ 2 * n) (η : FormCoefficients n q) :
    castForm (show 2 * n - (2 * n - q) = q by omega)
      (degreeStar w e z (2 * n - q) (degreeStar w e z q η)) =
      (-1 : ℝ) ^ (q * (2 * n - q)) • η := by
  classical
  obtain ⟨b, hb, hν⟩ := exists_unit_metric_basis w hw e z hz
  let k := 2 * n - q
  have h : k + q = 2 * n := by dsimp [k]; omega
  let f : Fin k ⊕ Fin q ≃ Fin (2 * n) := finSumFinEquiv.trans (finCongr h)
  apply ContinuousAlternatingMap.toAlternatingMap_injective
  apply Module.Basis.ext_alternating b
  intro α hα
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair
    (@Sum.inr (Fin k) (Fin q)) (f.symm ∘ α) Sum.inr_injective (f.symm.injective.comp hα)
  let bs := b.reindex (f.symm.trans σ.symm)
  have hbsval (i : Fin k ⊕ Fin q) : bs i = b (f (σ i)) := by
    simp only [bs, Module.Basis.reindex_apply]
    rfl
  have hbs : ∀ i j, associatedMetricCLM (w.coeff e z) (bs i) (bs j) =
      if i = j then 1 else 0 := by
    intro i j
    rw [hbsval, hbsval, hb]
    simp only [Equiv.apply_eq_iff_eq]
  have hright : (fun j => bs (Sum.inr j)) = b ∘ α := by
    funext j
    rw [hbsval, hσ]
    exact congrArg b (f.apply_symm_apply (α j))
  have hframe : (fun i => bs (finSumFinEquiv.symm (Fin.cast h.symm i))) =
      b ∘ f.permCongr σ := by
    funext i
    rw [hbsval]
    have hf : finSumFinEquiv.symm (Fin.cast h.symm i) = f.symm i := rfl
    rw [hf]
    rfl
  have hνb : metricVolumeCoefficients w e z b = 1 := by
    change (metricVolumeCoefficients w e z).toAlternatingMap b = 1
    rw [hν, b.det_self]
  have hvolume : metricVolumeCoefficients w e z
      (fun i => bs (finSumFinEquiv.symm (Fin.cast h.symm i))) =
      ((Perm.sign σ : ℤ) : ℝ) := by
    rw [hframe, form_map_perm, hνb, mul_one, Perm.sign_permCongr]
  have hsign : (((Perm.sign σ : ℤ) : ℝ)) ^ 2 = 1 := by
    rcases Int.units_eq_one_or (Perm.sign σ) with hs | hs <;> simp [hs]
  have ht := degreeStar_double_split_evaluation w hw e z hz h bs hbs η
  rw [hright, hvolume, hsign, mul_one] at ht
  simpa only [k, castForm_self, ContinuousAlternatingMap.coe_toAlternatingMap,
    ContinuousAlternatingMap.smul_apply, smul_eq_mul, Function.comp_def] using ht

/-- The same actual coefficient star preserves the entire original metric. -/
theorem degreeStar_metric_isometry (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (e : ComplexChart n M) (z : ComplexModel n) (hz : z ∈ e.val.target)
    (q : ℕ) (hq : q ≤ 2 * n) (η θ : FormCoefficients n q) :
    formMetricCoefficients w e z (2 * n - q)
      (degreeStar w e z q η) (degreeStar w e z q θ) =
      formMetricCoefficients w e z q η θ := by
  let k := 2 * n - q
  have hk : k ≤ 2 * n := Nat.sub_le _ _
  have h : k + q = 2 * n := by dsimp [k]; omega
  have hc : 2 * n - k = q := by dsimp [k]; omega
  have ht : wedgeTo h (degreeStar w e z q η)
      (castForm hc (degreeStar w e z k (degreeStar w e z q θ))) =
      formMetricCoefficients w e z k (degreeStar w e z q η) (degreeStar w e z q θ) •
        metricVolumeCoefficients w e z := by
    rw [wedgeTo_castForm_right hc h (Nat.add_sub_of_le hk)]
    exact degreeStar_wedge_identity w hw e z hz k hk _ _
  have hsign : (-1 : ℝ) ^ (q * k) * (-1 : ℝ) ^ (k * q) = 1 := by
    rw [Nat.mul_comm k q, ← mul_pow]
    simp
  rw [degreeStar_square w hw e z hz q hq, wedgeTo_smul_right,
    wedgeTo_graded_comm h (Nat.add_sub_of_le hq), smul_smul, hsign, one_smul,
    degreeStar_wedge_identity w hw e z hz q hq θ η,
    (formMetricCoefficients_positive w hw e z hz q).1 θ η] at ht
  obtain ⟨b, _, hν⟩ := exists_unit_metric_basis w hw e z hz
  have hνb : metricVolumeCoefficients w e z b = 1 := by
    change (metricVolumeCoefficients w e z).toAlternatingMap b = 1
    rw [hν, b.det_self]
  have hs := congrArg (fun A : FormCoefficients n (2 * n) => A b) ht
  simpa only [ContinuousAlternatingMap.smul_apply, smul_eq_mul, hνb, mul_one, k] using hs.symm

/-- The original global smooth star with only its output degree transported. -/
def degreeHodgeStarForm (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (q : ℕ) (hq : q ≤ 2 * n) (α : SmoothRealForm n M q) :
    SmoothRealForm n M (2 * n - q) :=
  castSmoothForm (show Module.finrank ℝ (ComplexModel n) - q = 2 * n - q by
    rw [complexModel_real_finrank])
      (hodgeStarForm w hw ⟨q, by rw [complexModel_real_finrank]; omega⟩ α)

/-- Exact coefficients of the same natural-degree global smooth star. -/
theorem degreeHodgeStarForm_coeff (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (q : ℕ) (hq : q ≤ 2 * n) (α : SmoothRealForm n M q)
    (e : ComplexChart n M) (z : ComplexModel n) :
    (degreeHodgeStarForm w hw q hq α).coeff e z = degreeStar w e z q (α.coeff e z) := by
  rw [degreeHodgeStarForm, castSmoothForm_coeff, hodgeStarForm_coeff, degreeStar_below w e z q hq]

/-- The actual double-star law on the original geometric smooth forms. -/
theorem degreeHodgeStarForm_square_geometricallyEq (w : SmoothRealForm n M 2)
    (hw : w.IsHermitian) (q : ℕ) (hq : q ≤ 2 * n) (α : SmoothRealForm n M q) :
    (castSmoothForm (show 2 * n - (2 * n - q) = q by omega)
      (degreeHodgeStarForm w hw (2 * n - q) (Nat.sub_le _ _)
        (degreeHodgeStarForm w hw q hq α))).GeometricallyEq
      ((-1 : ℝ) ^ (q * (2 * n - q)) • α) := by
  intro e z hz
  rw [castSmoothForm_coeff, degreeHodgeStarForm_coeff, degreeHodgeStarForm_coeff]
  exact degreeStar_square w hw e z hz q hq (α.coeff e z)

/-- Excessive degree really has zero source and zero star, without a degree-square assertion. -/
theorem degreeStar_above_source (w : SmoothRealForm n M 2) (e : ComplexChart n M)
    (z : ComplexModel n) (q : ℕ) (hq : 2 * n < q) (η : FormCoefficients n q) :
    η = 0 ∧ degreeStar w e z q η = 0 := by
  have hs := allDegreeStarCoefficients_above_source w e z q
    (by simpa only [complexModel_real_finrank] using hq) η
  refine ⟨hs.1, ?_⟩
  change castForm _ (allDegreeStarCoefficients w e z q η) = 0
  rw [hs.2, map_zero]

end SGPT.Foundations.Analysis.Pending.NaturalHermitianHodgeStarSquare
