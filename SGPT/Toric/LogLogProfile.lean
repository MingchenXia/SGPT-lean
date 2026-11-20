import Mathlib.Analysis.Convex.Piecewise
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Data.EReal.Basic

set_option autoImplicit false
noncomputable section

namespace SGPT.Toric

open Set Filter
open scoped Topology

def logLogCrossingGap (t : ℝ) : ℝ := Real.log t - t + 2

lemma hasDerivAt_logLogCrossingGap {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt logLogCrossingGap (t⁻¹ - 1) t := by
  exact ((Real.hasDerivAt_log ht).sub (hasDerivAt_id t)).add_const 2

lemma strictAntiOn_logLogCrossingGap : StrictAntiOn logLogCrossingGap (Ioi 1) := by
  refine strictAntiOn_of_hasDerivWithinAt_neg (f' := fun t : ℝ => t⁻¹ - 1) (convex_Ioi 1) ?_ ?_ ?_
  · intro t ht
    change 1 < t at ht
    exact (hasDerivAt_logLogCrossingGap (by linarith : t ≠ 0)).continuousAt.continuousWithinAt
  · intro t ht
    have ht' : 1 < t := by simpa only [interior_Ioi, mem_Ioi] using ht
    exact (hasDerivAt_logLogCrossingGap (by linarith : t ≠ 0)).hasDerivWithinAt
  · intro t ht
    have ht' : 1 < t := by simpa only [interior_Ioi, mem_Ioi] using ht
    have hinv : t⁻¹ < (1 : ℝ) := (inv_lt_one₀ (by linarith)).2 ht'
    linarith

lemma exists_logLogLambda : ∃ ell : ℝ, 2 < ell ∧ ell < 4 ∧ Real.log ell = ell - 2 := by
  have htwo : 0 < logLogCrossingGap 2 := by
    have h := Real.log_two_gt_d9
    dsimp [logLogCrossingGap]
    linarith
  have hfour : logLogCrossingGap 4 < 0 := by
    have hlog : Real.log (4 : ℝ) = Real.log 2 + Real.log 2 := by
      rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    have h := Real.log_two_lt_d9
    dsimp [logLogCrossingGap]
    rw [hlog]
    linarith
  have hcont : ContinuousOn logLogCrossingGap (Icc (2 : ℝ) 4) := by
    intro t ht
    exact (hasDerivAt_logLogCrossingGap (by linarith [ht.1] : t ≠ 0)).continuousAt.continuousWithinAt
  obtain ⟨ell, hell, hzero⟩ := intermediate_value_Icc' (by norm_num : (2 : ℝ) ≤ 4)
    hcont (show 0 ∈ Icc (logLogCrossingGap 4) (logLogCrossingGap 2) from ⟨hfour.le, htwo.le⟩)
  have helltwo : 2 < ell := by
    refine lt_of_le_of_ne hell.1 ?_
    intro heq
    have h := hzero
    rw [← heq] at h
    linarith
  have hellfour : ell < 4 := by
    refine lt_of_le_of_ne hell.2 ?_
    intro heq
    have h := hzero
    rw [heq] at h
    linarith
  exact ⟨ell, helltwo, hellfour, by dsimp [logLogCrossingGap] at hzero; linarith⟩

def logLogLambda : ℝ := Classical.choose exists_logLogLambda

lemma logLogLambda_gt_two : 2 < logLogLambda := (Classical.choose_spec exists_logLogLambda).1
lemma logLogLambda_lt_four : logLogLambda < 4 := (Classical.choose_spec exists_logLogLambda).2.1
lemma log_logLogLambda : Real.log logLogLambda = logLogLambda - 2 :=
  (Classical.choose_spec exists_logLogLambda).2.2

lemma logLogLambda_unique {t : ℝ} (ht : 1 < t) (hroot : Real.log t = t - 2) :
    t = logLogLambda := by
  apply strictAntiOn_logLogCrossingGap.injOn ht (show 1 < logLogLambda by linarith [logLogLambda_gt_two])
  dsimp [logLogCrossingGap]
  rw [hroot, log_logLogLambda]
  ring

lemma logLogCrossingGap_lambda : logLogCrossingGap logLogLambda = 0 := by
  dsimp [logLogCrossingGap]
  rw [log_logLogLambda]
  ring

lemma logLogCrossingGap_nonneg_of_le {t : ℝ}
    (ht : Real.log 2 ≤ t) (hell : t ≤ logLogLambda) : 0 ≤ logLogCrossingGap t := by
  by_cases htOne : t ≤ 1
  · have hlogTwo := Real.log_two_gt_d9
    have hlogTwo' := Real.log_two_lt_d9
    have htHalf : (1 / 2 : ℝ) ≤ t := by linarith
    have hlog : Real.log (1 / 2 : ℝ) ≤ Real.log t := Real.log_le_log (by norm_num) htHalf
    have hhalf : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
      rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]
    rw [hhalf] at hlog
    dsimp [logLogCrossingGap]
    linarith
  · have ht' : 1 < t := lt_of_not_ge htOne
    have h := strictAntiOn_logLogCrossingGap.antitoneOn ht'
      (show 1 < logLogLambda by linarith [logLogLambda_gt_two]) hell
    rw [logLogCrossingGap_lambda] at h
    exact h

lemma logLogCrossingGap_nonpos_of_lambda_le {t : ℝ} (hell : logLogLambda ≤ t) :
    logLogCrossingGap t ≤ 0 := by
  have h := strictAntiOn_logLogCrossingGap.antitoneOn
    (show 1 < logLogLambda by linarith [logLogLambda_gt_two])
    (show 1 < t by linarith [logLogLambda_gt_two]) hell
  rwa [logLogCrossingGap_lambda] at h

def logLogProfile (x : ℝ) : ℝ := if x ≤ -logLogLambda then -Real.log (-x) else x + 2

def sourceLogLogProfile (x : ℝ) : ℝ :=
  if x < -Real.log 2 then max (-Real.log (-x)) (x + 2) else x + 2

lemma logLogProfile_eq_source (x : ℝ) : logLogProfile x = sourceLogLogProfile x := by
  have hlog2 := Real.log_two_lt_d9
  have hell := logLogLambda_gt_two
  by_cases hx : x ≤ -logLogLambda
  · have hxcut : x < -Real.log 2 := by linarith
    have hgap := logLogCrossingGap_nonpos_of_lambda_le (t := -x) (by linarith)
    have hmax : x + 2 ≤ -Real.log (-x) := by dsimp [logLogCrossingGap] at hgap; linarith
    simp only [logLogProfile, sourceLogLogProfile, hx, hxcut, if_pos, max_eq_left hmax]
  · by_cases hxcut : x < -Real.log 2
    · have hgap := logLogCrossingGap_nonneg_of_le (t := -x) (by linarith) (by linarith)
      have hmax : -Real.log (-x) ≤ x + 2 := by dsimp [logLogCrossingGap] at hgap; linarith
      simp only [logLogProfile, sourceLogLogProfile, hx, hxcut, if_false, if_pos, max_eq_right hmax]
    · simp only [logLogProfile, sourceLogLogProfile, hx, hxcut, if_false]

lemma convexOn_logLogProfile : ConvexOn ℝ univ logLogProfile := by
  let left : ℝ → ℝ := fun x => -Real.log x - x
  let right : ℝ → ℝ := fun _ => 2
  have hell := logLogLambda_gt_two
  have hleft : ConvexOn ℝ (Iic (-logLogLambda)) left := by
    exact (strictConcaveOn_log_Iio.concaveOn.neg.sub (concaveOn_id (convex_Iio 0))).subset
      (fun x hx => show x < 0 by have hx' : x ≤ -logLogLambda := hx; linarith)
      (convex_Iic _)
  have hderiv (x : ℝ) (hx : x ≠ 0) : HasDerivAt left (-x⁻¹ - 1) x :=
    (Real.hasDerivAt_log hx).neg.sub (hasDerivAt_id x)
  have hanti : AntitoneOn left (Iic (-logLogLambda)) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos
      (f' := fun x : ℝ => -x⁻¹ - 1) (convex_Iic _) ?_ ?_ ?_
    · intro x hx
      have hx' : x ≤ -logLogLambda := hx
      exact (hderiv x (by linarith)).continuousAt.continuousWithinAt
    · intro x hx
      have hx' : x < -logLogLambda := by simpa only [interior_Iic, mem_Iio] using hx
      exact (hderiv x (by linarith)).hasDerivWithinAt
    · intro x hx
      have hx' : x < -logLogLambda := by simpa only [interior_Iic, mem_Iio] using hx
      have hinv : (-x)⁻¹ ≤ (1 : ℝ) := (inv_le_one₀ (by linarith)).2 (by linarith)
      rw [inv_neg] at hinv
      linarith
  have hmatch : left (-logLogLambda) = right (-logLogLambda) := by
    dsimp [left, right]
    rw [Real.log_neg_eq_log, log_logLogLambda]
    ring
  have hglue := convexOn_univ_piecewise_Iic_of_antitoneOn_Iic_monotoneOn_Ici hleft
    (convexOn_const (2 : ℝ) (convex_Ici (-logLogLambda))) hanti
    (show MonotoneOn right (Ici (-logLogLambda)) from fun _ _ _ _ _ => le_rfl) hmatch
  have hsum := hglue.add (convexOn_id (convex_univ : Convex ℝ (univ : Set ℝ)))
  apply hsum.congr
  intro x _
  by_cases hx : x ≤ -logLogLambda
  · simp only [Pi.add_apply, id_eq, piecewise, mem_Iic, hx, if_pos, logLogProfile,
      left, Real.log_neg_eq_log]
    ring
  · simp only [Pi.add_apply, id_eq, piecewise, mem_Iic, hx, if_false, logLogProfile, left]
    ring

lemma logLogProfile_le_support_add_two (x : ℝ) : logLogProfile x ≤ max 0 x + 2 := by
  have hell := logLogLambda_gt_two
  by_cases hx : x ≤ -logLogLambda
  · have hpos : 0 < logLogLambda := by linarith
    have hlog : Real.log logLogLambda ≤ Real.log (-x) := Real.log_le_log hpos (by linarith)
    rw [log_logLogLambda] at hlog
    rw [logLogProfile, if_pos hx]
    linarith [le_max_left (0 : ℝ) x]
  · rw [logLogProfile, if_neg hx]
    linarith [le_max_right (0 : ℝ) x]

lemma logLogProfile_neg_lambda : logLogProfile (-logLogLambda) = 2 - logLogLambda := by
  rw [logLogProfile, if_pos le_rfl, neg_neg, log_logLogLambda]
  ring

lemma logLogProfile_cost_le_small_left {m x : ℝ}
    (hm : 0 < m) (hx : x ≤ -logLogLambda) :
    m * x - logLogProfile x ≤ -Real.log m - 1 := by
  have hell := logLogLambda_gt_two
  have hpos : 0 < m * (-x) := mul_pos hm (by linarith)
  have hlog := Real.log_le_sub_one_of_pos hpos
  rw [Real.log_mul hm.ne' (by linarith : -x ≠ 0)] at hlog
  rw [logLogProfile, if_pos hx]
  nlinarith

lemma logLogProfile_cost_le_small {m : ℝ}
    (hm : 0 < m) (hmb : m ≤ logLogLambda⁻¹) (x : ℝ) :
    m * x - logLogProfile x ≤ -Real.log m - 1 := by
  have hell := logLogLambda_gt_two
  have hmOne : m ≤ 1 := hmb.trans ((inv_le_one₀ (by linarith)).2 (by linarith))
  by_cases hx : x ≤ -logLogLambda
  · exact logLogProfile_cost_le_small_left hm hx
  · have hmul := mul_le_mul_of_nonpos_left (show -logLogLambda ≤ x by linarith)
      (show m - 1 ≤ 0 by linarith)
    have hbase := logLogProfile_cost_le_small_left (m := m) (x := -logLogLambda) hm le_rfl
    rw [logLogProfile_neg_lambda] at hbase
    rw [logLogProfile, if_neg hx]
    nlinarith

lemma logLogProfile_cost_attains_small {m : ℝ}
    (hm : 0 < m) (hmb : m ≤ logLogLambda⁻¹) :
    m * (-m⁻¹) - logLogProfile (-m⁻¹) = -Real.log m - 1 := by
  have hell := logLogLambda_gt_two
  have hprod : m * logLogLambda ≤ 1 :=
    (le_div_iff₀ (show 0 < logLogLambda by linarith)).mp (by simpa only [one_div] using hmb)
  have hinv : logLogLambda ≤ m⁻¹ := by
    simpa only [one_div] using
      (le_div_iff₀ hm).mpr (show logLogLambda * m ≤ (1 : ℝ) by nlinarith)
  rw [logLogProfile, if_pos (show -m⁻¹ ≤ -logLogLambda by linarith), neg_neg,
    Real.log_inv, mul_neg, mul_inv_cancel₀ hm.ne']
  ring

lemma logLogProfile_cost_le_large {m : ℝ}
    (hmb : logLogLambda⁻¹ ≤ m) (hmOne : m ≤ 1) (x : ℝ) :
    m * x - logLogProfile x ≤ (1 - m) * logLogLambda - 2 := by
  have hell := logLogLambda_gt_two
  by_cases hx : x ≤ -logLogLambda
  · have htpos : 0 < -x := by linarith
    have hellpos : 0 < logLogLambda := by linarith
    have hlog := Real.log_le_sub_one_of_pos (div_pos htpos hellpos)
    rw [Real.log_div htpos.ne' hellpos.ne', div_eq_mul_inv] at hlog
    have hprod : logLogLambda * logLogLambda⁻¹ = 1 := mul_inv_cancel₀ hellpos.ne'
    have hsign : (-x - logLogLambda) * (logLogLambda⁻¹ - m) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
    rw [log_logLogLambda] at hlog
    rw [logLogProfile, if_pos hx]
    nlinarith
  · have hmul := mul_le_mul_of_nonpos_left (show -logLogLambda ≤ x by linarith)
      (show m - 1 ≤ 0 by linarith)
    rw [logLogProfile, if_neg hx]
    nlinarith

lemma logLogProfile_cost_attains_large (m : ℝ) :
    m * (-logLogLambda) - logLogProfile (-logLogLambda) = (1 - m) * logLogLambda - 2 := by
  rw [logLogProfile_neg_lambda]
  ring

lemma logLogProfile_cost_unbounded_of_nonpos {m : ℝ} (hm : m ≤ 0) (C : ℝ) :
    ∃ x : ℝ, C < m * x - logLogProfile x := by
  let t : ℝ := logLogLambda + Real.exp (C + 1)
  have hell := logLogLambda_gt_two
  have ht : logLogLambda ≤ t := by dsimp [t]; linarith [Real.exp_pos (C + 1)]
  have htpos : 0 < t := by linarith
  have hlog : C + 1 ≤ Real.log t := by
    have h := Real.log_le_log (Real.exp_pos (C + 1))
      (show Real.exp (C + 1) ≤ t by dsimp [t]; linarith)
    simpa only [Real.log_exp] using h
  have hmx : 0 ≤ m * (-t) := mul_nonneg_of_nonpos_of_nonpos hm (by linarith)
  refine ⟨-t, ?_⟩
  rw [logLogProfile, if_pos (show -t ≤ -logLogLambda by linarith), neg_neg]
  linarith

lemma logLogProfile_cost_unbounded_of_one_lt {m : ℝ} (hm : 1 < m) (C : ℝ) :
    ∃ x : ℝ, C < m * x - logLogProfile x := by
  let x : ℝ := max 0 ((C + 2) / (m - 1)) + 1
  have hxpos : 0 < x := by dsimp [x]; linarith [le_max_left (0 : ℝ) ((C + 2) / (m - 1))]
  have hcut : ¬ x ≤ -logLogLambda := by linarith [logLogLambda_gt_two]
  have hratio : (C + 2) / (m - 1) < x := by
    dsimp [x]; linarith [le_max_right (0 : ℝ) ((C + 2) / (m - 1))]
  have hprod := (div_lt_iff₀ (show 0 < m - 1 by linarith)).mp hratio
  refine ⟨x, ?_⟩
  rw [logLogProfile, if_neg hcut]
  nlinarith

def logLogConjugate (m : ℝ) : EReal := ⨆ x : ℝ, ((m * x - logLogProfile x : ℝ) : EReal)

lemma logLogConjugate_small {m : ℝ} (hm : 0 < m) (hmb : m ≤ logLogLambda⁻¹) :
    logLogConjugate m = ((-Real.log m - 1 : ℝ) : EReal) := by
  apply le_antisymm
  · exact iSup_le fun x => EReal.coe_le_coe (logLogProfile_cost_le_small hm hmb x)
  · have h := le_iSup (fun x : ℝ => ((m * x - logLogProfile x : ℝ) : EReal)) (-m⁻¹)
    rwa [logLogProfile_cost_attains_small hm hmb] at h

lemma logLogConjugate_large {m : ℝ} (hmb : logLogLambda⁻¹ ≤ m) (hmOne : m ≤ 1) :
    logLogConjugate m = (((1 - m) * logLogLambda - 2 : ℝ) : EReal) := by
  apply le_antisymm
  · exact iSup_le fun x => EReal.coe_le_coe (logLogProfile_cost_le_large hmb hmOne x)
  · have h := le_iSup (fun x : ℝ => ((m * x - logLogProfile x : ℝ) : EReal)) (-logLogLambda)
    rwa [logLogProfile_cost_attains_large m] at h

lemma logLogConjugate_nonpos {m : ℝ} (hm : m ≤ 0) : logLogConjugate m = ⊤ := by
  apply (EReal.eq_top_iff_forall_lt _).mpr
  intro C
  obtain ⟨x, hx⟩ := logLogProfile_cost_unbounded_of_nonpos hm C
  exact (EReal.coe_lt_coe hx).trans_le
    (le_iSup (fun x : ℝ => ((m * x - logLogProfile x : ℝ) : EReal)) x)

lemma logLogConjugate_one_lt {m : ℝ} (hm : 1 < m) : logLogConjugate m = ⊤ := by
  apply (EReal.eq_top_iff_forall_lt _).mpr
  intro C
  obtain ⟨x, hx⟩ := logLogProfile_cost_unbounded_of_one_lt hm C
  exact (EReal.coe_lt_coe hx).trans_le
    (le_iSup (fun x : ℝ => ((m * x - logLogProfile x : ℝ) : EReal)) x)

def sourceLogLogConjugate (m : ℝ) : EReal :=
  if 0 < m ∧ m ≤ logLogLambda⁻¹ then ((-Real.log m - 1 : ℝ) : EReal)
  else if logLogLambda⁻¹ < m ∧ m ≤ 1 then (((1 - m) * logLogLambda - 2 : ℝ) : EReal)
  else ⊤

lemma logLogConjugate_eq_source (m : ℝ) : logLogConjugate m = sourceLogLogConjugate m := by
  by_cases hm : 0 < m
  · by_cases hmb : m ≤ logLogLambda⁻¹
    · rw [sourceLogLogConjugate, if_pos ⟨hm, hmb⟩]
      exact logLogConjugate_small hm hmb
    · have hmb' : logLogLambda⁻¹ < m := lt_of_not_ge hmb
      by_cases hmOne : m ≤ 1
      · rw [sourceLogLogConjugate, if_neg (by tauto), if_pos ⟨hmb', hmOne⟩]
        exact logLogConjugate_large hmb'.le hmOne
      · rw [sourceLogLogConjugate, if_neg (by tauto), if_neg (by tauto)]
        exact logLogConjugate_one_lt (lt_of_not_ge hmOne)
  · have hm' : m ≤ 0 := le_of_not_gt hm
    have hmb : ¬ logLogLambda⁻¹ < m := by
      have hell := logLogLambda_gt_two
      have hinv : 0 < logLogLambda⁻¹ := inv_pos.mpr (by linarith)
      linarith
    rw [sourceLogLogConjugate, if_neg (by tauto), if_neg (by tauto)]
    exact logLogConjugate_nonpos hm'

end SGPT.Toric

namespace SGPT.Toric
open Set Filter
open scoped Topology

lemma strictMonoOn_logLogCrossingGap_small : StrictMonoOn logLogCrossingGap (Ioo 0 1) := by
  refine strictMonoOn_of_hasDerivWithinAt_pos (f' := fun t : ℝ => t⁻¹ - 1)
    (convex_Ioo 0 1) ?_ ?_ ?_
  · intro t ht
    exact (hasDerivAt_logLogCrossingGap ht.1.ne').continuousAt.continuousWithinAt
  · intro t ht
    have ht' : 0 < t ∧ t < 1 := by simpa only [interior_Ioo, mem_Ioo] using ht
    exact (hasDerivAt_logLogCrossingGap ht'.1.ne').hasDerivWithinAt
  · intro t ht
    have ht' : 0 < t ∧ t < 1 := by simpa only [interior_Ioo, mem_Ioo] using ht
    have hinv : (1 : ℝ) < t⁻¹ := (one_lt_inv₀ ht'.1).2 ht'.2
    linarith

lemma exists_logLogSmallRoot : ∃ ell : ℝ,
    Real.exp (-2) < ell ∧ ell < 1 / 2 ∧ Real.log ell = ell - 2 := by
  have hab : Real.exp (-2) < (1 / 2 : ℝ) := by
    have h := Real.exp_lt_exp.mpr
      (show (-2 : ℝ) < -Real.log 2 by linarith [Real.log_two_lt_d9])
    simpa only [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2), one_div] using h
  have ha : logLogCrossingGap (Real.exp (-2)) < 0 := by
    dsimp [logLogCrossingGap]
    rw [Real.log_exp]
    linarith [Real.exp_pos (-2)]
  have hb : 0 < logLogCrossingGap (1 / 2) := by
    have hlog : Real.log (1 / 2 : ℝ) = -Real.log 2 := by rw [one_div, Real.log_inv]
    dsimp [logLogCrossingGap]
    rw [hlog]
    linarith [Real.log_two_lt_d9]
  have hc : ContinuousOn logLogCrossingGap (Icc (Real.exp (-2)) (1 / 2)) := by
    intro t ht
    exact (hasDerivAt_logLogCrossingGap
      (ne_of_gt ((Real.exp_pos (-2)).trans_le ht.1))).continuousAt.continuousWithinAt
  obtain ⟨ell, hell, hzero⟩ := intermediate_value_Icc hab.le hc
    (show 0 ∈ Icc (logLogCrossingGap (Real.exp (-2))) (logLogCrossingGap (1 / 2))
      from ⟨ha.le, hb.le⟩)
  have hleft : Real.exp (-2) < ell := by
    refine lt_of_le_of_ne hell.1 ?_
    intro heq
    have h := hzero
    rw [← heq] at h
    linarith
  have hright : ell < 1 / 2 := by
    refine lt_of_le_of_ne hell.2 ?_
    intro heq
    have h := hzero
    rw [heq] at h
    linarith
  exact ⟨ell, hleft, hright, by dsimp [logLogCrossingGap] at hzero; linarith⟩

def logLogSmallRoot : ℝ := Classical.choose exists_logLogSmallRoot

lemma logLogSmallRoot_gt_exp_neg_two : Real.exp (-2) < logLogSmallRoot :=
  (Classical.choose_spec exists_logLogSmallRoot).1

lemma logLogSmallRoot_lt_half : logLogSmallRoot < 1 / 2 :=
  (Classical.choose_spec exists_logLogSmallRoot).2.1

lemma log_logLogSmallRoot : Real.log logLogSmallRoot = logLogSmallRoot - 2 :=
  (Classical.choose_spec exists_logLogSmallRoot).2.2

lemma logLogSmallRoot_lt_log_two : logLogSmallRoot < Real.log 2 := by
  linarith [logLogSmallRoot_lt_half, Real.log_two_gt_d9]

lemma logLogSmallRoot_unique {t : ℝ} (ht : 0 < t) (htOne : t < 1)
    (hroot : Real.log t = t - 2) : t = logLogSmallRoot := by
  apply strictMonoOn_logLogCrossingGap_small.injOn ⟨ht, htOne⟩
    ⟨(Real.exp_pos (-2)).trans logLogSmallRoot_gt_exp_neg_two,
      show logLogSmallRoot < 1 by linarith [logLogSmallRoot_lt_half]⟩
  dsimp [logLogCrossingGap]
  rw [hroot, log_logLogSmallRoot]
  ring

end SGPT.Toric
