import SGPT.NPP.FrameFreeMetricJet
import SGPT.NPP.ChartTransitionQuadraticRemainder

/-!
# Actual coordinate overlap of the local polynomial metric jets

The literal local polynomial is kept distinct from the full formal Chern
exponential. Blueprint: `dnt-big-metric-jet-overlap.tex`, written first.
No estimate for a nonsmooth envelope average or its base derivative is an input.
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 3

noncomputable section

open Set Filter Metric
open scoped Topology ContDiff

namespace SGPT.NPP.DNTBig

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Envelopes

variable {n : ℕ}

/-- Actual vanishing two-jets produce actual cubic values and quadratic
operator-derivative bounds on a manufactured neighbourhood. -/
theorem exists_local_cubic_bound_of_zero_two_jet
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {F : ComplexModel n → G} {Ω : Set (ComplexModel n)}
    (hΩ : IsOpen Ω) (hF : ContDiffOn ℝ 3 F Ω) (h0 : (0 : ComplexModel n) ∈ Ω)
    (hF0 : F 0 = 0) (hDF0 : fderiv ℝ F 0 = 0)
    (hD2F0 : fderiv ℝ (fderiv ℝ F) 0 = 0) :
    ∃ r : ℝ, 0 < r ∧ closedBall (0 : ComplexModel n) r ⊆ Ω ∧
      ∃ M : ℝ, 0 ≤ M ∧ ∀ v ∈ closedBall (0 : ComplexModel n) r,
        ‖fderiv ℝ F v‖ ≤ M * ‖v‖ ^ 2 ∧ ‖F v‖ ≤ M * ‖v‖ ^ 3 := by
  have hDF : ContDiffOn ℝ 2 (fderiv ℝ F) Ω :=
    hF.fderiv_of_isOpen hΩ (by norm_num)
  obtain ⟨r, hr, hrΩ, M, hM, hbound⟩ :=
    exists_local_quadratic_remainder_of_contDiffOn hΩ hDF h0
  have hder : ∀ v ∈ closedBall (0 : ComplexModel n) r,
      ‖fderiv ℝ F v‖ ≤ M * ‖v‖ ^ 2 := by
    intro v hv
    have H := hbound 0 (mem_closedBall_self hr.le) v hv
    simpa only [hDF0, hD2F0, _root_.zero_apply, sub_zero] using H
  refine ⟨r, hr, hrΩ, M, hM, fun v hv => ⟨hder v hv, ?_⟩⟩
  have hseg : segment ℝ (0 : ComplexModel n) v ⊆ closedBall 0 r :=
    (convex_closedBall (0 : ComplexModel n) r).segment_subset
      (mem_closedBall_self hr.le) hv
  have hnorm : ∀ w ∈ segment ℝ (0 : ComplexModel n) v, ‖w‖ ≤ ‖v‖ := by
    intro w hw
    rw [segment_eq_image'] at hw
    obtain ⟨t, ht, rfl⟩ := hw
    simp only [sub_zero, zero_add, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
    exact mul_le_of_le_one_left (norm_nonneg _) ht.2
  have hderSeg : ∀ w ∈ segment ℝ (0 : ComplexModel n) v,
      ‖fderiv ℝ F w‖ ≤ M * ‖v‖ ^ 2 := by
    intro w hw
    exact (hder w (hseg hw)).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (hnorm w hw) 2) hM)
  have H := (convex_segment (0 : ComplexModel n) v).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun w hw =>
      (((hF.differentiableOn (by norm_num)).differentiableAt
        (hΩ.mem_nhds (hrΩ (hseg hw)))).hasFDerivAt).hasFDerivWithinAt)
    hderSeg (left_mem_segment ℝ 0 v) (right_mem_segment ℝ 0 v)
  simpa only [hF0, sub_zero, ← pow_succ, mul_assoc] using H

/-- The literal Koszul covector, simultaneously continuous bilinear in its
first two arguments. -/
def metricKoszulBilin
    (D : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ) :
    ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ :=
  (1 / 2 : ℝ) • (D + D.flip -
    (ContinuousLinearMap.flipₗᵢ ℝ (ComplexModel n) (ComplexModel n) ℝ).toContinuousLinearEquiv.toContinuousLinearMap ∘L D.flip)

@[simp] theorem metricKoszulBilin_apply
    (D : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ)
    (p u : ComplexModel n) :
    metricKoszulBilin D p u = metricKoszulCovector D p u := by
  ext v
  simp [metricKoszulBilin, metricKoszulCovector, ContinuousLinearMap.flip_apply]

/-- The SAME inverse-metric coefficient as an actual continuous bilinear map. -/
def metricConnectionBilin
    (g : ComplexModel n → ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ)
    (z : ComplexModel n) : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ComplexModel n :=
  (ContinuousLinearMap.compL ℝ (ComplexModel n) (ComplexModel n →L[ℝ] ℝ)
    (ComplexModel n) (ContinuousLinearMap.inverse (g z).flip)) ∘L
      metricKoszulBilin (fderiv ℝ g z)

@[simp] theorem metricConnectionBilin_apply
    (g : ComplexModel n → ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ)
    (z p u : ComplexModel n) :
    metricConnectionBilin g z p u = metricConnection g z p u := by
  simp only [metricConnectionBilin, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.compL_apply, metricKoszulBilin_apply,
    metricConnection, TosC11c.gradVec]

/-- The actual quadratic polynomial for any real continuous bilinear coefficient. -/
def bilinearQuadraticJet
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (z : E) (B : E →L[ℝ] E →L[ℝ] E) (v : E) : E :=
  z + v - (1 / 2 : ℝ) • B v v

/-- The actual first derivative operator of this polynomial. -/
def bilinearQuadraticJetDeriv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : E →L[ℝ] E →L[ℝ] E) (v : E) : E →L[ℝ] E :=
  ContinuousLinearMap.id ℝ E - (1 / 2 : ℝ) • (B v + B.flip v)

/-- The constant actual second derivative operator. -/
def bilinearQuadraticJetSecond
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : E →L[ℝ] E →L[ℝ] E) : E →L[ℝ] E →L[ℝ] E :=
  -(1 / 2 : ℝ) • (B + B.flip)

/-- Actual derivative of the polynomial, without an unnecessary symmetry assumption. -/
theorem hasFDerivAt_bilinearQuadraticJet
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (z : E) (B : E →L[ℝ] E →L[ℝ] E) (v : E) :
    HasFDerivAt (bilinearQuadraticJet z B) (bilinearQuadraticJetDeriv B v) v := by
  have hq := B.hasFDerivAt_of_bilinear (hasFDerivAt_id v) (hasFDerivAt_id v)
  have H := ((hasFDerivAt_id v).const_add z).sub (hq.const_smul (1 / 2 : ℝ))
  change HasFDerivAt (bilinearQuadraticJet z B) _ v at H
  apply H.congr_fderiv
  apply ContinuousLinearMap.ext
  intro p
  simp [bilinearQuadraticJetDeriv, ContinuousLinearMap.precompR_apply,
    ContinuousLinearMap.precompL_apply, ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.flip_apply]

/-- Actual constant second derivative of the same polynomial. -/
theorem hasFDerivAt_fderiv_bilinearQuadraticJet
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (z : E) (B : E →L[ℝ] E →L[ℝ] E) (v : E) :
    HasFDerivAt (fderiv ℝ (bilinearQuadraticJet z B))
      (bilinearQuadraticJetSecond B) v := by
  have hfun : fderiv ℝ (bilinearQuadraticJet z B) = bilinearQuadraticJetDeriv B :=
    funext fun w => (hasFDerivAt_bilinearQuadraticJet z B w).fderiv
  rw [hfun]
  have H := (hasFDerivAt_const (ContinuousLinearMap.id ℝ E) v).sub
    ((B.hasFDerivAt.add B.flip.hasFDerivAt).const_smul (1 / 2 : ℝ))
  change HasFDerivAt (bilinearQuadraticJetDeriv B) _ v at H
  simpa only [zero_sub, neg_smul, bilinearQuadraticJetSecond] using H

@[simp] theorem bilinearQuadraticJet_metricConnection
    (g : ComplexModel n → ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ)
    (z v : ComplexModel n) :
    bilinearQuadraticJet z (metricConnectionBilin g z) v = metricQuadraticJet g z v := by
  simp only [bilinearQuadraticJet, metricQuadraticJet, metricConnectionBilin_apply]


/-- The literal overlap difference for the two actual metric polynomial jets. -/
def metricJetOverlap
    (g : ComplexModel n → ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ)
    (φ : ComplexModel n → ComplexModel n) (z v : ComplexModel n) : ComplexModel n :=
  φ (metricQuadraticJet (TosC11b.pullbackBilin g φ) z v) -
    metricQuadraticJet g (φ z) (fderiv ℝ φ z v)

/-- The actual local polynomial has the expected value and derivative at zero. -/
theorem metricJetOverlap_zero_two_jet
    {g : ComplexModel n → ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ}
    {φ : ComplexModel n → ComplexModel n} {Ω : Set (ComplexModel n)}
    (hΩ : IsOpen Ω) (hφ : ContDiffOn ℝ 3 φ Ω)
    {z : ComplexModel n} (hz : z ∈ Ω)
    (hg : DifferentiableAt ℝ g (φ z))
    (hpos : ∀ v, v ≠ 0 → 0 < g (φ z) v v)
    (hsym : ∀ v t, g (φ z) v t = g (φ z) t v)
    (L : ComplexModel n ≃L[ℝ] ComplexModel n)
    (hL : fderiv ℝ φ z = L.toContinuousLinearMap) :
    metricJetOverlap g φ z 0 = 0 ∧
      fderiv ℝ (metricJetOverlap g φ z) 0 = 0 ∧
      fderiv ℝ (fderiv ℝ (metricJetOverlap g φ z)) 0 = 0 := by
  let B := metricConnectionBilin (TosC11b.pullbackBilin g φ) z
  let C := metricConnectionBilin g (φ z)
  let J := bilinearQuadraticJet z B
  let K := bilinearQuadraticJet (φ z) C
  let R := fun v => φ (J v) - K (L v)
  have hR : metricJetOverlap g φ z = R := by
    funext v
    simp only [metricJetOverlap, hL, R, J, K, B, C,
      bilinearQuadraticJet_metricConnection, ContinuousLinearEquiv.coe_coe]
  have hJ0 : J 0 = z := by simp [J, bilinearQuadraticJet]
  have hK0 : K 0 = φ z := by simp [K, bilinearQuadraticJet]
  have hDJ0 : bilinearQuadraticJetDeriv B 0 = ContinuousLinearMap.id ℝ _ := by
    simp [bilinearQuadraticJetDeriv]
  have hDK0 : bilinearQuadraticJetDeriv C 0 = ContinuousLinearMap.id ℝ _ := by
    simp [bilinearQuadraticJetDeriv]
  have hφz : ContDiffAt ℝ 3 φ z := hφ.contDiffAt (hΩ.mem_nhds hz)
  have hφ1 : HasFDerivAt φ L.toContinuousLinearMap z := by
    rw [← hL]
    exact (hφz.differentiableAt (by norm_num)).hasFDerivAt
  have hJ : ∀ v, HasFDerivAt J (bilinearQuadraticJetDeriv B v) v :=
    hasFDerivAt_bilinearQuadraticJet z B
  have hK : ∀ v, HasFDerivAt K (bilinearQuadraticJetDeriv C v) v :=
    hasFDerivAt_bilinearQuadraticJet (φ z) C
  have hR1 : HasFDerivAt R (0 : ComplexModel n →L[ℝ] ComplexModel n) 0 := by
    have hφJ0 : HasFDerivAt φ L.toContinuousLinearMap (J 0) := by
      simpa only [hJ0] using hφ1
    have H := (hφJ0.comp (0 : ComplexModel n) (hJ 0)).sub
      ((hK (L 0)).comp 0 L.hasFDerivAt)
    change HasFDerivAt R _ 0 at H
    rw [map_zero, hDJ0, hDK0] at H
    simpa only [ContinuousLinearMap.comp_id, ContinuousLinearMap.id_comp, sub_self] using H
  let d := fun v => (fderiv ℝ φ (J v)).comp (bilinearQuadraticJetDeriv B v) -
    (bilinearQuadraticJetDeriv C (L v)).comp L.toContinuousLinearMap
  have hd : d =ᶠ[𝓝 (0 : ComplexModel n)] fderiv ℝ R := by
    have hcont : ContinuousAt J 0 := (hJ 0).continuousAt
    have hJU : ∀ᶠ v in 𝓝 (0 : ComplexModel n), J v ∈ Ω := by
      exact hcont.preimage_mem_nhds (by simpa only [hJ0] using hΩ.mem_nhds hz)
    filter_upwards [hJU] with v hv
    have H := (((hφ.differentiableOn (by norm_num)).differentiableAt
      (hΩ.mem_nhds hv)).hasFDerivAt.comp v (hJ v)).sub ((hK (L v)).comp v L.hasFDerivAt)
    exact H.fderiv.symm
  have hDφ : HasFDerivAt (fderiv ℝ φ) (fderiv ℝ (fderiv ℝ φ) z) z :=
    ((hφz.fderiv_right (m := 2) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hDφJ : HasFDerivAt (fun v => fderiv ℝ φ (J v))
      (fderiv ℝ (fderiv ℝ φ) z) 0 := by
    have hDφJ0 : HasFDerivAt (fderiv ℝ φ) (fderiv ℝ (fderiv ℝ φ) z) (J 0) := by
      simpa only [hJ0] using hDφ
    have H := hDφJ0.comp 0 (hJ 0)
    change HasFDerivAt (fun v => fderiv ℝ φ (J v)) _ 0 at H
    simpa only [hJ0, hDJ0, ContinuousLinearMap.comp_id] using H
  have hDB : HasFDerivAt (bilinearQuadraticJetDeriv B)
      (bilinearQuadraticJetSecond B) (0 : ComplexModel n) := by
    have H := hasFDerivAt_fderiv_bilinearQuadraticJet z B (0 : ComplexModel n)
    have heq : fderiv ℝ J = bilinearQuadraticJetDeriv B := funext fun v => (hJ v).fderiv
    rwa [show fderiv ℝ (bilinearQuadraticJet z B) = fderiv ℝ J from rfl, heq] at H
  have hDC : ∀ v, HasFDerivAt (bilinearQuadraticJetDeriv C)
      (bilinearQuadraticJetSecond C) v := by
    intro v
    have H := hasFDerivAt_fderiv_bilinearQuadraticJet (φ z) C v
    have heq : fderiv ℝ K = bilinearQuadraticJetDeriv C := funext fun t => (hK t).fderiv
    rwa [show fderiv ℝ (bilinearQuadraticJet (φ z) C) = fderiv ℝ K from rfl, heq] at H
  have H := (hDφJ.clm_comp hDB).sub
    (((hDC (L 0)).comp 0 L.hasFDerivAt).clm_comp
      (hasFDerivAt_const L.toContinuousLinearMap 0))
  have hd0 : HasFDerivAt d (0 : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ComplexModel n) 0 := by
    apply H.congr_fderiv
    apply ContinuousLinearMap.ext
    intro p
    apply ContinuousLinearMap.ext
    intro u
    have hpu := metricConnection_pullback hg hpos hsym
      (hφz.of_le (by norm_num)) L hL p u
    have hup := metricConnection_pullback hg hpos hsym
      (hφz.of_le (by norm_num)) L hL u p
    have hswap : fderiv ℝ (fderiv ℝ φ) z p u = fderiv ℝ (fderiv ℝ φ) z u p :=
      (hφz.isSymmSndFDerivAt (by norm_num [minSmoothness])) p u
    simp only [hJ0, hDJ0, map_zero, hL,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.compL_apply,
      ContinuousLinearMap.flip_apply, _root_.add_apply,
      _root_.sub_apply, _root_.zero_apply,
      bilinearQuadraticJetSecond, _root_.smul_apply,
      map_smul, map_add, ContinuousLinearMap.id_apply,
      ContinuousLinearEquiv.coe_coe, B, C, metricConnectionBilin_apply] at ⊢
    rw [hpu, hup, ← hswap]
    module
  refine ⟨?_, ?_, ?_⟩
  · rw [hR]
    simp only [R, hJ0, map_zero, hK0, sub_self]
  · rw [hR]
    exact hR1.fderiv
  · rw [hR]
    exact (hd0.congr_of_eventuallyEq hd.symm).fderiv


/-- Cubic actual value overlap and quadratic fibre-derivative overlap follow
from the actual metric law; neither estimate is an incoming certificate. -/
theorem actual_metricQuadraticJet_locally_cubic_overlap
    {g : ComplexModel n → ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ}
    {φ : ComplexModel n → ComplexModel n} {Ω : Set (ComplexModel n)}
    (hΩ : IsOpen Ω) (hφ : ContDiffOn ℝ 3 φ Ω)
    {z : ComplexModel n} (hz : z ∈ Ω)
    (hg : DifferentiableAt ℝ g (φ z))
    (hpos : ∀ v, v ≠ 0 → 0 < g (φ z) v v)
    (hsym : ∀ v t, g (φ z) v t = g (φ z) t v)
    (L : ComplexModel n ≃L[ℝ] ComplexModel n)
    (hL : fderiv ℝ φ z = L.toContinuousLinearMap) :
    ∃ r : ℝ, 0 < r ∧ ∃ M : ℝ, 0 ≤ M ∧
      ∀ v ∈ closedBall (0 : ComplexModel n) r,
        ‖fderiv ℝ (metricJetOverlap g φ z) v‖ ≤ M * ‖v‖ ^ 2 ∧
        ‖metricJetOverlap g φ z v‖ ≤ M * ‖v‖ ^ 3 := by
  have hpoly : ∀ (a : ComplexModel n)
      (B : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ComplexModel n),
      ContDiff ℝ 3 (bilinearQuadraticJet a B) := by
    intro a B
    exact (contDiff_const.add contDiff_id).sub
      ((B.contDiff.clm_apply contDiff_id).const_smul (1 / 2 : ℝ))
  have hjet : ∀ (h : ComplexModel n → ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ)
      (a : ComplexModel n), ContDiff ℝ 3 (metricQuadraticJet h a) := by
    intro h a
    have heq : metricQuadraticJet h a = bilinearQuadraticJet a (metricConnectionBilin h a) := by
      funext v
      exact (bilinearQuadraticJet_metricConnection h a v).symm
    rw [heq]
    exact hpoly a _
  have hJ0 : metricQuadraticJet (TosC11b.pullbackBilin g φ) z 0 = z := by
    rw [← bilinearQuadraticJet_metricConnection]
    simp [bilinearQuadraticJet]
  have hφJ0 : ContDiffAt ℝ 3 φ (metricQuadraticJet (TosC11b.pullbackBilin g φ) z 0) := by
    simpa only [hJ0] using hφ.contDiffAt (hΩ.mem_nhds hz)
  have hR : ContDiffAt ℝ 3 (metricJetOverlap g φ z) 0 :=
    (hφJ0.comp 0 (hjet (TosC11b.pullbackBilin g φ) z).contDiffAt).sub
      ((hjet g (φ z)).contDiffAt.comp 0 (fderiv ℝ φ z).contDiff.contDiffAt)
  obtain ⟨U, hU, h0U, hRU⟩ := hR.contDiffOn' (m := 3) le_rfl (by simp)
  simp only [insert_eq_of_mem (mem_univ (0 : ComplexModel n)), univ_inter] at hRU
  obtain ⟨h0, hd0, hd20⟩ := metricJetOverlap_zero_two_jet hΩ hφ hz hg hpos hsym L hL
  obtain ⟨r, hr, _, M, hM, hbound⟩ :=
    exists_local_cubic_bound_of_zero_two_jet hU hRU h0U h0 hd0 hd20
  exact ⟨r, hr, M, hM, hbound⟩

end SGPT.NPP.DNTBig
