import SGPT.Foundations.Analysis.Pending.ActualHilbertEvaluationCoordinateDivision
import SGPT.Foundations.Analysis.Pending.HolomorphicCoordinateFactorization
import SGPT.Foundations.Analysis.Pending.HolomorphicAnalytic
import Mathlib.Analysis.Analytic.Uniqueness

set_option autoImplicit false

/-! # Smooth positive dual normalization from the whole principal evaluation ideal

All scalar evaluation germs of the actual Hilbert-dual map generate one
principal SNC ideal. The orders, the common dual quotient, and its nonzero
value are produced internally. This is a local principalized-kernel result.
-/

noncomputable section
open Set Filter Metric
open scoped Topology ContDiff

namespace SGPT.Foundations.Analysis.Pending.ActualHilbertEvaluationPrincipalNormalization

section General
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

private def evalGerm (A : E → StrongDual ℂ H)
    (hA : ∀ᶠ x in 𝓝 (0 : E), DifferentiableAt ℂ A x) (F : H) : HolGerm E :=
  HolGerm.mk (fun x => A x F) (hA.mono fun _ hx => hx.clm_apply (differentiableAt_const F))

private def linearGerm (l : E →L[ℂ] ℂ) : HolGerm E :=
  HolGerm.mk l (Eventually.of_forall fun _ => l.differentiableAt)

omit [FiniteDimensional ℂ E] in
private theorem linearGerm_ne_zero {l : E →L[ℂ] ℂ} (hl : l ≠ 0) : linearGerm l ≠ 0 := by
  intro hz
  have he : (l : E → ℂ) =ᶠ[𝓝 0] (0 : E → ℂ) :=
    HolGerm.mk_eq_mk_iff.mp (hz.trans HolGerm.mk_zero.symm)
  have hd : fderiv ℂ (l : E → ℂ) 0 = 0 := by rw [he.fderiv_eq]; simp
  rw [l.hasFDerivAt.fderiv] at hd
  exact hl hd

private def splitFunctional (l : E →L[ℂ] ℂ) (v : E) (hv : l v = 1) :
    E ≃L[ℂ] (LinearMap.ker l.toLinearMap) × ℂ :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun x => (⟨x - l x • v, by simp [map_sub, map_smul, hv]⟩, l x)
      invFun := fun x => x.1.val + x.2 • v
      map_add' := fun x y => by ext <;> simp [map_add, add_smul, sub_add_sub_comm]
      map_smul' := fun c x => by ext <;> simp [map_smul, smul_sub, smul_smul]
      left_inv := fun x => by simp
      right_inv := fun x => by
        have hx : l x.1.val = 0 := x.1.property
        ext <;> simp [map_add, map_smul, hv, hx] }

private theorem exists_linear_dual_quotient
    {A : E → StrongDual ℂ H}
    (hA : ∀ᶠ x in 𝓝 (0 : E), DifferentiableAt ℂ A x)
    {l : E →L[ℂ] ℂ} (hl : l ≠ 0)
    (hdiv : ∀ F : H, linearGerm l ∣ evalGerm A hA F) :
    ∃ (Q : E → StrongDual ℂ H)
      (_hQ : ∀ᶠ x in 𝓝 (0 : E), DifferentiableAt ℂ Q x),
      A =ᶠ[𝓝 0] fun x => l x • Q x := by
  classical
  have hex : ∃ w : E, l w ≠ 0 := by
    by_contra hh
    push Not at hh
    exact hl (ContinuousLinearMap.ext hh)
  obtain ⟨w, hw⟩ := hex
  let v : E := (l w)⁻¹ • w
  have hv : l v = 1 := by simp [v, map_smul, hw]
  let L := splitFunctional l v hv
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp hA
  have hAb : DifferentiableOn ℂ A (ball (0 : E) r) :=
    fun x hx => (hball x hx).differentiableWithinAt
  have hz : ∀ z ∈ ball (0 : LinearMap.ker l.toLinearMap) r, A z.val = 0 := by
    intro z hz
    apply ContinuousLinearMap.ext
    intro F
    obtain ⟨b, hb⟩ := hdiv F
    obtain ⟨f, hf, hbf⟩ := HolGerm.exists_eq_mk b
    have he : (fun x => A x F) =ᶠ[𝓝 (0 : E)] fun x => l x * f x := by
      apply HolGerm.mk_eq_mk_iff.mp
      change evalGerm A hA F = _
      rw [hb, hbf]
      exact (HolGerm.mk_mul l f (Eventually.of_forall fun _ => l.differentiableAt) hf).symm
    have he0 : (fun z : LinearMap.ker l.toLinearMap => A z.val F) =ᶠ[𝓝 0] 0 := by
      have ht : Tendsto (fun z : LinearMap.ker l.toLinearMap => z.val) (𝓝 0) (𝓝 (0 : E)) := by
        simpa using continuous_subtype_val.tendsto (0 : LinearMap.ker l.toLinearMap)
      filter_upwards [ht.eventually he] with z hz
      simp only [hz, show l z.val = 0 from z.property, zero_mul, Pi.zero_apply]
    have hscalar : DifferentiableOn ℂ (fun z : LinearMap.ker l.toLinearMap => A z.val F)
        (ball (0 : LinearMap.ker l.toLinearMap) r) :=
      (hAb.clm_apply (differentiableOn_const F)).comp
        (LinearMap.ker l.toLinearMap).subtype.toContinuousLinearMap.differentiableOn (fun z hz => by
          simpa only [mem_ball, dist_zero_right, Submodule.norm_coe] using hz)
    have han := HolomorphicAnalytic.analyticOnNhd_of_differentiableOn isOpen_ball hscalar
    exact han.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_ball (0 : LinearMap.ker l.toLinearMap) r).isPreconnected (mem_ball_self hr) he0 hz
  let A' : (LinearMap.ker l.toLinearMap) × ℂ → StrongDual ℂ H := fun x => A (L.symm x)
  have hA' : ∀ᶠ x in 𝓝 (0 : (LinearMap.ker l.toLinearMap) × ℂ), DifferentiableAt ℂ A' x := by
    have ht := HolGerm.tendsto_clm_nhds_zero L.symm.toContinuousLinearMap
    filter_upwards [ht.eventually hA] with x hx
    exact hx.comp x L.symm.differentiableAt
  have hz' : ∀ᶠ z in 𝓝 (0 : LinearMap.ker l.toLinearMap), A' (z, 0) = 0 := by
    filter_upwards [ball_mem_nhds (0 : LinearMap.ker l.toLinearMap) hr] with z hzball
    simpa [A', L, splitFunctional] using hz z hzball
  obtain ⟨s, hs, hQ', _, heq⟩ :=
    ActualHilbertEvaluationCoordinateDivision.exists_smooth_dual_coordinate_quotient hA' hz'
  let Q : E → StrongDual ℂ H := fun x =>
    ActualHilbertEvaluationCoordinateDivision.coordinateQuotient A' (L x)
  have ht := HolGerm.tendsto_clm_nhds_zero L.toContinuousLinearMap
  have hQ : ∀ᶠ x in 𝓝 (0 : E), DifferentiableAt ℂ Q x := by
    filter_upwards [ht.eventually (ball_mem_nhds (0 : (LinearMap.ker l.toLinearMap) × ℂ) hs)] with x hx
    exact (hQ'.differentiableAt (isOpen_ball.mem_nhds hx)).comp x L.differentiableAt
  refine ⟨Q, hQ, ?_⟩
  filter_upwards [ht.eventually (ball_mem_nhds (0 : (LinearMap.ker l.toLinearMap) × ℂ) hs)] with x hx
  simpa [A', Q, L, splitFunctional] using (heq (L x) hx).1

private def factorProduct (p : List (E →L[ℂ] ℂ)) (x : E) : ℂ :=
  (p.map fun l => l x).prod

omit [FiniteDimensional ℂ E] in
private theorem factorProduct_hol (p : List (E →L[ℂ] ℂ)) :
    ∀ᶠ x in 𝓝 (0 : E), DifferentiableAt ℂ (factorProduct p) x := by
  induction p with
  | nil => exact Eventually.of_forall fun _ => differentiableAt_const 1
  | cons l p ih =>
    filter_upwards [ih] with x hx
    exact l.differentiableAt.mul hx

omit [FiniteDimensional ℂ E] in
private theorem factorProduct_germ_cons (l : E →L[ℂ] ℂ) (p : List (E →L[ℂ] ℂ)) :
    HolGerm.mk (factorProduct (l :: p)) (factorProduct_hol (l :: p)) =
      linearGerm l * HolGerm.mk (factorProduct p) (factorProduct_hol p) := by
  exact HolGerm.mk_mul l (factorProduct p)
    (Eventually.of_forall fun _ => l.differentiableAt) (factorProduct_hol p)

private theorem exists_product_dual_quotient (p : List (E →L[ℂ] ℂ))
    (hp : ∀ l ∈ p, l ≠ 0) {A : E → StrongDual ℂ H}
    (hA : ∀ᶠ x in 𝓝 (0 : E), DifferentiableAt ℂ A x)
    (hdiv : ∀ F : H, HolGerm.mk (factorProduct p) (factorProduct_hol p) ∣ evalGerm A hA F) :
    ∃ (Q : E → StrongDual ℂ H)
      (_hQ : ∀ᶠ x in 𝓝 (0 : E), DifferentiableAt ℂ Q x),
      A =ᶠ[𝓝 0] fun x => factorProduct p x • Q x := by
  classical
  induction p generalizing A with
  | nil =>
    refine ⟨A, hA, ?_⟩
    filter_upwards with x
    simp [factorProduct]
  | cons l p ih =>
    have hl : l ≠ 0 := hp l (List.mem_cons_self)
    have hlDiv : ∀ F : H, linearGerm l ∣ evalGerm A hA F := by
      intro F
      refine dvd_trans (dvd_mul_right (linearGerm l)
        (HolGerm.mk (factorProduct p) (factorProduct_hol p))) ?_
      simpa only [factorProduct_germ_cons] using hdiv F
    obtain ⟨B, hB, hAB⟩ := exists_linear_dual_quotient hA hl hlDiv
    have hABg (F : H) : evalGerm A hA F = linearGerm l * evalGerm B hB F := by
      apply (HolGerm.mk_eq_mk_iff).mpr ?_ |>.trans
        (HolGerm.mk_mul l (fun x => B x F)
          (Eventually.of_forall fun _ => l.differentiableAt)
          (hB.mono fun _ hx => hx.clm_apply (differentiableAt_const F)))
      filter_upwards [hAB] with x hx
      exact congrArg (fun T : StrongDual ℂ H => T F) hx
    have hBDiv : ∀ F : H,
        HolGerm.mk (factorProduct p) (factorProduct_hol p) ∣ evalGerm B hB F := by
      intro F
      obtain ⟨b, hb⟩ := hdiv F
      refine ⟨b, ?_⟩
      apply mul_left_cancel₀ (linearGerm_ne_zero hl)
      rw [← hABg F, hb, factorProduct_germ_cons, mul_assoc]
    obtain ⟨Q, hQ, hBQ⟩ := ih (fun k hk => hp k (List.mem_cons_of_mem l hk)) hB hBDiv
    refine ⟨Q, hQ, ?_⟩
    filter_upwards [hAB, hBQ] with x hx hy
    rw [hx, hy, smul_smul]
    rfl

private theorem smooth_squared_dual_norm {Q : E → StrongDual ℂ H} {U : Set E}
    (hU : IsOpen U) (hQ : DifferentiableOn ℂ Q U) :
    ContDiffOn ℝ ∞ (fun x => ‖Q x‖ ^ 2) U := by
  let T := (InnerProductSpace.toDual ℂ H).symm
  let T' := @IsometryEquiv.toRealLinearIsometryEquivOfMapZero
    (StrongDual ℂ H) H _ NormedSpace.complexToReal _ _ T.toIsometryEquiv T.map_zero
  have ht := (contDiff_norm_sq ℂ).comp_contDiffOn
    (T'.contDiff.comp_contDiffOn (FirstPass.contDiffOn_real_of_differentiableOn_complex hQ hU))
  refine ht.congr fun x _ => ?_
  change ‖Q x‖ ^ 2 = ‖T' (Q x)‖ ^ 2
  rw [T'.norm_map]


omit [FiniteDimensional ℂ E] [CompleteSpace H] in
private theorem evalGerm_factor {A Q : E → StrongDual ℂ H} {g : E → ℂ}
    (hA : ∀ᶠ x in 𝓝 (0 : E), DifferentiableAt ℂ A x)
    (hQ : ∀ᶠ x in 𝓝 (0 : E), DifferentiableAt ℂ Q x)
    (hg : ∀ᶠ x in 𝓝 (0 : E), DifferentiableAt ℂ g x)
    (he : A =ᶠ[𝓝 0] fun x => g x • Q x) (F : H) :
    evalGerm A hA F = HolGerm.mk g hg * evalGerm Q hQ F := by
  have hs : (fun x => A x F) =ᶠ[𝓝 (0 : E)] fun x => g x * Q x F := by
    filter_upwards [he] with x hx
    simpa using congrArg (fun T : StrongDual ℂ H => T F) hx
  exact (HolGerm.mk_eq_mk_iff.mpr hs).trans
    (HolGerm.mk_mul g (fun x => Q x F) hg
      (hQ.mono fun _ hx => hx.clm_apply (differentiableAt_const F)))

omit [FiniteDimensional ℂ E] [CompleteSpace H] in
private theorem dual_quotient_ne_zero_of_whole_span {A Q : E → StrongDual ℂ H}
    {g : E → ℂ}
    (hA : ∀ᶠ x in 𝓝 (0 : E), DifferentiableAt ℂ A x)
    (hQ : ∀ᶠ x in 𝓝 (0 : E), DifferentiableAt ℂ Q x)
    (hg : ∀ᶠ x in 𝓝 (0 : E), DifferentiableAt ℂ g x)
    (hg0 : HolGerm.mk g hg ≠ 0)
    (he : A =ᶠ[𝓝 0] fun x => g x • Q x)
    (hprincipal : Ideal.span (Set.range (evalGerm A hA)) = Ideal.span {HolGerm.mk g hg}) :
    Q 0 ≠ 0 := by
  intro hzero
  have hmem : HolGerm.mk g hg ∈ Ideal.span (Set.range (evalGerm A hA)) := by
    rw [hprincipal]
    exact Ideal.subset_span (Set.mem_singleton _)
  have hprop : ∀ y ∈ Ideal.span (Set.range (evalGerm A hA)),
      ∃ b : HolGerm E, y = HolGerm.mk g hg * b ∧ HolGerm.eval b = 0 := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨F, rfl⟩ := hy
      refine ⟨evalGerm Q hQ F, evalGerm_factor hA hQ hg he F, ?_⟩
      simp [evalGerm, hzero]
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨b, rfl, hb⟩ := hx
      obtain ⟨c, rfl, hc⟩ := hy
      exact ⟨b + c, by simp [mul_add], by simp [map_add, hb, hc]⟩
    | smul c x _ hx =>
      obtain ⟨b, rfl, hb⟩ := hx
      refine ⟨c * b, ?_, by simp [map_mul, hb]⟩
      simp only [smul_eq_mul]
      ring
  obtain ⟨b, hb, hb0⟩ := hprop _ hmem
  have hb1 : b = 1 := by
    apply mul_left_cancel₀ hg0
    simpa using hb.symm
  simp [hb1] at hb0

end General

open FirstPass HolomorphicGermReducednessBridge

private def coordinateFactors {n : ℕ} (a : Fin n → ℕ) :
    List (ComplexModel n →L[ℂ] ℂ) :=
  (List.ofFn fun j : Fin n => List.replicate (a j) (EuclideanSpace.proj (𝕜 := ℂ) j)).flatten

private theorem coordinateFactors_product {n : ℕ} (a : Fin n → ℕ) (x : ComplexModel n) :
    factorProduct (coordinateFactors a) x = ∏ j : Fin n, x j ^ a j := by
  simp [factorProduct, coordinateFactors, List.prod_flatten, List.prod_ofFn]

private theorem coordinateFactors_nonzero {n : ℕ} (a : Fin n → ℕ) :
    ∀ l ∈ coordinateFactors a, l ≠ 0 := by
  intro l hl
  obtain ⟨s, hs, hl⟩ := List.mem_flatten.mp hl
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hs
  have he : l = EuclideanSpace.proj (𝕜 := ℂ) j := (List.mem_replicate.mp hl).2
  subst l
  intro hz
  apply coordinate_germ_ne_zero j
  change linearGerm (EuclideanSpace.proj (𝕜 := ℂ) j) = 0
  rw [hz]
  exact HolGerm.mk_zero

private theorem factorProduct_germ_nonzero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (p : List (E →L[ℂ] ℂ)) (hp : ∀ l ∈ p, l ≠ 0) :
    HolGerm.mk (factorProduct p) (factorProduct_hol p) ≠ 0 := by
  induction p with
  | nil =>
    change (1 : HolGerm E) ≠ 0
    exact one_ne_zero
  | cons l p ih =>
    rw [factorProduct_germ_cons]
    exact mul_ne_zero (linearGerm_ne_zero (hp l List.mem_cons_self))
      (ih (fun k hk => hp k (List.mem_cons_of_mem l hk)))

/-- The full principal evaluation ideal internally produces a smooth positive residual kernel. -/
theorem exists_smooth_positive_principal_quotient {n : ℕ} {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {A : ComplexModel n → StrongDual ℂ H} {g : ComplexModel n → ℂ}
    (hA : ∀ᶠ x in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ A x)
    (hg : ∀ᶠ x in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ g x)
    (hprincipal : Ideal.span (Set.range fun F : H => HolGerm.mk (fun x => A x F)
        (hA.mono fun _ hx => hx.clm_apply (differentiableAt_const F))) =
      Ideal.span {HolGerm.mk g hg})
    (hzero : ∀ᶠ x in 𝓝 (0 : ComplexModel n), g x = 0 → ∃ j : Fin n, x j = 0) :
    ∃ (Q : ComplexModel n → StrongDual ℂ H) (r : ℝ), 0 < r ∧
      DifferentiableOn ℂ Q (ball (0 : ComplexModel n) r) ∧
      ContDiffOn ℝ ∞ (fun x => ‖Q x‖ ^ 2) (ball (0 : ComplexModel n) r) ∧
      ∀ x ∈ ball (0 : ComplexModel n) r,
        0 < ‖Q x‖ ^ 2 ∧ A x = g x • Q x ∧ ‖A x‖ ^ 2 = ‖g x‖ ^ 2 * ‖Q x‖ ^ 2 := by
  classical
  obtain ⟨a, u, hu, hu0, hfac⟩ :=
    HolomorphicCoordinateFactorization.exists_unit_mul_coordinate_monomial_of_zero_locus hg hzero
  let p := coordinateFactors a
  have hp : ∀ l ∈ p, l ≠ 0 := coordinateFactors_nonzero a
  have huNear : ∀ᶠ x in 𝓝 (0 : ComplexModel n), u x ≠ 0 :=
    hu.self_of_nhds.continuousAt.eventually_ne hu0
  have hfacP : g =ᶠ[𝓝 (0 : ComplexModel n)] fun x => u x * factorProduct p x := by
    filter_upwards [hfac] with x hx
    simpa only [p, coordinateFactors_product] using hx
  have hgerm : HolGerm.mk g hg =
      HolGerm.mk u hu * HolGerm.mk (factorProduct p) (factorProduct_hol p) :=
    (HolGerm.mk_eq_mk_iff.mpr hfacP).trans
      (HolGerm.mk_mul u (factorProduct p) hu (factorProduct_hol p))
  have hgNonzero : HolGerm.mk g hg ≠ 0 := by
    rw [hgerm]
    exact mul_ne_zero (fun hz => hu0 (by simpa using congrArg HolGerm.eval hz))
      (factorProduct_germ_nonzero p hp)
  have hdiv : ∀ F : H, HolGerm.mk (factorProduct p) (factorProduct_hol p) ∣ evalGerm A hA F := by
    intro F
    have hf : HolGerm.mk g hg ∣ evalGerm A hA F := by
      apply Ideal.mem_span_singleton.mp
      rw [← hprincipal]
      exact Ideal.subset_span ⟨F, rfl⟩
    apply dvd_trans (dvd_mul_left (HolGerm.mk (factorProduct p) (factorProduct_hol p))
      (HolGerm.mk u hu))
    rwa [← hgerm]
  obtain ⟨B, hB, hAB⟩ := exists_product_dual_quotient p hp hA hdiv
  let Q : ComplexModel n → StrongDual ℂ H := fun x => (u x)⁻¹ • B x
  have hQ : ∀ᶠ x in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ Q x := by
    filter_upwards [hu, huNear, hB] with x hux hun hx
    exact (hux.inv hun).smul hx
  have hAQ : A =ᶠ[𝓝 (0 : ComplexModel n)] fun x => g x • Q x := by
    filter_upwards [hAB, hfacP, huNear] with x hx hfacx hun
    rw [hx, hfacx]
    dsimp only [Q]
    rw [smul_smul]
    congr 1
    field_simp
  have hQ0 : Q 0 ≠ 0 := dual_quotient_ne_zero_of_whole_span hA hQ hg hgNonzero hAQ hprincipal
  have hpos : ∀ᶠ x in 𝓝 (0 : ComplexModel n), 0 < ‖Q x‖ ^ 2 :=
    (hQ.self_of_nhds.continuousAt.norm.pow 2).eventually
      (lt_mem_nhds (pow_pos (norm_pos_iff.mpr hQ0) 2))
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp (hQ.and (hpos.and hAQ))
  have hQr : DifferentiableOn ℂ Q (ball (0 : ComplexModel n) r) :=
    fun x hx => (hball x hx).1.differentiableWithinAt
  refine ⟨Q, r, hr, hQr, smooth_squared_dual_norm isOpen_ball hQr, ?_⟩
  intro x hx
  refine ⟨(hball x hx).2.1, (hball x hx).2.2, ?_⟩
  rw [(hball x hx).2.2, norm_smul, mul_pow]

end SGPT.Foundations.Analysis.Pending.ActualHilbertEvaluationPrincipalNormalization
