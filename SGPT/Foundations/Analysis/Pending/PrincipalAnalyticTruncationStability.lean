import SGPT.Foundations.Analysis.Pending.StrictMonomialTruncationAllDimensions
import SGPT.Foundations.Analysis.Pending.PrincipalGeneratorLogPointwiseNormalForm
import SGPT.Foundations.Analysis.Pending.AnalyticSingularities

set_option autoImplicit false

/-! # Actual strict truncation stability for the whole principal analytic family -/

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.PrincipalAnalyticTruncationStability

open FirstPass HolomorphicGermReducednessBridge

noncomputable section

private theorem near_product {n : ℕ} {ι : Type*} (S : Finset ι)
    (f : ι → ComplexModel n → ℂ)
    (hf : ∀ i, ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ (f i) z) :
    ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ (fun z => ∏ i ∈ S, f i z) z := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty] using eventually_differentiableAt_const (E := ComplexModel n) 1
  | @insert i S hi ih =>
    simpa only [Finset.prod_insert hi] using eventually_differentiableAt_mul (hf i) ih

private theorem mk_product {n : ℕ} {ι : Type*} (S : Finset ι)
    (f : ι → ComplexModel n → ℂ)
    (hf : ∀ i, ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ (f i) z) :
    HolGerm.mk (fun z => ∏ i ∈ S, f i z) (near_product S f hf) =
      ∏ i ∈ S, HolGerm.mk (f i) (hf i) := by
  apply Subtype.ext
  rw [HolGerm.coe_mk, SubmonoidClass.coe_finsetProd]
  simp only [HolGerm.coe_mk]
  have h := map_prod
    (Germ.coeRingHom (𝓝 (0 : ComplexModel n)) : (ComplexModel n → ℂ) →+*
      Germ (𝓝 (0 : ComplexModel n)) ℂ) f S
  simp only [Germ.coe_coeRingHom] at h
  rw [← h, Finset.prod_fn]

private theorem mul_sum_nonneg_real {ι : Type*} (S : Finset ι) (f : ι → EReal)
    {c : ℝ} (hc : 0 ≤ c) :
    (c : EReal) * (∑ i ∈ S, f i) = ∑ i ∈ S, (c : EReal) * f i := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi,
      EReal.left_distrib_of_nonneg_of_ne_top (EReal.coe_nonneg.mpr hc) (EReal.coe_ne_top c), ih]

/-- Source integrals for all actual principal truncations return the original
whole-family integral; all monomial orders, units and comparisons are internal. -/
theorem multiplierIntegrableAt_of_all_principal_truncations {n s : ℕ}
    (G : Fin s → ComplexModel n → ℂ)
    (hG : ∀ i, ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ (G i) z)
    {H : ComplexModel n → ℂ}
    (hH : ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ H z)
    (hHnon : ∃ᶠ z in 𝓝 (0 : ComplexModel n), H z ≠ 0)
    (hspan : Ideal.span (Set.range fun i => HolGerm.mk (G i) (hG i)) =
      Ideal.span {HolGerm.mk H hH})
    (hzero : ∀ᶠ z in 𝓝 (0 : ComplexModel n), H z = 0 → ∃ j : Fin n, z j = 0)
    {q q' : ℝ} (hq' : 0 < q') (hqq' : q' < q) {F : ComplexModel n → ℂ}
    (htrunc : ∀ N : ℕ, ∃ (r : ℕ) (Q : Fin r → ComplexModel n → ℂ)
      (hQ : ∀ i, ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ (Q i) z),
      (∀ i, HolGerm.mk (Q i) (hQ i) ∈
        Ideal.span (Set.range fun j => HolGerm.mk (G j) (hG j)) ⊔
        (Ideal.span (Set.range fun j : Fin n => HolGerm.mk
          (fun z : ComplexModel n => z j) (eventually_differentiableAt_coordinate j))) ^ N) ∧
      MultiplierIntegrableAt (generatorLog Q) q F 0 volume) :
    MultiplierIntegrableAt (generatorLog G) q' F 0 volume := by
  classical
  obtain ⟨a, K, hK, hK0, hHK⟩ :=
    HolomorphicCoordinateFactorization.exists_unit_mul_coordinate_monomial_of_zero_locus hH hzero
  let M : ComplexModel n → ℂ := fun z => ∏ j : Fin n, z j ^ a j
  have hpowers (j : Fin n) : ∀ᶠ z in 𝓝 (0 : ComplexModel n),
      DifferentiableAt ℂ (fun z : ComplexModel n => z j ^ a j) z :=
    eventually_differentiableAt_pow (eventually_differentiableAt_coordinate j) (a j)
  have hM : ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ M z :=
    near_product Finset.univ (fun (j : Fin n) (z : ComplexModel n) => z j ^ a j) hpowers
  have hmkM : HolGerm.mk M hM = ∏ j : Fin n,
      HolGerm.mk (fun z : ComplexModel n => z j) (eventually_differentiableAt_coordinate j) ^ a j := by
    calc
      _ = ∏ j : Fin n, HolGerm.mk (fun z : ComplexModel n => z j ^ a j) (hpowers j) :=
        mk_product Finset.univ _ hpowers
      _ = _ := by
        apply Finset.prod_congr rfl
        intro j _
        exact HolGerm.mk_pow _ _ _
  have hKunit : IsUnit (HolGerm.mk K hK) :=
    (HolGerm.isUnit_iff_eval_ne_zero _).mpr (by simpa only [HolGerm.eval_mk] using hK0)
  have hHm : HolGerm.mk H hH = HolGerm.mk K hK * HolGerm.mk M hM := by
    calc
      _ = HolGerm.mk (fun z => K z * M z) (eventually_differentiableAt_mul hK hM) :=
        HolGerm.mk_eq_mk_iff.mpr hHK
      _ = _ := HolGerm.mk_mul K M hK hM
  have hspanM : Ideal.span (Set.range fun i => HolGerm.mk (G i) (hG i)) =
      Ideal.span {HolGerm.mk M hM} := by
    rw [hspan, hHm]
    exact Ideal.span_singleton_mul_left_unit hKunit _
  have htruncM : ∀ N : ℕ, ∃ (r : ℕ) (Q : Fin r → ComplexModel n → ℂ)
      (hQ : ∀ i, ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ (Q i) z),
      (∀ i, HolGerm.mk (Q i) (hQ i) ∈
        Ideal.span {∏ j : Fin n, HolGerm.mk (fun z : ComplexModel n => z j)
          (eventually_differentiableAt_coordinate j) ^ a j} ⊔
        (Ideal.span (Set.range fun j : Fin n => HolGerm.mk
          (fun z : ComplexModel n => z j) (eventually_differentiableAt_coordinate j))) ^ N) ∧
      MultiplierIntegrableAt (generatorLog Q) q F 0 volume := by
    intro N
    obtain ⟨r, Q, hQ, hmem, hint⟩ := htrunc N
    refine ⟨r, Q, hQ, ?_, hint⟩
    intro i
    have hi := hmem i
    rwa [hspanM, hmkM] at hi
  let ψ : ComplexModel n → EReal := fun z =>
    ∑ j : Fin n, ((2 * (a j : ℝ) : ℝ) : EReal) * ENNReal.log (ENNReal.ofReal ‖z j‖)
  have hψint : MultiplierIntegrableAt ψ q' F 0 volume :=
    StrictMonomialTruncationAllDimensions.multiplierIntegrableAt_of_all_monomial_truncations
      a hq' hqq' htruncM
  have hMnon : ∃ᶠ z in 𝓝 (0 : ComplexModel n), M z ≠ 0 := by
    by_contra hn
    have hMz : ∀ᶠ z in 𝓝 (0 : ComplexModel n), M z = 0 := by
      filter_upwards [Filter.not_frequently.mp hn] with z hz
      exact not_ne_iff.mp hz
    have hHz : ∀ᶠ z in 𝓝 (0 : ComplexModel n), H z = 0 := by
      filter_upwards [hHK, hMz] with z hz hzm
      simpa only [M, hzm, mul_zero] using hz
    obtain ⟨z, hzn, hzz⟩ := (hHnon.and_eventually hHz).exists
    exact hzn hzz
  obtain ⟨R, hR, hGR, i, hi⟩ :=
    PrincipalHolomorphicGeneratorQuotients.exists_holomorphic_quotients_of_principal_span
      G hG hM hMnon hspanM
  have hRc : ∀ᶠ z in 𝓝 (0 : ComplexModel n), ContinuousAt (generatorNormSq R) z := by
    filter_upwards [eventually_all.mpr hR] with z hz
    have hcont (j : Fin s) : ContinuousAt (R j) z := (hz j).continuousAt
    change ContinuousAt (fun w => ∑ j : Fin s, ‖R j w‖ ^ 2) z
    fun_prop
  have hRp0 : 0 < generatorNormSq R 0 :=
    Finset.sum_pos' (fun j _ => sq_nonneg ‖R j 0‖)
      ⟨i, Finset.mem_univ i, pow_pos (norm_pos_iff.mpr hi) 2⟩
  have hRp : ∀ᶠ z in 𝓝 (0 : ComplexModel n), 0 < generatorNormSq R z :=
    hRc.self_of_nhds.eventually (lt_mem_nhds hRp0)
  let η : ComplexModel n → ℝ := fun z => Real.log (generatorNormSq R z)
  have hηc : ContinuousAt η 0 := hRc.self_of_nhds.log hRp0.ne'
  have hηlower : ∀ᶠ z in 𝓝 (0 : ComplexModel n), η 0 - 1 < η z :=
    hηc.eventually (lt_mem_nhds (by linarith : η 0 - 1 < η 0))
  have hgen : ∀ᶠ z in 𝓝 (0 : ComplexModel n), generatorLog G z = ψ z + (η z : EReal) := by
    filter_upwards [eventually_all.mpr hGR, hRp] with z hz hp
    have hfamily : generatorLog G z = generatorLog (fun j w => M w * R j w) z := by
      simp only [generatorLog_eq_log_sum]
      apply congrArg (fun t : ℝ => ENNReal.log (ENNReal.ofReal t))
      exact Finset.sum_congr rfl fun j _ => congrArg (fun t : ℂ => ‖t‖ ^ 2) (hz j)
    have hlogM : ENNReal.log (ENNReal.ofReal ‖M z‖) =
        ∑ j : Fin n, ((a j : ℝ) : EReal) * ENNReal.log (ENNReal.ofReal ‖z j‖) := by
      have h := PrincipalGeneratorLogPointwiseNormalForm.log_norm_unit_monomial_eq a (1 : ℂ) z
      simpa only [one_mul, norm_one, ENNReal.ofReal_one, ENNReal.log_one, zero_add, M] using h
    rw [hfamily, PrincipalGeneratorLogNormNormalForm.generatorLog_common_factor M R z hp,
      hlogM, mul_sum_nonneg_real _ _ (by norm_num : (0 : ℝ) ≤ 2)]
    simp_rw [← mul_assoc, ← EReal.coe_mul]
    rfl
  have hcomp : MoreSingularAt ψ (generatorLog G) (0 : ComplexModel n) := by
    refine ⟨1 - η 0, ?_⟩
    filter_upwards [hgen, hηlower] with z hz hl
    rw [hz, add_assoc, ← EReal.coe_add]
    have hpos : (0 : EReal) ≤ ((η z + (1 - η 0) : ℝ) : EReal) :=
      EReal.coe_nonneg.mpr (by linarith)
    simpa only [zero_add, add_comm] using add_le_add_left hpos (ψ z)
  have hGpsh : QuasiPlurisubharmonicAt (generatorLog G) (0 : ComplexModel n) := by
    have hall : ∀ᶠ z in 𝓝 (0 : ComplexModel n), ∀ i, DifferentiableAt ℂ (G i) z :=
      Filter.eventually_all.mpr hG
    obtain ⟨O, hsub, hO, h0⟩ := _root_.mem_nhds_iff.mp hall
    have hgens : HolomorphicGeneratorsAt G (0 : ComplexModel n) :=
      ⟨O, hO, h0, fun i z hz => (hsub hz i).differentiableWithinAt⟩
    have hpsh := plurisubharmonicAt_scaled_generatorLog hgens (by norm_num : (0 : ℝ) < 1)
    simpa only [EReal.coe_one, one_mul] using hpsh.quasiPlurisubharmonicAt
  exact multiplierIntegrableAt_of_moreSingularAt hGpsh hcomp hψint

end
end SGPT.Foundations.Analysis.Pending.PrincipalAnalyticTruncationStability
