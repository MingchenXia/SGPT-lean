import SGPT.Foundations.Analysis.Pending.RawQuasiPshTestGenericLelongBound
import SGPT.Foundations.Analysis.Pending.CoordinateNormalOrderPointJetComparison
import SGPT.Foundations.Analysis.Pending.GermOrderProduct
import SGPT.Foundations.Analysis.Pending.HolomorphicZeroSetThin

set_option autoImplicit false

/-! # A genuine factor order before all original tests and multiplier levels

The fixed nonzero holomorphic factor supplies its actual least jet before
every test and level. Actual multiplier membership and point ideal algebra
bound the local divisorial reader; no order or reader certificate is supplied.
Reference: Demailly, CADG, holomorphic germs; Analytic Methods, multiplier
integrability; supplementary local necessary bound for the Xia route.
-/

open Set Filter Metric MeasureTheory
open scoped Topology Manifold ENNReal

namespace SGPT.Foundations.Analysis.Pending.RawQuasiPshProductPointOrderBound

open FirstPass FirstPass.HolomorphicIdealSheaves FirstPass.NonKahlerLocus
  HolomorphicGermReducednessBridge GermIdealOrder IdealWeightPowers

noncomputable section

private theorem frequently_mul_ne_zero {n : ℕ} {f J : ComplexModel n → ℂ}
    (hf : ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ f z)
    (hJ : ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ J z)
    (hfnon : ∃ᶠ z in 𝓝 (0 : ComplexModel n), f z ≠ 0)
    (hJnon : ∃ᶠ z in 𝓝 (0 : ComplexModel n), J z ≠ 0) :
    ∃ᶠ z in 𝓝 (0 : ComplexModel n), f z * J z ≠ 0 := by
  have hfmk : HolGerm.mk f hf ≠ 0 := by
    intro hzero
    have heq := HolGerm.mk_eq_mk_iff.mp (hzero.trans HolGerm.mk_zero.symm)
    exact (hfnon.and_eventually heq).exists.elim fun _ h => h.1 h.2
  have hJmk : HolGerm.mk J hJ ≠ 0 := by
    intro hzero
    have heq := HolGerm.mk_eq_mk_iff.mp (hzero.trans HolGerm.mk_zero.symm)
    exact (hJnon.and_eventually heq).exists.elim fun _ h => h.1 h.2
  have hnon := mul_ne_zero hfmk hJmk
  by_contra hn
  have heq : (fun z => f z * J z) =ᶠ[𝓝 0] fun _ => (0 : ℂ) := by
    filter_upwards [Filter.not_frequently.mp hn] with z hz
    exact not_ne_iff.mp hz
  apply hnon
  exact (HolGerm.mk_mul f J hf hJ).symm.trans
    ((HolGerm.mk_eq_mk_iff.mpr heq).trans HolGerm.mk_zero)

private theorem differentiableAt_coordinate_product {n : ℕ}
    (s : Finset (Fin n)) (L : Fin n → ℕ) (z : ComplexModel n) :
    DifferentiableAt ℂ (fun t : ComplexModel n => ∏ j ∈ s, t j ^ L j) z := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hj ih =>
      simp only [Finset.prod_insert hj]
      exact ((EuclideanSpace.proj (𝕜 := ℂ) j).differentiableAt.pow (L j)).mul ih

/-- The fixed factor supplies its least point order before all tests; each
test supplies its least order before all actual multiplier levels. -/
theorem exists_factor_order_uniform_test_bound {m : ℕ}
    {u : ComplexModel (m + 1) → EReal} (hu : QuasiPlurisubharmonicAt u 0)
    {J : ComplexModel (m + 1) → ℂ}
    (hJ : ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), DifferentiableAt ℂ J z)
    (hJnon : ∃ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), J z ≠ 0) :
    ∃ b : ℕ,
      (∀ k < b, iteratedFDeriv ℂ k J 0 = 0) ∧ iteratedFDeriv ℂ b J 0 ≠ 0 ∧
      ∀ (f : ComplexModel (m + 1) → ℂ),
        (∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), DifferentiableAt ℂ f z) →
        (∃ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), f z ≠ 0) →
        ∃ a : ℕ,
          (∀ k < a, iteratedFDeriv ℂ k f 0 = 0) ∧ iteratedFDeriv ℂ a f 0 ≠ 0 ∧
          ∀ c : ℝ, MultiplierIntegrableAt u c (fun z => f z * J z) 0 volume →
            ∀ R : ℝ, 0 < R →
              (⨅ z ∈ ball (0 : ComplexModel (m + 1)) R ∩ {z | z (Fin.last m) = 0},
                lelongNumber (n := m + 1) u z) ≤
                  ENNReal.ofReal (2 * ((a : ℝ) + (b : ℝ) + 1) / c) := by
  classical
  have hJnot : ¬ ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), J z = 0 := by
    intro hzero
    exact (hJnon.and_eventually hzero).exists.elim fun _ h => h.1 h.2
  obtain ⟨b, hJlow, hJsome, _⟩ :=
    ActualFiniteGeneratorLelongNormalization.exists_finite_generator_lelong_normalization
      (fun _ : Fin 1 => J) (fun _ => hJ) ⟨0, hJnot⟩
  obtain ⟨_, hJb⟩ := hJsome
  refine ⟨b, (fun k hk => hJlow 0 k hk), hJb, ?_⟩
  intro f hf hfnon
  have hfnot : ¬ ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), f z = 0 := by
    intro hzero
    exact (hfnon.and_eventually hzero).exists.elim fun _ h => h.1 h.2
  obtain ⟨a, hflow, hfsome, _⟩ :=
    ActualFiniteGeneratorLelongNormalization.exists_finite_generator_lelong_normalization
      (fun _ : Fin 1 => f) (fun _ => hf) ⟨0, hfnot⟩
  obtain ⟨_, hfa⟩ := hfsome
  have hfhol : HolomorphicAt (m + 1) f 0 :=
    hf.mono fun _ hz => mdifferentiableAt_iff_differentiableAt.mpr hz
  have hJhol : HolomorphicAt (m + 1) J 0 :=
    hJ.mono fun _ hz => mdifferentiableAt_iff_differentiableAt.mpr hz
  have hfnotmem : ¬(idealPow (pointIdeal (m + 1) (0 : ComplexModel (m + 1))) (a + 1)).mem 0 f := by
    intro hmem
    have hlow : ∀ k < a + 1, iteratedFDeriv ℂ k f 0 = 0 := by
      simpa [complexChartAt, chartAt_self_eq] using
        (OrderMultiplicativity.mem_idealPow_pointIdeal_iff_iteratedFDeriv hfhol (a + 1)).mp hmem
    exact hfa (hlow a (Nat.lt_succ_self a))
  have hJnotmem : ¬(idealPow (pointIdeal (m + 1) (0 : ComplexModel (m + 1))) (b + 1)).mem 0 J := by
    intro hmem
    have hlow : ∀ k < b + 1, iteratedFDeriv ℂ k J 0 = 0 := by
      simpa [complexChartAt, chartAt_self_eq] using
        (OrderMultiplicativity.mem_idealPow_pointIdeal_iff_iteratedFDeriv hJhol (b + 1)).mp hmem
    exact hJb (hlow b (Nat.lt_succ_self b))
  have hprodnotmem := GermOrderProduct.mul_notMem_idealPow hfhol hJhol hfnotmem hJnotmem
  have hprodnon := frequently_mul_ne_zero hf hJ hfnon hJnon
  refine ⟨a, (fun k hk => hflow 0 k hk), hfa, ?_⟩
  intro c hint
  have hc : 0 < c := hint.1
  obtain ⟨L, H, hH, _, heq, _, hbound⟩ :=
    RawQuasiPshTestGenericLelongBound.exists_orders_and_generic_bound hu hint hprodnon
  let j : Fin (m + 1) := Fin.last m
  let K : ComplexModel (m + 1) → ℂ :=
    fun z => H z * ∏ k ∈ (Finset.univ : Finset (Fin (m + 1))).erase j, z k ^ L k
  have hK : ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), DifferentiableAt ℂ K z := by
    filter_upwards [hH] with z hz
    exact hz.mul (differentiableAt_coordinate_product _ L z)
  have heqK : (fun z => f z * J z) =ᶠ[𝓝 0] fun z => K z * z j ^ L j := by
    filter_upwards [heq] with z hz
    rw [hz]
    dsimp only [K]
    rw [mul_assoc, Finset.prod_erase_mul _ _ (Finset.mem_univ j)]
  have hnormal : L j ≤ a + b := by
    by_contra hnot
    have hab : a + b < L j := lt_of_not_ge hnot
    have hjet := CoordinateNormalOrderPointJetComparison.iteratedFDeriv_eq_zero_of_coordinate_factorization
      j hK heqK
    have hlow : ∀ k < a + b + 1, iteratedFDeriv ℂ k (fun z => f z * J z) 0 = 0 :=
      fun k hk => hjet k (by omega)
    have hmem : (idealPow (pointIdeal (m + 1) (0 : ComplexModel (m + 1)))
        (a + b + 1)).mem 0 (fun z => f z * J z) := by
      apply (OrderMultiplicativity.mem_idealPow_pointIdeal_iff_iteratedFDeriv
        (hfhol.mul hJhol) (a + b + 1)).mpr
      simpa [complexChartAt, chartAt_self_eq] using hlow
    exact hprodnotmem hmem
  intro R hR
  refine (hbound R hR).trans (ENNReal.ofReal_le_ofReal ?_)
  apply div_le_div_of_nonneg_right _ hc.le
  have hreal : (L j : ℝ) ≤ (a : ℝ) + (b : ℝ) := by exact_mod_cast hnormal
  change 2 * ((L j : ℝ) + 1) ≤ 2 * ((a : ℝ) + (b : ℝ) + 1)
  linarith

end
end SGPT.Foundations.Analysis.Pending.RawQuasiPshProductPointOrderBound
