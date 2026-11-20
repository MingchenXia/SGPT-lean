import SGPT.PSH.CartierGeneratorUnits
import SGPT.Foundations.Analysis.FirstPass.AnalyticSingularities

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH

open Set Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending
open InvertibleIdealQuotient RegularLocusComponent AnalyticGermDecomposition
open scoped Topology Manifold ContDiff ENNReal

private theorem logNormSq_mul (v w : ℂ) :
    logNormSq (v * w) = logNormSq v + logNormSq w := by
  rw [logNormSq, norm_mul, mul_pow, ENNReal.ofReal_mul (sq_nonneg ‖v‖), ENNReal.log_mul_add]
  rfl

private theorem logNormSq_pow (v : ℂ) (a : ℕ) :
    logNormSq (v ^ a) = ((a : ℝ) : EReal) * logNormSq v := by
  rw [logNormSq, norm_pow, ← pow_mul, Nat.mul_comm a 2, pow_mul,
    ENNReal.ofReal_pow (sq_nonneg ‖v‖) a, ENNReal.log_pow, EReal.coe_natCast]
  rfl

private theorem logNormSq_finset_prod {ι : Type*} (s : Finset ι) (r : ι → ℂ) :
    logNormSq (∏ i ∈ s, r i) = ∑ i ∈ s, logNormSq (r i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [logNormSq]
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, logNormSq_mul, ih]

/-- The literal geometric product's extended squared-norm logarithm keeps
EVERY zero factor as bottom, including empty products and zero exponents. -/
theorem logNormSq_geometric_product {ι : Type*} [Fintype ι]
    (r : ι → ℂ) (a : ι → ℕ) (U : ℂ) :
    logNormSq ((∏ i, r i ^ a i) * U) =
      (∑ i, ((a i : ℝ) : EReal) * logNormSq (r i)) + logNormSq U := by
  rw [logNormSq_mul, logNormSq_finset_prod]
  congr 1
  exact Finset.sum_congr rfl fun i _ => logNormSq_pow (r i) (a i)

private theorem coe_mul_finset_sum {ι : Type*} (s : Finset ι) (f : ι → EReal)
    {c : ℝ} (hc : 0 ≤ c) :
    (c : EReal) * (∑ i ∈ s, f i) = ∑ i ∈ s, (c : EReal) * f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi,
      EReal.left_distrib_of_nonneg_of_ne_top (EReal.coe_nonneg.mpr hc) (EReal.coe_ne_top c), ih]

universe u
variable {m : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

/-- An ORIGINAL defining equation and arbitrary locally bounded remainder
produce the SAME actual geometric primes, positive rational coefficients and
an actual bounded corrected remainder, including every negative-infinite pole. -/
theorem exists_cartier_geometric_log_remainder
    (D : EffectiveDivisor (m + 1) M) (x : M) (g : M → ℂ)
    (hg : HolomorphicAt (m + 1) g x)
    (hgen : ∀ a, D.ideal.mem x a ↔ IsInSpanAt (n := m + 1) (· = g) x a)
    (c : ℚ) (hc : 0 < c) (u : ComplexModel (m + 1) → EReal)
    (R : ComplexModel (m + 1) → ℝ) (hR : BoundedRealGermAt R 0)
    (hu : u =ᶠ[𝓝 0] fun z => ((c : ℝ) : EReal) *
      logNormSq (g ((complexChartAt (n := m + 1) x).val.symm
        (z + (complexChartAt (n := m + 1) x).val x))) + (R z : EReal)) :
    ∃ S : Finset (GlobalComponents.globalComponents (n := m + 1) D.support),
      ∃ (r : GlobalComponents.globalComponents (n := m + 1) D.support →
          ComplexModel (m + 1) → ℂ)
        (hr : ∀ B, ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (r B) z),
        (∀ B, HolGerm.mk (r B) (hr B) ≠ 0 ∧ Squarefree (HolGerm.mk (r B) (hr B)) ∧
          vanishingIdeal (AnalyticDescendingChain.chartGerm (n := m + 1)
            (cartierPrimeComponent D B).carrier x) = Ideal.span {HolGerm.mk (r B) (hr B)} ∧
          AnalyticDescendingChain.chartGerm (n := m + 1)
            (cartierPrimeComponent D B).carrier x =ᶠ[𝓝 0] {z | r B z = 0}) ∧
        (∀ B ∈ S, 0 < c * (regularComponentOrder D D.support B : ℚ)) ∧
        (∃ T ∈ 𝓝 x, ∀ y ∈ T, y ∈ D.support ↔
          ∃ B ∈ S, y ∈ (cartierPrimeComponent D B).carrier) ∧
        ∃ b : ComplexModel (m + 1) → ℝ, BoundedRealGermAt b 0 ∧
          u =ᶠ[𝓝 0] fun z => (∑ B : {B // B ∈ S},
            (((c * (regularComponentOrder D D.support B.val : ℚ) : ℚ) : ℝ) : EReal) *
              logNormSq (r B.val z)) + (b z : EReal) := by
  classical
  obtain ⟨S, r, hr, hRdata, hpos, hcover, U, hU, hU0, hUnear, hfactor⟩ :=
    exists_geometric_factorization_of_cartier_stalk_generator D x g hg hgen
  have hcR : 0 < (c : ℝ) := by exact_mod_cast hc
  have hlogcont : ContinuousAt (fun z => Real.log (‖U z‖ ^ 2)) 0 :=
    (hU.self_of_nhds.continuousAt.norm.pow 2).log
      (pow_ne_zero 2 (norm_ne_zero_iff.mpr hU0))
  let b : ComplexModel (m + 1) → ℝ := fun z => R z + (c : ℝ) * Real.log (‖U z‖ ^ 2)
  have hb : BoundedRealGermAt b 0 :=
    hR.add (boundedRealGermAt_of_continuousAt (continuousAt_const.mul hlogcont))
  refine ⟨S, r, hr, hRdata, (fun B hBS => mul_pos hc (by exact_mod_cast hpos B hBS)), hcover,
    b, hb, ?_⟩
  have hcoef (B : {B // B ∈ S}) : ((c : ℝ) : EReal) *
      ((regularComponentOrder D D.support B.val : ℝ) : EReal) =
        (((c * (regularComponentOrder D D.support B.val : ℚ) : ℚ) : ℝ) : EReal) := by
    rw [← EReal.coe_mul]
    congr 1
    norm_cast
  filter_upwards [hu, hfactor, hUnear] with z hzu hzf hzU
  rw [hzu, hzf, logNormSq_geometric_product, logNormSq_of_ne_zero hzU,
    EReal.left_distrib_of_nonneg_of_ne_top (EReal.coe_nonneg.mpr hcR.le) (EReal.coe_ne_top (c : ℝ)),
    coe_mul_finset_sum _ _ hcR.le]
  have hsum : (∑ B : {B // B ∈ S}, ((c : ℝ) : EReal) *
      (((regularComponentOrder D D.support B.val : ℝ) : EReal) * logNormSq (r B.val z))) =
        ∑ B : {B // B ∈ S},
          (((c * (regularComponentOrder D D.support B.val : ℚ) : ℚ) : ℝ) : EReal) *
            logNormSq (r B.val z) := by
    apply Finset.sum_congr rfl
    intro B _
    rw [← mul_assoc, hcoef B]
  rw [hsum]
  dsimp only [b]
  rw [EReal.coe_add, EReal.coe_mul]
  ac_rfl

end SGPT.PSH
