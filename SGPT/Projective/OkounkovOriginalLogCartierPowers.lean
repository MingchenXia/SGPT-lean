import SGPT.Projective.OkounkovOriginalLogCartierInfty

/-! Every genuine original logarithmic degree has the actual holomorphic power quotient.
Blueprint: okounkov-original-log-cartier-powers.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 2200000
noncomputable section
namespace SGPT.Okounkov.OriginalLogCartier
open Set Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.PSH
open scoped Topology ENNReal
variable {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

private theorem actual_logNormSq_nat_pow (z : ℂ) (k : ℕ) :
    logNormSq (z^k)=(k:EReal)*logNormSq z := by
  rw [logNormSq,norm_pow,←pow_mul,Nat.mul_comm k 2,pow_mul,
    ENNReal.ofReal_pow (sq_nonneg ‖z‖) k,ENNReal.log_pow]
  rfl

theorem mem_inftyIdeal_nat_log_iff_holomorphic_power_quotient
    {U : Set M} (hU : IsOpen U) {x : M} (hx : x∈U) {g : M → ℂ}
    (hg : HolomorphicAt n g x)
    (hgne : ∀ W : Set M,IsOpen W → W⊆U → W.Nonempty → ∃y∈W,g y≠0)
    {u : M → EReal} {b : M → ℝ} (hb : BoundedRealGermAt b x)
    (heq : u =ᶠ[𝓝 x] fun y => logNormSq (g y)+(b y:EReal)) (k : ℕ) (f : M → ℂ) :
    (inftyIdeal (n:=n) (fun y => (k:EReal)*u y)).mem x f ↔
      ∃ a : M → ℂ,HolomorphicAt n a x ∧ f =ᶠ[𝓝 x] fun y => a y*g y^k := by
  have hkR : (0:ℝ)≤k := Nat.cast_nonneg k
  have hcoef : ((k:ℝ):EReal)=(k:EReal) := by simp
  have hb' : BoundedRealGermAt (fun y => (k:ℝ)*b y) x := by
    obtain ⟨C,hC,hbound⟩ := hb
    refine ⟨(k:ℝ)*C,mul_nonneg hkR hC,?_⟩
    filter_upwards [hbound] with y hy
    rw [abs_mul,abs_of_nonneg hkR]
    exact mul_le_mul_of_nonneg_left hy hkR
  have hread : (fun y => (k:EReal)*u y) =ᶠ[𝓝 x]
      fun y => logNormSq (g y^k)+(((k:ℝ)*b y):EReal) := by
    filter_upwards [heq] with y hy
    rw [hy,←hcoef,EReal.left_distrib_of_nonneg_of_ne_top
      (EReal.coe_nonneg.mpr hkR) (EReal.coe_ne_top (k:ℝ)),←EReal.coe_mul,hcoef,
      actual_logNormSq_nat_pow]
  have hgp : HolomorphicAt n (fun y => g y^k) x := by
    filter_upwards [hg] with y hy
    exact hy.pow k
  apply mem_inftyIdeal_local_log_iff_holomorphic_quotient hU hx hgp ?_ hb' hread f
  intro W hW hWU hWne
  obtain ⟨y,hy,hgy⟩ := hgne W hW hWU hWne
  exact ⟨y,hy,pow_ne_zero k hgy⟩
end SGPT.Okounkov.OriginalLogCartier
