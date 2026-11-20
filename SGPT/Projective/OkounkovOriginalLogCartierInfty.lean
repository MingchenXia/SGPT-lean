import SGPT.PSH.CanonicalGrowthManifold
import SGPT.Foundations.Analysis.Pending.HolomorphicBoundedQuotient

/-! Actual local logarithmic Cartier infinity ideal = actual holomorphic divisibility.
Blueprint: okounkov-original-log-cartier-infty.tex. No resolution construction. -/
set_option autoImplicit false
set_option maxHeartbeats 2200000
noncomputable section
namespace SGPT.Okounkov.OriginalLogCartier
open Set Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.Pending.HolomorphicBoundedQuotient
open SGPT.PSH
open scoped Topology
variable {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

theorem mem_inftyIdeal_local_log_iff_holomorphic_quotient
    {U : Set M} (hU : IsOpen U) {x : M} (hx : x∈U) {g : M → ℂ}
    (hg : HolomorphicAt n g x)
    (hgne : ∀ W : Set M,IsOpen W → W⊆U → W.Nonempty → ∃y∈W,g y≠0)
    {u : M → EReal} {b : M → ℝ} (hb : BoundedRealGermAt b x)
    (heq : u =ᶠ[𝓝 x] fun y => logNormSq (g y)+(b y:EReal)) (f : M → ℂ) :
    (inftyIdeal (n:=n) u).mem x f ↔
      ∃ a : M → ℂ,HolomorphicAt n a x ∧ f =ᶠ[𝓝 x] fun y => a y*g y := by
  have hG : generatorLog (fun _ : Fin 1 => g)=(fun y => logNormSq (g y)) := by
    funext y
    rw [generatorLog_eq_log_sum]
    simp [logNormSq]
  have hread : u =ᶠ[𝓝 x] fun y => (((1:ℚ):ℝ):EReal)*generatorLog (fun _ : Fin 1 => g) y+(b y:EReal) := by
    simpa only [Rat.cast_one,EReal.coe_one,one_mul,hG] using heq
  have criterion (h : M → ℂ) :
      (inftyIdeal (n:=n) u).mem x h ↔ HolomorphicAt n h x ∧
        ∃ C : ℝ,0≤C ∧ ∀ᶠ y in 𝓝 x,‖h y‖≤C*‖g y‖ := by
    have hh := mem_canonicalGrowthManifoldIdeal_iff_norm_bound (n:=n) (c:=1) (by norm_num) hb hread (h:=h)
    simpa [canonicalGrowthManifoldIdeal,Fin.sum_univ_one] using hh
  constructor
  · intro hf
    obtain ⟨hfh,C,_,hbound⟩ := (criterion f).mp hf
    exact exists_holomorphicAt_eventuallyEq_mul hU hx hfh hg hgne ⟨C,hbound⟩
  · rintro ⟨a,ha,haf⟩
    have hgmem : (inftyIdeal (n:=n) u).mem x g :=
      (criterion g).mpr ⟨hg,1,zero_le_one,Eventually.of_forall fun y => by simp⟩
    exact (inftyIdeal_mem_congr haf).mpr (inftyIdeal_mul_mem ha hgmem)
end SGPT.Okounkov.OriginalLogCartier
