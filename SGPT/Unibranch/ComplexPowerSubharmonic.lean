import SGPT.Unibranch.ComplexCompactMaximum
import SGPT.Unibranch.ComplexPowerSubmean
import SGPT.Foundations.Analysis.FirstPass.PshDiscLocalGlobal
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! Genuine full scalar finite-power descent, with actual compact preimages.
Blueprint: complex-power-subharmonic.tex. -/
set_option autoImplicit false
noncomputable section
open Set Filter Metric MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
namespace SGPT.Unibranch.RamifiedPower

/-- Actual holomorphic pullback of a real harmonic germ, also at critical points. -/
theorem harmonicAt_comp_analyticAt {h : ℂ → ℝ} {F : ℂ → ℂ} {z : ℂ}
    (hh : HarmonicAt h (F z)) (hF : AnalyticAt ℂ F z) : HarmonicAt (h ∘ F) z := by
  obtain ⟨r,hr,hball⟩ := isOpen_iff.mp (isOpen_setOfPred_harmonicAt (f := h)) (F z) hh
  obtain ⟨g,hg,hgre⟩ := HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq
    (fun w hw => hball hw)
  have hcenter : F z ∈ ball (F z) r := mem_ball_self hr
  have hgf : AnalyticAt ℂ (g ∘ F) z := (hg _ hcenter).comp hF
  have hnear : ∀ᶠ w in 𝓝 z,F w ∈ ball (F z) r :=
    hF.continuousAt.eventually (isOpen_ball.mem_nhds hcenter)
  have heq : (fun w => ((g ∘ F) w).re) =ᶠ[𝓝 z] h ∘ F := by
    filter_upwards [hnear] with w hw
    exact hgre hw
  exact (harmonicAt_congr_nhds heq).mp hgf.harmonicAt_re

private theorem norm_lt_of_pow_mem {k : ℕ} (_hk : 0 < k) {R : ℝ} (hR : 0 < R)
    {z : ℂ} (hz : z^k ∈ ball (0 : ℂ) (R^k)) : z ∈ ball (0 : ℂ) R := by
  rw [mem_ball_zero_iff] at hz ⊢
  rw [norm_pow] at hz
  by_contra hnot
  exact (not_lt_of_ge (pow_le_pow_left₀ hR.le (le_of_not_gt hnot) k)) hz

private theorem pow_mem_ball {k : ℕ} (hk : 0 < k) {R : ℝ}
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) R) : z^k ∈ ball (0 : ℂ) (R^k) := by
  rw [mem_ball_zero_iff] at hz ⊢
  rw [norm_pow]
  exact pow_lt_pow_left₀ hz (norm_nonneg _) (Nat.ne_of_gt hk)

/-- Genuine harmonic comparison on EVERY target disk under the actual
finite power, via an actual compact preimage rather than a desired SH certificate. -/
theorem le_harmonic_add_of_comp_pow {u : ℂ → EReal} (k : ℕ) (hk : 0 < k)
    {R : ℝ} (hR : 0 < R)
    (hcomp : PlurisubharmonicOn (fun z => u (z^k)) (ball 0 R))
    {a : ℂ} {r C : ℝ} (_hr : 0 < r)
    (hD : closedBall a r ⊆ ball (0 : ℂ) (R^k)) {h : ℂ → ℝ}
    (hh : HarmonicOnNhd h univ)
    (hbound : ∀ z ∈ sphere a r,u z ≤ ((h z + C : ℝ) : EReal)) :
    ∀ z ∈ closedBall a r,u z ≤ ((h z + C : ℝ) : EReal) := by
  let K : Set ℂ := (fun z : ℂ => z^k) ⁻¹' closedBall a r
  have hKclosed : IsClosed K := isClosed_closedBall.preimage (continuous_id.pow k)
  have hKS : K ⊆ ball (0 : ℂ) R := fun z hz => norm_lt_of_pow_mem hk hR (hD hz)
  have hK : IsCompact K := (isCompact_closedBall (0 : ℂ) R).of_isClosed_subset hKclosed
    (hKS.trans ball_subset_closedBall)
  have hhpow : HarmonicOnNhd (fun z : ℂ => h (z^k)) univ := by
    intro z _hz
    exact harmonicAt_comp_analyticAt (hh _ trivial) (analyticAt_id.pow k)
  have hsub := hcomp.sub_harmonic (hhpow.mono (subset_univ _))
  have hfront : ∀ z ∈ frontier K,u (z^k)-(h (z^k) : EReal) ≤ (C : EReal) := by
    intro z hz
    have hzK : z ∈ K := hKclosed.closure_eq ▸ frontier_subset_closure hz
    have hzs : z^k ∈ sphere a r := by
      have hle : dist (z^k) a ≤ r := mem_closedBall.mp hzK
      by_contra hnot
      have hlt : dist (z^k) a < r := lt_of_le_of_ne hle (fun heq => hnot (mem_sphere.mpr heq))
      have hzint : z ∈ interior K := interior_maximal
        (preimage_mono ball_subset_closedBall) (isOpen_ball.preimage (continuous_id.pow k)) hlt
      exact (mem_frontier_iff_notMem_interior hzK).mp hz hzint
    have hb := hbound _ hzs
    calc
      u (z^k)-(h (z^k) : EReal) ≤ ((h (z^k)+C : ℝ) : EReal)-(h (z^k) : EReal) :=
        EReal.sub_le_sub hb le_rfl
      _ = (C : EReal) := by rw [← EReal.coe_sub];congr 1;ring
  have hmax := SingularMaximum.le_const_on_compact_of_le_on_frontier hsub hK hKS hfront
  intro z hz
  obtain ⟨w,hw⟩ := IsAlgClosed.exists_pow_nat_eq z hk
  have hwm : w ∈ K := by change w^k ∈ closedBall a r;rw [hw];exact hz
  have h := hmax w hwm
  rw [hw] at h
  have h' := (EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot _))
    (Or.inl (EReal.coe_ne_top _))).mp h
  simpa only [← EReal.coe_add,add_comm] using h'

/-- Full ORIGINAL one-variable subharmonic descent through the actual finite
power. Upper semicontinuity is the already-produced target regularity;
all never-top/nontrivial/submean fields are proved, at EVERY target center. -/
theorem subharmonicOn_of_comp_pow {u : ℂ → EReal} (k : ℕ) (hk : 0 < k)
    {R : ℝ} (hR : 0 < R)
    (husc : UpperSemicontinuousOn u (ball (0 : ℂ) (R^k)))
    (hcomp : SGPT.PSH.SubharmonicOn (fun z => u (z^k)) (ball (0 : ℂ) R)) :
    SGPT.PSH.SubharmonicOn u (ball (0 : ℂ) (R^k)) := by
  have huP : PlurisubharmonicOn (fun z => u (z^k)) (ball (0 : ℂ) R) :=
    hcomp.discPshOn.plurisubharmonicOn isOpen_ball
  have htop : ∀ z ∈ ball (0 : ℂ) (R^k),u z ≠ ⊤ := by
    intro z hz
    obtain ⟨w,hw⟩ := IsAlgClosed.exists_pow_nat_eq z hk
    have hwS : w ∈ ball (0 : ℂ) R := norm_lt_of_pow_mem hk hR (by rw [hw];exact hz)
    have h := hcomp.ne_top w hwS
    rwa [hw] at h
  refine ⟨htop,husc,?_,?_⟩
  · obtain ⟨w,hw,hfin⟩ := hcomp.nontrivial
    exact ⟨w^k,pow_mem_ball hk hw,hfin⟩
  · intro a r hr hD C hC
    let K : Set ℂ := sphere a r
    have hK : IsCompact K := isCompact_sphere a r
    have hKne : K.Nonempty := by
      refine ⟨a+(r : ℂ),?_⟩
      simp [K,abs_of_pos hr]
    have hKΩ : K ⊆ ball (0 : ℂ) (R^k) := sphere_subset_closedBall.trans hD
    have huK := husc.mono hKΩ
    have htopK : ∀ z ∈ K,u z ≠ ⊤ := fun z hz => htop z (hKΩ hz)
    have hCK : ∀ z ∈ K,u z ≤ (C : EReal) := fun z hz => hC z (sphere_subset_closedBall hz)
    let g : ℕ → ℂ → ℝ := fun n => uscSupConvolution K u C n
    have hg : ∀ n,Continuous (g n) := fun n => continuous_uscSupConvolution hKne htopK hCK n
    have hgu : ∀ n z,z ∈ K → u z ≤ (g n z : EReal) :=
      fun n z hz => le_coe_uscSupConvolution hKne htopK hCK n hz
    have hgC : ∀ n z,g n z ≤ C := fun n z => uscSupConvolution_le hKne htopK hCK n z
    have hganti : ∀ z,Antitone fun n => g n z :=
      fun z => uscSupConvolution_antitone hKne htopK hCK z
    have hginf : ∀ z,z ∈ K → (⨅ n : ℕ,(g n z : EReal)) = u z :=
      fun z hz => iInf_coe_uscSupConvolution hKne huK htopK hCK hz
    have hcenter : ∀ n,u a ≤ ((Real.circleAverage (g n) a r : ℝ) : EReal) := by
      intro n
      by_cases habot : u a = ⊥
      · simp [habot]
      have hatop := htop a (hD (mem_closedBall_self hr.le))
      rw [← EReal.coe_toReal hatop habot,EReal.coe_le_coe_iff]
      apply le_of_forall_pos_le_add
      intro δ hδ
      let ε : ℝ := δ/2
      have hε : 0 < ε := div_pos hδ (by norm_num)
      obtain ⟨h,hh,happ⟩ := exists_global_harmonic_uniformApproxOn_sphere a hr
        (hg n).continuousOn hε
      have hboundary : ∀ z ∈ sphere a r,u z ≤ ((h z+ε : ℝ) : EReal) := by
        intro z hz
        apply (hgu n z hz).trans
        apply EReal.coe_le_coe_iff.mpr
        have he := (abs_lt.mp (happ z hz)).1
        linarith
      have hcmp := le_harmonic_add_of_comp_pow k hk hR huP hr hD hh hboundary a
        (mem_closedBall_self hr.le)
      have hhclosed : HarmonicOnNhd h (closedBall a |r|) := hh.mono (subset_univ _)
      have hcircH : CircleIntegrable h a r :=
        (hhclosed.continuousOn.mono sphere_subset_closedBall).circleIntegrable'
      have hcircG : CircleIntegrable (g n) a r := (hg n).continuousOn.circleIntegrable'
      have hcircE : CircleIntegrable (fun _ : ℂ => ε) a r := circleIntegrable_const ε a r
      have havg : h a ≤ Real.circleAverage (g n) a r+ε := by
        have hmono : Real.circleAverage h a r ≤
            Real.circleAverage (fun z => g n z+ε) a r := by
          apply Real.circleAverage_mono hcircH (hcircG.add hcircE)
          intro z hz
          have he := (abs_lt.mp (happ z (by simpa [abs_of_pos hr] using hz))).2
          change h z ≤ g n z+ε
          linarith
        rw [hhclosed.circleAverage_eq,Real.circleAverage_fun_add hcircG hcircE,
          Real.circleAverage_const] at hmono
        exact hmono
      have hreal : (u a).toReal ≤ h a+ε := by
        apply EReal.coe_le_coe_iff.mp
        rw [EReal.coe_toReal hatop habot]
        exact hcmp
      dsimp [ε] at hreal havg
      linarith
    have hdef : circleDeficit u a 1 r C ≤
        ENNReal.ofReal (2*Real.pi)*((C : EReal)-u a).toENNReal := by
      apply circleSubmean_of_continuous_antitone_majorants a g hg
      · intro n z _hz
        exact hgC n z
      · intro t m n hmn
        exact EReal.coe_le_coe_iff.mpr (hganti _ hmn)
      · intro t
        have hzK : a+circleMap 0 r t ∈ K := by
          simpa [K,circleMap] using circleMap_mem_sphere a hr.le t
        exact hginf _ hzK
      · exact hcenter
    apply (SGPT.PSH.le_circleMean_iff a 1 hr.le C ?_).mpr hdef
    rwa [SGPT.PSH.affineClosedDisc_one]

end SGPT.Unibranch.RamifiedPower
