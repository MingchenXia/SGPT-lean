import SGPT.Okounkov.TranscendentalBodyBound
import SGPT.Foundations.Analysis.Pending.DominationResidualMass
import SGPT.Foundations.Analysis.FirstPass.LocalPotentialPullback
import SGPT.Foundations.Analysis.FirstPass.HolomorphicDDC

/-!
# Restriction of a metered divisor to a submanifold not contained in its support

Package VOL (blueprint `claude-tok-volid`, node `tok-volid:divisor-restriction`), an ingredient
of the restricted mass identity used in `tok:Bn-implies-Cn` (DRWNXZ Lemma 7.5): for a holomorphic
map `f : V → M` and a metered effective `ℚ`-divisor `D` on `M` whose weight `ψ_D ∘ f` is not
identically `-∞` on any open subset of `V`, the pullback `f^*D` is a metered effective
`ℚ`-divisor on `V` with weight `ψ_D ∘ f` and curvature `f^*Θ_D` (`meteredPullback`): a local
presentation `ψ_D = ∑ aᵢ log |gᵢ|² + h` pulls back to `∑ aᵢ log |gᵢ ∘ f|² + h ∘ f` (the factors with
`aᵢ = 0` are replaced by `1`, and no `gᵢ ∘ f` with `aᵢ > 0` vanishes on an open set since
`ψ_D ∘ f` is nondegenerate), and `Θ_D = -dd^c h` pulls back to `-dd^c (h ∘ f)` (naturality of
`dd^c` under holomorphic maps, TN `HolomorphicDDC.smoothDDC_comp`).

Consequence (`diagonalPotentialMass_pullback_residual_eq`): if `w = ψ_D + b` on `M`, then the
restricted non-pluripolar masses agree, `∫_V ⟨(f^*(θ - Θ_D) + dd^c (b ∘ f))^k⟩ =
∫_V ⟨(f^*θ + dd^c (w ∘ f))^k⟩` (TN `diagonalPotentialMass_sub_curvature_eq` applied to `f^*D`).
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Okounkov.TranscendentalVolId

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps
open SGPT.Foundations.Analysis.FirstPass.LocalPotentialPullback
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.DiagonalMass

variable {k n : ℕ} {V M : Type*}
  [TopologicalSpace V] [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V]
  [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- A finite sum of extended reals, none `⊤`, one of them `⊥`, is `⊥`. -/
theorem finsetSum_eq_bot_of_mem {ι : Type*} (s : Finset ι) (u : ι → EReal)
    (_htop : ∀ i ∈ s, u i ≠ ⊤) {i₀ : ι} (hi₀ : i₀ ∈ s) (hbot : u i₀ = ⊥) :
    ∑ i ∈ s, u i = ⊥ := by
  classical
  rw [← Finset.add_sum_erase s u hi₀, hbot, EReal.bot_add]

/-- The generator logarithm never takes the value `⊤`. -/
theorem generatorLog_ne_top {X : Type*} (g : Fin 1 → X → ℂ) (x : X) : generatorLog g x ≠ ⊤ := by
  unfold generatorLog logNormSq
  intro h
  exact ENNReal.ofReal_ne_top (ENNReal.log_eq_top_iff.mp h)

/-- A nonnegative real multiple of an extended real `≠ ⊤` is `≠ ⊤`. -/
theorem coe_nonneg_mul_ne_top {a : ℝ} (ha : 0 ≤ a) {x : EReal} (hx : x ≠ ⊤) :
    (a : EReal) * x ≠ ⊤ := by
  induction x using EReal.rec with
  | bot =>
      rcases ha.lt_or_eq with h | h
      · rw [EReal.coe_mul_bot_of_pos h]; exact bot_ne_top
      · subst h; simp
  | coe r => rw [← EReal.coe_mul]; exact EReal.coe_ne_top _
  | top => exact absurd rfl hx

/-- **The pullback `f^*D` of a metered effective `ℚ`-divisor** along a holomorphic map whose
pulled-back weight is nondegenerate: weight `ψ_D ∘ f`, curvature `f^*Θ_D`. -/
def meteredPullback {f : V → M} (hf : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ f)
    (D : MeteredEffectiveQDivisor n M) (hnd : LocallyNondegenerate fun y => D.weight (f y)) :
    MeteredEffectiveQDivisor k V where
  weight := fun y => D.weight (f y)
  curvature := ClosedRealOneOneForm.pullback hf D.curvature
  local_presentation := fun y => by
    classical
    obtain ⟨U, hU, hxU, N, a, g, h, ha, hg, hne, hh, hw, hcurv⟩ := D.local_presentation (f y)
    refine ⟨f ⁻¹' U, hU.preimage hf.continuous, hxU, N, a,
      fun i => if a i = 0 then fun _ => (1 : ℂ) else fun z => g i (f z), fun z => h (f z),
      ha, ?_, ?_, ?_, ?_, ?_⟩
    · -- holomorphy
      intro i
      by_cases hai : a i = 0
      · simp only [hai, if_true]
        exact mdifferentiableOn_const
      · simp only [hai, if_false]
        exact (hg i).comp (hf.mdifferentiable (by simp)).mdifferentiableOn (fun z hz => hz)
    · -- no factor vanishes on an open set
      intro i W hW hWU hWne
      by_cases hai : a i = 0
      · obtain ⟨z, hz⟩ := hWne
        exact ⟨z, hz, by simp [hai]⟩
      · by_contra hall
        push Not at hall
        obtain ⟨z₀, hz₀⟩ := hWne
        obtain ⟨z, hzW, hzne⟩ := hnd z₀ W hW hz₀
        apply hzne
        show D.weight (f z) = ⊥
        have hzero : g i (f z) = 0 := by simpa [hai] using hall z hzW
        rw [hw (f z) (hWU hzW)]
        have hpos : (0 : ℝ) < (a i : ℝ) := by
          have : (0 : ℚ) < a i := lt_of_le_of_ne (ha i) (Ne.symm hai)
          exact_mod_cast this
        have hterm : ((a i : ℝ) : EReal) * generatorLog (fun _ : Fin 1 => g i) (f z) = ⊥ := by
          rw [(generatorLog_eq_bot_iff _ _).mpr (fun _ => hzero), EReal.coe_mul_bot_of_pos hpos]
        rw [finsetSum_eq_bot_of_mem _ _ (fun j _ => ?_) (Finset.mem_univ i) hterm, EReal.bot_add]
        exact coe_nonneg_mul_ne_top (by exact_mod_cast ha j) (generatorLog_ne_top _ _)
    · -- smoothness of `h ∘ f` in the charts of `V`
      intro e
      refine contDiffOn_of_locally_contDiffOn fun z hz => ?_
      set d := complexChartAt (n := n) (f (e.val.symm z))
      have hzd : z ∈ coordinateDomain f e d := ⟨hz.1, mem_complexChartAt_source _⟩
      set Wd := d.val.target ∩ d.val.symm ⁻¹' U
      have hWd : IsOpen Wd := d.val.isOpen_inter_preimage_symm hU
      have hhd : ContDiffOn ℝ ∞ (fun w => h (d.val.symm w)) Wd := hh d
      refine ⟨potentialDomain f e d Wd, potentialDomain_isOpen hf e d hWd, ⟨hzd, ?_⟩, ?_⟩
      · refine ⟨coordinateMap_mem_target hzd, ?_⟩
        show d.val.symm (d.val (f (e.val.symm z))) ∈ U
        rw [d.val.left_inv (mem_complexChartAt_source _)]
        exact hz.2
      · have hcomp := hhd.comp_inter (coordinateMap_contDiffOn_real hf e d)
        refine (hcomp.mono fun w hw => ?_).congr fun w hw => ?_
        · exact hw.2
        · show h (f (e.val.symm w)) = h (d.val.symm (d.val (f (e.val.symm w))))
          rw [d.val.left_inv hw.2.1.2]
    · -- the weight
      intro z hz
      show D.weight (f z) = _
      rw [hw (f z) hz]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases hai : a i = 0
      · simp [hai]
      · simp only [hai, if_false]
        rfl
    · -- the curvature
      intro e z hz hzU
      set d := complexChartAt (n := n) (f (e.val.symm z))
      have hzd : z ∈ coordinateDomain f e d := ⟨hz, mem_complexChartAt_source _⟩
      set Wd := d.val.target ∩ d.val.symm ⁻¹' U
      have hWd : IsOpen Wd := d.val.isOpen_inter_preimage_symm hU
      have hhd : ContDiffOn ℝ ∞ (fun w => h (d.val.symm w)) Wd := hh d
      have hzP : z ∈ potentialDomain f e d Wd := by
        refine ⟨hzd, coordinateMap_mem_target hzd, ?_⟩
        show d.val.symm (d.val (f (e.val.symm z))) ∈ U
        rw [d.val.left_inv (mem_complexChartAt_source _)]
        exact hzU
      have hPopen := potentialDomain_isOpen hf e d hWd
      have hcongr : (fun w => h (f (e.val.symm w))) =ᶠ[𝓝 z]
          fun w => h (d.val.symm (coordinateMap f e d w)) := by
        filter_upwards [hPopen.mem_nhds hzP] with w hw
        show h (f (e.val.symm w)) = h (d.val.symm (d.val (f (e.val.symm w))))
        rw [d.val.left_inv hw.1.2]
      rw [smoothDDC_congr hcongr, HolomorphicDDC.smoothDDC_comp hPopen hWd
        ((coordinateMap_contDiffOn hf e d).mono inter_subset_left) hhd (fun _ hw => hw.2) hzP]
      have hc := hcurv d (coordinateMap f e d z) (coordinateMap_mem_target hzd) hzP.2.2
      change (SmoothRealForm.pullback hf D.curvature.val).coeff e z = _
      rw [SmoothRealForm.pullback_coeff hf D.curvature.val e d hzd, hc]
      ext v
      simp

@[simp] theorem meteredPullback_weight {f : V → M}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ f)
    (D : MeteredEffectiveQDivisor n M) (hnd : LocallyNondegenerate fun y => D.weight (f y))
    (y : V) : (meteredPullback hf D hnd).weight y = D.weight (f y) := rfl

@[simp] theorem meteredPullback_curvature {f : V → M}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ f)
    (D : MeteredEffectiveQDivisor n M) (hnd : LocallyNondegenerate fun y => D.weight (f y)) :
    (meteredPullback hf D hnd).curvature = ClosedRealOneOneForm.pullback hf D.curvature := rfl

/-- The non-pluripolar mass does not depend on the proof that the potential is psh, and is
transported along equal forms. -/
theorem diagonalPotentialMass_congr_form [CompactSpace V] [MeasurableSpace V] {θ₁ θ₂ : ClosedRealOneOneForm k V}
    (h : θ₁ = θ₂) {u : V → EReal} (h₁ : IsThetaPshPotential θ₁.val u)
    (h₂ : IsThetaPshPotential θ₂.val u) :
    diagonalPotentialMass θ₁ u h₁ = diagonalPotentialMass θ₂ u h₂ := by
  subst h; rfl

/-- **The restricted residual mass identity**: if `w = ψ_D + b` on `M` (`w` `θ`-psh, `b`
`(θ - Θ_D)`-psh) and `ψ_D ∘ f` is nondegenerate, then
`∫_V ⟨(f^*(θ - Θ_D) + dd^c (b ∘ f))^k⟩ = ∫_V ⟨(f^*θ + dd^c (w ∘ f))^k⟩`. -/
theorem diagonalPotentialMass_pullback_residual_eq [CompactSpace V] [MeasurableSpace V]
    [BorelSpace V] {f : V → M}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ f)
    (θ : ClosedRealOneOneForm n M) (D : MeteredEffectiveQDivisor n M) {w b : M → EReal}
    (heq : ∀ x, w x = D.weight x + b x) (hnd : LocallyNondegenerate fun y => D.weight (f y))
    (hw : IsThetaPshPotential (ClosedRealOneOneForm.pullback hf θ).val fun y => w (f y))
    (hb : IsThetaPshPotential (ClosedRealOneOneForm.pullback hf (θ - D.curvature)).val
      fun y => b (f y)) :
    diagonalPotentialMass (ClosedRealOneOneForm.pullback hf (θ - D.curvature)) (fun y => b (f y))
        hb =
      diagonalPotentialMass (ClosedRealOneOneForm.pullback hf θ) (fun y => w (f y)) hw := by
  set D' := meteredPullback hf D hnd with hD'
  have hform : ClosedRealOneOneForm.pullback hf (θ - D.curvature) =
      ClosedRealOneOneForm.pullback hf θ - D'.curvature := by
    rw [hD', meteredPullback_curvature]
    exact SGPT.Okounkov.TranscendentalBody.pullback_sub' hf θ D.curvature
  have hb' : IsThetaPshPotential (ClosedRealOneOneForm.pullback hf θ - D'.curvature).val
      fun y => b (f y) := by rw [← hform]; exact hb
  rw [diagonalPotentialMass_congr_form hform hb hb']
  exact DominationResidualMass.diagonalPotentialMass_sub_curvature_eq _ D' hw hb'
    (fun y _ => heq (f y)) hnd

end SGPT.Okounkov.TranscendentalVolId
