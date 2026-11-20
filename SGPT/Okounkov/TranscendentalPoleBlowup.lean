import SGPT.Okounkov.TranscendentalPoleWeight
import SGPT.Foundations.Analysis.Pending.BlanchardForm
import SGPT.Foundations.Analysis.Pending.GermIdealPullbackCalculus

/-!
# The pole along a submanifold on the blowup

Source: Demailly--Păun, *Numerical characterization of the Kähler cone*, Lemma 2.1 (the pullback
of the pole to the blowup); Xia, *Foundations of pluripotential theory*, `lem:global-normal-pole`
(4). Blueprint node `tok:ext-pole`.

Let `π : Z → X` be a blowup along the closed submanifold `V` (`IsBlowupAlong`, the universal
property), so that the ideal `π^* 𝓘_V` of the exceptional divisor `E` is invertible
(`BlowupExceptionalDivisor.exceptionalDivisor`). Let `U = ∑_a θ_a² ∑_i |g_{a,i}|²` be the weight
of a concentration partition of `V` and `F = log U`. Near every point `z ∈ Z`, with `h` a local
generator of `π^* 𝓘_V`:

* every `g_{a,i} ∘ π` lies in `π^* 𝓘_V`, hence `g_{a,i} ∘ π = u_{a,i} h` (`u_{a,i}` holomorphic),
  so `U ∘ π = |h|² U'` with `U' = ∑_a (θ_a ∘ π)² ∑_i |u_{a,i}|²` smooth;
* `U'(z) > 0`: `h ∈ π^* 𝓘_V` is a combination of the `g_{a₀,i} ∘ π = u_{a₀,i} h` of a piece through
  `π z`, so `h = Ψ h` with `Ψ` a combination of the `u_{a₀,i}`; if all `u_{a₀,i}(z)` vanished,
  `1 - Ψ` would be invertible near `z` and `h` would vanish on an open set, which an invertible
  generator does not;
* hence `F ∘ π = log |h|² + log U'` with `log U'` smooth (`exists_blowup_factor`).
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalPole

open Set Filter
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.SubmanifoldConcentrationPotential
open SGPT.Foundations.Analysis.Pending.BlowupExceptionalDivisor

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]
  {Z : Type u} [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z]

/-- An invertible local generator `h` cannot satisfy `h = Ψ h` near `z` with `Ψ(z) = 0`. -/
theorem false_of_eq_mul_self {U : Set Z} (hU : IsOpen U) {z : Z} (hzU : z ∈ U) {h Ψ : Z → ℂ}
    (hnon : ∀ W : Set Z, IsOpen W → W ⊆ U → W.Nonempty → ∃ y ∈ W, h y ≠ 0)
    (hΨ : ContinuousAt Ψ z) (hΨ0 : Ψ z = 0) (heq : h =ᶠ[𝓝 z] fun y => Ψ y * h y) : False := by
  have hsmall : ∀ᶠ y in 𝓝 z, Ψ y ≠ 1 := by
    have := hΨ.eventually (isOpen_ne.mem_nhds (show Ψ z ≠ 1 by rw [hΨ0]; exact zero_ne_one))
    exact this
  obtain ⟨W, hWsub, hW, hzW⟩ :=
    _root_.mem_nhds_iff.mp ((heq.and hsmall).and (hU.mem_nhds hzU))
  obtain ⟨y, hyW, hy⟩ := hnon W hW (fun y hy => (hWsub hy).2) ⟨z, hzW⟩
  obtain ⟨⟨h1, h2⟩, -⟩ := hWsub hyW
  have : h y * (1 - Ψ y) = 0 := by
    have h1' : h y = Ψ y * h y := h1
    linear_combination h1'
  rcases mul_eq_zero.mp this with h0 | h0
  · exact hy h0
  · exact h2 (by linear_combination -h0)

variable {V : Set X} {ι : Type*} [Fintype ι] (P : ConcentrationPartition n V ι)

/-- **The pole on a blowup**: near every point of a blowup `π : Z → X` along `V`,
`F ∘ π = log |h|² + R` with `h` an invertible local generator of the exceptional ideal
`π^* 𝓘_V` and `R` smooth. -/
theorem exists_blowup_factor {π : Z → X} (hπ : IsBlowupAlong n V π) (z : Z) :
    ∃ (S : Set Z) (h : Z → ℂ) (R : Z → ℝ), IsOpen S ∧ z ∈ S ∧
      (∀ y ∈ S, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) h y) ∧
      (∀ W : Set Z, IsOpen W → W ⊆ S → W.Nonempty → ∃ y ∈ W, h y ≠ 0) ∧
      (∀ y ∈ S, ∀ a : Z → ℂ,
        (exceptionalDivisor hπ).ideal.mem y a ↔ IsInSpanAt (n := n) (· = h) y a) ∧
      (∀ e : ComplexChart n Z,
        ContDiffOn ℝ ∞ (fun w => R (e.val.symm w)) (e.val.target ∩ e.val.symm ⁻¹' S)) ∧
      ∀ y ∈ S, concentrationPole P (π y) =
        ENNReal.log (ENNReal.ofReal (‖h y‖ ^ 2)) + (R y : EReal) := by
  classical
  obtain ⟨U, hU, hzU, h, hhol, hnon, hgen⟩ := (exceptionalDivisor hπ).isInvertible z
  set x := π z with hxdef
  have hπs := hπ.contMDiff
  have hπc : Continuous π := hπs.continuous
  have hπd : ∀ y, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) π y :=
    fun y => (hπs y).mdifferentiableAt (by simp)
  have hhz : HolomorphicAt n h z := by
    filter_upwards [hU.mem_nhds hzU] with y hy
    exact (hhol y hy).mdifferentiableAt (hU.mem_nhds hy)
  -- holomorphy of the pulled-back generators
  have hgenπ : ∀ a, x ∈ P.dom a → ∀ j, HolomorphicAt n (fun y => P.gen a j (π y)) z := by
    intro a hxa j
    filter_upwards [hπc.continuousAt.preimage_mem_nhds ((P.isOpen_dom a).mem_nhds hxa)] with y hy
    exact ((P.gen_mdifferentiableOn a j (π y) hy).mdifferentiableAt
      ((P.isOpen_dom a).mem_nhds hy)).comp y (hπd y)
  -- every pulled-back generator is a multiple of `h`
  have hfac : ∀ a j, ∃ u : Z → ℂ, HolomorphicAt n u z ∧
      (x ∈ P.dom a → (fun y => P.gen a j (π y)) =ᶠ[𝓝 z] fun y => u y * h y) := by
    intro a j
    by_cases hxa : x ∈ P.dom a
    · have hmem : (exceptionalDivisor hπ).ideal.mem z (fun y => P.gen a j (π y)) := by
        rw [exceptionalDivisor_ideal, RelativePrincipalizationSpan.GermIdeal.mem_pullback_iff]
        exact InvertibleIdealQuotient.isInSpanAt_self
          ⟨P.gen a j, gen_mem_vanishingIdeal P hxa j, rfl⟩ (hgenπ a hxa j)
      obtain ⟨-, w, hw, heq⟩ := isInSpanAt_eq_iff.mp ((hgen z hzU _).mp hmem)
      exact ⟨w, hw, fun _ => heq⟩
    · exact ⟨fun _ => 0, holomorphicAt_const 0, fun h' => absurd h' hxa⟩
  choose u hu hueq using hfac
  -- the smooth factor
  set act : ι → Prop := fun a => x ∈ tsupport (P.part a) with hact
  set U₂ : Z → ℝ := fun y => ∑ a, if act a then
      P.part a (π y) ^ 2 * ∑ j, ‖u a j y‖ ^ 2 else 0 with hU₂
  -- the factorization near `z`
  have hfactor : ∀ᶠ y in 𝓝 z, P.weight (π y) = ‖h y‖ ^ 2 * U₂ y := by
    have hterm : ∀ a, ∀ᶠ y in 𝓝 z, P.part a (π y) ^ 2 * P.genNormSq a (π y) =
        ‖h y‖ ^ 2 * (if act a then P.part a (π y) ^ 2 * ∑ j, ‖u a j y‖ ^ 2 else 0) := by
      intro a
      by_cases ha : act a
      · have hxa : x ∈ P.dom a := P.part_tsupport a ha
        filter_upwards [hπc.continuousAt.preimage_mem_nhds ((P.isOpen_dom a).mem_nhds hxa),
          eventually_all.mpr fun j => hueq a j hxa] with y hy hyu
        rw [if_pos ha, ConcentrationPartition.genNormSq,
          Set.indicator_of_mem (show π y ∈ P.dom a from hy),
          generatorNormSq, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        have hj : P.gen a j (π y) = u a j y * h y := hyu j
        rw [hj, norm_mul]
        ring
      · filter_upwards [hπc.continuousAt.preimage_mem_nhds
          ((isClosed_tsupport (P.part a)).isOpen_compl.mem_nhds ha)] with y hy
        rw [if_neg ha, P.part_eq_zero_of_notMem_tsupport hy]
        ring
    filter_upwards [eventually_all.mpr hterm] with y hy
    rw [ConcentrationPartition.weight, Finset.sum_congr rfl fun a _ => hy a, ← Finset.mul_sum]
  -- positivity of the factor at `z`
  obtain ⟨a₀, ha₀⟩ := P.exists_part_pos x
  have hact₀ : act a₀ := subset_tsupport _ ha₀.ne'
  have hx₀ : x ∈ P.dom a₀ := P.part_tsupport a₀ hact₀
  have hu₀ : ∃ j, u a₀ j z ≠ 0 := by
    by_contra hcon
    push Not at hcon
    -- `h` is a combination of the `g_{a₀,j} ∘ π`
    have hmem : IsInSpanAt (n := n)
        (fun s => ∃ b, (vanishingIdeal (n := n) V).mem (π z) b ∧ s = b ∘ π) z h := by
      have h0 := (hgen z hzU h).mpr (InvertibleIdealQuotient.isInSpanAt_self rfl hhz)
      rwa [exceptionalDivisor_ideal, RelativePrincipalizationSpan.GermIdeal.mem_pullback_iff] at h0
    have hspan : IsInSpanAt (n := n)
        (fun s => ∃ a, a ∈ range (P.gen a₀) ∧ s = a ∘ π) z h := by
      refine RelativePrincipalizationSpan.IsInSpanAt.trans (fun s hs => ?_) hmem
      obtain ⟨b, hb, rfl⟩ := hs
      exact GermIdealPullbackCalculus.isInSpanAt_comp hπs ((P.gen_spec a₀ x hx₀ b).mp hb)
    obtain ⟨-, N, s, γ, hs, hγ, hsum⟩ := hspan
    choose t ht hts using hs
    choose j hj using ht
    set Ψ : Z → ℂ := fun y => ∑ i, γ i y * u a₀ (j i) y with hΨ
    have hΨc : ContinuousAt Ψ z :=
      tendsto_finsetSum _ fun i _ =>
        (hγ i).continuousAt.mul (hu a₀ (j i)).continuousAt
    have hΨ0 : Ψ z = 0 := Finset.sum_eq_zero fun i _ => by rw [hcon (j i), mul_zero]
    refine false_of_eq_mul_self hU hzU hnon hΨc hΨ0 ?_
    filter_upwards [hsum, eventually_all.mpr fun j => hueq a₀ j hx₀] with y hy hyu
    have hs' : ∀ i, s i y = u a₀ (j i) y * h y := fun i => by
      rw [hts i, Function.comp_apply, ← hj i]
      exact hyu (j i)
    calc h y = ∑ i, γ i y * s i y := hy
      _ = (∑ i, γ i y * u a₀ (j i) y) * h y := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => by rw [hs' i]; ring
  obtain ⟨j₀, hj₀⟩ := hu₀
  have hU₂z : 0 < U₂ z := by
    have hterm : 0 < (if act a₀ then
        P.part a₀ (π z) ^ 2 * ∑ j, ‖u a₀ j z‖ ^ 2 else 0) := by
      rw [if_pos hact₀]
      refine mul_pos (pow_pos ha₀ 2) (lt_of_lt_of_le (pow_pos (norm_pos_iff.mpr hj₀) 2) ?_)
      exact Finset.single_le_sum (f := fun j => ‖u a₀ j z‖ ^ 2) (fun j _ => sq_nonneg _)
        (Finset.mem_univ j₀)
    refine lt_of_lt_of_le hterm (Finset.single_le_sum (f := fun a => if act a then
        P.part a (π z) ^ 2 * ∑ j, ‖u a j z‖ ^ 2 else 0) (fun a _ => ?_) (Finset.mem_univ a₀))
    split_ifs
    · exact mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun j _ => sq_nonneg _)
    · exact le_rfl
  have hU₂c : ContinuousAt U₂ z := by
    refine tendsto_finsetSum _ fun a _ => ?_
    split_ifs
    · exact ((P.continuousAt_part a (π z)).comp hπc.continuousAt).pow 2 |>.mul
        (tendsto_finsetSum _ fun j _ => (hu a j).continuousAt.norm.pow 2)
    · exact continuousAt_const
  have hU₂pos : ∀ᶠ y in 𝓝 z, 0 < U₂ y := hU₂c.eventually (lt_mem_nhds hU₂z)
  -- the open set
  have hUev : ∀ᶠ y in 𝓝 z, y ∈ U := hU.mem_nhds hzU
  obtain ⟨S, hSsub, hS, hzS⟩ := _root_.mem_nhds_iff.mp
    (hUev.and (hfactor.and (hU₂pos.and (eventually_all.mpr fun a =>
      eventually_all.mpr fun j => (hu a j)))))
  refine ⟨S, h, fun y => Real.log (U₂ y), hS, hzS,
    fun y hy => (hhol y (hSsub hy).1).mdifferentiableAt (hU.mem_nhds (hSsub hy).1),
    fun W hW hWS hne => hnon W hW (hWS.trans fun y hy => (hSsub hy).1) hne,
    fun y hy => hgen y (hSsub hy).1, fun e => ?_, fun y hy => ?_⟩
  · -- smoothness of `log U₂`
    intro w hw
    have hO : IsOpen (e.val.target ∩ e.val.symm ⁻¹' S) := e.val.isOpen_inter_preimage_symm hS
    have hpart : ∀ a, ContDiffAt ℝ ∞ (fun w => P.part a (π (e.val.symm w))) w := fun a =>
      (BlanchardForm.contDiffOn_chartSmooth_comp hπs (P.part_smooth a) e).contDiffAt
        (e.val.open_target.mem_nhds hw.1)
    have hnorm : ∀ a j, ContDiffAt ℝ ∞ (fun w => ‖u a j (e.val.symm w)‖ ^ 2) w := by
      intro a j
      have hd : ∀ᶠ w' in 𝓝 w, DifferentiableAt ℂ (fun w => u a j (e.val.symm w)) w' := by
        filter_upwards [hO.mem_nhds hw] with w' hw'
        exact mdifferentiableAt_iff_differentiableAt.mp
          (((hSsub hw'.2).2.2.2 a j).comp w'
            (mdifferentiableAt_atlas_symm (I := 𝓘(ℂ, ComplexModel n)) e.property hw'.1))
      exact (contDiff_norm_sq ℝ).contDiffAt.comp w
        (ConcentrationPotentialLevi.contDiffAt_of_eventually_differentiableAt hd)
    have hU₂s : ContDiffAt ℝ ∞ (fun w => U₂ (e.val.symm w)) w := by
      refine ContDiffAt.sum fun a _ => ?_
      by_cases ha : act a
      · simp only [if_pos ha]
        exact (hpart a).pow 2 |>.mul (ContDiffAt.sum fun j _ => hnorm a j)
      · simp only [if_neg ha]
        exact contDiffAt_const
    exact (hU₂s.log (hSsub hw.2).2.2.1.ne').contDiffWithinAt
  · -- the identity
    obtain ⟨-, hfy, hposy, -⟩ := hSsub hy
    change ENNReal.log (ENNReal.ofReal (P.weight (π y))) = _
    rw [hfy, ENNReal.ofReal_mul (sq_nonneg _), ENNReal.log_mul_add,
      ENNReal.log_ofReal_of_pos hposy]

end SGPT.Okounkov.TranscendentalPole
