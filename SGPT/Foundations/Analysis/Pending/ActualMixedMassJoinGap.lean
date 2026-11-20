import SGPT.Foundations.Analysis.Pending.GlobalMixedMassMonotone
import SGPT.Foundations.Analysis.Pending.RelativeEnergy
import SGPT.Foundations.Analysis.Pending.RelativePreceqClasses
import SGPT.Foundations.Analysis.Pending.DominationPrincipleReduction

set_option autoImplicit false

/-! # The actual mixed mass expression in SGPT (6.9)

The expression uses the existing endpoint mixed non-pluripolar masses.
Its bounds and filter characterization are independent mass consequences;
identification or comparison with a singularity distance is a separate task.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.ActualMixedMassJoinGap

open FirstPass FirstPass.PositiveClasses GlobalNonPluripolar RelativeEnergy
  GlobalMixedMassMonotone MixedMass RelativePreceqClasses

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] {θ : ClosedRealOneOneForm n M} {p u v : M → EReal}

private theorem endpointMass_mono (omega : KahlerBackground n M)
    (hp : IsThetaPshPotential θ.val p) (hu : IsThetaPshPotential θ.val u)
    (hv : IsThetaPshPotential θ.val v) (huv : MoreSingularOn u v univ)
    (k : Fin (n + 1)) :
    (endpointMixedMass θ p u hp hu k).toReal ≤
      (endpointMixedMass θ p v hp hv k).toReal := by
  have htu : ∀ i : Fin n,
      IsThetaPshPotential θ.val (endpointMixedPotential k u p i) := by
    intro i
    by_cases h : i.val < k.val
    · simpa [endpointMixedPotential, h] using hu
    · simpa [endpointMixedPotential, h] using hp
  have htv : ∀ i : Fin n,
      IsThetaPshPotential θ.val (endpointMixedPotential k v p i) := by
    intro i
    by_cases h : i.val < k.val
    · simpa [endpointMixedPotential, h] using hv
    · simpa [endpointMixedPotential, h] using hp
  have ht : ∀ i : Fin n,
      MoreSingularOn (endpointMixedPotential k u p i)
        (endpointMixedPotential k v p i) univ := by
    intro i
    by_cases h : i.val < k.val
    · simpa [endpointMixedPotential, h] using huv
    · simpa [endpointMixedPotential, h] using MoreSingularOn.refl p univ
  have hm := globalMixedMass_mono_of_isThetaPshPotential omega htu htv ht
  change endpointMixedMass θ p u hp hu k ≤ endpointMixedMass θ p v hp hv k at hm
  exact ENNReal.toReal_mono
    (globalMixedMass_lt_top omega (endpointMixedPotential_thetaPlurisubharmonic θ k v p hv hp)).ne hm

/-- The actual average mixed mass change through the pointwise maximum.
This definition makes no identification with a singularity distance. -/
def mixedMassJoinGap (hp : IsThetaPshPotential θ.val p)
    (hu : IsThetaPshPotential θ.val u) (hv : IsThetaPshPotential θ.val v) : ℝ :=
  (∑ k : Fin (n + 1),
    (2 * (endpointMixedMass θ p (fun x => max (u x) (v x)) hp
        (IsThetaPshPotential.max hu hv) k).toReal -
      (endpointMixedMass θ p u hp hu k).toReal -
      (endpointMixedMass θ p v hp hv k).toReal)) / (n + 1 : ℝ)

/-- Genuine finite total masses give nonnegativity and per-slot absolute
mass bounds, in every dimension. No subset-wise measure comparison is used. -/
theorem mixedMassJoinGap_bounds (omega : KahlerBackground n M)
    (hp : IsThetaPshPotential θ.val p) (hu : IsThetaPshPotential θ.val u)
    (hv : IsThetaPshPotential θ.val v) :
    0 ≤ mixedMassJoinGap hp hu hv ∧ ∀ k : Fin (n + 1),
      |(endpointMixedMass θ p u hp hu k).toReal -
          (endpointMixedMass θ p v hp hv k).toReal| ≤
        (n + 1 : ℝ) * mixedMassJoinGap hp hu hv ∧
      |(endpointMixedMass θ p (fun x => max (u x) (v x)) hp
          (IsThetaPshPotential.max hu hv) k).toReal -
          (endpointMixedMass θ p v hp hv k).toReal| ≤
        (n + 1 : ℝ) * mixedMassJoinGap hp hu hv := by
  classical
  let a := fun k => (endpointMixedMass θ p u hp hu k).toReal
  let b := fun k => (endpointMixedMass θ p v hp hv k).toReal
  let c := fun k => (endpointMixedMass θ p (fun x => max (u x) (v x)) hp
    (IsThetaPshPotential.max hu hv) k).toReal
  have hac (k : Fin (n + 1)) : a k ≤ c k :=
    endpointMass_mono omega hp hu (IsThetaPshPotential.max hu hv)
      (MoreSingularOn.of_le fun x _ => le_max_left _ _) k
  have hbc (k : Fin (n + 1)) : b k ≤ c k :=
    endpointMass_mono omega hp hv (IsThetaPshPotential.max hu hv)
      (MoreSingularOn.of_le fun x _ => le_max_right _ _) k
  have hd (k : Fin (n + 1)) : 0 ≤ 2 * c k - a k - b k := by
    have := hac k
    have := hbc k
    linarith
  have hn : (n + 1 : ℝ) ≠ 0 := by positivity
  have hscale : (n + 1 : ℝ) * mixedMassJoinGap hp hu hv =
      ∑ k : Fin (n + 1), (2 * c k - a k - b k) := by
    unfold mixedMassJoinGap
    exact mul_div_cancel₀ _ hn
  constructor
  · exact div_nonneg (Finset.sum_nonneg fun k _ => hd k) (by positivity)
  · intro k
    have hsum : 2 * c k - a k - b k ≤
        ∑ j : Fin (n + 1), (2 * c j - a j - b j) :=
      Finset.single_le_sum (fun j _ => hd j) (Finset.mem_univ k)
    have hab : |a k - b k| ≤ 2 * c k - a k - b k := by
      have := hac k
      have := hbc k
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    have hcb : |c k - b k| ≤ 2 * c k - a k - b k := by
      have := hac k
      have := hbc k
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    rw [hscale]
    exact ⟨hab.trans hsum, hcb.trans hsum⟩

private theorem endpointMass_eq (omega : KahlerBackground n M)
    (hp : IsThetaPshPotential θ.val p) (hu : IsThetaPshPotential θ.val u)
    (hv : IsThetaPshPotential θ.val v) (huv : SameSingularityTypeOn u v univ)
    (k : Fin (n + 1)) :
    (endpointMixedMass θ p u hp hu k).toReal =
      (endpointMixedMass θ p v hp hv k).toReal :=
  le_antisymm (endpointMass_mono omega hp hu hv huv.1 k)
    (endpointMass_mono omega hp hv hu huv.2 k)

/-- Comparable genuine singularity types give the actual one-sided mass sum.
This does not use or assert a singularity-distance formula. -/
theorem mixedMassJoinGap_eq_sum_of_moreSingular (omega : KahlerBackground n M)
    (hp : IsThetaPshPotential θ.val p) (hu : IsThetaPshPotential θ.val u)
    (hv : IsThetaPshPotential θ.val v) (huv : MoreSingularOn u v univ) :
    mixedMassJoinGap hp hu hv =
      (∑ k : Fin (n + 1), ((endpointMixedMass θ p v hp hv k).toReal -
        (endpointMixedMass θ p u hp hu k).toReal)) / (n + 1 : ℝ) := by
  classical
  have hmax : SameSingularityTypeOn (fun x => max (u x) (v x)) v univ :=
    ⟨DominationPrincipleReduction.moreSingularOn_max huv (MoreSingularOn.refl v univ),
      MoreSingularOn.of_le fun x _ => le_max_right _ _⟩
  unfold mixedMassJoinGap
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [endpointMass_eq omega hp (IsThetaPshPotential.max hu hv) hv hmax k]
  ring

private theorem moreSingular_max_max {X : Type*} {a b c d : X → EReal}
    (hac : MoreSingularOn a c univ) (hbd : MoreSingularOn b d univ) :
    MoreSingularOn (fun x => max (a x) (b x)) (fun x => max (c x) (d x)) univ := by
  obtain ⟨C, hC⟩ := hac
  obtain ⟨D, hD⟩ := hbd
  refine ⟨max C D, fun x hx => ?_⟩
  rw [← max_add_coe]
  apply max_le_max
  · exact (hC x hx).trans
      (add_le_add le_rfl (EReal.coe_le_coe_iff.mpr (le_max_left C D)))
  · exact (hD x hx).trans
      (add_le_add le_rfl (EReal.coe_le_coe_iff.mpr (le_max_right C D)))

/-- Both endpoint types, including the actual maximum type, determine the
actual mixed mass expression. -/
theorem mixedMassJoinGap_eq_of_sameSingularityType (omega : KahlerBackground n M)
    {u' v' : M → EReal} (hp : IsThetaPshPotential θ.val p)
    (hu : IsThetaPshPotential θ.val u) (hv : IsThetaPshPotential θ.val v)
    (hu' : IsThetaPshPotential θ.val u') (hv' : IsThetaPshPotential θ.val v')
    (huu' : SameSingularityTypeOn u u' univ)
    (hvv' : SameSingularityTypeOn v v' univ) :
    mixedMassJoinGap hp hu hv = mixedMassJoinGap hp hu' hv' := by
  classical
  have hmax : SameSingularityTypeOn (fun x => max (u x) (v x))
      (fun x => max (u' x) (v' x)) univ :=
    ⟨moreSingular_max_max huu'.1 hvv'.1, moreSingular_max_max huu'.2 hvv'.2⟩
  unfold mixedMassJoinGap
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [endpointMass_eq omega hp hu hu' huu' k,
    endpointMass_eq omega hp hv hv' hvv' k,
    endpointMass_eq omega hp (IsThetaPshPotential.max hu hv)
      (IsThetaPshPotential.max hu' hv') hmax k]

/-- For every filter, vanishing of the genuine mass gap is exactly convergence
of both endpoint and maximum mixed masses. This is not a distance criterion. -/
theorem tendsto_mixedMassJoinGap_zero_iff (omega : KahlerBackground n M)
    {ι : Type*} (F : Filter ι) {w : ι → M → EReal}
    (hp : IsThetaPshPotential θ.val p) (hv : IsThetaPshPotential θ.val v)
    (hw : ∀ i, IsThetaPshPotential θ.val (w i)) :
    Tendsto (fun i => mixedMassJoinGap hp (hw i) hv) F (𝓝 0) ↔
      ∀ k : Fin (n + 1),
        Tendsto (fun i => (endpointMixedMass θ p (w i) hp (hw i) k).toReal) F
          (𝓝 (endpointMixedMass θ p v hp hv k).toReal) ∧
        Tendsto (fun i => (endpointMixedMass θ p (fun x => max (w i x) (v x)) hp
          (IsThetaPshPotential.max (hw i) hv) k).toReal) F
          (𝓝 (endpointMixedMass θ p v hp hv k).toReal) := by
  classical
  constructor
  · intro h k
    have hs : Tendsto (fun i => (n + 1 : ℝ) * mixedMassJoinGap hp (hw i) hv)
        F (𝓝 0) := by
      simpa only [mul_zero] using h.const_mul (n + 1 : ℝ)
    have ha : Tendsto (fun i => |(endpointMixedMass θ p (w i) hp (hw i) k).toReal -
        (endpointMixedMass θ p v hp hv k).toReal|) F (𝓝 0) :=
      squeeze_zero (fun _ => abs_nonneg _) (fun i =>
        ((mixedMassJoinGap_bounds omega hp (hw i) hv).2 k).1) hs
    have hb : Tendsto (fun i => |(endpointMixedMass θ p (fun x => max (w i x) (v x))
        hp (IsThetaPshPotential.max (hw i) hv) k).toReal -
        (endpointMixedMass θ p v hp hv k).toReal|) F (𝓝 0) :=
      squeeze_zero (fun _ => abs_nonneg _) (fun i =>
        ((mixedMassJoinGap_bounds omega hp (hw i) hv).2 k).2) hs
    constructor
    · exact tendsto_iff_dist_tendsto_zero.mpr (by simpa only [Real.dist_eq] using ha)
    · exact tendsto_iff_dist_tendsto_zero.mpr (by simpa only [Real.dist_eq] using hb)
  · intro h
    have hk (k : Fin (n + 1)) :
        Tendsto (fun i => 2 * (endpointMixedMass θ p (fun x => max (w i x) (v x)) hp
          (IsThetaPshPotential.max (hw i) hv) k).toReal -
          (endpointMixedMass θ p (w i) hp (hw i) k).toReal -
          (endpointMixedMass θ p v hp hv k).toReal) F (𝓝 0) := by
      have hz : 2 * (endpointMixedMass θ p v hp hv k).toReal -
          (endpointMixedMass θ p v hp hv k).toReal -
          (endpointMixedMass θ p v hp hv k).toReal = 0 := by ring
      simpa only [hz] using (((h k).2.const_mul 2).sub (h k).1).sub_const
        (endpointMixedMass θ p v hp hv k).toReal
    simpa only [mixedMassJoinGap, Finset.sum_const_zero, zero_div] using
      (tendsto_finsetSum Finset.univ fun k _ => hk k).div_const (n + 1 : ℝ)

end

end SGPT.Foundations.Analysis.Pending.ActualMixedMassJoinGap
