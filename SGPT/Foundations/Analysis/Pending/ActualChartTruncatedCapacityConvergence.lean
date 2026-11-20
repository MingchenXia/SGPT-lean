import SGPT.Foundations.Analysis.Pending.ActualChartCapacityReverse
import SGPT.Foundations.Analysis.Pending.ManifoldPluripolar

set_option autoImplicit false

/-! # Genuine global capacity convergence localizes after lower truncation

Independent all-filter compact chart localization for unbounded potentials.
Original closed backgrounds need not be Big or semipositive. The actual
lower extended-real maximum precedes realification, so poles are retained.
-/

open Set Filter TopologicalSpace
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.ActualChartTruncatedCapacityConvergence

open FirstPass FirstPass.PositiveClasses ThetaCapacity BedfordTaylor

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

omit [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M] in
private theorem lower_truncation_gap_le {a b : EReal}
    (hat : a ≠ ⊤) (hab : a ≠ ⊥) (hbt : b ≠ ⊤) (hbb : b ≠ ⊥) (r L : ℝ) :
    |(max (a + (r : EReal)) (L : EReal)).toReal -
        (max (b + (r : EReal)) (L : EReal)).toReal| ≤ |a.toReal - b.toReal| := by
  have heq (c : EReal) (hct : c ≠ ⊤) (hcb : c ≠ ⊥) :
      (max (c + (r : EReal)) (L : EReal)).toReal = max (c.toReal + r) L := by
    have hcoef : ((c.toReal : ℝ) : EReal) = c := EReal.coe_toReal hct hcb
    have hmax : max (c + (r : EReal)) (L : EReal) = ((max (c.toReal + r) L : ℝ) : EReal) := by
      rw [← hcoef, ← EReal.coe_add]
      exact (EReal.coe_strictMono.monotone.map_max).symm
    rw [hmax, EReal.toReal_coe]
  rw [heq a hat hab, heq b hbt hbb]
  simpa only [add_sub_add_right_eq_sub] using
    abs_max_sub_max_le_abs (a.toReal + r) (b.toReal + r) L

/-- Actual capacity convergence off the two genuine polar sets transports to
relative capacity of fixed lower truncations on an actual chart compact.
There is no boundedness or countability hypothesis on the incoming family. -/
theorem tendsto_relative_capacity_lower_truncation
    (omega : KahlerBackground n M) (e : ComplexChart n M)
    {D : Opens (ComplexModel n)} (hDt : (D : Set (ComplexModel n)) ⊆ e.val.target)
    {ρ : ComplexModel n → ℝ} (hρ : IsSmoothLocalPotential omega.form.val e D ρ)
    {K : Set (ComplexModel n)} (hK : IsCompact K) (hKD : K ⊆ D)
    {α : ClosedRealOneOneForm n M} {I : Type*} {F : Filter I}
    {u : I → M → EReal} {v : M → EReal}
    (hu : ∀ i, IsThetaPshPotential α.val (u i)) (hv : IsThetaPshPotential α.val v)
    (hcap : ∀ a : ℝ, 0 < a → Tendsto (fun i => thetaCapacity omega.form (fun _ => 0)
      {x | u i x ≠ ⊥ ∧ v x ≠ ⊥ ∧ a < |(u i x).toReal - (v x).toReal|}) F (𝓝 0))
    (r : ComplexModel n → ℝ) (L : ℝ) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun i => relCapacity D {z | z ∈ K ∧ a <
      |(max (u i (e.val.symm z) + (r z : EReal)) (L : EReal)).toReal -
        (max (v (e.val.symm z) + (r z : EReal)) (L : EReal)).toReal|}) F (𝓝 0) := by
  obtain ⟨C, _hC, hreverse⟩ := ActualChartCapacityReverse.exists_compact_capacity_reverse
    omega e hDt hρ hK hKD
  let E : I → Set (ComplexModel n) := fun i => {z | z ∈ K ∧ a <
      |(max (u i (e.val.symm z) + (r z : EReal)) (L : EReal)).toReal -
        (max (v (e.val.symm z) + (r z : EReal)) (L : EReal)).toReal|}
  let S : I → Set M := fun i =>
    {x | u i x ≠ ⊥ ∧ v x ≠ ⊥ ∧ a < |(u i x).toReal - (v x).toReal|}
  let P : I → Set M := fun i => {x | u i x = ⊥} ∪ {x | v x = ⊥}
  have hpolar (i : I) : FirstPass.ManifoldLocallyPluripolar (n := n) (P i) :=
    manifoldLocallyPluripolar_union
      (quasiPsh_poles_manifoldLocallyPluripolar (hu i).quasiPshPotential)
      (quasiPsh_poles_manifoldLocallyPluripolar hv.quasiPshPotential)
  have hzero (i : I) : thetaCapacity omega.form (fun _ => 0) (P i) = 0 :=
    thetaCapacity_eq_zero_of_manifoldLocallyPluripolar (fun _ => 0) (hpolar i)
  have hsubset (i : I) : e.val.symm '' E i ⊆ S i ∪ P i := by
    rintro x ⟨z, hz, rfl⟩
    by_cases hui : u i (e.val.symm z) = ⊥
    · exact Or.inr (Or.inl hui)
    by_cases hvi : v (e.val.symm z) = ⊥
    · exact Or.inr (Or.inr hvi)
    refine Or.inl ⟨hui, hvi, hz.2.trans_le ?_⟩
    exact lower_truncation_gap_le ((hu i).quasiPshPotential.1.ne_top (e.val.symm z)) hui
      (hv.quasiPshPotential.1.ne_top (e.val.symm z)) hvi (r z) L
  have hcap_bound (i : I) : thetaCapacity omega.form (fun _ => 0) (e.val.symm '' E i) ≤
      thetaCapacity omega.form (fun _ => 0) (S i) := by
    calc _ ≤ thetaCapacity omega.form (fun _ => 0) (S i ∪ P i) := thetaCapacity_mono (hsubset i)
         _ ≤ thetaCapacity omega.form (fun _ => 0) (S i) +
           thetaCapacity omega.form (fun _ => 0) (P i) := thetaCapacity_union_le _ _ _ _
         _ = _ := by rw [hzero i, add_zero]
  have hbound (i : I) : relCapacity D (E i) ≤
      ENNReal.ofReal C * thetaCapacity omega.form (fun _ => 0) (S i) :=
    (hreverse (E i) (fun _ hz => hz.1)).trans (mul_le_mul_right (hcap_bound i) _)
  have hupper : Tendsto (fun i => ENNReal.ofReal C * thetaCapacity omega.form (fun _ => 0) (S i))
      F (𝓝 0) := by
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul (hcap a ha) (Or.inr ENNReal.ofReal_ne_top)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
    (fun _ => bot_le) hbound

end
end SGPT.Foundations.Analysis.Pending.ActualChartTruncatedCapacityConvergence
