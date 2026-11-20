import SGPT.Foundations.Analysis.Pending.ActualSynchronizedChartCapacityLift
import SGPT.Foundations.Analysis.Pending.ThetaCapacityChartLocal
import SGPT.Foundations.Analysis.Pending.BedfordTaylorFixedWeight

set_option autoImplicit false

/-! # Actual local capacity convergence produces synchronized global limits

Independent all-filter consumer of the common genuine max-lift. Local
capacity is explicitly assumed on every smaller domain and interior compact.
The chart collar, local-potential bound and global capacity convergence are
produced. No mixed weak or unbounded lower semicontinuity claim is made.
-/

open Set Filter TopologicalSpace
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.ActualChartCapacityLiftConvergence

open FirstPass FirstPass.PositiveClasses FirstPass.MongeAmpere
  ThetaCapacity ThetaCapacityChart BedfordTaylor

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

/-- Actual local capacity convergence on every smaller domain and compact set
produces genuine synchronized global capacity-convergent boxed lifts. -/
theorem exists_capacity_convergent_lifts (omega : KahlerBackground n M)
    (e : ComplexChart n M) {D : Opens (ComplexModel n)}
    (hDt : (D : Set (ComplexModel n)) ⊆ e.val.target)
    {ρ : ComplexModel n → ℝ} (hρ : IsSmoothLocalPotential omega.form.val e D ρ)
    {K : Set (ComplexModel n)} (hK : IsCompact K) (hKD : K ⊆ D) {I : Type*} :
    ∃ δ : ℝ, 0 < δ ∧ ∃ (O : Set M) (lift : (ComplexModel n → ℝ) → M → EReal),
      IsOpen O ∧ e.val.symm '' K ⊆ O ∧
      O ⊆ e.val.source ∩ e.val ⁻¹' (D : Set (ComplexModel n)) ∧
      (∀ f, IsLocallyBoundedPshOn D f → (∀ z ∈ D, -1 ≤ f z ∧ f z ≤ 0) →
        IsThetaPshPotential omega.form.val (lift f) ∧
        (∀ x, (-1 : EReal) ≤ lift f x ∧ lift f x ≤ 0) ∧
        ∀ x ∈ O, lift f x = ((δ * f (e.val x) - δ : ℝ) : EReal)) ∧
      ∀ (F : Filter I) (f : I → ComplexModel n → ℝ) (g : ComplexModel n → ℝ),
        (∀ i z, z ∈ D → -1 ≤ f i z ∧ f i z ≤ 0) →
        (∀ z ∈ D, -1 ≤ g z ∧ g z ≤ 0) →
        (∀ (V : Opens (ComplexModel n)), V ≤ D → ∀ (T : Set (ComplexModel n)),
          IsCompact T → T ⊆ V → ∀ a : ℝ, 0 < a →
          Tendsto (fun i => relCapacity V {z | z ∈ T ∧ a < |f i z - g z|}) F (𝓝 0)) →
        ∀ a : ℝ, 0 < a → Tendsto (fun i => thetaCapacity omega.form (fun _ => 0)
          {x | a < |(lift (f i) x).toReal - (lift g x).toReal|}) F (𝓝 0) := by
  obtain ⟨V0, hVo, hKV, hclVD, hVc⟩ :=
    exists_open_between_and_isCompact_closure hK D.isOpen hKD
  let V : Opens (ComplexModel n) := ⟨V0, hVo⟩
  have hVD : V ≤ D := subset_closure.trans hclVD
  have hVt : (V : Set (ComplexModel n)) ⊆ e.val.target := fun z hz => hDt (hVD hz)
  have hρV : IsSmoothLocalPotential omega.form.val e V ρ := hρ.mono hVo hVD
  obtain ⟨A0, hA0⟩ := hVc.exists_bound_of_continuousOn (hρ.2.2.1.continuousOn.mono hclVD)
  let A : ℝ := max A0 0
  have hA : 0 ≤ A := le_max_right _ _
  have hρbound : ∀ z ∈ V, |ρ z| ≤ A := by
    intro z hz
    have hh : |ρ z| ≤ A0 := by simpa only [Real.norm_eq_abs] using hA0 z (subset_closure hz)
    exact hh.trans (le_max_left A0 0)
  obtain ⟨δ, hδ, _h3δ, O, T, lift, hO, hKO, hOV, hT, hTV, hPSH, hgap, houtside⟩ :=
    ActualSynchronizedChartCapacityLift.exists_synchronized_capacity_lift
      omega e hVt hρV hK hKV
  refine ⟨δ, hδ, O, lift, hO, hKO, ?_, ?_, ?_⟩
  · intro x hx
    exact ⟨(hOV hx).1, hVD (hOV hx).2⟩
  · intro f hf hb
    exact hPSH f (BedfordTaylor.IsLocallyBoundedPshOn.mono_opens hf hVD)
      (fun z hz => hb z (hVD hz))
  · intro F f g hfbox hgbox hcap a ha
    have hfboxV (i : I) : ∀ z ∈ V, -1 ≤ f i z ∧ f i z ≤ 0 :=
      fun z hz => hfbox i z (hVD hz)
    have hgboxV : ∀ z ∈ V, -1 ≤ g z ∧ g z ≤ 0 := fun z hz => hgbox z (hVD hz)
    let S : I → Set M := fun i => {x | a < |(lift (f i) x).toReal - (lift g x).toReal|}
    let E : I → Set (ComplexModel n) := fun i => {z | z ∈ T ∧ a / δ < |f i z - g z|}
    let J := diagSlotChart omega.form e V hVt ρ hρV
    have hST (i : I) : S i ⊆ e.val.symm '' T := by
      intro x hx
      by_contra hnot
      have hh := houtside (f i) g (hfboxV i) hgboxV x hnot
      have hn : a < 0 := by
        have hx' : a < |(lift (f i) x).toReal - (lift g x).toReal| := hx
        simpa only [hh, sub_self, abs_zero] using hx'
      exact (not_lt_of_ge ha.le) hn
    have hsource (i : I) : S i ⊆ (J.source : Set M) := by
      intro x hx
      obtain ⟨z, hz, rfl⟩ := hST i hx
      change e.val.symm z ∈ e.val.source ∩ e.val ⁻¹' (V : Set (ComplexModel n))
      refine ⟨e.val.map_target (hVt (hTV hz)), ?_⟩
      change e.val (e.val.symm z) ∈ (V : Set (ComplexModel n))
      rw [e.val.right_inv (hVt (hTV hz))]
      exact hTV hz
    have himage (i : I) : e.val '' S i ⊆ E i := by
      rintro z ⟨x, hx, rfl⟩
      obtain ⟨t, ht, hxt⟩ := hST i hx
      have hxT : e.val x ∈ T := by
        rw [← hxt, e.val.right_inv (hVt (hTV ht))]
        exact ht
      refine ⟨hxT, (div_lt_iff₀ hδ).mpr ?_⟩
      have hh : a < δ * |f i (e.val x) - g (e.val x)| := hx.trans_le (hgap (f i) g x)
      simpa only [mul_comm] using hh
    let C : ℝ := (2 * A + 2) ^ n
    have hbound (i : I) : thetaCapacity omega.form (fun _ => 0) (S i) ≤
        ENNReal.ofReal C * relCapacity V (E i) := by
      have hh := ThetaCapacityChartLocal.thetaCapacity_le_relCapacity_of_boundedOn
        (theta := omega.form) (V := fun _ => 0) e V hVt ρ hρV
        (c := 0) (d := 0) (L := A) (le_refl 0) hA
        (fun _ _ => ⟨le_rfl, le_rfl⟩) hρbound (S i) (hsource i)
      have hh' : thetaCapacity omega.form (fun _ => 0) (S i) ≤
          ENNReal.ofReal C * relCapacity V (e.val '' S i) := by
        simpa only [C, sub_self, zero_add] using hh
      exact hh'.trans (mul_le_mul_right (relCapacity_mono (himage i)) _)
    have hupper : Tendsto (fun i => ENNReal.ofReal C * relCapacity V (E i)) F (𝓝 0) := by
      simpa only [mul_zero] using ENNReal.Tendsto.const_mul
        (hcap V hVD T hT hTV (a / δ) (div_pos ha hδ)) (Or.inr ENNReal.ofReal_ne_top)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
      (fun _ => bot_le) hbound

end
end SGPT.Foundations.Analysis.Pending.ActualChartCapacityLiftConvergence
