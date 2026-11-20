import SGPT.Foundations.Analysis.Pending.ActualChartCapacityCompetitor

set_option autoImplicit false

/-! # One actual local-to-global operator controls all bounded local PSH gaps

Independent genuine negative-well and collar max construction. The common
operator, compact localization, and pointwise gap bound are produced;
actual mixed weak convergence and unbounded lower semicontinuity remain
separate consumers. All dimensions and the empty compact set are retained.
-/

open Set Filter TopologicalSpace
open scoped Topology ContDiff Manifold

namespace SGPT.Foundations.Analysis.Pending.ActualSynchronizedChartCapacityLift

open FirstPass FirstPass.PositiveClasses FirstPass.HolomorphicMaps
  FirstPass.AnalyticGluingData FirstPass.LocalPotentialPullback
  BedfordTaylor QuasiEquisingularCollarGluing

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]

/-- A single actual operator globalizes all normalized local PSH functions and
produces a common compact support for its pointwise-controlled differences. -/
theorem exists_synchronized_capacity_lift (omega : KahlerBackground n M)
    (e : ComplexChart n M) {D : Opens (ComplexModel n)}
    (hDt : (D : Set (ComplexModel n)) ⊆ e.val.target)
    {ρ : ComplexModel n → ℝ} (hρ : IsSmoothLocalPotential omega.form.val e D ρ)
    {K : Set (ComplexModel n)} (hK : IsCompact K) (hKD : K ⊆ D) :
    ∃ δ : ℝ, 0 < δ ∧ 3 * δ ≤ 1 ∧ ∃ (O : Set M) (T : Set (ComplexModel n))
      (lift : (ComplexModel n → ℝ) → M → EReal),
      IsOpen O ∧ e.val.symm '' K ⊆ O ∧
      O ⊆ e.val.source ∩ e.val ⁻¹' (D : Set (ComplexModel n)) ∧
      IsCompact T ∧ T ⊆ D ∧
      (∀ f, FirstPass.MongeAmpere.IsLocallyBoundedPshOn D f →
        (∀ z ∈ D, -1 ≤ f z ∧ f z ≤ 0) →
        IsThetaPshPotential omega.form.val (lift f) ∧
        (∀ x, (-1 : EReal) ≤ lift f x ∧ lift f x ≤ 0) ∧
        ∀ x ∈ O, lift f x = ((δ * f (e.val x) - δ : ℝ) : EReal)) ∧
      (∀ f g x, |(lift f x).toReal - (lift g x).toReal| ≤
        δ * |f (e.val x) - g (e.val x)|) ∧
      (∀ f g, (∀ z ∈ D, -1 ≤ f z ∧ f z ≤ 0) →
        (∀ z ∈ D, -1 ≤ g z ∧ g z ≤ 0) →
        ∀ x ∉ e.val.symm '' T, lift f x = lift g x) := by
  obtain ⟨δ, hδ, h3δ, χ, hχ, hχ01, hχsupp, hχK, hψ, hψ01⟩ :=
    ActualChartCapacityNegativeWell.exists_chart_negative_well omega e hDt hK hKD
  let U : Set M := e.val.source ∩ e.val ⁻¹' (D : Set (ComplexModel n))
  let O : Set M := U ∩ {x | (2 / 3 : ℝ) < χ x}
  have hU : IsOpen U := e.val.continuousOn.isOpen_inter_preimage e.val.open_source D.isOpen
  have hO : IsOpen O := hU.inter
    (isOpen_lt continuous_const (ProductTestForms.ChartSmooth.continuous hχ))
  have hKO : e.val.symm '' K ⊆ O := by
    rintro x ⟨z, hz, rfl⟩
    refine ⟨⟨e.val.map_target (hDt (hKD hz)), ?_⟩, ?_⟩
    · change e.val (e.val.symm z) ∈ (D : Set (ComplexModel n))
      rw [e.val.right_inv (hDt (hKD hz))]
      exact hKD hz
    · change (2 / 3 : ℝ) < χ (e.val.symm z)
      rw [hχK z hz]
      norm_num

  let T : Set (ComplexModel n) := e.val '' tsupport χ
  let lift : (ComplexModel n → ℝ) → M → EReal := fun f =>
    gluedMax U (fun x => ((δ * f (e.val x) - δ : ℝ) : EReal))
      (fun x => ((-3 * δ * χ x : ℝ) : EReal))
  have hT : IsCompact T := (HasCompactSupport.of_compactSpace χ).image_of_continuousOn
    (e.val.continuousOn.mono (fun _ hx => (hχsupp hx).1))
  have hTD : T ⊆ D := by
    rintro z ⟨x, hx, rfl⟩
    exact (hχsupp hx).2
  refine ⟨δ, hδ, h3δ, O, T, lift, hO, hKO, inter_subset_left, hT, hTD, ?_, ?_, ?_⟩
  · intro f hf hb
    let a : M → EReal := fun x => ((δ * f (e.val x) - δ : ℝ) : EReal)
    let ψ : M → EReal := fun x => ((-3 * δ * χ x : ℝ) : EReal)
    have hzero := (LocalPotentials.isThetaPshPotential_zero_iff omega.form).mpr omega.isSemipositive
    have hρpsh : PlurisubharmonicOn (fun z => (ρ z : EReal)) (D : Set (ComplexModel n)) := by
      simpa [chartFunction] using
        BoundedGlobalProduct.ThetaPlurisubharmonic.corrected_plurisubharmonicOn hzero.1 e hρ
    have hcorr : PlurisubharmonicOn (fun z => ((δ * f z - δ + ρ z : ℝ) : EReal))
        (D : Set (ComplexModel n)) := by
      have hh := ((hf.1.const_mul hδ).add_const (-δ)).add hρpsh
      simpa only [← EReal.coe_mul, ← EReal.coe_add, sub_eq_add_neg] using hh
    have haps : PlurisubharmonicOn (fun z => chartFunction a e z + (ρ z : EReal))
        (D : Set (ComplexModel n)) := by
      apply plurisubharmonicOn_congr D.isOpen hcorr
      intro z hz
      dsimp only [chartFunction, a]
      rw [e.val.right_inv (hDt hz), ← EReal.coe_add]
    have ha : ThetaPlurisubharmonicOn omega.form.val a U := by
      intro e' z hz hx
      have hxe' : e'.val.symm z ∈ e'.val.source := e'.val.map_target hz
      obtain ⟨W, r, hzW, hr, hp⟩ := OpensRestriction.exists_witness_of_chart
        e' e hxe' hx.1 hx.2 hρ haps
      rw [e'.val.right_inv hz] at hzW
      exact ⟨W, r, hzW, hr, hp⟩
    have hclosure : closure (tsupport χ) ⊆ U := by
      rw [(isClosed_tsupport χ).closure_eq]
      exact hχsupp
    have hcollar : ∀ x ∈ U \ tsupport χ, a x ≤ ψ x := by
      intro x hx
      have hx0 : χ x = 0 := by
        by_contra hne
        exact hx.2 (subset_tsupport χ hne)
      dsimp only [a, ψ]
      rw [hx0]
      apply EReal.coe_le_coe_iff.mpr
      have hh := hb (e.val x) hx.1.2
      nlinarith
    let v : M → EReal := gluedMax U a ψ
    have hv : IsThetaPshPotential omega.form.val v :=
      isThetaPshPotential_gluedMax hU hclosure hcollar ha hψ
    change IsThetaPshPotential omega.form.val v ∧
      (∀ x, (-1 : EReal) ≤ v x ∧ v x ≤ 0) ∧
      ∀ x ∈ O, v x = ((δ * f (e.val x) - δ : ℝ) : EReal)
    refine ⟨hv, fun x => ?_, fun x hx => ?_⟩
    · by_cases hx : x ∈ U
      · change (-1 : EReal) ≤ gluedMax U a ψ x ∧ gluedMax U a ψ x ≤ 0
        rw [gluedMax_eq_max hx]
        have ha0 : a x ≤ 0 := by
          dsimp only [a]
          change _ ≤ ((0 : ℝ) : EReal)
          apply EReal.coe_le_coe_iff.mpr
          have hh := hb (e.val x) hx.2
          nlinarith
        exact ⟨(hψ01 x).1.trans (le_max_right _ _), max_le ha0 (hψ01 x).2⟩
      · change (-1 : EReal) ≤ gluedMax U a ψ x ∧ gluedMax U a ψ x ≤ 0
        simp only [gluedMax, if_neg hx]
        exact hψ01 x
    · change gluedMax U a ψ x = _
      rw [gluedMax_eq_max hx.1]
      apply max_eq_left
      dsimp only [a, ψ]
      apply EReal.coe_le_coe_iff.mpr
      have hh := hb (e.val x) hx.1.2
      have hχx : (2 / 3 : ℝ) < χ x := hx.2
      nlinarith

  · intro f g x
    by_cases hx : x ∈ U
    · have hread (h : ComplexModel n → ℝ) : (lift h x).toReal =
          max (δ * h (e.val x) - δ) (-3 * δ * χ x) := by
        dsimp only [lift]
        rw [gluedMax_eq_max hx]
        have heq : max ((δ * h (e.val x) - δ : ℝ) : EReal)
            ((-3 * δ * χ x : ℝ) : EReal) =
            ((max (δ * h (e.val x) - δ) (-3 * δ * χ x) : ℝ) : EReal) :=
          (EReal.coe_strictMono.monotone.map_max).symm
        rw [heq, EReal.toReal_coe]
      rw [hread f, hread g]
      calc
        _ ≤ |(δ * f (e.val x) - δ) - (δ * g (e.val x) - δ)| :=
          abs_max_sub_max_le_abs _ _ _
        _ = δ * |f (e.val x) - g (e.val x)| := by
          rw [show (δ * f (e.val x) - δ) - (δ * g (e.val x) - δ) =
            δ * (f (e.val x) - g (e.val x)) by ring, abs_mul, abs_of_pos hδ]
    · simp only [lift, gluedMax, if_neg hx, sub_self, abs_zero]
      exact mul_nonneg hδ.le (abs_nonneg _)
  · intro f g hf hg x hx
    by_cases hxU : x ∈ U
    · have hxχ : x ∉ tsupport χ := by
        intro hs
        apply hx
        exact ⟨e.val x, ⟨x, hs, rfl⟩, e.val.left_inv hxU.1⟩
      have hχ0 : χ x = 0 := by
        by_contra hh
        exact hxχ (subset_tsupport χ hh)
      have hfle : ((δ * f (e.val x) - δ : ℝ) : EReal) ≤ 0 := by
        change _ ≤ ((0 : ℝ) : EReal)
        apply EReal.coe_le_coe_iff.mpr
        have hh := hf (e.val x) hxU.2
        nlinarith
      have hgle : ((δ * g (e.val x) - δ : ℝ) : EReal) ≤ 0 := by
        change _ ≤ ((0 : ℝ) : EReal)
        apply EReal.coe_le_coe_iff.mpr
        have hh := hg (e.val x) hxU.2
        nlinarith
      dsimp only [lift]
      rw [gluedMax_eq_max hxU, gluedMax_eq_max hxU]
      simp only [hχ0, mul_zero, EReal.coe_zero, max_eq_right hfle, max_eq_right hgle]
    · simp only [lift, gluedMax, if_neg hxU]

end
end SGPT.Foundations.Analysis.Pending.ActualSynchronizedChartCapacityLift
