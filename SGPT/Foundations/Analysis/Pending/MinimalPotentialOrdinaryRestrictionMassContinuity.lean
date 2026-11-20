import SGPT.Foundations.Analysis.Pending.MinimalPotentialRestrictionPositiveSeed
import SGPT.Foundations.Analysis.Pending.MixedSummandCapacityDomination
import SGPT.Foundations.Analysis.Pending.DivisorialDomination

set_option autoImplicit false

/-! # Actual ordinary moving-minimal restriction mass at a positive base -/

open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal ContDiff

namespace SGPT.Foundations.Analysis.Pending.MinimalPotentialOrdinaryRestrictionMassContinuity

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
  DiagonalMass MinimalPotentialRestrictionPositiveSeed MixedSummandCapacityDomination
  GlobalMultilinearExpansion ThetaPshConvexCombination AmbientConvexCurrent

noncomputable section

variable {n k : ℕ} {M V : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]
  [TopologicalSpace V] [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V]
  [MeasurableSpace V] [BorelSpace V] [CompactSpace V] [ConnectedSpace V]

/-- A true restricted strict seed and the selected positive mixed summand
produce finite ordinary mass bounds in the actual changing backgrounds. -/
theorem exists_ordinary_restriction_minimal_positive_base_mass_bound
    (omega : KahlerBackground n M) {ι : V → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (hpull : (ClosedRealOneOneForm.pullback hι omega.form).val.IsKahler)
    (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    (hgeneric : (⨅ y : V, lelongNumber (n := n) (thetaPshSupremum θ.val) (ι y)) = 0)
    {e : ℝ} (he : 0 < e) :
    ∃ h0 : IsThetaPshPotential (ClosedRealOneOneForm.pullback hι (θ + e • omega.form)).val
        (fun y => thetaPshSupremum (θ + e • omega.form).val (ι y)),
      ∃ hR : ∀ (r : ℝ), 0 < r →
        IsThetaPshPotential (ClosedRealOneOneForm.pullback hι (θ + (e + r) • omega.form)).val
          (fun y => thetaPshSupremum (θ + (e + r) • omega.form).val (ι y)),
      ∀ (r : ℝ) (hr : 0 < r),
        (diagonalPotentialMass (ClosedRealOneOneForm.pullback hι (θ + e • omega.form))
          (fun y => thetaPshSupremum (θ + e • omega.form).val (ι y)) h0).toReal ≤
          (diagonalPotentialMass (ClosedRealOneOneForm.pullback hι (θ + (e + r) • omega.form))
            (fun y => thetaPshSupremum (θ + (e + r) • omega.form).val (ι y)) (hR r hr)).toReal ∧
        (diagonalPotentialMass (ClosedRealOneOneForm.pullback hι (θ + (e + r) • omega.form))
          (fun y => thetaPshSupremum (θ + (e + r) • omega.form).val (ι y)) (hR r hr)).toReal ≤
          (diagonalPotentialMass (ClosedRealOneOneForm.pullback hι (θ + e • omega.form))
            (fun y => thetaPshSupremum (θ + e • omega.form).val (ι y)) h0).toReal /
              (e / 2 / (e / 2 + r)) ^ k := by
  classical
  let : Nonempty M := Nonempty.map ι inferInstance
  let ρ : KahlerBackground k V := ⟨ClosedRealOneOneForm.pullback hι omega.form, hpull⟩
  let η := ClosedRealOneOneForm.pullback hι (θ + e • omega.form)
  obtain ⟨h0, _⟩ := exists_positive_ordinary_restriction_minimal_add_smul
    omega hι hpull θ hbig hgeneric he
  let hR (r : ℝ) (hr : 0 < r) :=
    (exists_positive_ordinary_restriction_minimal_add_smul
      omega hι hpull θ hbig hgeneric (add_pos he hr)).choose
  obtain ⟨ψ, hψ, hψle, hψR⟩ := exists_restricted_strict_lower_seed_minimal_add_smul
    omega hι hpull θ hbig hgeneric he
  have hV := MinimalSingularityLelongVanishing.isThetaPshPotential_thetaPshSupremum θ hbig
  have hmin (r : ℝ) (hr : 0 < r) : IsThetaPshPotential
      (θ + r • omega.form).val (thetaPshSupremum (θ + r • omega.form).val) :=
    MinimalSingularityLelongVanishing.isThetaPshPotential_thetaPshSupremum _
      (PositiveCurrentAssembly.isBigClass_add_smul_of_isThetaPshPotential omega θ hV hr)
  refine ⟨h0, hR, fun r hr => ?_⟩
  let s : ℝ := e / 2 / (e / 2 + r)
  have hs : 0 < s := div_pos (half_pos he) (add_pos (half_pos he) hr)
  have hs1 : s < 1 := (div_lt_one (add_pos (half_pos he) hr)).mpr (by linarith)
  let W := thetaPshSupremum (θ + (e + r) • omega.form).val
  let Q := convexComb s W ψ
  have hc : s * r - (1 - s) * (e / 2) = 0 := by
    dsimp only [s]
    field_simp
    ring
  have hform : s • (θ + (e + r) • omega.form) +
      (1 - s) • (θ + e • omega.form - (e / 2) • omega.form) = θ + e • omega.form := by
    calc
      _ = θ + e • omega.form + (s * r - (1 - s) * (e / 2)) • omega.form := by module
      _ = _ := by rw [hc]; simp
  have hQ : IsThetaPshPotential (θ + e • omega.form).val Q := by
    simpa only [hform] using isThetaPshPotential_convexComb_forms
      (hmin (e + r) (add_pos he hr)) hψ hs hs1
  have hQ0 : Q ≤ 0 := by
    intro x
    exact add_nonpos
      (mul_nonpos_of_nonneg_of_nonpos (EReal.coe_nonneg.mpr hs.le)
        (thetaPshSupremum_le_zero _ x))
      (mul_nonpos_of_nonneg_of_nonpos (EReal.coe_nonneg.mpr (sub_nonneg.mpr hs1.le))
        ((hψle x).trans (thetaPshSupremum_le_zero _ x)))
  have hQle := le_thetaPshSupremum hQ hQ0
  let α : Bool → ClosedRealOneOneForm k V := fun b => if b then
    ClosedRealOneOneForm.pullback hι (θ + (e + r) • omega.form) else
    ClosedRealOneOneForm.pullback hι (θ + e • omega.form - (e / 2) • omega.form)
  let w : Bool → ℝ := fun b => if b then s else 1 - s
  let f : Bool → V → EReal := fun b => if b then (fun y => W (ι y)) else (fun y => ψ (ι y))
  have hT : (Finset.univ : Finset Bool).Nonempty := Finset.univ_nonempty
  have hw (b : Bool) : 0 < w b := by
    cases b <;> simp only [w, Bool.false_eq_true, ↓reduceIte] <;>
      first | exact hs | exact sub_pos.mpr hs1
  have hf (b : Bool) : IsThetaPshPotential (α b).val (f b) := by
    cases b
    · exact hψR
    · exact hR r hr
  have hα : sumForm Finset.univ w α = η := by
    simp only [sumForm, Fintype.sum_bool]
    change s • ClosedRealOneOneForm.pullback hι (θ + (e + r) • omega.form) +
      (1 - s) • ClosedRealOneOneForm.pullback hι
        (θ + e • omega.form - (e / 2) • omega.form) = η
    have hψform : θ + e • omega.form - (e / 2) • omega.form =
        θ + (e - e / 2) • omega.form := by module
    dsimp only [η]
    rw [hψform, NefCoreKahlerCurrent.pullback_add_smul,
      NefCoreKahlerCurrent.pullback_add_smul, NefCoreKahlerCurrent.pullback_add_smul]
    calc
      _ = ClosedRealOneOneForm.pullback hι θ +
          e • ClosedRealOneOneForm.pullback hι omega.form +
          (s * r - (1 - s) * (e / 2)) • ClosedRealOneOneForm.pullback hι omega.form := by module
      _ = _ := by rw [hc]; simp
  have hQR := isThetaPshPotential_sumPot hT hw hf
  rw [hα] at hQR
  have hQident : sumPot Finset.univ w f = fun y => Q (ι y) := by
    funext y
    simp only [sumPot, Fintype.sum_bool]
    rfl
  have hQRle : sumPot Finset.univ w f ≤
      fun y => thetaPshSupremum (θ + e • omega.form).val (ι y) := by
    rw [hQident]
    exact fun y => hQle (ι y)
  have hmono := diagonalPotentialMass_mono_of_kahler ρ hQR h0
    (MoreSingularOn.of_le fun y _ => hQRle y)
  have hsel := selectedMixedMeasure_apply_le_diagonal_sum hT hw hf
    (fun _ : Fin k => true) (fun _ => Finset.mem_univ _) Set.univ
  have hlow : ENNReal.ofReal (s ^ k) * diagonalPotentialMass
      (ClosedRealOneOneForm.pullback hι (θ + (e + r) • omega.form))
      (fun y => W (ι y)) (hR r hr) ≤
      diagonalPotentialMass η (sumPot Finset.univ w f) hQR := by
    simpa only [w, α, f, ↓reduceIte, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, hα, diagonalPotentialMass, diagonalPotentialMeasure] using hsel
  have hlarge : IsThetaPshPotential (θ + (e + r) • omega.form).val
      (thetaPshSupremum (θ + e • omega.form).val) := by
    have heq : θ + e • omega.form + r • omega.form = θ + (e + r) • omega.form := by module
    simpa only [heq] using LocalPotentials.isThetaPshPotential_add_of_semipositive
      (hmin e he) (KahlerDomination.isSemipositive_smul omega.isSemipositive hr.le)
  have hVW := le_thetaPshSupremum hlarge (thetaPshSupremum_le_zero _)
  have hρform : η + r • ρ.form =
      ClosedRealOneOneForm.pullback hι (θ + (e + r) • omega.form) := by
    rw [← NefCoreKahlerCurrent.pullback_add_smul]
    congr 1
    module
  have hR' : IsThetaPshPotential (η + r • ρ.form).val (fun y => W (ι y)) := by
    rw [hρform]
    exact hR r hr
  have hlower := DivisorialDomination.diagonalPotentialMass_le_of_le_add_smul
    ρ hr h0 hR' (fun y => hVW (ι y))
  have hlower' : diagonalPotentialMass η
      (fun y => thetaPshSupremum (θ + e • omega.form).val (ι y)) h0 ≤
      diagonalPotentialMass (ClosedRealOneOneForm.pullback hι (θ + (e + r) • omega.form))
        (fun y => W (ι y)) (hR r hr) := by
    change diagonalPotentialMass η _ h0 ≤ diagonalPotentialMass (η + r • ρ.form) _ hR' at hlower
    simpa only [hρform] using hlower
  have hfinite0 : diagonalPotentialMass η
      (fun y => thetaPshSupremum (θ + e • omega.form).val (ι y)) h0 ≠ ⊤ :=
    (MixedMass.globalMixedMass_lt_top ρ (fun _ : Fin k => h0.1)).ne
  have hfiniteR : diagonalPotentialMass
      (ClosedRealOneOneForm.pullback hι (θ + (e + r) • omega.form))
      (fun y => W (ι y)) (hR r hr) ≠ ⊤ :=
    (MixedMass.globalMixedMass_lt_top ρ (fun _ : Fin k => (hR r hr).1)).ne
  have hupper := ENNReal.toReal_mono hfinite0 (hlow.trans hmono)
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hs.le k)] at hupper
  refine ⟨ENNReal.toReal_mono hfiniteR hlower', ?_⟩
  exact (le_div_iff₀ (pow_pos hs k)).mpr (by simpa only [mul_comm] using hupper)

/-- The same produced witnesses give real and defining ENNReal ordinary
mass limits for every actual positive coefficient path and every filter. -/
theorem exists_tendsto_ordinary_restriction_minimal_positive_base_mass
    (omega : KahlerBackground n M) {ι : V → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (hpull : (ClosedRealOneOneForm.pullback hι omega.form).val.IsKahler)
    (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    (hgeneric : (⨅ y : V, lelongNumber (n := n) (thetaPshSupremum θ.val) (ι y)) = 0)
    {e : ℝ} (he : 0 < e) :
    ∃ h0 : IsThetaPshPotential (ClosedRealOneOneForm.pullback hι (θ + e • omega.form)).val
        (fun y => thetaPshSupremum (θ + e • omega.form).val (ι y)),
      ∃ hR : ∀ (r : ℝ), 0 < r →
        IsThetaPshPotential (ClosedRealOneOneForm.pullback hι (θ + (e + r) • omega.form)).val
          (fun y => thetaPshSupremum (θ + (e + r) • omega.form).val (ι y)),
      ∀ (I : Type*) (F : Filter I) (r : I → ℝ) (hr : ∀ i, 0 < r i),
        Tendsto r F (𝓝 0) →
          Tendsto (fun i => (diagonalPotentialMass
            (ClosedRealOneOneForm.pullback hι (θ + (e + r i) • omega.form))
            (fun y => thetaPshSupremum (θ + (e + r i) • omega.form).val (ι y))
            (hR (r i) (hr i))).toReal) F
            (𝓝 (diagonalPotentialMass (ClosedRealOneOneForm.pullback hι (θ + e • omega.form))
              (fun y => thetaPshSupremum (θ + e • omega.form).val (ι y)) h0).toReal) ∧
          Tendsto (fun i => diagonalPotentialMass
            (ClosedRealOneOneForm.pullback hι (θ + (e + r i) • omega.form))
            (fun y => thetaPshSupremum (θ + (e + r i) • omega.form).val (ι y))
            (hR (r i) (hr i))) F
            (𝓝 (diagonalPotentialMass (ClosedRealOneOneForm.pullback hι (θ + e • omega.form))
              (fun y => thetaPshSupremum (θ + e • omega.form).val (ι y)) h0)) := by
  obtain ⟨h0, hR, hbound⟩ := exists_ordinary_restriction_minimal_positive_base_mass_bound
    omega hι hpull θ hbig hgeneric he
  let ρ : KahlerBackground k V := ⟨ClosedRealOneOneForm.pullback hι omega.form, hpull⟩
  let M0 := diagonalPotentialMass (ClosedRealOneOneForm.pullback hι (θ + e • omega.form))
    (fun y => thetaPshSupremum (θ + e • omega.form).val (ι y)) h0
  let MR (r : ℝ) (hr : 0 < r) := diagonalPotentialMass
    (ClosedRealOneOneForm.pullback hι (θ + (e + r) • omega.form))
    (fun y => thetaPshSupremum (θ + (e + r) • omega.form).val (ι y)) (hR r hr)
  refine ⟨h0, hR, fun I F r hr hrlim => ?_⟩
  have hδlim : Tendsto (fun _ : I => e / 2) F (𝓝 (e / 2)) := tendsto_const_nhds
  have hs : Tendsto (fun i => e / 2 / (e / 2 + r i)) F (𝓝 (1 : ℝ)) := by
    have hden : Tendsto (fun i => e / 2 + r i) F (𝓝 (e / 2)) := by
      simpa only [add_zero] using hδlim.add hrlim
    have hh : Tendsto (fun i => e / 2 * (e / 2 + r i)⁻¹) F
        (𝓝 (e / 2 * (e / 2)⁻¹)) := hδlim.mul (hden.inv₀ (half_pos he).ne')
    rw [mul_inv_cancel₀ (half_pos he).ne'] at hh
    simpa only [div_eq_mul_inv] using hh
  have hupper : Tendsto (fun i => M0.toReal / (e / 2 / (e / 2 + r i)) ^ k)
      F (𝓝 M0.toReal) := by
    simpa only [div_eq_mul_inv, one_pow, inv_one, mul_one] using
      (tendsto_const_nhds (x := M0.toReal)).mul ((hs.pow k).inv₀ (by simp))
  have hreal : Tendsto (fun i => (MR (r i) (hr i)).toReal) F (𝓝 M0.toReal) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
      (fun i => (hbound (r i) (hr i)).1) (fun i => (hbound (r i) (hr i)).2)
  have hrec0 : ENNReal.ofReal M0.toReal = M0 :=
    ENNReal.ofReal_toReal (MixedMass.globalMixedMass_lt_top ρ (fun _ : Fin k => h0.1)).ne
  have hrec (i : I) : ENNReal.ofReal (MR (r i) (hr i)).toReal = MR (r i) (hr i) :=
    ENNReal.ofReal_toReal
      (MixedMass.globalMixedMass_lt_top ρ (fun _ : Fin k => (hR (r i) (hr i)).1)).ne
  have henn := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hreal
  simp only [Function.comp_def, hrec, hrec0] at henn
  exact ⟨hreal, henn⟩

end
end SGPT.Foundations.Analysis.Pending.MinimalPotentialOrdinaryRestrictionMassContinuity
