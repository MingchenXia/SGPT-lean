import SGPT.Foundations.Analysis.Pending.SingularMinimalBackgroundPositive
import SGPT.Foundations.Analysis.Pending.NonPluripolarConvexCombLower
import SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityOrderedMassCriterion

set_option autoImplicit false

/-! # Actual minimal potentials converge in one fixed genuine enlargement -/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.MinimalPotentialFixedEnlargementNativeLimit

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
  DiagonalMass SingularMinimalCanonicalRay SingularMinimalBackgroundNegative
  ThetaPshConvexCombination AmbientConvexCurrent SingularCanonicalSingularityDistance
  ThetaPshL1Topology

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M] [ConnectedSpace M]


/-- Genuine strict geometry internally produces fixed-background witnesses and
finite actual top-mass bounds before all positive coefficient paths. -/
theorem exists_fixed_enlargement_minimal_mass_bound
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ)) :
    let Γ := θ + omega.form
    ∃ δ : ℝ, 0 < δ ∧
      ∃ hV : IsThetaPshPotential Γ.val (thetaPshSupremum θ.val),
      ∃ _hplus : ∀ (ε : ℝ), 0 < ε → IsBigClass (RealBottChern.ofRepresentative (θ + ε • omega.form)),
      ∃ hW : ∀ (ε : ℝ), 0 < ε → ε ≤ 1 →
        IsThetaPshPotential Γ.val (thetaPshSupremum (θ + ε • omega.form).val),
      ∀ (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1),
        (diagonalPotentialMass Γ (thetaPshSupremum θ.val) hV).toReal ≤
          (diagonalPotentialMass Γ (thetaPshSupremum (θ + ε • omega.form).val) (hW ε hε hε1)).toReal ∧
        (diagonalPotentialMass Γ (thetaPshSupremum (θ + ε • omega.form).val) (hW ε hε hε1)).toReal ≤
          (diagonalPotentialMass Γ (thetaPshSupremum θ.val) hV).toReal /
            (δ / (δ + ε)) ^ n := by
  let Γ := θ + omega.form
  have hVθ : IsThetaPshPotential θ.val (thetaPshSupremum θ.val) :=
    (isModelPotential_thetaPshSupremum omega θ hbig).plurisubharmonic
  have hV : IsThetaPshPotential Γ.val (thetaPshSupremum θ.val) :=
    LocalPotentials.isThetaPshPotential_add_of_semipositive hVθ omega.isSemipositive
  let hplus : ∀ (ε : ℝ), 0 < ε → IsBigClass (RealBottChern.ofRepresentative (θ + ε • omega.form)) :=
    fun ε hε => PositiveCurrentAssembly.isBigClass_add_smul_of_isThetaPshPotential omega θ hVθ hε
  have hW (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
      IsThetaPshPotential Γ.val (thetaPshSupremum (θ + ε • omega.form).val) := by
    have hform : θ + ε • omega.form + (1 - ε) • omega.form = Γ := by
      dsimp only [Γ]
      module
    have h := LocalPotentials.isThetaPshPotential_add_of_semipositive
      (isModelPotential_thetaPshSupremum omega (θ + ε • omega.form) (hplus ε hε)).plurisubharmonic
      (KahlerDomination.isSemipositive_smul omega.isSemipositive (sub_nonneg.mpr hε1))
    simpa only [hform] using h
  obtain ⟨δ, hδ, ψ, hψ, hψ0, _⟩ := exists_minimal_sub_smul_convex_barrier omega θ hbig
  have hψΓ : IsThetaPshPotential Γ.val ψ := by
    have hform : θ - δ • omega.form + (1 + δ) • omega.form = Γ := by
      dsimp only [Γ]
      module
    have h := LocalPotentials.isThetaPshPotential_add_of_semipositive hψ
      (KahlerDomination.isSemipositive_smul omega.isSemipositive (by linarith : 0 ≤ 1 + δ))
    simpa only [hform] using h
  refine ⟨δ, hδ, hV, hplus, hW, fun ε hε hε1 => ?_⟩
  let s : ℝ := δ / (δ + ε)
  have hs : 0 < s := div_pos hδ (add_pos hδ hε)
  have hs1 : s < 1 := (div_lt_one (add_pos hδ hε)).mpr (by linarith)
  let W := thetaPshSupremum (θ + ε • omega.form).val
  have hp : IsThetaPshPotential (θ + ε • omega.form).val W :=
    (isModelPotential_thetaPshSupremum omega (θ + ε • omega.form) (hplus ε hε)).plurisubharmonic
  have hcoeff : s * ε - (1 - s) * δ = 0 := by
    dsimp only [s]
    field_simp
    ring
  have hform : s • (θ + ε • omega.form) + (1 - s) • (θ - δ • omega.form) = θ := by
    calc
      _ = (s + (1 - s)) • θ + (s * ε - (1 - s) * δ) • omega.form := by module
      _ = θ := by rw [hcoeff]; simp
  have hqθ : IsThetaPshPotential θ.val (convexComb s W ψ) := by
    have h := isThetaPshPotential_convexComb_forms hp hψ hs hs1
    simpa only [hform] using h
  have hq0 : convexComb s W ψ ≤ 0 := by
    intro x
    exact add_nonpos
      (mul_nonpos_of_nonneg_of_nonpos (EReal.coe_nonneg.mpr hs.le)
        (thetaPshSupremum_le_zero _ x))
      (mul_nonpos_of_nonneg_of_nonpos (EReal.coe_nonneg.mpr (sub_nonneg.mpr hs1.le)) (hψ0 x))
  have hqV : convexComb s W ψ ≤ thetaPshSupremum θ.val := le_thetaPshSupremum hqθ hq0
  have hVW : thetaPshSupremum θ.val ≤ W :=
    le_thetaPshSupremum
      (LocalPotentials.isThetaPshPotential_add_of_semipositive hVθ
        (KahlerDomination.isSemipositive_smul omega.isSemipositive hε.le))
      (thetaPshSupremum_le_zero θ.val)
  have hqΓ : IsThetaPshPotential Γ.val (convexComb s W ψ) :=
    LocalPotentials.isThetaPshPotential_add_of_semipositive hqθ omega.isSemipositive
  have hMW : diagonalPotentialMass Γ (thetaPshSupremum θ.val) hV ≤
      diagonalPotentialMass Γ W (hW ε hε hε1) :=
    diagonalPotentialMass_mono_of_kahler omega hV (hW ε hε hε1)
      (MoreSingularOn.of_le fun x _ => hVW x)
  have hMQ : diagonalPotentialMass Γ (convexComb s W ψ) hqΓ ≤
      diagonalPotentialMass Γ (thetaPshSupremum θ.val) hV :=
    diagonalPotentialMass_mono_of_kahler omega hqΓ hV
      (MoreSingularOn.of_le fun x _ => hqV x)
  have hlow := NonPluripolarConvexCombLower.ofReal_pow_smul_diagonalPotentialMeasure_le_convexComb
    Γ (hW ε hε hε1) hψΓ hs hs1 hqΓ univ
  change ENNReal.ofReal (s ^ n) * diagonalPotentialMass Γ W (hW ε hε hε1) ≤
    diagonalPotentialMass Γ (convexComb s W ψ) hqΓ at hlow
  have hfiniteV : diagonalPotentialMass Γ (thetaPshSupremum θ.val) hV ≠ ⊤ :=
    (MixedMass.globalMixedMass_lt_top omega (fun _ : Fin n => hV.1)).ne
  have hfiniteW : diagonalPotentialMass Γ W (hW ε hε hε1) ≠ ⊤ :=
    (MixedMass.globalMixedMass_lt_top omega (fun _ : Fin n => (hW ε hε hε1).1)).ne
  have hreal := ENNReal.toReal_mono hfiniteV (hlow.trans hMQ)
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hs.le n)] at hreal
  refine ⟨ENNReal.toReal_mono hfiniteW hMW, ?_⟩
  exact (le_div_iff₀ (pow_pos hs n)).mpr (by simpa only [mul_comm] using hreal)


/-- Actual geometry is chosen before all filters; finite real mass squeeze and
the genuine ordered native criterion produce the fixed-background minimal limit. -/
theorem exists_native_minimal_add_smul_fixed_enlargement
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ)) :
    let Γ := θ + omega.form
    ∃ hΓ : IsBigClass (RealBottChern.ofRepresentative Γ),
    ∃ hV : IsThetaPshPotential Γ.val (thetaPshSupremum θ.val),
    ∃ _hplus : ∀ (ε : ℝ), 0 < ε → IsBigClass (RealBottChern.ofRepresentative (θ + ε • omega.form)),
    ∃ hW : ∀ (ε : ℝ), 0 < ε → ε ≤ 1 →
        IsThetaPshPotential Γ.val (thetaPshSupremum (θ + ε • omega.form).val),
    ∀ (I : Type*) (F : Filter I) (ε : I → ℝ)
      (hεpos : ∀ i, 0 < ε i) (hε1 : ∀ i, ε i ≤ 1),
      Tendsto ε F (𝓝 0) →
      Tendsto (fun i => (⟨thetaPshSupremum (θ + ε i • omega.form).val,
        hW (ε i) (hεpos i) (hε1 i)⟩ : ThetaPshL1 Γ.val)) F
        (@nhds (ThetaPshL1 Γ.val)
          (singularityPseudoMetricSpace omega Γ hΓ).toUniformSpace.toTopologicalSpace
          ⟨thetaPshSupremum θ.val, hV⟩) := by
  obtain ⟨δ, hδ, hV, hplus, hW, hbound⟩ :=
    exists_fixed_enlargement_minimal_mass_bound omega θ hbig
  let Γ := θ + omega.form
  have hVθ : IsThetaPshPotential θ.val (thetaPshSupremum θ.val) :=
    (isModelPotential_thetaPshSupremum omega θ hbig).plurisubharmonic
  have hΓ : IsBigClass (RealBottChern.ofRepresentative Γ) := by
    simpa only [one_smul] using
      PositiveCurrentAssembly.isBigClass_add_smul_of_isThetaPshPotential omega θ hVθ zero_lt_one
  have hVpos : 0 < diagonalPotentialMass Γ (thetaPshSupremum θ.val) hV := by
    have hm := AmbientMassBackgroundMonotone.diagonalPotentialMass_le_add_smul
      omega.isSemipositive zero_lt_one hVθ
      (LocalPotentials.isThetaPshPotential_add_of_semipositive hVθ
        (KahlerDomination.isSemipositive_smul omega.isSemipositive zero_le_one))
    simpa only [one_smul] using (isModelPotential_thetaPshSupremum omega θ hbig).positive_mass.trans_le hm
  refine ⟨hΓ, hV, hplus, hW, fun I F ε hεpos hε1 hεlim => ?_⟩
  let V := thetaPshSupremum θ.val
  let W : I → M → EReal := fun i => thetaPshSupremum (θ + ε i • omega.form).val
  have hVW (i : I) : V ≤ W i :=
    le_thetaPshSupremum
      (LocalPotentials.isThetaPshPotential_add_of_semipositive hVθ
        (KahlerDomination.isSemipositive_smul omega.isSemipositive (hεpos i).le))
      (thetaPshSupremum_le_zero θ.val)
  let m : ℝ := (diagonalPotentialMass Γ V hV).toReal
  have hδlim : Tendsto (fun _ : I => δ) F (𝓝 δ) := tendsto_const_nhds
  have hs : Tendsto (fun i => δ / (δ + ε i)) F (𝓝 (1 : ℝ)) := by
    have hden : Tendsto (fun i => δ + ε i) F (𝓝 δ) := by
      simpa only [add_zero] using hδlim.add hεlim
    simpa only [div_eq_mul_inv, mul_inv_cancel₀ hδ.ne'] using
      hδlim.mul (hden.inv₀ hδ.ne')
  have hupper : Tendsto (fun i => m / (δ / (δ + ε i)) ^ n) F (𝓝 m) := by
    simpa only [div_eq_mul_inv, one_pow, inv_one, mul_one] using
      (tendsto_const_nhds (x := m)).mul ((hs.pow n).inv₀ (by simp))
  have hreal : Tendsto (fun i => (diagonalPotentialMass Γ (W i)
      (hW (ε i) (hεpos i) (hε1 i))).toReal) F (𝓝 m) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
      (fun i => (hbound (ε i) (hεpos i) (hε1 i)).1)
      (fun i => (hbound (ε i) (hεpos i) (hε1 i)).2)
  have hrec {p : M → EReal} (hp : IsThetaPshPotential Γ.val p) :
      ENNReal.ofReal (diagonalPotentialMass Γ p hp).toReal = diagonalPotentialMass Γ p hp :=
    ENNReal.ofReal_toReal (MixedMass.globalMixedMass_lt_top omega (fun _ : Fin n => hp.1)).ne
  have hmass : Tendsto (fun i => diagonalPotentialMass Γ (W i)
      (hW (ε i) (hεpos i) (hε1 i))) F (𝓝 (diagonalPotentialMass Γ V hV)) := by
    have hh := (ENNReal.continuous_ofReal.tendsto m).comp hreal
    simpa only [m, Function.comp_def, hrec] using hh
  exact (SingularCanonicalSingularityOrderedMassCriterion.tendsto_native_iff_diagonalPotentialMass_of_le
    omega Γ hΓ F (fun i => ⟨W i, hW (ε i) (hεpos i) (hε1 i)⟩) ⟨V, hV⟩ hVW hVpos).mpr hmass

end
end SGPT.Foundations.Analysis.Pending.MinimalPotentialFixedEnlargementNativeLimit
