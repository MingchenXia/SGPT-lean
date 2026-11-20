import SGPT.Foundations.Analysis.Pending.MinimalPotentialFixedEnlargementNativeLimit
import SGPT.Foundations.Analysis.Pending.SingularNativeCommonBackground

set_option autoImplicit false

/-! # Actual minimal-potential right limits in every genuine common native carrier -/

open Set Filter
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.MinimalPotentialCommonBackgroundNativeLimit

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
  SingularCanonicalSingularityDistance ThetaPshL1Topology MinimalPotentialFixedEnlargementNativeLimit

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M] [ConnectedSpace M]


/-- The internally produced fixed enlargement native limit genuinely transports
to any actual common Big carrier of the same minimal potentials. -/
theorem tendsto_native_minimal_add_smul_in_common_background
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    (β : ClosedRealOneOneForm n M) (hβ : IsBigClass (RealBottChern.ofRepresentative β))
    {I : Type*} (F : Filter I) (ε : I → ℝ)
    (hεpos : ∀ i, 0 < ε i) (hε1 : ∀ i, ε i ≤ 1)
    (hεlim : Tendsto ε F (𝓝 0))
    (hVβ : IsThetaPshPotential β.val (thetaPshSupremum θ.val))
    (hWβ : ∀ i, IsThetaPshPotential β.val (thetaPshSupremum (θ + ε i • omega.form).val)) :
    Tendsto (fun i => (⟨thetaPshSupremum (θ + ε i • omega.form).val, hWβ i⟩ : ThetaPshL1 β.val)) F
      (@nhds (ThetaPshL1 β.val)
        (singularityPseudoMetricSpace omega β hβ).toUniformSpace.toTopologicalSpace
        ⟨thetaPshSupremum θ.val, hVβ⟩) := by
  obtain ⟨hΓ, hVΓ, _, hWΓ, hlim⟩ := exists_native_minimal_add_smul_fixed_enlargement omega θ hbig
  exact (SingularNativeCommonBackground.tendsto_native_iff_common_backgrounds
    omega (θ + omega.form) β hΓ hβ F
    (fun i => hWΓ (ε i) (hεpos i) (hε1 i)) hVΓ hWβ hVβ).mp
    (hlim I F ε hεpos hε1 hεlim)

/-- The actual real right-neighborhood path in a given genuine common native
carrier, with its total genuine witness internally produced. -/
theorem exists_tendsto_native_minimal_add_smul_right_in_common_background
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    (β : ClosedRealOneOneForm n M) (hβ : IsBigClass (RealBottChern.ofRepresentative β))
    (hVβ : IsThetaPshPotential β.val (thetaPshSupremum θ.val))
    (hWβ : ∀ (ε : ℝ), 0 < ε → ε ≤ 1 →
      IsThetaPshPotential β.val (thetaPshSupremum (θ + ε • omega.form).val)) :
    let W : ℝ → M → EReal := fun ε => if 0 < ε ∧ ε ≤ 1 then
      thetaPshSupremum (θ + ε • omega.form).val else thetaPshSupremum θ.val
    ∃ hW : ∀ ε, IsThetaPshPotential β.val (W ε),
      Tendsto (fun ε => (⟨W ε, hW ε⟩ : ThetaPshL1 β.val)) (𝓝[>] (0 : ℝ))
        (@nhds (ThetaPshL1 β.val)
          (singularityPseudoMetricSpace omega β hβ).toUniformSpace.toTopologicalSpace
          ⟨thetaPshSupremum θ.val, hVβ⟩) := by
  classical
  let W : ℝ → M → EReal := fun ε => if 0 < ε ∧ ε ≤ 1 then
    thetaPshSupremum (θ + ε • omega.form).val else thetaPshSupremum θ.val
  have hW (ε : ℝ) : IsThetaPshPotential β.val (W ε) := by
    dsimp only [W]
    split_ifs with hε
    · exact hWβ ε hε.1 hε.2
    · exact hVβ
  let r : ℝ → ℝ := fun ε => if 0 < ε ∧ ε ≤ 1 then ε else 1 / 2
  have hrpos (ε : ℝ) : 0 < r ε := by
    dsimp only [r]
    split_ifs with hε
    · exact hε.1
    · norm_num
  have hr1 (ε : ℝ) : r ε ≤ 1 := by
    dsimp only [r]
    split_ifs with hε
    · exact hε.2
    · norm_num
  have hnear : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε ∧ ε ≤ 1 := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
    exact ⟨hε.1, hε.2.le⟩
  have hrlim : Tendsto r (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    (tendsto_id.mono_left nhdsWithin_le_nhds).congr' (by
      filter_upwards [hnear] with ε hε
      simp only [r, if_pos hε, id_eq])
  have hlim := tendsto_native_minimal_add_smul_in_common_background
    omega θ hbig β hβ (𝓝[>] (0 : ℝ)) r hrpos hr1 hrlim hVβ
    (fun ε => hWβ (r ε) (hrpos ε) (hr1 ε))
  refine ⟨hW, hlim.congr' ?_⟩
  filter_upwards [hnear] with ε hε
  apply Subtype.ext
  simp only [r, if_pos hε]

end
end SGPT.Foundations.Analysis.Pending.MinimalPotentialCommonBackgroundNativeLimit
