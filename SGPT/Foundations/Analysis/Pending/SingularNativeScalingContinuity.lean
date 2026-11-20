import SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityInterpolation
import SGPT.Foundations.Analysis.Pending.SingularNativeCommonBackground

set_option autoImplicit false

/-! # Actual admissible scaling continuity in the original background

SGPT PDF0232--0233 Lemma 6.2.3, zero-limit consequence and actual
semipositive enlargement. Independent fixed-Kahler-minimal-interpolation
adaptation, with genuine common-background transport and eventual-set
filter recovery. No quantitative uniform linear estimate is claimed.
-/

open Set Filter
open scoped ENNReal Topology

namespace SGPT.Foundations.Analysis.Pending.SingularNativeScalingContinuity

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
  ThetaPshConvexCombination ThetaPshL1Topology SingularMinimalCanonicalRay
  SingularCanonicalSingularityDistance SingularCanonicalSingularityInterpolation
  SingularNativeCommonBackground

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

/-- Actual compact domination, genuine minimal interpolation and actual
common-background transport produce the original admissible scaling limit. -/
theorem tendsto_native_admissible_scaling_one
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    {u : M → EReal} (hu : IsThetaPshPotential θ.val u)
    {I : Type*} (F : Filter I) (t : I → Ioo (0 : ℝ) 1)
    (ht : Tendsto (fun i => (t i).val) F (𝓝 0))
    (hscaled : ∀ i, IsThetaPshPotential θ.val
      (fun x => (((1 - (t i).val : ℝ) : EReal) * u x))) :
    Tendsto (fun i => (⟨fun x => (((1 - (t i).val : ℝ) : EReal) * u x),
      hscaled i⟩ : ThetaPshL1 θ.val)) F
      (@nhds (ThetaPshL1 θ.val)
        (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace
        ⟨u, hu⟩) := by
  obtain ⟨A, hA, hsemi⟩ := KahlerDomination.exists_pos_isSemipositive_add_smul omega (-θ)
  let κ : KahlerBackground n M := KahlerBackground.smul hA omega
  have hdiff : (κ.form - θ).val.IsSemipositive := by
    simpa only [κ, KahlerBackground.smul_form, sub_eq_add_neg, add_comm] using hsemi
  have hform : θ + (κ.form - θ) = κ.form := by abel
  have huκ : IsThetaPshPotential κ.form.val u := by
    simpa only [hform] using LocalPotentials.isThetaPshPotential_add_of_semipositive hu hdiff
  have hscaledκ (i : I) : IsThetaPshPotential κ.form.val
      (fun x => (((1 - (t i).val : ℝ) : EReal) * u x)) := by
    simpa only [hform] using
      LocalPotentials.isThetaPshPotential_add_of_semipositive (hscaled i) hdiff
  have hκ := PluripolarCapacityDichotomy.isBigClass_kahler κ
  have hVzero : thetaPshSupremum κ.form.val = (fun _ : M => (0 : EReal)) :=
    le_antisymm (thetaPshSupremum_le_zero κ.form.val)
      (le_thetaPshSupremum (PluripolarCapacityDichotomy.isThetaPshPotential_zero κ) le_rfl)
  have hlimκ : Tendsto (fun i => (⟨fun x => (((1 - (t i).val : ℝ) : EReal) * u x),
      hscaledκ i⟩ : ThetaPshL1 κ.form.val)) F
      (@nhds (ThetaPshL1 κ.form.val)
        (singularityPseudoMetricSpace omega κ.form hκ).toUniformSpace.toTopologicalSpace
        ⟨u, huκ⟩) := by
    have h := tendsto_native_convexComb_minimal_zero omega κ.form hκ ⟨u, huκ⟩ F t ht
    dsimp only at h
    refine h.congr' (Eventually.of_forall fun i => ?_)
    apply Subtype.ext
    funext x
    simp only [convexComb, hVzero, mul_zero, add_zero]
  exact (tendsto_native_iff_common_backgrounds omega θ κ.form hbig hκ F
    hscaled hu hscaledκ huκ).mpr hlimκ

/-- Eventual genuine admissibility suffices for the actual raw right-hand
scaling distances, both defining extended and finite real, to tend to zero. -/
theorem tendsto_singularityDistance_admissible_scaling_right
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    {u : M → EReal} (hu : IsThetaPshPotential θ.val u)
    (hscaled : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      IsThetaPshPotential θ.val (fun x => (((1 - ε : ℝ) : EReal) * u x))) :
    Tendsto (fun ε : ℝ => singularityDistance omega θ hbig
      (fun x => (((1 - ε : ℝ) : EReal) * u x)) u) (𝓝[>] 0) (𝓝 (0 : EReal)) ∧
    Tendsto (fun ε : ℝ => (singularityDistance omega θ hbig
      (fun x => (((1 - ε : ℝ) : EReal) * u x)) u).toReal) (𝓝[>] 0) (𝓝 (0 : ℝ)) := by
  let S : Set ℝ := {ε | ε ∈ Ioo (0 : ℝ) 1 ∧
    IsThetaPshPotential θ.val (fun x => (((1 - ε : ℝ) : EReal) * u x))}
  have hS : S ∈ (𝓝[>] (0 : ℝ)) := by
    have hgt : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε := self_mem_nhdsWithin
    have hlt : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε < 1 :=
      (eventually_lt_nhds (show (0 : ℝ) < 1 from zero_lt_one)).filter_mono nhdsWithin_le_nhds
    filter_upwards [hgt, hlt, hscaled] with ε hε₀ hε₁ hεpsh
    exact ⟨⟨hε₀, hε₁⟩, hεpsh⟩
  let G : Filter S := comap ((↑) : S → ℝ) (𝓝[>] (0 : ℝ))
  let t : S → Ioo (0 : ℝ) 1 := fun ε => ⟨ε.val, ε.property.1⟩
  have ht : Tendsto (fun ε : S => (t ε).val) G (𝓝 (0 : ℝ)) :=
    tendsto_comap.mono_right nhdsWithin_le_nhds
  have hψ (ε : S) : IsThetaPshPotential θ.val
      (fun x => (((1 - ε.val : ℝ) : EReal) * u x)) := ε.property.2
  have hnative := tendsto_native_admissible_scaling_one omega θ hbig hu G t ht hψ
  let : PseudoMetricSpace (ThetaPshL1 θ.val) := singularityPseudoMetricSpace omega θ hbig
  let : TopologicalSpace (ThetaPshL1 θ.val) :=
    (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace
  let w : S → ThetaPshL1 θ.val := fun ε =>
    ⟨fun x => (((1 - ε.val : ℝ) : EReal) * u x), hψ ε⟩
  let U : ThetaPshL1 θ.val := ⟨u, hu⟩
  have hw : Tendsto w G (𝓝 U) := hnative
  have hreal : Tendsto (fun ε : S => (singularityDistance omega θ hbig
      (fun x => (((1 - ε.val : ℝ) : EReal) * u x)) u).toReal) G (𝓝 (0 : ℝ)) := by
    have h := tendsto_iff_dist_tendsto_zero.mp hw
    have he : (fun ε : S => dist (w ε) U) = fun ε => (singularityDistance omega θ hbig
        (fun x => (((1 - ε.val : ℝ) : EReal) * u x)) u).toReal :=
      funext fun ε => dist_eq_singularityDistance_toReal omega θ hbig (w ε) U
    exact he ▸ h
  have hfinite (ε : S) : singularityDistance omega θ hbig
      (fun x => (((1 - ε.val : ℝ) : EReal) * u x)) u =
      ((singularityDistance omega θ hbig
        (fun x => (((1 - ε.val : ℝ) : EReal) * u x)) u).toReal : EReal) := by
    obtain ⟨m, _, _, _, hD⟩ := exists_tendsto_singularityDistance omega θ hbig (hψ ε) hu
    simp only [hD, EReal.toReal_coe]
  have hextended : Tendsto (fun ε : S => singularityDistance omega θ hbig
      (fun x => (((1 - ε.val : ℝ) : EReal) * u x)) u) G (𝓝 (0 : EReal)) := by
    simpa only [← hfinite, EReal.coe_zero] using EReal.tendsto_coe.mpr hreal
  have hrange : range ((↑) : S → ℝ) ∈ (𝓝[>] (0 : ℝ)) := by
    simpa only [Subtype.range_val] using hS
  exact ⟨(tendsto_comap'_iff hrange).mp hextended, (tendsto_comap'_iff hrange).mp hreal⟩

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
private theorem isBigClass_add_semipositive
    {θ η : ClosedRealOneOneForm n M}
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ)) (hη : η.val.IsSemipositive) :
    IsBigClass (RealBottChern.ofRepresentative (θ + η)) := by
  obtain ⟨T⟩ := hbig
  refine ⟨{
    representative := T.representative + η
    represents := by
      rw [RealBottChern.ofRepresentative_add, T.represents, RealBottChern.ofRepresentative_add]
    potential := T.potential
    lowerBound := T.lowerBound
    strictlyPsh := ?_ }⟩
  have hform : T.representative + η - T.lowerBound.form =
      (T.representative - T.lowerBound.form) + η := by abel
  rw [hform]
  exact LocalPotentials.isThetaPshPotential_add_of_semipositive T.strictlyPsh hη

/-- Actual semipositive enlargement produces its own big-class witness and
the genuine raw right-hand scaling limits, rather than receiving them. -/
theorem exists_tendsto_singularityDistance_admissible_scaling_enlarged_right
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    (η : ClosedRealOneOneForm n M) (hη : η.val.IsSemipositive)
    {u : M → EReal} (hu : IsThetaPshPotential θ.val u)
    (hscaled : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      IsThetaPshPotential θ.val (fun x => (((1 - ε : ℝ) : EReal) * u x))) :
    ∃ hγ : IsBigClass (RealBottChern.ofRepresentative (θ + η)),
      Tendsto (fun ε : ℝ => singularityDistance omega (θ + η) hγ
        (fun x => (((1 - ε : ℝ) : EReal) * u x)) u) (𝓝[>] 0) (𝓝 (0 : EReal)) ∧
      Tendsto (fun ε : ℝ => (singularityDistance omega (θ + η) hγ
        (fun x => (((1 - ε : ℝ) : EReal) * u x)) u).toReal) (𝓝[>] 0) (𝓝 (0 : ℝ)) := by
  have hγ := isBigClass_add_semipositive hbig hη
  have huγ := LocalPotentials.isThetaPshPotential_add_of_semipositive hu hη
  exact ⟨hγ, tendsto_singularityDistance_admissible_scaling_right omega (θ + η) hγ huγ
    (hscaled.mono fun _ hε => LocalPotentials.isThetaPshPotential_add_of_semipositive hε hη)⟩

end
end SGPT.Foundations.Analysis.Pending.SingularNativeScalingContinuity
