import SGPT.Foundations.Analysis.Pending.SingularBoundedRayJoinStageOrder

set_option autoImplicit false

/-! # Produced uniform bounds for actual bounded-ray join stages -/

open Set

namespace SGPT.Foundations.Analysis.Pending.SingularBoundedRayJoinStageBounds

open FirstPass FirstPass.PositiveClasses RelativeEnergy RelativeDarvasDistance
  RelativePreceqClasses RelativePreceqRays SingularBoundedRayJoinStages
  FiniteUpperGapGeodesicSupremum

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M] {θ : ClosedRealOneOneForm n M}
  {φ : M → EReal} {hφ : IsModelPotential θ φ} {ℓ ℓ' : ℝ → M → EReal}

/-- Actual time-one source suprema internally produce the uniform pointwise model bound for every actual closed join stage, including poles and singular references. -/
theorem joinStage_le_model_add_linear (omega : KahlerBackground n M)
    (hℓ : IsBoundedRayFromModel θ φ hφ ℓ)
    (hℓ' : IsBoundedRayFromModel θ φ hφ ℓ')
    {T s : ℝ} (hT : 0 < T) (hs : s ∈ Icc (0 : ℝ) T) :
    joinStage θ φ ℓ ℓ' T s ≤ fun x => φ x +
      ((s * max (⨆ y, ℓ 1 y).toReal (⨆ y, ℓ' 1 y).toReal : ℝ) : EReal) := by
  let C := max (⨆ y, ℓ 1 y).toReal (⨆ y, ℓ' 1 y).toReal
  have h1 : RelativeEInfinity θ φ (fun x => max (ℓ T x) (ℓ' T x)) :=
    relativeEInfinity_max (hℓ.1.2 T hT.le) (hℓ'.1.2 T hT.le)
  have hleft (x : M) : ℓ T x ≤ ((T * C : ℝ) : EReal) := by
    calc
      ℓ T x ≤ ⨆ y, ℓ T y := le_iSup (ℓ T) x
      _ = ((T * (⨆ y, ℓ 1 y).toReal : ℝ) : EReal) :=
        ModelRaySupremum.iSup_ray_eq ⟨hℓ.1.1, hℓ.2⟩ hT.le
      _ ≤ ((T * C : ℝ) : EReal) := EReal.coe_le_coe_iff.mpr
        (mul_le_mul_of_nonneg_left (le_max_left _ _) hT.le)
  have hright (x : M) : ℓ' T x ≤ ((T * C : ℝ) : EReal) := by
    calc
      ℓ' T x ≤ ⨆ y, ℓ' T y := le_iSup (ℓ' T) x
      _ = ((T * (⨆ y, ℓ' 1 y).toReal : ℝ) : EReal) :=
        ModelRaySupremum.iSup_ray_eq ⟨hℓ'.1.1, hℓ'.2⟩ hT.le
      _ ≤ ((T * C : ℝ) : EReal) := EReal.coe_le_coe_iff.mpr
        (mul_le_mul_of_nonneg_left (le_max_right _ _) hT.le)
  have hf := differenceSup_ne_top_ne_bot hφ.plurisubharmonic
    h1.plurisubharmonic h1.sameSingularityType.1
  have hD : (differenceSup (fun x => max (ℓ T x) (ℓ' T x)) φ).toReal ≤ T * C := by
    apply EReal.coe_le_coe_iff.mp
    rw [EReal.coe_toReal hf.1 hf.2,
      ModelRaySupremum.differenceSup_eq_iSup hφ
        ⟨h1.plurisubharmonic, h1.sameSingularityType.1⟩]
    exact iSup_le fun x => max_le (hleft x) (hright x)
  have hr : s / T ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg hs.1 hT.le, (div_le_one hT).mpr hs.2⟩
  have hd := differenceSup_closedFiniteGeodesic hφ.plurisubharmonic
    h1.plurisubharmonic h1.sameSingularityType.1 hr
  change differenceSup (joinStage θ φ ℓ ℓ' T s) φ =
    (((s / T) * (differenceSup (fun x => max (ℓ T x) (ℓ' T x)) φ).toReal : ℝ) : EReal) at hd
  have hp := le_add_differenceSup hφ.plurisubharmonic
    (relativeEInfinity_joinStage omega hℓ hℓ' hT hs).sameSingularityType.1
  rw [hd] at hp
  have hreal : (s / T) * (differenceSup (fun x => max (ℓ T x) (ℓ' T x)) φ).toReal ≤
      s * C := by
    calc
      _ ≤ (s / T) * (T * C) := mul_le_mul_of_nonneg_left hD (div_nonneg hs.1 hT.le)
      _ = s * C := by rw [← mul_assoc, div_mul_cancel₀ _ hT.ne']
  intro x
  exact (hp x).trans (add_le_add le_rfl (EReal.coe_le_coe_iff.mpr hreal))

/-- Actual model normalization gives a genuinely finite fixed-time scalar upper bound independent of terminal time. -/
theorem joinStage_le_linear (omega : KahlerBackground n M)
    (hℓ : IsBoundedRayFromModel θ φ hφ ℓ)
    (hℓ' : IsBoundedRayFromModel θ φ hφ ℓ')
    {T s : ℝ} (hT : 0 < T) (hs : s ∈ Icc (0 : ℝ) T) :
    joinStage θ φ ℓ ℓ' T s ≤ fun _ =>
      ((s * max (⨆ y, ℓ 1 y).toReal (⨆ y, ℓ' 1 y).toReal : ℝ) : EReal) := by
  have hφ0 : φ ≤ 0 := hφ.envelope_eq ▸ singularityEnvelope_le_zero θ.val φ
  let c : ℝ := s * max (⨆ y, ℓ 1 y).toReal (⨆ y, ℓ' 1 y).toReal
  intro x
  calc
    joinStage θ φ ℓ ℓ' T s x ≤ φ x + (c : EReal) :=
      joinStage_le_model_add_linear omega hℓ hℓ' hT hs x
    _ ≤ 0 + (c : EReal) := add_le_add (hφ0 x) le_rfl
    _ = (c : EReal) := zero_add _

end

end SGPT.Foundations.Analysis.Pending.SingularBoundedRayJoinStageBounds
