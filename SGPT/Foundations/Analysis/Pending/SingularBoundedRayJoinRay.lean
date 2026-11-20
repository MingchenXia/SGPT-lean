import SGPT.Foundations.Analysis.Pending.SingularBoundedRayJoinCommonTail
import SGPT.Foundations.Analysis.Pending.SingularModelGeodesicIncreasingEndpoints

set_option autoImplicit false

/-! # The actual least bounded Perron ray above two bounded source rays -/

open Set

namespace SGPT.Foundations.Analysis.Pending.SingularBoundedRayJoinRay

open FirstPass FirstPass.PositiveClasses RelativeEnergy RelativeDarvasDistance
  RelativePreceqClasses RelativePreceqRays SingularBoundedRayJoinStages
  SingularBoundedRayJoinStageOrder SingularBoundedRayJoinSlices
  SingularBoundedRayJoinCommonTail

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M] {θ : ClosedRealOneOneForm n M}
  {φ : M → EReal} {hφ : IsModelPotential θ φ} {ℓ ℓ' : ℝ → M → EReal}

private theorem joinSlice_finite_interval_geometry (omega : KahlerBackground n M)
    (hℓ : IsBoundedRayFromModel θ φ hφ ℓ)
    (hℓ' : IsBoundedRayFromModel θ φ hφ ℓ')
    {a b r : ℝ} (ha : 0 ≤ a) (hab : a < b) (hr : r ∈ Ioo (0 : ℝ) 1) :
    joinSlice θ φ ℓ ℓ' (a + r * (b - a)) =
      finiteGeodesic θ.val (joinSlice θ φ ℓ ℓ' a) (joinSlice θ φ ℓ ℓ' b) r := by
  let I := {T : ℝ // b < T}
  let : Nonempty I := ⟨⟨b + 1, by linarith⟩⟩
  have hb : 0 ≤ b := ha.trans hab.le
  have hT (T : I) : 0 < T.val := lt_of_le_of_lt hb T.property
  have haT (T : I) : a ∈ Icc (0 : ℝ) T.val :=
    ⟨ha, hab.le.trans T.property.le⟩
  have hbT (T : I) : b ∈ Icc (0 : ℝ) T.val := ⟨hb, T.property.le⟩
  let ui₀ : I → M → EReal := fun T => joinStage θ φ ℓ ℓ' T.val a
  let ui₁ : I → M → EReal := fun T => joinStage θ φ ℓ ℓ' T.val b
  have hui₀ (T : I) : RelativeFiniteEnergyPreceq θ φ (ui₀ T) hφ :=
    RelativePreceqStatements.relativeFiniteEnergyPreceq_of_relativeEInfinity omega
      (relativeEInfinity_joinStage omega hℓ hℓ' (hT T) (haT T))
  have hui₁ (T : I) : RelativeFiniteEnergyPreceq θ φ (ui₁ T) hφ :=
    RelativePreceqStatements.relativeFiniteEnergyPreceq_of_relativeEInfinity omega
      (relativeEInfinity_joinStage omega hℓ hℓ' (hT T) (hbT T))
  have hu₀ : RelativeFiniteEnergyPreceq θ φ (joinSlice θ φ ℓ ℓ' a) hφ :=
    RelativePreceqStatements.relativeFiniteEnergyPreceq_of_relativeEInfinity omega
      (relativeEInfinity_joinSlice omega hℓ hℓ' a)
  have hu₁ : RelativeFiniteEnergyPreceq θ φ (joinSlice θ φ ℓ ℓ' b) hφ :=
    RelativePreceqStatements.relativeFiniteEnergyPreceq_of_relativeEInfinity omega
      (relativeEInfinity_joinSlice omega hℓ hℓ' b)
  have hreg₀ : uscRegularization (⨆ T : I, ui₀ T) = joinSlice θ φ ℓ ℓ' a :=
    (joinSlice_eq_regularized_common_tail omega hℓ hℓ' ha hab.le).symm
  have hreg₁ : uscRegularization (⨆ T : I, ui₁ T) = joinSlice θ φ ℓ ℓ' b :=
    (joinSlice_eq_regularized_common_tail omega hℓ hℓ' hb le_rfl).symm
  have hm₀ : ∀ x, Monotone fun T : I => ui₀ T x := by
    intro x T S hTS
    exact joinStage_mono_terminalTime omega hℓ hℓ' (hT T) hTS (haT T) x
  have hm₁ : ∀ x, Monotone fun T : I => ui₁ T x := by
    intro x T S hTS
    exact joinStage_mono_terminalTime omega hℓ hℓ' (hT T) hTS (hbT T) x
  have hlim :=
    SingularModelGeodesicIncreasingEndpoints.uscRegularization_iSup_closedSubgeodesicSlice_eq
      omega hui₀ hui₁ hu₀ hu₁ hreg₀ hreg₁ hm₀ hm₁ ⟨hr.1.le, hr.2.le⟩
  let q : ℝ := a + r * (b - a)
  have hq : 0 ≤ q := add_nonneg ha (mul_nonneg hr.1.le (sub_nonneg.mpr hab.le))
  have hqb : q ≤ b := by
    have hpos := mul_pos (sub_pos.mpr hr.2) (sub_pos.mpr hab)
    dsimp only [q]
    nlinarith
  have hstage (T : I) : joinStage θ φ ℓ ℓ' T.val q =
      closedSubgeodesicSlice (finiteGeodesic θ.val (ui₀ T) (ui₁ T))
        (ui₀ T) (ui₁ T) r := by
    have h := joinStage_closed_geometry omega hℓ hℓ' (hT T) ha
      T.property.le hab ⟨hr.1.le, hr.2.le⟩
    have htime : (1 - r) * a + r * b = q := by dsimp only [q]; ring
    rw [htime] at h
    exact h
  calc
    joinSlice θ φ ℓ ℓ' (a + r * (b - a)) =
        uscRegularization (⨆ T : I, joinStage θ φ ℓ ℓ' T.val q) :=
      joinSlice_eq_regularized_common_tail omega hℓ hℓ' hq hqb
    _ = uscRegularization (⨆ T : I,
        closedSubgeodesicSlice (finiteGeodesic θ.val (ui₀ T) (ui₁ T))
          (ui₀ T) (ui₁ T) r) := congrArg uscRegularization (iSup_congr hstage)
    _ = closedSubgeodesicSlice
        (finiteGeodesic θ.val (joinSlice θ φ ℓ ℓ' a) (joinSlice θ φ ℓ ℓ' b))
        (joinSlice θ φ ℓ ℓ' a) (joinSlice θ φ ℓ ℓ' b) r := hlim
    _ = finiteGeodesic θ.val (joinSlice θ φ ℓ ℓ' a) (joinSlice θ φ ℓ ℓ' b) r :=
      closedSubgeodesicSlice_eq_curve hr

/-- The actual regularized terminal-maximum slices internally satisfy the genuine source bounded-ray predicate, including every finite Perron interval and the actual model initial value. -/
theorem isBoundedRayFromModel_joinSlice (omega : KahlerBackground n M)
    (hℓ : IsBoundedRayFromModel θ φ hφ ℓ)
    (hℓ' : IsBoundedRayFromModel θ φ hφ ℓ') :
    IsBoundedRayFromModel θ φ hφ (joinSlice θ φ ℓ ℓ') := by
  have hfull (t : ℝ) : RelativeFullMassPreceq θ φ (joinSlice θ φ ℓ ℓ' t) hφ :=
    (RelativePreceqStatements.relativeFiniteEnergyPreceq_of_relativeEInfinity omega
      (relativeEInfinity_joinSlice omega hℓ hℓ' t)).1
  refine ⟨⟨⟨fun t _ => hfull t, ?_⟩,
    fun t _ => relativeEInfinity_joinSlice omega hℓ hℓ' t⟩, joinSlice_zero (hφ := hφ)⟩
  intro a b ha hab r hr
  exact joinSlice_finite_interval_geometry omega hℓ hℓ' ha hab hr

/-- Two genuine bounded source rays have an internally constructed genuine least bounded upper source ray, ordered at every nonnegative source time. -/
theorem exists_boundedRayJoin (omega : KahlerBackground n M)
    (hℓ : IsBoundedRayFromModel θ φ hφ ℓ)
    (hℓ' : IsBoundedRayFromModel θ φ hφ ℓ') :
    ∃ J : ℝ → M → EReal, IsBoundedRayFromModel θ φ hφ J ∧
      (∀ t, 0 ≤ t → (fun x => max (ℓ t x) (ℓ' t x)) ≤ J t) ∧
      ∀ L : ℝ → M → EReal, IsBoundedRayFromModel θ φ hφ L →
        (∀ t, 0 ≤ t → ℓ t ≤ L t) → (∀ t, 0 ≤ t → ℓ' t ≤ L t) →
          ∀ t, 0 ≤ t → J t ≤ L t := by
  refine ⟨joinSlice θ φ ℓ ℓ', isBoundedRayFromModel_joinSlice omega hℓ hℓ',
    fun _ ht => max_le_joinSlice hℓ hℓ' ht, ?_⟩
  intro L hL hle hle' t ht
  exact joinSlice_le_upperRay ⟨hL.1.1, hL.2⟩ hle hle' ht

end

end SGPT.Foundations.Analysis.Pending.SingularBoundedRayJoinRay
