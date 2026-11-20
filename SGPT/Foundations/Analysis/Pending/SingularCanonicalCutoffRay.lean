import SGPT.Foundations.Analysis.Pending.SingularCanonicalCutoffTailLimits

set_option autoImplicit false

/-! # The genuine canonical bounded cutoff ray over a singular model -/

open Set

namespace SGPT.Foundations.Analysis.Pending.SingularCanonicalCutoffRay

open FirstPass FirstPass.PositiveClasses RelativeEnergy RelativePreceqClasses
  RelativePreceqRays SingularCanonicalCutoffStages SingularCanonicalCutoffStageOrder
  SingularCanonicalCutoffSlices SingularCanonicalCutoffTailLimits

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M] {θ : ClosedRealOneOneForm n M}
  {φ u : M → EReal}

private theorem cutoffSlice_finite_interval_geometry (omega : KahlerBackground n M)
    (hφ : IsModelPotential θ φ) (hu : IsThetaPshPotential θ.val u) (hup : u ≤ φ)
    {a b r : ℝ} (ha : 0 ≤ a) (hab : a < b) (hr : r ∈ Ioo (0 : ℝ) 1) :
    cutoffSlice θ φ u (a + r * (b - a)) =
      finiteGeodesic θ.val (cutoffSlice θ φ u a) (cutoffSlice θ φ u b) r := by
  let I := {T : ℝ // b < T}
  let : Nonempty I := ⟨⟨b + 1, by linarith⟩⟩
  have hb : 0 ≤ b := ha.trans hab.le
  have hT (T : I) : 0 < T.val := lt_of_le_of_lt hb T.property
  have haT (T : I) : a ∈ Icc (0 : ℝ) T.val :=
    ⟨ha, hab.le.trans T.property.le⟩
  have hbT (T : I) : b ∈ Icc (0 : ℝ) T.val := ⟨hb, T.property.le⟩
  let ui₀ : I → M → EReal := fun T => cutoffStage θ φ u T.val a
  let ui₁ : I → M → EReal := fun T => cutoffStage θ φ u T.val b
  have hui₀ (T : I) : RelativeFiniteEnergyPreceq θ φ (ui₀ T) hφ :=
    RelativePreceqStatements.relativeFiniteEnergyPreceq_of_relativeEInfinity omega
      (relativeEInfinity_cutoffStage omega hφ hu hup (hT T) (haT T))
  have hui₁ (T : I) : RelativeFiniteEnergyPreceq θ φ (ui₁ T) hφ :=
    RelativePreceqStatements.relativeFiniteEnergyPreceq_of_relativeEInfinity omega
      (relativeEInfinity_cutoffStage omega hφ hu hup (hT T) (hbT T))
  have hu₀ : RelativeFiniteEnergyPreceq θ φ (cutoffSlice θ φ u a) hφ :=
    RelativePreceqStatements.relativeFiniteEnergyPreceq_of_relativeEInfinity omega
      (relativeEInfinity_cutoffSlice omega hφ hu hup a)
  have hu₁ : RelativeFiniteEnergyPreceq θ φ (cutoffSlice θ φ u b) hφ :=
    RelativePreceqStatements.relativeFiniteEnergyPreceq_of_relativeEInfinity omega
      (relativeEInfinity_cutoffSlice omega hφ hu hup b)
  have hreg₀ : uscRegularization (⨆ T : I, ui₀ T) = cutoffSlice θ φ u a :=
    (cutoffSlice_eq_regularized_common_tail omega hφ hu hup ha hab.le).symm
  have hreg₁ : uscRegularization (⨆ T : I, ui₁ T) = cutoffSlice θ φ u b :=
    (cutoffSlice_eq_regularized_common_tail omega hφ hu hup hb le_rfl).symm
  have hm₀ : ∀ x, Monotone fun T : I => ui₀ T x := by
    intro x T S hTS
    exact cutoffStage_mono_horizon omega hφ hu hup (hT T) hTS (haT T) x
  have hm₁ : ∀ x, Monotone fun T : I => ui₁ T x := by
    intro x T S hTS
    exact cutoffStage_mono_horizon omega hφ hu hup (hT T) hTS (hbT T) x
  have hlim :=
    SingularModelGeodesicIncreasingEndpoints.uscRegularization_iSup_closedSubgeodesicSlice_eq
      omega hui₀ hui₁ hu₀ hu₁ hreg₀ hreg₁ hm₀ hm₁ ⟨hr.1.le, hr.2.le⟩
  let q : ℝ := a + r * (b - a)
  have hq : 0 ≤ q := add_nonneg ha (mul_nonneg hr.1.le (sub_nonneg.mpr hab.le))
  have hqb : q ≤ b := by
    have hpos := mul_pos (sub_pos.mpr hr.2) (sub_pos.mpr hab)
    dsimp only [q]
    nlinarith
  have hstage (T : I) : cutoffStage θ φ u T.val q =
      closedSubgeodesicSlice (finiteGeodesic θ.val (ui₀ T) (ui₁ T))
        (ui₀ T) (ui₁ T) r := by
    have h := cutoffStage_closed_geometry omega hφ hu hup (hT T) ha
      T.property.le hab ⟨hr.1.le, hr.2.le⟩
    have htime : (1 - r) * a + r * b = q := by dsimp only [q]; ring
    rw [htime] at h
    exact h
  calc
    cutoffSlice θ φ u (a + r * (b - a)) =
        uscRegularization (⨆ T : I, cutoffStage θ φ u T.val q) :=
      cutoffSlice_eq_regularized_common_tail omega hφ hu hup hq hqb
    _ = uscRegularization (⨆ T : I,
        closedSubgeodesicSlice (finiteGeodesic θ.val (ui₀ T) (ui₁ T))
          (ui₀ T) (ui₁ T) r) := congrArg uscRegularization (iSup_congr hstage)
    _ = closedSubgeodesicSlice
        (finiteGeodesic θ.val (cutoffSlice θ φ u a) (cutoffSlice θ φ u b))
        (cutoffSlice θ φ u a) (cutoffSlice θ φ u b) r := hlim
    _ = finiteGeodesic θ.val (cutoffSlice θ φ u a) (cutoffSlice θ φ u b) r :=
      closedSubgeodesicSlice_eq_curve hr

/-- Internally produced increasing finite-energy endpoint nets identify the genuine cutoff-slice Perron geometry on every closed finite interval. -/
theorem cutoffSlice_closed_geometry (omega : KahlerBackground n M)
    (hφ : IsModelPotential θ φ) (hu : IsThetaPshPotential θ.val u) (hup : u ≤ φ)
    {a b r : ℝ} (ha : 0 ≤ a) (hab : a < b) (hr : r ∈ Icc (0 : ℝ) 1) :
    cutoffSlice θ φ u ((1 - r) * a + r * b) =
      closedSubgeodesicSlice
        (finiteGeodesic θ.val (cutoffSlice θ φ u a) (cutoffSlice θ φ u b))
        (cutoffSlice θ φ u a) (cutoffSlice θ φ u b) r := by
  by_cases h0 : r = 0
  · rw [h0]
    simp only [sub_zero, one_mul, zero_mul, add_zero, closedSubgeodesicSlice_zero]
  by_cases h1 : r = 1
  · rw [h1]
    simp only [sub_self, zero_mul, one_mul, zero_add, closedSubgeodesicSlice_one]
  have hri : r ∈ Ioo (0 : ℝ) 1 :=
    ⟨lt_of_le_of_ne hr.1 (Ne.symm h0), lt_of_le_of_ne hr.2 h1⟩
  have htime : (1 - r) * a + r * b = a + r * (b - a) := by ring
  rw [htime, closedSubgeodesicSlice_eq_curve hri]
  exact cutoffSlice_finite_interval_geometry omega hφ hu hup ha hab hri

/-- The actual cutoff construction internally satisfies the entire bounded source-ray predicate, including actual full mass, all finite Perron intervals and the exact model initial value. -/
theorem isBoundedRayFromModel_cutoffSlice (omega : KahlerBackground n M)
    (hφ : IsModelPotential θ φ) (hu : IsThetaPshPotential θ.val u) (hup : u ≤ φ) :
    IsBoundedRayFromModel θ φ hφ (cutoffSlice θ φ u) := by
  have hfull (t : ℝ) : RelativeFullMassPreceq θ φ (cutoffSlice θ φ u t) hφ :=
    (RelativePreceqStatements.relativeFiniteEnergyPreceq_of_relativeEInfinity omega
      (relativeEInfinity_cutoffSlice omega hφ hu hup t)).1
  refine ⟨⟨⟨fun t _ => hfull t, ?_⟩,
    fun t _ => relativeEInfinity_cutoffSlice omega hφ hu hup t⟩,
    cutoffSlice_zero hφ.plurisubharmonic⟩
  intro a b ha hab r hr
  exact cutoffSlice_finite_interval_geometry omega hφ hu hup ha hab hr

end

end SGPT.Foundations.Analysis.Pending.SingularCanonicalCutoffRay
