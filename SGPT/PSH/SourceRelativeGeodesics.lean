import SGPT.PSH.SourceAffineGeodesics
import SGPT.Envelopes.SourceRelativeEnergy
import SGPT.Foundations.Analysis.Pending.SingularModelGeodesicRestriction

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ u₀ u₁ : M → EReal}
  {hφ : SourceModelPotential θ φ}

/-- Actual original preceq full mass produces full product PSH and both
original GLOBAL Kähler-volume L1 endpoint limits for the entire Perron curve.
The original model reference may be unbounded. -/
theorem sourcePerron_isSubgeodesicFrom_of_relativeFullMass (omega : KahlerBackground n M)
    (h₀ : SourceRelativeFullMass θ φ u₀ hφ) (h₁ : SourceRelativeFullMass θ φ u₁ hφ) :
    SourceSubgeodesicFrom omega θ (sourcePerronGeodesic omega θ u₀ u₁) u₀ u₁ := by
  apply (sourceSubgeodesicFrom_iff_native omega θ _ _ _).mpr
  have heq : sourcePerronGeodesic omega θ u₀ u₁ =
      finiteGeodesic (atlasClosedFormToNative θ).val u₀ u₁ :=
    funext fun t ↦ sourcePerronGeodesic_eq_native omega θ u₀ u₁ t
  rw [heq]
  exact RelativePreceqClasses.finiteGeodesic_isSubgeodesicFrom_of_relativeFullMassPreceq
    omega ((sourceRelativeFullMass_iff_native θ φ u₀ hφ).mp h₀)
    ((sourceRelativeFullMass_iff_native θ φ u₁ hφ).mp h₁)

/-- Every original interior Perron slice has the same actual original mass
and additive-constant singularity order; no normalized class is substituted. -/
theorem sourceRelativeFullMass_sourcePerron (omega : KahlerBackground n M)
    (h₀ : SourceRelativeFullMass θ φ u₀ hφ) (h₁ : SourceRelativeFullMass θ φ u₁ hφ)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    SourceRelativeFullMass θ φ (sourcePerronGeodesic omega θ u₀ u₁ t) hφ := by
  rw [sourcePerronGeodesic_eq_native]
  exact (sourceRelativeFullMass_iff_native θ φ _ hφ).mpr
    (RelativePreceqClasses.relativeFullMassPreceq_finiteGeodesic omega
      ((sourceRelativeFullMass_iff_native θ φ u₀ hφ).mp h₀)
      ((sourceRelativeFullMass_iff_native θ φ u₁ hφ).mp h₁) ht)

/-- The original closed Perron family assigns the requested original
endpoint values at zero and one, retaining the literal interior envelope. -/
def sourcePerronClosedSlice (omega : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (u₀ u₁ : M → EReal)
    (t : ℝ) : M → EReal :=
  closedSubgeodesicSlice (sourcePerronGeodesic omega θ u₀ u₁) u₀ u₁ t

omit [ConnectedSpace M] in
/-- Exact whole-function dictionary for the actual assigned closed trace. -/
theorem sourcePerronClosedSlice_eq_native (omega : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (u₀ u₁ : M → EReal) (t : ℝ) :
    sourcePerronClosedSlice omega θ u₀ u₁ t =
      closedSubgeodesicSlice (finiteGeodesic (atlasClosedFormToNative θ).val u₀ u₁) u₀ u₁ t := by
  unfold sourcePerronClosedSlice
  have heq : sourcePerronGeodesic omega θ u₀ u₁ =
      finiteGeodesic (atlasClosedFormToNative θ).val u₀ u₁ :=
    funext fun s ↦ sourcePerronGeodesic_eq_native omega θ u₀ u₁ s
  rw [heq]

/-- Full mass of every actual closed slice, including both original endpoints. -/
theorem sourceRelativeFullMass_sourcePerronClosedSlice (omega : KahlerBackground n M)
    (h₀ : SourceRelativeFullMass θ φ u₀ hφ) (h₁ : SourceRelativeFullMass θ φ u₁ hφ)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    SourceRelativeFullMass θ φ (sourcePerronClosedSlice omega θ u₀ u₁ t) hφ := by
  by_cases ht0 : t = 0
  · simpa only [ht0, sourcePerronClosedSlice, closedSubgeodesicSlice_zero] using h₀
  by_cases ht1 : t = 1
  · simpa only [ht1, sourcePerronClosedSlice, closedSubgeodesicSlice_one] using h₁
  have hti : t ∈ Ioo (0 : ℝ) 1 :=
    ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 ht1⟩
  simpa only [sourcePerronClosedSlice, closedSubgeodesicSlice_eq_curve hti] using
    sourceRelativeFullMass_sourcePerron omega h₀ h₁ hti

/-- Genuine restriction and dominating joint-PSH gluing identify the WHOLE
original Perron subsegment, with exact assigned original endpoint values. -/
theorem sourcePerron_subsegment_eq (omega : KahlerBackground n M)
    (h₀ : SourceRelativeFullMass θ φ u₀ hφ) (h₁ : SourceRelativeFullMass θ φ u₁ hφ)
    {a b s : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) (hab : a < b)
    (hs : s ∈ Ioo (0 : ℝ) 1) :
    sourcePerronGeodesic omega θ (sourcePerronClosedSlice omega θ u₀ u₁ a)
      (sourcePerronClosedSlice omega θ u₀ u₁ b) s =
        sourcePerronClosedSlice omega θ u₀ u₁ (s * b + (1 - s) * a) := by
  let t : ℝ := s * b + (1 - s) * a
  have hpos := mul_pos hs.1 (sub_pos.mpr hab)
  have hpos' := mul_pos (sub_pos.mpr hs.2) (sub_pos.mpr hab)
  have htab : t ∈ Ioo a b := by
    constructor <;> dsimp [t] <;> nlinarith
  have hti : t ∈ Ioo (0 : ℝ) 1 := ⟨ha.trans_lt htab.1, htab.2.trans_le hb⟩
  have hinverse : (t - a) / (b - a) = s := by
    dsimp [t]
    field_simp [ne_of_gt (sub_pos.mpr hab)]
    ring
  have hn := SingularModelGeodesicRestriction.finiteGeodesic_closed_interval_restriction_eq
    omega ((sourceRelativeFullMass_iff_native θ φ u₀ hφ).mp h₀)
    ((sourceRelativeFullMass_iff_native θ φ u₁ hφ).mp h₁) ha hb hab htab
  rw [hinverse] at hn
  simp only [sourcePerronGeodesic_eq_native, sourcePerronClosedSlice_eq_native]
  exact hn.trans (closedSubgeodesicSlice_eq_curve hti).symm

/-- Every original CLOSED subsegment is its own geodesic, with all source
slices genuine, both prescribed endpoints, and the printed a=b case retained. -/
theorem sourcePerronClosedSlice_isGeodesic (omega : KahlerBackground n M)
    (h₀ : SourceRelativeFullMass θ φ u₀ hφ) (h₁ : SourceRelativeFullMass θ φ u₁ hφ)
    {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) (hab : a ≤ b) :
    SourceGeodesicClosedInterval omega θ a b (sourcePerronClosedSlice omega θ u₀ u₁) := by
  have hslice : ∀ t ∈ Icc (0 : ℝ) 1,
      (ofFixedModel n M).IsThetaPSH θ (sourcePerronClosedSlice omega θ u₀ u₁ t) :=
    fun t ht ↦ (sourceRelativeFullMass_sourcePerronClosedSlice omega h₀ h₁ ht).choose
  rcases eq_or_lt_of_le hab with heq | hab'
  · subst b
    exact (sourceGeodesicClosedInterval_self_iff omega θ a _).mpr (hslice a ⟨ha, hb⟩)
  refine ⟨hab, fun t ht ↦ hslice t ⟨ha.trans ht.1, ht.2.trans hb⟩,
    hslice a ⟨ha, hab.trans hb⟩, hslice b ⟨ha.trans hab, hb⟩, ?_, ?_⟩
  · intro s hs
    have hpos := mul_pos hs.1 (sub_pos.mpr hab')
    have hpos' := mul_pos (sub_pos.mpr hs.2) (sub_pos.mpr hab')
    apply Or.inl
    exact hslice _ ⟨by nlinarith, by nlinarith⟩
  · intro s hs
    exact (sourcePerron_subsegment_eq omega h₀ h₁ ha hb hab' hs).symm

/-- The actual original preceq E1 class and its own true gap integral are
preserved by every interior Perron slice, for an unbounded model reference. -/
theorem sourceRelativeFiniteEnergy_sourcePerron (omega : KahlerBackground n M)
    (h₀ : SourceRelativeFiniteEnergy θ φ u₀ hφ)
    (h₁ : SourceRelativeFiniteEnergy θ φ u₁ hφ)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    SourceRelativeFiniteEnergy θ φ (sourcePerronGeodesic omega θ u₀ u₁ t) hφ := by
  rw [sourcePerronGeodesic_eq_native]
  exact (sourceRelativeFiniteEnergy_iff_native θ φ _ hφ).mpr
    (RelativePreceqClasses.relativeFiniteEnergyPreceq_finiteGeodesic omega
      ((sourceRelativeFiniteEnergy_iff_native θ φ u₀ hφ).mp h₀)
      ((sourceRelativeFiniteEnergy_iff_native θ φ u₁ hφ).mp h₁) ht)

/-- The source's ENTIRE final minimal-singularity clause. Genuine Perron
PSH is internally produced from original full mass before the actual
same-type chord/constant-competitor mother is applied. -/
theorem sourceRelativeEInfinity_sourcePerron (omega : KahlerBackground n M)
    (h₀ : SourceRelativeFullMass θ φ u₀ hφ) (h₁ : SourceRelativeFullMass θ φ u₁ hφ)
    (hmin₀ : SourceRelativeEInfinity θ φ u₀) (hmin₁ : SourceRelativeEInfinity θ φ u₁)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    SourceRelativeEInfinity θ φ (sourcePerronGeodesic omega θ u₀ u₁ t) := by
  have hsub := RelativePreceqClasses.finiteGeodesic_isSubgeodesicFrom_of_relativeFullMassPreceq
    omega ((sourceRelativeFullMass_iff_native θ φ u₀ hφ).mp h₀)
    ((sourceRelativeFullMass_iff_native θ φ u₁ hφ).mp h₁)
  rw [sourcePerronGeodesic_eq_native]
  exact (sourceRelativeEInfinity_iff_native θ φ _).mpr
    (relativeEInfinity_finiteGeodesic_of_interior (atlasClosedFormToNative θ) φ u₀ u₁
      hφ.toNative ((sourceRelativeEInfinity_iff_native θ φ u₀).mp hmin₀)
      ((sourceRelativeEInfinity_iff_native θ φ u₁).mp hmin₁) hsub.interior t ht)

/-- The WHOLE original prop:perronenvissubgeod: actual endpoint/global L1
recovery, original full-mass preservation, EVERY closed subsegment including
a=b, and both additional original E1 and E-infinity preservation clauses. -/
theorem source_relative_perron_whole (omega : KahlerBackground n M)
    (h₀ : SourceRelativeFullMass θ φ u₀ hφ) (h₁ : SourceRelativeFullMass θ φ u₁ hφ) :
    SourceSubgeodesicFrom omega θ (sourcePerronGeodesic omega θ u₀ u₁) u₀ u₁ ∧
      (∀ t ∈ Ioo (0 : ℝ) 1,
        SourceRelativeFullMass θ φ (sourcePerronGeodesic omega θ u₀ u₁ t) hφ) ∧
      (∀ a b : ℝ, 0 ≤ a → b ≤ 1 → a ≤ b →
        SourceGeodesicClosedInterval omega θ a b (sourcePerronClosedSlice omega θ u₀ u₁)) ∧
      (SourceRelativeFiniteEnergy θ φ u₀ hφ → SourceRelativeFiniteEnergy θ φ u₁ hφ →
        ∀ t ∈ Ioo (0 : ℝ) 1,
          SourceRelativeFiniteEnergy θ φ (sourcePerronGeodesic omega θ u₀ u₁ t) hφ) ∧
      (SourceRelativeEInfinity θ φ u₀ → SourceRelativeEInfinity θ φ u₁ →
        ∀ t ∈ Ioo (0 : ℝ) 1,
          SourceRelativeEInfinity θ φ (sourcePerronGeodesic omega θ u₀ u₁ t)) :=
  ⟨sourcePerron_isSubgeodesicFrom_of_relativeFullMass omega h₀ h₁,
    fun _ ht ↦ sourceRelativeFullMass_sourcePerron omega h₀ h₁ ht,
    fun _ _ ha hb hab ↦ sourcePerronClosedSlice_isGeodesic omega h₀ h₁ ha hb hab,
    fun hE₀ hE₁ _ ht ↦ sourceRelativeFiniteEnergy_sourcePerron omega hE₀ hE₁ ht,
    fun hE₀ hE₁ _ ht ↦ sourceRelativeEInfinity_sourcePerron omega h₀ h₁ hE₀ hE₁ ht⟩

end SGPT.PSH.VariableComplexAtlas
