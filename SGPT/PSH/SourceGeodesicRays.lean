import SGPT.Envelopes.SourceRelativeEnergy
import SGPT.PSH.SourcePerronConsumers
import SGPT.Foundations.Analysis.Pending.ModelRaySupremum

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending

/-- The original ray has precisely the nonnegative real time domain. -/
abbrev SourceRayFamily (X : Type*) := Ici (0 : ℝ) → X → EReal

/-- Canonical normalization for the native real-time API. Negative times
are not additional source times or additional source hypotheses. -/
def sourceRayExtension {X : Type*} (ℓ : SourceRayFamily X) (t : ℝ) : X → EReal :=
  ℓ ⟨max t 0, le_max_right t 0⟩

/-- At every original time the extension is the identical original value. -/
theorem sourceRayExtension_nonneg {X : Type*} (ℓ : SourceRayFamily X)
    (t : ℝ) (ht : 0 ≤ t) : sourceRayExtension ℓ t = ℓ ⟨t, ht⟩ := by
  simp only [sourceRayExtension, max_eq_left ht]

/-- Exactly the printed pointwise order at all original ray times. -/
def SourceRayLE {X : Type*} (ℓ ℓ' : SourceRayFamily X) : Prop :=
  ∀ t, ℓ t ≤ ℓ' t

theorem sourceRayLE_iff_extension {X : Type*} (ℓ ℓ' : SourceRayFamily X) :
    SourceRayLE ℓ ℓ' ↔ ∀ t : ℝ, 0 ≤ t → sourceRayExtension ℓ t ≤ sourceRayExtension ℓ' t := by
  constructor
  · intro h t ht
    simpa only [sourceRayExtension_nonneg ℓ t ht, sourceRayExtension_nonneg ℓ' t ht] using
      h ⟨t, ht⟩
  · intro h t
    simpa only [sourceRayExtension_nonneg ℓ t.val t.property,
      sourceRayExtension_nonneg ℓ' t.val t.property] using h t.val t.property

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- The WHOLE original relative ray definition: actual preceq full mass,
and EVERY closed interval 0≤a≤b, retaining the degenerate interval. -/
def SourceIsRelativeGeodesicRay (omega : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (φ : M → EReal)
    (hφ : SourceModelPotential θ φ) (ℓ : SourceRayFamily M) : Prop :=
  (∀ t, SourceRelativeFullMass θ φ (ℓ t) hφ) ∧
    ∀ a b : ℝ, 0 ≤ a → a ≤ b →
      SourceGeodesicClosedInterval omega θ a b (sourceRayExtension ℓ)

/-- The printed finite-energy condition is imposed at t>0. -/
def SourceIsFiniteEnergyRay (omega : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (φ : M → EReal)
    (hφ : SourceModelPotential θ φ) (ℓ : SourceRayFamily M) : Prop :=
  SourceIsRelativeGeodesicRay omega θ φ hφ ℓ ∧
    ∀ t, 0 < t.val → SourceRelativeFiniteEnergy θ φ (ℓ t) hφ

/-- The printed bounded-ray condition is relative same type at ALL t≥0;
it does not assert absolute boundedness of an unbounded model. -/
def SourceIsBoundedRay (omega : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (φ : M → EReal)
    (hφ : SourceModelPotential θ φ) (ℓ : SourceRayFamily M) : Prop :=
  SourceIsRelativeGeodesicRay omega θ φ hφ ℓ ∧
    ∀ t, SourceRelativeEInfinity θ φ (ℓ t)

/-- The original R collection retains its prescribed model initial value. -/
def sourceGeodesicRays (omega : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (φ : M → EReal)
    (hφ : SourceModelPotential θ φ) : Set (SourceRayFamily M) :=
  {ℓ | SourceIsRelativeGeodesicRay omega θ φ hφ ℓ ∧ ℓ ⟨0, by simp⟩ = φ}

def sourceFiniteEnergyRays (omega : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (φ : M → EReal)
    (hφ : SourceModelPotential θ φ) : Set (SourceRayFamily M) :=
  {ℓ | SourceIsFiniteEnergyRay omega θ φ hφ ℓ ∧ ℓ ⟨0, by simp⟩ = φ}

def sourceBoundedRays (omega : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (φ : M → EReal)
    (hφ : SourceModelPotential θ φ) : Set (SourceRayFamily M) :=
  {ℓ | SourceIsBoundedRay omega θ φ hφ ℓ ∧ ℓ ⟨0, by simp⟩ = φ}

/-- The native strict-interval API is equivalent to the complete original
closed-interval condition. Actual full-mass slice PSH produces a=b. -/
theorem sourceIsRelativeGeodesicRay_iff_native (omega : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (φ : M → EReal)
    (hφ : SourceModelPotential θ φ) (ℓ : SourceRayFamily M) :
    SourceIsRelativeGeodesicRay omega θ φ hφ ℓ ↔
      RelativePreceqRays.IsRelativeGeodesicRayPreceq
        (atlasClosedFormToNative θ) φ hφ.toNative (sourceRayExtension ℓ) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro t ht
      rw [sourceRayExtension_nonneg ℓ t ht]
      exact (sourceRelativeFullMass_iff_native θ φ _ hφ).mp (h.1 ⟨t, ht⟩)
    · intro a b ha hab s hs
      have heq := (h.2 a b ha hab.le).2.2.2.2.2 s hs
      rw [sourcePerronGeodesic_eq_native] at heq
      convert heq using 1
      congr 1
      ring
  · intro h
    have hfull : ∀ t, 0 ≤ t → SourceRelativeFullMass θ φ (sourceRayExtension ℓ t) hφ :=
      fun t ht ↦ (sourceRelativeFullMass_iff_native θ φ _ hφ).mpr (h.1 t ht)
    refine ⟨?_, ?_⟩
    · intro t
      simpa only [sourceRayExtension_nonneg ℓ t.val t.property] using hfull t.val t.property
    · intro a b ha hab
      rcases eq_or_lt_of_le hab with heq | hab'
      · subst b
        exact (sourceGeodesicClosedInterval_self_iff omega θ a _).mpr (hfull a ha).choose
      have hslice : ∀ t ∈ Icc a b,
          (ofFixedModel n M).IsThetaPSH θ (sourceRayExtension ℓ t) :=
        fun t ht ↦ (hfull t (ha.trans ht.1)).choose
      refine ⟨hab, hslice, hslice a ⟨le_rfl, hab⟩, hslice b ⟨hab, le_rfl⟩, ?_, ?_⟩
      · intro s hs
        apply Or.inl
        apply hslice
        constructor <;> nlinarith [mul_nonneg hs.1.le (sub_nonneg.mpr hab),
          mul_nonneg (sub_nonneg.mpr hs.2.le) (sub_nonneg.mpr hab)]
      · intro s hs
        change sourceRayExtension ℓ (s * b + (1 - s) * a) = _
        rw [sourcePerronGeodesic_eq_native]
        convert h.2 a b ha hab' s hs using 1
        congr 1
        ring

theorem sourceIsFiniteEnergyRay_iff_native (omega : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (φ : M → EReal)
    (hφ : SourceModelPotential θ φ) (ℓ : SourceRayFamily M) :
    SourceIsFiniteEnergyRay omega θ φ hφ ℓ ↔ RelativePreceqRays.IsFiniteEnergyRayPreceq
      (atlasClosedFormToNative θ) φ hφ.toNative (sourceRayExtension ℓ) := by
  constructor
  · intro h
    refine ⟨(sourceIsRelativeGeodesicRay_iff_native omega θ φ hφ ℓ).mp h.1, ?_⟩
    intro t ht
    rw [sourceRayExtension_nonneg ℓ t ht.le]
    exact (sourceRelativeFiniteEnergy_iff_native θ φ _ hφ).mp (h.2 ⟨t, ht.le⟩ ht)
  · intro h
    refine ⟨(sourceIsRelativeGeodesicRay_iff_native omega θ φ hφ ℓ).mpr h.1, ?_⟩
    intro t ht
    have he := (sourceRelativeFiniteEnergy_iff_native θ φ _ hφ).mpr (h.2 t.val ht)
    simpa only [sourceRayExtension_nonneg ℓ t.val t.property] using he

theorem sourceIsBoundedRay_iff_native (omega : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (φ : M → EReal)
    (hφ : SourceModelPotential θ φ) (ℓ : SourceRayFamily M) :
    SourceIsBoundedRay omega θ φ hφ ℓ ↔ RelativePreceqRays.IsBoundedRayPreceq
      (atlasClosedFormToNative θ) φ hφ.toNative (sourceRayExtension ℓ) := by
  constructor
  · intro h
    refine ⟨(sourceIsRelativeGeodesicRay_iff_native omega θ φ hφ ℓ).mp h.1, ?_⟩
    intro t ht
    rw [sourceRayExtension_nonneg ℓ t ht]
    exact (sourceRelativeEInfinity_iff_native θ φ _).mp (h.2 ⟨t, ht⟩)
  · intro h
    refine ⟨(sourceIsRelativeGeodesicRay_iff_native omega θ φ hφ ℓ).mpr h.1, ?_⟩
    intro t
    have he := (sourceRelativeEInfinity_iff_native θ φ _).mpr (h.2 t.val t.property)
    simpa only [sourceRayExtension_nonneg ℓ t.val t.property] using he

theorem mem_sourceGeodesicRays_iff_native (omega : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (φ : M → EReal)
    (hφ : SourceModelPotential θ φ) (ℓ : SourceRayFamily M) :
    ℓ ∈ sourceGeodesicRays omega θ φ hφ ↔ RelativePreceqRays.IsRayFromModel
      (atlasClosedFormToNative θ) φ hφ.toNative (sourceRayExtension ℓ) := by
  change (SourceIsRelativeGeodesicRay omega θ φ hφ ℓ ∧ ℓ ⟨0, by simp⟩ = φ) ↔
    (RelativePreceqRays.IsRelativeGeodesicRayPreceq (atlasClosedFormToNative θ) φ hφ.toNative
      (sourceRayExtension ℓ) ∧ sourceRayExtension ℓ 0 = φ)
  rw [sourceIsRelativeGeodesicRay_iff_native, sourceRayExtension_nonneg ℓ 0 le_rfl]

theorem mem_sourceFiniteEnergyRays_iff_native (omega : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (φ : M → EReal)
    (hφ : SourceModelPotential θ φ) (ℓ : SourceRayFamily M) :
    ℓ ∈ sourceFiniteEnergyRays omega θ φ hφ ↔ RelativePreceqRays.IsFiniteEnergyRayFromModel
      (atlasClosedFormToNative θ) φ hφ.toNative (sourceRayExtension ℓ) := by
  change (SourceIsFiniteEnergyRay omega θ φ hφ ℓ ∧ ℓ ⟨0, by simp⟩ = φ) ↔
    (RelativePreceqRays.IsFiniteEnergyRayPreceq (atlasClosedFormToNative θ) φ hφ.toNative
      (sourceRayExtension ℓ) ∧ sourceRayExtension ℓ 0 = φ)
  rw [sourceIsFiniteEnergyRay_iff_native, sourceRayExtension_nonneg ℓ 0 le_rfl]

theorem mem_sourceBoundedRays_iff_native (omega : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (φ : M → EReal)
    (hφ : SourceModelPotential θ φ) (ℓ : SourceRayFamily M) :
    ℓ ∈ sourceBoundedRays omega θ φ hφ ↔ RelativePreceqRays.IsBoundedRayFromModel
      (atlasClosedFormToNative θ) φ hφ.toNative (sourceRayExtension ℓ) := by
  change (SourceIsBoundedRay omega θ φ hφ ℓ ∧ ℓ ⟨0, by simp⟩ = φ) ↔
    (RelativePreceqRays.IsBoundedRayPreceq (atlasClosedFormToNative θ) φ hφ.toNative
      (sourceRayExtension ℓ) ∧ sourceRayExtension ℓ 0 = φ)
  rw [sourceIsBoundedRay_iff_native, sourceRayExtension_nonneg ℓ 0 le_rfl]

omit [BorelSpace M] in
/-- The whole original model-supremum proposition, on the literal model
nonpole domain and the original preceq PSH class, not a normalized class. -/
theorem sourceModelDifferenceSup_eq_globalSup
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ u : M → EReal}
    (hφ : SourceModelPotential θ φ) (hu : SourceRelativePSH θ φ u) :
    sourceDifferenceSup u φ = ⨆ x, u x :=
  ModelRaySupremum.differenceSup_eq_iSup hφ.toNative
    ((sourceRelativePSH_iff_native θ φ u).mp hu)

omit [BorelSpace M] in
/-- The printed consequence follows from an actual model-envelope
competitor, without a contact-set or comparison certificate. -/
theorem sourceModel_nonpositive_le
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ u : M → EReal}
    (hφ : SourceModelPotential θ φ) (hu : SourceRelativePSH θ φ u) (hu0 : u ≤ 0) :
    u ≤ φ := by
  have hn := (sourceRelativePSH_iff_native θ φ u).mp hu
  have h := le_singularityEnvelope hn.1 hu0 hn.2
  simpa only [← hφ.toNative.envelope_eq] using h

omit [BorelSpace M] in
/-- Actual model fixed point and actual positive mass produce the true
global normalization, including an unbounded reference. -/
theorem sourceModel_globalSup_zero
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ : M → EReal}
    (hφ : SourceModelPotential θ φ) : (⨆ x, φ x) = 0 :=
  ModelRaySupremum.iSup_model_eq_zero hφ.toNative

omit [BorelSpace M] in
/-- Compact upper bounds, genuine nondegeneracy and actual positive model
mass exclude BOTH extended endpoints before any global real readback. -/
theorem sourceRay_globalSup_finite (omega : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ : M → EReal}
    {hφ : SourceModelPotential θ φ} {ℓ : SourceRayFamily M}
    (hℓ : ℓ ∈ sourceGeodesicRays omega θ φ hφ) (t : Ici (0 : ℝ)) :
    (⨆ x, ℓ t x) ≠ ⊤ ∧ (⨆ x, ℓ t x) ≠ ⊥ := by
  let : Nonempty M := ModelRaySupremum.nonempty_of_modelPotential hφ.toNative
  exact ModelRaySupremum.iSup_ne_top_ne_bot
    ((isThetaPSH_iff_nativeThetaPotential θ (ℓ t)).mp (hℓ.1.1 t).choose)

/-- The actual model-origin ray and its genuine Perron restrictions
produce the original spatial supremum at every nonnegative time. -/
theorem sourceRay_globalSup_eq (omega : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ : M → EReal}
    {hφ : SourceModelPotential θ φ} {ℓ : SourceRayFamily M}
    (hℓ : ℓ ∈ sourceGeodesicRays omega θ φ hφ) (t : Ici (0 : ℝ)) :
    (⨆ x, ℓ t x) = ((t.val * (⨆ x, ℓ ⟨1, by norm_num⟩ x).toReal : ℝ) : EReal) := by
  have hn := (mem_sourceGeodesicRays_iff_native omega θ φ hφ ℓ).mp hℓ
  simpa only [sourceRayExtension_nonneg ℓ t.val t.property,
    sourceRayExtension_nonneg ℓ 1 (by norm_num)] using
    ModelRaySupremum.iSup_ray_eq hn t.property

/-- WHOLE original prop:raysuplinear, with a genuine finite real constant
produced from the actual time-one spatial supremum. No growth premise. -/
theorem source_ray_globalSup_linear (omega : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ : M → EReal}
    {hφ : SourceModelPotential θ φ} {ℓ : SourceRayFamily M}
    (hℓ : ℓ ∈ sourceGeodesicRays omega θ φ hφ) :
    ∃ C : ℝ, ∀ t : Ici (0 : ℝ), (⨆ x, ℓ t x) = ((C * t.val : ℝ) : EReal) := by
  refine ⟨(⨆ x, ℓ ⟨1, by norm_num⟩ x).toReal, ?_⟩
  intro t
  simpa only [mul_comm] using sourceRay_globalSup_eq omega hℓ t

/-- The same actual supremum gives the pointwise model bound, at original
poles as well. It is an output, not an assumed linear-bound certificate. -/
theorem sourceRay_le_model_add_linear (omega : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ : M → EReal}
    {hφ : SourceModelPotential θ φ} {ℓ : SourceRayFamily M}
    (hℓ : ℓ ∈ sourceGeodesicRays omega θ φ hφ) (t : Ici (0 : ℝ)) :
    ℓ t ≤ fun x ↦ φ x + ((t.val * (⨆ x, ℓ ⟨1, by norm_num⟩ x).toReal : ℝ) : EReal) := by
  have hn := (mem_sourceGeodesicRays_iff_native omega θ φ hφ ℓ).mp hℓ
  simpa only [sourceRayExtension_nonneg ℓ t.val t.property,
    sourceRayExtension_nonneg ℓ 1 (by norm_num)] using
    ModelRaySupremum.ray_le_model_add_linear hn t.property

end SGPT.PSH.VariableComplexAtlas
