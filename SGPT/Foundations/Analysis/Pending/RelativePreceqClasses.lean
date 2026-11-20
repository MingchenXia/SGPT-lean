import SGPT.Foundations.Analysis.Pending.RelativeGeodesicRays
import SGPT.Foundations.Analysis.FirstPass.FiniteGeodesicAffineCovariance
import SGPT.Foundations.Analysis.Pending.RooftopEnvelopeNormalization

set_option autoImplicit false

/-!
# Xia's relative classes with the singularity-type order `⪯`

Xia (SGPT, Definition 3.1.5, PDF 115) defines, for a model potential `φ`,

  `PSH(X, θ; φ) = {η ∈ PSH(X, θ) : η ⪯ φ}`,  `E(X, θ; φ)`, `E¹(X, θ; φ)` inside it,

with `⪯` the singularity-type order (`η ≤ φ + C` for some constant `C`). The classes
`RelativePSH` / `RelativeFullMass` / `RelativeFiniteEnergy` of `Pending.RelativeFullMass` are the
normalized subclasses `{η ≤ φ}`. This file defines the source classes (`RelativePSHPreceq`,
`RelativeFullMassPreceq`, `RelativeFiniteEnergyPreceq`), relates them to the normalized ones by
finite translation, and transfers results to them:

* any model potential: `u` is in a `⪯` class iff `u + c` is in the normalized class for one (every
  sufficiently negative) `c`; Perron geodesics between `E(X, θ; φ)`-endpoints (Xia Proposition 4.2.1)
  are subgeodesics with slices in `E(X, θ; φ)`, and in `E¹(X, θ; φ)` for `E¹` endpoints;
* a bounded model potential: the translation formula `E(u + c) = E(u) + c ∫ θ_φ^n` for the extended
  energy (Xia (3.31)); `E` is affine along Perron geodesics (Xia Proposition 4.3.3), the diamond
  inequality (Xia Corollary 3.1.7) and `d₁` is a metric on `E¹(X, θ; φ)` (Xia Lemma 4.3.1, with
  the contraction of Proposition 4.3.1), all for the `⪯` classes.

For a bounded model potential every `θ`-PSH potential is `⪯ φ`, so there `PSH(X, θ; φ)` is all of
`PSH(X, θ)` (`relativePSHPreceq_iff_of_bounded`).
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.RelativePreceqClasses

open FirstPass FirstPass.PositiveClasses BoundedGlobalProduct GlobalNonPluripolar RelativeEnergy
  BoundedMongeAmpereEnergy MongeAmpereEnergyDecreasing FiniteEnergyCharacterization DiagonalMass
  RelativeEnergyDiamond RelativeDarvasDistance FiniteGeodesicEnergyAffineE1

noncomputable section

/-! ### Extended-real translation -/

/-- `(a + c) - c = a` in `EReal`, poles included. -/
theorem add_coe_add_coe_neg (a : EReal) (c : ℝ) :
    a + (c : EReal) + ((-c : ℝ) : EReal) = a := by
  rw [add_assoc, ← EReal.coe_add, add_neg_cancel, EReal.coe_zero, add_zero]

/-- `a + c ≤ b ↔ a ≤ b - c` in `EReal`, for a finite `c`. -/
theorem add_coe_le_iff (a b : EReal) (c : ℝ) :
    a + (c : EReal) ≤ b ↔ a ≤ b + ((-c : ℝ) : EReal) := by
  constructor
  · intro h
    have h' := add_le_add_left h ((-c : ℝ) : EReal)
    rwa [add_coe_add_coe_neg] at h'
  · intro h
    have h' := add_le_add_left h (c : EReal)
    rwa [show b + ((-c : ℝ) : EReal) + (c : EReal) = b by
      simpa using add_coe_add_coe_neg b (-c)] at h'

theorem add_coe_le_add_coe_iff (a b : EReal) (c : ℝ) :
    a + (c : EReal) ≤ b + (c : EReal) ↔ a ≤ b :=
  (EReal.addLECancellable_coe c).add_le_add_iff_right

theorem add_coe_injective (c : ℝ) : Function.Injective fun a : EReal => a + (c : EReal) :=
  fun a b h => le_antisymm ((add_coe_le_add_coe_iff a b c).1 h.le)
    ((add_coe_le_add_coe_iff b a c).1 h.ge)

/-- Translating a function by `c` and then by `-c` gives it back. -/
theorem translate_translate_neg {M : Type*} (u : M → EReal) (c : ℝ) :
    (fun x => (u x + (c : EReal)) + ((-c : ℝ) : EReal)) = u :=
  funext fun x => add_coe_add_coe_neg (u x) c

theorem min_add_coe (a b : EReal) (c : ℝ) :
    min (a + (c : EReal)) (b + (c : EReal)) = min a b + (c : EReal) := by
  rcases le_total a b with hab | hab
  · rw [min_eq_left hab, min_eq_left ((add_coe_le_add_coe_iff a b c).2 hab)]
  · rw [min_eq_right hab, min_eq_right ((add_coe_le_add_coe_iff b a c).2 hab)]

theorem max_add_coe (a b : EReal) (c : ℝ) :
    max (a + (c : EReal)) (b + (c : EReal)) = max a b + (c : EReal) := by
  rcases le_total a b with hab | hab
  · rw [max_eq_right hab, max_eq_right ((add_coe_le_add_coe_iff a b c).2 hab)]
  · rw [max_eq_left hab, max_eq_left ((add_coe_le_add_coe_iff b a c).2 hab)]

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-! ### The classes -/

/-- **Xia's `PSH(X, θ; φ)`** (SGPT Definition 3.1.5): the `θ`-PSH potentials `η ⪯ φ`, i.e.
`η ≤ φ + C` for some real `C`. -/
def RelativePSHPreceq (θ : ClosedRealOneOneForm n M) (φ u : M → EReal) : Prop :=
  IsThetaPshPotential θ.val u ∧ MoreSingularOn u φ univ

variable [MeasurableSpace M] [CompactSpace M]

/-- **Xia's `E(X, θ; φ)`**: potentials `η ⪯ φ` with the diagonal non-pluripolar mass of `φ`. -/
def RelativeFullMassPreceq (θ : ClosedRealOneOneForm n M) (φ u : M → EReal)
    (hφ : IsModelPotential θ φ) : Prop :=
  ∃ hu : IsThetaPshPotential θ.val u, MoreSingularOn u φ univ ∧
    diagonalPotentialMass θ u hu = diagonalPotentialMass θ φ hφ.plurisubharmonic

/-- **Xia's `E¹(X, θ; φ)`**: potentials of `E(X, θ; φ)` with `∫ |φ - η| θ_η^n < ∞`. -/
def RelativeFiniteEnergyPreceq (θ : ClosedRealOneOneForm n M) (φ u : M → EReal)
    (hφ : IsModelPotential θ φ) : Prop :=
  RelativeFullMassPreceq θ φ u hφ ∧
    ∃ hu : IsThetaPshPotential θ.val u, relativeFiniteEnergyIntegral θ φ u hu < ⊤

omit [MeasurableSpace M] [CompactSpace M] in
theorem preceq_of_relativePSH {θ : ClosedRealOneOneForm n M} {φ u : M → EReal}
    (h : RelativePSH θ φ u) : RelativePSHPreceq θ φ u :=
  ⟨h.1, ⟨0, fun x _ => by rw [EReal.coe_zero, add_zero]; exact h.2 x⟩⟩

section Classes

variable [BorelSpace M] {θ : ClosedRealOneOneForm n M} {φ u : M → EReal} {hφ : IsModelPotential θ φ}

omit [BorelSpace M] in
theorem preceq_of_relativeFullMass (h : RelativeFullMass θ φ u hφ) : RelativeFullMassPreceq θ φ u hφ :=
  let ⟨hu, hle, hm⟩ := h
  ⟨hu, (preceq_of_relativePSH ⟨hu, hle⟩).2, hm⟩

omit [BorelSpace M] in
theorem preceq_of_relativeFiniteEnergy (h : RelativeFiniteEnergy θ φ u hφ) :
    RelativeFiniteEnergyPreceq θ φ u hφ :=
  ⟨preceq_of_relativeFullMass h.1, h.2⟩

omit [BorelSpace M] in
theorem RelativeFullMassPreceq.plurisubharmonic (h : RelativeFullMassPreceq θ φ u hφ) :
    IsThetaPshPotential θ.val u :=
  h.1

omit [BorelSpace M] in
theorem RelativeFullMassPreceq.relativePSHPreceq (h : RelativeFullMassPreceq θ φ u hφ) :
    RelativePSHPreceq θ φ u :=
  ⟨h.1, h.2.1⟩

omit [BorelSpace M] in
theorem RelativeFullMassPreceq.mass_eq (h : RelativeFullMassPreceq θ φ u hφ)
    (hu : IsThetaPshPotential θ.val u) :
    diagonalPotentialMass θ u hu = diagonalPotentialMass θ φ hφ.plurisubharmonic := by
  obtain ⟨hu', -, hm⟩ := h
  exact hm

omit [MeasurableSpace M] [CompactSpace M] in
/-- A potential `u ⪯ φ` lies below `φ` after any sufficiently negative translation. -/
theorem RelativePSHPreceq.exists_add_le (h : RelativePSHPreceq θ φ u) :
    ∃ C : ℝ, ∀ c : ℝ, c ≤ C → ∀ x, u x + (c : EReal) ≤ φ x := by
  obtain ⟨D, hD⟩ := h.2
  refine ⟨-D, fun c hc x => ?_⟩
  calc u x + (c : EReal) ≤ (φ x + (D : EReal)) + (c : EReal) := add_le_add (hD x (mem_univ x)) le_rfl
    _ = φ x + ((D + c : ℝ) : EReal) := by rw [add_assoc, EReal.coe_add]
    _ ≤ φ x + ((0 : ℝ) : EReal) := add_le_add le_rfl (EReal.coe_le_coe_iff.2 (by linarith))
    _ = φ x := by rw [EReal.coe_zero, add_zero]

omit [MeasurableSpace M] [CompactSpace M] in
theorem RelativePSHPreceq.add_const (h : RelativePSHPreceq θ φ u) (c : ℝ) :
    RelativePSHPreceq θ φ (fun x => u x + (c : EReal)) :=
  ⟨h.1.add_const c, ((sameSingularityTypeOn_add_const u univ c).1).trans h.2⟩

omit [MeasurableSpace M] [CompactSpace M] in
theorem RelativePSHPreceq.relativePSH_add (h : RelativePSHPreceq θ φ u) {c : ℝ}
    (hc : ∀ x, u x + (c : EReal) ≤ φ x) : RelativePSH θ φ (fun x => u x + (c : EReal)) :=
  ⟨h.1.add_const c, hc⟩

theorem RelativeFullMassPreceq.add_const (h : RelativeFullMassPreceq θ φ u hφ) (c : ℝ) :
    RelativeFullMassPreceq θ φ (fun x => u x + (c : EReal)) hφ := by
  obtain ⟨hu, hle, hm⟩ := h
  obtain ⟨h1, h2⟩ := FiniteGeodesicsFullMassAnyDim.moreSingularOn_add_const_and_mass_eq θ
    hφ.plurisubharmonic hu hle hm c
  exact ⟨hu.add_const c, h1, h2 _⟩

theorem RelativeFullMassPreceq.relativeFullMass_add (h : RelativeFullMassPreceq θ φ u hφ) {c : ℝ}
    (hc : ∀ x, u x + (c : EReal) ≤ φ x) : RelativeFullMass θ φ (fun x => u x + (c : EReal)) hφ := by
  obtain ⟨hu', -, hm'⟩ := h.add_const c
  exact ⟨hu', hc, hm'⟩

theorem relativeFullMassPreceq_of_add {c : ℝ}
    (h : RelativeFullMassPreceq θ φ (fun x => u x + (c : EReal)) hφ) :
    RelativeFullMassPreceq θ φ u hφ := by
  have h' := h.add_const (-c)
  rwa [translate_translate_neg] at h'

theorem relativeFullMassPreceq_iff_exists :
    RelativeFullMassPreceq θ φ u hφ ↔ ∃ c : ℝ, RelativeFullMass θ φ (fun x => u x + (c : EReal)) hφ := by
  constructor
  · intro h
    obtain ⟨C, hC⟩ := h.relativePSHPreceq.exists_add_le
    exact ⟨C, h.relativeFullMass_add (hC C le_rfl)⟩
  · rintro ⟨c, hc⟩
    exact relativeFullMassPreceq_of_add (preceq_of_relativeFullMass hc)

/-- The finite-energy integral stays finite under a finite translation. -/
theorem relativeFiniteEnergyIntegral_add_lt_top (omega : KahlerBackground n M)
    (hu : IsThetaPshPotential θ.val u) (hfin : relativeFiniteEnergyIntegral θ φ u hu < ⊤) (c : ℝ)
    (huc : IsThetaPshPotential θ.val fun x => u x + (c : EReal)) :
    relativeFiniteEnergyIntegral θ φ (fun x => u x + (c : EReal)) huc < ⊤ := by
  have := DiagonalMeasureRegularity.isFiniteMeasure_diagonalPotentialMeasure omega θ hu
  unfold relativeFiniteEnergyIntegral
  rw [DiagonalMeasureRegularity.diagonalPotentialMeasure_add_const θ hu c huc]
  have hle : ∀ x, canonicalERealAbsDiff (φ x) (u x + (c : EReal)) ≤
      canonicalERealAbsDiff (φ x) (u x) + ENNReal.ofReal |0 - c| := fun x => by
    have h := canonicalERealAbsDiff_add_coe_add_coe_le (φ x) (u x) 0 c
    rwa [EReal.coe_zero, add_zero] at h
  calc ∫⁻ x, canonicalERealAbsDiff (φ x) (u x + (c : EReal)) ∂ diagonalPotentialMeasure θ u hu
      ≤ ∫⁻ x, (canonicalERealAbsDiff (φ x) (u x) + ENNReal.ofReal |0 - c|)
          ∂ diagonalPotentialMeasure θ u hu := lintegral_mono hle
    _ ≤ ∫⁻ x, canonicalERealAbsDiff (φ x) (u x) ∂ diagonalPotentialMeasure θ u hu +
          ∫⁻ _, ENNReal.ofReal |0 - c| ∂ diagonalPotentialMeasure θ u hu :=
        (lintegral_add_right _ measurable_const).le
    _ < ⊤ := by
        rw [lintegral_const]
        exact ENNReal.add_lt_top.2 ⟨hfin, ENNReal.mul_lt_top ENNReal.ofReal_lt_top
          (measure_lt_top _ _)⟩

theorem RelativeFiniteEnergyPreceq.add_const (omega : KahlerBackground n M)
    (h : RelativeFiniteEnergyPreceq θ φ u hφ) (c : ℝ) :
    RelativeFiniteEnergyPreceq θ φ (fun x => u x + (c : EReal)) hφ := by
  obtain ⟨hm, hu, hfin⟩ := h
  exact ⟨hm.add_const c, hu.add_const c,
    relativeFiniteEnergyIntegral_add_lt_top omega hu hfin c _⟩

theorem RelativeFiniteEnergyPreceq.relativeFiniteEnergy_add (omega : KahlerBackground n M)
    (h : RelativeFiniteEnergyPreceq θ φ u hφ) {c : ℝ} (hc : ∀ x, u x + (c : EReal) ≤ φ x) :
    RelativeFiniteEnergy θ φ (fun x => u x + (c : EReal)) hφ := by
  obtain ⟨hm, hu', hfin⟩ := h.add_const omega c
  exact ⟨h.1.relativeFullMass_add hc, hu', hfin⟩

theorem relativeFiniteEnergyPreceq_of_add (omega : KahlerBackground n M) {c : ℝ}
    (h : RelativeFiniteEnergyPreceq θ φ (fun x => u x + (c : EReal)) hφ) :
    RelativeFiniteEnergyPreceq θ φ u hφ := by
  have h' := h.add_const omega (-c)
  rwa [translate_translate_neg] at h'

theorem relativeFiniteEnergyPreceq_iff_exists (omega : KahlerBackground n M) :
    RelativeFiniteEnergyPreceq θ φ u hφ ↔
      ∃ c : ℝ, RelativeFiniteEnergy θ φ (fun x => u x + (c : EReal)) hφ := by
  constructor
  · intro h
    obtain ⟨C, hC⟩ := h.1.relativePSHPreceq.exists_add_le
    exact ⟨C, h.relativeFiniteEnergy_add omega (hC C le_rfl)⟩
  · rintro ⟨c, hc⟩
    exact relativeFiniteEnergyPreceq_of_add omega (preceq_of_relativeFiniteEnergy hc)

omit [MeasurableSpace M] [BorelSpace M] in
/-- A `θ`-PSH potential on a compact manifold is bounded above by a real constant. -/
theorem exists_le_coe_of_isThetaPshPotential {θ' : SmoothRealForm n M 2} {v : M → EReal}
    (hv : IsThetaPshPotential θ' v) : ∃ m : ℝ, ∀ x, v x ≤ (m : EReal) := by
  rcases isEmpty_or_nonempty M with hM | hM
  · exact ⟨0, fun x => (IsEmpty.false x).elim⟩
  obtain ⟨y, -, hmax⟩ :=
    (hv.1.quasiPlurisubharmonic.upperSemicontinuous.upperSemicontinuousOn univ).exists_isMaxOn
      univ_nonempty isCompact_univ
  have htop : v y ≠ ⊤ := hv.1.quasiPlurisubharmonic.ne_top y
  rcases eq_or_ne (v y) ⊥ with hbot | hbot
  · exact ⟨0, fun x => (hmax (mem_univ x)).trans (hbot ▸ bot_le)⟩
  exact ⟨(v y).toReal, fun x => (EReal.coe_toReal htop hbot).symm ▸ hmax (mem_univ x)⟩

omit [MeasurableSpace M] [BorelSpace M] in
/-- **For a bounded model potential, `PSH(X, θ; φ) = PSH(X, θ)`**: a `θ`-PSH potential on a compact
manifold is bounded above, hence `⪯ φ`. -/
theorem relativePSHPreceq_iff_of_bounded (hφb : IsBoundedPotential φ) :
    RelativePSHPreceq θ φ u ↔ IsThetaPshPotential θ.val u := by
  refine ⟨fun h => h.1, fun hu => ⟨hu, ?_⟩⟩
  obtain ⟨m, hm⟩ := exists_le_coe_of_isThetaPshPotential hu
  obtain ⟨a, _, hab⟩ := hφb
  refine ⟨m - a, fun x _ => ?_⟩
  calc u x ≤ (m : EReal) := hm x
    _ = (a : EReal) + ((m - a : ℝ) : EReal) := by rw [← EReal.coe_add]; ring_nf
    _ ≤ φ x + ((m - a : ℝ) : EReal) := add_le_add (hab x).1 le_rfl

omit [BorelSpace M] in
/-- For a bounded model potential, `E(X, θ; φ)` is the set of `θ`-PSH potentials with the mass of
`φ`. -/
theorem relativeFullMassPreceq_iff_of_bounded (hφb : IsBoundedPotential φ) :
    RelativeFullMassPreceq θ φ u hφ ↔ ∃ hu : IsThetaPshPotential θ.val u,
      diagonalPotentialMass θ u hu = diagonalPotentialMass θ φ hφ.plurisubharmonic := by
  refine ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, ?_, h.2⟩⟩
  exact ((relativePSHPreceq_iff_of_bounded (θ := θ) hφb).2 h.1).2

end Classes

/-! ### Perron geodesics between `⪯` endpoints (any model potential) -/

section Geodesics

omit [MeasurableSpace M] [CompactSpace M] in
/-- Perron geodesics commute with a finite translation of both endpoints. -/
theorem finiteGeodesic_add_const (θ : SmoothRealForm n M 2) (u₀ u₁ : M → EReal) (c t : ℝ) :
    finiteGeodesic θ (fun x => u₀ x + (c : EReal)) (fun x => u₁ x + (c : EReal)) t =
      fun x => finiteGeodesic θ u₀ u₁ t x + (c : EReal) := by
  have h := finiteGeodesic_affineCovariance θ u₀ u₁ 0 c t
  simpa only [zero_add, zero_mul] using h

omit [MeasurableSpace M] [CompactSpace M] in
/-- A subgeodesic stays a subgeodesic after a finite translation. -/
theorem isSubgeodesicFrom_add_const {θ : SmoothRealForm n M 2} {curve : ℝ → M → EReal}
    {u₀ u₁ : M → EReal} (h : IsSubgeodesicFrom θ curve u₀ u₁) (c : ℝ) :
    IsSubgeodesicFrom θ (fun t x => curve t x + (c : EReal)) (fun x => u₀ x + (c : EReal))
      (fun x => u₁ x + (c : EReal)) := by
  have h' := h.affineTranslated 0 c
  have e : affineTranslatedCurve curve 0 c = fun t x => curve t x + (c : EReal) := by
    funext t x
    rw [affineTranslatedCurve_apply, zero_mul, zero_add]
  rwa [e, zero_add] at h'

omit [MeasurableSpace M] [CompactSpace M] in
theorem finiteGeodesic_add_const_neg (θ : SmoothRealForm n M 2) (u₀ u₁ : M → EReal) (c : ℝ) :
    (fun t x => finiteGeodesic θ (fun x => u₀ x + (c : EReal)) (fun x => u₁ x + (c : EReal)) t x +
      ((-c : ℝ) : EReal)) = finiteGeodesic θ u₀ u₁ := by
  funext t x
  rw [finiteGeodesic_add_const]
  exact add_coe_add_coe_neg _ _

variable [BorelSpace M] [ConnectedSpace M] {θ : ClosedRealOneOneForm n M} {φ u₀ u₁ : M → EReal}
  {hφ : IsModelPotential θ φ}

omit [MeasurableSpace M] [CompactSpace M] [BorelSpace M] [ConnectedSpace M] in
/-- Two `⪯ φ` potentials lie below `φ` after one common translation. -/
theorem exists_common_add_le (h₀ : RelativePSHPreceq θ φ u₀) (h₁ : RelativePSHPreceq θ φ u₁) :
    ∃ c : ℝ, (∀ x, u₀ x + (c : EReal) ≤ φ x) ∧ ∀ x, u₁ x + (c : EReal) ≤ φ x := by
  obtain ⟨C₀, hC₀⟩ := h₀.exists_add_le
  obtain ⟨C₁, hC₁⟩ := h₁.exists_add_le
  exact ⟨min C₀ C₁, hC₀ _ (min_le_left _ _), hC₁ _ (min_le_right _ _)⟩

/-- **Xia, Proposition 4.2.1, for the `⪯` class**: for `u₀, u₁ ∈ E(X, θ; φ)` (Xia's class, `⪯ φ`),
the Perron geodesic is a subgeodesic from `u₀` to `u₁`. -/
theorem finiteGeodesic_isSubgeodesicFrom_of_relativeFullMassPreceq (omega : KahlerBackground n M)
    (h₀ : RelativeFullMassPreceq θ φ u₀ hφ) (h₁ : RelativeFullMassPreceq θ φ u₁ hφ) :
    IsSubgeodesicFrom θ.val (finiteGeodesic θ.val u₀ u₁) u₀ u₁ := by
  obtain ⟨c, hc₀, hc₁⟩ := exists_common_add_le h₀.relativePSHPreceq h₁.relativePSHPreceq
  have hs := isSubgeodesicFrom_add_const
    (FiniteGeodesicsFullMassAnyDim.finiteGeodesic_isSubgeodesicFrom_of_relativeFullMass
      omega θ φ _ _ hφ (h₀.relativeFullMass_add hc₀) (h₁.relativeFullMass_add hc₁)) (-c)
  rwa [finiteGeodesic_add_const_neg, translate_translate_neg, translate_translate_neg] at hs

/-- The interior Perron slices between `u₀, u₁ ∈ E(X, θ; φ)` (Xia's class) lie in
`E(X, θ; φ)`. -/
theorem relativeFullMassPreceq_finiteGeodesic (omega : KahlerBackground n M)
    (h₀ : RelativeFullMassPreceq θ φ u₀ hφ) (h₁ : RelativeFullMassPreceq θ φ u₁ hφ) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) : RelativeFullMassPreceq θ φ (finiteGeodesic θ.val u₀ u₁ t) hφ := by
  obtain ⟨c, hc₀, hc₁⟩ := exists_common_add_le h₀.relativePSHPreceq h₁.relativePSHPreceq
  have h := FiniteGeodesicsFullMassAnyDim.relativeFullMass_finiteGeodesic omega θ φ _ _ hφ
    (h₀.relativeFullMass_add hc₀) (h₁.relativeFullMass_add hc₁) t ht
  rw [finiteGeodesic_add_const] at h
  exact relativeFullMassPreceq_of_add (preceq_of_relativeFullMass h)

/-- **Xia, Proposition 4.2.1, finite-energy case, for the `⪯` class**: for `u₀, u₁ ∈ E¹(X, θ; φ)`
the interior Perron slices lie in `E¹(X, θ; φ)`. -/
theorem relativeFiniteEnergyPreceq_finiteGeodesic (omega : KahlerBackground n M)
    (h₀ : RelativeFiniteEnergyPreceq θ φ u₀ hφ) (h₁ : RelativeFiniteEnergyPreceq θ φ u₁ hφ) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) : RelativeFiniteEnergyPreceq θ φ (finiteGeodesic θ.val u₀ u₁ t) hφ := by
  obtain ⟨c, hc₀, hc₁⟩ := exists_common_add_le h₀.1.relativePSHPreceq h₁.1.relativePSHPreceq
  have h := FiniteGeodesicsFullMassAnyDim.relativeFiniteEnergy_finiteGeodesic omega θ φ _ _ hφ
    (h₀.relativeFiniteEnergy_add omega hc₀) (h₁.relativeFiniteEnergy_add omega hc₁) t ht
  rw [finiteGeodesic_add_const] at h
  exact relativeFiniteEnergyPreceq_of_add omega (preceq_of_relativeFiniteEnergy h)

end Geodesics

/-! ### Extended-real affine algebra -/

omit [MeasurableSpace M] [CompactSpace M] in
/-- `(1 - t) a + t b + k = (1 - t)(a + k) + t (b + k)` in `EReal` for `0 < t < 1`, finite `k` and
`a, b ≠ +∞`, poles included. -/
theorem affine_add_coe {a b : EReal} (ha : a ≠ ⊤) (hb : b ≠ ⊤) (k : ℝ) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    ((1 - t : ℝ) : EReal) * a + ((t : ℝ) : EReal) * b + (k : EReal) =
      ((1 - t : ℝ) : EReal) * (a + (k : EReal)) + ((t : ℝ) : EReal) * (b + (k : EReal)) := by
  have h1 : (0 : ℝ) < 1 - t := sub_pos.2 ht.2
  induction a using EReal.rec with
  | bot =>
    simp only [EReal.bot_add, EReal.coe_mul_bot_of_pos h1]
  | top => exact (ha rfl).elim
  | coe a =>
    induction b using EReal.rec with
    | bot =>
      simp only [EReal.bot_add, EReal.add_bot, EReal.coe_mul_bot_of_pos ht.1]
    | top => exact (hb rfl).elim
    | coe b =>
      norm_cast
      ring

omit [MeasurableSpace M] [CompactSpace M] in
/-- Cancelling a finite translation in an affine identity in `EReal`. -/
theorem eq_affine_of_add_coe {x a b : EReal} (ha : a ≠ ⊤) (hb : b ≠ ⊤) {k t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1)
    (h : x + (k : EReal) =
      ((1 - t : ℝ) : EReal) * (a + (k : EReal)) + ((t : ℝ) : EReal) * (b + (k : EReal))) :
    x = ((1 - t : ℝ) : EReal) * a + ((t : ℝ) : EReal) * b :=
  add_coe_injective k (h.trans (affine_add_coe ha hb k ht).symm)

/-! ### The translation formula for the extended energy (bounded model potential) -/

section Energy

variable [BorelSpace M] {θ : ClosedRealOneOneForm n M} {φ u : M → EReal}
  {hφ : IsModelPotential θ φ}

/-- The volume `∫_X θ_φ^n` of the model potential, as a real number. -/
def modelVolume (θ : ClosedRealOneOneForm n M) (φ : M → EReal) (hφ : IsModelPotential θ φ) : ℝ :=
  (diagonalPotentialMeasure θ φ hφ.plurisubharmonic).real univ

omit [BorelSpace M] in
theorem relativeEnergyOfMinimalType_congr {θ : ClosedRealOneOneForm n M} {φ u v : M → EReal}
    (hφ : IsThetaPshPotential θ.val φ) (huv : u = v) (hu : IsThetaPshPotential θ.val u)
    (hv : IsThetaPshPotential θ.val v) :
    relativeEnergyOfMinimalType θ φ u hφ hu = relativeEnergyOfMinimalType θ φ v hφ hv := by
  subst huv
  rfl

omit [MeasurableSpace M] [CompactSpace M] [BorelSpace M] in
theorem RelativeEInfinity.add_const {v : M → EReal} (hv : RelativeEInfinity θ φ v) (c : ℝ) :
    RelativeEInfinity θ φ (fun x => v x + (c : EReal)) :=
  ⟨hv.1.add_const c, (sameSingularityTypeOn_add_const v univ c).trans hv.2⟩

/-- **Xia (3.31) for relatively minimal potentials**: `E(v + c) = E(v) + c ∫ θ_φ^n` (bounded
model potential). -/
theorem relativeEnergyOfMinimalType_add_const (omega : KahlerBackground n M)
    (hφb : IsBoundedPotential φ) {v : M → EReal} (hv : RelativeEInfinity θ φ v) (c : ℝ)
    (hvc : RelativeEInfinity θ φ (fun x => v x + (c : EReal))) :
    relativeEnergyOfMinimalType θ φ _ hφ.plurisubharmonic hvc.1 =
      relativeEnergyOfMinimalType θ φ v hφ.plurisubharmonic hv.1 + c * modelVolume θ φ hφ := by
  have hvb := isBoundedPotential_of_sameSingularityType hφb hv.2
  have e : (fun x => v x - ((-c : ℝ) : EReal)) = fun x => v x + (c : EReal) := by
    funext x
    rw [sub_eq_add_neg, EReal.coe_neg, neg_neg]
  have hvs : IsThetaPshPotential θ.val fun x => v x - ((-c : ℝ) : EReal) := e ▸ hvc.1
  have h := relativeEnergyOfMinimalType_sub_const omega θ hφ.plurisubharmonic hv.1 hφb hvb (-c) hvs
  rw [relativeEnergyOfMinimalType_congr hφ.plurisubharmonic e hvs hvc.1] at h
  rw [h, modelVolume]
  simp only [diagonalPotentialMeasure]
  ring

/-- One half of the translation formula for the extended energy. -/
theorem energy_add_coe_le (omega : KahlerBackground n M) (hφb : IsBoundedPotential φ)
    (u : M → EReal) (c : ℝ) :
    energy θ φ hφ u + ((c * modelVolume θ φ hφ : ℝ) : EReal) ≤
      energy θ φ hφ (fun x => u x + (c : EReal)) := by
  refine le_sInf ?_
  rintro e ⟨w, hw, huw, rfl⟩
  have hv := RelativeEInfinity.add_const hw (-c)
  have huv : u ≤ fun x => w x + ((-c : ℝ) : EReal) := fun x => (add_coe_le_iff _ _ c).1 (huw x)
  have hle : energy θ φ hφ u ≤
      (relativeEnergyOfMinimalType θ φ _ hφ.plurisubharmonic hv.1 : EReal) :=
    sInf_le ⟨_, hv, huv, rfl⟩
  have hw' : RelativeEInfinity θ φ (fun x => (w x + ((-c : ℝ) : EReal)) + (c : EReal)) := by
    simpa only [show ((c : ℝ) : EReal) = ((-(-c) : ℝ) : EReal) by rw [neg_neg],
      translate_translate_neg] using hw
  have hE := relativeEnergyOfMinimalType_add_const (hφ := hφ) omega hφb hv c hw'
  have ew : (fun x => (w x + ((-c : ℝ) : EReal)) + (c : EReal)) = w := by
    simpa only [neg_neg] using translate_translate_neg w (-c)
  rw [relativeEnergyOfMinimalType_congr hφ.plurisubharmonic ew hw'.1 hw.1] at hE
  rw [hE, EReal.coe_add]
  exact add_le_add hle le_rfl

/-- **The translation formula for the extended energy** (Xia (3.31); bounded model potential):
`E(u + c) = E(u) + c ∫_X θ_φ^n` for every potential `u` and real `c`, in `[-∞, +∞]`. -/
theorem energy_add_const (omega : KahlerBackground n M) (hφb : IsBoundedPotential φ)
    (u : M → EReal) (c : ℝ) :
    energy θ φ hφ (fun x => u x + (c : EReal)) =
      energy θ φ hφ u + ((c * modelVolume θ φ hφ : ℝ) : EReal) := by
  refine le_antisymm ?_ (energy_add_coe_le omega hφb u c)
  have h := energy_add_coe_le (hφ := hφ) omega hφb (fun x => u x + (c : EReal)) (-c)
  rw [translate_translate_neg, show -c * modelVolume θ φ hφ = -(c * modelVolume θ φ hφ) by ring,
    add_coe_le_iff, neg_neg] at h
  exact h

omit [BorelSpace M] in
theorem energy_mono_of_le {u v : M → EReal} (huv : u ≤ v) : energy θ φ hφ u ≤ energy θ φ hφ v := by
  refine sInf_le_sInf ?_
  rintro e ⟨w, hw, hvw, rfl⟩
  exact ⟨w, hw, huv.trans hvw, rfl⟩

omit [BorelSpace M] in
/-- The energy of a potential `⪯ φ` is `< +∞`. -/
theorem energy_ne_top_of_preceq (h : RelativePSHPreceq θ φ u) : energy θ φ hφ u ≠ ⊤ := by
  obtain ⟨C, hC⟩ := h.exists_add_le
  obtain ⟨D, hD⟩ := h.2
  -- `u ≤ φ + D`, and `φ + D` is a relatively minimal majorant
  have hm : RelativeEInfinity θ φ (fun x => φ x + (D : EReal)) :=
    RelativeEInfinity.add_const ⟨hφ.plurisubharmonic, SameSingularityTypeOn.refl φ univ⟩ D
  have hle : energy θ φ hφ u ≤
      (relativeEnergyOfMinimalType θ φ _ hφ.plurisubharmonic hm.1 : EReal) :=
    sInf_le ⟨_, hm, fun x => hD x (mem_univ x), rfl⟩
  exact ne_top_of_le_ne_top (EReal.coe_ne_top _) hle

omit [BorelSpace M] in
theorem bot_lt_add_coe_iff (x : EReal) (k : ℝ) : ⊥ < x + (k : EReal) ↔ ⊥ < x := by
  induction x using EReal.rec with
  | bot => simp
  | top => simp
  | coe x => simp [← EReal.coe_add]

/-- **The energy characterization of `E¹` for the `⪯` classes** (bounded model potential): for
`u ⪯ φ`, `u ∈ E¹(X, θ; φ)` iff `E(u) > -∞`. -/
theorem relativeFiniteEnergyPreceq_iff_bot_lt_energy (omega : KahlerBackground n M)
    (hφb : IsBoundedPotential φ) (h : RelativePSHPreceq θ φ u) :
    RelativeFiniteEnergyPreceq θ φ u hφ ↔ ⊥ < energy θ φ hφ u := by
  obtain ⟨C, hC⟩ := h.exists_add_le
  have hr := h.relativePSH_add (hC C le_rfl)
  have hiff := relativeFiniteEnergy_iff_bot_lt_energy omega θ hφ hφb hr
  rw [← energy_eq, energy_add_const omega hφb, bot_lt_add_coe_iff] at hiff
  constructor
  · intro hf
    exact hiff.1 (hf.relativeFiniteEnergy_add omega (hC C le_rfl))
  · intro hb
    exact relativeFiniteEnergyPreceq_of_add omega (preceq_of_relativeFiniteEnergy (hiff.2 hb))

theorem bot_lt_energy_of_preceq (omega : KahlerBackground n M) (hφb : IsBoundedPotential φ)
    (h : RelativeFiniteEnergyPreceq θ φ u hφ) : ⊥ < energy θ φ hφ u :=
  (relativeFiniteEnergyPreceq_iff_bot_lt_energy omega hφb h.1.relativePSHPreceq).1 h

theorem coe_toReal_energy_of_preceq (omega : KahlerBackground n M) (hφb : IsBoundedPotential φ)
    (h : RelativeFiniteEnergyPreceq θ φ u hφ) :
    (((energy θ φ hφ u).toReal : ℝ) : EReal) = energy θ φ hφ u :=
  EReal.coe_toReal (energy_ne_top_of_preceq h.1.relativePSHPreceq)
    (bot_lt_energy_of_preceq omega hφb h).ne'

theorem toReal_energy_add_const (omega : KahlerBackground n M) (hφb : IsBoundedPotential φ)
    (h : RelativeFiniteEnergyPreceq θ φ u hφ) (c : ℝ) :
    (energy θ φ hφ (fun x => u x + (c : EReal))).toReal =
      (energy θ φ hφ u).toReal + c * modelVolume θ φ hφ := by
  rw [energy_add_const omega hφb, ← coe_toReal_energy_of_preceq omega hφb h, ← EReal.coe_add]
  simp only [EReal.toReal_coe]

/-! ### The energy along Perron geodesics (Xia Proposition 4.3.3, `⪯` classes) -/

variable [ConnectedSpace M]

/-- **The energy is affine along Perron geodesics** (bounded model potential, `⪯` classes): if
`u₀, u₁ ⪯ φ` and their Perron geodesic `(u_t)` is a subgeodesic from `u₀` to `u₁`, then
`E(u_t) = (1 - t) E(u₀) + t E(u₁)` for `0 < t < 1`, in `[-∞, +∞)`. -/
theorem energy_finiteGeodesic_of_preceq (omega : KahlerBackground n M) (hφb : IsBoundedPotential φ)
    {u₀ u₁ : M → EReal} (h₀ : RelativePSHPreceq θ φ u₀) (h₁ : RelativePSHPreceq θ φ u₁)
    (hsub : IsSubgeodesicFrom θ.val (finiteGeodesic θ.val u₀ u₁) u₀ u₁) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    energy θ φ hφ (finiteGeodesic θ.val u₀ u₁ t) =
      ((1 - t : ℝ) : EReal) * energy θ φ hφ u₀ + ((t : ℝ) : EReal) * energy θ φ hφ u₁ := by
  obtain ⟨c, hc₀, hc₁⟩ := exists_common_add_le h₀ h₁
  have hr₀ := h₀.relativePSH_add hc₀
  have hr₁ := h₁.relativePSH_add hc₁
  have hsub' := isSubgeodesicFrom_add_const hsub c
  have ecurve : (fun s x => finiteGeodesic θ.val u₀ u₁ s x + (c : EReal)) =
      finiteGeodesic θ.val (fun x => u₀ x + (c : EReal)) (fun x => u₁ x + (c : EReal)) := by
    funext s x
    rw [finiteGeodesic_add_const]
  rw [ecurve] at hsub'
  have hUt := relativePSH_finiteGeodesic hsub'.2.2.1 hr₀ hr₁ ht
  have h := relativeMongeAmpereEnergy_finiteGeodesic omega θ hφ hφb hr₀ hr₁ hsub' ht hUt
  rw [← energy_eq, ← energy_eq, ← energy_eq, finiteGeodesic_add_const, energy_add_const omega hφb,
    energy_add_const omega hφb, energy_add_const omega hφb] at h
  exact eq_affine_of_add_coe (energy_ne_top_of_preceq h₀) (energy_ne_top_of_preceq h₁) ht h

/-- **Xia, Proposition 4.3.3, `⪯` classes** (bounded model potential): for
`u₀, u₁ ∈ E(X, θ; φ)` the energy is affine along their Perron geodesic. -/
theorem energy_finiteGeodesic_of_relativeFullMassPreceq (omega : KahlerBackground n M)
    (hφb : IsBoundedPotential φ) {u₀ u₁ : M → EReal} (h₀ : RelativeFullMassPreceq θ φ u₀ hφ)
    (h₁ : RelativeFullMassPreceq θ φ u₁ hφ) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    energy θ φ hφ (finiteGeodesic θ.val u₀ u₁ t) =
      ((1 - t : ℝ) : EReal) * energy θ φ hφ u₀ + ((t : ℝ) : EReal) * energy θ φ hφ u₁ :=
  energy_finiteGeodesic_of_preceq omega hφb h₀.relativePSHPreceq h₁.relativePSHPreceq
    (finiteGeodesic_isSubgeodesicFrom_of_relativeFullMassPreceq omega h₀ h₁) ht

/-- **Xia, Proposition 4.3.3, `⪯` classes, real form** (bounded model potential): for
`u₀, u₁ ∈ E¹(X, θ; φ)` the energies are finite and `E(u_t) = (1 - t) E(u₀) + t E(u₁)`. -/
theorem toReal_energy_finiteGeodesic_of_preceq (omega : KahlerBackground n M)
    (hφb : IsBoundedPotential φ) {u₀ u₁ : M → EReal} (h₀ : RelativeFiniteEnergyPreceq θ φ u₀ hφ)
    (h₁ : RelativeFiniteEnergyPreceq θ φ u₁ hφ) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    (energy θ φ hφ (finiteGeodesic θ.val u₀ u₁ t)).toReal =
      (1 - t) * (energy θ φ hφ u₀).toReal + t * (energy θ φ hφ u₁).toReal := by
  rw [energy_finiteGeodesic_of_relativeFullMassPreceq omega hφb h₀.1 h₁.1 ht,
    ← coe_toReal_energy_of_preceq omega hφb h₀, ← coe_toReal_energy_of_preceq omega hφb h₁,
    ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
  simp only [EReal.toReal_coe]

end Energy

/-! ### The diamond inequality and the Darvas metric for the `⪯` classes (bounded model) -/

section Distance

omit [MeasurableSpace M] [CompactSpace M] in
/-- The rooftop envelope commutes with a common finite translation. -/
theorem rooftop_add_const (θ : ClosedRealOneOneForm n M) (u v : M → EReal) (c : ℝ) :
    rooftop θ (fun x => u x + (c : EReal)) (fun x => v x + (c : EReal)) =
      fun x => rooftop θ u v x + (c : EReal) := by
  unfold rooftop
  rw [show (fun x => min (u x + (c : EReal)) (v x + (c : EReal))) =
      fun x => min (u x) (v x) + (c : EReal) from funext fun x => min_add_coe _ _ _]
  exact RooftopEnvelopeNormalization.rooftopEnvelope_add_const θ.val _ c

variable [BorelSpace M] [ConnectedSpace M] {θ : ClosedRealOneOneForm n M} {φ u v w : M → EReal}
  {hφ : IsModelPotential θ φ}

omit [MeasurableSpace M] [CompactSpace M] [BorelSpace M] [ConnectedSpace M] in
/-- Three `⪯ φ` potentials lie below `φ` after one common translation. -/
theorem exists_common_add_le₃ (hu : RelativePSHPreceq θ φ u) (hv : RelativePSHPreceq θ φ v)
    (hw : RelativePSHPreceq θ φ w) :
    ∃ c : ℝ, (∀ x, u x + (c : EReal) ≤ φ x) ∧ (∀ x, v x + (c : EReal) ≤ φ x) ∧
      ∀ x, w x + (c : EReal) ≤ φ x := by
  obtain ⟨C₀, hC₀⟩ := hu.exists_add_le
  obtain ⟨C₁, hC₁⟩ := hv.exists_add_le
  obtain ⟨C₂, hC₂⟩ := hw.exists_add_le
  exact ⟨min (min C₀ C₁) C₂, hC₀ _ ((min_le_left _ _).trans (min_le_left _ _)),
    hC₁ _ ((min_le_left _ _).trans (min_le_right _ _)), hC₂ _ (min_le_right _ _)⟩

/-- **The diamond inequality for the `⪯` classes** (Xia, SGPT, Corollary 3.1.7; bounded model
potential): if `u, v ⪯ φ` and the rooftop `u ∧ v` is a `θ`-PSH potential, then
`E(u) + E(v) ≤ E(u ∨ v) + E(u ∧ v)`, in `[-∞, +∞)`. -/
theorem energy_add_le_max_add_rooftop_of_preceq (omega : KahlerBackground n M)
    (hφb : IsBoundedPotential φ) (hu : RelativePSHPreceq θ φ u) (hv : RelativePSHPreceq θ φ v)
    (hw : IsThetaPshPotential θ.val (rooftop θ u v)) :
    energy θ φ hφ u + energy θ φ hφ v ≤
      energy θ φ hφ (fun x => max (u x) (v x)) + energy θ φ hφ (rooftop θ u v) := by
  obtain ⟨c, hc₀, hc₁⟩ := exists_common_add_le hu hv
  have hr₀ := hu.relativePSH_add hc₀
  have hr₁ := hv.relativePSH_add hc₁
  have hm := relativePSH_max hr₀ hr₁
  have hw' : RelativePSH θ φ (rooftopEnvelope θ.val
      (fun x => min (u x + (c : EReal)) (v x + (c : EReal)))) := by
    refine ⟨?_, fun x => (rooftop_le_left hr₀.1 hr₁.1 x).trans (hc₀ x)⟩
    change IsThetaPshPotential θ.val (rooftop θ _ _)
    rw [rooftop_add_const]
    exact hw.add_const c
  have hd := relativeMongeAmpereEnergy_add_le_max_add_rooftop omega θ hφ hφb hr₀ hr₁ hm hw'
  change energy θ φ hφ _ + energy θ φ hφ _ ≤ energy θ φ hφ _ + energy θ φ hφ (rooftop θ _ _) at hd
  rw [show (fun x => max (u x + (c : EReal)) (v x + (c : EReal))) =
      fun x => max (u x) (v x) + (c : EReal) from funext fun x => max_add_coe _ _ _,
    rooftop_add_const, energy_add_const omega hφb, energy_add_const omega hφb,
    energy_add_const omega hφb, energy_add_const omega hφb, add_add_add_comm,
    add_add_add_comm (energy θ φ hφ (fun x => max (u x) (v x))), ← EReal.coe_add] at hd
  exact (add_coe_le_add_coe_iff _ _ _).1 hd

/-- The rooftop of two potentials of `E(X, θ; φ)` (`⪯` class) is a `θ`-PSH potential of
`E(X, θ; φ)` (Xia, Proposition 3.1.5 for the `⪯` class). -/
theorem relativeFullMassPreceq_rooftop (omega : KahlerBackground n M)
    (hu : RelativeFullMassPreceq θ φ u hφ) (hv : RelativeFullMassPreceq θ φ v hφ) :
    RelativeFullMassPreceq θ φ (rooftop θ u v) hφ := by
  obtain ⟨c, hc₀, hc₁⟩ := exists_common_add_le hu.relativePSHPreceq hv.relativePSHPreceq
  have h := (FiniteGeodesicsFullMassAnyDim.relativeFullMass_rooftop omega θ φ _ _ hφ
    (hu.relativeFullMass_add hc₀) (hv.relativeFullMass_add hc₁)).1
  change RelativeFullMass θ φ (rooftop θ _ _) hφ at h
  rw [rooftop_add_const] at h
  exact relativeFullMassPreceq_of_add (preceq_of_relativeFullMass h)

/-- **The diamond inequality on Xia's `E(X, θ; φ)`** (`⪯` class; bounded model potential). -/
theorem energy_add_le_max_add_rooftop_of_relativeFullMassPreceq (omega : KahlerBackground n M)
    (hφb : IsBoundedPotential φ) (hu : RelativeFullMassPreceq θ φ u hφ)
    (hv : RelativeFullMassPreceq θ φ v hφ) :
    energy θ φ hφ u + energy θ φ hφ v ≤
      energy θ φ hφ (fun x => max (u x) (v x)) + energy θ φ hφ (rooftop θ u v) :=
  energy_add_le_max_add_rooftop_of_preceq omega hφb hu.relativePSHPreceq hv.relativePSHPreceq
    (relativeFullMassPreceq_rooftop omega hu hv).1

/-- The rooftop of two potentials of `E¹(X, θ; φ)` (`⪯` class) is in `E¹(X, θ; φ)`. -/
theorem relativeFiniteEnergyPreceq_rooftop (omega : KahlerBackground n M)
    (hu : RelativeFiniteEnergyPreceq θ φ u hφ) (hv : RelativeFiniteEnergyPreceq θ φ v hφ) :
    RelativeFiniteEnergyPreceq θ φ (rooftop θ u v) hφ := by
  obtain ⟨c, hc₀, hc₁⟩ := exists_common_add_le hu.1.relativePSHPreceq hv.1.relativePSHPreceq
  have h := relativeFiniteEnergy_rooftop omega (hu.relativeFiniteEnergy_add omega hc₀)
    (hv.relativeFiniteEnergy_add omega hc₁)
  rw [rooftop_add_const] at h
  exact relativeFiniteEnergyPreceq_of_add omega (preceq_of_relativeFiniteEnergy h)

/-- `d₁` is invariant under a common finite translation on `E¹(X, θ; φ)` (bounded model
potential). -/
theorem relativeD1_add_const (omega : KahlerBackground n M) (hφb : IsBoundedPotential φ)
    (hu : RelativeFiniteEnergyPreceq θ φ u hφ) (hv : RelativeFiniteEnergyPreceq θ φ v hφ) (c : ℝ) :
    relativeD1 θ φ hφ (fun x => u x + (c : EReal)) (fun x => v x + (c : EReal)) =
      relativeD1 θ φ hφ u v := by
  rw [relativeD1, relativeD1, rooftop_add_const, toReal_energy_add_const omega hφb hu,
    toReal_energy_add_const omega hφb hv,
    toReal_energy_add_const omega hφb (relativeFiniteEnergyPreceq_rooftop omega hu hv)]
  ring

theorem relativeD1_nonneg_of_preceq (omega : KahlerBackground n M) (hφb : IsBoundedPotential φ)
    (hu : RelativeFiniteEnergyPreceq θ φ u hφ) (hv : RelativeFiniteEnergyPreceq θ φ v hφ) :
    0 ≤ relativeD1 θ φ hφ u v := by
  obtain ⟨c, hc₀, hc₁⟩ := exists_common_add_le hu.1.relativePSHPreceq hv.1.relativePSHPreceq
  rw [← relativeD1_add_const omega hφb hu hv c]
  exact relativeD1_nonneg omega hφb (hu.relativeFiniteEnergy_add omega hc₀)
    (hv.relativeFiniteEnergy_add omega hc₁)

/-- **The contraction for the `⪯` classes** (Xia, SGPT, Proposition 4.3.1; bounded model
potential): `d₁(u ∧ w, v ∧ w) ≤ d₁(u, v)` on `E¹(X, θ; φ)`. -/
theorem relativeD1_rooftop_le_of_preceq (omega : KahlerBackground n M)
    (hφb : IsBoundedPotential φ) (hu : RelativeFiniteEnergyPreceq θ φ u hφ)
    (hv : RelativeFiniteEnergyPreceq θ φ v hφ) (hw : RelativeFiniteEnergyPreceq θ φ w hφ) :
    relativeD1 θ φ hφ (rooftop θ u w) (rooftop θ v w) ≤ relativeD1 θ φ hφ u v := by
  obtain ⟨c, hc₀, hc₁, hc₂⟩ := exists_common_add_le₃ hu.1.relativePSHPreceq
    hv.1.relativePSHPreceq hw.1.relativePSHPreceq
  rw [← relativeD1_add_const omega hφb (relativeFiniteEnergyPreceq_rooftop omega hu hw)
      (relativeFiniteEnergyPreceq_rooftop omega hv hw) c,
    ← relativeD1_add_const omega hφb hu hv c, ← rooftop_add_const θ u w c,
    ← rooftop_add_const θ v w c]
  exact relativeD1_rooftop_le omega hφb (hu.relativeFiniteEnergy_add omega hc₀)
    (hv.relativeFiniteEnergy_add omega hc₁) (hw.relativeFiniteEnergy_add omega hc₂)

/-- **The triangle inequality for the `⪯` classes** (Xia, SGPT, Lemma 4.3.1; bounded model
potential). -/
theorem relativeD1_triangle_of_preceq (omega : KahlerBackground n M) (hφb : IsBoundedPotential φ)
    (hu : RelativeFiniteEnergyPreceq θ φ u hφ) (hv : RelativeFiniteEnergyPreceq θ φ v hφ)
    (hw : RelativeFiniteEnergyPreceq θ φ w hφ) :
    relativeD1 θ φ hφ u v ≤ relativeD1 θ φ hφ u w + relativeD1 θ φ hφ w v := by
  obtain ⟨c, hc₀, hc₁, hc₂⟩ := exists_common_add_le₃ hu.1.relativePSHPreceq
    hv.1.relativePSHPreceq hw.1.relativePSHPreceq
  rw [← relativeD1_add_const omega hφb hu hv c, ← relativeD1_add_const omega hφb hu hw c,
    ← relativeD1_add_const omega hφb hw hv c]
  exact relativeD1_triangle omega hφb (hu.relativeFiniteEnergy_add omega hc₀)
    (hv.relativeFiniteEnergy_add omega hc₁) (hw.relativeFiniteEnergy_add omega hc₂)

/-- **Separation for the `⪯` classes** (Xia, SGPT, Lemma 4.3.1, Step 1; bounded model
potential). -/
theorem eq_of_relativeD1_eq_zero_of_preceq (omega : KahlerBackground n M)
    (hφb : IsBoundedPotential φ) (hu : RelativeFiniteEnergyPreceq θ φ u hφ)
    (hv : RelativeFiniteEnergyPreceq θ φ v hφ) (h : relativeD1 θ φ hφ u v = 0) : u = v := by
  obtain ⟨c, hc₀, hc₁⟩ := exists_common_add_le hu.1.relativePSHPreceq hv.1.relativePSHPreceq
  rw [← relativeD1_add_const omega hφb hu hv c] at h
  have e := eq_of_relativeD1_eq_zero omega hφb (hu.relativeFiniteEnergy_add omega hc₀)
    (hv.relativeFiniteEnergy_add omega hc₁) h
  funext x
  exact add_coe_injective c (congrFun e x)

/-- **`d₁` is a metric on Xia's `E¹(X, θ; φ)`** (SGPT, Lemma 4.3.1, with `⪯`), for a bounded model
potential on a connected compact Kähler manifold. -/
theorem relativeD1_isMetric_of_preceq (omega : KahlerBackground n M) (hφb : IsBoundedPotential φ) :
    (∀ u v, RelativeFiniteEnergyPreceq θ φ u hφ → RelativeFiniteEnergyPreceq θ φ v hφ →
      0 ≤ relativeD1 θ φ hφ u v) ∧
    (∀ u, RelativeFiniteEnergyPreceq θ φ u hφ → relativeD1 θ φ hφ u u = 0) ∧
    (∀ u v, relativeD1 θ φ hφ u v = relativeD1 θ φ hφ v u) ∧
    (∀ u v w, RelativeFiniteEnergyPreceq θ φ u hφ → RelativeFiniteEnergyPreceq θ φ v hφ →
      RelativeFiniteEnergyPreceq θ φ w hφ →
      relativeD1 θ φ hφ u v ≤ relativeD1 θ φ hφ u w + relativeD1 θ φ hφ w v) ∧
    (∀ u v, RelativeFiniteEnergyPreceq θ φ u hφ → RelativeFiniteEnergyPreceq θ φ v hφ →
      relativeD1 θ φ hφ u v = 0 → u = v) :=
  ⟨fun _ _ hu hv => relativeD1_nonneg_of_preceq omega hφb hu hv,
    fun _ hu => relativeD1_self hu.1.plurisubharmonic,
    fun u v => relativeD1_comm θ φ hφ u v,
    fun _ _ _ hu hv hw => relativeD1_triangle_of_preceq omega hφb hu hv hw,
    fun _ _ hu hv h => eq_of_relativeD1_eq_zero_of_preceq omega hφb hu hv h⟩

end Distance

end

end SGPT.Foundations.Analysis.Pending.RelativePreceqClasses
