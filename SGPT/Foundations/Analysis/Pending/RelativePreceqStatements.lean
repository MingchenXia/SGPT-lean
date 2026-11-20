import SGPT.Foundations.Analysis.Pending.RelativePreceqClasses
import SGPT.Foundations.Analysis.Pending.TraceFoundationsEnvelopes
import SGPT.Foundations.Analysis.Pending.RooftopConvexCombBarrierStepOne

set_option autoImplicit false

/-!
# Xia's statements with the singularity-type order `⪯`

The transcription audit of 3 Oct 2026 (`fd7b7482`) found that several SGPT statements use `⪯`
(`≤` up to an additive constant) where our blueprint and Lean use the pointwise `≤`. With the
classes `RelativePSHPreceq` / `RelativeFullMassPreceq` / `RelativeFiniteEnergyPreceq` of
`RelativePreceqClasses` (Xia's Definition 3.1.5), this file states them as in the source:

* `relativeFullMassPreceq_iff_singularityEnvelope_eq` — **Xia, Proposition 3.1.14, as stated**:
  `u ∈ E(X, θ; φ) ⟺ P_θ[u] = φ`, with no normalization of `u`;
* `relativeFiniteEnergyPreceq_of_relativeEInfinity` — the first inclusion of **Xia (3.26)**,
  `E^∞(X, θ; φ) ⊆ E¹(X, θ; φ)` (the others are definitional);
* `relativeFullMassPreceq_of_singularity_between`, `relativeFiniteEnergyPreceq_of_singularity_between`
  — **Xia, Proposition 3.1.22**: if `u ⪯ v ⪯ φ` and `u ∈ E` (resp. `E¹`), then `v ∈ E` (resp. `E¹`);
* `rooftop_mass_eq_of_moreSingular` — **Xia, Lemma 3.1.2** with `γ ⪯ φ`, `η ⪯ ψ`;
* `le_add_const_of_moreSingularOn_of_singularityEnvelope_eq` — **Xia (2.34)**: `τ ⪯ Φ = P_θ[Φ]` and
  `τ ≤ B` give `τ ≤ Φ + B`.

Each is reduced to the normalized statement by a finite translation.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.RelativePreceqStatements

open FirstPass FirstPass.PositiveClasses DiagonalMass RelativePreceqClasses

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] in
/-- `⪯` is invariant under finite translations of both sides. -/
theorem moreSingularOn_add_const {u v : M → EReal} (huv : MoreSingularOn u v univ) (a b : ℝ) :
    MoreSingularOn (fun x => u x + (a : EReal)) (fun x => v x + (b : EReal)) univ :=
  ((sameSingularityTypeOn_add_const u univ a).1).trans
    (huv.trans (sameSingularityTypeOn_add_const v univ b).2)

/-- **Xia (2.34), as stated** (blueprint `xab:p-fixed-bound` with `⪯`): if `P_θ[Φ] = Φ`, `τ` is
`θ`-PSH, `τ ⪯ Φ` and `τ ≤ B` on `X`, then `τ ≤ Φ + B` everywhere. -/
theorem le_add_const_of_moreSingularOn_of_singularityEnvelope_eq {θ : SmoothRealForm n M 2}
    {Φ τ : M → EReal} (hτ : IsThetaPshPotential θ τ) (hfix : singularityEnvelope θ Φ = Φ)
    (hle : MoreSingularOn τ Φ univ) {B : ℝ} (hB : ∀ x, τ x ≤ (B : EReal)) (x : M) :
    τ x ≤ Φ x + (B : EReal) := by
  have hshift : IsThetaPshPotential θ (fun y => τ y + ((-B : ℝ) : EReal)) := hτ.add_const (-B)
  have hle0 : (fun y => τ y + ((-B : ℝ) : EReal)) ≤ 0 := fun y => by
    have h := add_le_add (hB y) (le_refl ((-B : ℝ) : EReal))
    rwa [← EReal.coe_add, add_neg_cancel, EReal.coe_zero] at h
  have hkey := le_singularityEnvelope hshift hle0
    (((sameSingularityTypeOn_add_const τ univ (-B)).1).trans hle)
  rw [hfix] at hkey
  exact (add_coe_le_iff _ _ (-B)).1 (hkey x) |>.trans_eq (by rw [neg_neg])

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]
  {θ : ClosedRealOneOneForm n M} {φ u v : M → EReal} {hφ : IsModelPotential θ φ}

omit [BorelSpace M] [ConnectedSpace M] in
theorem diagonalPotentialMass_congr {f g : M → EReal} (hfg : f = g)
    (hf : IsThetaPshPotential θ.val f) (hg : IsThetaPshPotential θ.val g) :
    diagonalPotentialMass θ f hf = diagonalPotentialMass θ g hg := by
  subst hfg
  rfl

/-- **Xia, Proposition 3.1.14, as stated** (blueprint `trace:full-mass-envelope` read with Xia's
`⪯` class): for a `θ`-PSH potential `u`, `u ∈ E(X, θ; φ)` if and only if `P_θ[u] = φ`. No
normalization of `u` is needed. -/
theorem relativeFullMassPreceq_iff_singularityEnvelope_eq (omega : KahlerBackground n M)
    (hu : IsThetaPshPotential θ.val u) :
    RelativeFullMassPreceq θ φ u hφ ↔ singularityEnvelope θ.val u = φ := by
  rw [TraceFoundationsEnvelopes.singularityEnvelope_eq_iff_exists_relativeFullMass_sub omega hφ hu]
  constructor
  · intro h
    obtain ⟨c, hc⟩ := relativeFullMassPreceq_iff_exists.1 h
    exact ⟨-c, by simpa only [neg_neg] using hc⟩
  · rintro ⟨C, hC⟩
    exact relativeFullMassPreceq_of_add (preceq_of_relativeFullMass hC)

omit [ConnectedSpace M] in
/-- **Xia, Proposition 3.1.22, full-mass case, as stated**: if `u ⪯ v ⪯ φ`, `u ∈ E(X, θ; φ)` and
`v` is `θ`-PSH, then `v ∈ E(X, θ; φ)`. -/
theorem relativeFullMassPreceq_of_singularity_between (omega : KahlerBackground n M)
    (hu : RelativeFullMassPreceq θ φ u hφ) (hv : IsThetaPshPotential θ.val v)
    (huv : MoreSingularOn u v univ) (hvφ : MoreSingularOn v φ univ) :
    RelativeFullMassPreceq θ φ v hφ := by
  obtain ⟨c, hc₀, hc₁⟩ := exists_common_add_le hu.relativePSHPreceq
    (show RelativePSHPreceq θ φ v from ⟨hv, hvφ⟩)
  have h := FiniteGeodesicsFullMassAnyDim.relativeFullMass_of_singularity_between omega
    (hu.relativeFullMass_add hc₀) (hv.add_const c) (moreSingularOn_add_const huv c c)
    (((sameSingularityTypeOn_add_const v univ c).1).trans hvφ) hc₁
  exact relativeFullMassPreceq_of_add (preceq_of_relativeFullMass h)

/-- **Xia, Proposition 3.1.22, finite-energy case, as stated**: if `u ⪯ v ⪯ φ`,
`u ∈ E¹(X, θ; φ)` and `v` is `θ`-PSH, then `v ∈ E¹(X, θ; φ)`. -/
theorem relativeFiniteEnergyPreceq_of_singularity_between (omega : KahlerBackground n M)
    (hu : RelativeFiniteEnergyPreceq θ φ u hφ) (hv : IsThetaPshPotential θ.val v)
    (huv : MoreSingularOn u v univ) (hvφ : MoreSingularOn v φ univ) :
    RelativeFiniteEnergyPreceq θ φ v hφ := by
  obtain ⟨C, hC⟩ := (show RelativePSHPreceq θ φ v from ⟨hv, hvφ⟩).exists_add_le
  obtain ⟨D, hD⟩ := huv
  -- `u + (C - D) ≤ v + C ≤ φ`
  have hle : ∀ x, u x + ((C - D : ℝ) : EReal) ≤ v x + (C : EReal) := fun x => by
    calc u x + ((C - D : ℝ) : EReal) ≤ (v x + (D : EReal)) + ((C - D : ℝ) : EReal) :=
          add_le_add (hD x (mem_univ x)) le_rfl
      _ = v x + (C : EReal) := by rw [add_assoc, ← EReal.coe_add]; ring_nf
  have hu' := hu.relativeFiniteEnergy_add omega (fun x => (hle x).trans (hC C le_rfl x))
  have h := FiniteGeodesicsFullMassAnyDim.relativeFiniteEnergy_of_between_of_kahler omega hu'
    (hv.add_const C) hle (hC C le_rfl)
  exact relativeFiniteEnergyPreceq_of_add omega (preceq_of_relativeFiniteEnergy h)

omit [ConnectedSpace M] in
/-- **The first inclusion of Xia (3.26)**: `E^∞(X, θ; φ) ⊆ E¹(X, θ; φ)` for Xia's classes. -/
theorem relativeFiniteEnergyPreceq_of_relativeEInfinity (omega : KahlerBackground n M)
    (hu : RelativeEInfinity θ φ u) : RelativeFiniteEnergyPreceq θ φ u hφ := by
  have hφm : RelativeFullMassPreceq θ φ φ hφ :=
    ⟨hφ.plurisubharmonic, MoreSingularOn.refl φ univ, rfl⟩
  refine ⟨relativeFullMassPreceq_of_singularity_between omega hφm hu.1 hu.2.2 hu.2.1, hu.1, ?_⟩
  obtain ⟨R, hR⟩ := canonicalERealAbsDiff_bounded_of_sameSingularityTypeOn θ φ u
    hφ.plurisubharmonic hu.2
  have := DiagonalMeasureRegularity.isFiniteMeasure_diagonalPotentialMeasure omega θ hu.1
  unfold relativeFiniteEnergyIntegral
  calc ∫⁻ x, canonicalERealAbsDiff (φ x) (u x) ∂ diagonalPotentialMeasure θ u hu.1
      ≤ ∫⁻ _, (R : ℝ≥0∞) ∂ diagonalPotentialMeasure θ u hu.1 := lintegral_mono fun x => hR x
    _ < ⊤ := by
        rw [lintegral_const]
        exact ENNReal.mul_lt_top ENNReal.coe_lt_top (measure_lt_top _ _)

omit [ConnectedSpace M] in
/-- **Xia (3.26) for the `⪯` classes**: `E^∞ ⊆ E¹ ⊆ E ⊆ PSH(X, θ; φ)`. -/
theorem inclusions_3_26 (omega : KahlerBackground n M) :
    (∀ u, RelativeEInfinity θ φ u → RelativeFiniteEnergyPreceq θ φ u hφ) ∧
    (∀ u, RelativeFiniteEnergyPreceq θ φ u hφ → RelativeFullMassPreceq θ φ u hφ) ∧
    (∀ u, RelativeFullMassPreceq θ φ u hφ → RelativePSHPreceq θ φ u) :=
  ⟨fun _ hu => relativeFiniteEnergyPreceq_of_relativeEInfinity omega hu, fun _ hu => hu.1,
    fun _ hu => hu.relativePSHPreceq⟩

/-- **Xia, Lemma 3.1.2, as stated (`⪯`)**: let `A, B` be `θ`-PSH with `θ`-PSH rooftop of positive
mass, and `g ⪯ A`, `h ⪯ B` `θ`-PSH with the masses of `A`, `B`. Then the rooftop of `g, h` is a
`θ`-PSH potential with the mass of the rooftop of `A, B`. -/
theorem rooftop_mass_eq_of_moreSingular (omega : KahlerBackground n M)
    {A B g h : M → EReal} (hA : IsThetaPshPotential θ.val A) (hB : IsThetaPshPotential θ.val B)
    (hAB : IsThetaPshPotential θ.val (rooftopEnvelope θ.val (fun x => min (A x) (B x))))
    (hpos : 0 < diagonalPotentialMass θ _ hAB)
    (hg : IsThetaPshPotential θ.val g) (hgA : MoreSingularOn g A univ)
    (hmg : diagonalPotentialMass θ g hg = diagonalPotentialMass θ A hA)
    (hh : IsThetaPshPotential θ.val h) (hhB : MoreSingularOn h B univ)
    (hmh : diagonalPotentialMass θ h hh = diagonalPotentialMass θ B hB) :
    ∃ hgh : IsThetaPshPotential θ.val (rooftopEnvelope θ.val (fun x => min (g x) (h x))),
      diagonalPotentialMass θ _ hgh = diagonalPotentialMass θ _ hAB := by
  obtain ⟨C₁, hC₁⟩ := hgA
  obtain ⟨C₂, hC₂⟩ := hhB
  set C : ℝ := max C₁ C₂
  have hg' := hg.add_const (-C)
  have hh' := hh.add_const (-C)
  have hle : ∀ {w W : M → EReal} {D : ℝ}, (∀ x ∈ univ, w x ≤ W x + (D : EReal)) → D ≤ C →
      (fun x => w x + ((-C : ℝ) : EReal)) ≤ W := fun {w W D} hD hDC x => by
    show w x + ((-C : ℝ) : EReal) ≤ W x
    rw [add_coe_le_iff, neg_neg]
    exact (hD x (mem_univ x)).trans (add_le_add le_rfl (EReal.coe_le_coe_iff.2 hDC))
  have hmg' : diagonalPotentialMass θ _ hg' = diagonalPotentialMass θ A hA :=
    ((FiniteGeodesicsFullMassAnyDim.finiteTranslation_invariance θ hg (-C)).2.2 hg').trans hmg
  have hmh' : diagonalPotentialMass θ _ hh' = diagonalPotentialMass θ B hB :=
    ((FiniteGeodesicsFullMassAnyDim.finiteTranslation_invariance θ hh (-C)).2.2 hh').trans hmh
  obtain ⟨hgh', hm⟩ := RooftopEnvelopeLatticeMass.rooftop_mass_eq_of_le_of_mass_eq₂ omega θ hA hB
    hAB hpos hg' (hle hC₁ (le_max_left _ _)) hmg' hh' (hle hC₂ (le_max_right _ _)) hmh'
  have e : rooftopEnvelope θ.val (fun x => min (g x + ((-C : ℝ) : EReal)) (h x + ((-C : ℝ) : EReal)))
      = fun x => rooftopEnvelope θ.val (fun x => min (g x) (h x)) x + ((-C : ℝ) : EReal) := by
    have := rooftop_add_const θ g h (-C)
    simpa only [RelativeDarvasDistance.rooftop] using this
  have hgh'' : IsThetaPshPotential θ.val
      (fun x => rooftopEnvelope θ.val (fun x => min (g x) (h x)) x + ((-C : ℝ) : EReal)) := e ▸ hgh'
  have hgh : IsThetaPshPotential θ.val (rooftopEnvelope θ.val (fun x => min (g x) (h x))) := by
    have := hgh''.add_const C
    rwa [show (C : EReal) = ((-(-C) : ℝ) : EReal) by rw [neg_neg], translate_translate_neg] at this
  refine ⟨hgh, ?_⟩
  rw [← hm]
  exact ((FiniteGeodesicsFullMassAnyDim.finiteTranslation_invariance θ hgh (-C)).2.2 hgh'').symm.trans
    (diagonalPotentialMass_congr e.symm _ _)
