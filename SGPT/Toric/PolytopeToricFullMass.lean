import SGPT.Toric.PolytopeToricMongeAmpere

/-!
# Total Monge–Ampère mass and full mass of toric potentials

Source `chapter_toric_ample.tex`:

* `prop:toricMAandrealMA`, mass clauses: `∫_X ω_φ^n = ∫ MA_ℝ(F_φ) = n! vol Δ(ω, φ)` and
  `∫_X ω^n = n! vol P` (the volume on `M_ℝ = ℝ^n` gives the lattice cube mass one);
* `prop:toric-ample:L1003`: for `φ ∈ PSH_tor(X, ω)`, `φ ∈ 𝓔(X, ω)` iff
  `F_φ ∈ 𝓔(N_ℝ, P)` iff `cl Dom G_φ = P`.
-/

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set Filter MeasureTheory SGPT.PSH SGPT.PSH.VariableComplexAtlas SGPT.Convex
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology ContDiff BigOperators

variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]

/-- A closed subset of a convex body with nonempty interior and the same finite volume
is the whole body. -/
theorem eq_of_subset_of_volume_eq {K P : Set (EuclideanSpace ℝ (Fin n))} (hKP : K ⊆ P)
    (hK : IsClosed K) (hP : Convex ℝ P) (hint : (interior P).Nonempty)
    (hfin : volume P ≠ ⊤) (hvol : volume K = volume P) : K = P := by
  apply le_antisymm hKP
  intro p hp
  by_contra hpK
  have hcl : p ∈ closure (interior P) := by
    rw [hP.closure_interior_eq_closure_of_nonempty_interior hint]
    exact subset_closure hp
  obtain ⟨q, hqK, hqint⟩ := mem_closure_iff.mp hcl Kᶜ hK.isOpen_compl hpK
  have hopen : IsOpen (Kᶜ ∩ interior P) := hK.isOpen_compl.inter isOpen_interior
  have hpos : 0 < volume (Kᶜ ∩ interior P) := hopen.measure_pos volume ⟨q, hqK, hqint⟩
  have hdisj : Disjoint K (Kᶜ ∩ interior P) := disjoint_compl_right.mono_right inter_subset_left
  have hunion : K ∪ (Kᶜ ∩ interior P) ⊆ P :=
    union_subset hKP (inter_subset_right.trans interior_subset)
  have hle := measure_mono (μ := volume) hunion
  rw [measure_union hdisj hopen.measurableSet, hvol] at hle
  exact absurd hle (not_le.mpr (ENNReal.lt_add_right hfin hpos.ne'))

/-- A convex set of positive volume has nonempty interior. -/
theorem interior_nonempty_of_volume_pos {P : Set (EuclideanSpace ℝ (Fin n))} (hP : Convex ℝ P)
    (hpos : 0 < volume P) : (interior P).Nonempty := by
  by_contra h
  rw [not_nonempty_iff_eq_empty] at h
  have hfront := hP.addHaar_frontier volume
  have hsub : P ⊆ frontier P := by
    intro x hx
    rw [frontier, h, sdiff_empty]
    exact subset_closure hx
  exact absurd (measure_mono_null hsub hfront) hpos.ne'

variable (γ : K → Fin n → ℤ) (hs : latticePolytopeEdgeSmooth γ)

/-- The boundary carries no Monge–Ampère mass. -/
theorem polytopeToricMA_boundary {u : PolytopeToricVariety γ hs → EReal}
    (hu : u ∈ PolytopeToricPSH γ hs) :
    polytopeToricMA γ hs hu (polytopeToricBoundary γ hs) = 0 := by
  have hn : IsThetaPshPotential (polytopeToricKahlerForm γ hs).val u :=
    (isThetaPSH_iff_nativeThetaPotential (polytopeToricOmega γ hs) u).mp hu.1
  exact Pending.GlobalNonPluripolar.globalMixedMeasure_doesNotChargeManifoldPluripolar
    (fun _ => hn.1) _ (manifoldLocallyPluripolar_polytopeToricBoundary γ hs)

/-- Source `prop:toricMAandrealMA`: `∫_X ω_φ^n = ∫ MA_ℝ(F_φ)`. -/
theorem polytopeToricMA_univ_eq_alexandrov {u : PolytopeToricVariety γ hs → EReal}
    (hu : u ∈ PolytopeToricPSH γ hs) :
    polytopeToricMA γ hs hu univ =
      alexandrovMeasure (innerₗ (EuclideanSpace ℝ (Fin n))) volume
        (polytopeToricProfile γ hs u) univ := by
  rw [← polytopeToric_map_tropicalization_MA γ hs hu,
    Measure.map_apply_of_aemeasurable (aemeasurable_polytopeToricLog γ hs _) MeasurableSet.univ,
    preimage_univ, Measure.restrict_apply_univ]
  apply le_antisymm
  · calc polytopeToricMA γ hs hu univ
        = polytopeToricMA γ hs hu (polytopeToricBoundary γ hs ∪ (polytopeToricBoundary γ hs)ᶜ) := by
          rw [union_compl_self]
      _ ≤ polytopeToricMA γ hs hu (polytopeToricBoundary γ hs) +
          polytopeToricMA γ hs hu (polytopeToricBoundary γ hs)ᶜ := measure_union_le _ _
      _ = _ := by rw [polytopeToricMA_boundary γ hs hu, zero_add]
  · exact measure_mono (subset_univ _)

/-- Source `prop:toricMAandrealMA`: `∫_X ω_φ^n = n! vol Δ(ω, φ)`. -/
theorem polytopeToricMA_univ {u : PolytopeToricVariety γ hs → EReal}
    (hu : u ∈ PolytopeToricPSH γ hs) :
    polytopeToricMA γ hs hu univ =
      (n.factorial : ENNReal) * volume (polytopeToricNewtonBody γ hs u) := by
  have hf := polytopeToricProfile_mem_growthClass γ hs hu
  rw [polytopeToricMA_univ_eq_alexandrov, alexandrovMeasure_univ_eq_closure_rawSubgradientImage
    (innerₗ (EuclideanSpace ℝ (Fin n))) hf.1
      (lowerSemicontinuous_of_isClosedConvex (isClosedConvex_polytopeToricProfile γ hs hu)),
    finrank_euclideanSpace_fin, ← polytopeToricNewtonBody_eq_closure_rawSubgradientImage γ hs hu]

/-- Source `prop:toricMAandrealMA`: `∫_X ω^n = n! vol P`. -/
theorem polytopeToricMA_zero_univ :
    polytopeToricMA γ hs (zero_mem_polytopeToricPSH γ hs) univ =
      (n.factorial : ENNReal) * volume (polytopeToricMomentPolytope γ) := by
  rw [polytopeToricMA_univ, polytopeToricNewtonBody_zero]

/-- The non-pluripolar mass of any `ω`-psh representative of `0`. -/
theorem sourcePotentialNonPluripolarMeasure_zero_univ (w : PolytopeToricVariety γ hs → EReal)
    (hw : (ofFixedModel n (PolytopeToricVariety γ hs)).IsThetaPSH (polytopeToricOmega γ hs) w)
    (hw0 : w = 0) :
    sourcePotentialNonPluripolarMeasure (polytopeToricOmega γ hs) w hw univ =
      (n.factorial : ENNReal) * volume (polytopeToricMomentPolytope γ) := by
  subst hw0
  exact polytopeToricMA_zero_univ γ hs

omit [Nonempty K] in
theorem volume_polytopeToricMomentPolytope_lt_top :
    volume (polytopeToricMomentPolytope γ) < ⊤ :=
  (isCompact_polytopeToricMomentPolytope γ).measure_lt_top

include hs in
theorem volume_polytopeToricMomentPolytope_pos :
    0 < volume (polytopeToricMomentPolytope γ) := by
  obtain ⟨hV, _, hpos⟩ := polytopeToric_sourceModelPotential_minimalEnvelope γ hs
  rw [sourcePotentialNonPluripolarMeasure_zero_univ γ hs _ hV
    (polytopeToric_sourceMinimalEnvelope_eq_zero γ hs)] at hpos
  exact pos_of_ne_zero fun h => by simp [h] at hpos

include hs in
theorem interior_polytopeToricMomentPolytope_nonempty :
    (interior (polytopeToricMomentPolytope γ)).Nonempty :=
  interior_nonempty_of_volume_pos (convex_polytopeToricMomentPolytope γ)
    (volume_polytopeToricMomentPolytope_pos γ hs)

/-- Source `prop:toric-ample:L1003`, (1) ⇔ (3): `φ ∈ 𝓔(X, ω)` iff `cl Dom G_φ = P`. -/
theorem polytopeToric_mem_fullMass_iff {u : PolytopeToricVariety γ hs → EReal}
    (hu : u ∈ PolytopeToricPSH γ hs) :
    SourceRelativeFullMass (polytopeToricOmega γ hs)
        (sourceMinimalEnvelope (polytopeToricOmega γ hs)) u
        (polytopeToric_sourceModelPotential_minimalEnvelope γ hs) ↔
      closure (effectiveDomain (polytopeToricLegendre γ hs u)) = polytopeToricMomentPolytope γ := by
  have hV0 := polytopeToric_sourceMinimalEnvelope_eq_zero γ hs
  have hmassV := sourcePotentialNonPluripolarMeasure_zero_univ γ hs _
    (polytopeToric_sourceModelPotential_minimalEnvelope γ hs).thetaPSH hV0
  have hmassu := polytopeToricMA_univ γ hs hu
  have hfact : (n.factorial : ENNReal) ≠ 0 := by exact_mod_cast (Nat.factorial_pos n).ne'
  have hfact' : (n.factorial : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hΔ := polytopeToricNewtonBody_properties γ hs hu
  constructor
  · rintro ⟨hu', _, hmass⟩
    have hmass' : polytopeToricMA γ hs hu univ = sourcePotentialNonPluripolarMeasure
        (polytopeToricOmega γ hs) (sourceMinimalEnvelope (polytopeToricOmega γ hs))
        (polytopeToric_sourceModelPotential_minimalEnvelope γ hs).thetaPSH univ := hmass
    rw [hmassu, hmassV] at hmass'
    have hvol := (ENNReal.mul_right_inj hfact hfact').mp hmass'
    exact eq_of_subset_of_volume_eq hΔ.2.2.2 isClosed_closure
      (convex_polytopeToricMomentPolytope γ) (interior_polytopeToricMomentPolytope_nonempty γ hs)
      (volume_polytopeToricMomentPolytope_lt_top γ).ne hvol
  · intro hcl
    refine ⟨hu.1, ?_, ?_⟩
    · obtain ⟨C, hC⟩ := exists_upper_bound_polytopeToricPSH γ hs hu.1
      refine (SGPT.PSH.singularityLE_iff_exists_real _ _).mpr ⟨C, fun p => ?_⟩
      rw [hV0]
      simpa using hC p
    · change polytopeToricMA γ hs hu univ = _
      rw [hmassu, hmassV]
      change (n.factorial : ENNReal) * volume (closure (effectiveDomain
        (polytopeToricLegendre γ hs u))) = _
      rw [hcl]

/-- Source `prop:toric-ample:L1003`, (2) ⇔ (3): `F_φ ∈ 𝓔(N_ℝ, P)` iff `cl Dom G_φ = P`. -/
theorem polytopeToric_mem_fullMassClass_iff {u : PolytopeToricVariety γ hs → EReal}
    (hu : u ∈ PolytopeToricPSH γ hs) :
    polytopeToricProfile γ hs u ∈
        FullMassClass (innerₗ (EuclideanSpace ℝ (Fin n))) (polytopeToricMomentPolytope γ) ↔
      closure (effectiveDomain (polytopeToricLegendre γ hs u)) = polytopeToricMomentPolytope γ := by
  have hne := interior_polytopeToricMomentPolytope_nonempty γ hs
  have hcl := polytopeToricNewtonBody_eq_closure_rawSubgradientImage γ hs hu
  change closure (effectiveDomain (polytopeToricLegendre γ hs u)) = _ at hcl
  constructor
  · rintro ⟨_, h | h⟩
    · exact absurd h hne.ne_empty
    · rw [hcl]; exact h
  · intro h
    exact ⟨polytopeToricProfile_mem_growthClass γ hs hu, Or.inr (hcl ▸ h)⟩

end SGPT.Toric
