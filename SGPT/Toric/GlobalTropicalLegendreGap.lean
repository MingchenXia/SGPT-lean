import SGPT.Toric.GlobalTropicalMixedEnergy
import SGPT.Toric.TropicalFullMassCriterion
import SGPT.Convex.SubgradientMeasure
import SGPT.Convex.MixedAlexandrovIdentities

set_option autoImplicit false
noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.GlobalPotentialPatches
open SGPT.Foundations.Analysis.Pending
open scoped Topology ENNReal RealInnerProductSpace

namespace SGPT.Convex

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "B" => innerₗ E

private theorem legendreProfile_closed (f : RealConvexFunction E) :
    LowerSemicontinuous (fun a => (f.val a : EReal)) := by
  have hfull : effectiveDomain (fun a => (f.val a : EReal)) = univ := by
    ext a
    simp [effectiveDomain]
  exact lowerSemicontinuous_of_isClosedConvex
    (isClosedConvex_of_isProper_full_domain (isProper_coe_of_convexOn f.property) hfull)

private theorem legendreReferenceBody_data (f₀ : RealConvexFunction E) :
    let P := closure (rawSubgradientImage B (fun a => (f₀.val a : EReal)))
    P.Nonempty ∧ Convex ℝ P ∧ (fun a => (f₀.val a : EReal)) ∈ FullMassClass B P := by
  dsimp only
  have hp := isProper_coe_of_convexOn f₀.property
  have hc := closure_rawSubgradientImage_eq_closure_effectiveDomain_conjugate
    B hp (legendreProfile_closed f₀)
  have hne : (closure (rawSubgradientImage B (fun a => (f₀.val a : EReal)))).Nonempty := by
    rw [hc]
    exact (isProper_conjugate_of_isContPerfPair B hp).2.1.closure
  have hconv : Convex ℝ (closure (rawSubgradientImage B (fun a => (f₀.val a : EReal)))) := by
    rw [hc]
    exact (convex_effectiveDomain (isConvex_conjugate B _)).closure
  have hfull : effectiveDomain (fun a => (f₀.val a : EReal)) = univ := by
    ext a
    simp [effectiveDomain]
  have hbound := singularityLE_support_of_full_domain_rawSubgradientImage_subset B hp hfull
    (subset_closure : rawSubgradientImage B (fun a => (f₀.val a : EReal)) ⊆
      closure (rawSubgradientImage B (fun a => (f₀.val a : EReal))))
  exact ⟨hne, hconv, ⟨⟨hp, hbound⟩, Or.inr rfl⟩⟩

/-- The two genuine Haar-a.e. domain and derivative producers give finite
conjugates and the literal two-gradient Fenchel inequalities, including n=0
and the null ordinary-interior branch of the original full-mass class. -/
theorem ae_conjugate_gap_between_endpoint_gradients
    {P : Set E} (hP : IsCompact P) (hne : P.Nonempty) (hconv : Convex ℝ P)
    (f g : RealConvexFunction E)
    (hf : (fun a => (f.val a : EReal)) ∈ FullMassClass B P)
    (hg : (fun a => (g.val a : EReal)) ∈ FullMassClass B P) :
    ∀ᵐ p ∂(volume : Measure E).restrict P,
      conjugate B (fun a => (f.val a : EReal)) p ≠ ⊤ ∧
      conjugate B (fun a => (f.val a : EReal)) p ≠ ⊥ ∧
      conjugate B (fun a => (g.val a : EReal)) p ≠ ⊤ ∧
      conjugate B (fun a => (g.val a : EReal)) p ≠ ⊥ ∧
      f.val (conjugateGradient B (fun a => (f.val a : EReal)) p) -
          g.val (conjugateGradient B (fun a => (f.val a : EReal)) p) ≤
        (conjugate B (fun a => (g.val a : EReal)) p).toReal -
          (conjugate B (fun a => (f.val a : EReal)) p).toReal ∧
      (conjugate B (fun a => (g.val a : EReal)) p).toReal -
          (conjugate B (fun a => (f.val a : EReal)) p).toReal ≤
        f.val (conjugateGradient B (fun a => (g.val a : EReal)) p) -
          g.val (conjugateGradient B (fun a => (g.val a : EReal)) p) := by
  let F : E → EReal := fun a => (f.val a : EReal)
  let G : E → EReal := fun a => (g.val a : EReal)
  have hFp : IsProper F := hf.1.1
  have hGp : IsProper G := hg.1.1
  have hFc := isProper_conjugate_of_isContPerfPair B hFp
  have hGc := isProper_conjugate_of_isContPerfPair B hGp
  have hFd := interior_effectiveDomain_conjugate_ae_eq_of_mem_fullMassClass
    B (ν := (volume : Measure E)) hP hne hconv hf
  have hGd := interior_effectiveDomain_conjugate_ae_eq_of_mem_fullMassClass
    B (ν := (volume : Measure E)) hP hne hconv hg
  have hFdiff := ae_differentiableAt_toReal_of_isProper
    (μ := (volume : Measure E)) hFc
  have hGdiff := ae_differentiableAt_toReal_of_isProper
    (μ := (volume : Measure E)) hGc
  filter_upwards [ae_restrict_mem hP.measurableSet, ae_restrict_of_ae hFd,
    ae_restrict_of_ae hGd, ae_restrict_of_ae hFdiff, ae_restrict_of_ae hGdiff]
    with p hp hfd hgd hdiffF hdiffG
  have hpF : p ∈ interior (effectiveDomain (conjugate B F)) := by
    change (p ∈ interior (effectiveDomain (conjugate B F))) = (p ∈ P) at hfd
    exact hfd.symm.mp hp
  have hpG : p ∈ interior (effectiveDomain (conjugate B G)) := by
    change (p ∈ interior (effectiveDomain (conjugate B G))) = (p ∈ P) at hgd
    exact hgd.symm.mp hp
  have hpFD : p ∈ effectiveDomain (conjugate B F) := interior_subset hpF
  have hpGD : p ∈ effectiveDomain (conjugate B G) := interior_subset hpG
  have hFtop : conjugate B F p ≠ ⊤ := ne_of_lt hpFD
  have hGtop : conjugate B G p ≠ ⊤ := ne_of_lt hpGD
  have hFfinite : conjugate B F p = ((conjugate B F p).toReal : EReal) :=
    (EReal.coe_toReal hFtop (hFc.2.2 p)).symm
  have hGfinite : conjugate B G p = ((conjugate B G p).toReal : EReal) :=
    (EReal.coe_toReal hGtop (hGc.2.2 p)).symm
  let xf := conjugateGradient B F p
  let xg := conjugateGradient B G p
  have hxf : xf ∈ rawSubdifferential (innerₗ E).flip (conjugate B F) p := by
    rw [rawSubdifferential_conjugate_eq_singleton_of_differentiableAt
      B hFp hpF (hdiffF hpF)]
    exact mem_singleton _
  have hxg : xg ∈ rawSubdifferential (innerₗ E).flip (conjugate B G) p := by
    rw [rawSubdifferential_conjugate_eq_singleton_of_differentiableAt
      B hGp hpG (hdiffG hpG)]
    exact mem_singleton _
  have hxfD : xf ∈ effectiveDomain F := by
    change (f.val xf : EReal) < ⊤
    exact EReal.coe_lt_top _
  have hxgD : xg ∈ effectiveDomain G := by
    change (g.val xg : EReal) < ⊤
    exact EReal.coe_lt_top _
  have hpxf := (mem_rawSubdifferential_iff_conjugate_rawSubdifferential
    B hFp (legendreProfile_closed f) hxfD (interior_subset hpF)).mpr hxf
  have hpxg := (mem_rawSubdifferential_iff_conjugate_rawSubdifferential
    B hGp (legendreProfile_closed g) hxgD (interior_subset hpG)).mpr hxg
  rw [rawSubdifferential_eq_subdifferential_of_isProper B hFp] at hpxf
  rw [rawSubdifferential_eq_subdifferential_of_isProper B hGp] at hpxg
  have htouchF : (conjugate B F p).toReal = B xf p - f.val xf := by
    rw [(mem_subdifferential_iff_fenchel B hFp hxfD).mp hpxf]
    simp only [F, ← EReal.coe_sub, EReal.toReal_coe]
  have htouchG : (conjugate B G p).toReal = B xg p - g.val xg := by
    rw [(mem_subdifferential_iff_fenchel B hGp hxgD).mp hpxg]
    simp only [G, ← EReal.coe_sub, EReal.toReal_coe]
  have hcrossG : B xf p - g.val xf ≤ (conjugate B G p).toReal := by
    have h := le_iSup (fun x => (B x p : EReal) - G x) xf
    change (B xf p : EReal) - (g.val xf : EReal) ≤ conjugate B G p at h
    rw [← EReal.coe_sub, hGfinite] at h
    exact EReal.coe_le_coe_iff.mp h
  have hcrossF : B xg p - f.val xg ≤ (conjugate B F p).toReal := by
    have h := le_iSup (fun x => (B x p : EReal) - F x) xg
    change (B xg p : EReal) - (f.val xg : EReal) ≤ conjugate B F p at h
    rw [← EReal.coe_sub, hFfinite] at h
    exact EReal.coe_le_coe_iff.mp h
  refine ⟨hFtop, hFc.2.2 p, hGtop, hGc.2.2 p, ?_, ?_⟩ <;>
    dsimp only [xf, xg] at * <;> linarith

end SGPT.Convex

namespace SGPT.Toric

open SGPT.Convex FirstPass.PositiveClasses RelativePreceqClasses

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M]
  {θ : ClosedRealOneOneForm n M} {φ u v : M → EReal}
  {hφ : IsModelPotential θ φ} {r : ComplexModel n → ℝ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "B" => innerₗ E
local notation "D" => tropicalSmoothDomain n

private theorem legendreDiagonal_native_mass
    (hu : IsThetaPshPotential θ.val u)
    (e : ComplexChart n M) (hD : (D : Set (ComplexModel n)) ⊆ e.val.target)
    (hr : IsSmoothLocalPotential θ.val e D r) (f : RealConvexFunction E)
    (hf : EqOn (fun z => chartFunction u e z + (r z : EReal))
      (fun z => (f.val (tropicalization z) : EReal)) D)
    {ψ : M → EReal} (hψ : IsGlobalQuasiPshPotential (n := n) ψ)
    (hpole : (e.val.source ∩ e.val ⁻¹' (D : Set (ComplexModel n)))ᶜ ⊆ {x | ψ x = ⊥}) :
    DiagonalMass.diagonalPotentialMass θ u hu =
      alexandrovMeasure B (volume : Measure E) (fun a => (f.val a : EReal)) univ := by
  let F : Fin n → RealConvexFunction E := fun _ => f
  let P := mixedTropicalPotentialPatch e hD (fun _ => hr) F (fun _ => hf)
  let μ := tropicalCanonicalMixedBTMeasure F
  have hglobal := globalMixedMeasure_eq_mixedTropical_chart_pushMeasure
    (fun _ : Fin n => hu.1) e hD (fun _ => hr) F (fun _ => hf) hψ hpole
  have hnull : μ (D : Set (ComplexModel n))ᶜ = 0 := tropicalCanonicalMixedBTMeasure_compl F
  have htotal : μ (D : Set (ComplexModel n)) = μ univ := by
    have h := measure_add_measure_compl (μ := μ) (tropicalSmoothDomain n).isOpen.measurableSet
    rwa [hnull, add_zero] at h
  have hmass : DiagonalMass.diagonalPotentialMass θ u hu = μ univ := by
    change GlobalNonPluripolar.globalMixedMeasure
      (fun _ : Fin n => θ) (fun _ => u) (fun _ => hu.1) univ = μ univ
    rw [hglobal, P.pushMeasure_apply]
    change μ ((D : Set (ComplexModel n)) ∩ e.val.symm ⁻¹' univ) = μ univ
    simpa only [preimage_univ, inter_univ] using htotal
  have hmap := tropicalization_canonicalMixedBTMeasure_eq_mixedAlexandrov F
  rw [mixedAlexandrovMeasure_diagonal] at hmap
  obtain ⟨hT, _⟩ := exists_compact_tropical_torus_lift (n := n) isCompact_empty
  have hreal := congrArg (fun ν : Measure E => ν univ) hmap
  rw [Measure.map_apply hT MeasurableSet.univ, preimage_univ] at hreal
  exact hmass.trans hreal

/-- Actual compact reference raw-image geometry, native additive order, the
whole mixed NP/chart producer and SAME original Haar full-mass iff internally
manufacture the reference and endpoint geometric real full-mass memberships. -/
theorem fullMassClass_of_nativeRelativeFullMass_tropical_chart
    (hu : RelativeFullMassPreceq θ φ u hφ)
    (e : ComplexChart n M) (hD : (D : Set (ComplexModel n)) ⊆ e.val.target)
    (hr : IsSmoothLocalPotential θ.val e D r) (f₀ f : RealConvexFunction E)
    (h₀ : EqOn (fun z => chartFunction φ e z + (r z : EReal))
      (fun z => (f₀.val (tropicalization z) : EReal)) D)
    (hf : EqOn (fun z => chartFunction u e z + (r z : EReal))
      (fun z => (f.val (tropicalization z) : EReal)) D)
    {ψ : M → EReal} (hψ : IsGlobalQuasiPshPotential (n := n) ψ)
    (hpole : (e.val.source ∩ e.val ⁻¹' (D : Set (ComplexModel n)))ᶜ ⊆ {x | ψ x = ⊥})
    (hP : IsCompact (closure (rawSubgradientImage B (fun a => (f₀.val a : EReal))))) :
    let P := closure (rawSubgradientImage B (fun a => (f₀.val a : EReal)))
    P.Nonempty ∧ Convex ℝ P ∧
      (fun a => (f₀.val a : EReal)) ∈ FullMassClass B P ∧
      (fun a => (f.val a : EReal)) ∈ FullMassClass B P := by
  dsimp only
  let P := closure (rawSubgradientImage B (fun a => (f₀.val a : EReal)))
  obtain ⟨hne, hconv, hRef⟩ := legendreReferenceBody_data f₀
  have horder : SGPT.PSH.SingularityLE (fun a => (f.val a : EReal))
      (fun a => (f₀.val a : EReal)) := by
    obtain ⟨C, hC⟩ := hu.relativePSHPreceq.2
    refine (SGPT.PSH.singularityLE_iff_exists_real _ _).mpr ⟨C, fun a => ?_⟩
    let z := expCoordinates a
    have hz : z ∈ D := expCoordinates_mem_complexTorus a
    have hfz : chartFunction u e z + (r z : EReal) = (f.val a : EReal) := by
      simpa only [z, tropicalization_expCoordinates] using hf hz
    have h₀z : chartFunction φ e z + (r z : EReal) = (f₀.val a : EReal) := by
      simpa only [z, tropicalization_expCoordinates] using h₀ hz
    have h := add_le_add (hC (e.val.symm z) (mem_univ _)) (le_refl (r z : EReal))
    change chartFunction u e z + (r z : EReal) ≤
      (chartFunction φ e z + (C : EReal)) + (r z : EReal) at h
    rw [add_right_comm, hfz, h₀z] at h
    exact h
  have hGrowth : (fun a => (f.val a : EReal)) ∈ GrowthClass B P :=
    ⟨isProper_coe_of_convexOn f.property,
      SGPT.PSH.singularityLE_trans horder hRef.1.2⟩
  have hmass : alexandrovMeasure B (volume : Measure E) (fun a => (f.val a : EReal)) univ =
      alexandrovMeasure B (volume : Measure E) (fun a => (f₀.val a : EReal)) univ := by
    rw [← legendreDiagonal_native_mass hu.plurisubharmonic e hD hr f hf hψ hpole,
      ← legendreDiagonal_native_mass hφ.plurisubharmonic e hD hr f₀ h₀ hψ hpole]
    exact hu.mass_eq hu.plurisubharmonic
  have hRefMass := alexandrovMeasure_univ_eq_body_of_mem_fullMassClass
    B (ν := (volume : Measure E)) hP hne hconv hRef
  have hFull := (mem_fullMassClass_iff_alexandrovMeasure_univ_eq_euclidean
    B hP hne hconv hGrowth).mpr (hmass.trans hRefMass)
  exact ⟨hne, hconv, hRef, hFull⟩

section NativeE1

variable [ConnectedSpace M]

/-- Native E1 produces both real full-mass memberships and endpoint L1. The
actual nonzero n! gradient pushforwards and the genuine Fenchel sandwich
then dominate the signed conjugate gap; no real-side L1 or finite-value
certificate is supplied, and the original empty-interior branch is retained. -/
theorem integrable_conjugate_gap_of_native_E1_tropical_chart
    (omega : KahlerBackground n M)
    (hu : RelativeFiniteEnergyPreceq θ φ u hφ)
    (hv : RelativeFiniteEnergyPreceq θ φ v hφ)
    (e : ComplexChart n M) (hD : (D : Set (ComplexModel n)) ⊆ e.val.target)
    (hr : IsSmoothLocalPotential θ.val e D r) (f₀ f g : RealConvexFunction E)
    (h₀ : EqOn (fun z => chartFunction φ e z + (r z : EReal))
      (fun z => (f₀.val (tropicalization z) : EReal)) D)
    (hf : EqOn (fun z => chartFunction u e z + (r z : EReal))
      (fun z => (f.val (tropicalization z) : EReal)) D)
    (hg : EqOn (fun z => chartFunction v e z + (r z : EReal))
      (fun z => (g.val (tropicalization z) : EReal)) D)
    {ψ : M → EReal} (hψ : IsGlobalQuasiPshPotential (n := n) ψ)
    (hpole : (e.val.source ∩ e.val ⁻¹' (D : Set (ComplexModel n)))ᶜ ⊆ {x | ψ x = ⊥})
    (hP : IsCompact (closure (rawSubgradientImage B (fun a => (f₀.val a : EReal))))) :
    let P := closure (rawSubgradientImage B (fun a => (f₀.val a : EReal)))
    (∀ᵐ p ∂(volume : Measure E).restrict P,
      conjugate B (fun a => (f.val a : EReal)) p ≠ ⊤ ∧
      conjugate B (fun a => (f.val a : EReal)) p ≠ ⊥ ∧
      conjugate B (fun a => (g.val a : EReal)) p ≠ ⊤ ∧
      conjugate B (fun a => (g.val a : EReal)) p ≠ ⊥) ∧
    Integrable (fun p =>
      (conjugate B (fun a => (g.val a : EReal)) p).toReal -
        (conjugate B (fun a => (f.val a : EReal)) p).toReal)
      ((volume : Measure E).restrict P) := by
  dsimp only
  let P := closure (rawSubgradientImage B (fun a => (f₀.val a : EReal)))
  obtain ⟨hne, hconv, _, hF⟩ := fullMassClass_of_nativeRelativeFullMass_tropical_chart
    hu.1 e hD hr f₀ f h₀ hf hψ hpole hP
  obtain ⟨_, _, _, hG⟩ := fullMassClass_of_nativeRelativeFullMass_tropical_chart
    hv.1 e hD hr f₀ g h₀ hg hψ hpole hP
  have hsandwich := ae_conjugate_gap_between_endpoint_gradients hP hne hconv f g hF hG
  refine ⟨hsandwich.mono (fun _ h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩), ?_⟩
  have hiF := integrable_tropical_endpoint_gap_mixedAlexandrov
    omega hu hv e hD hr f g hf hg hψ hpole (Fin.last n)
  have hiG := integrable_tropical_endpoint_gap_mixedAlexandrov
    omega hu hv e hD hr f g hf hg hψ hpole (0 : Fin (n + 1))
  have htupleF : (fun i : Fin n => if i.val < (Fin.last n).val then f else g) =
      (fun _ : Fin n => f) := by
    funext i
    simp only [Fin.val_last, if_pos i.isLt]
  have htupleG : (fun i : Fin n => if i.val < (0 : Fin (n + 1)).val then f else g) =
      (fun _ : Fin n => g) := by
    funext i
    simp
  rw [htupleF, mixedAlexandrovMeasure_diagonal] at hiF
  rw [htupleG, mixedAlexandrovMeasure_diagonal] at hiG
  rw [alexandrovMeasure_eq_gradient_pushforward_of_mem_fullMassClass B hP hne hconv hF] at hiF
  rw [alexandrovMeasure_eq_gradient_pushforward_of_mem_fullMassClass B hP hne hconv hG] at hiG
  have hcoef : ((Module.finrank ℝ E).factorial : ENNReal) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (Module.finrank ℝ E)
  have hcoefTop : ((Module.finrank ℝ E).factorial : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hiFmap := (integrable_smul_measure hcoef hcoefTop).mp hiF
  have hiGmap := (integrable_smul_measure hcoef hcoefTop).mp hiG
  have hiA := hiFmap.comp_measurable (measurable_conjugateGradient B (fun a => (f.val a : EReal)))
  have hiB := hiGmap.comp_measurable (measurable_conjugateGradient B (fun a => (g.val a : EReal)))
  have hmeas : Measurable (fun p =>
      (conjugate B (fun a => (g.val a : EReal)) p).toReal -
        (conjugate B (fun a => (f.val a : EReal)) p).toReal) :=
    (measurable_conjugate B (fun a => (g.val a : EReal))).ereal_toReal.sub
      (measurable_conjugate B (fun a => (f.val a : EReal))).ereal_toReal
  apply (hiA.norm.add hiB.norm).mono' hmeas.aestronglyMeasurable
  filter_upwards [hsandwich] with p hp
  have hlow := hp.2.2.2.2.1
  have hupp := hp.2.2.2.2.2
  simp only [Pi.add_apply, Function.comp_def, Real.norm_eq_abs]
  apply abs_le.mpr
  constructor
  · exact (by
      have h := neg_abs_le (f.val (conjugateGradient B (fun a => (f.val a : EReal)) p) -
        g.val (conjugateGradient B (fun a => (f.val a : EReal)) p))
      have h' := abs_nonneg (f.val (conjugateGradient B (fun a => (g.val a : EReal)) p) -
        g.val (conjugateGradient B (fun a => (g.val a : EReal)) p))
      linarith)
  · exact (by
      have h := le_abs_self (f.val (conjugateGradient B (fun a => (g.val a : EReal)) p) -
        g.val (conjugateGradient B (fun a => (g.val a : EReal)) p))
      have h' := abs_nonneg (f.val (conjugateGradient B (fun a => (f.val a : EReal)) p) -
        g.val (conjugateGradient B (fun a => (f.val a : EReal)) p))
      linarith)

end NativeE1

end SGPT.Toric
