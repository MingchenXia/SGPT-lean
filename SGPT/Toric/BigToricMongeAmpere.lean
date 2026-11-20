import SGPT.Toric.BigToricNewtonBody
import SGPT.Toric.PolytopeToricFullMass

/-!
# The complex and the real Monge–Ampère measures in a big toric class

Source `chapter_toric_big.tex`:

* `prop:toricMAandrealMA2`: for `φ ∈ PSH_tor(X, θ)`,
  `Trop_*(θ|_T + ddᶜφ|_T)^n = MA_ℝ(F_φ)` (`eq:tropMAmea2`) and
  `∫_X θ_φ^n = n! vol Δ(θ, φ)` (`eq:toricmass2`);
* `thm:FVtheta`, second assertion `eq:toricminsingmass`: `∫_X θ_{V_θ}^n = n! vol P_D`.

`θ_φ^n` is the source non-pluripolar measure of the `θ`-psh function `φ`.  The source
reduces to the ample case through `θ + Cω` and the polynomiality of both sides in `C`; here
the identity is proved directly, as in the ample case: on `T(ℂ)` the measure is the
Bedford–Taylor measure of the psh function `Trop^* F_φ` (computed in the base vertex
chart, where `φ + ψ_v` is the tropical pullback of the chart profile) and the toric
boundary is pluripolar, hence carries no non-pluripolar mass.  The volume is the Lebesgue
measure of `M_ℝ = ℝ^n` (the lattice cube has volume one).
-/

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set Filter MeasureTheory SGPT.PSH SGPT.PSH.VariableComplexAtlas SGPT.Convex
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.GlobalPotentialPatches
open scoped Topology ContDiff BigOperators RealInnerProductSpace

variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

namespace BigToricMetric

variable {D : ToricDivisor γ hs} (h : BigToricMetric D)

theorem latticeFunctional_eq_inner_latticeVector (m : Fin n → ℤ) (x : EuclideanSpace ℝ (Fin n)) :
    latticeFunctional m x = ⟪latticeVector m, x⟫ := by
  rw [inner_latticeVector]

/-- The convex function representing a toric potential in the base vertex chart. -/
def chartProfile (u : PolytopeToricVariety γ hs → EReal) (y : EuclideanSpace ℝ (Fin n)) : ℝ :=
  h.realProfile u
      (latticeBasisLogInverse (originalPolytopeNativeBasis γ hs (polytopeToricBaseVertex γ)) y) -
    latticeFunctional (toricCartierDatum D (polytopeToricBaseVertex γ))
      (latticeBasisLogInverse (originalPolytopeNativeBasis γ hs (polytopeToricBaseVertex γ)) y)

theorem convexOn_chartProfile {u : PolytopeToricVariety γ hs → EReal} (hu : u ∈ h.PSHTor) :
    ConvexOn ℝ univ (h.chartProfile u) := by
  have hf := (h.realProfile_mem hu).1.1
  let C := latticeBasisLogInverse (originalPolytopeNativeBasis γ hs (polytopeToricBaseVertex γ))
  have h1 : ConvexOn ℝ univ (h.realProfile u ∘ C) := by
    simpa only [preimage_univ] using hf.comp_linearMap C
  have h2 : ConvexOn ℝ univ
      (-(latticeFunctional (toricCartierDatum D (polytopeToricBaseVertex γ)) ∘ₗ C)) :=
    LinearMap.convexOn _ convex_univ
  exact h1.add h2

/-- The toric profile in terms of the chart profile and the unimodular change. -/
theorem realProfile_eq_chartProfile (u : PolytopeToricVariety γ hs → EReal)
    (x : EuclideanSpace ℝ (Fin n)) :
    h.realProfile u x =
      h.chartProfile u ((latticeBasisUnimodularChange
          (originalPolytopeNativeBasis γ hs (polytopeToricBaseVertex γ))).B x) +
        ⟪latticeVector (toricCartierDatum D (polytopeToricBaseVertex γ)), x⟫ := by
  change _ = h.realProfile u (latticeBasisLogInverse _ (latticeBasisLogMap _ x)) -
    latticeFunctional _ (latticeBasisLogInverse _ (latticeBasisLogMap _ x)) + _
  rw [latticeBasisLogInverse_logMap, latticeFunctional_eq_inner_latticeVector]
  ring

theorem baseChart_localPotential :
    IsSmoothLocalPotential h.form.val (polytopeToricBaseChart γ hs)
      (tropicalSmoothDomain n) (h.weight (polytopeToricBaseVertex γ)) := by
  refine ⟨(tropicalSmoothDomain n).isOpen, ?_, ?_, ?_⟩
  · intro z _
    change z ∈ (originalPolytopeNativeModelChart γ hs (polytopeToricBaseVertex γ)).target
    rw [originalPolytopeNativeModelChart_target]
    exact mem_univ z
  · exact (h.smooth _).contDiffOn
  · intro z _
    exact (h.coeff _ z).symm

theorem baseChart_corrected {u : PolytopeToricVariety γ hs → EReal} (hu : u ∈ h.PSHTor) :
    EqOn (fun z => chartFunction u (polytopeToricBaseChart γ hs) z +
        (h.weight (polytopeToricBaseVertex γ) z : EReal))
      (fun z => (h.chartProfile u (tropicalization z) : EReal))
      (tropicalSmoothDomain n) := by
  intro z hz
  have h' := h.vertexChart_corrected_eq (fun a => hu.2.embedding_eq γ hs a)
    (polytopeToricBaseVertex γ) hz
  change u ((originalPolytopeNativeModelChart γ hs (polytopeToricBaseVertex γ)).symm z) + _ = _
  rw [h', (h.realProfile_mem hu).2]
  simp only [tropicalPullback, chartProfile, EReal.coe_add, sub_eq_add_neg]

/-- The non-pluripolar measure `θ_φ^n` of a toric potential (source `def:npp`). -/
abbrev MA {u : PolytopeToricVariety γ hs → EReal} (hu : u ∈ h.PSHTor) :
    Measure (PolytopeToricVariety γ hs) :=
  sourcePotentialNonPluripolarMeasure h.atlasForm u hu.1

theorem patchSource_eq {u : PolytopeToricVariety γ hs → EReal} (hu : u ∈ h.PSHTor) :
    ((tropicalPotentialPatch (polytopeToricBaseChart γ hs)
      h.baseChart_localPotential (h.convexOn_chartProfile hu)
        (h.baseChart_corrected hu)).source : Set (PolytopeToricVariety γ hs)) =
      (polytopeToricBoundary γ hs)ᶜ := by
  ext p
  change p ∈ (originalPolytopeNativeModelChart γ hs (polytopeToricBaseVertex γ)).source ∧
      originalPolytopeNativeModelChart γ hs (polytopeToricBaseVertex γ) p ∈ complexTorus n ↔ _
  constructor
  · rintro ⟨hp, hz⟩
    have h' :=
      (polytopeToricVertexChart_symm_mem_compl_iff γ hs (polytopeToricBaseVertex γ) _).mpr hz
    rwa [(originalPolytopeNativeModelChart γ hs (polytopeToricBaseVertex γ)).left_inv hp] at h'
  · intro hp
    obtain ⟨a, rfl⟩ := (mem_polytopeToricBoundary_compl_iff γ hs p).mp hp
    have hsrc : polytopeToricEmbedding γ hs a ∈
        (originalPolytopeNativeModelChart γ hs (polytopeToricBaseVertex γ)).source := by
      rw [originalPolytopeNativeModelChart_source]
      exact originalPolytopeNativeOrbitMap_mem_chart_source γ hs _ a
    refine ⟨hsrc, ?_⟩
    apply (polytopeToricVertexChart_symm_mem_compl_iff γ hs (polytopeToricBaseVertex γ) _).mp
    rw [(originalPolytopeNativeModelChart γ hs (polytopeToricBaseVertex γ)).left_inv hsrc]
    exact polytopeToricEmbedding_mem_compl γ hs a

/-- Source `prop:toricMAandrealMA2`, `eq:tropMAmea2`:
`Trop_*(θ|_T + ddᶜφ|_T)^n = MA_ℝ(F_φ)`. -/
theorem map_tropicalization_MA {u : PolytopeToricVariety γ hs → EReal} (hu : u ∈ h.PSHTor) :
    Measure.map (polytopeToricLog γ hs) ((h.MA hu).restrict (polytopeToricBoundary γ hs)ᶜ) =
      alexandrovMeasure (innerₗ (EuclideanSpace ℝ (Fin n))) volume (h.profile u) := by
  let b := originalPolytopeNativeBasis γ hs (polytopeToricBaseVertex γ)
  let T := latticeBasisUnimodularChange b
  let hc := h.convexOn_chartProfile hu
  let P := tropicalPotentialPatch (polytopeToricBaseChart γ hs)
    h.baseChart_localPotential hc (h.baseChart_corrected hu)
  have hn : IsThetaPshPotential h.form.val u :=
    (isThetaPSH_iff_nativeThetaPotential h.atlasForm u).mp hu.1
  have hrestr := globalMixedMeasure_restrict_tropical_chart hn (polytopeToricBaseChart γ hs)
    h.baseChart_localPotential hc (h.baseChart_corrected hu)
  have hmeasure : (h.MA hu).restrict (polytopeToricBoundary γ hs)ᶜ =
      P.pushMeasure (tropicalCanonicalBTMeasure hc) := by
    rw [← h.patchSource_eq hu]
    exact hrestr
  have hprof : h.profile u = fun x =>
      ((h.chartProfile u (T.B x) +
        ⟪latticeVector (toricCartierDatum D (polytopeToricBaseVertex γ)), x⟫ : ℝ) : EReal) := by
    rw [(h.realProfile_mem hu).2]
    funext x
    rw [h.realProfile_eq_chartProfile]
  have hT : Measurable (@tropicalization n) :=
    (exists_compact_tropical_torus_lift (n := n) isCompact_empty).1
  have hCm : Measurable (T.C : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) :=
    T.C.continuous_of_finiteDimensional.measurable
  have hsupp : tropicalCanonicalBTMeasure hc (complexTorus n)ᶜ = 0 :=
    Pending.MixedMongeAmpere.canonicalMixedBedfordTaylorMeasure_compl (tropicalSmoothDomain n)
      (fun _ : Fin n => fun z => h.chartProfile u (tropicalization z))
      (fun _ => isLocallyBoundedPshOn_tropicalConvexProfile hc)
  have hae := aemeasurable_polytopeToricLog γ hs (h.MA hu)
  rw [hprof, T.alexandrovMeasure_comp, ← tropicalization_canonicalBTMeasure_eq_alexandrov hc,
    Measure.map_map hCm hT]
  ext s hs'
  rw [Measure.map_apply_of_aemeasurable hae hs', Measure.map_apply (hCm.comp hT) hs',
    hmeasure, Patch.pushMeasure_apply]
  have hlog : ∀ z, polytopeToricLog γ hs
      ((originalPolytopeNativeModelChart γ hs (polytopeToricBaseVertex γ)).symm z) =
        T.C (tropicalization z) := by
    intro z
    have ht : z ∈ (originalPolytopeNativeModelChart γ hs (polytopeToricBaseVertex γ)).target := by
      rw [originalPolytopeNativeModelChart_target]; exact mem_univ z
    change latticeBasisLogInverse b (tropicalization
      ((originalPolytopeNativeModelChart γ hs (polytopeToricBaseVertex γ))
        ((originalPolytopeNativeModelChart γ hs (polytopeToricBaseVertex γ)).symm z))) = _
    rw [(originalPolytopeNativeModelChart γ hs (polytopeToricBaseVertex γ)).right_inv ht]
    rfl
  have hset : (P.domain : Set (ComplexModel n)) ∩
      P.chart.val.symm ⁻¹' (polytopeToricLog γ hs ⁻¹' s) =
      complexTorus n ∩ (T.C ∘ tropicalization) ⁻¹' s := by
    ext z
    change z ∈ complexTorus n ∧ polytopeToricLog γ hs
      ((originalPolytopeNativeModelChart γ hs (polytopeToricBaseVertex γ)).symm z) ∈ s ↔
        z ∈ complexTorus n ∧ T.C (tropicalization z) ∈ s
    rw [hlog]
  rw [hset, inter_comm, measure_inter_conull hsupp]

/-- The toric boundary carries no non-pluripolar mass. -/
theorem MA_boundary {u : PolytopeToricVariety γ hs → EReal} (hu : u ∈ h.PSHTor) :
    h.MA hu (polytopeToricBoundary γ hs) = 0 := by
  have hn : IsThetaPshPotential h.form.val u :=
    (isThetaPSH_iff_nativeThetaPotential h.atlasForm u).mp hu.1
  exact Pending.GlobalNonPluripolar.globalMixedMeasure_doesNotChargeManifoldPluripolar
    (fun _ => hn.1) _ (manifoldLocallyPluripolar_polytopeToricBoundary γ hs)

/-- `∫_X θ_φ^n = ∫ MA_ℝ(F_φ)`. -/
theorem MA_univ_eq_alexandrov {u : PolytopeToricVariety γ hs → EReal} (hu : u ∈ h.PSHTor) :
    h.MA hu univ =
      alexandrovMeasure (innerₗ (EuclideanSpace ℝ (Fin n))) volume (h.profile u) univ := by
  rw [← h.map_tropicalization_MA hu,
    Measure.map_apply_of_aemeasurable (aemeasurable_polytopeToricLog γ hs _) MeasurableSet.univ,
    preimage_univ, Measure.restrict_apply_univ]
  apply le_antisymm
  · calc h.MA hu univ
        = h.MA hu (polytopeToricBoundary γ hs ∪ (polytopeToricBoundary γ hs)ᶜ) := by
          rw [union_compl_self]
      _ ≤ h.MA hu (polytopeToricBoundary γ hs) + h.MA hu (polytopeToricBoundary γ hs)ᶜ :=
          measure_union_le _ _
      _ = _ := by rw [h.MA_boundary hu, zero_add]
  · exact measure_mono (subset_univ _)

/-- Source `prop:toricMAandrealMA2`, `eq:toricmass2`: `∫_X θ_φ^n = n! vol Δ(θ, φ)`. -/
theorem MA_univ (hP : (toricDivisorPolytope D).Nonempty) {u : PolytopeToricVariety γ hs → EReal}
    (hu : u ∈ h.PSHTor) :
    h.MA hu univ = (n.factorial : ENNReal) * volume (h.newtonBody u) := by
  have hf := h.profile_mem_growthClass hP hu
  rw [h.MA_univ_eq_alexandrov, alexandrovMeasure_univ_eq_closure_rawSubgradientImage
    (innerₗ (EuclideanSpace ℝ (Fin n))) hf.1
      (lowerSemicontinuous_of_isClosedConvex (h.isClosedConvex_profile hP hu)),
    finrank_euclideanSpace_fin]
  rfl

/-- Source `thm:FVtheta`, `eq:toricminsingmass`: `∫_X θ_{V_θ}^n = n! vol P_D`. -/
theorem MA_minimalEnvelope_univ (hP : (toricDivisorPolytope D).Nonempty) :
    h.MA (h.minimalEnvelope_mem hP) univ =
      (n.factorial : ENNReal) * volume (toricDivisorPolytope D) := by
  rw [h.MA_univ hP, h.newtonBody_minimalEnvelope hP]

end BigToricMetric

end SGPT.Toric
