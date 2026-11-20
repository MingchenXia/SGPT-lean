import SGPT.Toric.TropicalMixedBedfordTaylor
import SGPT.Foundations.Analysis.Pending.GlobalDiagonalScaling
import SGPT.Foundations.Analysis.Pending.PatchLocalBoundedMeasure
import SGPT.Foundations.Analysis.Pending.CompactNonPluripolarChartWeightIntegrability
import SGPT.Foundations.Analysis.Pending.SingularModelFiniteEnergyMixedCocycle

set_option autoImplicit false
noncomputable section

namespace SGPT.Toric

open Set Filter MeasureTheory TopologicalSpace SGPT.Convex
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.GlobalPotentialPatches
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.MixedMongeAmpere
open scoped Topology BigOperators ENNReal RealInnerProductSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {θ : Fin n → ClosedRealOneOneForm n M} {U : Fin n → M → EReal}
  {ρ : Fin n → ComplexModel n → ℝ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "D" => tropicalSmoothDomain n

/-- Genuine target inclusion, actual local potentials and literal finite-convex
source values manufacture the SAME mixed patch, retaining the empty tuple. -/
def mixedTropicalPotentialPatch (e : ComplexChart n M)
    (hD : (D : Set (ComplexModel n)) ⊆ e.val.target)
    (hρ : ∀ i, IsSmoothLocalPotential (θ i).val e D (ρ i))
    (F : Fin n → RealConvexFunction E)
    (heq : ∀ i, EqOn (fun z => chartFunction (U i) e z + (ρ i z : EReal))
      (fun z => ((F i).val (tropicalization z) : EReal)) D) : Patch θ U where
  chart := e
  domain := D
  domain_le_target := hD
  potential := ρ
  localPotential := hρ
  plurisubharmonic := fun i => plurisubharmonicOn_congr (tropicalSmoothDomain n).isOpen
    (isLocallyBoundedPshOn_tropicalConvexProfile (F i).property).1
    (fun _z hz => (heq i hz).symm)

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- Genuine finite-cover NP restriction and locally bounded comparison give the
actual canonical mixed product, without a caller measure-equality certificate. -/
theorem globalMixedMeasure_restrict_mixedTropical_chart
    (hu : ∀ i, ThetaPlurisubharmonic (θ i).val (U i)) (e : ComplexChart n M)
    (hD : (D : Set (ComplexModel n)) ⊆ e.val.target)
    (hρ : ∀ i, IsSmoothLocalPotential (θ i).val e D (ρ i))
    (F : Fin n → RealConvexFunction E)
    (heq : ∀ i, EqOn (fun z => chartFunction (U i) e z + (ρ i z : EReal))
      (fun z => ((F i).val (tropicalization z) : EReal)) D) :
    (GlobalNonPluripolar.globalMixedMeasure θ U hu).restrict
      (mixedTropicalPotentialPatch e hD hρ F heq).source =
      (mixedTropicalPotentialPatch e hD hρ F heq).pushMeasure
        (tropicalCanonicalMixedBTMeasure F) := by
  rw [GlobalNonPluripolar.globalMixedMeasure_restrict_patch]
  unfold GlobalNonPluripolar.patchMeasure
  apply congrArg (mixedTropicalPotentialPatch e hD hρ F heq).pushMeasure
  exact MixedNonPluripolar.mixedTruncationLimitMeasure_eq_canonical_of_eqOn
    (fun i => isLocallyBoundedPshOn_tropicalConvexProfile (F i).property)
    (mixedTropicalPotentialPatch e hD hρ F heq).plurisubharmonic heq

/-- Independent actual quasi-PSH pole geometry manufactures boundary nullity and
the whole mixed NP measure, including n=0 without nonexistent slot data. -/
theorem globalMixedMeasure_eq_mixedTropical_chart_pushMeasure
    (hu : ∀ i, ThetaPlurisubharmonic (θ i).val (U i)) (e : ComplexChart n M)
    (hD : (D : Set (ComplexModel n)) ⊆ e.val.target)
    (hρ : ∀ i, IsSmoothLocalPotential (θ i).val e D (ρ i))
    (F : Fin n → RealConvexFunction E)
    (heq : ∀ i, EqOn (fun z => chartFunction (U i) e z + (ρ i z : EReal))
      (fun z => ((F i).val (tropicalization z) : EReal)) D)
    {ψ : M → EReal} (hψ : IsGlobalQuasiPshPotential (n := n) ψ)
    (hpole : ((mixedTropicalPotentialPatch e hD hρ F heq).source : Set M)ᶜ ⊆
      {x | ψ x = ⊥}) :
    GlobalNonPluripolar.globalMixedMeasure θ U hu =
      (mixedTropicalPotentialPatch e hD hρ F heq).pushMeasure
        (tropicalCanonicalMixedBTMeasure F) := by
  have hnull : GlobalNonPluripolar.globalMixedMeasure θ U hu
      ((mixedTropicalPotentialPatch e hD hρ F heq).source : Set M)ᶜ = 0 :=
    le_antisymm ((measure_mono hpole).trans_eq
      (GlobalDiagonalScaling.globalMixedMeasure_pole_null_of_quasiPsh hu hψ)) bot_le
  have hself := Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr hnull)
  exact hself.symm.trans
    (globalMixedMeasure_restrict_mixedTropical_chart hu e hD hρ F heq)

section Endpoints

open FirstPass.PositiveClasses RelativeEnergy RelativeDarvasDistance RelativePreceqClasses
open SingularModelFiniteEnergyMixedCocycle SingularModelEnergyChartIntegrals

variable [ConnectedSpace M] {θ₀ : ClosedRealOneOneForm n M}
  {φ u v : M → EReal} {hφ : IsModelPotential θ₀ φ}
  {r : ComplexModel n → ℝ}

private def mixedTropicalEndpointPatch
    (e : ComplexChart n M) (hD : (D : Set (ComplexModel n)) ⊆ e.val.target)
    (hr : IsSmoothLocalPotential θ₀.val e D r)
    (f g : RealConvexFunction E)
    (hf : EqOn (fun z => chartFunction u e z + (r z : EReal))
      (fun z => (f.val (tropicalization z) : EReal)) D)
    (hg : EqOn (fun z => chartFunction v e z + (r z : EReal))
      (fun z => (g.val (tropicalization z) : EReal)) D)
    (k : Fin (n + 1)) :
    Patch (fun _ : Fin n => θ₀) (endpointMixedPotential k u v) :=
  mixedTropicalPotentialPatch e hD (fun _ => hr)
    (fun i => if i.val < k.val then f else g) (by
      intro i z hz
      by_cases hi : i.val < k.val
      · simpa only [endpointMixedPotential, hi, ↓reduceIte] using hf hz
      · simpa only [endpointMixedPotential, hi, ↓reduceIte] using hg hz)

omit [ConnectedSpace M] in
private theorem mixedTropicalEndpoint_measure
    (hu : IsThetaPshPotential θ₀.val u) (hv : IsThetaPshPotential θ₀.val v)
    (e : ComplexChart n M) (hD : (D : Set (ComplexModel n)) ⊆ e.val.target)
    (hr : IsSmoothLocalPotential θ₀.val e D r)
    (f g : RealConvexFunction E)
    (hf : EqOn (fun z => chartFunction u e z + (r z : EReal))
      (fun z => (f.val (tropicalization z) : EReal)) D)
    (hg : EqOn (fun z => chartFunction v e z + (r z : EReal))
      (fun z => (g.val (tropicalization z) : EReal)) D)
    {ψ : M → EReal} (hψ : IsGlobalQuasiPshPotential (n := n) ψ)
    (hpole : (e.val.source ∩ e.val ⁻¹' (D : Set (ComplexModel n)))ᶜ ⊆ {x | ψ x = ⊥})
    (k : Fin (n + 1)) :
    endpointMixedMeasure θ₀ v u hv hu k =
      (mixedTropicalEndpointPatch e hD hr f g hf hg k).pushMeasure
        (tropicalCanonicalMixedBTMeasure (fun i => if i.val < k.val then f else g)) := by
  apply globalMixedMeasure_eq_mixedTropical_chart_pushMeasure
    (endpointMixedPotential_thetaPlurisubharmonic θ₀ k u v hu hv)
  · exact hψ
  · exact hpole

private theorem mixedTropicalEndpoint_signed_readback
    (omega : KahlerBackground n M)
    (hu : RelativeFiniteEnergyPreceq θ₀ φ u hφ)
    (hv : RelativeFiniteEnergyPreceq θ₀ φ v hφ)
    (e : ComplexChart n M) (hD : (D : Set (ComplexModel n)) ⊆ e.val.target)
    (hr : IsSmoothLocalPotential θ₀.val e D r)
    (f g : RealConvexFunction E)
    (hf : EqOn (fun z => chartFunction u e z + (r z : EReal))
      (fun z => (f.val (tropicalization z) : EReal)) D)
    (hg : EqOn (fun z => chartFunction v e z + (r z : EReal))
      (fun z => (g.val (tropicalization z) : EReal)) D)
    {ψ : M → EReal} (hψ : IsGlobalQuasiPshPotential (n := n) ψ)
    (hpole : (e.val.source ∩ e.val ⁻¹' (D : Set (ComplexModel n)))ᶜ ⊆ {x | ψ x = ⊥})
    (k : Fin (n + 1)) :
    Integrable (fun a => f.val a - g.val a)
      (mixedAlexandrovMeasure volume (EuclideanSpace.basisFun (Fin n) ℝ)
        (fun i => if i.val < k.val then f else g)) ∧
    (∫ x, canonicalERealDiffToReal (u x) (v x)
      ∂endpointMixedMeasure θ₀ v u hv.1.plurisubharmonic hu.1.plurisubharmonic k) =
      ∫ a, (f.val a - g.val a)
        ∂mixedAlexandrovMeasure volume (EuclideanSpace.basisFun (Fin n) ℝ)
          (fun i => if i.val < k.val then f else g) := by
  let F : Fin n → RealConvexFunction E := fun i => if i.val < k.val then f else g
  let P := mixedTropicalEndpointPatch e hD hr f g hf hg k
  let μ := tropicalCanonicalMixedBTMeasure F
  have hm : μ (P.domain : Set (ComplexModel n))ᶜ = 0 :=
    tropicalCanonicalMixedBTMeasure_compl F
  have hp : endpointMixedMeasure θ₀ v u hv.1.plurisubharmonic hu.1.plurisubharmonic k =
      P.pushMeasure μ := mixedTropicalEndpoint_measure
        hu.1.plurisubharmonic hv.1.plurisubharmonic e hD hr f g hf hg hψ hpole k
  have hi := integrable_endpoint_canonicalDiff_of_preceq omega hu hv k
  rw [hp] at hi
  have hic := (P.integrable_pushMeasure_iff hm
    (fun x => canonicalERealDiffToReal (u x) (v x))).mp hi
  have heq : (fun z => canonicalERealDiffToReal (u (e.val.symm z)) (v (e.val.symm z)))
      =ᵐ[μ] (fun z => f.val (tropicalization z) - g.val (tropicalization z)) := by
    have hmem : ∀ᵐ z ∂μ, z ∈ D := ae_iff.mpr (tropicalCanonicalMixedBTMeasure_compl F)
    filter_upwards [hmem] with z hz
    calc
      _ = canonicalERealDiffToReal
          (chartFunction u e z + (r z : EReal))
          (chartFunction v e z + (r z : EReal)) :=
        (canonicalDiff_add_common _ _ (r z)).symm
      _ = _ := by
        have hfz : chartFunction u e z + (r z : EReal) =
            ((f.val (tropicalization z)) : EReal) := hf hz
        have hgz : chartFunction v e z + (r z : EReal) =
            ((g.val (tropicalization z)) : EReal) := hg hz
        rw [hfz, hgz, canonicalERealDiffToReal_coe_coe]
  have hic' : Integrable (fun z => f.val (tropicalization z) - g.val (tropicalization z)) μ :=
    hic.congr heq
  have hgap : Continuous (fun a => f.val a - g.val a) :=
    (continuousOn_univ.mp (f.property.continuousOn isOpen_univ)).sub
      (continuousOn_univ.mp (g.property.continuousOn isOpen_univ))
  obtain ⟨hT, _⟩ := exists_compact_tropical_torus_lift (n := n) isCompact_empty
  have hmap := tropicalization_canonicalMixedBTMeasure_eq_mixedAlexandrov F
  have hir : Integrable (fun a => f.val a - g.val a) (Measure.map tropicalization μ) :=
    (integrable_map_measure hgap.aestronglyMeasurable hT.aemeasurable).mpr hic'
  refine ⟨?_, ?_⟩
  · rwa [hmap] at hir
  · rw [hp, P.integral_pushMeasure hm]
    exact (integral_congr_ae heq).trans
      ((integral_map hT.aemeasurable hgap.aestronglyMeasurable).symm.trans
        (congrArg (fun ν : Measure E => ∫ a, (f.val a - g.val a) ∂ν) hmap))

/-- Native E1 supplies signed L1; actual whole NP/chart/map readbacks transport it
to the ORIGINAL mixed Alexandrov measure without an integrability certificate. -/
theorem integrable_tropical_endpoint_gap_mixedAlexandrov
    (omega : KahlerBackground n M)
    (hu : RelativeFiniteEnergyPreceq θ₀ φ u hφ)
    (hv : RelativeFiniteEnergyPreceq θ₀ φ v hφ)
    (e : ComplexChart n M) (hD : (D : Set (ComplexModel n)) ⊆ e.val.target)
    (hr : IsSmoothLocalPotential θ₀.val e D r)
    (f g : RealConvexFunction E)
    (hf : EqOn (fun z => chartFunction u e z + (r z : EReal))
      (fun z => (f.val (tropicalization z) : EReal)) D)
    (hg : EqOn (fun z => chartFunction v e z + (r z : EReal))
      (fun z => (g.val (tropicalization z) : EReal)) D)
    {ψ : M → EReal} (hψ : IsGlobalQuasiPshPotential (n := n) ψ)
    (hpole : (e.val.source ∩ e.val ⁻¹' (D : Set (ComplexModel n)))ᶜ ⊆ {x | ψ x = ⊥})
    (k : Fin (n + 1)) :
    Integrable (fun a => f.val a - g.val a)
      (mixedAlexandrovMeasure volume (EuclideanSpace.basisFun (Fin n) ℝ)
        (fun i => if i.val < k.val then f else g)) :=
  (mixedTropicalEndpoint_signed_readback omega hu hv e hD hr f g hf hg hψ hpole k).1

/-- Genuine canonical finite-value gap cancellation and actual subtype chart
transport give the SAME native endpoint signed integral on the real side. -/
theorem integral_endpoint_canonicalDiff_eq_tropicalMixedAlexandrov
    (omega : KahlerBackground n M)
    (hu : RelativeFiniteEnergyPreceq θ₀ φ u hφ)
    (hv : RelativeFiniteEnergyPreceq θ₀ φ v hφ)
    (e : ComplexChart n M) (hD : (D : Set (ComplexModel n)) ⊆ e.val.target)
    (hr : IsSmoothLocalPotential θ₀.val e D r)
    (f g : RealConvexFunction E)
    (hf : EqOn (fun z => chartFunction u e z + (r z : EReal))
      (fun z => (f.val (tropicalization z) : EReal)) D)
    (hg : EqOn (fun z => chartFunction v e z + (r z : EReal))
      (fun z => (g.val (tropicalization z) : EReal)) D)
    {ψ : M → EReal} (hψ : IsGlobalQuasiPshPotential (n := n) ψ)
    (hpole : (e.val.source ∩ e.val ⁻¹' (D : Set (ComplexModel n)))ᶜ ⊆ {x | ψ x = ⊥})
    (k : Fin (n + 1)) :
    (∫ x, canonicalERealDiffToReal (u x) (v x)
      ∂endpointMixedMeasure θ₀ v u hv.1.plurisubharmonic hu.1.plurisubharmonic k) =
      ∫ a, (f.val a - g.val a)
        ∂mixedAlexandrovMeasure volume (EuclideanSpace.basisFun (Fin n) ℝ)
          (fun i => if i.val < k.val then f else g) :=
  (mixedTropicalEndpoint_signed_readback omega hu hv e hD hr f g hf hg hψ hpole k).2

/-- The accepted all-model unnormalized native E1 cocycle reads back the sum of
the ORIGINAL real mixed endpoint integrals, with no extra factorial or Legendre claim. -/
theorem energy_sub_eq_tropicalMixedAlexandrov_integrals
    (omega : KahlerBackground n M)
    (hu : RelativeFiniteEnergyPreceq θ₀ φ u hφ)
    (hv : RelativeFiniteEnergyPreceq θ₀ φ v hφ)
    (e : ComplexChart n M) (hD : (D : Set (ComplexModel n)) ⊆ e.val.target)
    (hr : IsSmoothLocalPotential θ₀.val e D r)
    (f g : RealConvexFunction E)
    (hf : EqOn (fun z => chartFunction u e z + (r z : EReal))
      (fun z => (f.val (tropicalization z) : EReal)) D)
    (hg : EqOn (fun z => chartFunction v e z + (r z : EReal))
      (fun z => (g.val (tropicalization z) : EReal)) D)
    {ψ : M → EReal} (hψ : IsGlobalQuasiPshPotential (n := n) ψ)
    (hpole : (e.val.source ∩ e.val ⁻¹' (D : Set (ComplexModel n)))ᶜ ⊆ {x | ψ x = ⊥}) :
    ((n : ℝ) + 1) * ((energy θ₀ φ hφ u).toReal - (energy θ₀ φ hφ v).toReal) =
      ∑ k : Fin (n + 1), ∫ a, (f.val a - g.val a)
        ∂mixedAlexandrovMeasure volume (EuclideanSpace.basisFun (Fin n) ℝ)
          (fun i => if i.val < k.val then f else g) := by
  rw [mul_toReal_energy_sub_eq_sum_endpoint_integrals omega hu hv]
  exact Finset.sum_congr rfl (fun k _ =>
    integral_endpoint_canonicalDiff_eq_tropicalMixedAlexandrov
      omega hu hv e hD hr f g hf hg hψ hpole k)

end Endpoints

end SGPT.Toric
