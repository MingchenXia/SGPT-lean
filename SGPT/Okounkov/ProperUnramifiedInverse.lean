import SGPT.Foundations.Analysis.Pending.HolomorphicLocalInverse
import SGPT.Foundations.Analysis.Pending.AnalyticModificationConnectedFibres
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Closure

set_option autoImplicit false

/-! # Whole inverse geometry for a proper unramified original map -/

noncomputable section
universe u

namespace SGPT.Okounkov

open Set Filter
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.Pending

/-- Genuine density and openness upgrade singleton fibres to whole injectivity. -/
theorem injective_of_openMap_dense_singleton_fibres
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    {f : Y → X} (hf : IsOpenMap f) {D : Set X} (hD : Dense D)
    (hone : ∀ x ∈ D, ∀ y z : Y, f y = x → f z = x → y = z) :
    Function.Injective f := by
  intro y z hyz
  by_contra hne
  obtain ⟨U, V, hU, hV, hyU, hzV, hUV⟩ := t2_separation hne
  obtain ⟨x, hxD, hx⟩ := hD.exists_mem_open ((hf U hU).inter (hf V hV))
    ⟨f y, ⟨mem_image_of_mem f hyU, hyz.symm ▸ mem_image_of_mem f hzV⟩⟩
  obtain ⟨a, haU, hax⟩ := hx.1
  obtain ⟨b, hbV, hbx⟩ := hx.2
  have hab := hone x hxD a b hax hbx
  exact Set.disjoint_left.mp hUV haU (hab.symm ▸ hbV)

/-- Actual bijectivity of the differential internally gives original open images. -/
theorem isOpenMap_of_everywhere_unramified
    {n : ℕ} {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    [ChartedSpace (ComplexModel n) X] [ChartedSpace (ComplexModel n) Y]
    [IsComplexManifold n X] [IsComplexManifold n Y]
    {f : Y → X}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hu : ∀ y, Function.Bijective
      (mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) f y)) :
    IsOpenMap f := by
  intro U hU
  rw [isOpen_iff_mem_nhds]
  rintro x ⟨y, hy, rfl⟩
  have hne : y ∉ exceptionalLocus n f := by
    simpa only [exceptionalLocus, mem_ofPred_eq, not_not] using hu y
  have hmap := StrictTransformComposition.map_nhds_eq_of_not_mem_exceptionalLocus hf hne
  rw [← hmap]
  change f ⁻¹' (f '' U) ∈ 𝓝 y
  exact Filter.mem_of_superset (hU.mem_nhds hy) (fun z hz => ⟨z, hz, rfl⟩)

/-- The original proper map produces one unique whole holomorphic inverse from a
dense geometric degree-one locus and actual unramified differentials. No global
inverse or sheaf-unit inverse is a premise. -/
theorem exists_unique_holomorphic_inverse_of_proper_unramified_dense_fibres
    {n : ℕ} {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    [ChartedSpace (ComplexModel n) X] [ChartedSpace (ComplexModel n) Y]
    [IsComplexManifold n X] [IsComplexManifold n Y]
    {f : Y → X}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hp : IsProperMap f)
    (hu : ∀ y, Function.Bijective
      (mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) f y))
    {D : Set X} (hD : Dense D) (himage : D ⊆ range f)
    (hone : ∀ x ∈ D, ∀ y z : Y, f y = x → f z = x → y = z) :
    ∃! s : X → Y,
      ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ s ∧
        f ∘ s = id ∧ s ∘ f = id := by
  classical
  have hinj := injective_of_openMap_dense_singleton_fibres
    (isOpenMap_of_everywhere_unramified hf hu) hD hone
  have hclosed : IsClosed (range f) := by
    simpa only [image_univ] using hp.isClosedMap univ isClosed_univ
  have hrange : range f = univ :=
    hclosed.closure_eq.symm.trans (hD.mono himage).closure_eq
  have hsurj : Function.Surjective f := by
    intro x
    have hx : x ∈ range f := hrange.symm ▸ mem_univ x
    exact hx
  let s : X → Y := fun x => Classical.choose (hsurj x)
  have hright (x : X) : f (s x) = x := Classical.choose_spec (hsurj x)
  have hleft (y : Y) : s (f y) = y := hinj (hright (f y))
  have hs : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ s := by
    intro x
    have hne : s x ∉ exceptionalLocus n f := by
      simpa only [exceptionalLocus, mem_ofPred_eq, not_not] using hu (s x)
    obtain ⟨V, a, hV, hxV, _ha, hfa, hahol, _halocal⟩ :=
      HolomorphicLocalInverse.exists_localInverse hf hne
    have hxV' : x ∈ V := by simpa only [hright] using hxV
    have heq : a =ᶠ[𝓝 x] s := by
      filter_upwards [hV.mem_nhds hxV'] with z hz
      exact hinj ((hfa z hz).trans (hright z).symm)
    exact (hahol x hxV').congr_of_eventuallyEq heq.symm
  refine ⟨s, ⟨hs, funext hright, funext hleft⟩, ?_⟩
  rintro t ⟨_ht, hft, _htf⟩
  funext x
  exact hinj ((congrFun hft x).trans (hright x).symm)

/-- The supported smooth case of the original Zariski-main theorem.  This
reuses the genuine connected-complement and compact-fibre separation producer;
the singular unibranch complex-space case is not asserted. -/
theorem zariski_main_smooth_analytic_modification
    {n : ℕ} {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    [ChartedSpace (ComplexModel n) X] [ChartedSpace (ComplexModel n) Y]
    [IsComplexManifold n X] [IsComplexManifold n Y]
    {f : Y → X}
    (hf : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := n) f)
    (x : X) : IsConnected (f ⁻¹' ({x} : Set X)) ∧
      IsCompact (f ⁻¹' ({x} : Set X)) :=
  AnalyticModificationConnectedFibres.isConnected_fibre hf x

end SGPT.Okounkov
