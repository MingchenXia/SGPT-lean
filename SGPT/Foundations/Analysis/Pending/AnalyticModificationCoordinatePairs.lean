import SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
import SGPT.Foundations.Analysis.Pending.BedfordTaylorHolomorphic
import SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps
import SGPT.Foundations.Analysis.FirstPass.GlobalCurrents

set_option autoImplicit false

/-! Genuine analytic-modification geometry internally produces actual
coordinate biholomorphic pairs off its analytic exceptional set.
Entire BP before Lean. All dimensions, no Compact/Connected/factorization
or supplied coordinate/current identity certificate. -/

noncomputable section
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace SGPT.Foundations.Analysis.Pending.AnalyticModificationCoordinatePairs
open FirstPass FirstPass.HolomorphicMaps AnalyticModificationLocalDiscrepancy BedfordTaylor

variable {n : ℕ} {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]

private theorem coordinateMap_contDiffAt_of_contMDiffAt {f : X → Y}
    (e : ComplexChart n X) (d : ComplexChart n Y) {z : ComplexModel n}
    (hz : z ∈ coordinateDomain f e d)
    (hf : ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f (e.val.symm z)) :
    ContDiffAt ℂ ∞ (coordinateMap f e d) z := by
  have h := (contMDiffAt_iff_of_mem_maximalAtlas
    (IsManifold.subset_maximalAtlas e.property)
    (IsManifold.subset_maximalAtlas d.property)
    (e.val.map_target hz.1) hz.2).mp hf
  simpa [coordinateMap, OpenPartialHomeomorph.extend_coe,
    OpenPartialHomeomorph.extend_coe_symm, e.val.right_inv hz.1,
    contDiffWithinAt_univ] using h.2

/-- Natural proper holomorphic modification data internally produce actual
coordinate biholomorphic pairs at EVERY point of an analytic complement,
for ANY valid original charts. All dimensions, no compactness or supplied pair. -/
theorem exists_coordinate_pairs_off_analytic_set
    {π : Y → X} (hπ : IsAnalyticModification (n := n) π) :
    ∃ (E : Set X) (s : X → Y), IsClosed E ∧ IsComplexAnalyticSubset (n := n) E ∧
      interior E = ∅ ∧ IsComplexAnalyticSubset (n := n) (π ⁻¹' E) ∧
      interior (π ⁻¹' E) = ∅ ∧
      ∀ (y : Y), π y ∉ E →
        ∀ (e : ComplexChart n Y) (d : ComplexChart n X),
          y ∈ e.val.source → π y ∈ d.val.source →
          ∃ (A B : Opens (ComplexModel n)), e.val y ∈ A ∧
            A ≤ chartTarget e ∧ B ≤ chartTarget d ∧
            ((A : Set (ComplexModel n)) ⊆ coordinateDomain π e d) ∧
            (∀ z ∈ B, d.val.symm z ∉ E) ∧
            IsBiholomorphicPair A B (coordinateMap π e d) (coordinateMap s d e) := by
  obtain ⟨D, E, s, _hDc, hDa, hDi, hEc, hEa, hEi, hpre, hs, hright, hleft⟩ := hπ.2.2
  have hne (y : Y) (hy : π y ∉ E) : y ∉ D := by
    intro hyD
    apply hy
    change y ∈ π ⁻¹' E
    rwa [hpre]
  refine ⟨E, s, hEc, hEa, hEi, ?_, ?_, ?_⟩
  · rwa [hpre]
  · rwa [hpre]
  intro y hy e d hye hyd
  let V : Set X := d.val.source ∩ (Eᶜ ∩ s ⁻¹' e.val.source)
  have hV : IsOpen V := d.val.open_source.inter
    (hs.continuousOn.isOpen_inter_preimage hEc.isOpen_compl e.val.open_source)
  have hys : s (π y) = y := hleft y (hne y hy)
  have hyV : π y ∈ V := by
    refine ⟨hyd, hy, ?_⟩
    change s (π y) ∈ e.val.source
    rwa [hys]
  let A : Opens (ComplexModel n) := ⟨e.val.target ∩ e.val.symm ⁻¹' (π ⁻¹' V),
    e.val.isOpen_inter_preimage_symm (hV.preimage hπ.1.continuous)⟩
  let B : Opens (ComplexModel n) := ⟨d.val.target ∩ d.val.symm ⁻¹' V,
    d.val.isOpen_inter_preimage_symm hV⟩
  have hyA : e.val y ∈ A := ⟨e.val.map_source hye, by
    change π (e.val.symm (e.val y)) ∈ V
    rwa [e.val.left_inv hye]⟩
  have hAt : A ≤ chartTarget e := fun _ hz => hz.1
  have hBt : B ≤ chartTarget d := fun _ hz => hz.1
  have hAdom : (A : Set (ComplexModel n)) ⊆ coordinateDomain π e d :=
    fun _ hz => ⟨hz.1, hz.2.1⟩
  have hBoff : ∀ z ∈ B, d.val.symm z ∉ E := fun _ hz => hz.2.2.1
  refine ⟨A, B, hyA, hAt, hBt, hAdom, hBoff, ?_⟩
  refine { holo := (coordinateMap_contDiffOn hπ.1 e d).mono hAdom
           holo_inv := ?_
           mapsTo := ?_
           mapsTo_inv := ?_
           left_inv := ?_
           right_inv := ?_ }
  · intro w hw
    have hdom : w ∈ coordinateDomain s d e := ⟨hw.1, hw.2.2.2⟩
    exact (coordinateMap_contDiffAt_of_contMDiffAt d e hdom
      (hs.contMDiffAt (hEc.isOpen_compl.mem_nhds (hBoff w hw)))).contDiffWithinAt
  · intro z hz
    have hzdom := hAdom hz
    refine ⟨coordinateMap_mem_target hzdom, ?_⟩
    change d.val.symm (d.val (π (e.val.symm z))) ∈ V
    rw [d.val.left_inv hzdom.2]
    exact hz.2
  · intro w hw
    have hswe : s (d.val.symm w) ∈ e.val.source := hw.2.2.2
    refine ⟨e.val.map_source hswe, ?_⟩
    change π (e.val.symm (e.val (s (d.val.symm w)))) ∈ V
    rw [e.val.left_inv hswe, hright _ (hBoff w hw)]
    exact hw.2
  · intro z hz
    have hzdom := hAdom hz
    change e.val (s (d.val.symm (d.val (π (e.val.symm z))))) = z
    rw [d.val.left_inv hzdom.2, hleft _ (hne _ hz.2.2.1), e.val.right_inv hz.1]
  · intro w hw
    have hswe : s (d.val.symm w) ∈ e.val.source := hw.2.2.2
    change d.val (π (e.val.symm (e.val (s (d.val.symm w))))) = w
    rw [e.val.left_inv hswe, hright _ (hBoff w hw), d.val.right_inv hw.1]

end SGPT.Foundations.Analysis.Pending.AnalyticModificationCoordinatePairs
