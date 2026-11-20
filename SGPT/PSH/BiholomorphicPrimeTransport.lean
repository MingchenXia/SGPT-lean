import SGPT.PSH.HolomorphicImageIrreducibility
import SGPT.PSH.GeometricQDivisor
import SGPT.Foundations.Analysis.Pending.RegularAtDimChart

set_option autoImplicit false
noncomputable section
namespace SGPT.PSH
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open scoped Topology Manifold ContDiff

universe u
variable {n : ℕ} {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [ChartedSpace (ComplexModel n) N] [IsComplexManifold n N]

private theorem native_coordinate_differentiableOn {f : M → N}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f)
    (x : M) (y : N) :
    DifferentiableOn ℂ
      ((complexChartAt (n := n) y).val ∘ f ∘ (complexChartAt (n := n) x).val.symm)
      ((complexChartAt (n := n) x).val.target ∩
        (complexChartAt (n := n) x).val.symm ⁻¹'
          (f ⁻¹' (complexChartAt (n := n) y).val.source)) := by
  have h := (contMDiff_iff.mp hf).2 x y
  simp only [extChartAt_coe, extChartAt_coe_symm, extChartAt_source, extChartAt_target,
    modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, range_id, preimage_id,
    inter_univ, Function.comp_id, Function.id_comp] at h
  exact h.differentiableOn (by simp)

/-- Genuine native biholomorphic regularity transport, using the existing
actual local holomorphic-equivalence composition producer. No local flattening
or regular-output witness is supplied beyond the ORIGINAL target regularity. -/
theorem regularAtDim_preimage_biholomorphic (e : M ≃ₜ N)
    (he : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ e)
    (hei : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ e.symm)
    {B : Set N} {y : M} {k : ℕ}
    (hB : RegularAtDim (n := n) B (e y) k) :
    RegularAtDim (n := n) (e ⁻¹' B) y k := by
  let s := (complexChartAt (n := n) y).val
  let t := (complexChartAt (n := n) (e y)).val
  let T := (s.symm.trans e.toOpenPartialHomeomorph).trans t
  have hsource : T.source = s.target ∩ s.symm ⁻¹' (e ⁻¹' t.source) := by
    change (s.target ∩ s.symm ⁻¹' (univ : Set M)) ∩
      (fun z => e (s.symm z)) ⁻¹' t.source = _
    simp only [preimage_univ, inter_univ]
    rfl
  have htarget : T.target = t.target ∩ t.symm ⁻¹' (e.symm ⁻¹' s.source) := by
    change t.target ∩ t.symm ⁻¹' ((univ : Set N) ∩ e.symm ⁻¹' s.source) = _
    simp only [univ_inter]
  have hT : DifferentiableOn ℂ T T.source := by
    change DifferentiableOn ℂ (t ∘ e ∘ s.symm) T.source
    rw [hsource]
    exact native_coordinate_differentiableOn he y (e y)
  have hTi : DifferentiableOn ℂ T.symm T.target := by
    change DifferentiableOn ℂ (s ∘ e.symm ∘ t.symm) T.target
    rw [htarget]
    exact native_coordinate_differentiableOn hei (e y) y
  have hy : y ∈ s.source := mem_complexChartAt_source y
  have hey : e y ∈ t.source := mem_complexChartAt_source (e y)
  have hc : s y ∈ T.source := by
    rw [hsource]
    refine ⟨s.map_source hy, ?_⟩
    change e (s.symm (s y)) ∈ t.source
    rwa [s.left_inv hy]
  have hcenter : T (s y) = t (e y) := by
    change t (e (s.symm (s y))) = t (e y)
    rw [s.left_inv hy]
  obtain ⟨hk, hyB, Φ, _hΦt, hΦ0, hflat⟩ := hB
  let Ψ := RegularAtDimChart.precomp T hT hTi hc hcenter Φ
  refine ⟨hk, hyB, Ψ, ?_, ?_, ?_⟩
  · intro z hz
    have hzT : z ∈ T.source := hz.1
    rw [hsource] at hzT
    exact hzT.1
  · change Φ.toFun (T (s y)) = 0
    rw [hcenter]
    exact hΦ0
  · intro z hz hzΦ
    change s z ∈ T.source ∩ T ⁻¹' Φ.source at hzΦ
    have hzT := hzΦ.1
    rw [hsource] at hzT
    have htz : e z ∈ t.source := by
      have h := hzT.2
      change e (s.symm (s z)) ∈ t.source at h
      rwa [s.left_inv hz] at h
    have happ : T (s z) = t (e z) := by
      change t (e (s.symm (s z))) = t (e z)
      rw [s.left_inv hz]
    have hΦz : t (e z) ∈ Φ.source := by
      rw [← happ]
      exact hzΦ.2
    change e z ∈ B ↔ Φ.toFun (T (s z)) ∈ complexCoordinatePlane n k
    rw [happ]
    exact hflat htz hΦz

/-- Actual biholomorphic preimage manufactures the complete irreducible
analytic subvariety and preserves its genuine original regular dimension.
The existing generic image-irreducibility mother supplies irreducibility. -/
theorem exists_biholomorphic_subvariety_preimage (e : M ≃ₜ N)
    (he : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ e)
    (hei : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ e.symm)
    (W : ClosedIrreducibleAnalyticSubvariety n N) :
    ∃ V : ClosedIrreducibleAnalyticSubvariety n M,
      V.carrier = e ⁻¹' W.carrier ∧ V.dim = W.dim := by
  have hA : IsComplexAnalyticSubset (n := n) (e ⁻¹' W.carrier) :=
    AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage he W.analytic
  have himage : e.symm '' W.carrier = e ⁻¹' W.carrier := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      simpa only [mem_preimage, e.apply_symm_apply] using hz
    · intro hx
      exact ⟨e x, hx, e.symm_apply_apply x⟩
  have hirr := holomorphic_analytic_image_irreducible hei W
    (by rwa [himage])
  rw [himage] at hirr
  obtain ⟨z, hz⟩ := W.regularLocus_nonempty
  change RegularAtDim (n := n) W.carrier z W.dim at hz
  have hreg : RegularAtDim (n := n) (e ⁻¹' W.carrier) (e.symm z) W.dim := by
    apply regularAtDim_preimage_biholomorphic e he hei
    simpa only [e.apply_symm_apply] using hz
  exact ⟨{
    carrier := e ⁻¹' W.carrier
    isClosed_carrier := W.isClosed_carrier.preimage e.continuous
    irreducible_carrier := hirr
    dim := W.dim
    dim_le := W.dim_le
    regularLocus_nonempty := ⟨e.symm z, hreg⟩ }, rfl, rfl⟩

/-- Literal canonical prime preimage; actual geometry is produced internally,
with no new witness or catalog input and no stored witness-choice data. -/
def biholomorphic_geometricPrimeCarrier_preimage (e : M ≃ₜ N)
    (he : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ e)
    (hei : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ e.symm)
    (P : GeometricPrimeCarrier n N) : GeometricPrimeCarrier n M :=
  ⟨e ⁻¹' P.val, by
    obtain ⟨V, hV, hdim⟩ := exists_biholomorphic_subvariety_preimage e he hei P.subvariety
    refine ⟨V, ?_, ?_⟩
    · rw [hV, P.subvariety_carrier]
    · rw [hdim]
      exact P.subvariety_codimension⟩

theorem biholomorphic_geometricPrimeCarrier_preimage_carrier (e : M ≃ₜ N)
    (he : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ e)
    (hei : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ e.symm)
    (P : GeometricPrimeCarrier n N) :
    (biholomorphic_geometricPrimeCarrier_preimage e he hei P).val = e ⁻¹' P.val := rfl

end SGPT.PSH
