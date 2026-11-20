import SGPT.Trace.BertiniExactNormalCoordinates
import SGPT.Trace.NativeTensorPullbackSectionRestriction

/-! Actual native local sections of the original pencil projection, and
holomorphic actual native coefficients at genuine moving points. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.BertiniFamilyCanonical
open Bundle Set Filter TensorProduct
open scoped Manifold ContDiff Topology TensorProduct
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.TensorDictionaryDraft
open SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle
open SGPT.Trace.Bertini SGPT.Trace.BertiniPencilFamily SGPT.Trace.BertiniPencilNormal
open SGPT.Trace.BertiniExactNormalCoordinates SGPT.Trace.OTMargin

section Scalar
variable {m : ℕ} {Y : Type} [TopologicalSpace Y]
  [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y]

theorem exists_native_scalar_localSection {f : Y → ℂ}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ℂ) ∞ f)
    (x₀ : Y)
    (hsub : Function.Surjective (mfderiv 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ℂ) f x₀))
    (z₀ : ComplexModel 1) (h₀ : z₀ 0 = f x₀) :
    ∃ (V : TopologicalSpace.Opens (ComplexModel 1)) (hz₀ : z₀ ∈ V),
      ∃ g : ContMDiffMap 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ComplexModel (m + 1)) V Y ∞,
        g ⟨z₀,hz₀⟩ = x₀ ∧ ∀ z : V, f (g z) = z.val 0 := by
  let f₀ := fun x => f x - f x₀
  have hf₀ : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ℂ) ∞ f₀ := hf.sub contMDiff_const
  have hder : mfderiv 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ℂ) f₀ x₀ =
      mfderiv 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ℂ) f x₀ := by
    change mfderiv 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ℂ) (f - fun _ => f x₀) x₀ = _
    rw [mfderiv_sub (hf.contMDiffAt.mdifferentiableAt (by simp)) mdifferentiableAt_const,
      mfderiv_const,sub_zero]
  have hsub₀ : Function.Surjective (mfderiv 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ℂ) f₀ x₀) := by
    rwa [hder]
  obtain ⟨hn,F,hxF,hF0,hread⟩ := exists_exact_normal_flatData hf₀ hsub₀ (sub_self (f x₀))
  let j : Fin (m + 1) := ⟨m + 1 - 1,Nat.sub_lt hn one_pos⟩
  have h0target : (0 : ComplexModel (m + 1)) ∈ F.flat.target := by
    rw [← hF0]
    exact fcoord_mem F hxF
  let axis : ComplexModel 1 → ComplexModel (m + 1) :=
    fun z => (z 0 - z₀ 0) • EuclideanSpace.single j 1
  have hc : ContDiff ℂ ∞ axis :=
    ((EuclideanSpace.proj (0 : Fin 1) : ComplexModel 1 →L[ℂ] ℂ).contDiff.sub contDiff_const).smul contDiff_const
  let V : TopologicalSpace.Opens (ComplexModel 1) :=
    ⟨axis ⁻¹' F.flat.target,F.flat.open_target.preimage hc.continuous⟩
  have hz₀ : z₀ ∈ V := by
    change axis z₀ ∈ F.flat.target
    simpa only [axis,sub_self,zero_smul] using h0target
  let g : ContMDiffMap 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ComplexModel (m + 1)) V Y ∞ :=
    ⟨fun z => finv F (axis z.val), by
      intro z
      have hz : axis z.val ∈ F.flat.target := z.property
      have hflat : ContDiffAt ℂ ∞ F.flat.symm (axis z.val) :=
        contDiffAt_of_differentiableOn_complex F.differentiableOn_flat_symm F.flat.open_target hz
      have hamb : ContMDiffAt 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1)) ∞
          F.amb.val.symm (F.flat.symm (axis z.val)) :=
        contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas F.amb.property)
          (F.flat_source_subset (F.flat.map_target hz))
      exact hamb.comp z (hflat.contMDiffAt.comp z (hc.contMDiff.comp contMDiff_subtype_val).contMDiffAt)⟩
  refine ⟨V,hz₀,g,?_,?_⟩
  · change finv F (axis z₀) = x₀
    have ha : axis z₀ = 0 := by simp only [axis,sub_self,zero_smul]
    rw [ha,← hF0,finv_fcoord F hxF]
  · intro z
    have h := exact_normal_inverse hread (show axis z.val ∈ F.flat.target from z.property)
    have ha : axis z.val j = z.val 0 - z₀ 0 := by simp [axis]
    rw [ha] at h
    change f (g z) - f x₀ = z.val 0 - z₀ 0 at h
    rw [h₀] at h
    exact sub_left_inj.mp h
end Scalar

variable {d N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (d + 1)) X] [IsComplexManifold (d + 1) X]
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞)
  (i : Fin (N + 1)) (a v : ComplexModel N) (U : TopologicalSpace.Opens (ComplexModel 1))
  (hsm : ∀ t : U, IsSmoothHypersurfaceMember (d + 1) p (pencilParameter i a v t.val))

theorem exists_familyProjection_localSection (q₀ : familyIncidence p i a v U) :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∃ (V : TopologicalSpace.Opens (ComplexModel 1)), V ≤ U ∧
      ∃ (ht₀ : q₀.val.1.val ∈ V),
      ∃ g : ContMDiffMap 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ComplexModel (d + 1))
        V (familyIncidence p i a v U) ∞,
        g ⟨q₀.val.1.val,ht₀⟩ = q₀ ∧ ∀ t : V, (g t).val.1.val = t.val := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  obtain ⟨V,ht₀,g,hg₀,hg⟩ := exists_native_scalar_localSection
    (contMDiff_scalarParameter p i a v U p.contMDiff hsm) q₀
    (surjective_mfderiv_scalarParameter p i a v U p.contMDiff hsm q₀) q₀.val.1.val rfl
  have hproj (t : V) : (g t).val.1.val = t.val := by
    ext k
    fin_cases k
    exact hg t
  have hVU : V ≤ U := by
    intro t ht
    have h := (g ⟨t,ht⟩).val.1.property
    rwa [hproj ⟨t,ht⟩] at h
  exact ⟨V,hVU,ht₀,g,hg₀,hproj⟩

omit p i a v U hsm in
theorem contMDiffAt_nativeSection_movingPointCoefficient
    {n : ℕ} {Y : Type} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
    (B : HermitianHolomorphicLineBundle n Y) (e : AtlasFrame B)
    (S : HolomorphicSections (n := n) B.Fiber) (V : TopologicalSpace.Opens (ComplexModel 1))
    (g : ContMDiffMap 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ComplexModel n) V Y ∞)
    (t : V) (ht : g t ∈ e.val.baseSet) :
    ContMDiffAt 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ℂ) ∞
      (fun z => (e.val ⟨g z,S (g z)⟩).2) t := by
  let := e.property
  have hs := (e.val.contMDiffAt_section_iff ht).mp (S.contMDiff (g t))
  exact hs.comp t g.contMDiff.contMDiffAt

end SGPT.Trace.BertiniFamilyCanonical
