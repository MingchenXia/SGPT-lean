import SGPT.Trace.BertiniNativeFiniteException
import SGPT.Trace.BertiniNativeQuotientEnergyField

/-! Produced ACTUAL native quotient positive singular norm family on the FULL original affine base. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.Bertini
open Bundle Set Filter TensorProduct
open scoped Manifold ContDiff Topology TensorProduct ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.PSH.VariableComplexAtlas SGPT.PSH.DirImg2
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.TensorDictionaryDraft
open SGPT.Bergman.CompactHolomorphicSectionsDraft SGPT.Bergman.MultiplierSectionsDraft
open SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle

variable {d N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (d + 1)) X] [IsComplexManifold (d + 1) X] [CompactSpace X] [ConnectedSpace X]
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞)
  (L : HermitianHolomorphicLineBundle.{0,0} (d + 1) X)
  {φ : X → EReal} (hφ : IsGlobalQuasiPshPotential (n := d + 1) φ)

theorem exists_nativeBertini_generic_singularNormFamily :
    ∃ F : Finset X, F.Nonempty ∧ IsComplexAnalyticSubset (n := N) (finitePointHyperplaneException p F) ∧
      finitePointHyperplaneException p F ≠ univ ∧
      (ofFixedModel N (HyperplaneSpace N)).LocallyPluripolar (finitePointHyperplaneException p F) ∧
      ∀ (ℓ₀ : HyperplaneSpace N) (_hsm₀ : IsSmoothHypersurfaceMember (d + 1) p ℓ₀),
        ℓ₀ ∉ finitePointHyperplaneException p F →
        ∃ (r : ℕ) (S : Fin r → nativeMultiplierSections
          (tensor (tensor (nativeCanonicalBundle (n := d + 1) (X := X)) L) (nativeBertiniHyperplaneBundle p)) φ)
          (V : TopologicalSpace.Opens (ComplexModel N))
          (hsV : ∀ ζ : V, IsSmoothHypersurfaceMember (d + 1) p (affinePoint (chartIndex ℓ₀) ζ.val))
          (U : TopologicalSpace.Opens (ComplexModel N)) (_hUV : U ≤ V),
          affineChart (chartIndex ℓ₀) ℓ₀ ∈ U ∧
          (∀ ζ : V, ∃ b : Module.Basis (Fin r) ℂ (NativeBertiniMultiplierQuotient p (chartIndex ℓ₀) ζ.val L hφ),
            ∀ j, b j = (nativeMultiplierSectionMap (tensor (nativeCanonicalBundle (n := d + 1) (X := X)) L)
              (nativeBertiniHyperplaneBundle p) hφ (nativeBertiniAffineSection p (chartIndex ℓ₀) ζ.val)).range.mkQ (S j)) ∧
          (∀ ζ ∈ U, affinePoint (chartIndex ℓ₀) ζ ∉ finitePointHyperplaneException p F) ∧
          IsSingularNormFamily (nativeBertiniQuotientFrameEnergy p (chartIndex ℓ₀) V hsV L hφ S) U := by
  classical
  obtain ⟨F,hFn,ha,hproper,ho,_hd,hpl,hInj⟩ := exists_nativeBertini_generic_quotient_injective p L hφ
  refine ⟨F,hFn,ha,hproper,hpl,?_⟩
  intro ℓ₀ hsm₀ hgood₀
  let i := chartIndex ℓ₀
  let a := affineChart i ℓ₀
  have hcentre : affinePoint i a = ℓ₀ := (affineChart i).left_inv (mem_affineChart_chartIndex ℓ₀)
  obtain ⟨x,hx⟩ := hFn
  have hp : ∃ x : X, x ∉ member p ℓ₀ := ⟨x,fun hxH => hgood₀ ⟨x,hx,hxH⟩⟩
  obtain ⟨r,S,V,hV,hsV,hb,hl⟩ := exists_native_fullBase_quotient_energy_field p L hφ ℓ₀ hsm₀ hp
  let U : TopologicalSpace.Opens (ComplexModel N) :=
    ⟨(V : Set _) ∩ (affinePoint i) ⁻¹' (finitePointHyperplaneException p F)ᶜ,
      V.isOpen.inter (ho.preimage (continuous_affinePoint i))⟩
  have hUV : U ≤ V := fun _ hz => hz.1
  have haU : a ∈ U := by
    refine ⟨hV,?_⟩
    change affinePoint i a ∉ finitePointHyperplaneException p F
    rw [hcentre]
    exact hgood₀
  refine ⟨r,S,V,hsV,U,hUV,haU,hb,(fun _ hz => hz.2),?_⟩
  refine {
    smul := nativeBertiniQuotientFrameEnergy_smul p i V hsV L hφ S
    add_le := nativeBertiniQuotientFrameEnergy_add_le p i V hsV L hφ S
    pos := ?_
    lsc := fun ζ _ v => hl (ζ,v) }
  intro ζ hζ v hv
  let zV : V := ⟨ζ,hζ.1⟩
  let hsm := hsV zV
  let := nativeBertiniMemberChartedSpace p i ζ hsm
  let := nativeBertiniMemberComplex p i ζ hsm
  let := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous (affinePoint i ζ)).isCompact
  obtain ⟨b,hbS⟩ := hb zV
  have hQ : (∑ j, v j • (nativeMultiplierSectionMap
      (tensor (nativeCanonicalBundle (n := d + 1) (X := X)) L) (nativeBertiniHyperplaneBundle p)
      hφ (nativeBertiniAffineSection p i ζ)).range.mkQ (S j)) = b.equivFun.symm v := by
    rw [b.equivFun_symm_apply]
    apply Finset.sum_congr rfl
    intro j _
    rw [hbS j]
  have hnonzero : b.equivFun.symm v ≠ 0 := by
    intro hz
    apply hv
    apply b.equivFun.symm.injective
    exact hz.trans (map_zero _).symm
  have hR := hInj i ζ hsm hζ.2
  have hpos : 0 < nativeBertiniPhysicalQuotientHodgeEnergy p i ζ hsm L hφ (b.equivFun.symm v) :=
    (nativeBertiniPhysicalQuotientHodgeEnergy_positive_iff_injective p i ζ hsm L hφ).mpr hR _ hnonzero
  have hread := nativeBertiniQuotientFrameEnergy_apply p i V hsV L hφ S zV v
  rw [hread,hQ]
  exact hpos.ne'

end SGPT.Trace.Bertini
