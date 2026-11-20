import SGPT.Trace.BertiniNativeQuotientInfiniteLocus
import SGPT.Trace.BertiniNativeFiniteFrameFibre
import SGPT.Trace.BertiniNativeSingularNormFamily
import SGPT.Trace.BertiniLocalCircleMEP

/-! Explicit original local-MEP/AE consumer and genuine source projective chart transport. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.Bertini
open Bundle Set Filter TensorProduct MeasureTheory Metric
open scoped Manifold ContDiff Topology TensorProduct ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.PSH.VariableComplexAtlas SGPT.PSH.DirImg2
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.TensorDictionaryDraft
open SGPT.Bergman.CompactHolomorphicSectionsDraft SGPT.Bergman.MultiplierSectionsDraft
open SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle

theorem sourceLocallyPluripolar_affine_image_of_local {N : ℕ} (i : Fin (N + 1))
    (U : TopologicalSpace.Opens (ComplexModel N)) (s : Set (ComplexModel N))
    (hs : LocallyPluripolarOn s U) :
    (ofFixedModel N (HyperplaneSpace N)).LocallyPluripolar
      (affinePoint i '' (s ∩ U)) := by
  classical
  let : LocallyCompactSpace U := U.isOpen.locallyCompactSpace
  let K : ℕ → Set (ComplexModel N) := fun j => Subtype.val '' compactCovering U j
  have hK (j : ℕ) : IsCompact (K j) :=
    (isCompact_compactCovering U j).image continuous_subtype_val
  have hKU (j : ℕ) : K j ⊆ U := by
    rintro _ ⟨z,_,rfl⟩
    exact z.property
  have hpart (j : ℕ) : (ofFixedModel N (HyperplaneSpace N)).LocallyPluripolar
      (affinePoint i '' (s ∩ K j)) := by
    have hman := SGPT.PSH.manifoldLocallyPluripolar_chartImage (affineComplexChart i)
      (hK j) (by simp [affineComplexChart]) (fun z hz => hs z (hKU j hz))
    apply locallyPluripolar_of_in_chart
    intro e
    exact hman e
  have hUnion := SGPT.PSH.VariableComplexAtlas.LocallyPluripolar.iUnion hpart
  have heq : (⋃ j, affinePoint i '' (s ∩ K j)) = affinePoint i '' (s ∩ U) := by
    ext ℓ
    constructor
    · intro hℓ
      obtain ⟨j,ζ,hζ,rfl⟩ := mem_iUnion.mp hℓ
      exact ⟨ζ,⟨hζ.1,hKU j hζ.2⟩,rfl⟩
    · rintro ⟨ζ,hζ,rfl⟩
      obtain ⟨j,hj⟩ := exists_mem_compactCovering (⟨ζ,hζ.2⟩ : U)
      exact mem_iUnion.mpr ⟨j,ζ,⟨hζ.1,⟨⟨ζ,hζ.2⟩,hj,rfl⟩⟩,rfl⟩
  rwa [heq] at hUnion

variable {d N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (d + 1)) X] [IsComplexManifold (d + 1) X] [CompactSpace X]
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞)
  (L : HermitianHolomorphicLineBundle.{0,0} (d + 1) X)
  {φ : X → EReal} (hφ : IsGlobalQuasiPshPotential (n := d + 1) φ)

private theorem actualNativeInfinityPluripolar (i : Fin (N + 1))
    (V : TopologicalSpace.Opens (ComplexModel N))
    (hsV : ∀ ζ : V, IsSmoothHypersurfaceMember (d + 1) p (affinePoint i ζ.val))
    (U : TopologicalSpace.Opens (ComplexModel N)) (hUV : U ≤ V) {r : ℕ}
    (S : Fin r → nativeMultiplierSections
      (tensor (tensor (nativeCanonicalBundle (n := d + 1) (X := X)) L) (nativeBertiniHyperplaneBundle p)) φ)
    (hBasis : ∀ ζ : V, ∃ b : Module.Basis (Fin r) ℂ (NativeBertiniMultiplierQuotient p i ζ.val L hφ),
      ∀ j, b j = (nativeMultiplierSectionMap (tensor (nativeCanonicalBundle (n := d + 1) (X := X)) L)
        (nativeBertiniHyperplaneBundle p) hφ (nativeBertiniAffineSection p i ζ.val)).range.mkQ (S j))
    (hq : IsSingularNormFamily (nativeBertiniQuotientFrameEnergy p i V hsV L hφ S) U)
    (hlocal : HasLocalCircleMEP (nativeBertiniQuotientFrameEnergy p i V hsV L hφ S) U)
    (hAE : ∀ j : Fin r, ∀ᵐ ζ ∂volume.restrict (V : Set (ComplexModel N)),
      nativeBertiniQuotientFrameEnergy p i V hsV L hφ S ζ (Pi.single j (1 : ℂ)) ≠ ⊤) :
    LocallyPluripolarOn (nativeBertiniQuotientInfiniteLocus p i L hφ) U := by
  classical
  let q := nativeBertiniQuotientFrameEnergy p i V hsV L hφ S
  have hpsh := (hq.discPshOn_logDetDual_of_local_mep U.isOpen hlocal).plurisubharmonicOn U.isOpen
  intro x hx
  obtain ⟨a,ha,hball⟩ := Metric.isOpen_iff.mp U.isOpen x hx
  let B : TopologicalSpace.Opens (ComplexModel N) := ⟨ball x a,isOpen_ball⟩
  have hBV : B ≤ V := hball.trans hUV
  obtain ⟨ζ,hζ,hfinite⟩ := exists_native_quotient_finite_fibre_in_open_of_ae_frame
    p i V hsV L hφ S hBasis hAE B hBV (nonempty_ball.mpr ha)
  have hqfinite : ∀ v, q ζ.val v ≠ ⊤ := by
    intro v
    rw [show q ζ.val v = nativeBertiniQuotientFrameEnergy p i V hsV L hφ S ζ.val v by rfl,
      nativeBertiniQuotientFrameEnergy_apply p i V hsV L hφ S ζ]
    exact hfinite _
  refine ⟨ball x a,logDetDual q,isOpen_ball,mem_ball_self ha,isPreconnected_ball,
    hpsh.mono hball,⟨ζ.val,hζ,hq.logDetDual_ne_bot ζ.val hqfinite⟩,?_⟩
  intro y hy hybad
  have hyV : y ∈ V := hUV (hball hy)
  have hinf := (nativeBertiniQuotientInfiniteLocus_iff_frame p i L hφ V hsV S hBasis ⟨y,hyV⟩).mp hybad
  exact hq.logDetDual_eq_bot_of_exists_eq_top (hball hy) hinf

theorem exists_nativeBertini_infinite_locus_pluripolar_of_actual_local_mep_ae [ConnectedSpace X] :
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
          IsSingularNormFamily (nativeBertiniQuotientFrameEnergy p (chartIndex ℓ₀) V hsV L hφ S) U ∧
          (HasLocalCircleMEP (nativeBertiniQuotientFrameEnergy p (chartIndex ℓ₀) V hsV L hφ S) U →
            (∀ j : Fin r, ∀ᵐ ζ ∂volume.restrict (V : Set (ComplexModel N)),
              nativeBertiniQuotientFrameEnergy p (chartIndex ℓ₀) V hsV L hφ S ζ (Pi.single j (1 : ℂ)) ≠ ⊤) →
            LocallyPluripolarOn (nativeBertiniQuotientInfiniteLocus p (chartIndex ℓ₀) L hφ) U ∧
            (ofFixedModel N (HyperplaneSpace N)).LocallyPluripolar
              (affinePoint (chartIndex ℓ₀) '' (nativeBertiniQuotientInfiniteLocus p (chartIndex ℓ₀) L hφ ∩ U))) := by
  classical
  obtain ⟨F,hFn,hFa,hFproper,hFp,hfactory⟩ := exists_nativeBertini_generic_singularNormFamily p L hφ
  refine ⟨F,hFn,hFa,hFproper,hFp,?_⟩
  intro ℓ₀ hsm₀ hgood
  obtain ⟨r,S,V,hsV,U,hUV,hcentre,hBasis,havoid,hq⟩ := hfactory ℓ₀ hsm₀ hgood
  refine ⟨r,S,V,hsV,U,hUV,hcentre,hBasis,havoid,hq,?_⟩
  intro hlocal hAE
  have hp := actualNativeInfinityPluripolar p L hφ (chartIndex ℓ₀) V hsV U hUV S hBasis hq hlocal hAE
  exact ⟨hp,sourceLocallyPluripolar_affine_image_of_local (chartIndex ℓ₀) U _ hp⟩

end SGPT.Trace.Bertini
