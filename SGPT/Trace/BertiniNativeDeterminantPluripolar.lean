import SGPT.Trace.BertiniNativeLocalMEP
import SGPT.Trace.BertiniNativeInfinitePluripolar
import SGPT.Trace.BertiniUniversalFiniteFibres
import SGPT.Foundations.Analysis.Pending.KahlerVolumeSmoothPositive

/-! Actual determinant PSH and local infinity pluripolarity of the original quotient field. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.Bertini
open Bundle Set Filter Metric TensorProduct MeasureTheory
open scoped Manifold ContDiff Topology TensorProduct ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.PSH.VariableComplexAtlas SGPT.PSH.DirImg2
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.NativeHermitianMetric
open SGPT.Bergman.CompactHolomorphicSectionsDraft SGPT.Bergman.MultiplierSectionsDraft
open SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle
open SGPT.Trace.BertiniFamilyCanonical

variable {d N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (d+1)) X] [IsComplexManifold (d+1) X] [CompactSpace X]
  (p : ContMDiffMap 𝓘(ℂ,ComplexModel (d+1)) 𝓘(ℂ,ComplexModel N) X (ComplexProjectiveSpace N) ∞)
  (L : HermitianHolomorphicLineBundle.{0,0} (d+1) X)
  {φ : X → EReal} (hφ : IsGlobalQuasiPshPotential (n := d+1) φ)

theorem nativeBertiniQuotientRestriction_injective_of_positive_field
    (i : Fin (N+1)) (B : TopologicalSpace.Opens (ComplexModel N))
    (hsB : ∀ zeta : B, IsSmoothHypersurfaceMember (d+1) p (affinePoint i zeta.val))
    (D : TopologicalSpace.Opens (ComplexModel N)) (hDB : D ≤ B) (r : ℕ)
    (S : Fin r → nativeMultiplierSections
      (tensor (tensor (nativeCanonicalBundle (n := d+1) (X := X)) L) (nativeBertiniHyperplaneBundle p)) φ)
    (hb : ∀ zeta : B, ∃ b : Module.Basis (Fin r) ℂ (NativeBertiniMultiplierQuotient p i zeta.val L hφ),
      ∀ j, b j = (nativeMultiplierSectionMap (tensor (nativeCanonicalBundle (n := d+1) (X := X)) L)
        (nativeBertiniHyperplaneBundle p) hφ (nativeBertiniAffineSection p i zeta.val)).range.mkQ (S j))
    (hq : IsSingularNormFamily (nativeBertiniQuotientFrameEnergy p i B hsB L hφ S) D)
    (zeta : D) :
    let hsm := hsB ⟨zeta.val,hDB zeta.property⟩
    letI := nativeBertiniMemberChartedSpace p i zeta.val hsm
    letI := nativeBertiniMemberComplex p i zeta.val hsm
    letI := isCompact_iff_compactSpace.mp
      (isClosed_member p p.contMDiff.continuous (affinePoint i zeta.val)).isCompact
    Function.Injective (nativeBertiniPhysicalQuotientRestriction p i zeta.val hsm L hφ) := by
  classical
  let hsm := hsB ⟨zeta.val,hDB zeta.property⟩
  let := nativeBertiniMemberChartedSpace p i zeta.val hsm
  let := nativeBertiniMemberComplex p i zeta.val hsm
  let := isCompact_iff_compactSpace.mp
    (isClosed_member p p.contMDiff.continuous (affinePoint i zeta.val)).isCompact
  apply (nativeBertiniPhysicalQuotientHodgeEnergy_positive_iff_injective p i zeta.val hsm L hφ).mp
  intro q hq0
  obtain ⟨b,hbS⟩ := hb ⟨zeta.val,hDB zeta.property⟩
  have hc : b.equivFun q ≠ 0 := by
    intro hc
    apply hq0
    exact b.equivFun.injective (hc.trans (map_zero _).symm)
  have hsum : (∑ j, (b.equivFun q) j • (nativeMultiplierSectionMap
      (tensor (nativeCanonicalBundle (n := d+1) (X := X)) L) (nativeBertiniHyperplaneBundle p)
      hφ (nativeBertiniAffineSection p i zeta.val)).range.mkQ (S j)) = q := by
    calc
      _ = ∑ j, (b.equivFun q) j • b j := by
        apply Finset.sum_congr rfl
        intro j _
        rw [hbS j]
      _ = b.equivFun.symm (b.equivFun q) := (b.equivFun_symm_apply _).symm
      _ = q := b.equivFun.symm_apply_apply q
  have hp := pos_iff_ne_zero.mpr (hq.pos zeta.val zeta.property (b.equivFun q) hc)
  rw [nativeBertiniQuotientFrameEnergy_apply p i B hsB L hφ S ⟨zeta.val,hDB zeta.property⟩,hsum] at hp
  exact hp


private theorem native_infinite_locus_pluripolar_of_produced_local_circle
    [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X] {k : ℕ}
    (p : ContMDiffMap 𝓘(ℂ,ComplexModel (d+1)) 𝓘(ℂ,ComplexModel (k+1)) X (ComplexProjectiveSpace (k+1)) ∞)
    (L : HermitianHolomorphicLineBundle.{0,0} (d+1) X)
    {φ : X → EReal} (hφ : IsGlobalQuasiPshPotential (n := d+1) φ)
    (mu : Measure X) (hmu : IsSmoothPositiveVolume (n := d+1) mu)
    (hLocal :
      ∀ (i : Fin ((k+1)+1)) (B : TopologicalSpace.Opens (ComplexModel (k+1)))
        (hsB : ∀ zeta : B, IsSmoothHypersurfaceMember (d+1) p (affinePoint i zeta.val))
        (D : TopologicalSpace.Opens (ComplexModel (k+1))) (hDB : D ≤ B)
        (r : ℕ) (S : Fin r → nativeMultiplierSections
          (tensor (tensor (nativeCanonicalBundle (n := d+1) (X := X)) L) (nativeBertiniHyperplaneBundle p)) φ),
      (∀ zeta : B, ∃ b : Module.Basis (Fin r) ℂ (NativeBertiniMultiplierQuotient p i zeta.val L hφ),
        ∀ j, b j = (nativeMultiplierSectionMap (tensor (nativeCanonicalBundle (n := d+1) (X := X)) L)
          (nativeBertiniHyperplaneBundle p) hφ (nativeBertiniAffineSection p i zeta.val)).range.mkQ (S j)) →
      (∀ zeta : D,
        let hsm := hsB ⟨zeta.val,hDB zeta.property⟩
        letI := nativeBertiniMemberChartedSpace p i zeta.val hsm
        letI := nativeBertiniMemberComplex p i zeta.val hsm
        letI := isCompact_iff_compactSpace.mp
          (isClosed_member p p.contMDiff.continuous (affinePoint i zeta.val)).isCompact
        Function.Injective (nativeBertiniPhysicalQuotientRestriction p i zeta.val hsm L hφ)) →
      HasLocalCircleMEP (nativeBertiniQuotientFrameEnergy p i B hsB L hφ S) D) :
    ∃ F : Finset X, F.Nonempty ∧ IsComplexAnalyticSubset (n := k+1) (finitePointHyperplaneException p F) ∧
      finitePointHyperplaneException p F ≠ univ ∧
      (ofFixedModel (k+1) (HyperplaneSpace (k+1))).LocallyPluripolar (finitePointHyperplaneException p F) ∧
      ∀ (ell : HyperplaneSpace (k+1)) (_hsm0 : IsSmoothHypersurfaceMember (d+1) p ell),
        ell ∉ finitePointHyperplaneException p F →
        ∃ U : TopologicalSpace.Opens (ComplexModel (k+1)), affineChart (chartIndex ell) ell ∈ U ∧
          LocallyPluripolarOn (nativeBertiniQuotientInfiniteLocus p (chartIndex ell) L hφ) U ∧
          (ofFixedModel (k+1) (HyperplaneSpace (k+1))).LocallyPluripolar
            (affinePoint (chartIndex ell) '' (nativeBertiniQuotientInfiniteLocus p (chartIndex ell) L hφ ∩ U)) := by
  classical
  obtain ⟨F,hFn,hFa,hFproper,hFpl,hNorm⟩ := exists_nativeBertini_generic_singularNormFamily p L hφ
  refine ⟨F,hFn,hFa,hFproper,hFpl,?_⟩
  intro ell hsm0 hell
  obtain ⟨r,S,B,hsB,D,hDB,hcentre,hb,_havoid,hq⟩ := hNorm ell hsm0 hell
  have hInj := nativeBertiniQuotientRestriction_injective_of_positive_field p L hφ
    (chartIndex ell) B hsB D hDB r S hb hq
  have hMEP := hLocal (chartIndex ell) B hsB D hDB r S hb hInj
  have hpsh := (hq.discPshOn_logDetDual_of_local_mep D.isOpen hMEP).plurisubharmonicOn D.isOpen
  obtain ⟨x,hxF⟩ := hFn
  have hproper : ∃ x : X, x ∉ member p ell := ⟨x,fun hxH => hell ⟨x,hxF,hxH⟩⟩
  obtain ⟨r2,S2,V,hV,hsV,_hb2,hDense⟩ :=
    SGPT.Trace.BertiniUniversal.exists_original_fullBase_entire_quotient_finite_fibres p L hφ ell hsm0 hproper mu hmu
  let U : TopologicalSpace.Opens (ComplexModel (k+1)) := ⟨D ∩ V,D.isOpen.inter V.isOpen⟩
  have hUD : U ≤ D := fun _ hz => hz.1
  have hUV : U ≤ V := fun _ hz => hz.2
  have hcentreU : affineChart (chartIndex ell) ell ∈ U := ⟨hcentre,hV⟩
  have hpl : LocallyPluripolarOn (nativeBertiniQuotientInfiniteLocus p (chartIndex ell) L hφ) U := by
    intro y hy
    obtain ⟨a,ha,hball⟩ := Metric.isOpen_iff.mp U.isOpen y hy
    let W : TopologicalSpace.Opens (ComplexModel (k+1)) := ⟨ball y a,isOpen_ball⟩
    have hWV : W ≤ V := fun _ hz => hUV (hball hz)
    obtain ⟨z,hz,hfinite⟩ := hDense W hWV (nonempty_ball.mpr ha)
    have hzB : z.val ∈ B := hDB (hUD (hball hz))
    have hfiniteFrame : ∀ c, nativeBertiniQuotientFrameEnergy p (chartIndex ell) B hsB L hφ S z.val c ≠ ⊤ := by
      intro c
      rw [nativeBertiniQuotientFrameEnergy_apply p (chartIndex ell) B hsB L hφ S ⟨z.val,hzB⟩]
      exact hfinite _
    refine ⟨ball y a,logDetDual (nativeBertiniQuotientFrameEnergy p (chartIndex ell) B hsB L hφ S),
      isOpen_ball,mem_ball_self ha,isPreconnected_ball,hpsh.mono (hball.trans hUD),
      ⟨z.val,hz,hq.logDetDual_ne_bot z.val hfiniteFrame⟩,?_⟩
    intro zeta hzeta hbad
    have hzetaD : zeta ∈ D := hUD (hball hzeta)
    have hinf := (nativeBertiniQuotientInfiniteLocus_iff_frame p (chartIndex ell) L hφ B hsB S hb
      ⟨zeta,hDB hzetaD⟩).mp hbad
    exact hq.logDetDual_eq_bot_of_exists_eq_top hzetaD hinf
  exact ⟨U,hcentreU,hpl,sourceLocallyPluripolar_affine_image_of_local (chartIndex ell) U _ hpl⟩


theorem exists_uniform_nativeBertini_local_infinite_locus_pluripolar
    [ConnectedSpace X] {k : ℕ}
    (p : ContMDiffMap 𝓘(ℂ,ComplexModel (d+1)) 𝓘(ℂ,ComplexModel (k+1)) X (ComplexProjectiveSpace (k+1)) ∞)
    (G : HermitianHolomorphicLineBundle.{0,0} (d+1) X)
    (hG : SGPT.Bergman.PolynomialH0Growth.IsSourceSmoothHermitianMetric G)
    (hGpos : (sourceNativeFirstChernForm G hG).val.IsKahler)
    (φ : X → EReal) (hφ : IsGlobalQuasiPshPotential (n := d+1) φ) :
    ∃ k₀ : ℕ, 0 < k₀ ∧ ∀ (A : HermitianHolomorphicLineBundle.{0,0} (d+1) X)
      (hA : SGPT.Bergman.PolynomialH0Growth.IsSourceSmoothHermitianMetric A),
      (sourceNativeFirstChernForm A hA).val.IsSemipositive → ∀ power : ℕ, k₀ ≤ power →
      let L := twistedPower G A power

    ∃ F : Finset X, F.Nonempty ∧ IsComplexAnalyticSubset (n := k+1) (finitePointHyperplaneException p F) ∧
      finitePointHyperplaneException p F ≠ univ ∧
      (ofFixedModel (k+1) (HyperplaneSpace (k+1))).LocallyPluripolar (finitePointHyperplaneException p F) ∧
      ∀ (ell : HyperplaneSpace (k+1)) (_hsm0 : IsSmoothHypersurfaceMember (d+1) p ell),
        ell ∉ finitePointHyperplaneException p F →
        ∃ U : TopologicalSpace.Opens (ComplexModel (k+1)), affineChart (chartIndex ell) ell ∈ U ∧
          LocallyPluripolarOn (nativeBertiniQuotientInfiniteLocus p (chartIndex ell) L hφ) U ∧
          (ofFixedModel (k+1) (HyperplaneSpace (k+1))).LocallyPluripolar
            (affinePoint (chartIndex ell) '' (nativeBertiniQuotientInfiniteLocus p (chartIndex ell) L hφ ∩ U)) := by
  let : MeasurableSpace X := borel X
  let : BorelSpace X := ⟨rfl⟩
  obtain ⟨k0,hk0,hLocal⟩ := exists_uniform_native_quotient_local_circle_mep p G hG hGpos φ hφ
  refine ⟨k0,hk0,?_⟩
  intro A hA hAsemi power hpower
  dsimp only
  let omegaG : KahlerBackground (d+1) X := ⟨sourceNativeFirstChernForm G hG,hGpos⟩
  exact native_infinite_locus_pluripolar_of_produced_local_circle p (twistedPower G A power) hφ
    (IntegrationCurrent.kahlerVolume omegaG)
    (KahlerVolumeSmoothPositive.isSmoothPositiveVolume_kahlerVolume omegaG)
    (hLocal A hA hAsemi power hpower)

end SGPT.Trace.Bertini
