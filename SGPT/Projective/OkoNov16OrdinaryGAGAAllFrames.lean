import SGPT.Projective.OkounkovNativeOrdinaryGAGA
import SGPT.Okounkov.AlgebraicValuationSections

/-! Actual ordinary original GAGA reader in EVERY original local frame.
Blueprint: oko-nov16-ordinary-gaga-all-frames.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Okounkov.OkoNov16
open Set Filter Bundle CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.QuantizationDraft
open SGPT.Bergman.CompactHolomorphicSectionsDraft HermitianHolomorphicLineBundle
open SGPT.NAPotential.GAGAMult SGPT.GAGA.H0L SGPT.Okounkov.NativeFrames
open SGPT.Okounkov.AlgebraicValuation
variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  (E : ClosedProjectiveEmbedding f) [SmoothOfRelativeDimension n f]
  [IsSeparated f] [QuasiCompact f]
local instance allFrameTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance allFrameCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance allFrameManifold : IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n

theorem ordinaryOriginal_coefficient_transition {L : X.Modules} (σ : Γ(L,⊤))
    {U V : X.Opens} (α : LocalBundleFrame L U) (β : LocalBundleFrame L V)
    {p : SchemeComplexPoint f} (hU : schemeComplexPointImage f p∈U)
    (hV : schemeComplexPointImage f p∈V) :
    schemeOpenRegularFunction f n E V
      (β.coefficients (𝟙 _) (L.val.map V.leTop.op σ)) p =
      schemeFrameTransition f n E α β p * schemeOpenRegularFunction f n E U
        (α.coefficients (𝟙 _) (L.val.map U.leTop.op σ)) p := by
  let W : X.Opens := U⊓V
  let l : W ⟶ U := homOfLE inf_le_left
  let r : W ⟶ V := homOfLE inf_le_right
  have hp : schemeComplexPointImage f p∈W := ⟨hU,hV⟩
  let τ : Γ(X,W)ˣ := localBundleFrameTransition α β l r
  let aW : Γ(X,W) := α.coefficients l (L.val.map W.leTop.op σ)
  let bW : Γ(X,W) := β.coefficients r (L.val.map W.leTop.op σ)
  have h : X.presheaf.map r.op (β.coefficients (𝟙 _) (L.val.map V.leTop.op σ)) =
      τ.val *
        X.presheaf.map l.op (α.coefficients (𝟙 _) (L.val.map U.leTop.op σ)) := by
    calc
      _ = bW :=
        (frame_global_coefficients_restrict β r σ).symm
      _ = τ.val * aW :=
        localBundleFrameTransition_coefficients α β l r (L.val.map W.leTop.op σ)
      _ = _ := congrArg (fun z : Γ(X,W) => τ.val*z)
        (frame_global_coefficients_restrict α l σ)
  have he := congrArg (fun z : Γ(X,W) => schemeOpenRegularFunction f n E W z p) h
  rw [schemeOpenRegularFunction_mul' f E n W _ _ hp,
    schemeOpenRegularFunction_restrict f n E W V inf_le_right _ hp,
    schemeOpenRegularFunction_restrict f n E W U inf_le_left _ hp] at he
  exact he

theorem ordinaryNative_coefficient_transition {L : X.Modules} (a : LineBundleAtlas L)
    (H : SchemeLineBundleMetric f n E L)
    (s : HolomorphicSections (n:=n) (schemeHermitianLineBundle f n E a H).Fiber)
    {U V : X.Opens} (α : LocalBundleFrame L U) (β : LocalBundleFrame L V)
    {p : SchemeComplexPoint f} (hU : schemeComplexPointImage f p∈U)
    (hV : schemeComplexPointImage f p∈V) :
    sectionCoefficient (schemeHermitianLineBundle f n E a H).Fiber
      (schemeHermitianAtlasFrame f n E a H β).val s p =
      schemeFrameTransition f n E α β p *
        sectionCoefficient (schemeHermitianLineBundle f n E a H).Fiber
          (schemeHermitianAtlasFrame f n E a H α).val s p := by
  let e := schemeHermitianAtlasFrame f n E a H α
  let g := schemeHermitianAtlasFrame f n E a H β
  have he : p∈e.val.baseSet := by
    change p∈(schemeHermitianAtlasFrame f n E a H α).val.baseSet
    rwa [schemeHermitianAtlasFrame_baseSet]
  have hg : p∈g.val.baseSet := by
    change p∈(schemeHermitianAtlasFrame f n E a H β).val.baseSet
    rwa [schemeHermitianAtlasFrame_baseSet]
  have hs : s p=e.val.symm p ((e.val ⟨p,s p⟩).2) := (e.val.symm_apply_apply_mk he (s p)).symm
  change (g.val ⟨p,s p⟩).2 = _
  conv_lhs => rw [hs]
  rw [←Trivialization.coordChangeL_apply (R:=ℂ) e.val g.val ⟨he,hg⟩]
  have hlin : (e.val.coordChangeL ℂ g.val p) ((e.val ⟨p,s p⟩).2) =
      (e.val ⟨p,s p⟩).2 * (e.val.coordChangeL ℂ g.val p) 1 := by
    rw [←smul_eq_mul,←map_smul,smul_eq_mul,mul_one]
  rw [hlin,coordChangeL_schemeHermitianAtlasFrame' a H α β hU hV,mul_comm]
  rfl

theorem exists_ordinary_original_allFrame_reader {L : X.Modules} (a : LineBundleAtlas L)
    (H : SchemeLineBundleMetric f n E L)
    (s : HolomorphicSections (n:=n) (schemeHermitianLineBundle f n E a H).Fiber) :
    ∃ σ : Γ(L,⊤), ∀ (U : X.Opens) (β : LocalBundleFrame L U) (p : SchemeComplexPoint f),
      schemeComplexPointImage f p∈U →
      sectionCoefficient (schemeHermitianLineBundle f n E a H).Fiber
        (schemeHermitianAtlasFrame f n E a H β).val s p =
      schemeOpenRegularFunction f n E U
        (β.coefficients (𝟙 _) (L.val.map U.leTop.op σ)) p := by
  obtain ⟨σ,hσ⟩ := exists_algebraic_ordinary_section f n E a H s
  refine ⟨σ,?_⟩
  intro U β p hp
  obtain ⟨i,hi⟩ := a.covers (schemeComplexPointImage f p)
  rw [ordinaryNative_coefficient_transition f n E a H s (a.frame i) β hi hp,hσ i p hi]
  exact (ordinaryOriginal_coefficient_transition f n E σ (a.frame i) β hi hp).symm

end SGPT.Okounkov.OkoNov16
