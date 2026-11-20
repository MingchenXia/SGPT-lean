import SGPT.Projective.OkounkovOriginalIsoMultiplier
import SGPT.AlmostSemigroup.CommonConeMonotonicity
import SGPT.Projective.OkounkovOriginalBookRescalingIVolume
import SGPT.Projective.OkounkovOriginalPerturbIsomorphisms

/-! SAME literal original isomorphism carriers and existing partial bodies in independently retained actual cones.
Blueprint: okounkov-original-carrier-body-transport.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Okounkov.OriginalCarrierBodyTransport
open Set CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open scoped Pointwise
open SGPT.Okounkov.AlgebraicValuation SGPT.AlmostSemigroup SGPT.AlmostSemigroup.Class SGPT.AlmostSemigroup.Okounkov
variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
    [SmoothOfRelativeDimension n f] (E : ClosedProjectiveEmbedding f)
local instance carrierBodyTransportTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance carrierBodyTransportCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n

/-- Actual original isomorphism and inverse manufacture equality of ENTIRE literal raw multiplier carriers. -/
theorem multiplierSectionSet_eq_of_iso {L M : X.Modules} (e : L ≅ M) (a : LineBundleAtlas L) (b : LineBundleAtlas M)
    (v : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ)))) {c : X} (hc : IsNonnegAt v c)
    (φ : SchemeComplexPoint f → EReal) :
    AlgebraicValuation.multiplierSectionSet f n E v c a φ = AlgebraicValuation.multiplierSectionSet f n E v c b φ :=
  Set.Subset.antisymm (OriginalIsoMultiplier.multiplierSectionSet_subset_iso f n E e a b v hc φ)
    (OriginalIsoMultiplier.multiplierSectionSet_subset_iso f n E e.symm b a v hc φ)

/-- Genuine original isomorphism body transport with EXPLICIT actual low-level cone/locus domains, no target equality premise. -/
theorem partialBody_eq_of_iso {L M : X.Modules} (e : L ≅ M) (a : LineBundleAtlas L) (b : LineBundleAtlas M)
    (v : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ)))) {c : X} (hc : IsNonnegAt v c)
    (φ : SchemeComplexPoint f → EReal) (C D : AdmissibleCone n)
    (hsub : AlgebraicValuation.multiplierSectionSet f n E v c a φ ⊆ (latticePoints C.cone : Set ((Fin n → ℤ)×ℤ)))
    (hΓ : (⟨_,hsub⟩ : ConeSubset C) ∈ almostSemigroupLocus C)
    (hsub' : AlgebraicValuation.multiplierSectionSet f n E v c b φ ⊆ (latticePoints D.cone : Set ((Fin n → ℤ)×ℤ)))
    (hΓ' : (⟨_,hsub'⟩ : ConeSubset D) ∈ almostSemigroupLocus D) :
    ValGen.partialBody f n E v c a C φ = ValGen.partialBody f n E v c b D φ := by
  rw [ValGen.partialBody_eq a φ hsub hΓ,ValGen.partialBody_eq b φ hsub' hΓ']
  have hraw := multiplierSectionSet_eq_of_iso f n E e a b v hc φ
  exact Set.Subset.antisymm
    (CommonConeMonotonicity.bodyExtension_mono_of_carrier_subset ⟨⟨_,hsub⟩,hΓ⟩ ⟨⟨_,hsub'⟩,hΓ'⟩ hraw.subset)
    (CommonConeMonotonicity.bodyExtension_mono_of_carrier_subset ⟨⟨_,hsub'⟩,hΓ'⟩ ⟨⟨_,hsub⟩,hΓ⟩ hraw.symm.subset)

/-- ACTUAL original perturbation common powers have the SAME scaled body, using genuine original regrouping and Veronese sections. -/
theorem partialBody_power_perturbRegroup_eq {L A : X.Modules}
    (a : LineBundleAtlas L) (aA : LineBundleAtlas A) (q p r : ℕ) (hr : 0<r)
    (b : LineBundleAtlas (bundleTensor (bundleTensorPower L q) (bundleTensorPower A p)))
    (b' : LineBundleAtlas (bundleTensor (bundleTensorPower L (q*r)) (bundleTensorPower A (p*r))))
    (v : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ)))) {c : X} (hc : IsNonnegAt v c)
    (φ : SchemeComplexPoint f → EReal) (C D : AdmissibleCone n)
    (hsub : AlgebraicValuation.multiplierSectionSet f n E v c b φ ⊆ (latticePoints C.cone : Set ((Fin n → ℤ)×ℤ)))
    (hΓ : (⟨_,hsub⟩ : ConeSubset C) ∈ almostSemigroupLocus C)
    (hsub' : AlgebraicValuation.multiplierSectionSet f n E v c b' (fun x => (r:EReal)*φ x) ⊆
      (latticePoints D.cone : Set ((Fin n → ℤ)×ℤ)))
    (hΓ' : (⟨_,hsub'⟩ : ConeSubset D) ∈ almostSemigroupLocus D) :
    letI := E.isSeparated
    letI := E.quasiCompact
    ValGen.partialBody f n E v c b' D (fun x => (r:EReal)*φ x) =
      (r:ℝ) • ValGen.partialBody f n E v c b C φ := by
  let := E.isSeparated
  let := E.quasiCompact
  have hres := ValGen2.partialBody_tensorPower_eq_smul f n E v hc b hr (b.tensorPower r) φ hsub hΓ
  obtain ⟨hsubP,hΓP⟩ := hres.1
  have heq := partialBody_eq_of_iso f n E (OriginalPerturbIsomorphisms.perturbPowerIso a aA q p r)
    (b.tensorPower r) b' v hc (fun x => (r:EReal)*φ x) (ValGen2.veroneseCone C hr) D hsubP hΓP hsub' hΓ'
  exact heq.symm.trans hres.2
end SGPT.Okounkov.OriginalCarrierBodyTransport
