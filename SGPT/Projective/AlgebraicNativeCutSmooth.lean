import SGPT.Projective.AlgebraicNativeRegularDerivative
import SGPT.Projective.AlgebraicNativeZeroTrace
import SGPT.Projective.AlgebraicSmoothStalk
import SGPT.Projective.PrincipalCotangentSmooth
import SGPT.Projective.AlgebraicSectionZeroStalk
import Mathlib.AlgebraicGeometry.AlgClosed.Basic

/-! Smoothness of the ACTUAL SAME original algebraic zero cut, from
manufactured original normal derivatives and the actual stalk kernel.
Blueprint: algebraic-native-cut-smooth.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI

open Set Filter Bundle CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes IsLocalRing
open scoped Topology Manifold ContDiff TensorProduct
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves SGPT.Foundations.Analysis.Pending
open SGPT.Okounkov SGPT.NAPotential.GAGAMult SGPT.NAPotential.Berkovich
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.QuantizationDraft
open SGPT.Bergman.CompactHolomorphicSectionsDraft HermitianHolomorphicLineBundle
open SGPT.Bergman.AnalyticSectionProducts
open SGPT.Trace.Bertini SGPT.Projective.ComplexProjectiveSpace
open SGPT.BDivisor.NSKodaira SGPT.Projective.NumEq.AlgebraicCurveDegree

/-- The genuine original closed-point criterion, retaining the actual
original structural stalk algebra and the entire original scheme. -/
theorem smooth_of_formallySmooth_complexPoint_stalk {Y : Scheme.{0}}
    (g : Y ⟶ Spec (.of ℂ)) [LocallyOfFinitePresentation g]
    (h : ∀ p : SchemeComplexPoint g,
      letI := stalkComplexAlgebra g (schemeComplexPointImage g p)
      Algebra.FormallySmooth ℂ (Y.presheaf.stalk (schemeComplexPointImage g p))) : Smooth g := by
  have : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace g
  rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← TopologicalSpace.Opens.coe_eq_univ,
    ← not_ne_iff, ← Set.nonempty_compl]
  intro H
  obtain ⟨y, hy, hyc⟩ := nonempty_inter_closedPoints H g.smoothLocus.2.isClosed_compl.isLocallyClosed
  let p : SchemeComplexPoint g := ⟨pointOfClosedPoint g y hyc, pointOfClosedPoint_comp g y hyc⟩
  have himage : schemeComplexPointImage g p = y := pointOfClosedPoint_apply g y hyc _
  have hs := (originalStalk_formallySmooth_iff g (schemeComplexPointImage g p)).mp (h p)
  exact hy (himage ▸ hs)

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  (E : ClosedProjectiveEmbedding f) [SmoothOfRelativeDimension n f]
  [IsSeparated f] [QuasiCompact f]
  {L : X.Modules} (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f n E L)

local instance cutSmoothPointTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance cutSmoothPointCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance cutSmoothPointManifold : IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n

/-- The SAME original physical positive metric manufactures a whole native
regular cut whose ACTUAL original algebraic section-zero closed subscheme
is genuinely smooth. No zero-scheme smoothness/differential premise. -/
theorem exists_same_algebraic_regular_cut_smooth (hn : 0 < n)
    (hK : (H.curvature a).val.IsKahler) :
    ∃ D : NativeRegularCut (schemeNativePositiveLine f n E a H hK),
      ∃ σ : bundlePowerGlobalSections L D.power,
        (∀ (i : a.I) (p : SchemeComplexPoint f), schemeComplexPointImage f p ∈ a.opens i →
          sectionCoefficient
            (positivePower (schemeHermitianLineBundle f n E a H) (D.power - 1)).Fiber
            (positivePowerAtlasFrame (schemeHermitianAtlasFrame f n E a H (a.frame i)) (D.power - 1)).val
              D.cuttingSection p =
            schemeOpenRegularFunction f n E (a.opens i) (algCoef (a.frame i) D.power σ) p) ∧
        (∀ (p : SchemeComplexPoint f) (g : SchemeComplexPoint f → ℂ),
          (analytificationIdeal f n E (sectionZeroIdealSheaf (a.tensorPower D.power) σ)).mem p g ↔
            (nativeSectionIdeal
              (positivePower (schemeHermitianLineBundle f n E a H) (D.power - 1)) D.cuttingSection).mem p g) ∧
        Smooth (sectionZeroι (a.tensorPower D.power) σ ≫ f) := by
  let : Smooth f := SmoothOfRelativeDimension.smooth n f
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  obtain ⟨D, σ, hread, hideal, hderiv⟩ :=
    exists_same_algebraic_regular_cut_derivations f n E a H hn hK
  refine ⟨D, σ, hread, hideal, ?_⟩
  let i := sectionZeroι (a.tensorPower D.power) σ
  apply smooth_of_formallySmooth_complexPoint_stalk (i ≫ f)
  intro q
  let z := schemeComplexPointImage (i ≫ f) q
  let p := schemeComplexPointMap (i ≫ f) f i rfl q
  have hpimage : schemeComplexPointImage f p = i z := rfl
  obtain ⟨j, hj⟩ := a.covers (schemeComplexPointImage f p)
  have hsupp : schemeComplexPointImage f p ∈ (sectionZeroIdealSheaf (a.tensorPower D.power) σ).support := by
    have hz : i z ∈ (sectionZeroIdealSheaf (a.tensorPower D.power) σ).support := z.property
    exact hpimage.symm ▸ hz
  have hcoeff0 := (sectionZero_support_iff_coefficient_zero f n E (a.tensorPower D.power) σ
    ((a.frame j).tensorPower D.power) p hj).mp hsupp
  let Bp := positivePower (schemeHermitianLineBundle f n E a H) (D.power - 1)
  let e := positivePowerAtlasFrame (schemeHermitianAtlasFrame f n E a H (a.frame j)) (D.power - 1)
  have he : p ∈ e.val.baseSet := mem_positivePowerAtlasFrame_baseSet _ hj _
  have hsec0 : D.cuttingSection p = 0 := by
    apply (e.val.linearEquivAt ℂ p he).injective
    change sectionCoefficient Bp.Fiber e.val D.cuttingSection p = _
    rw [map_zero, hread j p hj]
    exact hcoeff0
  have hx : p ∈ D.carrier := (linearSection_zero_iff Bp D.sections D.generated D.hyperplane p).mp hsec0
  let A := X.presheaf.stalk (schemeComplexPointImage f p)
  let B := (sectionZeroSubscheme (a.tensorPower D.power) σ).presheaf.stalk z
  let := stalkComplexAlgebra f (schemeComplexPointImage f p)
  let := stalkComplexAlgebra (i ≫ f) z
  let tau : A →+* B := (i.stalkMap z).hom
  let : Algebra A B := tau.toAlgebra
  let : Algebra A ℂ := (schemeComplexPointStalkEval f p).toAlgebra
  let : Algebra B ℂ := (schemeComplexPointStalkEval (i ≫ f) q).toAlgebra
  let : IsScalarTower ℂ A B := IsScalarTower.of_algebraMap_eq fun c =>
    (originalStalk_algebraMap_comp f i z c).symm
  have heval : schemeComplexPointStalkEval f p =
      (schemeComplexPointStalkEval (i ≫ f) q).comp tau :=
    schemeComplexPointStalkEval_comp (i ≫ f) f i rfl q
  let : IsScalarTower A B ℂ := IsScalarTower.of_algebraMap_eq fun r =>
    RingHom.congr_fun heval r
  let : IsScalarTower ℂ A ℂ := originalPointStalk_scalarTower f n p
  obtain ⟨hsm, hft, hfin, hfree⟩ := originalSmoothStalk_differentials f (schemeComplexPointImage f p)
  let : Algebra.FormallySmooth ℂ A := hsm
  let : Module.Finite A Ω[A⁄ℂ] := hfin
  let : Module.Free A Ω[A⁄ℂ] := hfree
  let g : A := X.presheaf.germ (a.opens j) (schemeComplexPointImage f p) hj
    (algCoef (a.frame j) D.power σ)
  have hker : RingHom.ker tau = Ideal.span {g} :=
    sectionZero_stalk_kernel (a.tensorPower D.power) σ z j hj
  have hev_surj : Function.Surjective (schemeComplexPointStalkEval (i ≫ f) q) := by
    intro c
    refine ⟨tau (algebraMap ℂ A c), ?_⟩
    rw [← RingHom.comp_apply, ← heval]
    exact originalPointStalkEval_algebraMap f n p c
  have hBK : maximalIdeal B ≤ RingHom.ker (algebraMap B ℂ) :=
    (IsLocalRing.ker_eq_maximalIdeal (schemeComplexPointStalkEval (i ≫ f) q) hev_surj).ge
  obtain ⟨δ, hδ⟩ := hderiv j p hj hx
  exact PrincipalCotangentSmooth.formallySmooth_of_principal_relation_derivation
    (i.stalkMap_surjective z) g hker δ hδ hBK

end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
