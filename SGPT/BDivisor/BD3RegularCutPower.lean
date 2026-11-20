import SGPT.Projective.OriginalAlgebraicRegularCut
import SGPT.BDivisor.BD3KodairaAllPowers

/-!
# algebraic regular cuts of a prescribed power

Source: `rmk:bdiv:L749` (chapter_bdiv.tex, line 749).  The Codex producers
`exists_same_algebraic_regular_cut` → `…_smooth` → `…_whole` → `…_dimension` →
`exists_originalRegularCut` each start from ONE native regular cut chosen by
`exists_nativeRegularCut`; their proofs are parametric in that cut.  Here they are restated for an
ARBITRARY given native regular cut `D` (`exists_same_algebraic_regular_cut_of`,
`algebraic_regular_cut_smooth_of`, `exists_originalRegularCut_of_nativeCut`), and combined with
`BD3KodairaAllPowers.exists_nativeRegularCut_power_ge` to give original algebraic smooth cuts of every
sufficiently large power (`exists_originalRegularCut_power_ge`).
-/

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

section GivenCut

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  (E : ClosedProjectiveEmbedding f) [SmoothOfRelativeDimension n f]
  [IsSeparated f] [QuasiCompact f]
  {L : X.Modules} (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f n E L)

local instance bd3CutPointTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance bd3CutPointCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance bd3CutPointManifold : IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n
local instance bd3CutStalkAlgebra (p : SchemeComplexPoint f) :
    Algebra ℂ (X.presheaf.stalk (schemeComplexPointImage f p)) :=
  stalkComplexAlgebra f (schemeComplexPointImage f p)
local instance bd3CutPointAlgebra (p : SchemeComplexPoint f) :
    Algebra (X.presheaf.stalk (schemeComplexPointImage f p)) ℂ :=
  (schemeComplexPointStalkEval f p).toAlgebra

private theorem algCoef_degree_cast_bd3 {r t : ℕ} (h : r = t)
    {U : X.Opens} (α : LocalBundleFrame L U) (σ : bundlePowerGlobalSections L r) :
    algCoef α t (h ▸ σ : bundlePowerGlobalSections L t) = algCoef α r σ := by
  cases h
  rfl

private theorem sectionZeroIdeal_degree_cast_bd3 {r t : ℕ} (h : r = t)
    (σ : bundlePowerGlobalSections L r) :
    sectionZeroIdealSheaf (a.tensorPower t) (h ▸ σ : bundlePowerGlobalSections L t) =
      sectionZeroIdealSheaf (a.tensorPower r) σ := by
  cases h
  rfl

variable (hK : (H.curvature a).val.IsKahler)
  (D : NativeRegularCut (schemeNativePositiveLine f n E a H hK))

/-- For a GIVEN native regular cut `D` of the positive bundle of a positive algebraic metric, the
same algebraic power has a global section with the same coefficients and the same zero ideal
(the proof of `exists_same_algebraic_regular_cut`, with `D` prescribed). -/
theorem exists_same_algebraic_regular_cut_of :
    ∃ σ : bundlePowerGlobalSections L D.power,
      (∀ (i : a.I) (p : SchemeComplexPoint f), schemeComplexPointImage f p ∈ a.opens i →
        sectionCoefficient
          (positivePower (schemeHermitianLineBundle f n E a H) (D.power - 1)).Fiber
          (positivePowerAtlasFrame (schemeHermitianAtlasFrame f n E a H (a.frame i)) (D.power - 1)).val
            D.cuttingSection p =
          schemeOpenRegularFunction f n E (a.opens i) (algCoef (a.frame i) D.power σ) p) ∧
      ∀ (p : SchemeComplexPoint f) (g : SchemeComplexPoint f → ℂ),
        (analytificationIdeal f n E (sectionZeroIdealSheaf (a.tensorPower D.power) σ)).mem p g ↔
          (nativeSectionIdeal
            (positivePower (schemeHermitianLineBundle f n E a H) (D.power - 1)) D.cuttingSection).mem p g := by
  let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  obtain ⟨σ, hread, hideal⟩ := exists_algebraic_positivePower_section f n E a H
    (D.power - 1) D.cuttingSection
  have hq : D.power - 1 + 1 = D.power := Nat.sub_add_cancel (Nat.succ_le_of_lt D.power_pos)
  let σ' : bundlePowerGlobalSections L D.power := hq ▸ σ
  refine ⟨σ', ?_, ?_⟩
  · intro i p hp
    change _ = schemeOpenRegularFunction f n E (a.opens i)
      (algCoef (a.frame i) D.power (hq ▸ σ : bundlePowerGlobalSections L D.power)) p
    rw [algCoef_degree_cast_bd3]
    exact hread i p hp
  · intro p g
    change (analytificationIdeal f n E
      (sectionZeroIdealSheaf (a.tensorPower D.power) (hq ▸ σ : bundlePowerGlobalSections L D.power))).mem p g ↔ _
    rw [sectionZeroIdeal_degree_cast_bd3]
    exact hideal p g

/-- For a GIVEN native regular cut `D` and an algebraic section reading it, the algebraic zero
scheme is smooth over `ℂ` (the proof of `exists_same_algebraic_regular_cut_smooth`, with the
derivations supplied by the parametric `regularCut_stalk_derivation`). -/
theorem algebraic_regular_cut_smooth_of (σ : bundlePowerGlobalSections L D.power)
    (hread : ∀ (j : a.I) (p : SchemeComplexPoint f), schemeComplexPointImage f p ∈ a.opens j →
      sectionCoefficient
        (positivePower (schemeHermitianLineBundle f n E a H) (D.power - 1)).Fiber
        (positivePowerAtlasFrame (schemeHermitianAtlasFrame f n E a H (a.frame j)) (D.power - 1)).val
          D.cuttingSection p =
        schemeOpenRegularFunction f n E (a.opens j) (algCoef (a.frame j) D.power σ) p) :
    Smooth (sectionZeroι (a.tensorPower D.power) σ ≫ f) := by
  let : Smooth f := SmoothOfRelativeDimension.smooth n f
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hderiv := regularCut_stalk_derivation f n E a H hK D σ hread
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


/-- For a GIVEN native regular cut, the algebraic zero scheme has smooth relative dimension
`n - 1`. -/
theorem exists_same_algebraic_regular_cut_dimension_of :
    ∃ σ : bundlePowerGlobalSections L D.power,
      (∀ (j : a.I) (p : SchemeComplexPoint f), schemeComplexPointImage f p ∈ a.opens j →
        sectionCoefficient
          (positivePower (schemeHermitianLineBundle f n E a H) (D.power - 1)).Fiber
          (positivePowerAtlasFrame (schemeHermitianAtlasFrame f n E a H (a.frame j)) (D.power - 1)).val
            D.cuttingSection p =
          schemeOpenRegularFunction f n E (a.opens j) (algCoef (a.frame j) D.power σ) p) ∧
      (∀ (p : SchemeComplexPoint f) (g : SchemeComplexPoint f → ℂ),
        (analytificationIdeal f n E (sectionZeroIdealSheaf (a.tensorPower D.power) σ)).mem p g ↔
          (nativeSectionIdeal
            (positivePower (schemeHermitianLineBundle f n E a H) (D.power - 1)) D.cuttingSection).mem p g) ∧
      SmoothOfRelativeDimension (n - 1) (sectionZeroι (a.tensorPower D.power) σ ≫ f) := by
  obtain ⟨σ, hread, hideal⟩ := exists_same_algebraic_regular_cut_of f n E a H hK D
  let : Smooth (sectionZeroι (a.tensorPower D.power) σ ≫ f) :=
    algebraic_regular_cut_smooth_of f n E a H hK D σ hread
  refine ⟨σ, hread, hideal, ?_⟩
  exact smoothOfRelativeDimension_of_complexPoint_cotangent_finrank
    (sectionZeroι (a.tensorPower D.power) σ ≫ f) (n - 1)
      (regularCutPoint_cotangent_finrank f n E a H hK D σ hread)

end GivenCut

section OriginalCut

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension (n + 1) f] [IsSeparated f] [QuasiCompact f]
  (E : ClosedProjectiveEmbedding f)

local instance bd3OriginalCutTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance bd3OriginalCutCharts : ChartedSpace (ComplexModel (n + 1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (n + 1)
local instance bd3OriginalCutManifold : IsComplexManifold (n + 1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (n + 1)

/-- Every native regular cut of a positive original line is the native cut of an original
algebraic regular cut. -/
theorem exists_originalRegularCut_of_nativeCut (P : OriginalPositiveLine f (n + 1) E)
    (D : NativeRegularCut P.native) :
    ∃ C : OriginalRegularCut f n E P, C.nativeCut = D := by
  obtain ⟨σ, hread, hideal, hdim⟩ :=
    exists_same_algebraic_regular_cut_dimension_of f (n + 1) E P.atlas P.metric P.positive D
  exact ⟨⟨D, σ, hread, hideal, by simpa only [Nat.add_sub_cancel] using hdim⟩, rfl⟩

/-- Original algebraic smooth regular cuts of a positive line exist in EVERY sufficiently large
power. -/
theorem exists_originalRegularCut_power_ge (P : OriginalPositiveLine f (n + 1) E) :
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ∃ C : OriginalRegularCut f n E P, C.nativeCut.power = d := by
  let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  obtain ⟨d₀, hd₀⟩ := SGPT.BDivisor.BD3.exists_nativeRegularCut_power_ge (Nat.succ_pos n) P.native
  refine ⟨d₀, fun d hd => ?_⟩
  obtain ⟨D, hD⟩ := hd₀ d hd
  obtain ⟨C, hC⟩ := exists_originalRegularCut_of_nativeCut f n E P D
  exact ⟨C, hC ▸ hD⟩

end OriginalCut

end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
