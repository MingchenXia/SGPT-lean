import SGPT.Checks.Comparison.GfImTransport
import SGPT.Checks.Comparison.BJExistPackage
import SGPT.Checks.Comparison.GFRationalDimZero
import SGPT.Checks.Comparison.SourceZeroModels
import SGPT.NAPotential.QwNAConcavity
import SGPT.NAPotential.GFRationalHullRealization
import SGPT.NAPotential.GFRationalCofinality

/-! # ORIGINAL rational hulls: actual section products and analytification at EVERY original point
Source: `lma:gfinimage`, closing paragraph and `eq:gf-rational-hull`.
Blueprint: `gf-rational-hull-comparison.tex`. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.NAPotential.BJ.SourceRationalHull

open SGPT.NAPotential.BJ.GfIm SGPT.NAPotential.BJ.GfIm.RationalHull

open AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes
open SGPT.Okounkov SGPT.NAPotential.Berkovich SGPT.NAPotential.Berkovich.BJSections
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.PSH.VariableComplexAtlas SGPT.Convex.CutSimplex
open SGPT.NAPotential.Berkovich.PiecewiseLinearData.SimplexRevision
open SGPT.NAPotential.Berkovich.PiecewiseLinearData.SimplexRevision.WholeHull
open SGPT.Foundations.Envelope
open scoped BigOperators Classical ENNReal

variable {X : Scheme.{0}} {L : X.Modules} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] (E : ClosedProjectiveEmbedding f) [IsProjective f] [IsIntegral X]

local instance rationalHullProper : IsProper f :=
  (ProjectiveFactorizationRingIso.of_isProjective f).isProper
local instance rationalHullPointTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance rationalHullPointCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance rationalHullPointManifold : IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n

variable (H : SchemeLineBundleMetric f n E L)

/-- The all-point original section maximum formula through the narrow actual dimension-zero geometry. -/
theorem potentialAn_sectionsMaxLog_all_narrow (b : LineBundleAtlas L) (N : ℕ)
    {J : Type} [Fintype J] [Nonempty J] (t : J → bundlePowerGlobalSections L N)
    (ht : ∀ j, t j ≠ 0) {K : ℕ} (hK : 0 < K) (v : BerkovichPoint f) :
    potentialAn n E (fun p => (((K : ℝ)⁻¹ : ℝ) : EReal) * sectionsMaxLog f n E b N t H p) v =
      -(((v.idealVal (sectionsIdeal b N t) / K : ℝ≥0∞)) : EReal) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have hΦ := isThetaPshPotential_sectionsMaxLog f 0 E b N t H ht
    have hψ := SGPT.Okounkov.TranscendentalCore.isThetaPshPotential_nonneg_smul hΦ
      (inv_nonneg.mpr (Nat.cast_nonneg (α := ℝ) K))
    have := NarrowDimensionZero.berkovichPoint_subsingleton_of_dim_zero f
    have hv : v = BerkovichPoint.trivial f := Subsingleton.elim _ _
    rw [SGPT.NAPotential.BJ.SourceZeroModels.potentialAn_eq_zero_of_dim_zero (E := E) hψ.quasiPshPotential v,
      idealVal_sectionsIdeal f b N t v, hv]
    simp [powerSectionValue_trivial b N _ (ht _)]
  · exact potentialAn_sectionsMaxLog f n E b N t H hn ht hK v

/-- The ACTUAL original section maximum analytifies to its actual logarithmic maximum on ALL X^An. -/
theorem potentialAn_finiteSectionMaximum_eq_logValue (b : LineBundleAtlas L) (N K : ℕ)
    (hK : 0 < K) {J : Type} [Fintype J] [Nonempty J]
    (t : J → bundlePowerGlobalSections L N) (ht : ∀ j, t j ≠ 0) (v : BerkovichPoint f) :
    potentialAn n E (fun p => (((K : ℝ)⁻¹ : ℝ) : EReal) *
      finiteMaximum (fun j => H.sectionLogNormSq b N (t j)) p) v =
    (((K : ℝ)⁻¹ : ℝ) : EReal) * finiteMaximum
      (fun j => fun v : BerkovichPoint f => negativeValue (powerSectionValue b N (t j) v)) v := by
  change potentialAn n E (fun p => (((K : ℝ)⁻¹ : ℝ) : EReal) *
    sectionsMaxLog f n E b N t H p) v = _
  rw [potentialAn_sectionsMaxLog_all_narrow f n E H b N t ht hK v, idealVal_sectionsIdeal,
    finiteMaximum_eq_iSup, scale_iSup_finite _ _ (by positivity)]
  have hterm (j : J) : (((K : ℝ)⁻¹ : ℝ) : EReal) * negativeValue (powerSectionValue b N (t j) v) =
      -((toENNReal (powerSectionValue b N (t j) v) / K : ℝ≥0∞) : EReal) := by
    rw [Assembly.negativeValue_eq_neg_toENNReal (powerSectionValue_nonneg _ _ _ v)]
    simpa only [one_div] using Assembly.inv_mul_neg_coe_ennreal hK
      (toENNReal (powerSectionValue b N (t j) v))
  simp_rw [hterm]
  have h := Exist.iSup_neg_div_add (fun j => toENNReal (powerSectionValue b N (t j) v)) K 0
  simpa only [EReal.coe_zero, add_zero] using h.symm

/-- The ORIGINAL regularized hull at rational s has EXACTLY the actual original vertex
analytification on EVERY original Berkovich point, proved using ONE genuine section family. -/
theorem potentialAn_originalHull_eq_vertexMaximum (b : LineBundleAtlas L)
    (N K : ℕ) (hK : 0 < K)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n (SchemeComplexPoint f))}
    (D : PiecewiseLinearData θ) (hτ : ∀ i, ∃ q : ℚ, D.τ i = q)
    (I : Fin (D.N + 1) → Type) [∀ i, Fintype (I i)] [∀ i, Nonempty (I i)]
    (t : (i : Fin (D.N + 1)) → I i → bundlePowerGlobalSections L N) (ht : ∀ i j, t i j ≠ 0)
    (hA : ∀ i, D.A i = fun p => (((K : ℝ)⁻¹ : ℝ) : EReal) *
      finiteMaximum (fun j => H.sectionLogNormSq b N (t i j)) p)
    (s : ℚ) (hs : (s : ℝ) ≤ D.τ 0) (v : BerkovichPoint f) :
    potentialAn n E (uscRegularization (D.pointwiseUpperConcaveEnvelope (s : ℝ))) v =
      ⨆ u : VertexIndex D.τ (s : ℝ), ∑ i,
        ((vertexVector D.τ (s : ℝ) u i : ℝ) : EReal) * potentialAn n E (D.A i) v := by
  obtain ⟨Q, hQ, F, hF, heq, hval⟩ :=
    exists_originalHull_commonSectionFamily n E H b N K hK D hτ I t ht hA s hs
  rw [heq, potentialAn_finiteSectionMaximum_eq_logValue f n E H b (N * Q) (K * Q)
    (Nat.mul_pos hK hQ) F.sections hF v, hval v]
  apply iSup_congr
  intro u
  apply Finset.sum_congr rfl
  intro i _
  rw [hA i, potentialAn_finiteSectionMaximum_eq_logValue f n E H b N K hK (t i) (ht i) v]

/-- **The ORIGINAL source equation `eq:gf-rational-hull`, on ALL original X^An.**
The nodal sections are the original generators; all hull, product, and finite vertex identities
are produced internally. -/
theorem curveAn_eq_rational_originalHullSup (b : LineBundleAtlas L)
    (N K : ℕ) (hK : 0 < K)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n (SchemeComplexPoint f))}
    (D : PiecewiseLinearData θ) (hτ : ∀ i, ∃ q : ℚ, D.τ i = q)
    (I : Fin (D.N + 1) → Type) [∀ i, Fintype (I i)] [∀ i, Nonempty (I i)]
    (t : (i : Fin (D.N + 1)) → I i → bundlePowerGlobalSections L N) (ht : ∀ i j, t i j ≠ 0)
    (hA : ∀ i, D.A i = fun p => (((K : ℝ)⁻¹ : ℝ) : EReal) *
      finiteMaximum (fun j => H.sectionLogNormSq b N (t i j)) p)
    (v : BerkovichPoint f) :
    D.curveAn n E v = ⨆ q : ℚ, ⨆ (_ : (q : ℝ) < D.τ 0),
      potentialAn n E (uscRegularization (D.pointwiseUpperConcaveEnvelope (q : ℝ))) v +
        ((q : ℝ) : EReal) := by
  rw [D.curveAn_eq_iSup]
  rw [nodeMaximum_eq_rational_cutVertexSup D.τ (fun i => potentialAn n E (D.A i) v)
    0 D.tau_le_tau_zero]
  apply iSup_congr
  intro q
  apply iSup_congr
  intro hq
  rw [potentialAn_originalHull_eq_vertexMaximum f n E H b N K hK D hτ I t ht hA q hq.le v]
  rfl

end SGPT.NAPotential.BJ.SourceRationalHull
