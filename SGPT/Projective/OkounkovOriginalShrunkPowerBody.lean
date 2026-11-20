import SGPT.Projective.OkounkovOriginalBookRescalingIVolume

/-! Literal OWN original positive-power cones and actual rationally normalized shrinking identity.
Blueprint: okounkov-original-shrunk-power-body.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Okounkov.OriginalBook
open Set Filter MeasureTheory CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Okounkov.AlgebraicValuation SGPT.AlmostSemigroup
open scoped Topology ENNReal Pointwise
variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ))

/-- The literal original positive power's OWN full-body cone; true full-body geometry is manufactured. -/
def ownPositivePowerCone [IsProper f] {n : ℕ} {L : X.Modules}
    (v : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ)))) (a : LineBundleAtlas L)
    (hKc : IsCompact (centreOkounkovBody f v a)) (hKv : Convex ℝ (centreOkounkovBody f v a))
    (d : ℕ) (hd : 0<d) (b : LineBundleAtlas (bundleTensorPower L d)) : AdmissibleCone n := by
  have he : centreOkounkovBody f v b=(d:ℝ)•centreOkounkovBody f v a :=
    okounkovBody_tensorPower (isNonnegAt_valuationCenter f v) a hd b
  have hDc : IsCompact (centreOkounkovBody f v b) := by rw [he]; exact IsCompact.smul (d:ℝ) hKc
  have hDv : Convex ℝ (centreOkounkovBody f v b) := by rw [he]; exact hKv.smul (d:ℝ)
  exact SGPT.GAGA.OkoClose.coneOver _ hDc hDv

local instance shrunkPowerBodyTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance shrunkPowerBodyCharts {n : ℕ} [SmoothOfRelativeDimension n f] : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance shrunkPowerBodyManifold {n : ℕ} [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f] : IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n

/-- Exact literal rational shrinking identity in ACTUAL OWN original power/body cones, all dimensions. -/
theorem normalized_shrunk_power_partialBody_eq
    (n : ℕ) [SmoothOfRelativeDimension n f] (E : ClosedProjectiveEmbedding f)
    [Nonempty (SchemeComplexPoint f)] {L : X.Modules}
    (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f n E L) (hbig : SGPT.LineBundle.IsBig f L n)
    (v : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ)))) (hv : Function.Surjective v)
    (hKc : haveI := E.isProper; IsCompact (centreOkounkovBody f v a))
    (hKv : haveI := E.isProper; Convex ℝ (centreOkounkovBody f v a))
    (φ : SchemeComplexPoint f → EReal) (β : ℚ) (hβ1 : (β:ℝ)<1)
    (hφr : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val (fun x => ((((1-(β:ℝ))⁻¹:ℝ):EReal))*φ x))
    (hpos : letI := E.isSeparated; letI := E.quasiCompact;
      letI : MeasurableSpace (SchemeComplexPoint f) := borel _;
      haveI : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩;
      haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact;
      0 < iVolume (H.curvature a) (LocalPotentials.closedRealOneOne_hasLocalPotentials _)
        (fun x => ((((1-(β:ℝ))⁻¹:ℝ):EReal))*φ x) hφr)
    (q p : ℕ) (hq : 0<q) (hrep : β=(p:ℚ)/q)
    (b : LineBundleAtlas (bundleTensorPower L (q-p))) :
    haveI := E.isProper
    letI := E.isSeparated
    letI := E.quasiCompact
    ∃ hpq : p<q,
      (q:ℝ)⁻¹ • ValGen.partialBody f n E v (valuationCenter f v) b
        (ownPositivePowerCone f v a hKc hKv (q-p) (Nat.sub_pos_of_lt hpq) b) (fun x => (q:EReal)*φ x) =
      (1-(β:ℝ)) • ValGen.partialBody f n E v (valuationCenter f v) a
        (SGPT.GAGA.OkoClose.coneOver _ hKc hKv) (fun x => ((((1-(β:ℝ))⁻¹:ℝ):EReal))*φ x) := by
  let := E.isProper
  let := E.isSeparated
  let := E.quasiCompact
  let : MeasurableSpace (SchemeComplexPoint f) := borel _
  have : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  have hqR : (0:ℝ)<q := by exact_mod_cast hq
  have hrepR : (β:ℝ)=(p:ℝ)/q := by rw [hrep]; push_cast; rfl
  have hpq : p<q := by exact_mod_cast (div_lt_one hqR).mp (hrepR ▸ hβ1)
  have hd : 0<q-p := Nat.sub_pos_of_lt hpq
  let ψ : SchemeComplexPoint f → EReal := fun x => ((((1-(β:ℝ))⁻¹:ℝ):EReal))*φ x
  obtain ⟨hKc₁,hKv₁,hres⟩ := partialBody_tensorPower_eq_smul_ownBodies_of_iVolume_allDimensions
    f n E a H hbig v hv hφr hpos
  obtain ⟨hDcp,hDvp,hsub,hΓ,heq⟩ := hres (q-p) hd b
  have hbase : ValGen.partialBody f n E v (valuationCenter f v) b
      (ownPositivePowerCone f v a hKc hKv (q-p) hd b) (fun x => ((q-p:ℕ):EReal)*ψ x) =
      ((q-p:ℕ):ℝ) • ValGen.partialBody f n E v (valuationCenter f v) a
        (SGPT.GAGA.OkoClose.coneOver _ hKc hKv) ψ := heq
  have hcoef : (q:ℝ)⁻¹*((q-p:ℕ):ℝ)=1-(β:ℝ) := by
    rw [Nat.cast_sub hpq.le,hrepR]
    field_simp
  have hprod : ((q-p:ℕ):ℝ)*(1-(β:ℝ))⁻¹=(q:ℝ) := by
    change (((q-p:ℕ):ℝ)/(1-(β:ℝ)))=(q:ℝ)
    apply (div_eq_iff (sub_pos.mpr hβ1).ne').mpr
    have hh := congrArg (fun z : ℝ => (q:ℝ)*z) hcoef
    simpa only [←mul_assoc,mul_inv_cancel₀ hqR.ne',one_mul] using hh
  have hweight : (fun x => ((q-p:ℕ):EReal)*ψ x)=(fun x => (q:EReal)*φ x) := by
    funext x
    dsimp only [ψ]
    rw [←mul_assoc]
    change (((((q-p:ℕ):ℝ):EReal))*((((1-(β:ℝ))⁻¹:ℝ):EReal)))*φ x = ((q:ℝ):EReal)*φ x
    rw [←EReal.coe_mul,hprod]
  rw [hweight] at hbase
  refine ⟨hpq,?_⟩
  have hh := congrArg (fun S : Set (EuclideanSpace ℝ (Fin n)) => (q:ℝ)⁻¹ • S) hbase
  simpa only [smul_smul,hcoef] using hh
end SGPT.Okounkov.OriginalBook
