import SGPT.Projective.OkounkovOriginalBookKahlerHCP
import SGPT.Projective.OkounkovOriginalPerturbGeometry
import SGPT.Projective.OkounkovFloorDegreeHausdorff

/-! Genuine original positive-perturbation outer polytopes, EVERY large original degree.
Blueprint: okounkov-original-perturb-outer-limit.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 3500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Okounkov.OriginalBook
open Set Filter MeasureTheory CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Okounkov.AlgebraicValuation SGPT.Okounkov.ValGen2
open scoped Topology Pointwise
variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ))
    {m : ℕ} [SmoothOfRelativeDimension (m+1) f] (E : ClosedProjectiveEmbedding f)
    [Nonempty (SchemeComplexPoint f)]
local instance perturbOuterLimitTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance perturbOuterLimitCharts : ChartedSpace (ComplexModel (m+1)) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f (m+1)
local instance perturbOuterLimitManifold [IsSeparated f] [QuasiCompact f] : IsComplexManifold (m+1) (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f (m+1)

/-- SAME actual positive-perturbation raw polytopes have their genuine all-original-degree outer limit. -/
theorem exists_positivePerturb_outerPolytope_limit {L A : X.Modules}
    (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f (m+1) E L)
    (aA : LineBundleAtlas A) (K : SchemeLineBundleMetric f (m+1) E A)
    (hK : letI := E.isSeparated; letI := E.quasiCompact; (K.curvature aA).val.IsKahler)
    {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact; IsThetaPshPotential (H.curvature a).val φ)
    (v : AddValuation X.functionField (WithTop (Lex (Fin (m+1) → ℤ)))) (hv : Function.Surjective v)
    (q p : ℕ) (hq : 0<q) (hp : 0<p) :
    letI := E.isProper
    letI := E.isSeparated
    letI := E.quasiCompact
    let b := OkoNS.perturbAtlas a aA q p
    let Q := fun g => AlgebraicValuation.twistedMultiplierValues
      (T:=SheafOfModules.unit X.ringCatSheaf) f (m+1) E v (valuationCenter f v) g
      ((b.tensorPower g).tensorPower 1) (fun x => (q:EReal)*φ x)
    let R := fun k : ℕ => (((k/q:ℕ):ℝ)/(k:ℝ)) • poly Q (k/q)
    ∃ (hKc : IsCompact (centreOkounkovBody f v b)) (hKv : Convex ℝ (centreOkounkovBody f v b)),
      let B := (q:ℝ)⁻¹ • ValGen.partialBody f (m+1) E v (valuationCenter f v) b
        (SGPT.GAGA.OkoClose.coneOver _ hKc hKv) (fun x => (q:EReal)*φ x)
      IsCompact B ∧ Convex ℝ B ∧ B.Nonempty ∧
      (∀ᶠ k : ℕ in atTop, IsCompact (R k) ∧ (R k).Nonempty) ∧
      Tendsto (fun k => Metric.hausdorffDist (R k) B) atTop (𝓝 0) := by
  let := E.isProper
  let := E.isSeparated
  let := E.quasiCompact
  let : MeasurableSpace (SchemeComplexPoint f) := borel _
  have : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  let b := OkoNS.perturbAtlas a aA q p
  let HM := originalPerturbMetric f (m+1) E a H aA K q p
  let ψ := fun x => (q:EReal)*φ x
  let rM := fun g => (b.tensorPower g).tensorPower 1
  let Q := fun g => AlgebraicValuation.twistedMultiplierValues f (m+1) E v (valuationCenter f v) g (rM g) ψ
  obtain ⟨hcur,hbig⟩ := original_positivePerturbation_kahler_and_big f (m+1) E a H aA K hK hφ q p hq hp
  obtain ⟨hKc,hKv,hlim⟩ := tendsto_twistedMultiplierPolytope_kahler_positiveDimension f E b
    (b.tensorPower 0) HM hbig v hv rM hcur
  let F := ValGen.partialBody f (m+1) E v (valuationCenter f v) b
    (SGPT.GAGA.OkoClose.coneOver _ hKc hKv) ψ
  obtain ⟨hKc₁,hKv₁,hFc,hFv,hFne,hFvol⟩ := OriginalAnalyticUpperPoints.exists_kahler_partialBody_geometry
    f E b HM hbig v hv (valuationCenter f v) hcur
  have hθ := PartialBody.isThetaPshPotential_of_isKahlerCurrentPotential hcur
  have hpos := original_iVolume_pos_of_kahler_allDimensions f (m+1) E b HM hcur
  have hdom := eventually_twistedMultiplierPolytope_compact_nonempty_positiveDimension
    f E b (b.tensorPower 0) HM hbig v hv (valuationCenter f v) rM hθ hpos
  have hP : ∀ᶠ g : ℕ in atTop, IsCompact (poly Q g) ∧ (poly Q g).Nonempty ∧ Convex ℝ (poly Q g) := by
    filter_upwards [hdom] with g hg
    exact ⟨hg.2,(hg.1.image _).convexHull,convex_convexHull ℝ _⟩
  have hfloor := FloorDegreeHausdorff.floor_degree_hausdorff_limit q hq F hFc hFne hFv (poly Q) hP hlim
  refine ⟨hKc,hKv,IsCompact.smul _ hFc,hFv.smul _,?_,?_,hfloor.2⟩
  · exact hFne.smul_set
  · exact hfloor.1.mono fun _ hk => ⟨hk.1,hk.2.1⟩
end SGPT.Okounkov.OriginalBook
