import SGPT.Projective.OkounkovOriginalPerturbOuterLimit
import SGPT.Projective.OkounkovOriginalPerturbRawUpper
import SGPT.Projective.OkounkovOriginalBookDeltapert

/-! Genuine upper control of EVERY large original twisted multiplier value, positive ORIGINAL I-volume.
Blueprint: okounkov-original-general-upper-points.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Okounkov.OriginalBook
open Set Filter MeasureTheory CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Okounkov.AlgebraicValuation SGPT.Okounkov.ValGen2 SGPT.AlmostSemigroup
open SGPT.AlmostSemigroup.Class SGPT.AlmostSemigroup.OkounkovExtension
open scoped Topology Pointwise ENNReal
variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ))
    {m : ℕ} [SmoothOfRelativeDimension (m+1) f] (E : ClosedProjectiveEmbedding f)
    [Nonempty (SchemeComplexPoint f)]
local instance generalUpperPointsTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance generalUpperPointsCharts : ChartedSpace (ComplexModel (m+1)) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f (m+1)
local instance generalUpperPointsManifold [IsSeparated f] [QuasiCompact f] : IsComplexManifold (m+1) (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f (m+1)

/-- Actual original positive-I-volume raw upper control, arbitrary valuation and original twist. -/
theorem exists_general_original_twisted_values_eventually_near_partialBody {L T A : X.Modules}
    (a : LineBundleAtlas L) (aT : LineBundleAtlas T) (H : SchemeLineBundleMetric f (m+1) E L)
    (aA : LineBundleAtlas A) (P : SGPT.LineBundle.AmplePolarization f A)
    (K : SchemeLineBundleMetric f (m+1) E A)
    (hK : letI := E.isSeparated; letI := E.quasiCompact; (K.curvature aA).val.IsKahler)
    (v : AddValuation X.functionField (WithTop (Lex (Fin (m+1) → ℤ)))) (hv : Function.Surjective v)
    (r : ∀ k, LineBundleAtlas (bundleTensor T (bundleTensorPower L k)))
    {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact; IsThetaPshPotential (H.curvature a).val φ)
    (hpos : letI := E.isSeparated; letI := E.quasiCompact;
      letI : MeasurableSpace (SchemeComplexPoint f) := borel _;
      haveI : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩;
      haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact;
      0 < iVolume (H.curvature a) (LocalPotentials.closedRealOneOne_hasLocalPotentials _) φ hφ) :
    letI := E.isProper
    letI := E.isSeparated
    letI := E.quasiCompact
    ∃ (hKc : IsCompact (centreOkounkovBody f v a)) (hKv : Convex ℝ (centreOkounkovBody f v a)),
      ∀ η : ℝ, 0<η → ∀ᶠ k : ℕ in atTop,
        ∀ x∈AlgebraicValuation.twistedMultiplierValues f (m+1) E v (valuationCenter f v) k (r k) φ,
          ∃ z∈ValGen.partialBody f (m+1) E v (valuationCenter f v) a
            (SGPT.GAGA.OkoClose.coneOver _ hKc hKv) φ,
            dist ((k:ℝ)⁻¹ • euclideanCast (m+1) x) z≤η := by
  let := E.isProper
  let := E.isSeparated
  let := E.quasiCompact
  let : MeasurableSpace (SchemeComplexPoint f) := borel _
  have : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  let c := valuationCenter f v
  have hc : IsNonnegAt v c := isNonnegAt_valuationCenter f v
  let q := fun j : ℕ => j+1
  let p := P.power*1
  have hq (j : ℕ) : 0<q j := Nat.succ_pos j
  have hp : 0<p := Nat.mul_pos P.power_pos zero_lt_one
  have hδ : Tendsto (fun j : ℕ => (p:ℝ)/(q j:ℝ)) atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat 1).mpr (tendsto_const_div_atTop_nhds_zero_nat (p:ℝ))
  obtain ⟨hKc,hKv,hpert⟩ := tendsto_normalized_positivePerturb_partialBody_allDimensions
    f (m+1) E a H aA P K hK hφ hpos v hv
  obtain ⟨hKic,hKiv,hFc,hFne,hFlim⟩ := hpert ℕ atTop q (fun _ => p) hq (fun _ => hp) hδ
  let B := ValGen.partialBody f (m+1) E v c a (SGPT.GAGA.OkoClose.coneOver _ hKc hKv) φ
  let F := fun j => (q j:ℝ)⁻¹ • ValGen.partialBody f (m+1) E v c
    (OkoNS.perturbAtlas a aA (q j) p) (SGPT.GAGA.OkoClose.coneOver _ (hKic j) (hKiv j))
    (fun x => (q j:EReal)*φ x)
  have hBc : IsCompact B := ValGen.isCompact_setBody _ _
  have hbig := original_isBig_of_positive_iVolume_allDimensions f (m+1) E a H hφ hpos
  obtain ⟨hKc₀,hKv₀,hsub,hΓ,hvol,hext,hvolB⟩ :=
    multiplierSectionSet_mem_ownBody_almostSemigroupLocus_allDimensions f (m+1) E a H hbig v hv c hφ hpos
  have hBne : B.Nonempty := by
    rw [show B= (bodyExtension (⟨⟨_,hsub⟩,hΓ⟩ : AlmostSpace (SGPT.GAGA.OkoClose.coneOver _ hKc₀ hKv₀)) :
      Set (EuclideanSpace ℝ (Fin (m+1)))) from hext]
    exact (bodyExtension (⟨⟨_,hsub⟩,hΓ⟩ : AlmostSpace (SGPT.GAGA.OkoClose.coneOver _ hKc₀ hKv₀))).nonempty
  let Qj := fun j g => AlgebraicValuation.twistedMultiplierValues (T:=SheafOfModules.unit X.ringCatSheaf)
    f (m+1) E v c g (((OkoNS.perturbAtlas a aA (q j) p).tensorPower g).tensorPower 1)
    (fun x => (q j:EReal)*φ x)
  let R := fun j k : ℕ => (((k/q j:ℕ):ℝ)/(k:ℝ)) • poly (Qj j) (k/q j)
  have houter (j : ℕ) : (∀ᶠ k : ℕ in atTop, IsCompact (R j k) ∧ (R j k).Nonempty) ∧
      Tendsto (fun k => Metric.hausdorffDist (R j k) (F j)) atTop (𝓝 0) := by
    obtain ⟨hKjc,hKjv,hBc,hBv,hBne,hdom,hlim⟩ := exists_positivePerturb_outerPolytope_limit
      f E a H aA K hK hφ v hv (q j) p (hq j) hp
    exact ⟨hdom,hlim⟩
  let Q := fun k : ℕ => (fun x => (k:ℝ)⁻¹ • euclideanCast (m+1) x) ''
    AlgebraicValuation.twistedMultiplierValues f (m+1) E v c k (r k) φ
  have hQR (j : ℕ) : ∀ᶠ k : ℕ in atTop, Q k⊆R j k :=
    OriginalPerturbRawUpper.eventually_rawPoints_subset_scaled_unitPerturbPolytope
      f (m+1) E a aT aA P H hφ v hc (q j) 1 (hq j) zero_lt_one r
  have hnear := OuterApproximationControl.eventually_near_of_compact_outer_limits hBc hBne
    F hFc hFne hFlim R (fun j => (houter j).1.mono fun _ hk => ⟨hk.2,hk.1.isBounded⟩)
    (fun j => (houter j).2) Q hQR
  refine ⟨hKc,hKv,?_⟩
  intro η hη
  filter_upwards [hnear η hη] with k hk x hx
  exact hk _ ⟨x,hx,rfl⟩
end SGPT.Okounkov.OriginalBook
