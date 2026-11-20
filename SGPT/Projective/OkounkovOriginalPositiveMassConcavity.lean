import SGPT.Projective.OkounkovOriginalPerturbedRealConcavity
import SGPT.Projective.OkounkovOriginalBookDeltapert
import SGPT.Foundations.Analysis.Pending.SingularPositiveConvexMixedMass

/-! Actual positive-nonpluripolar-mass concavity on the SAME original bodies.
Blueprint: okounkov-original-positive-mass-concavity.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Okounkov.OriginalBook
open Set Filter MeasureTheory CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.Pending.ThetaPshConvexCombination
open SGPT.Foundations.Analysis.Pending.EndpointMixedMassConvexCombination
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Okounkov.AlgebraicValuation SGPT.Okounkov.TranscendentalCore SGPT.AlmostSemigroup
open scoped Topology Pointwise ENNReal
variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ))
    {m : ℕ} [SmoothOfRelativeDimension (m+1) f] (E : ClosedProjectiveEmbedding f)
    [Nonempty (SchemeComplexPoint f)]
local instance positiveMassConcTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance positiveMassConcCharts : ChartedSpace (ComplexModel (m+1)) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f (m+1)
local instance positiveMassConcManifold [IsSeparated f] [QuasiCompact f] : IsComplexManifold (m+1) (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f (m+1)

theorem original_partialBody_real_concavity_positive_mass {L A : X.Modules}
    (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f (m+1) E L)
    (b : LineBundleAtlas A) (P : SGPT.LineBundle.AmplePolarization f A)
    (K : SchemeLineBundleMetric f (m+1) E A)
    (hK : letI := E.isSeparated;letI := E.quasiCompact;(K.curvature b).val.IsKahler)
    (v : AddValuation X.functionField (WithTop (Lex (Fin (m+1) → ℤ)))) (hv : Function.Surjective v)
    {φ ψ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated;letI := E.quasiCompact;IsThetaPshPotential (H.curvature a).val φ)
    (hψ : letI := E.isSeparated;letI := E.quasiCompact;IsThetaPshPotential (H.curvature a).val ψ)
    {t : ℝ} (ht0 : 0<t) (ht1 : t<1) :
    letI := E.isProper
    letI := E.isSeparated
    letI := E.quasiCompact
    letI : MeasurableSpace (SchemeComplexPoint f) := borel _
    haveI : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
    haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    HasPositivePotentialMass (H.curvature a) φ hφ →
    HasPositivePotentialMass (H.curvature a) ψ hψ →
    ∃ (hKc : IsCompact (centreOkounkovBody f v a)) (hKv : Convex ℝ (centreOkounkovBody f v a)),
      t • ValGen.partialBody f (m+1) E v (valuationCenter f v) a (SGPT.GAGA.OkoClose.coneOver _ hKc hKv) φ +
        (1-t) • ValGen.partialBody f (m+1) E v (valuationCenter f v) a (SGPT.GAGA.OkoClose.coneOver _ hKc hKv) ψ ⊆
      ValGen.partialBody f (m+1) E v (valuationCenter f v) a (SGPT.GAGA.OkoClose.coneOver _ hKc hKv) (convexComb t φ ψ) := by
  let := E.isProper
  let := E.isSeparated
  let := E.quasiCompact
  let : MeasurableSpace (SchemeComplexPoint f) := borel _
  have : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  have : ConnectedSpace (SchemeComplexPoint f) := SGPT.GAGA.OkoClose.connectedSpace_of_isIntegral f E (m+1)
  intro hmφ hmψ
  let θ := H.curvature a
  let omega := schemeProjectiveTNKahlerBackground f (m+1) E
  let χ := convexComb t φ ψ
  have hχ : IsThetaPshPotential θ.val χ := isThetaPshPotential_convexComb_closed hφ hψ ht0.le ht1.le
  have hmχ : HasPositivePotentialMass θ χ hχ :=
    SingularPositiveConvexMixedMass.hasPositivePotentialMass_convexComb_of_right hφ hψ hmψ ht0 ht1
  have hposφ := hmφ.trans_le (PartialBody.diagonalPotentialMass_le_iVolume omega hφ)
  have hposψ := hmψ.trans_le (PartialBody.diagonalPotentialMass_le_iVolume omega hψ)
  have hposχ := hmχ.trans_le (PartialBody.diagonalPotentialMass_le_iVolume omega hχ)
  have hbig := original_isBig_of_positive_iVolume_allDimensions f (m+1) E a H hφ hposφ
  obtain ⟨hKc,hKv,_,_,_⟩ := sectionSemigroup_mem_ownBody_fullSemigroupLocus_allDimensions f a (m+1) E hbig v hv (valuationCenter f v)
  let C := SGPT.GAGA.OkoClose.coneOver _ hKc hKv
  let B := fun ρ => ValGen.partialBody f (m+1) E v (valuationCenter f v) a C ρ
  have hgeom (ρ : SchemeComplexPoint f → EReal) (hρ : IsThetaPshPotential θ.val ρ)
      (hposρ : 0 < iVolume θ (LocalPotentials.closedRealOneOne_hasLocalPotentials _) ρ hρ) :
      IsCompact (B ρ) ∧ (B ρ).Nonempty := by
    obtain ⟨_,_,_,_,_,_,hvol⟩ := multiplierSectionSet_mem_ownBody_almostSemigroupLocus_allDimensions
      f (m+1) E a H hbig v hv (valuationCenter f v) hρ hposρ
    have hBc : IsCompact (B ρ) := ValGen.isCompact_setBody _ _
    have hBv : Convex ℝ (B ρ) := ValGen.convex_setBody _ _
    have hBpos : 0<volume (B ρ) := by
      rw [hvol]
      exact ENNReal.div_pos hposρ.ne' (ENNReal.natCast_ne_top _)
    exact ⟨hBc,(PartialBody.interior_nonempty_of_convex_of_measure_pos volume hBv hBpos).mono interior_subset⟩
  let q := fun j : ℕ => j+1
  let p := fun _ : ℕ => 1
  have hq : ∀j,0<q j := fun j => Nat.succ_pos j
  have hp : ∀j,0<p j := fun _ => zero_lt_one
  have ht : Tendsto (fun j => (p j:ℝ)/(q j:ℝ)) atTop (𝓝 0) := by
    simpa only [p,q,Nat.cast_add,Nat.cast_one] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ))
  obtain ⟨_,_,hlimφ⟩ := tendsto_normalized_positivePerturb_partialBody_allDimensions f (m+1) E a H b P K hK hφ hposφ v hv
  obtain ⟨_,_,hlimψ⟩ := tendsto_normalized_positivePerturb_partialBody_allDimensions f (m+1) E a H b P K hK hψ hposψ v hv
  obtain ⟨_,_,hlimχ⟩ := tendsto_normalized_positivePerturb_partialBody_allDimensions f (m+1) E a H b P K hK hχ hposχ v hv
  obtain ⟨hic,hiv,hφc,hφne,hφlim⟩ := hlimφ ℕ atTop q p hq hp ht
  obtain ⟨_,_,hψc,hψne,hψlim⟩ := hlimψ ℕ atTop q p hq hp ht
  obtain ⟨_,_,hχc,hχne,hχlim⟩ := hlimχ ℕ atTop q p hq hp ht
  let Ci := fun j => SGPT.GAGA.OkoClose.coneOver _ (hic j) (hiv j)
  let Bi := fun (j : ℕ) (ρ : SchemeComplexPoint f → EReal) => (q j:ℝ)⁻¹ • ValGen.partialBody f (m+1) E v (valuationCenter f v)
    (OkoNS.perturbAtlas a b (q j) (p j)) (Ci j) (fun x => (q j:EReal)*ρ x)
  have hstage (j : ℕ) : t•Bi j φ+(1-t)•Bi j ψ⊆Bi j χ := by
    obtain ⟨_,_,hinc⟩ := original_normalized_positivePerturb_real_concavity f E a H b K hK v hv hφ hψ ht0 ht1 (q j) (p j) (hq j) (hp j)
    exact hinc
  refine ⟨hKc,hKv,?_⟩
  exact SGPT.Convex.MinkowskiHausdorffLimit.weighted_sum_subset_of_hausdorff_limits
    (hgeom φ hφ hposφ).1 (hgeom φ hφ hposφ).2
    (hgeom ψ hψ hposψ).1 (hgeom ψ hψ hposψ).2
    (hgeom χ hχ hposχ).1 (hgeom χ hχ hposχ).2
    hφc hφne hψc hψne hχc hχne hφlim hψlim hχlim t (1-t) (Eventually.of_forall hstage)
end SGPT.Okounkov.OriginalBook
