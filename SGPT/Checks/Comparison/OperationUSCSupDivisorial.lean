import SGPT.Checks.Comparison.OperationMaxCorrespondence
import SGPT.NAPotential.NAFiniteJoinComponents
import SGPT.NAPotential.AlgebraicPrimeDictionaryMain
import SGPT.Checks.Comparison.SourceZeroModels

/-! Actual original USC supremum on the ENTIRE augmented source X^Div.
Blueprint: operation-usc-supremum.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.NAPotential.OperationComparison
open Set AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes SGPT.Okounkov
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.PSH.VariableComplexAtlas SGPT.NAPotential.Berkovich
open SGPT.NAPotential.BJ SGPT.NAPotential.BJ.Printed SGPT.NAPotential.BJ.NativePicard
open SGPT.Foundations.Envelope

/-- The exact nonempty finite subsets supply all supremum tests internally. -/
theorem iSup_nonemptyFinite_sup' {I : Type*} {α : Type*} [CompleteLattice α] (a : I → α) :
    (⨆ F : SourceTestCurveFiniteIndex I, F.1.sup' F.2 a) = ⨆ i, a i := by
  classical
  apply le_antisymm
  · exact iSup_le fun F => Finset.sup'_le F.2 a fun i _ => le_iSup a i
  · refine iSup_le fun i => ?_
    exact le_iSup_of_le (⟨{i},Finset.singleton_nonempty i⟩ : SourceTestCurveFiniteIndex I)
      (by simp only [Finset.sup'_singleton]; exact le_rfl)

/-- The real cutoff supremum embeds as its actual extended-real supremum,
with the original nonemptiness and real bound retained. -/
theorem coe_csSup_eq_iSup {I : Type*} [Nonempty I] (a : I → ℝ)
    (hb : BddAbove (range a)) :
    ((sSup (range a) : ℝ) : EReal) = ⨆ i, (a i : EReal) := by
  obtain ⟨B,hB⟩ := hb
  have hb' : BddAbove (range a) := ⟨B,hB⟩
  let z : EReal := ⨆ i, (a i : EReal)
  have hzup : z ≤ (B : EReal) := iSup_le fun i =>
    EReal.coe_le_coe_iff.mpr (hB (mem_range_self i))
  have hztop : z ≠ ⊤ := ne_of_lt (hzup.trans_lt (EReal.coe_lt_top B))
  have hzbot : z ≠ ⊥ := ne_bot_of_le_ne_bot
    (EReal.coe_ne_bot (a (Classical.arbitrary I)))
    (le_iSup (fun i => (a i : EReal)) (Classical.arbitrary I))
  have hz : (z.toReal : EReal) = z := EReal.coe_toReal hztop hzbot
  apply le_antisymm
  · change ((sSup (range a) : ℝ) : EReal) ≤ z
    rw [← hz]
    apply EReal.coe_le_coe_iff.mpr
    apply csSup_le (range_nonempty a)
    rintro _ ⟨i,rfl⟩
    apply EReal.coe_le_coe_iff.mp
    rw [hz]
    exact le_iSup (fun j => (a j : EReal)) i
  · exact iSup_le fun i => EReal.coe_le_coe_iff.mpr (le_csSup hb' (mem_range_self i))

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] (E : ClosedProjectiveEmbedding f)
  [IsProjective f] [IsIntegral X]
local instance uscDivProper : IsProper f := (ProjectiveFactorizationRingIso.of_isProjective f).isProper
local instance uscDivPointTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance uscDivPointCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance uscDivPointManifold : IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n
variable [MeasurableSpace (SchemeComplexPoint f)] [BorelSpace (SchemeComplexPoint f)]
  [CompactSpace (SchemeComplexPoint f)] [ConnectedSpace (SchemeComplexPoint f)]
  {M : X.Modules} (b : LineBundleAtlas M) (HM : SchemeLineBundleMetric f n E M)
  {m : ℕ} (hm : 0 < m)
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n (SchemeComplexPoint f))}
  (hθ : (atlasClosedFormToNative θ).val.GeometricallyEq (((m : ℝ)⁻¹) • HM.curvature b).val)
include b HM hm hθ

/-- Actual pointwise supremum on EVERY original source divisor including
trivial, with actual finite join/net/dictionary geometry produced internally. -/
theorem naPotentialAnAt_uscSup_on_sourceDivisorialSet
    (ω : SourceKahlerForm n (SchemeComplexPoint f)) {I : Type*} [Nonempty I]
    (Γ : I → SourceNAPotential θ)
    (hb : BddAbove (range fun i => sourceNAPotentialCutoff
      (sourceKahlerFormRepresentative ω) (Γ i)))
    (v : BerkovichPoint f) (hv : v ∈ sourceDivisorialSet f) :
    naPotentialAnAt n E (SourceNAPotential.uscSup
      (sourceKahlerFormRepresentative ω) Γ hb) ω v =
      ⨆ i, naPotentialAnAt n E (Γ i) ω v := by
  have hcut :
      (((SourceNAPotential.uscSup (sourceKahlerFormRepresentative ω) Γ hb).component ω).val.max : EReal) =
        ⨆ i, (((Γ i).component ω).val.max : EReal) := by
    have hmax := SourceTestCurve.generalSup_max (sourceKahlerFormRepresentative ω)
      (fun i => ((Γ i).component ω).val)
      (sourceNAFamily_component_bddAbove (sourceKahlerFormRepresentative ω) Γ hb ω)
    change ((SourceTestCurve.generalSup (sourceKahlerFormRepresentative ω)
      (fun i => ((Γ i).component ω).val)
      (sourceNAFamily_component_bddAbove (sourceKahlerFormRepresentative ω) Γ hb ω)).max : EReal) = _
    rw [hmax]
    exact coe_csSup_eq_iSup _ (sourceNAFamily_component_bddAbove
      (sourceKahlerFormRepresentative ω) Γ hb ω)
  cases n with
  | zero =>
    simpa only [SGPT.NAPotential.BJ.SourceZeroModels.naPotentialAnAt_eq_of_dim_zero] using hcut
  | succ k =>
    rcases (mem_sourceDivisorialSet_iff f v).mp hv with hv0 | hvD
    · subst v
      simpa only [DivDict2.naPotentialAnAt_trivial (E := E)] using hcut
    · rcases hvD with ⟨D,t,ht,rfl⟩
      obtain ⟨p,hp⟩ := AlgebraicPrimeDictionary.algebraicPrimesRealized (m := k) E D
      rw [DivDict2.naPotentialAnAt_ordVal hp, BJPrep.naDivisorialTransform_uscSup_finiteJoin
        (sourceKahlerFormRepresentative ω) Γ hb ω p ht]
      calc
        (⨆ F : SourceTestCurveFiniteIndex I, BJPrep.naDivisorialTransform
          (SourceNAPotential.finiteJoin (sourceKahlerFormRepresentative ω) Γ F.1 F.2) ω p t) =
          ⨆ F : SourceTestCurveFiniteIndex I, F.1.sup' F.2
            (fun i => naPotentialAnAt (k+1) E (Γ i) ω (D.ordVal f t ht)) := by
          apply iSup_congr
          intro F
          rw [← DivDict2.naPotentialAnAt_ordVal hp,
            naPotentialAnAt_finiteJoin f (k+1) E b HM hm hθ]
        _ = _ := iSup_nonemptyFinite_sup' _

end SGPT.NAPotential.OperationComparison
