import SGPT.Projective.OkounkovOriginalBookVolume
import SGPT.Okounkov.QwOkoCurrent

/-! Actual whole-current equality manufactures SAME original class, all multiplier ideals, I-volume.
Blueprint: okounkov-original-current-dictionary.tex. No current/body comparison certificate input. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Okounkov.OriginalCurrentDictionary
open Set Filter MeasureTheory CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open NaturalThetaPshGeometricCurrent
open scoped Topology ENNReal
variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ))
  {m : ℕ} [SmoothOfRelativeDimension (m+1) f] (E : ClosedProjectiveEmbedding f)
  [Nonempty (SchemeComplexPoint f)]
local instance currentDictionaryTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance currentDictionaryCharts : ChartedSpace (ComplexModel (m+1)) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f (m+1)
local instance currentDictionaryManifold [IsSeparated f] [QuasiCompact f] :
    IsComplexManifold (m+1) (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f (m+1)

/-- SAME actual whole currents produce actual original class, EVERY multiplier ideal and original I-volume equality. -/
theorem original_class_ideals_iVolume_of_current_eq {L L' : X.Modules}
    (a : LineBundleAtlas L) (b : LineBundleAtlas L')
    (H : SchemeLineBundleMetric f (m+1) E L) (K : SchemeLineBundleMetric f (m+1) E L')
    {φ ψ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact; IsThetaPshPotential (H.curvature a).val φ)
    (hψ : letI := E.isSeparated; letI := E.quasiCompact; IsThetaPshPotential (K.curvature b).val ψ)
    (heq : letI := E.isSeparated; letI := E.quasiCompact;
      thetaPotentialCurrent (H.curvature a).val φ hφ = thetaPotentialCurrent (K.curvature b).val ψ hψ) :
    letI := E.isSeparated
    letI := E.quasiCompact
    letI : MeasurableSpace (SchemeComplexPoint f) := borel _
    haveI : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
    haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    RealBottChern.ofRepresentative (H.curvature a) = RealBottChern.ofRepresentative (K.curvature b) ∧
    (∀ d : ℝ, multiplierIdeal (n:=m+1) d φ = multiplierIdeal (n:=m+1) d ψ) ∧
    iVolume (H.curvature a) (LocalPotentials.closedRealOneOne_hasLocalPotentials _) φ hφ =
      iVolume (K.curvature b) (LocalPotentials.closedRealOneOne_hasLocalPotentials _) ψ hψ := by
  let := E.isSeparated
  let := E.quasiCompact
  let : MeasurableSpace (SchemeComplexPoint f) := borel _
  have : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  obtain ⟨g,hg,hcoeff,hweights⟩ := QwOko.exists_chartSmooth_of_thetaPotentialCurrent_eq hφ hψ heq
  have hclass : RealBottChern.ofRepresentative (H.curvature a) = RealBottChern.ofRepresentative (K.curvature b) :=
    (RealBottChern.ofRepresentative_eq_iff _ _).mpr ⟨g,hg,hcoeff⟩
  obtain ⟨B,hB⟩ : ∃ B : ℝ, ∀ x, |g x|≤B := by
    have hcont : Continuous (fun x => |g x|) := (ProductTestForms.ChartSmooth.continuous hg).abs
    obtain ⟨x,-,hx⟩ := isCompact_univ.exists_isMaxOn univ_nonempty hcont.continuousOn
    exact ⟨_,fun y => hx (mem_univ y)⟩
  have hφeq : φ = fun x => ψ x + (g x:EReal) := funext hweights
  have hI : ∀ d : ℝ, multiplierIdeal (n:=m+1) d φ = multiplierIdeal (n:=m+1) d ψ := by
    intro d
    rw [hφeq]
    exact SGPT.Okounkov.multiplierIdeal_add_bounded_smooth hψ.1.quasiPlurisubharmonic hg hB d
  have hψeq : ψ = fun x => φ x - (g x:EReal) := by
    funext x
    rw [hweights x,EReal.add_sub_cancel_right]
  obtain ⟨Y,hY⟩ := OriginalBook.exists_original_smoothFlag_allDimensions f (m+1) E
  let F := schemeFubiniStudyOriginalFlagGeometry f (m+1) E Y hY
  have hbody0 := PartialBody.generalPartialBody_sub_smooth (F:=F) hg hcoeff hφ
  have hbody : PartialBody.generalPartialBody F (K.curvature b) ψ =
      PartialBody.generalPartialBody F (H.curvature a) φ :=
    (congrArg (fun χ : SchemeComplexPoint f → EReal => PartialBody.generalPartialBody F (K.curvature b) χ)
      hψeq).trans hbody0
  have hvol :
      iVolume (K.curvature b) (LocalPotentials.closedRealOneOne_hasLocalPotentials _) ψ hψ /
          ((m+1).factorial:ℝ≥0∞) =
        iVolume (H.curvature a) (LocalPotentials.closedRealOneOne_hasLocalPotentials _) φ hφ /
          ((m+1).factorial:ℝ≥0∞) :=
    (PartialBody.volume_generalPartialBody_uncond (F:=F) hψ).symm.trans
      ((congrArg volume hbody).trans (PartialBody.volume_generalPartialBody_uncond (F:=F) hφ))
  have hf0 : ((m+1).factorial:ℝ≥0∞)≠0 := by exact_mod_cast Nat.factorial_ne_zero (m+1)
  have hft : ((m+1).factorial:ℝ≥0∞)≠⊤ := ENNReal.natCast_ne_top _
  have hmass := congrArg (fun z : ℝ≥0∞ => z*((m+1).factorial:ℝ≥0∞)) hvol
  simp only [ENNReal.div_mul_cancel hf0 hft] at hmass
  exact ⟨hclass,hI,hmass.symm⟩

end SGPT.Okounkov.OriginalCurrentDictionary
