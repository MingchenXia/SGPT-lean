import SGPT.Projective.OkounkovOriginalPerturbGeometry
import SGPT.PSH.NativeIVolumeScaling

/-! Actual original own-body rational normalization volume = EXISTING native ORIGINAL perturbed I-volume, no flag identification.
Blueprint: okounkov-original-perturb-volume.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Okounkov.OriginalBook
open Set Filter MeasureTheory CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Okounkov.AlgebraicValuation SGPT.Okounkov.TranscendentalCore
open scoped Pointwise
variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
    [SmoothOfRelativeDimension n f] (E : ClosedProjectiveEmbedding f) [Nonempty (SchemeComplexPoint f)]
local instance perturbVolumeTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance perturbVolumeCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance perturbVolumeManifold [IsSeparated f] [QuasiCompact f] : IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n

/-- The LITERAL normalized original positive perturbation body has the true native ORIGINAL I-volume, every dimension. -/
theorem normalized_positivePerturb_partialBody_volume {L A : X.Modules}
    (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f n E L)
    (aA : LineBundleAtlas A) (K : SchemeLineBundleMetric f n E A)
    (hK : letI := E.isSeparated; letI := E.quasiCompact; (K.curvature aA).val.IsKahler)
    {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact; IsThetaPshPotential (H.curvature a).val φ)
    (v : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ)))) (hv : Function.Surjective v)
    (c : X) (q p : ℕ) (hq : 0<q) (hp : 0<p) :
    letI := E.isSeparated
    letI := E.quasiCompact
    letI : MeasurableSpace (SchemeComplexPoint f) := borel _
    haveI : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
    haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    ∃ (hφδ : IsThetaPshPotential (H.curvature a+((p:ℝ)/(q:ℝ))•K.curvature aA).val φ)
      (hKc : IsCompact (okounkovBody v c (OkoNS.perturbAtlas a aA q p)))
      (hKv : Convex ℝ (okounkovBody v c (OkoNS.perturbAtlas a aA q p))),
      volume.real ((q:ℝ)⁻¹ • ValGen.partialBody f n E v c (OkoNS.perturbAtlas a aA q p)
        (SGPT.GAGA.OkoClose.coneOver _ hKc hKv) (fun x => (q:EReal)*φ x)) =
      (iVolume (H.curvature a+((p:ℝ)/(q:ℝ))•K.curvature aA)
        (LocalPotentials.closedRealOneOne_hasLocalPotentials _) φ hφδ).toReal / (n.factorial:ℝ) := by
  let := E.isSeparated
  let := E.quasiCompact
  let : MeasurableSpace (SchemeComplexPoint f) := borel _
  have : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  have : ConnectedSpace (SchemeComplexPoint f) := SGPT.GAGA.OkoClose.connectedSpace_of_isIntegral f E n
  let κ : KahlerBackground n (SchemeComplexPoint f) := ⟨K.curvature aA,hK⟩
  let θδ := H.curvature a+((p:ℝ)/(q:ℝ))•K.curvature aA
  let b := OkoNS.perturbAtlas a aA q p
  let HM := originalPerturbMetric f n E a H aA K q p
  have hqR : (0:ℝ)<q := by exact_mod_cast hq
  have hpR : (0:ℝ)<p := by exact_mod_cast hp
  have hφδ : IsThetaPshPotential θδ.val φ := LocalPotentials.isThetaPshPotential_add_of_semipositive hφ
    (KahlerDomination.isSemipositive_smul κ.isSemipositive (div_nonneg hpR.le hqR.le))
  obtain ⟨hcur,hbig⟩ := original_positivePerturbation_kahler_and_big f n E a H aA K hK hφ q p hq hp
  have hφM := PartialBody.isThetaPshPotential_of_isKahlerCurrentPotential hcur
  have hposM := original_iVolume_pos_of_kahler_allDimensions f n E b HM hcur
  have heq : (q:ℝ)•θδ=(q:ℝ)•H.curvature a+(p:ℝ)•K.curvature aA := by
    dsimp only [θδ]
    have hqp : (q:ℝ)*((p:ℝ)/(q:ℝ))=(p:ℝ) := by field_simp [hqR.ne']
    rw [smul_add,smul_smul,hqp]
  have hgeo : (HM.curvature b).val.GeometricallyEq ((q:ℝ)•θδ).val := by
    rw [heq]
    exact originalPerturbMetric_curvature f n E a H aA K q p
  have hmass := SGPT.GAGA.H0L.iVolume_congr_geometricallyEq hgeo
    (LocalPotentials.closedRealOneOne_hasLocalPotentials _) (LocalPotentials.closedRealOneOne_hasLocalPotentials _)
    (fun x => (q:EReal)*φ x) hφM (isThetaPshPotential_nonneg_smul hφδ hqR.le)
  have hscale := SGPT.PSH.VariableComplexAtlas.nativeIVolume_positive_smul κ hφδ hqR
  have hM : iVolume (HM.curvature b) (LocalPotentials.closedRealOneOne_hasLocalPotentials _)
      (fun x => (q:EReal)*φ x) hφM =
      ENNReal.ofReal (q:ℝ)^n * iVolume θδ (LocalPotentials.closedRealOneOne_hasLocalPotentials _) φ hφδ :=
    hmass.trans hscale
  obtain ⟨hKc,hKv,hsub,hΓ,hvol,hbody,hvolume⟩ :=
    multiplierSectionSet_mem_ownBody_almostSemigroupLocus_allDimensions f n E b HM hbig v hv c hφM hposM
  refine ⟨hφδ,hKc,hKv,?_⟩
  rw [measureReal_def,Measure.addHaar_smul_of_nonneg volume (inv_nonneg.mpr hqR.le),finrank_euclideanSpace,Fintype.card_fin,
    hvolume,hM,ENNReal.toReal_mul,ENNReal.toReal_ofReal (pow_nonneg (inv_nonneg.mpr hqR.le) _),
    ENNReal.toReal_div,ENNReal.toReal_mul,ENNReal.toReal_pow,ENNReal.toReal_ofReal hqR.le,ENNReal.toReal_natCast]
  have hf : (n.factorial:ℝ)≠0 := by exact_mod_cast Nat.factorial_ne_zero n
  field_simp [hqR.ne',hf]
  rw [one_div,←mul_pow,inv_mul_cancel₀ hqR.ne',one_pow,one_mul]
end SGPT.Okounkov.OriginalBook
