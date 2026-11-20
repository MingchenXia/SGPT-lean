import SGPT.Projective.OkounkovOriginalPerturbGeometry
import SGPT.Projective.OkounkovOriginalCarrierBodyTransport

/-! SAME original positive-I-volume partial body inside EVERY true positive rational perturbation, all dimensions.
Blueprint: okounkov-original-base-perturb-inclusion.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Okounkov.OriginalBook
open Set Filter MeasureTheory CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Okounkov.AlgebraicValuation SGPT.AlmostSemigroup SGPT.AlmostSemigroup.Class
open scoped Pointwise
variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
    [SmoothOfRelativeDimension n f] (E : ClosedProjectiveEmbedding f) [Nonempty (SchemeComplexPoint f)]
local instance basePerturbTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance basePerturbCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance basePerturbManifold [IsSeparated f] [QuasiCompact f] : IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n

/-- The genuine original base body lies in every normalized original positive perturbation, actual ORIGINAL I-volume domain. -/
theorem partialBody_subset_normalized_positivePerturb {L A : X.Modules}
    (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f n E L)
    (aA : LineBundleAtlas A) (P : SGPT.LineBundle.AmplePolarization f A)
    (K : SchemeLineBundleMetric f n E A)
    (hK : letI := E.isSeparated; letI := E.quasiCompact; (K.curvature aA).val.IsKahler)
    {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact; IsThetaPshPotential (H.curvature a).val φ)
    (hpos : letI := E.isSeparated; letI := E.quasiCompact;
      letI : MeasurableSpace (SchemeComplexPoint f) := borel _;
      haveI : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩;
      haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact;
      0 < iVolume (H.curvature a) (LocalPotentials.closedRealOneOne_hasLocalPotentials _) φ hφ)
    (v : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ)))) (hv : Function.Surjective v)
    (c : X) (hc : IsNonnegAt v c) (q p : ℕ) (hq : 0<q) (hp : 0<p) :
    letI := E.isSeparated
    letI := E.quasiCompact
    ∃ (hKc : IsCompact (okounkovBody v c a)) (hKv : Convex ℝ (okounkovBody v c a))
      (hKpc : IsCompact (okounkovBody v c (OkoNS.perturbAtlas a aA q p)))
      (hKpv : Convex ℝ (okounkovBody v c (OkoNS.perturbAtlas a aA q p))),
      ValGen.partialBody f n E v c a (SGPT.GAGA.OkoClose.coneOver _ hKc hKv) φ ⊆
      (q:ℝ)⁻¹ • ValGen.partialBody f n E v c (OkoNS.perturbAtlas a aA q p)
        (SGPT.GAGA.OkoClose.coneOver _ hKpc hKpv) (fun x => (q:EReal)*φ x) := by
  let := E.isSeparated
  let := E.quasiCompact
  let : MeasurableSpace (SchemeComplexPoint f) := borel _
  have : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  let b (u t : ℕ) := OkoNS.perturbAtlas a aA u t
  let ψ (u : ℕ) := fun x => (u:EReal)*φ x
  have hdata (u t : ℕ) (hu : 0<u) (ht : 0<t) :
      ∃ (hKc : IsCompact (okounkovBody v c (b u t))) (hKv : Convex ℝ (okounkovBody v c (b u t)))
        (hsub : AlgebraicValuation.multiplierSectionSet f n E v c (b u t) (ψ u) ⊆
          (latticePoints (SGPT.GAGA.OkoClose.coneOver _ hKc hKv).cone : Set ((Fin n → ℤ)×ℤ))),
        (⟨_,hsub⟩ : ConeSubset (SGPT.GAGA.OkoClose.coneOver _ hKc hKv)) ∈
          almostSemigroupLocus (SGPT.GAGA.OkoClose.coneOver _ hKc hKv) := by
    let HM := originalPerturbMetric f n E a H aA K u t
    obtain ⟨hcur,hbig⟩ := original_positivePerturbation_kahler_and_big f n E a H aA K hK hφ u t hu ht
    have hθ := PartialBody.isThetaPshPotential_of_isKahlerCurrentPotential hcur
    have hpos := original_iVolume_pos_of_kahler_allDimensions f n E (b u t) HM hcur
    obtain ⟨hKc,hKv,hsub,hΓ,hvol,hbody,hvolume⟩ :=
      multiplierSectionSet_mem_ownBody_almostSemigroupLocus_allDimensions f n E (b u t) HM hbig v hv c hθ hpos
    exact ⟨hKc,hKv,hsub,hΓ⟩
  have hbig := original_isBig_of_positive_iVolume_allDimensions f n E a H hφ hpos
  obtain ⟨hKc,hKv,hsub,hΓ,hvol,hbody,hvolume⟩ :=
    multiplierSectionSet_mem_ownBody_almostSemigroupLocus_allDimensions f n E a H hbig v hv c hφ hpos
  let C := SGPT.GAGA.OkoClose.coneOver _ hKc hKv
  obtain ⟨d,hd,hraw⟩ := OriginalTensorMultiplier.exists_ample_multiple_multiplier_inclusions f n E aA P
  let Q := q*d
  have hQ : 0<Q := Nat.mul_pos hq hd
  have hpCommon : 0<d*p := Nat.mul_pos hd hp
  have hpd : p*d=d*p := Nat.mul_comm _ _
  have hw : (fun x => (d:EReal)*ψ q x)=ψ Q := by
    funext x
    change ((d:ℝ):EReal)*(((q:ℝ):EReal)*φ x)=((Q:ℝ):EReal)*φ x
    have he : (d:ℝ)*(q:ℝ)=(Q:ℝ) := by dsimp [Q]; push_cast; ring
    rw [←mul_assoc,←EReal.coe_mul,he]
  obtain ⟨hKpc,hKpv,hsubp,hΓp⟩ := hdata q p hq hp
  obtain ⟨hKdc,hKdv,hsubd,hΓd⟩ := hdata Q (d*p) hQ hpCommon
  let Cp := SGPT.GAGA.OkoClose.coneOver _ hKpc hKpv
  let D := SGPT.GAGA.OkoClose.coneOver _ hKdc hKdv
  have hres := ValGen2.partialBody_tensorPower_eq_smul f n E v hc a hQ (a.tensorPower Q) φ hsub hΓ
  obtain ⟨hsubPower,hΓPower⟩ := hres.1
  have hrawComp := hraw p (a.tensorPower Q) (b Q (d*p)) v c hc (ψ Q)
  have hBI : ValGen.partialBody f n E v c (a.tensorPower Q) (ValGen2.veroneseCone C hQ) (ψ Q) ⊆
      ValGen.partialBody f n E v c (b Q (d*p)) D (ψ Q) := by
    rw [ValGen.partialBody_eq _ _ hsubPower hΓPower,ValGen.partialBody_eq _ _ hsubd hΓd]
    exact CommonConeMonotonicity.bodyExtension_mono_of_carrier_subset ⟨⟨_,hsubPower⟩,hΓPower⟩ ⟨⟨_,hsubd⟩,hΓd⟩ hrawComp
  have hs : AlgebraicValuation.multiplierSectionSet f n E v c (b (q*d) (p*d))
      (fun x => (d:EReal)*ψ q x) ⊆ (latticePoints D.cone : Set ((Fin n → ℤ)×ℤ)) := by
    rw [hpd,hw]
    exact hsubd
  have hG : (⟨_,hs⟩ : ConeSubset D) ∈ almostSemigroupLocus D := by
    convert hΓd using 1
    apply Subtype.ext
    change AlgebraicValuation.multiplierSectionSet f n E v c (b (q*d) (p*d))
      (fun x => (d:EReal)*ψ q x)=AlgebraicValuation.multiplierSectionSet f n E v c (b Q (d*p)) (ψ Q)
    rw [hpd,hw]
  have hscale := OriginalCarrierBodyTransport.partialBody_power_perturbRegroup_eq f n E a aA q p d hd
    (b q p) (b (q*d) (p*d)) v hc (ψ q) Cp D hsubp hΓp hs hG
  rw [hpd,hw] at hscale
  have hinc : (Q:ℝ)⁻¹ • ValGen.partialBody f n E v c (a.tensorPower Q) (ValGen2.veroneseCone C hQ) (ψ Q) ⊆
      (Q:ℝ)⁻¹ • ValGen.partialBody f n E v c (b Q (d*p)) D (ψ Q) := by
    change (fun x => (Q:ℝ)⁻¹ • x) '' _ ⊆ (fun x => (Q:ℝ)⁻¹ • x) '' _
    exact Set.image_mono hBI
  have hQR : (Q:ℝ)≠0 := by exact_mod_cast hQ.ne'
  have hqR : (q:ℝ)≠0 := by exact_mod_cast hq.ne'
  have hdR : (d:ℝ)≠0 := by exact_mod_cast hd.ne'
  have hscalar : (Q:ℝ)⁻¹*(d:ℝ)=(q:ℝ)⁻¹ := by dsimp only [Q]; push_cast; field_simp
  rw [hres.2,hscale,smul_smul,smul_smul,inv_mul_cancel₀ hQR,one_smul,hscalar] at hinc
  exact ⟨hKc,hKv,hKpc,hKpv,hinc⟩
end SGPT.Okounkov.OriginalBook
