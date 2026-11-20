import SGPT.Projective.OkounkovOriginalPerturbMonotonicity
import SGPT.Projective.OkounkovOriginalPerturbGeometry
import SGPT.Projective.OkounkovOriginalCarrierBodyTransport

/-! SAME original rational perturbation bodies, arbitrary valuations and ACTUAL common powers, all dimensions.
Blueprint: okounkov-original-rational-perturb-monotonicity.tex. -/
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
local instance rationalPerturbMonoTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance rationalPerturbMonoCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance rationalPerturbMonoManifold [IsSeparated f] [QuasiCompact f] : IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n

/-- Genuine original common powers prove the actual arbitrary-valuation rational perturbation monotonicity. -/
theorem normalized_positivePerturb_partialBody_mono {L A : X.Modules}
    (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f n E L)
    (aA : LineBundleAtlas A) (P : SGPT.LineBundle.AmplePolarization f A)
    (K : SchemeLineBundleMetric f n E A)
    (hK : letI := E.isSeparated; letI := E.quasiCompact; (K.curvature aA).val.IsKahler)
    {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact; IsThetaPshPotential (H.curvature a).val φ)
    (v : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ)))) (hv : Function.Surjective v)
    (c : X) (hc : IsNonnegAt v c)
    (q₁ p₁ q₂ p₂ : ℕ) (hq₁ : 0<q₁) (hp₁ : 0<p₁) (hq₂ : 0<q₂) (hp₂ : 0<p₂)
    (hle : p₁*q₂≤p₂*q₁) :
    letI := E.isSeparated
    letI := E.quasiCompact
    ∃ (hK₁c : IsCompact (okounkovBody v c (OkoNS.perturbAtlas a aA q₁ p₁)))
      (hK₁v : Convex ℝ (okounkovBody v c (OkoNS.perturbAtlas a aA q₁ p₁)))
      (hK₂c : IsCompact (okounkovBody v c (OkoNS.perturbAtlas a aA q₂ p₂)))
      (hK₂v : Convex ℝ (okounkovBody v c (OkoNS.perturbAtlas a aA q₂ p₂))),
      (q₁:ℝ)⁻¹ • ValGen.partialBody f n E v c (OkoNS.perturbAtlas a aA q₁ p₁)
        (SGPT.GAGA.OkoClose.coneOver _ hK₁c hK₁v) (fun x => (q₁:EReal)*φ x) ⊆
      (q₂:ℝ)⁻¹ • ValGen.partialBody f n E v c (OkoNS.perturbAtlas a aA q₂ p₂)
        (SGPT.GAGA.OkoClose.coneOver _ hK₂c hK₂v) (fun x => (q₂:EReal)*φ x) := by
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
  obtain ⟨d,hd,hraw⟩ := OriginalPerturbMonotonicity.exists_ample_multiple_perturb_multiplier_inclusions f n E aA P
  let r₁ := q₂*d
  let r₂ := q₁*d
  let Q := q₁*r₁
  let m := p₂*q₁-p₁*q₂
  have hr₁ : 0<r₁ := Nat.mul_pos hq₂ hd
  have hr₂ : 0<r₂ := Nat.mul_pos hq₁ hd
  have hQ : 0<Q := Nat.mul_pos hq₁ hr₁
  have hQ₂ : q₂*r₂=Q := by dsimp [Q,r₁,r₂]; ring
  have hnum : p₁*r₁+d*m=p₂*r₂ := by
    have hh := congrArg (fun k : ℕ => d*k) (Nat.sub_add_cancel hle)
    dsimp only [r₁,r₂,m]
    nlinarith only [hh]
  have hw₁ : (fun x => (r₁:EReal)*ψ q₁ x)=ψ Q := by
    funext x
    change ((r₁:ℝ):EReal)*(((q₁:ℝ):EReal)*φ x)=((Q:ℝ):EReal)*φ x
    have he : (r₁:ℝ)*(q₁:ℝ)=(Q:ℝ) := by dsimp [Q]; push_cast; ring
    rw [←mul_assoc,←EReal.coe_mul,he]
  have hw₂ : (fun x => (r₂:EReal)*ψ q₂ x)=ψ Q := by
    funext x
    change ((r₂:ℝ):EReal)*(((q₂:ℝ):EReal)*φ x)=((Q:ℝ):EReal)*φ x
    have he : (r₂:ℝ)*(q₂:ℝ)=(Q:ℝ) := by rw [←hQ₂]; push_cast; ring
    rw [←mul_assoc,←EReal.coe_mul,he]
  obtain ⟨hK₁c,hK₁v,hsub₁,hΓ₁⟩ := hdata q₁ p₁ hq₁ hp₁
  obtain ⟨hK₂c,hK₂v,hsub₂,hΓ₂⟩ := hdata q₂ p₂ hq₂ hp₂
  obtain ⟨hKlc,hKlv,hsubl,hΓl⟩ := hdata Q (p₁*r₁) hQ (Nat.mul_pos hp₁ hr₁)
  obtain ⟨hKhc,hKhv,hsubh,hΓh⟩ := hdata Q (p₂*r₂) hQ (Nat.mul_pos hp₂ hr₂)
  let C₁ := SGPT.GAGA.OkoClose.coneOver _ hK₁c hK₁v
  let C₂ := SGPT.GAGA.OkoClose.coneOver _ hK₂c hK₂v
  let D₁ := SGPT.GAGA.OkoClose.coneOver _ hKlc hKlv
  let D₂ := SGPT.GAGA.OkoClose.coneOver _ hKhc hKhv
  have hrawComp : AlgebraicValuation.multiplierSectionSet f n E v c (b Q (p₁*r₁)) (ψ Q) ⊆
      AlgebraicValuation.multiplierSectionSet f n E v c (b Q (p₂*r₂)) (ψ Q) := by
    have hh := hraw a Q (p₁*r₁) m (b Q (p₁*r₁)) (b Q (p₁*r₁+d*m)) v c hc (ψ Q)
    dsimp only [b] at hh ⊢
    rw [hnum] at hh
    exact hh
  have hBI : ValGen.partialBody f n E v c (b Q (p₁*r₁)) D₁ (ψ Q) ⊆
      ValGen.partialBody f n E v c (b Q (p₂*r₂)) D₂ (ψ Q) := by
    rw [ValGen.partialBody_eq _ _ hsubl hΓl,ValGen.partialBody_eq _ _ hsubh hΓh]
    exact CommonConeMonotonicity.bodyExtension_mono_of_carrier_subset ⟨⟨_,hsubl⟩,hΓl⟩ ⟨⟨_,hsubh⟩,hΓh⟩ hrawComp
  have hscale₁ : ValGen.partialBody f n E v c (b Q (p₁*r₁)) D₁ (ψ Q)=
      (r₁:ℝ) • ValGen.partialBody f n E v c (b q₁ p₁) C₁ (ψ q₁) := by
    have hp := OriginalCarrierBodyTransport.partialBody_power_perturbRegroup_eq f n E a aA q₁ p₁ r₁ hr₁
      (b q₁ p₁) (b (q₁*r₁) (p₁*r₁)) v hc (ψ q₁) C₁ D₁ hsub₁ hΓ₁
      (by simpa only [hw₁] using hsubl) (by simpa only [hw₁] using hΓl)
    simpa only [hw₁] using hp
  have hscale₂ : ValGen.partialBody f n E v c (b Q (p₂*r₂)) D₂ (ψ Q)=
      (r₂:ℝ) • ValGen.partialBody f n E v c (b q₂ p₂) C₂ (ψ q₂) := by
    have hs : AlgebraicValuation.multiplierSectionSet f n E v c (b (q₂*r₂) (p₂*r₂))
        (fun x => (r₂:EReal)*ψ q₂ x) ⊆ (latticePoints D₂.cone : Set ((Fin n → ℤ)×ℤ)) := by
      rw [hQ₂,hw₂]
      exact hsubh
    have hG : (⟨_,hs⟩ : ConeSubset D₂) ∈ almostSemigroupLocus D₂ := by
      convert hΓh using 1
      apply Subtype.ext
      change AlgebraicValuation.multiplierSectionSet f n E v c (b (q₂*r₂) (p₂*r₂))
        (fun x => (r₂:EReal)*ψ q₂ x)=AlgebraicValuation.multiplierSectionSet f n E v c (b Q (p₂*r₂)) (ψ Q)
      rw [hQ₂,hw₂]
    have hp := OriginalCarrierBodyTransport.partialBody_power_perturbRegroup_eq f n E a aA q₂ p₂ r₂ hr₂
      (b q₂ p₂) (b (q₂*r₂) (p₂*r₂)) v hc (ψ q₂) C₂ D₂ hsub₂ hΓ₂ hs hG
    rw [hQ₂,hw₂] at hp
    exact hp
  have hinc : (Q:ℝ)⁻¹ • ValGen.partialBody f n E v c (b Q (p₁*r₁)) D₁ (ψ Q) ⊆
      (Q:ℝ)⁻¹ • ValGen.partialBody f n E v c (b Q (p₂*r₂)) D₂ (ψ Q) := by
    change (fun x => (Q:ℝ)⁻¹ • x) '' _ ⊆ (fun x => (Q:ℝ)⁻¹ • x) '' _
    exact Set.image_mono hBI
  have hq₁R : (q₁:ℝ)≠0 := by exact_mod_cast hq₁.ne'
  have hq₂R : (q₂:ℝ)≠0 := by exact_mod_cast hq₂.ne'
  have hr₁R : (r₁:ℝ)≠0 := by exact_mod_cast hr₁.ne'
  have hr₂R : (r₂:ℝ)≠0 := by exact_mod_cast hr₂.ne'
  have hs₁ : (Q:ℝ)⁻¹*(r₁:ℝ)=(q₁:ℝ)⁻¹ := by dsimp only [Q]; push_cast; field_simp
  have hs₂ : (Q:ℝ)⁻¹*(r₂:ℝ)=(q₂:ℝ)⁻¹ := by rw [←hQ₂]; push_cast; field_simp
  rw [hscale₁,hscale₂,smul_smul,smul_smul,hs₁,hs₂] at hinc
  exact ⟨hK₁c,hK₁v,hK₂c,hK₂v,hinc⟩
end SGPT.Okounkov.OriginalBook
