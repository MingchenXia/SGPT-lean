import SGPT.Trace.BertiniNativeComplexCoefficients
import SGPT.Trace.BertiniLocalCircleMEP
import SGPT.Trace.BertiniNativeFiniteCoefficientEnergy
import SGPT.Trace.BertiniNativeAmbientCoefficientDatum
import SGPT.Trace.BertiniUniversalSimultaneousSharp

/-! Literal original pencils inside an actual original quotient-frame domain.
The full same-circle producer is appended after the guarded actual energy specialization. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.BertiniFamilyCanonical
open Set Filter Metric MeasureTheory TensorProduct
open scoped Topology Manifold ContDiff ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.NativeHermitianMetric
open SGPT.Bergman.CompactHolomorphicSectionsDraft SGPT.Bergman.MultiplierSectionsDraft
open SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle
open SGPT.Trace.BertiniPencilFamily SGPT.Trace.BertiniDiscExhaustion SGPT.Trace.OptimalNativeNormalBackground
open SGPT.PSH.DirImg2
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Trace.Bertini SGPT.Trace.BertiniNativeNormalKernel

variable {N : ℕ}

def nativeQuotientPencilDomain (B : TopologicalSpace.Opens (ComplexModel N)) (a v : ComplexModel N) :
    TopologicalSpace.Opens (ComplexModel 1) :=
  ⟨{t | a-t 0 • v ∈ B},B.isOpen.preimage
    (continuous_const.sub (modelOneScalarEquiv.continuous.smul continuous_const))⟩

theorem nativeQuotientPencilDomain_zero (B : TopologicalSpace.Opens (ComplexModel N))
    {a : ComplexModel N} (ha : a ∈ B) (v : ComplexModel N) :
    (0 : ComplexModel 1) ∈ nativeQuotientPencilDomain B a v := by
  change a-(0 : ComplexModel 1) 0 • v ∈ B
  simpa only [PiLp.zero_apply,zero_smul,sub_zero] using ha

def nativeQuotientPencilPoint (B : TopologicalSpace.Opens (ComplexModel N)) (a v : ComplexModel N)
    (t : nativeQuotientPencilDomain B a v) : B :=
  ⟨a-t.val 0 • v,t.property⟩

theorem nativeQuotientPencilPoint_apply (B : TopologicalSpace.Opens (ComplexModel N))
    (a v : ComplexModel N) (t : nativeQuotientPencilDomain B a v) :
    (nativeQuotientPencilPoint B a v t).val = a-t.val 0 • v := rfl

theorem contMDiff_nativeQuotientPencilPoint (B : TopologicalSpace.Opens (ComplexModel N))
    (a v : ComplexModel N) :
    ContMDiff 𝓘(ℂ,ComplexModel 1) 𝓘(ℂ,ComplexModel N) ∞ (nativeQuotientPencilPoint B a v) := by
  apply (ContMDiff.subtypeVal_comp_iff B _).mp
  exact (contMDiff_const.sub
    (modelOneScalarEquiv.toContinuousLinearEquiv.toContinuousLinearMap.contMDiff.smul contMDiff_const)).comp
      contMDiff_subtype_val

theorem nativeQuotientPencilDomain_smooth {d : ℕ} {X : Type} [TopologicalSpace X]
    [ChartedSpace (ComplexModel (d+1)) X] [IsComplexManifold (d+1) X]
    (p : ContMDiffMap 𝓘(ℂ,ComplexModel (d+1)) 𝓘(ℂ,ComplexModel N) X (ComplexProjectiveSpace N) ∞)
    (i : Fin (N+1)) (B : TopologicalSpace.Opens (ComplexModel N))
    (hsB : ∀ zeta : B, IsSmoothHypersurfaceMember (d+1) p (affinePoint i zeta.val))
    (a v : ComplexModel N) (t : nativeQuotientPencilDomain B a v) :
    IsSmoothHypersurfaceMember (d+1) p (affinePoint i (a-t.val 0 • v)) :=
  hsB (nativeQuotientPencilPoint B a v t)


variable {d : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (d+1)) X] [IsComplexManifold (d+1) X] [CompactSpace X]
  (p : ContMDiffMap 𝓘(ℂ,ComplexModel (d+1)) 𝓘(ℂ,ComplexModel N) X (ComplexProjectiveSpace N) ∞)

private theorem native_pencil_circle_extensions_from_actual_producers
    (i : Fin (N+1)) (a v : ComplexModel N) (U : TopologicalSpace.Opens (ComplexModel 1))
    (hsm : ∀ t : U, IsSmoothHypersurfaceMember (d+1) p (affinePoint i (a-t.val 0 • v)))
    (h0 : (0 : ComplexModel 1) ∈ U)
    (L : HermitianHolomorphicLineBundle.{0,0} (d+1) X)
    {φ : X → EReal} (hφ : IsGlobalQuasiPshPotential (n := d+1) φ)
    (B : TopologicalSpace.Opens (ComplexModel N))
    (hsB : ∀ zeta : B, IsSmoothHypersurfaceMember (d+1) p (affinePoint i zeta.val))
    (hUB : ∀ t : U, a-t.val 0 • v ∈ B)
    (r : ℕ) (S : Fin r → nativeMultiplierSections
      (tensor (tensor (nativeCanonicalBundle (n := d+1) (X := X)) L) (nativeBertiniHyperplaneBundle p)) φ)
    (hcoef :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    let T := fun j => nativeMultiplierFamilyPhysicalSectionMap p i a v U hsm L hφ (S j)
    ∃ (W : TopologicalSpace.Opens (ComplexModel 1)) (hWU : W ≤ U), (0 : ComplexModel 1) ∈ W ∧
      ∀ (V : TopologicalSpace.Opens (ComplexModel 1)) (hVW : V ≤ W),
      let hVU := hVW.trans hWU
      let hsV : ∀ t : V, IsSmoothHypersurfaceMember (d+1) p (affinePoint i (a-t.val 0 • v)) :=
        familyBaseRestrictedSmoothness p i a v U V hVU hsm
      letI := familyChartedSpace p i a v V p.contMDiff hsV
      letI := isComplexManifold_family p i a v V p.contMDiff hsV
      ∃ C : HolomorphicSections (n := d+1) (familyNativePhysicalModel p i a v V hsV L).Fiber →ₗ[ℂ]
          (V → Fin r → ℂ),
        (∀ F, ContMDiff 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, Fin r → ℂ) ∞ (C F)) ∧
        (∀ (c : Fin r → ℂ) (t : V),
          C (familyPhysicalBaseRestriction p i a v U V hVU hsm L (∑ j, c j • T j)) t = c) ∧
        (∀ (F : HolomorphicSections (n := d+1) (familyNativePhysicalModel p i a v V hsV L).Fiber) (t : V),
          nativeBertiniPhysicalQuotientHodgeEnergy p i (a-t.val 0 • v) (hsV t) L hφ
            (∑ j, (C F t) j • (nativeMultiplierSectionMap
              (tensor (nativeCanonicalBundle (n := d+1) (X := X)) L) (nativeBertiniHyperplaneBundle p)
              hφ (nativeBertiniAffineSection p i (a-t.val 0 • v))).range.mkQ (S j)) ≤
            familyNativeMemberHodgeEnergy p i a v V hsV L φ t F) ∧
        ∀ (F : HolomorphicSections (n := d+1) (familyNativePhysicalModel p i a v V hsV L).Fiber)
          (t : V) (c : Fin r → ℂ),
          (∀ q : familyIncidence p i a v V, q.val.1.val = t.val →
            F q = ∑ j, c j • T j (familyBaseInclusion p i a v U V hVU q)) → C F t = c)
    (hsharp :
      letI := familyChartedSpace p i a v U p.contMDiff hsm
      letI := isComplexManifold_family p i a v U p.contMDiff hsm
      ∃ r : ℝ, 0 < r ∧ Metric.closedBall (0 : ComplexModel 1) r ⊆ U ∧
        ∀ ρ : ℝ, 0 < ρ → ρ ≤ r / 4 → ∃ hVU : parameterDisc ρ ≤ U,
        letI := familyChartedSpace p i a v (parameterDisc ρ) p.contMDiff
          (familyBaseRestrictedSmoothness p i a v U (parameterDisc ρ) hVU hsm)
        letI := isComplexManifold_family p i a v (parameterDisc ρ) p.contMDiff
          (familyBaseRestrictedSmoothness p i a v U (parameterDisc ρ) hVU hsm)
        ∀ ρ' : ℝ, 0 < ρ' → ρ' < ρ → ∀ η : ℝ, 0 < η →
        ∀ (m : ℕ) (T : Fin m → HolomorphicSections (n := d + 1)
          (tensor (tensor (nativeCanonicalBundle (n := d + 1) (X := X))
            (nativeBertiniHyperplaneBundle p)) L).Fiber),
          (∀ j, nativeBertiniAdjunctionHodgeEnergy p i (a - (0 : ComplexModel 1) 0 • v)
            (hsm ⟨0,h0⟩) L φ (T j) < ⊤) →
        ∃ S : Fin m → HolomorphicSections (n := d + 1)
          (familyNativePhysicalModel p i a v (parameterDisc ρ)
            (familyBaseRestrictedSmoothness p i a v U (parameterDisc ρ) hVU hsm) L).Fiber,
          (∀ j q, normalizedPencilNormal p i a v (parameterDisc ρ) ρ q = 0 → S j q = T j q.val.2) ∧
          ∃ s ∈ Ioo ρ' ρ, Metric.closedBall (0 : ℂ) s ⊆ Metric.ball (0 : ℂ) ρ ∧
            (∑ j, ∫⁻ θ in Ioc (0 : ℝ) (2 * Real.pi), familySmallMemberHodgeMarginal p i a v U
              (parameterDisc ρ) hVU hsm L (S j) (fun q => multiplierWeight 1 (φ q.val.2)) (circleMap 0 s θ)) ≤
              ENNReal.ofReal ((1 + η) * (2 * Real.pi)) *
                ∑ j, nativeBertiniAdjunctionHodgeEnergy p i
                  (a - (0 : ComplexModel 1) 0 • v) (hsm ⟨0,h0⟩) L φ (T j) ∧
            (∑ j, familyNativeMemberCircleHodgeMean p i a v U (parameterDisc ρ) hVU hsm L φ s (S j)) ≤
              ENNReal.ofReal (1 + η) * ∑ j, nativeBertiniAdjunctionHodgeEnergy p i
                (a - (0 : ComplexModel 1) 0 • v) (hsm ⟨0,h0⟩) L φ (T j)) :
    ∃ R : ℝ, 0 < R ∧ ∀ rho : ℝ, 0 < rho → rho ≤ R →
      HasCircleExtensionsAtRadius (nativeBertiniQuotientFrameEnergy p i B hsB L hφ S) a (-v) rho := by
  classical
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  obtain ⟨W,hWU,h0W,hcoefficients⟩ := hcoef
  obtain ⟨rS,hrS,_hrSU,hsmall⟩ := hsharp
  obtain ⟨rW,hrW,hrWW⟩ := Metric.isOpen_iff.mp W.isOpen 0 h0W
  refine ⟨min rW (rS/4),lt_min hrW (by positivity),?_⟩
  intro rho hrho hrhoR
  have hrhoS : rho ≤ rS/4 := hrhoR.trans (min_le_right _ _)
  have hrhoW : rho ≤ rW := hrhoR.trans (min_le_left _ _)
  have hVW : parameterDisc rho ≤ W := fun z hz => hrWW (Metric.ball_subset_ball hrhoW hz)
  obtain ⟨hVU,hsections⟩ := hsmall rho hrho hrhoS
  let V := parameterDisc rho
  let hsV : ∀ t : V, IsSmoothHypersurfaceMember (d+1) p (affinePoint i (a-t.val 0 • v)) :=
    familyBaseRestrictedSmoothness p i a v U V hVU hsm
  let := familyChartedSpace p i a v V p.contMDiff hsV
  let := isComplexManifold_family p i a v V p.contMDiff hsV
  obtain ⟨C,hC,_hNorm,hEnergy,hRead⟩ := hcoefficients V hVW
  intro e he inner hinner hinnerR eta heta
  let T := fun j : Fin r =>
    (nativeMultiplierSwapLastSectionMap (nativeCanonicalBundle (n := d+1) (X := X)) L
      (nativeBertiniHyperplaneBundle p) hφ (∑ k, e j k • S k)).val
  have hDatum (j : Fin r) : nativeBertiniAdjunctionHodgeEnergy p i
      (a-(0 : ComplexModel 1) 0 • v) (hsm ⟨0,h0⟩) L φ (T j) =
      nativeBertiniQuotientFrameEnergy p i B hsB L hφ S a (e j) := by
    have h := nativeMultiplierAmbientCoefficientDatum_hodgeEnergy p i a v U hsm L hφ ⟨0,h0⟩ r S (e j)
    have hread := nativeBertiniQuotientFrameEnergy_apply p i B hsB L hφ S
      ⟨a-(0 : ComplexModel 1) 0 • v,hUB ⟨0,h0⟩⟩ (e j)
    have hz : a-(0 : ComplexModel 1) 0 • v = a := by simp
    exact h.trans (hread.symm.trans (congrArg
      (fun z => nativeBertiniQuotientFrameEnergy p i B hsB L hφ S z (e j)) hz))

  have hFinite (j : Fin r) : nativeBertiniAdjunctionHodgeEnergy p i
      (a-(0 : ComplexModel 1) 0 • v) (hsm ⟨0,h0⟩) L φ (T j) < ⊤ := by
    rw [hDatum j]
    exact lt_top_iff_ne_top.mpr (he j)
  obtain ⟨F,hTrace,s,hs,hclosed,hbound,_hmean⟩ := hsections inner hinner hinnerR eta heta r T hFinite
  let f : Fin r → ℂ → Fin r → ℂ := fun j => ordinaryNativeCoefficient V (C (F j))
  have hf (j : Fin r) : DifferentiableOn ℂ (f j) (Metric.ball 0 rho) := by
    have h := differentiableOn_ordinaryNativeCoefficient V (C (F j)) (hC (F j))
    rwa [ordinaryCoefficientDomain_parameterDisc] at h
  have h0V : (0 : ComplexModel 1) ∈ V := Metric.mem_ball_self hrho
  have hf0 (j : Fin r) : f j 0 = e j := by
    have hRead0 := hRead (F j) ⟨0,h0V⟩ (e j)
    have hCoeq : C (F j) ⟨0,h0V⟩ = e j := by
      apply hRead0
      intro q hq
      have hn : normalizedPencilNormal p i a v V rho q = 0 := by
        change q.val.1.val 0 / (rho : ℂ) = 0
        rw [hq]
        simp
      have ht := hTrace j q hn
      exact ht.trans (nativeMultiplierAmbientCoefficientDatum_trace p i a v U hsm L hφ r S (e j)
        (familyBaseInclusion p i a v U V hVU q))
    have hactual := ordinaryNativeCoefficient_at_actual V (C (F j)) ⟨0,h0V⟩
    simpa only [map_zero,f] using hactual.trans hCoeq
  refine ⟨s,⟨hs.1,hs.2.le⟩,Metric.ball 0 rho,f,Metric.isOpen_ball,hclosed,hf,hf0,?_⟩
  have hpoint (j : Fin r) (theta : ℝ) :
      nativeBertiniQuotientFrameEnergy p i B hsB L hφ S
        (a + circleMap 0 s theta • (-v)) (f j (circleMap 0 s theta)) ≤
      familySmallMemberHodgeMarginal p i a v U V hVU hsm L (F j)
        (fun q => multiplierWeight 1 (φ q.val.2)) (circleMap 0 s theta) := by
    let tau := circleMap 0 s theta
    have htau : modelOneScalarEquiv.symm tau ∈ V := by
      change dist (modelOneScalarEquiv.symm tau) 0 < rho
      rw [dist_zero_right,modelOneScalarEquiv.symm.norm_map]
      simpa only [Metric.mem_ball,dist_zero_right] using hclosed (Metric.sphere_subset_closedBall
        (circleMap_mem_sphere 0 (hinner.trans hs.1).le theta))

    let t : V := ⟨modelOneScalarEquiv.symm tau,htau⟩
    have hbase : a-t.val 0 • v ∈ B := hUB ⟨t.val,hVU t.property⟩
    have hfactual : f j tau = C (F j) t := by
      have h := ordinaryNativeCoefficient_at_actual V (C (F j)) t
      simpa only [LinearIsometryEquiv.apply_symm_apply,f,t] using h
    have hp : a+tau • (-v) = a-t.val 0 • v := by
      rw [native_pencil_parameter_ordinary a v tau]
      simp only [smul_neg,sub_eq_add_neg]
    rw [hp,hfactual,nativeBertiniQuotientFrameEnergy_apply p i B hsB L hφ S ⟨_,hbase⟩ (C (F j) t),
      familySmallMemberHodgeMarginal_originalPotential p i a v U V hVU hsm L φ tau htau (F j)]
    exact hEnergy (F j) t
  calc
    _ ≤ ∑ j, ∫⁻ theta in Ioc (0 : ℝ) (2*Real.pi), familySmallMemberHodgeMarginal p i a v U V hVU hsm L
        (F j) (fun q => multiplierWeight 1 (φ q.val.2)) (circleMap 0 s theta) := by
      apply Finset.sum_le_sum
      intro j _
      exact lintegral_mono (hpoint j)
    _ ≤ ENNReal.ofReal ((1+eta)*(2*Real.pi)) *
        ∑ j, nativeBertiniAdjunctionHodgeEnergy p i (a-(0 : ComplexModel 1) 0 • v)
          (hsm ⟨0,h0⟩) L φ (T j) := hbound
    _ = _ := by simp only [hDatum]

theorem exists_uniform_native_quotient_local_circle_mep
    (G : HermitianHolomorphicLineBundle.{0,0} (d+1) X)
    (hG : SGPT.Bergman.PolynomialH0Growth.IsSourceSmoothHermitianMetric G)
    (hGpos : (sourceNativeFirstChernForm G hG).val.IsKahler)
    (φ : X → EReal) (hφ : IsGlobalQuasiPshPotential (n := d+1) φ) :
    ∃ k₀ : ℕ, 0 < k₀ ∧ ∀ (A : HermitianHolomorphicLineBundle.{0,0} (d+1) X)
      (hA : SGPT.Bergman.PolynomialH0Growth.IsSourceSmoothHermitianMetric A),
      (sourceNativeFirstChernForm A hA).val.IsSemipositive → ∀ k : ℕ, k₀ ≤ k →
      let L := twistedPower G A k
      ∀ (i : Fin (N+1)) (B : TopologicalSpace.Opens (ComplexModel N))
        (hsB : ∀ zeta : B, IsSmoothHypersurfaceMember (d+1) p (affinePoint i zeta.val))
        (D : TopologicalSpace.Opens (ComplexModel N)) (hDB : D ≤ B)
        (r : ℕ) (S : Fin r → nativeMultiplierSections
          (tensor (tensor (nativeCanonicalBundle (n := d+1) (X := X)) L) (nativeBertiniHyperplaneBundle p)) φ),
      (∀ zeta : B, ∃ b : Module.Basis (Fin r) ℂ (NativeBertiniMultiplierQuotient p i zeta.val L hφ),
        ∀ j, b j = (nativeMultiplierSectionMap (tensor (nativeCanonicalBundle (n := d+1) (X := X)) L)
          (nativeBertiniHyperplaneBundle p) hφ (nativeBertiniAffineSection p i zeta.val)).range.mkQ (S j)) →
      (∀ zeta : D,
        let hsm := hsB ⟨zeta.val,hDB zeta.property⟩
        letI := nativeBertiniMemberChartedSpace p i zeta.val hsm
        letI := nativeBertiniMemberComplex p i zeta.val hsm
        letI := isCompact_iff_compactSpace.mp
          (isClosed_member p p.contMDiff.continuous (affinePoint i zeta.val)).isCompact
        Function.Injective (nativeBertiniPhysicalQuotientRestriction p i zeta.val hsm L hφ)) →
      HasLocalCircleMEP (nativeBertiniQuotientFrameEnergy p i B hsB L hφ S) D := by
  classical
  let : MeasurableSpace X := borel X
  let : BorelSpace X := ⟨rfl⟩
  obtain ⟨kC,hkC,hCoefficient⟩ := exists_uniform_native_coefficient_energy_control p G hG hGpos φ hφ
  obtain ⟨kS,hkS,hSharp⟩ := SGPT.Trace.BertiniUniversal.exists_uniform_original_ambient_simultaneous_annular_hodge_extension
    φ hφ G hG hGpos
  refine ⟨max kC kS,hkC.trans_le (le_max_left _ _),?_⟩
  intro A hA hAsemi k hk
  dsimp only
  have hCoefficientCurrent := hCoefficient A hA hAsemi k ((le_max_left _ _).trans hk)
  have hSharpCurrent := hSharp k ((le_max_right _ _).trans hk) A hA hAsemi
  intro i B hsB D hDB r S hb hInj a ha w
  let U := nativeQuotientPencilDomain D a (-w)
  have h0 : (0 : ComplexModel 1) ∈ U := nativeQuotientPencilDomain_zero D ha (-w)
  let point : U → B := fun t => ⟨a-t.val 0 • (-w),hDB t.property⟩
  let hsU : ∀ t : U, IsSmoothHypersurfaceMember (d+1) p (affinePoint i (a-t.val 0 • (-w))) :=
    fun t => hsB (point t)
  let b := fun t : U => Classical.choose (hb (point t))
  have hbU (t : U) (j : Fin r) : b t j =
      (nativeMultiplierSectionMap (tensor (nativeCanonicalBundle (n := d+1) (X := X)) (twistedPower G A k))
        (nativeBertiniHyperplaneBundle p) hφ (nativeBertiniAffineSection p i (a-t.val 0 • (-w)))).range.mkQ (S j) :=
    Classical.choose_spec (hb (point t)) j
  have hInjU (t : U) :
      letI := nativeBertiniMemberChartedSpace p i (a-t.val 0 • (-w)) (hsU t)
      letI := nativeBertiniMemberComplex p i (a-t.val 0 • (-w)) (hsU t)
      letI := isCompact_iff_compactSpace.mp
        (isClosed_member p p.contMDiff.continuous (affinePoint i (a-t.val 0 • (-w)))).isCompact
      Function.Injective (nativeBertiniPhysicalQuotientRestriction p i (a-t.val 0 • (-w)) (hsU t)
        (twistedPower G A k) hφ) := hInj ⟨a-t.val 0 • (-w),t.property⟩
  have hc := hCoefficientCurrent i a (-w) U hsU ⟨0,h0⟩ r S b hbU hInjU
  have hs := hSharpCurrent N p i a (-w) U hsU h0
  obtain ⟨R,hR,hcircles⟩ := native_pencil_circle_extensions_from_actual_producers p i a (-w) U hsU h0
    (twistedPower G A k) hφ B hsB (fun t => hDB t.property) r S hc hs
  refine ⟨R,hR,?_⟩
  intro rho hrho hrhoR _hDisc
  simpa only [neg_neg] using hcircles rho hrho hrhoR

end SGPT.Trace.BertiniFamilyCanonical
