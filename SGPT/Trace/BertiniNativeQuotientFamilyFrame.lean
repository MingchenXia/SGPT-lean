import SGPT.Trace.BertiniNativeQuotientHodge
import SGPT.Trace.BertiniFamilyAmbientSection
import SGPT.Trace.BertiniHolomorphicQuotientCoordinates

/-! Actual original quotient representatives are realized by genuine native
family H0, with exact FULL intrinsic coefficient Hodge energy. Quotient bases
are produced; no member-image independence or direct-image landing is assumed. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.BertiniFamilyCanonical
open Bundle Set Filter TensorProduct MeasureTheory
open scoped Manifold ContDiff Topology TensorProduct ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.TensorDictionaryDraft SGPT.Toric.F1IntersectionDraft
open SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle
open SGPT.Bergman.MultiplierSectionsDraft
open SGPT.Trace.Bertini SGPT.Trace.BertiniPencilFamily

variable {d N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (d + 1)) X] [IsComplexManifold (d + 1) X] [CompactSpace X]
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞)
  (i : Fin (N + 1)) (a v : ComplexModel N) (U : TopologicalSpace.Opens (ComplexModel 1))
  (hsm : ∀ t : U, IsSmoothHypersurfaceMember (d + 1) p (pencilParameter i a v t.val))
  (L : HermitianHolomorphicLineBundle.{0,0} (d + 1) X)
  {φ : X → EReal} (hφ : IsGlobalQuasiPshPotential (n := d + 1) φ)

def nativeMultiplierFamilyPhysicalSectionMap :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    nativeMultiplierSections
      (tensor (tensor (nativeCanonicalBundle (n := d + 1) (X := X)) L) (nativeBertiniHyperplaneBundle p)) φ →ₗ[ℂ]
      HolomorphicSections (n := d + 1) (familyNativePhysicalModel p i a v U hsm L).Fiber := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  let K := nativeCanonicalBundle (n := d + 1) (X := X)
  let P := nativeBertiniHyperplaneBundle p
  let W := fullHolomorphicIdealSections (n := d + 1) (tensor (tensor K P) L).Fiber (sourceDegreeMultiplierIdeal 1 φ)
  exact (nativeTensorSectionPullbackLinearMap (tensor K P) L (familyNativeXMap p i a v U hsm)).comp
    (W.subtype.comp (nativeMultiplierSwapLastSectionMap K L P hφ))

theorem nativeMultiplierFamilyPhysicalSectionMap_apply :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ (S : nativeMultiplierSections
      (tensor (tensor (nativeCanonicalBundle (n := d + 1) (X := X)) L) (nativeBertiniHyperplaneBundle p)) φ)
      (q : familyIncidence p i a v U),
      nativeMultiplierFamilyPhysicalSectionMap p i a v U hsm L hφ S q =
        NativeTensorSwap.swapLastFiber (nativeCanonicalBundle (n := d + 1) (X := X)) L
          (nativeBertiniHyperplaneBundle p) q.val.2 (S.val q.val.2) := by
  intros
  rfl

theorem nativeMultiplierFamilyPhysicalSectionMap_memberHodgeEnergy (t : U) :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ S : nativeMultiplierSections
      (tensor (tensor (nativeCanonicalBundle (n := d + 1) (X := X)) L) (nativeBertiniHyperplaneBundle p)) φ,
      familyNativeMemberHodgeEnergy p i a v U hsm L φ t
        (nativeMultiplierFamilyPhysicalSectionMap p i a v U hsm L hφ S) =
      nativeBertiniPhysicalQuotientHodgeEnergy p i (a - t.val 0 • v) (hsm t) L hφ
        ((nativeMultiplierSectionMap (tensor (nativeCanonicalBundle (n := d + 1) (X := X)) L)
          (nativeBertiniHyperplaneBundle p) hφ (nativeBertiniAffineSection p i (a - t.val 0 • v))).range.mkQ S) := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro S
  change familyNativeMemberHodgeEnergy p i a v U hsm L φ t
    (familyAmbientPhysicalSection p i a v U hsm L
      (NativeTensorSwap.swapLastSection (nativeCanonicalBundle (n := d + 1) (X := X)) L
        (nativeBertiniHyperplaneBundle p) S.val)) = _
  rw [familyAmbientPhysicalSection_memberHodgeEnergy,nativeBertiniPhysicalQuotientHodgeEnergy_mk]

theorem nativeMultiplierFamilyPhysicalSectionMap_memberHodgeEnergy_sum (t : U) :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ (r : ℕ) (S : Fin r → nativeMultiplierSections
      (tensor (tensor (nativeCanonicalBundle (n := d + 1) (X := X)) L) (nativeBertiniHyperplaneBundle p)) φ)
      (c : Fin r → ℂ),
      nativeBertiniPhysicalQuotientHodgeEnergy p i (a - t.val 0 • v) (hsm t) L hφ
        (∑ j, c j • (nativeMultiplierSectionMap (tensor (nativeCanonicalBundle (n := d + 1) (X := X)) L)
          (nativeBertiniHyperplaneBundle p) hφ (nativeBertiniAffineSection p i (a - t.val 0 • v))).range.mkQ (S j)) =
      familyNativeMemberHodgeEnergy p i a v U hsm L φ t
        (∑ j, c j • nativeMultiplierFamilyPhysicalSectionMap p i a v U hsm L hφ (S j)) := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  classical
  intro r S c
  have h := nativeMultiplierFamilyPhysicalSectionMap_memberHodgeEnergy p i a v U hsm L hφ t (∑ j, c j • S j)
  simpa only [map_sum,map_smul] using h.symm

theorem exists_native_pencil_quotient_family_frame [ConnectedSpace X]
    (h0 : (0 : ComplexModel 1) ∈ U) (hproper : ∃ x : X, x ∉ member p (affinePoint i a)) :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∃ (r : ℕ) (S : Fin r → nativeMultiplierSections
      (tensor (tensor (nativeCanonicalBundle (n := d + 1) (X := X)) L) (nativeBertiniHyperplaneBundle p)) φ)
      (V : TopologicalSpace.Opens (ComplexModel 1)) (_hVU : V ≤ U) (_h0V : (0 : ComplexModel 1) ∈ V),
      ∀ t : V, ∃ b : Module.Basis (Fin r) ℂ (NativeBertiniMultiplierQuotient p i (a - t.val 0 • v) L hφ),
        (∀ j, b j = (nativeMultiplierSectionMap (tensor (nativeCanonicalBundle (n := d + 1) (X := X)) L)
          (nativeBertiniHyperplaneBundle p) hφ (nativeBertiniAffineSection p i (a - t.val 0 • v))).range.mkQ (S j)) ∧
        ∀ c : Fin r → ℂ,
          nativeBertiniPhysicalQuotientHodgeEnergy p i (a - t.val 0 • v) (hsm ⟨t.val,_hVU t.property⟩) L hφ
            (∑ j, c j • b j) =
          familyNativeMemberHodgeEnergy p i a v U hsm L φ ⟨t.val,_hVU t.property⟩
            (∑ j, c j • nativeMultiplierFamilyPhysicalSectionMap p i a v U hsm L hφ (S j)) := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  classical
  obtain ⟨r,S,W,hW,haW,hbasis⟩ := exists_nativeBertiniHyperplane_quotientBasis p
    (tensor (nativeCanonicalBundle (n := d + 1) (X := X)) L) hφ i a hproper
  let f : ComplexModel 1 → ComplexModel N := fun z => a - z 0 • v
  have hf : Continuous f := continuous_const.sub
    ((EuclideanSpace.proj (0 : Fin 1) : ComplexModel 1 →L[ℂ] ℂ).continuous.smul continuous_const)
  let V : TopologicalSpace.Opens (ComplexModel 1) := ⟨(U : Set (ComplexModel 1)) ∩ f ⁻¹' W,
    U.isOpen.inter (hW.preimage hf)⟩
  have hVU : V ≤ U := fun _ hz => hz.1
  have h0V : (0 : ComplexModel 1) ∈ V := by
    refine ⟨h0,?_⟩
    change a - (0 : ComplexModel 1) 0 • v ∈ W
    simpa only [PiLp.zero_apply,zero_smul,sub_zero] using haW
  refine ⟨r,S,V,hVU,h0V,?_⟩
  intro t
  obtain ⟨b,hb⟩ := hbasis (a - t.val 0 • v) t.property.2
  refine ⟨b,hb,?_⟩
  intro c
  have h := nativeMultiplierFamilyPhysicalSectionMap_memberHodgeEnergy_sum p i a v U hsm L hφ
    ⟨t.val,hVU t.property⟩ r S c
  have hsum : (∑ j, c j • b j) = ∑ j, c j •
      (nativeMultiplierSectionMap (tensor (nativeCanonicalBundle (n := d + 1) (X := X)) L)
        (nativeBertiniHyperplaneBundle p) hφ (nativeBertiniAffineSection p i (a - t.val 0 • v))).range.mkQ (S j) := by
    apply Finset.sum_congr rfl
    intro j _
    rw [hb j]
  rw [hsum]
  exact h

end SGPT.Trace.BertiniFamilyCanonical
