import SGPT.Trace.BertiniUniversalPhysicalFactor
import SGPT.Trace.BertiniUniversalChartMass

/-! Actual original global multiplier section -> finite physical q target
mass on compact true chart/frame domains. No finite-energy premise. -/
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.BertiniUniversal
open Bundle Set Filter Metric TensorProduct MeasureTheory
open scoped Topology Manifold ContDiff BigOperators TensorProduct ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.ProductComplexManifold
open SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Trace.Bertini
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.TensorDictionaryDraft
open SGPT.Bergman.CompactHolomorphicSectionsDraft SGPT.Bergman.MultiplierSectionsDraft
open SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle

section Point
variable {d N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (d + 1)) X] [IsComplexManifold (d + 1) X] [CompactSpace X]
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞)
  {φ : X → EReal} (c : SliceChart (d + 1) (p : X → ComplexProjectiveSpace N) φ)
  (a : X) (L : HermitianHolomorphicLineBundle.{0,0} (d + 1) X)
  (eP : AtlasFrame (nativeBertiniHyperplaneBundle p)) (eL : AtlasFrame L) (m : Fin N)

theorem originalLocalQTargetDensity_eq_original (ha : c.e = complexChartAt (n := d + 1) a)
    {z₀ : ComplexModel (N + d)} (Θ : LocalHolomorphicEquivAt (n := N + d) z₀)
    (hsrc : Θ.source ⊆ originalQSourceDomain p c) (hfun : Θ.toFun = originalQCoordinateMap p c m)
    (T : HolomorphicSections (n := d + 1) (OriginalAmbientPhysicalBundle p L).Fiber)
    {y : ComplexModel (N + d)} (hy : y ∈ Θ.target)
    (hP : originalQTargetX p c m y ∈ eP.val.baseSet) (hL : originalQTargetX p c m y ∈ eL.val.baseSet) :
    originalLocalQTargetDensity p c m Θ hsrc L T (fun x => multiplierWeight 1 (φ x)) y =
      ENNReal.ofReal (originalQPhysicalFrameFactor p c a L eP eL m (originalQTargetX p c m y) ^ 2) *
        originalSectionDensity (OriginalAmbientPhysicalBundle p L).Fiber φ 1 T (originalQTargetX p c m y) := by
  let q := originalQSourcePair p c ⟨Θ.invFun y,hsrc (Θ.mapsTo_invFun hy)⟩
  have hx : c.tangentPoint q = originalQTargetX p c m y := originalLocalQInverse_X p c m Θ hsrc hfun hy
  have hn := originalQPhysical_norm_factor p c a L eP eL m ha q (hx.symm ▸ hP) (hx.symm ▸ hL) T
  have hd : originalLocalQTargetDensity p c m Θ hsrc L T (fun x => multiplierWeight 1 (φ x)) y =
      ENNReal.ofReal (‖(parameterCoefficient p c.i c.j m (c.tangentPoint q))⁻¹ •
        c.originalAmbientLValue p.contMDiff q L (T (c.tangentPoint q))‖ ^ 2) * multiplierWeight 1 (φ (c.tangentPoint q)) := dif_pos hy
  rw [hn,mul_pow,ENNReal.ofReal_mul (sq_nonneg _),hx] at hd
  simpa only [originalSectionDensity,mul_assoc] using hd
end Point

section Mass
variable {k d : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (d + 1)) X] [IsComplexManifold (d + 1) X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel (k + 1)) X (ComplexProjectiveSpace (k + 1)) ∞)
  {φ : X → EReal} (c : SliceChart (d + 1) (p : X → ComplexProjectiveSpace (k + 1)) φ)
  (a : X) (L : HermitianHolomorphicLineBundle.{0,0} (d + 1) X)
  (eP : AtlasFrame (nativeBertiniHyperplaneBundle p)) (eL : AtlasFrame L) (m : Fin (k + 1))

theorem originalLocalQTargetDensity_compact_integral_lt_top
    (ha : c.e = complexChartAt (n := d + 1) a)
    {z₀ : ComplexModel (k + 1 + d)} (Θ : LocalHolomorphicEquivAt (n := k + 1 + d) z₀)
    (hsrc : Θ.source ⊆ originalQSourceDomain p c) (hfun : Θ.toFun = originalQCoordinateMap p c m)
    {D : Set (ComplexModel (k + 1 + d))} (hD : IsCompact D) (hDt : D ⊆ Θ.target)
    (hDX : ∀ y ∈ D, originalQTargetXCoordinates (d := d) m y ∈ c.e.val.target)
    (hDF : ∀ y ∈ D, originalQTargetX p c m y ∈ eP.val.baseSet ∧
      originalQTargetX p c m y ∈ eL.val.baseSet ∧
      p (originalQTargetX p c m y) ∈ (affineChart c.j).source ∧
      parameterCoefficient p c.i c.j m (originalQTargetX p c m y) ≠ 0)
    (hφ : IsGlobalQuasiPshPotential (n := d + 1) φ)
    (T : nativeMultiplierSections (OriginalAmbientPhysicalBundle p L) φ)
    (μ : Measure X) (hμ : IsSmoothPositiveVolume (n := d + 1) μ) :
    (∫⁻ y in D, originalLocalQTargetDensity p c m Θ hsrc L T.val
      (fun x => multiplierWeight 1 (φ x)) y) < ⊤ := by
  let E := deletedParameterProductEquiv k d
  let R : ComplexModel (k + 1 + d) → ComplexModel (d + 1) := originalQTargetXCoordinates (d := d) m
  have hR : Continuous R :=
    ((prodModelEquiv (k + 1) (d + 1)).symm.continuous.snd).comp (parameterZeroInsert (m.castAdd (d + 1))).continuous
  let K := R '' D
  have hK : IsCompact K := hD.image hR
  have hKt : K ⊆ c.e.val.target := by rintro _ ⟨y,hy,rfl⟩; exact hDX y hy
  let A := c.e.val.symm '' K
  have hA : IsCompact A := hK.image_of_continuousOn (c.e.val.continuousOn_symm.mono hKt)
  have hAD : A ⊆ {x | x ∈ c.e.val.source ∧ x ∈ eP.val.baseSet ∧ x ∈ eL.val.baseSet ∧
      p x ∈ (affineChart c.j).source ∧ parameterCoefficient p c.i c.j m x ≠ 0} := by
    rintro x ⟨z,⟨y,hy,rfl⟩,rfl⟩
    exact ⟨c.e.val.map_target (hDX y hy),(hDF y hy).1,(hDF y hy).2.1,(hDF y hy).2.2⟩
  have hc := (originalQPhysicalFrameFactor_continuousOn p c a L eP eL m ha).mono hAD
  obtain ⟨C,hC⟩ := hA.exists_bound_of_continuousOn (hc.pow 2)
  have hfree : IsCompact ((fun y => (E.symm y).1) '' D) := hD.image (continuous_fst.comp E.symm.continuous)
  obtain ⟨r,hr⟩ := hfree.isBounded.subset_closedBall (0 : ComplexModel k)
  have hbox : D ⊆ E '' ((closedBall 0 r) ×ˢ K) := by
    intro y hy
    refine ⟨E.symm y,⟨hr ⟨y,hy,rfl⟩,?_⟩,E.apply_symm_apply y⟩
    have he : originalQTargetXCoordinates (d := d) m y = (E.symm y).2 := by
      calc
        _ = originalQTargetXCoordinates (d := d) m (E (E.symm y)) :=
          congrArg (originalQTargetXCoordinates (d := d) m) (E.apply_symm_apply y).symm
        _ = _ := by
          simpa only [Prod.mk.eta] using
            originalQTargetXCoordinates_product k d m (E.symm y).1 (E.symm y).2
    rw [← he]
    exact ⟨y,hy,rfl⟩
  have hmass : (∫⁻ y in D, originalSectionDensity (OriginalAmbientPhysicalBundle p L).Fiber φ 1 T.val
      (originalQTargetX p c m y)) < ⊤ := by
    have hfull := originalMultiplier_retained_chart_integral_lt_top
      (OriginalAmbientPhysicalBundle p L) φ hφ T μ hμ c.e m 0 r hK hKt
    exact (lintegral_mono' (Measure.restrict_mono hbox le_rfl) le_rfl).trans_lt hfull
  have hbound : (∫⁻ y in D, originalLocalQTargetDensity p c m Θ hsrc L T.val
      (fun x => multiplierWeight 1 (φ x)) y) ≤ ENNReal.ofReal C *
        ∫⁻ y in D, originalSectionDensity (OriginalAmbientPhysicalBundle p L).Fiber φ 1 T.val
          (originalQTargetX p c m y) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem hD.isClosed.measurableSet] with y hy
    rw [originalLocalQTargetDensity_eq_original p c a L eP eL m ha Θ hsrc hfun T.val
      (hDt hy) (hDF y hy).1 (hDF y hy).2.1]
    apply mul_le_mul' _ le_rfl
    apply ENNReal.ofReal_le_ofReal
    exact (le_abs_self _).trans ((Real.norm_eq_abs _).symm.le.trans (hC _ ⟨R y,⟨y,hy,rfl⟩,rfl⟩))
  exact hbound.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hmass)
end Mass
end SGPT.Trace.BertiniUniversal
