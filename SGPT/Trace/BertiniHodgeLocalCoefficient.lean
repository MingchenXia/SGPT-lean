import SGPT.Trace.NativeCanonicalPhysicalHodgeIntegral
import SGPT.Bergman.SourceMultiplierSectionLocalMass

/-! Actual canonical physical coefficient and local multiplier mass dictionary.
All extended weights are retained; no auxiliary K norm is called Hodge. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.Bertini
open Bundle Set Filter TensorProduct MeasureTheory
open scoped Manifold ContDiff Topology TensorProduct ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.TensorDictionaryDraft
open SGPT.Bergman.CompactHolomorphicSectionsDraft SGPT.Bergman.MultiplierSectionsDraft
open SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] [CompactSpace X]
  (L : HermitianHolomorphicLineBundle n X)

theorem nativePhysicalPreferredChartValue_eq_coefficient
    (a x : X) (hx : x ∈ (complexChartAt (n := n) a).val.source)
    (e : AtlasFrame L) (he : x ∈ e.val.baseSet)
    (T : (tensor (nativeCanonicalBundle (n := n) (X := X)) L).Fiber x) :
    nativeCanonicalPhysicalChartValue L (complexChartAt (n := n) a) x hx T =
      ((tensorAtlasFrame (nativeCanonicalFrame (n := n) a) e).val ⟨x,T⟩).2 • e.val.symm x 1 := by
  let eK := nativeCanonicalFrame (n := n) a
  let q := tensorAtlasFrame eK e
  let := eK.property
  let := e.property
  let := q.property
  have hq : x ∈ q.val.baseSet := ⟨hx,he⟩
  let E := q.val.linearEquivAt ℂ x hq
  have hq1 : E (q.val.symm x 1) = 1 := by
    exact congrArg Prod.snd (q.val.apply_mk_symm hq (1 : ℂ))
  have hT : T = E T • q.val.symm x 1 := by
    apply E.injective
    rw [map_smul,hq1,smul_eq_mul,mul_one]
  have hK1 : ((eK.val ⟨x,eK.val.symm x 1⟩).2) = 1 :=
    congrArg Prod.snd (eK.val.apply_mk_symm hx (1 : ℂ))
  have hunit : nativeCanonicalPhysicalChartValue L (complexChartAt (n := n) a) x hx
      (q.val.symm x 1) = e.val.symm x 1 := by
    rw [tensorAtlasFrame_symm eK e hq,one_smul]
    change nativeCanonicalFiberInChart (complexChartAt (n := n) a) x hx (eK.val.symm x 1)
      (EuclideanSpace.basisFun (Fin n) ℂ).toBasis • e.val.symm x 1 = _
    rw [nativeCanonicalFiberInPreferredChart_coordinates,Module.Basis.det_self,hK1,mul_one,one_smul]
  calc
    _ = nativeCanonicalPhysicalChartValue L (complexChartAt (n := n) a) x hx
        (E T • q.val.symm x 1) := congrArg _ hT
    _ = E T • e.val.symm x 1 := by rw [map_smul,hunit]
    _ = _ := rfl

theorem nativePhysicalPreferredCoordinateDensity_eq_multiplier
    (S : ∀ x, (tensor (nativeCanonicalBundle (n := n) (X := X)) L).Fiber x)
    (φ : X → EReal) (a : X) (e : AtlasFrame L) (z : ComplexModel n)
    (hz : z ∈ (complexChartAt (n := n) a).val.target)
    (he : (complexChartAt (n := n) a).val.symm z ∈ e.val.baseSet) :
    nativeCanonicalPhysicalCoordinateDensity L S (fun x => multiplierWeight 1 (φ x))
      (complexChartAt (n := n) a) z =
    ENNReal.ofReal (‖e.val.symm ((complexChartAt (n := n) a).val.symm z) 1‖ ^ 2) *
      multiplierDensity (chartFunction φ (complexChartAt (n := n) a)) 1
        (fun y => ((tensorAtlasFrame (nativeCanonicalFrame (n := n) a) e).val
          ⟨(complexChartAt (n := n) a).val.symm y,S ((complexChartAt (n := n) a).val.symm y)⟩).2) z := by
  classical
  unfold nativeCanonicalPhysicalCoordinateDensity
  rw [dif_pos hz]
  unfold nativeCanonicalPhysicalChartDensity
  rw [nativePhysicalPreferredChartValue_eq_coefficient L a _ _ e he,
    norm_smul,mul_pow,ENNReal.ofReal_mul (sq_nonneg _)]
  unfold multiplierDensity chartFunction
  dsimp only
  rw [mul_assoc]
  exact mul_left_comm _ _ _

theorem nativePhysicalPreferredCompact_finite_iff
    (S : ∀ x, (tensor (nativeCanonicalBundle (n := n) (X := X)) L).Fiber x)
    (φ : X → EReal) (a : X) (e : AtlasFrame L)
    {K : Set (ComplexModel n)} (hK : IsCompact K)
    (hKt : K ⊆ (complexChartAt (n := n) a).val.target)
    (hKe : ∀ z ∈ K, (complexChartAt (n := n) a).val.symm z ∈ e.val.baseSet) :
    (∫⁻ z in K, nativeCanonicalPhysicalCoordinateDensity L S
      (fun x => multiplierWeight 1 (φ x)) (complexChartAt (n := n) a) z) < ⊤ ↔
    (∫⁻ z in K, multiplierDensity (chartFunction φ (complexChartAt (n := n) a)) 1
      (fun y => ((tensorAtlasFrame (nativeCanonicalFrame (n := n) a) e).val
        ⟨(complexChartAt (n := n) a).val.symm y,S ((complexChartAt (n := n) a).val.symm y)⟩).2) z) < ⊤ := by
  classical
  let := e.property
  let c := complexChartAt (n := n) a
  let g : ComplexModel n → ℝ := fun z => ‖e.val.symm (c.val.symm z) 1‖ ^ 2
  let D := multiplierDensity (chartFunction φ c) 1
    (fun y => ((tensorAtlasFrame (nativeCanonicalFrame (n := n) a) e).val ⟨c.val.symm y,S (c.val.symm y)⟩).2)
  have hidentity : (∫⁻ z in K, nativeCanonicalPhysicalCoordinateDensity L S
      (fun x => multiplierWeight 1 (φ x)) c z) =
      ∫⁻ z in K, ENNReal.ofReal (g z) * D z := by
    refine setLIntegral_congr_fun hK.isClosed.measurableSet fun z hz => ?_
    exact nativePhysicalPreferredCoordinateDensity_eq_multiplier L S φ a e z (hKt hz) (hKe z hz)
  rw [hidentity]
  rcases K.eq_empty_or_nonempty with rfl | hne
  · simp
  have hgc : ContinuousOn g K :=
    (((frameNorm_continuousOn L.Fiber e.val).comp (c.val.continuousOn_symm.mono hKt) hKe).pow 2)
  have hgp : ∀ z ∈ K, 0 < g z := fun z hz =>
    sq_pos_of_pos (frameNorm_pos L.Fiber e.val (hKe z hz))
  obtain ⟨z₀,hz₀,hmin⟩ := hK.exists_isMinOn hne hgc
  have hg₀ : 0 < g z₀ := hgp z₀ hz₀
  obtain ⟨B,hB⟩ := hK.exists_bound_of_continuousOn hgc
  constructor
  · intro hf
    have hb : (∫⁻ z in K, D z) ≤ ENNReal.ofReal (g z₀)⁻¹ *
        ∫⁻ z in K, ENNReal.ofReal (g z) * D z := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hK.isClosed.measurableSet] with z hz
      rw [← mul_assoc,← ENNReal.ofReal_mul (inv_nonneg.mpr hg₀.le)]
      apply le_mul_of_one_le_left zero_le
      rw [← ENNReal.ofReal_one]
      apply ENNReal.ofReal_le_ofReal
      rw [inv_mul_eq_div,le_div_iff₀ hg₀,one_mul]
      exact hmin hz
    exact hb.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hf)
  · intro hf
    have hb : (∫⁻ z in K, ENNReal.ofReal (g z) * D z) ≤
        ENNReal.ofReal B * ∫⁻ z in K, D z := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hK.isClosed.measurableSet] with z hz
      exact mul_le_mul' (ENNReal.ofReal_le_ofReal
        ((le_abs_self _).trans ((Real.norm_eq_abs _).symm.le.trans (hB z hz)))) le_rfl
    exact hb.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hf)

end SGPT.Trace.Bertini
