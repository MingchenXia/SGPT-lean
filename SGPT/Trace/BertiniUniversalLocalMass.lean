import SGPT.Trace.BertiniUniversalTargetMass

/-! Internally produced true original residue finite-mass neighborhoods
from actual global original multiplier sections, no L1/Fubini certificate. -/
set_option autoImplicit false
set_option maxHeartbeats 3500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.BertiniUniversal
attribute [local instance] Classical.propDecidable
open Bundle Set Filter Metric TensorProduct MeasureTheory
open scoped Topology Manifold ContDiff BigOperators TensorProduct ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending.ProductComplexManifold
open SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Trace.Bertini
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.TensorDictionaryDraft
open SGPT.Bergman.CompactHolomorphicSectionsDraft SGPT.Bergman.MultiplierSectionsDraft
open SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle

variable {k d : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (d + 1)) X] [IsComplexManifold (d + 1) X] [CompactSpace X]
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel (k + 1)) X (ComplexProjectiveSpace (k + 1)) ∞)
  {φ : X → EReal} (c : SliceChart (d + 1) (p : X → ComplexProjectiveSpace (k + 1)) φ)

private theorem originalSourceDensity_jac_target
    (m : Fin (k + 1)) {z₀ : ComplexModel (k + 1 + d)}
    (Θ : LocalHolomorphicEquivAt (n := k + 1 + d) z₀)
    (hsrc : Θ.source ⊆ originalQSourceDomain p c) (hfun : Θ.toFun = originalQCoordinateMap p c m)
    (hcoeff : ∀ z ∈ Θ.source, parameterCoefficient p c.i c.j m (originalQSourceX p c z) ≠ 0)
    (L : HermitianHolomorphicLineBundle.{0,0} (d + 1) X)
    (T : ∀ x, (OriginalAmbientPhysicalBundle p L).Fiber x) (w : X → ℝ≥0∞)
    {z : ComplexModel (k + 1 + d)} (hz : z ∈ Θ.source) :
    originalMemberResidueSourceDensity p c L T w z =
      ENNReal.ofReal |LinearMap.det (fderiv ℝ (originalQCoordinateMap p c m) z).toLinearMap| *
        originalLocalQTargetDensity p c m Θ hsrc L T w (originalQCoordinateMap p c m z) := by
  let q := originalQSourcePair p c ⟨z,hsrc hz⟩
  have hpoint : prodModelEquiv (k + 1) d (q.1.val,q.2.val) = z := (prodModelEquiv (k + 1) d).apply_symm_apply z
  have ht : originalQCoordinateMap p c m z ∈ Θ.target := by rw [← hfun]; exact Θ.mapsTo_toFun hz
  have hi : Θ.invFun (originalQCoordinateMap p c m z) = z := by rw [← hfun]; exact Θ.left_inv z hz
  have hpair : (⟨Θ.invFun (originalQCoordinateMap p c m z),hsrc (Θ.mapsTo_invFun ht)⟩ : originalQSourceDomain p c) =
      ⟨z,hsrc hz⟩ := Subtype.ext hi
  have hg : originalLocalQTargetDensity p c m Θ hsrc L T w (originalQCoordinateMap p c m z) =
      originalQDividedSourceDensity p c m L T w ⟨z,hsrc hz⟩ := by
    dsimp only [originalLocalQTargetDensity]
    rw [dif_pos ht,hpair]
  have hp := originalPhysicalResidueDensity_qJacobian p c m q L (T (c.tangentPoint q)) (hcoeff z hz) (w (c.tangentPoint q))
  rw [hpoint] at hp
  have hs : originalMemberResidueSourceDensity p c L T w z =
      ENNReal.ofReal (‖(c.tangentNormalDenominator q)⁻¹ • c.originalAmbientLValue p.contMDiff q L (T (c.tangentPoint q))‖ ^ 2) *
        w (c.tangentPoint q) := dif_pos (hsrc hz)
  exact hs.trans (hp.trans (congrArg
    (fun a : ℝ≥0∞ => ENNReal.ofReal |LinearMap.det (fderiv ℝ (originalQCoordinateMap p c m) z).toLinearMap| * a) hg.symm))

variable [MeasurableSpace X] [BorelSpace X]

theorem exists_originalResidue_multiplier_finite_neighborhood
    (a : X) (ha : c.e = complexChartAt (n := d + 1) a)
    (L : HermitianHolomorphicLineBundle.{0,0} (d + 1) X)
    (q₀ : (ball c.ζ₀ c.r) × c.tangentPatch) :
    ∃ W : Set (ComplexModel (k + 1 + d)), IsOpen W ∧
      prodModelEquiv (k + 1) d (q₀.1.val,q₀.2.val) ∈ W ∧ W ⊆ originalQSourceDomain p c ∧
      ∀ (_hφ : IsGlobalQuasiPshPotential (n := d + 1) φ)
        (T : nativeMultiplierSections (OriginalAmbientPhysicalBundle p L) φ)
        (μ : Measure X) (_hμ : IsSmoothPositiveVolume (n := d + 1) μ),
        (∫⁻ z in W, originalMemberResidueSourceDensity p c L T.val (fun x => multiplierWeight 1 (φ x)) z) < ⊤ := by
  classical
  let x₀ := c.tangentPoint q₀
  let z₀ := prodModelEquiv (k + 1) d (q₀.1.val,q₀.2.val)
  have hxj : p x₀ ∈ (affineChart c.j).source :=
    (mem_chartLiftDomain_iff p (c.tangentPoint_chart_coordinates q₀).1).mp
      (c.tangentPoint_chart_coordinates q₀).2.2
  have hzero : localEquation p c.i c.j (q₀.1.val,x₀) = 0 :=
    (mem_affineIncidence_iff_localEquation p c.i c.j hxj).mp (c.tangentPoint_mem_member q₀)
  obtain ⟨m,hm⟩ := exists_succAbove_ne_zero_of_pairing_eq_zero (affineLift_ne_zero c.j _) hzero
  have hm₀ : parameterCoefficient p c.i c.j m x₀ ≠ 0 := hm
  obtain ⟨Θ,hsrc,hfun,hcoeff,hcov⟩ := exists_originalQCoordinate_local_COV p c m q₀ hm₀
  let y₀ := originalQCoordinateMap p c m z₀
  have hy₀ : y₀ ∈ Θ.target := by rw [show y₀ = Θ.toFun z₀ by exact congrFun hfun.symm z₀]; exact Θ.mapsTo_toFun Θ.center_mem_source
  let eP : AtlasFrame (nativeBertiniHyperplaneBundle p) := ⟨trivializationAt ℂ (nativeBertiniHyperplaneBundle p).Fiber x₀,inferInstance⟩
  let eL : AtlasFrame L := ⟨trivializationAt ℂ L.Fiber x₀,inferInstance⟩
  have hP₀ : x₀ ∈ eP.val.baseSet := mem_baseSet_trivializationAt ℂ _ _
  have hL₀ : x₀ ∈ eL.val.baseSet := mem_baseSet_trivializationAt ℂ _ _
  let R : ComplexModel (k + 1 + d) → ComplexModel (d + 1) := originalQTargetXCoordinates (d := d) m
  let f : ComplexModel (k + 1 + d) → X := originalQTargetX p c m
  have hR : Continuous R := ((prodModelEquiv (k + 1) (d + 1)).symm.continuous.snd).comp
    (parameterZeroInsert (m.castAdd (d + 1))).continuous
  have hpoint : f y₀ = x₀ := originalQTargetX_apply p c m q₀
  have hR₀ : R y₀ ∈ c.e.val.target := by
    rw [show R y₀ = c.originalTangentCoordinateMap q₀.1.val q₀.2.val from originalQTargetXCoordinates_apply p c m q₀]
    change c.slice q₀.1.val (c.tangentLift q₀.2.val) ∈ c.e.val.target
    rw [← (c.tangentPoint_chart_coordinates q₀).2.1]
    exact c.e.val.map_source (c.tangentPoint_chart_coordinates q₀).1
  have hf : ContinuousAt f y₀ := (c.e.val.continuousOn_symm.continuousAt (c.e.val.open_target.mem_nhds hR₀)).comp hR.continuousAt
  have hc : ContinuousAt (parameterCoefficient p c.i c.j m) x₀ :=
    (contMDiffAt_parameterCoefficient p c.i c.j m hxj).continuousAt
  have hgood : {y | y ∈ Θ.target ∧ R y ∈ c.e.val.target ∧ f y ∈ eP.val.baseSet ∧
      f y ∈ eL.val.baseSet ∧ p (f y) ∈ (affineChart c.j).source ∧ parameterCoefficient p c.i c.j m (f y) ≠ 0} ∈ 𝓝 y₀ := by
    have hP' : ∀ᶠ x in 𝓝 (f y₀), x ∈ eP.val.baseSet := by
      change eP.val.baseSet ∈ 𝓝 (f y₀)
      rw [hpoint]
      exact eP.val.open_baseSet.mem_nhds hP₀
    have hL' : ∀ᶠ x in 𝓝 (f y₀), x ∈ eL.val.baseSet := by
      change eL.val.baseSet ∈ 𝓝 (f y₀)
      rw [hpoint]
      exact eL.val.open_baseSet.mem_nhds hL₀
    have hP : ∀ᶠ y in 𝓝 y₀, f y ∈ eP.val.baseSet := hf.eventually hP'
    have hL : ∀ᶠ y in 𝓝 y₀, f y ∈ eL.val.baseSet := hf.eventually hL'
    have hp' : ∀ᶠ x in 𝓝 (p (f y₀)), x ∈ (affineChart c.j).source := by
      change (affineChart c.j).source ∈ 𝓝 (p (f y₀))
      rw [hpoint]
      exact (affineChart c.j).open_source.mem_nhds hxj
    have hpf : ContinuousAt (fun y => p (f y)) y₀ := p.contMDiff.continuous.continuousAt.comp (f := f) (x := y₀) hf
    have hj : ∀ᶠ y in 𝓝 y₀, p (f y) ∈ (affineChart c.j).source := hpf.eventually hp'
    have hc' : ContinuousAt (parameterCoefficient p c.i c.j m) (f y₀) := by rw [hpoint]; exact hc
    have hcf : ContinuousAt (fun y => parameterCoefficient p c.i c.j m (f y)) y₀ := hc'.comp (f := f) (x := y₀) hf
    have hn : ∀ᶠ y in 𝓝 y₀, parameterCoefficient p c.i c.j m (f y) ≠ 0 :=
      hcf.eventually_ne (by rw [hpoint]; exact hm₀)
    have ht : ∀ᶠ y in 𝓝 y₀, y ∈ Θ.target := Θ.isOpen_target.mem_nhds hy₀
    exact ht.and ((hR.continuousAt.eventually (c.e.val.open_target.mem_nhds hR₀)).and
      (hP.and (hL.and (hj.and hn))))
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp hgood
  let ε := r / 2
  have hε : 0 < ε := half_pos hr
  have hDgood : closedBall y₀ ε ⊆ {y | y ∈ Θ.target ∧ R y ∈ c.e.val.target ∧ f y ∈ eP.val.baseSet ∧
      f y ∈ eL.val.baseSet ∧ p (f y) ∈ (affineChart c.j).source ∧ parameterCoefficient p c.i c.j m (f y) ≠ 0} :=
    (closedBall_subset_ball (by dsimp only [ε]; linarith)).trans hball
  let W := {z | z ∈ Θ.source ∧ originalQCoordinateMap p c m z ∈ ball y₀ ε}
  have hW : IsOpen W := by
    rw [isOpen_iff_mem_nhds]
    intro z hz
    have hs : ∀ᶠ y in 𝓝 z, y ∈ Θ.source := Θ.isOpen_source.mem_nhds hz.1
    exact hs.and
      ((differentiableAt_originalQCoordinateMap p c m (hsrc hz.1)).continuousAt.eventually (isOpen_ball.mem_nhds hz.2))
  refine ⟨W,hW,⟨Θ.center_mem_source,by exact mem_ball_self hε⟩,fun z hz => hsrc hz.1,?_⟩
  intro hφ T μ hμ
  let dens := originalLocalQTargetDensity p c m Θ hsrc L T.val (fun x => multiplierWeight 1 (φ x))
  let g := (closedBall y₀ ε).indicator dens
  have hfinite : (∫⁻ y in closedBall y₀ ε, dens y) < ⊤ :=
    originalLocalQTargetDensity_compact_integral_lt_top p c a L eP eL m ha Θ hsrc hfun
      (isCompact_closedBall _ _) (fun y hy => (hDgood hy).1) (fun y hy => (hDgood hy).2.1)
      (fun y hy => (hDgood hy).2.2) hφ T μ hμ
  have hineq : (∫⁻ z in W, originalMemberResidueSourceDensity p c L T.val (fun x => multiplierWeight 1 (φ x)) z) ≤
      ∫⁻ y in closedBall y₀ ε, dens y := by
    calc
      _ = ∫⁻ z in W, ENNReal.ofReal |LinearMap.det (fderiv ℝ (originalQCoordinateMap p c m) z).toLinearMap| *
          g (originalQCoordinateMap p c m z) := by
        apply setLIntegral_congr_fun hW.measurableSet
        intro z hz
        have hg : g (originalQCoordinateMap p c m z) = dens (originalQCoordinateMap p c m z) :=
          indicator_of_mem (ball_subset_closedBall hz.2) dens
        exact (originalSourceDensity_jac_target p c m Θ hsrc hfun hcoeff L T.val (fun x => multiplierWeight 1 (φ x)) hz.1).trans
          (congrArg (fun b : ℝ≥0∞ => ENNReal.ofReal |LinearMap.det (fderiv ℝ (originalQCoordinateMap p c m) z).toLinearMap| * b) hg.symm)
      _ ≤ ∫⁻ z in Θ.source, ENNReal.ofReal |LinearMap.det (fderiv ℝ (originalQCoordinateMap p c m) z).toLinearMap| *
          g (originalQCoordinateMap p c m z) := lintegral_mono' (Measure.restrict_mono (fun z hz => hz.1) le_rfl) le_rfl
      _ = ∫⁻ y in Θ.target, g y := (hcov g).symm
      _ ≤ ∫⁻ y, g y := setLIntegral_le_lintegral _ g
      _ = _ := lintegral_indicator isClosed_closedBall.measurableSet dens
  exact hineq.trans_lt hfinite

end SGPT.Trace.BertiniUniversal
