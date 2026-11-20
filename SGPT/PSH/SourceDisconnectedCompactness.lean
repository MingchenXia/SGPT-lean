import SGPT.PSH.AnalyticGeneratorAlgebra
import SGPT.PSH.LocalL1Atlas
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! The two-point dimension-zero obstruction to original disconnected
compactness statements. All finite functions satisfy genuine source PSH. -/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.SourceDisconnectedCompactness

open Set Filter MeasureTheory
open VariableComplexAtlas
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology ContDiff ENNReal

/-- One actual complex dimension-zero chart for either original point. -/
def twoPointChart (b : Bool) : OpenPartialHomeomorph Bool (ComplexModel 0) where
  toFun := fun _ ↦ 0
  invFun := fun _ ↦ b
  source := {b}
  target := univ
  map_source' := by simp
  map_target' := by simp
  left_inv' := by intro x hx; exact (mem_singleton_iff.mp hx).symm
  right_inv' := by intro x _; exact Subsingleton.elim _ _
  open_source := isOpen_discrete _
  open_target := isOpen_univ
  continuousOn_toFun := continuous_const.continuousOn
  continuousOn_invFun := continuous_const.continuousOn

/-- The literal compact discrete two-point original manifold, with two
genuine zero-dimensional charts and actual holomorphic transitions. -/
def twoPointAtlas : VariableComplexAtlas Bool where
  Index := Bool
  dimension := fun _ ↦ 0
  chart := twoPointChart
  cover := fun b ↦ ⟨b, mem_singleton b⟩
  holomorphic := by
    intro i j
    change DifferentiableOn ℂ (fun _ : ComplexModel 0 ↦ (0 : ComplexModel 0)) _
    exact differentiableOn_const _

/-- The actual zero smooth closed real (1,1)-form in both original charts. -/
def twoPointZeroForm : AtlasClosedRealOneOneForm twoPointAtlas where
  coeff := fun _ _ ↦ 0
  smooth := fun _ ↦ contDiffOn_const
  compatible := by intro i j z hz w; simp
  closed := by
    intro i z hz
    ext w
    simp [extDeriv, ContinuousAlternatingMap.alternatizeUncurryFin_apply]
  typeOneOne := by intro i z hz v w; simp

/-- Every original open-subset test is a finite constant on its actual
one-point complex chart. -/
theorem twoPoint_finite_isPSHOn (f : Bool → ℝ) (U : Set Bool) :
    twoPointAtlas.IsPSHOn (fun b ↦ (f b : EReal)) U := by
  intro x hx
  refine ⟨x, mem_singleton x, univ, isOpen_univ, isConnected_univ, ?_, mem_univ _, ?_⟩
  · intro z _
    exact ⟨mem_univ _, hx⟩
  · exact pshOn_real_const (f x) univ_nonempty

/-- Every actual smooth local potential is tested; the original genuine
theta-PSH condition is never replaced by raw local regularity. -/
theorem twoPoint_finite_isThetaPSH (f : Bool → ℝ) :
    twoPointAtlas.IsThetaPSH twoPointZeroForm (fun b ↦ (f b : EReal)) := by
  refine ⟨fun b ↦ EReal.coe_ne_top _, ?_⟩
  intro U g _hg
  simpa only [EReal.coe_add] using twoPoint_finite_isPSHOn (fun b ↦ f b + g b) U

/-- Exact full original-domain dictionary: each zero-dimensional component
must have a finite value, rather than merely one global nonpole. -/
theorem twoPoint_isThetaPSH_iff_finite (u : Bool → EReal) :
    twoPointAtlas.IsThetaPSH twoPointZeroForm u ↔ ∀ b, ∃ a : ℝ, u b = (a : EReal) := by
  constructor
  · intro hu b
    have hq : twoPointAtlas.IsQPSH u := ⟨twoPointZeroForm, hu⟩
    obtain ⟨c, hc, hfin⟩ := hq.locallyNondegenerate b {b} (isOpen_discrete _) (mem_singleton _)
    have hc' : c = b := mem_singleton_iff.mp hc
    subst c
    exact ⟨(u b).toReal, (EReal.coe_toReal (hu.1 b) hfin).symm⟩
  · intro h
    choose f hf using h
    have heq : u = fun b ↦ (f b : EReal) := funext hf
    rw [heq]
    exact twoPoint_finite_isThetaPSH f

/-- The normalized decreasing original family, real-valued before embedding. -/
def twoPointRealFamily (k : ℕ) (b : Bool) : ℝ := if b then 0 else -(k : ℝ)

def twoPointFamily (k : ℕ) (b : Bool) : EReal := (twoPointRealFamily k b : EReal)

theorem twoPointFamily_isThetaPSH (k : ℕ) :
    twoPointAtlas.IsThetaPSH twoPointZeroForm (twoPointFamily k) :=
  twoPoint_finite_isThetaPSH (twoPointRealFamily k)

theorem twoPointFamily_antitone : Antitone twoPointFamily := by
  intro i j hij b
  cases b
  · exact EReal.coe_le_coe_iff.mpr (neg_le_neg (by exact_mod_cast hij))
  · exact le_rfl

theorem twoPointFamily_iSup (k : ℕ) : (⨆ b, twoPointFamily k b) = 0 := by
  apply le_antisymm
  · apply iSup_le
    intro b
    cases b
    · exact EReal.coe_le_coe_iff.mpr (neg_nonpos.mpr (Nat.cast_nonneg k))
    · exact le_rfl
  · exact le_iSup_of_le true le_rfl

theorem twoPointFamily_iInf_false : (⨅ k, twoPointFamily k false) = ⊥ := by
  apply le_bot_iff.mp
  apply le_of_forall_gt
  intro a ha
  obtain ⟨r, hrbot, hra⟩ := EReal.lt_iff_exists_real_btwn.mp ha
  obtain ⟨k, hk⟩ := exists_nat_gt (-r)
  have hlow : (⨅ j, twoPointFamily j false) ≤ twoPointFamily k false := iInf_le _ k
  apply hlow.trans_lt
  change ((-(k : ℝ) : ℝ) : EReal) < a
  exact (EReal.coe_lt_coe_iff.mpr (by linarith : -(k : ℝ) < r)).trans hra

/-- The pointwise infimum fails original local nondegeneracy on one actual
open component, despite every original supremum being zero. -/
theorem twoPointFamily_iInf_not_isQPSH :
    ¬ twoPointAtlas.IsQPSH (fun b ↦ ⨅ k, twoPointFamily k b) := by
  intro h
  obtain ⟨b, hb, hfin⟩ := h.locallyNondegenerate false {false} (isOpen_discrete _) (mem_singleton _)
  have hb' : b = false := mem_singleton_iff.mp hb
  subst b
  exact hfin twoPointFamily_iInf_false

/-- ALL actual original compact-manifold hypotheses and the decreasing
normalized family are supplied; the printed theta-PSH limit fails. -/
theorem twoPoint_decreasingnet_counterexample :
    CompactSpace Bool ∧ T2Space Bool ∧ ParacompactSpace Bool ∧
      (∀ k, twoPointAtlas.IsThetaPSH twoPointZeroForm (twoPointFamily k)) ∧
      Antitone twoPointFamily ∧ (∀ k, (⨆ b, twoPointFamily k b) = 0) ∧
      ¬ twoPointAtlas.IsThetaPSH twoPointZeroForm (fun b ↦ ⨅ k, twoPointFamily k b) := by
  refine ⟨inferInstance, inferInstance, inferInstance, twoPointFamily_isThetaPSH,
    twoPointFamily_antitone, twoPointFamily_iSup, ?_⟩
  exact fun h ↦ twoPointFamily_iInf_not_isQPSH ⟨twoPointZeroForm, h⟩

private theorem twoPoint_memLp (f : Bool → ℝ) :
    MemLp f 1 (Measure.count : Measure Bool) :=
  ⟨(measurable_of_finite f).aestronglyMeasurable, eLpNorm_lt_top_of_finite⟩

/-- The unchanged finite original function in actual counting-measure L¹. -/
def twoPointToL1 (f : Bool → ℝ) : Lp ℝ 1 (Measure.count : Measure Bool) :=
  (twoPoint_memLp f).toLp f

/-- Exact actual L¹ distance for ANY two original finite representatives. -/
theorem twoPointToL1_norm_sub (f g : Bool → ℝ) :
    ‖twoPointToL1 f - twoPointToL1 g‖ =
      |f false - g false| + |f true - g true| := by
  rw [twoPointToL1, twoPointToL1, ← MemLp.toLp_sub, Lp.norm_toLp,
    eLpNorm_one_eq_lintegral_enorm, lintegral_count, tsum_fintype]
  simp [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_add,
    abs_nonneg, add_comm]
  positivity

/-- The actual canonical chart volume in complex dimension zero is the
unit Dirac measure; no alternative Haar normalization is assumed. -/
theorem complexModelZero_volume_eq_dirac :
    (volume : Measure (ComplexModel 0)) = Measure.dirac 0 := by
  let e := (stdOrthonormalBasis ℝ (ComplexModel 0)).repr.symm
  let : IsEmpty (Fin (Module.finrank ℝ (ComplexModel 0))) := by
    simpa only [complexModel_real_finrank, Nat.mul_zero] using
      (inferInstance : IsEmpty (Fin 0))
  calc
    (volume : Measure (ComplexModel 0)) = Measure.map e volume :=
      e.measurePreserving.map_eq.symm
    _ = Measure.dirac 0 := by
      rw [volume_euclideanSpace_eq_dirac, Measure.map_dirac]
      simp

open Classical in
/-- Every actual compact-chart L¹ test is the original coordinate absolute
difference or zero, according to membership of the unique chart point. -/
theorem twoPoint_chart_integral_norm_sub (f g : Bool → ℝ) (b : Bool)
    (K : Set (ComplexModel 0)) :
    (∫ z in K, ‖(twoPointAtlas.coordinate (fun a ↦ (f a : EReal)) b z).toReal -
      (twoPointAtlas.coordinate (fun a ↦ (g a : EReal)) b z).toReal‖ ∂volume) =
      if (0 : ComplexModel 0) ∈ K then |f b - g b| else 0 := by
  classical
  rw [complexModelZero_volume_eq_dirac, restrict_dirac]
  split_ifs with hK
  · simp [coordinate, twoPointAtlas, twoPointChart, Real.norm_eq_abs]
    rfl
  · simp

/-- Exact bridge from the ORIGINAL variable-chart local-L¹ reader to the
actual counting-L¹ norm of the SAME finite functions. -/
theorem twoPoint_localL1_iff_norm (f : ℕ → Bool → ℝ) (g : Bool → ℝ) :
    twoPointAtlas.L1LocallyTendsto (fun k b ↦ (f k b : EReal)) (fun b ↦ (g b : EReal)) ↔
      Tendsto (fun k ↦ ‖twoPointToL1 (f k) - twoPointToL1 g‖) atTop (𝓝 0) := by
  classical
  have heq (k : ℕ) (b : Bool) (K : Set (ComplexModel (twoPointAtlas.dimension b))) :
      (∫ z in K, ‖(twoPointAtlas.coordinate (fun a ↦ (f k a : EReal)) b z).toReal -
        (twoPointAtlas.coordinate (fun a ↦ (g a : EReal)) b z).toReal‖ ∂volume) =
        if (0 : ComplexModel 0) ∈ K then |f k b - g b| else 0 :=
    twoPoint_chart_integral_norm_sub (f k) g b K
  constructor
  · intro h
    have hc : IsCompact (univ : Set (ComplexModel 0)) :=
      (show (univ : Set (ComplexModel 0)).Subsingleton from fun _ _ _ _ ↦ Subsingleton.elim _ _).isCompact
    have hp := h false univ hc (fun _ _ ↦ mem_univ _)
    have hq := h true univ hc (fun _ _ ↦ mem_univ _)
    have hp' : Tendsto (fun k ↦ |f k false - g false|) atTop (𝓝 0) :=
      hp.congr' (Eventually.of_forall fun k ↦
        (heq k false univ).trans (if_pos (mem_univ (0 : ComplexModel 0))))
    have hq' : Tendsto (fun k ↦ |f k true - g true|) atTop (𝓝 0) :=
      hq.congr' (Eventually.of_forall fun k ↦
        (heq k true univ).trans (if_pos (mem_univ (0 : ComplexModel 0))))
    simpa only [twoPointToL1_norm_sub, add_zero] using hp'.add hq'
  · intro h b K _hK _hsub
    have hcoord : Tendsto (fun k ↦ |f k b - g b|) atTop (𝓝 0) := by
      apply squeeze_zero (fun k ↦ abs_nonneg _) ?_ h
      intro k
      rw [twoPointToL1_norm_sub]
      cases b
      · exact le_add_of_nonneg_right (abs_nonneg _)
      · exact le_add_of_nonneg_left (abs_nonneg _)
    have hfun : (fun k ↦ ∫ z in K,
        ‖(twoPointAtlas.coordinate (fun a ↦ (f k a : EReal)) b z).toReal -
          (twoPointAtlas.coordinate (fun a ↦ (g a : EReal)) b z).toReal‖ ∂volume) =
        fun k ↦ if (0 : ComplexModel 0) ∈ K then |f k b - g b| else 0 :=
      funext fun k ↦ heq k b K
    rw [hfun]
    split_ifs
    · exact hcoord
    · exact tendsto_const_nhds

/-- The complete original chart-local convergence agrees with convergence
in the actual counting-measure L¹ topology on this original source domain. -/
theorem twoPoint_localL1_iff_tendsto_L1 (f : ℕ → Bool → ℝ) (g : Bool → ℝ) :
    twoPointAtlas.L1LocallyTendsto (fun k b ↦ (f k b : EReal)) (fun b ↦ (g b : EReal)) ↔
      Tendsto (fun k ↦ twoPointToL1 (f k)) atTop (𝓝 (twoPointToL1 g)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact twoPoint_localL1_iff_norm f g

/-- The SAME real representatives in the actual counting-measure L¹ space. -/
def twoPointL1Family (k : ℕ) : Lp ℝ 1 (Measure.count : Measure Bool) :=
  (twoPoint_memLp (twoPointRealFamily k)).toLp (twoPointRealFamily k)

/-- The literal actual L¹ norm of the unchanged normalized source family. -/
theorem twoPointL1Family_norm (k : ℕ) : ‖twoPointL1Family k‖ = (k : ℝ) := by
  rw [twoPointL1Family, Lp.norm_toLp, eLpNorm_one_eq_lintegral_enorm, lintegral_count,
    tsum_fintype]
  simp [twoPointRealFamily]

/-- No actual compact L¹ subset can contain all these original normalized
theta-PSH functions. -/
theorem twoPointL1Family_not_contained_in_compact :
    ¬ ∃ K : Set (Lp ℝ 1 (Measure.count : Measure Bool)),
      IsCompact K ∧ range twoPointL1Family ⊆ K := by
  rintro ⟨K, hK, hsub⟩
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn continuous_norm.continuousOn
  obtain ⟨k, hk⟩ := exists_nat_gt C
  have hb := hC (twoPointL1Family k) (hsub ⟨k, rfl⟩)
  simp only [Real.norm_eq_abs, twoPointL1Family_norm,
    abs_of_nonneg (show (0 : ℝ) ≤ k from Nat.cast_nonneg k)] at hb
  exact (not_le_of_gt hk) hb

/-- The literal original normalized domain, embedded in its actual L¹ space. -/
def twoPointNormalizedL1 : Set (Lp ℝ 1 (Measure.count : Measure Bool)) :=
  {F | ∃ f : Bool → ℝ,
    twoPointAtlas.IsThetaPSH twoPointZeroForm (fun b ↦ (f b : EReal)) ∧
    (⨆ b, (f b : EReal)) = 0 ∧ F = (twoPoint_memLp f).toLp f}

/-- An actual disconnected compact original complex-manifold counterexample
to the printed global-supremum L¹ compactness assertion `prop:L1compa`. -/
theorem twoPointNormalizedL1_not_isCompact : ¬ IsCompact twoPointNormalizedL1 := by
  intro hK
  apply twoPointL1Family_not_contained_in_compact
  refine ⟨twoPointNormalizedL1, hK, ?_⟩
  rintro F ⟨k, rfl⟩
  exact ⟨twoPointRealFamily k, twoPointFamily_isThetaPSH k, twoPointFamily_iSup k, rfl⟩

end SGPT.PSH.SourceDisconnectedCompactness
