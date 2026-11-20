import SGPT.PSH.LocalL1
import SGPT.PSH.LocalManifold
import SGPT.PSH.Pluripolar
import SGPT.Foundations.Analysis.Pending.SkodaIntegrability
import SGPT.Foundations.Analysis.Pending.PshLogExponentBound
import Mathlib.Probability.Moments.IntegrableExpMul

namespace SGPT.PSH
open Set Filter Metric MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.BergmanSupWeight
open SGPT.Foundations.Analysis.Pending.SkodaIntegrability
open scoped Topology ENNReal

/-- A genuine PSH germ with a real finite point away from the center admits an
actual nonvanishing weighted Bergman member at some produced positive level.
The existing logarithmic bound and local Skoda estimate are reused. -/
theorem exists_nonzero_bergman_member {n : ℕ} {U : Set (ComplexModel n)}
    {u : ComplexModel n → EReal} (hu : PlurisubharmonicOn u U)
    {p : ComplexModel n} {R : ℝ} (hR : 0 < R) (hclosed : closedBall p R ⊆ U)
    {y : ComplexModel n} (hy : ‖y - p‖ < R) (hyp : y ≠ p) (huy : u y ≠ ⊥) :
    ∃ c : ℝ, 0 < c ∧ ∃ f ∈ bergmanBall (ball p R) (fun z ↦ multiplierWeight c (u z)),
      f p ≠ 0 := by
  obtain ⟨S, hS⟩ := Pending.PshLogExponentBound.exists_bound_forall_log_exponent
    (hu.mono (ball_subset_closedBall.trans hclosed)) hy hyp huy
  let c : ℝ := 1 / (max S 0 + 1)
  have hden : 0 < max S 0 + 1 := by linarith [le_max_right S 0]
  have hc : 0 < c := one_div_pos.mpr hden
  have hlarge : S < 2 / c := by
    have heq : 2 / c = 2 * (max S 0 + 1) := by dsimp [c]; field_simp
    rw [heq]
    linarith [le_max_left S 0, le_max_right S 0]
  refine ⟨c, hc, ?_⟩
  by_contra hnot
  have hvan : ∀ f ∈ bergmanBall (ball p R)
      (fun z ↦ multiplierWeight 1 ((c : EReal) * u z)), f p = 0 := by
    intro f hf
    have hf' : f ∈ bergmanBall (ball p R) (fun z ↦ multiplierWeight c (u z)) := by
      simpa only [multiplierWeight_one_mul] using hf
    by_contra hfp
    exact hnot ⟨f, hf', hfp⟩
  obtain ⟨r, C, hr, hbound⟩ :=
    exists_log_bound_of_forall_bergmanBall_vanish (hu.const_mul hc) hR hclosed hvan
  have hle : 2 / c ≤ S := hS (2 / c) (C / c) r hr (by
    intro z hz0 hzlt
    have hzneq : z ≠ p := sub_ne_zero.mp (norm_pos_iff.mp hz0)
    have hb := hbound z (mem_ball_iff_norm.mpr hzlt) hzneq
    induction hv : u z using EReal.rec with
    | bot => exact bot_le
    | top =>
      rw [hv, EReal.coe_mul_top_of_pos hc] at hb
      exact False.elim (EReal.coe_ne_top _ (top_le_iff.mp hb))
    | coe t =>
      rw [hv, ← EReal.coe_mul, EReal.coe_le_coe_iff] at hb
      rw [EReal.coe_le_coe_iff]
      apply (mul_le_mul_iff_of_pos_right hc).mp
      have heq : ((2 / c) * Real.log ‖z - p‖ + C / c) * c =
          2 * Real.log ‖z - p‖ + C := by field_simp
      rw [heq]
      nlinarith [hb])
  exact hlarge.not_ge hle

/-- Actual nonvanishing of an original Bergman member supplies a local finite
integral of the original weight, with no integrability certificate assumed. -/
theorem exists_finite_weight_ball_of_nonzero_bergman {n : ℕ}
    {p : ComplexModel n} {R : ℝ} (hR : 0 < R)
    {w : ComplexModel n → ℝ≥0∞} {f : ComplexModel n → ℂ}
    (hf : f ∈ bergmanBall (ball p R) w) (hfp : f p ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ r ≤ R ∧ (∫⁻ z in ball p r, w z) < ⊤ := by
  have hnorm : 0 < ‖f p‖ := norm_pos_iff.mpr hfp
  have hcont := (hf.1.continuousOn p (mem_ball_self hR)).continuousAt
    (isOpen_ball.mem_nhds (mem_ball_self hR))
  have hev : ∀ᶠ z in 𝓝 p, ‖f p‖ / 2 ≤ ‖f z‖ :=
    hcont.norm.eventually_const_le (by linarith)
  obtain ⟨s, hs, hsbound⟩ := Metric.eventually_nhds_iff.mp hev
  let r : ℝ := min s R
  have hr : 0 < r := lt_min hs hR
  have hα : 0 < ENNReal.ofReal ((‖f p‖ / 2) ^ 2) :=
    ENNReal.ofReal_pos.mpr (sq_pos_of_pos (by linarith))
  let α : ℝ≥0∞ := ENNReal.ofReal ((‖f p‖ / 2) ^ 2)
  have hα0 : α ≠ 0 := hα.ne'
  have hαtop : α ≠ ⊤ := ENNReal.ofReal_ne_top
  refine ⟨r, hr, min_le_right _ _, ?_⟩
  calc
    (∫⁻ z in ball p r, w z) ≤
        ∫⁻ z in ball p r, α⁻¹ * (ENNReal.ofReal (‖f z‖ ^ 2) * w z) := by
      apply setLIntegral_mono' measurableSet_ball
      intro z hz
      have hlow : ‖f p‖ / 2 ≤ ‖f z‖ := hsbound
        (lt_of_lt_of_le (mem_ball.mp hz) (min_le_left s R))
      have hcoeff : α ≤ ENNReal.ofReal (‖f z‖ ^ 2) :=
        ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (by positivity) hlow 2)
      have hmul : α * w z ≤ ENNReal.ofReal (‖f z‖ ^ 2) * w z :=
        mul_le_mul' hcoeff le_rfl
      have hcan : α⁻¹ * (α * w z) = w z := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hα0 hαtop, one_mul]
      calc w z = α⁻¹ * (α * w z) := hcan.symm
           _ ≤ α⁻¹ * (ENNReal.ofReal (‖f z‖ ^ 2) * w z) :=
             mul_le_mul' le_rfl hmul
    _ = α⁻¹ * ∫⁻ z in ball p r, ENNReal.ofReal (‖f z‖ ^ 2) * w z :=
      lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr hα0)
    _ ≤ α⁻¹ * 1 := by
      exact mul_le_mul' le_rfl ((lintegral_mono_set
        (ball_subset_ball (min_le_right s R))).trans hf.2)
    _ < ⊤ := by rw [mul_one]; exact ENNReal.inv_lt_top.mpr hα

/-- Genuine source PSH on a connected open positive-dimensional domain
produces a positive local multiplier level with finite original weight integral. -/
theorem PSHOn.exists_finite_weight_ball {n : ℕ} [Nontrivial (ComplexModel n)]
    {u : ComplexModel n → EReal} {U : Set (ComplexModel n)}
    (hu : PSHOn u U) (hU : IsOpen U) (hconn : IsPreconnected U)
    {p : ComplexModel n} (hp : p ∈ U) :
    ∃ c r : ℝ, 0 < c ∧ 0 < r ∧ ball p r ⊆ U ∧
      (∫⁻ z in ball p r, multiplierWeight c (u z)) < ⊤ := by
  obtain ⟨R, hR, hclosed⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hp)
  have hraw := hu.disc.plurisubharmonicOn hU
  have hfin := hu.ae_finite_on_compact hU hconn volume (isCompact_closedBall p R) hclosed
  have hfinB := ae_restrict_of_ae_restrict_of_subset ball_subset_closedBall hfin
  have hneq : ∀ᵐ z ∂(volume : Measure (ComplexModel n)), z ≠ p := by
    simp [ae_iff]
  obtain ⟨y, hyB, hyfin, hyp⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (measure_ball_pos volume p hR).ne' (hfinB.and (ae_restrict_of_ae hneq))
  obtain ⟨c, hc, f, hf, hfp⟩ := exists_nonzero_bergman_member hraw hR hclosed
    (mem_ball_iff_norm.mp hyB) hyp hyfin.2
  obtain ⟨r, hr, hrR, hweight⟩ := exists_finite_weight_ball_of_nonzero_bergman hR hf hfp
  exact ⟨c, r, hc, hr, (ball_subset_ball hrR).trans
    (ball_subset_closedBall.trans hclosed), hweight⟩

/-- Actual AE-finite source values identify the original weight with the real
negative exponential; a compact PSH upper bound supplies the positive moment. -/
theorem memLp_on_ball_of_finite_weight {n : ℕ}
    {u : ComplexModel n → EReal} {U : Set (ComplexModel n)}
    (hu : PlurisubharmonicOn u U) {p : ComplexModel n} {R c q : ℝ}
    (hclosed : closedBall p R ⊆ U) (hc : 0 < c) (hq : 0 < q)
    (hfin : ∀ᵐ z ∂volume.restrict (ball p R), u z ≠ ⊤ ∧ u z ≠ ⊥)
    (hmeas : AEStronglyMeasurable (fun z ↦ (u z).toReal) (volume.restrict (ball p R)))
    (hw : (∫⁻ z in ball p R, multiplierWeight c (u z)) < ⊤) :
    MemLp (fun z ↦ (u z).toReal) (ENNReal.ofReal q) (volume.restrict (ball p R)) := by
  let μ : Measure (ComplexModel n) := volume.restrict (ball p R)
  let : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  have hposmeas : AEStronglyMeasurable (fun z ↦ Real.exp (c * (u z).toReal)) μ :=
    (Real.measurable_exp.comp_aemeasurable (hmeas.aemeasurable.const_mul c)).aestronglyMeasurable
  have hnegmeas : AEStronglyMeasurable (fun z ↦ Real.exp (-c * (u z).toReal)) μ :=
    (Real.measurable_exp.comp_aemeasurable (hmeas.aemeasurable.const_mul (-c))).aestronglyMeasurable
  have hweight_eq : (fun z ↦ ENNReal.ofReal (Real.exp (-c * (u z).toReal))) =ᵐ[μ]
      (fun z ↦ multiplierWeight c (u z)) := by
    filter_upwards [hfin] with z hz
    rw [← EReal.coe_toReal hz.1 hz.2, multiplierWeight_coe]
    simp only [EReal.toReal_coe, neg_mul]
  have hneg : Integrable (fun z ↦ Real.exp (-c * (u z).toReal)) μ := by
    apply (lintegral_ofReal_ne_top_iff_integrable hnegmeas
      (ae_of_all _ (fun z ↦ (Real.exp_pos _).le))).mp
    rw [lintegral_congr_ae hweight_eq]
    exact hw.ne
  obtain ⟨C, _, hC⟩ := hu.exists_nonnegative_compact_upper_bound
    (isCompact_closedBall p R) hclosed
  have hpos : Integrable (fun z ↦ Real.exp (c * (u z).toReal)) μ := by
    apply (integrable_const (Real.exp (c * C))).mono' hposmeas
    filter_upwards [hfin, ae_restrict_mem measurableSet_ball] with z hz hzB
    simp only [Real.norm_eq_abs, Real.abs_exp]
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_left _ hc.le
    have hbound := hC z (ball_subset_closedBall hzB)
    rw [← EReal.coe_toReal hz.1 hz.2, EReal.coe_le_coe_iff] at hbound
    exact hbound
  apply (integrable_norm_rpow_iff hmeas (by simp [hq]) ENNReal.ofReal_ne_top).mp
  simpa only [ENNReal.toReal_ofReal hq.le, Real.norm_eq_abs] using
    ProbabilityTheory.integrable_rpow_abs_of_integrable_exp_mul hc.ne' hpos hneg hq.le

/-- Every source PSH point in positive dimension has actual AE-finite original
values and all finite positive-power moments on a produced original ball. -/
theorem PSHOn.exists_memLp_ball_positive_dim {n : ℕ} [Nontrivial (ComplexModel n)]
    {u : ComplexModel n → EReal} {U : Set (ComplexModel n)}
    (hu : PSHOn u U) (hU : IsOpen U) (hconn : IsPreconnected U)
    {p : ComplexModel n} (hp : p ∈ U) {q : ℝ} (hq : 0 < q) :
    ∃ R : ℝ, 0 < R ∧ ball p R ⊆ U ∧
      (∀ᵐ z ∂volume.restrict (ball p R), u z ≠ ⊤ ∧ u z ≠ ⊥) ∧
      MemLp (fun z ↦ (u z).toReal) (ENNReal.ofReal q) (volume.restrict (ball p R)) := by
  have hraw := hu.disc.plurisubharmonicOn hU
  obtain ⟨V, hV, hpV, hfinV, hIV⟩ :=
    hraw.subset_pshIntegrabilityLocus volume hconn hu.nontrivial hp
  obtain ⟨c, r, hc, hr, hrU, hw⟩ := hu.exists_finite_weight_ball hU hconn hp
  obtain ⟨R, hR, hclosed⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    ((hV.inter isOpen_ball).mem_nhds ⟨hpV, mem_ball_self hr⟩)
  have hball : ball p R ⊆ V ∩ ball p r := ball_subset_closedBall.trans hclosed
  have hRU : closedBall p R ⊆ U := fun z hz ↦ hrU (hclosed hz).2
  have hfinR := ae_restrict_of_ae_restrict_of_subset
    (hball.trans inter_subset_left) hfinV
  have hIR := hIV.mono_set (hball.trans inter_subset_left)
  have hwR : (∫⁻ z in ball p R, multiplierWeight c (u z)) < ⊤ :=
    (lintegral_mono_set (hball.trans inter_subset_right)).trans_lt hw
  exact ⟨R, hR, (ball_subset_closedBall.trans hRU), hfinR,
    memLp_on_ball_of_finite_weight hraw hRU hc hq hfinR hIR.aestronglyMeasurable hwR⟩

/-- The source local-Lp producer includes the genuine finite singleton case
in dimension zero and all positive-dimensional source PSH germs. -/
theorem PSHOn.exists_memLp_ball {n : ℕ}
    {u : ComplexModel n → EReal} {U : Set (ComplexModel n)}
    (hu : PSHOn u U) (hU : IsOpen U) (hconn : IsPreconnected U)
    {p : ComplexModel n} (hp : p ∈ U) {q : ℝ} (hq : 0 < q) :
    ∃ R : ℝ, 0 < R ∧ ball p R ⊆ U ∧
      (∀ᵐ z ∂volume.restrict (ball p R), u z ≠ ⊤ ∧ u z ≠ ⊥) ∧
      MemLp (fun z ↦ (u z).toReal) (ENNReal.ofReal q) (volume.restrict (ball p R)) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst n
    have htop : u p ≠ ⊤ := (hu.disc.plurisubharmonicOn hU p hp).ne_top
    have hbot : u p ≠ ⊥ := by
      obtain ⟨y, _, hy⟩ := hu.nontrivial
      simpa only [Subsingleton.elim y p] using hy
    have hu_eq : u = fun _ ↦ u p := funext (fun z ↦ congrArg u (Subsingleton.elim z p))
    refine ⟨1, one_pos, (fun z _ ↦ ?_), ?_, ?_⟩
    · simpa only [Subsingleton.elim z p] using hp
    · exact ae_of_all _ (fun z ↦ by simpa only [Subsingleton.elim z p] using And.intro htop hbot)
    · rw [hu_eq]
      exact memLp_const _
  · let : NeZero n := ⟨hn.ne'⟩
    exact hu.exists_memLp_ball_positive_dim hU hconn hp hq

namespace VariableComplexAtlas
variable {X : Type*} [TopologicalSpace X] {A : VariableComplexAtlas X}

/-- Actual local Lp on every original coordinate chart, together with original
AE-finite source values; chart dimensions and component counts are unrestricted. -/
def CoordinateLocallyMemLp (A : VariableComplexAtlas X) (u : X → EReal) (q : ℝ) : Prop :=
  ∀ i : A.Index, ∀ z ∈ (A.chart i).target, ∃ r : ℝ, 0 < r ∧
    ball z r ⊆ (A.chart i).target ∧
    (∀ᵐ y ∂volume.restrict (ball z r), A.coordinate u i y ≠ ⊤ ∧ A.coordinate u i y ≠ ⊥) ∧
    MemLp (fun y ↦ (A.coordinate u i y).toReal) (ENNReal.ofReal q)
      (volume.restrict (ball z r))

/-- Genuine original source PSH produces actual local Lp in each original
chart for every finite positive real exponent, including zero-dimensional charts. -/
theorem IsPSH.coordinateLocallyMemLp {u : X → EReal} (hu : A.IsPSH u)
    {q : ℝ} (hq : 0 < q) : A.CoordinateLocallyMemLp u q := by
  intro i z hz
  obtain ⟨R, hR, hclosed⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    ((A.chart i).open_target.mem_nhds hz)
  have hball : ball z R ⊆ (A.chart i).target := ball_subset_closedBall.trans hclosed
  have hn := LocallyNondegenerate.exists_coordinate_ne_bot hu.locallyNondegenerate
    (A.chart i) isOpen_ball hball (mem_ball_self hR)
  have hpsh : PSHOn (A.coordinate u i) (ball z R) :=
    ⟨(hu.chartPlurisubharmonic i).discPshOn.mono hball, hn⟩
  obtain ⟨r, hr, hrB, hfin, hLp⟩ := hpsh.exists_memLp_ball isOpen_ball
    (isConnected_ball hR).isPreconnected (mem_ball_self hR) hq
  exact ⟨r, hr, hrB.trans hball, hfin, hLp⟩

/-- Actual real-power local integrability, a coordinate definition of the
original local Lp conclusion with no exponent/integral certificate assumed. -/
theorem IsPSH.coordinate_locallyIntegrable_norm_rpow {u : X → EReal} (hu : A.IsPSH u)
    (i : A.Index) {q : ℝ} (hq : 0 < q) :
    LocallyIntegrableOn (fun z ↦ ‖(A.coordinate u i z).toReal‖ ^ q)
      (A.chart i).target volume := by
  intro z hz
  obtain ⟨r, hr, _, _, hLp⟩ := hu.coordinateLocallyMemLp hq i z hz
  refine ⟨ball z r, mem_nhdsWithin_of_mem_nhds (isOpen_ball.mem_nhds (mem_ball_self hr)), ?_⟩
  have hpow := (integrable_norm_rpow_iff hLp.aestronglyMeasurable
    (by simp [hq]) ENNReal.ofReal_ne_top).mpr hLp
  simpa only [IntegrableOn, ENNReal.toReal_ofReal hq.le] using hpow

/-- Reuse the source pluripolar witness definition with the original PSH
function itself; no new pole-nullity proof is introduced. -/
theorem IsPSH.locallyPluripolar_pole_locus {u : X → EReal} (hu : A.IsPSH u) :
    A.LocallyPluripolar {x | u x = ⊥} := by
  intro x
  exact ⟨univ, isOpen_univ, mem_univ x, u, isPSHOn_univ_iff.mpr hu,
    fun y hy ↦ hy.1⟩

/-- Existing genuine pluripolar outer-nullity gives AE-finite original values
in every original chart, with no measurability or countability assumption on X. -/
theorem IsPSH.coordinate_ae_finite {u : X → EReal} (hu : A.IsPSH u) (i : A.Index) :
    ∀ᵐ z ∂volume.restrict (A.chart i).target,
      A.coordinate u i z ≠ ⊤ ∧ A.coordinate u i z ≠ ⊥ := by
  filter_upwards [hu.locallyPluripolar_pole_locus.ae_notMem_in_chart i volume] with z hz
  exact ⟨hu.ne_top ((A.chart i).symm z), hz⟩

/-- The actual source all-power producer at exponent one gives local real
integrability, used only for its existing strong-measurability consequence. -/
theorem IsPSH.coordinate_locallyIntegrable_toReal {u : X → EReal} (hu : A.IsPSH u)
    (i : A.Index) :
    LocallyIntegrableOn (fun z ↦ (A.coordinate u i z).toReal) (A.chart i).target volume := by
  intro z hz
  obtain ⟨r, hr, _, _, hLp⟩ := hu.coordinateLocallyMemLp one_pos i z hz
  refine ⟨ball z r, mem_nhdsWithin_of_mem_nhds (isOpen_ball.mem_nhds (mem_ball_self hr)), ?_⟩
  apply memLp_one_iff_integrable.mp
  simpa only [ENNReal.ofReal_one] using hLp

/-- Actual compact-coordinate Lp follows from the produced local power
integrals through Mathlib's compact local-integrability theorem. -/
theorem IsPSH.coordinate_memLp_on_compact {u : X → EReal} (hu : A.IsPSH u)
    (i : A.Index) {K : Set (ComplexModel (A.dimension i))}
    (hK : IsCompact K) (hKT : K ⊆ (A.chart i).target) {q : ℝ} (hq : 0 < q) :
    MemLp (fun z ↦ (A.coordinate u i z).toReal) (ENNReal.ofReal q) (volume.restrict K) := by
  have hmeas := (hu.coordinate_locallyIntegrable_toReal i).mono_set hKT
    |>.aestronglyMeasurable
  have hpow := (hu.coordinate_locallyIntegrable_norm_rpow i hq).integrableOn_compact_subset hKT hK
  apply (integrable_norm_rpow_iff hmeas (by simp [hq]) ENNReal.ofReal_ne_top).mp
  simpa only [IntegrableOn, ENNReal.toReal_ofReal hq.le] using hpow

/-- Original local Lp tested on every actual compact subset of each original
coordinate chart, with genuine AE-finite source values. -/
def CoordinateLocalLp (A : VariableComplexAtlas X) (u : X → EReal) (q : ℝ) : Prop :=
  ∀ i : A.Index, ∀ K : Set (ComplexModel (A.dimension i)), IsCompact K →
    K ⊆ (A.chart i).target →
    (∀ᵐ z ∂volume.restrict K, A.coordinate u i z ≠ ⊤ ∧ A.coordinate u i z ≠ ⊥) ∧
    MemLp (fun z ↦ (A.coordinate u i z).toReal) (ENNReal.ofReal q) (volume.restrict K)

/-- Exact source prop:pshlocLp for every finite real p ≥ 1, on the original
manifold with arbitrary varying dimensions, components and empty-space case. -/
theorem IsPSH.localLp_of_one_le {u : X → EReal} (hu : A.IsPSH u)
    {q : ℝ} (hq : 1 ≤ q) : A.CoordinateLocalLp u q := by
  intro i K hK hKT
  exact ⟨ae_restrict_of_ae_restrict_of_subset hKT (hu.coordinate_ae_finite i),
    hu.coordinate_memLp_on_compact i hK hKT (lt_of_lt_of_le one_pos hq)⟩

end VariableComplexAtlas

end SGPT.PSH
