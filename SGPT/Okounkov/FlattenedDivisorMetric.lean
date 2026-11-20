import SGPT.Okounkov.SmoothDivisorResidual
import SGPT.Foundations.Analysis.Pending.DivisorMetric
import SGPT.Foundations.Analysis.Pending.EmbeddedFromResolution
import SGPT.Foundations.Analysis.Pending.MeteredDivisorSmoothOffSupport
import SGPT.Foundations.Analysis.Pending.BlowupExistenceCodimOne
import SGPT.Foundations.Analysis.Pending.VanishingIdealZeroLocus

set_option autoImplicit false

noncomputable section

namespace SGPT.Okounkov

open Set Filter
open scoped Topology Manifold ContDiff ENNReal
open SGPT.Foundations.Analysis
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending
open BlowupFlatCoordinates
open VanishingIdealCoherent
open ChartPartition
open FactorizedWeightForm
open FirstPass.PositiveClasses

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

/-- Actual regular-point dimension rules out ordinary interior of the original
smooth codimension-one carrier. -/
theorem smooth_divisor_interior_eq_empty {W : Set M}
    (hW : IsClosedConnectedSubmanifold (m + 1) W m) : interior W = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hfull := EmbeddedFromResolution.regularAtDim_of_mem_nhds (n := m + 1)
    (mem_interior_iff_mem_nhds.mp hx)
  have heq := RegularPointDimension.eq_of_regularAtDim
    (hW.2.2 x (interior_subset hx)) hfull
  omega

variable {p : M}
  (Φ : LocalHolomorphicEquivAt (n := m + 1)
    (chartAt (ComplexModel (m + 1)) p p))
  (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel (m + 1)) p).target)
  {W : Set M}
  (hflat : ∀ {y : M}, y ∈ (chartAt (ComplexModel (m + 1)) p).source →
    chartAt (ComplexModel (m + 1)) p y ∈ Φ.source →
    (y ∈ W ↔ Φ.toFun (chartAt (ComplexModel (m + 1)) p y) ∈
      complexCoordinatePlane (m + 1) m))

include hΦsrc hflat in
/-- Main's actual Hadamard producer specializes to the same chosen last
flattening coordinate, with the literal original vanishing ideal. -/
theorem flat_last_generates_vanishingIdeal {y : M} (hy : y ∈ flatDomain Φ)
    (a : M → ℂ) :
    (vanishingIdeal (n := m + 1) W).mem y a ↔
      IsInSpanAt (n := m + 1) (· = flatCoord Φ (Fin.last m)) y a := by
  constructor
  · intro ha
    obtain ⟨b, hb0, hbhol, hbeq⟩ := exists_eq_sum_flatCoord Φ hΦsrc hflat hy ha
    refine isInSpanAt_of_eq_mul rfl ha.1 (hbhol (Fin.last m)) ?_
    filter_upwards [hbeq] with y' hy'
    rw [hy', Finset.sum_eq_single (Fin.last m)]
    · intro i _ hi
      have hilast : i.val ≠ m := fun h => hi (Fin.ext h)
      rw [hb0 i (by have := i.isLt; omega)]
      simp
    · simp
  · intro ha
    exact mem_vanishingIdeal_of_isInSpanAt
      (g := fun _ : Fin 1 => flatCoord Φ (Fin.last m))
      (fun _ => flatCoord_mem_vanishingIdeal Φ hflat (by simp) hy)
      (ha.mono fun s hs => ⟨0, hs.symm⟩)

include hflat in
/-- The chosen generator is genuinely nonzero on every nonempty open piece;
this is produced from the original carrier, not imposed as a unit certificate. -/
theorem flat_last_nonzero_on_open
    (hW : IsClosedConnectedSubmanifold (m + 1) W m)
    (O : Set M) (hO : IsOpen O) (hOF : O ⊆ flatDomain Φ) (hne : O.Nonempty) :
    ∃ y ∈ O, flatCoord Φ (Fin.last m) y ≠ 0 := by
  by_contra h
  push Not at h
  obtain ⟨x, hx⟩ := hne
  have hOW : O ⊆ W := by
    intro y hy
    have hyF := hOF hy
    apply (hflat hyF.1 hyF.2).mpr
    exact (mem_codimension_one_plane_iff _).mpr (h y hy)
  have hxI : x ∈ interior W := mem_interior.mpr ⟨O, hOW, hO, hx⟩
  rw [smooth_divisor_interior_eq_empty hW] at hxI
  exact hxI

include hΦsrc hflat in
/-- A genuine smooth divisor metric has its actual extended-logarithmic normal
form in the same chosen flattening. Main's unit-change theorem produces the
nowhere-zero factor; all original divisor points are retained in the identity. -/
theorem exists_divisor_metric_flat_normal_form
    (hW : IsClosedConnectedSubmanifold (m + 1) W m)
    (D : EffectiveDivisor (m + 1) M) (hD : D.ideal = vanishingIdeal (n := m + 1) W)
    (E : MeteredEffectiveQDivisor (m + 1) M) (hE : DivisorMetric.IsDivisorMetric D E) :
    ∃ (V : Set M) (ell : M → ℝ), IsOpen V ∧ p ∈ V ∧ V ⊆ flatDomain Φ ∧
      (∀ e : ComplexChart (m + 1) M, ContDiffOn ℝ ∞
        (fun z => ell (e.val.symm z)) (e.val.target ∩ e.val.symm ⁻¹' V)) ∧
      (∀ y ∈ V, E.weight y = logNormSq (flatCoord Φ (Fin.last m) y) + (ell y : EReal)) := by
  obtain ⟨U, hU, hpU, g, hgd, hgen, h, hh, hweight⟩ := hE p
  have hgenF : ∀ y ∈ flatDomain Φ, ∀ a,
      D.ideal.mem y a ↔ IsInSpanAt (n := m + 1) (· = flatCoord Φ (Fin.last m)) y a := by
    intro y hy a
    rw [hD]
    exact flat_last_generates_vanishingIdeal Φ hΦsrc hflat hy a
  obtain ⟨V, unit, hV, hpV, hVU, hunitd, hunit0, hunitg⟩ :=
    DivisorMetric.exists_unit_of_generators (isOpen_flatDomain Φ) hU
      (fun y hy => (holomorphicAt_flatCoord Φ (Fin.last m) hy).mdifferentiableAt.mdifferentiableWithinAt)
      hgd (flat_last_nonzero_on_open Φ hflat hW) hgenF hgen
      (mem_flatDomain_self Φ) hpU
  refine ⟨V, fun y => Real.log (Complex.normSq (unit y)) + h y,
    hV, hpV, fun y hy => (hVU hy).1, ?_, ?_⟩
  · intro e z hz
    have hopen : IsOpen (e.val.target ∩ e.val.symm ⁻¹' V) :=
      e.val.isOpen_inter_preimage_symm hV
    have hnorm : ContDiffAt ℝ ∞ (fun w => Complex.normSq (unit (e.val.symm w))) z := by
      apply BlanchardWeight.BlanchardData.contDiffAt_normSq_comp
      filter_upwards [hopen.mem_nhds hz] with w hw
      exact differentiableAt_comp_chart_symm e hw.1 (hunitd _ hw.2)
    exact ((hnorm.log (Complex.normSq_pos.mpr (hunit0 _ hz.2)).ne').contDiffWithinAt).add
      ((hh e z ⟨hz.1, (hVU hz.2).2⟩).mono
        (fun w hw => ⟨hw.1, (hVU hw.2).2⟩))
  · intro y hy
    rw [hweight y (hVU hy).2, generatorLog_eq_log_sum]
    simp only [Fin.sum_univ_one, hunitg y hy, norm_mul, mul_pow, logNormSq]
    rw [ENNReal.ofReal_mul (sq_nonneg _), ENNReal.log_mul_add,
      ENNReal.log_ofReal_of_pos (pow_pos (norm_pos_iff.mpr (hunit0 y hy)) 2)]
    simp only [← Complex.normSq_eq_norm_sq, EReal.coe_add]
    ac_rfl

include hflat in
/-- The actual metric curvature is the negative ddC of the produced correction
on the whole original chart neighborhood, including the divisor. The equality
off the divisor extends by genuine density and smoothness. -/
theorem curvature_eq_neg_smoothDDC_flat_normal_form
    (hW : IsClosedConnectedSubmanifold (m + 1) W m)
    (E : MeteredEffectiveQDivisor (m + 1) M)
    {V : Set M} (hV : IsOpen V) (hVF : V ⊆ flatDomain Φ)
    (ell : M → ℝ)
    (hell : ∀ e : ComplexChart (m + 1) M, ContDiffOn ℝ ∞
      (fun z => ell (e.val.symm z)) (e.val.target ∩ e.val.symm ⁻¹' V))
    (hweight : ∀ y ∈ V,
      E.weight y = logNormSq (flatCoord Φ (Fin.last m) y) + (ell y : EReal))
    (e : ComplexChart (m + 1) M) {z : ComplexModel (m + 1)}
    (hz : z ∈ e.val.target ∩ e.val.symm ⁻¹' V) :
    E.curvature.val.coeff e z = -smoothDDC (fun w => ell (e.val.symm w)) z := by
  let S := e.val.target ∩ e.val.symm ⁻¹' V
  let F : ComplexModel (m + 1) → ℂ := fun w => flatCoord Φ (Fin.last m) (e.val.symm w)
  have hS : IsOpen S := e.val.isOpen_inter_preimage_symm hV
  have hFd : DifferentiableOn ℂ F S := by
    intro w hw
    exact (differentiableAt_comp_chart_symm e hw.1
      (holomorphicAt_flatCoord Φ (Fin.last m) (hVF hw.2)).mdifferentiableAt).differentiableWithinAt
  have hkey : ∀ w ∈ S, F w ≠ 0 →
      E.curvature.val.coeff e w + smoothDDC (fun y => ell (e.val.symm y)) w = 0 := by
    intro w hw hwF
    have hwE : e.val.symm w ∉ E.support := by
      change E.weight (e.val.symm w) ≠ ⊥
      rw [hweight _ hw.2, logNormSq, ENNReal.log_ofReal_of_pos
        (pow_pos (norm_pos_iff.mpr hwF) 2), ← EReal.coe_add]
      exact EReal.coe_ne_bot _
    obtain ⟨B, hwB, hpot⟩ :=
      MeteredDivisorSmoothOffSupport.exists_isSmoothLocalPotential_neg_curvature E hwE e
        (e.val.map_target hw.1)
    rw [e.val.right_inv hw.1] at hwB
    let A := (S ∩ B) ∩ F ⁻¹' {v : ℂ | v ≠ 0}
    have hA : IsOpen A :=
      (hFd.continuousOn.mono inter_subset_left).isOpen_inter_preimage
        (hS.inter hpot.1) isOpen_ne
    have hwA : w ∈ A := ⟨⟨hw, hwB⟩, hwF⟩
    have hlog : ContDiffOn ℝ ∞ (fun y => Real.log (Complex.normSq (F y))) A := by
      intro y hy
      exact (MeteredDivisorSmoothOffSupport.contDiffAt_log_normSq hS hFd hy.1.1 hy.2).contDiffWithinAt
    have hll : ContDiffOn ℝ ∞ (fun y => ell (e.val.symm y)) A :=
      (hell e).mono (inter_subset_left.trans inter_subset_left)
    have hfun : (fun y => (E.weight (e.val.symm y)).toReal) =ᶠ[𝓝 w]
        (fun y => Real.log (Complex.normSq (F y)) + ell (e.val.symm y)) := by
      filter_upwards [hA.mem_nhds hwA] with y hy
      rw [hweight _ hy.1.1.2, logNormSq,
        ENNReal.log_ofReal_of_pos (pow_pos (norm_pos_iff.mpr hy.2) 2),
        ← EReal.coe_add, EReal.toReal_coe, Complex.normSq_eq_norm_sq]
    have hzero : smoothDDC (fun y => Real.log (Complex.normSq (F y))) w = 0 :=
      PluriharmonicLogNorm.smoothDDC_log_normSq_eq_zero
        (by
          filter_upwards [hS.mem_nhds hw] with y hy
          exact (hFd y hy).differentiableAt (hS.mem_nhds hy)) hwF
    have hp := hpot.2.2.2 hwB
    rw [smoothDDC_congr hfun, smoothDDC_add hA hlog hll hwA,
      hzero, zero_add, ClosedRealOneOneForm.coeff_neg] at hp
    rw [hp]
    simp
  have hdense : S ⊆ closure {w | w ∈ S ∧ F w ≠ 0} := by
    intro w hw
    rw [mem_closure_iff]
    intro O hO hwO
    have hOimage : IsOpen (e.val.symm '' (O ∩ S)) :=
      e.val.symm.isOpen_image_of_subset_source (hO.inter hS) fun y hy => hy.2.1
    obtain ⟨y, ⟨a, ha, rfl⟩, hya⟩ :=
      flat_last_nonzero_on_open Φ hflat hW (e.val.symm '' (O ∩ S)) hOimage
        (fun y hy => by
          obtain ⟨a, ha, rfl⟩ := hy
          exact hVF ha.2.2) ⟨e.val.symm w, w, ⟨hwO, hw⟩, rfl⟩
    exact ⟨a, ha.1, ha.2, hya⟩
  have hcont : ContinuousAt
      (fun w => E.curvature.val.coeff e w + smoothDDC (fun y => ell (e.val.symm y)) w) z :=
    ((E.curvature.val.smooth e).continuousOn.continuousAt
      (e.val.open_target.mem_nhds hz.1)).add
      ((LogWeightFactorization.smoothDDC_contDiffOn hS (hell e)).continuousOn.continuousAt
        (hS.mem_nhds hz))
  have := mem_closure_iff_nhdsWithin_neBot.mp (hdense hz)
  have heq : E.curvature.val.coeff e z +
      smoothDDC (fun y => ell (e.val.symm y)) z = 0 :=
    tendsto_nhds_unique (hcont.tendsto.mono_left nhdsWithin_le_nhds)
      (tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall
        fun y (hy : y ∈ {w | w ∈ S ∧ F w ≠ 0}) => (hkey y hy.1 hy.2).symm))
  exact eq_neg_of_add_eq_zero_left heq

/-- Original compact smooth-divisor geometry internally supplies the actual
effective divisor and one global metric. Every chosen original flattening
then has the genuine all-point weight and curvature normal forms. -/
theorem exists_normalized_smooth_divisor_metric_normal_forms [CompactSpace M] {W : Set M}
    (hW : IsClosedConnectedSubmanifold (m + 1) W m) :
    ∃ D : EffectiveDivisor (m + 1) M, D.ideal = vanishingIdeal (n := m + 1) W ∧
      ∃ E : MeteredEffectiveQDivisor (m + 1) M, E.support = W ∧
        DivisorMetric.IsDivisorMetric D E ∧
      ∀ (p : M) (Φ : LocalHolomorphicEquivAt (n := m + 1)
        (chartAt (ComplexModel (m + 1)) p p)),
        Φ.source ⊆ (chartAt (ComplexModel (m + 1)) p).target →
        (∀ {y : M}, y ∈ (chartAt (ComplexModel (m + 1)) p).source →
          chartAt (ComplexModel (m + 1)) p y ∈ Φ.source →
          (y ∈ W ↔ Φ.toFun (chartAt (ComplexModel (m + 1)) p y) ∈
            complexCoordinatePlane (m + 1) m)) →
        ∃ (V : Set M) (ell : M → ℝ), IsOpen V ∧ p ∈ V ∧ V ⊆ flatDomain Φ ∧
          (∀ e : ComplexChart (m + 1) M, ContDiffOn ℝ ∞
            (fun z => ell (e.val.symm z)) (e.val.target ∩ e.val.symm ⁻¹' V)) ∧
          (∀ y ∈ V, E.weight y = logNormSq (flatCoord Φ (Fin.last m) y) + (ell y : EReal)) ∧
          (∀ (e : ComplexChart (m + 1) M) (z : ComplexModel (m + 1)),
            z ∈ e.val.target → e.val.symm z ∈ V →
            E.curvature.val.coeff e z = -smoothDDC (fun w => ell (e.val.symm w)) z) := by
  let D : EffectiveDivisor (m + 1) M :=
    ⟨vanishingIdeal (n := m + 1) W,
      BlowupExistenceCodimOne.isInvertible_vanishingIdeal_of_codimOne hW.1
        (smooth_divisor_interior_eq_empty hW) (fun x hx => ⟨m, hW.2.2 x hx, rfl⟩)⟩
  obtain ⟨E, hED, hmetric⟩ := DivisorMetric.exists_divisorMetric D
  have hsupport : E.support = W := hED.trans
    (VanishingIdealZeroLocus.zeroLocus_vanishingIdeal (n := m + 1) hW.1)
  refine ⟨D, rfl, E, hsupport, hmetric, ?_⟩
  intro p Φ hΦsrc hflat
  obtain ⟨V, ell, hV, hpV, hVF, hell, hweight⟩ :=
    exists_divisor_metric_flat_normal_form Φ hΦsrc hflat hW D rfl E hmetric
  exact ⟨V, ell, hV, hpV, hVF, hell, hweight, fun e z hz hx =>
    curvature_eq_neg_smoothDDC_flat_normal_form Φ hflat hW E hV hVF ell hell hweight
      e ⟨hz, hx⟩⟩


/-- Original compact smooth-divisor geometry internally supplies the actual
effective divisor and one global metric. Every chosen original flattening
then has the genuine all-point weight and curvature normal forms. -/
theorem exists_smooth_divisor_metric_normal_forms [CompactSpace M] {W : Set M}
    (hW : IsClosedConnectedSubmanifold (m + 1) W m) :
    ∃ E : MeteredEffectiveQDivisor (m + 1) M, E.support = W ∧
      ∀ (p : M) (Φ : LocalHolomorphicEquivAt (n := m + 1)
        (chartAt (ComplexModel (m + 1)) p p)),
        Φ.source ⊆ (chartAt (ComplexModel (m + 1)) p).target →
        (∀ {y : M}, y ∈ (chartAt (ComplexModel (m + 1)) p).source →
          chartAt (ComplexModel (m + 1)) p y ∈ Φ.source →
          (y ∈ W ↔ Φ.toFun (chartAt (ComplexModel (m + 1)) p y) ∈
            complexCoordinatePlane (m + 1) m)) →
        ∃ (V : Set M) (ell : M → ℝ), IsOpen V ∧ p ∈ V ∧ V ⊆ flatDomain Φ ∧
          (∀ e : ComplexChart (m + 1) M, ContDiffOn ℝ ∞
            (fun z => ell (e.val.symm z)) (e.val.target ∩ e.val.symm ⁻¹' V)) ∧
          (∀ y ∈ V, E.weight y = logNormSq (flatCoord Φ (Fin.last m) y) + (ell y : EReal)) ∧
          (∀ (e : ComplexChart (m + 1) M) (z : ComplexModel (m + 1)),
            z ∈ e.val.target → e.val.symm z ∈ V →
            E.curvature.val.coeff e z = -smoothDDC (fun w => ell (e.val.symm w)) z) := by
  obtain ⟨D, _hDI, E, hEW, _hmetric, hnormal⟩ :=
    exists_normalized_smooth_divisor_metric_normal_forms hW
  exact ⟨E, hEW, hnormal⟩

end SGPT.Okounkov
