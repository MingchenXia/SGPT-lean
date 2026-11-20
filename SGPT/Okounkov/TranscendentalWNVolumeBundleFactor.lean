import SGPT.Okounkov.TranscendentalWNVolumeBundleMain
import SGPT.Okounkov.TranscendentalSliceClasses
import SGPT.Foundations.Analysis.Pending.BlowupLocalSurjectivity

/-!
# The local factor of `|s_Z|²` along `Z` and the twist `g_Z` (package WN-VF4)

Blueprint `claude-tok-wn-vf4`, node `tok-wn-vf4:twist`; source WN21 §4 (`|s_Y|² e^{-g_Y}`, the
normal coordinate `z₁` of `Y` and the smooth `g_Y` with `dd^c g_Y = η` near `Y`).

Let `Φ` flatten `Z` near `x₀ ∈ Z` (`Z = {z₁ = 0}`, `z₁ = (Φ ∘ e)_m`).  For the unit metric `E` of
`𝒪(Z)` (weight `log |s_Z|²_h`) there are a neighbourhood `N` of `x₀` and a smooth `G > 0` on `N`
with `|s_Z|²_h = |z₁|² G` on `N` (`exists_weight_factor`): the local generator `g` of the ideal of
`Z` in the presentation of `E` is `b z₁` with `b(x₀) ≠ 0` (Hadamard in the flattening, and `z₁`
is a multiple of `g`).  Then `-log G` is a smooth local potential of `η = E.curvature`
(`isSmoothLocalPotential_neg_log_factor`): off `Z`, `-log G = -log |s_Z|²_h + log |z₁|²` with
`dd^c log |z₁|² = 0`, and both sides are continuous across the nowhere dense `Z`.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalWN

open Set Filter
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.BlowupFlatCoordinates
open SGPT.Okounkov.TranscendentalMain

variable {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))

/-- **The local factor** (`tok-wn-vf4:twist`, first half): `|s_Z|²_h = |z₁|² G` near `x₀ ∈ Z`
with `G` smooth and positive. -/
theorem exists_weight_factor {E : MeteredEffectiveQDivisor (m + 1) F.carrier}
    (hE : IsFirstDivisorUnitMetric F E) {x₀ : F.carrier}
    {Φ : LocalHolomorphicEquivAt (n := m + 1) (chartAt (ComplexModel (m + 1)) x₀ x₀)}
    (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel (m + 1)) x₀).target)
    (hflat : ∀ {y : F.carrier}, y ∈ (chartAt (ComplexModel (m + 1)) x₀).source →
      chartAt (ComplexModel (m + 1)) x₀ y ∈ Φ.source →
        (y ∈ F.flag (1 : Fin (m + 2)) ↔
          Φ.toFun (chartAt (ComplexModel (m + 1)) x₀ y) ∈ complexCoordinatePlane (m + 1) m)) :
    ∃ N : Set F.carrier, IsOpen N ∧ x₀ ∈ N ∧ N ⊆ flatDomain Φ ∧ ∃ G : F.carrier → ℝ,
      (∀ y ∈ N, 0 < G y) ∧ ContinuousOn G N ∧
      (∀ e : ComplexChart (m + 1) F.carrier,
        ContDiffOn ℝ ∞ (fun u => G (e.val.symm u)) (e.val.target ∩ e.val.symm ⁻¹' N)) ∧
      ∀ y ∈ N, (EReal.exp (E.weight y)).toReal = ‖flatCoord Φ (Fin.last m) y‖ ^ 2 * G y := by
  classical
  obtain ⟨D, hDid, hsupp, hmet⟩ := hE
  obtain ⟨V, hV, hx₀V, g, hg, hgen, h, hh, hw⟩ := hmet x₀
  have hx₀f : x₀ ∈ flatDomain Φ := mem_flatDomain_self Φ
  have hghol : ∀ y ∈ V, HolomorphicAt (m + 1) g y := fun y hy => by
    filter_upwards [hV.mem_nhds hy] with z hz
    exact (hg z hz).mdifferentiableAt (hV.mem_nhds hz)
  -- `g = b z₁` near `x₀`
  have hgZ : (vanishingIdeal (n := m + 1) (F.flag (1 : Fin (m + 2)))).mem x₀ g := by
    rw [← hDid]
    exact (hgen x₀ hx₀V g).mpr (isInSpanAt_of_eq_mul rfl (hghol x₀ hx₀V) (holomorphicAt_const 1)
      (Eventually.of_forall fun _ => by simp))
  obtain ⟨b, hb0, hbhol, hgb⟩ := exists_eq_sum_flatCoord Φ hΦsrc hflat hx₀f hgZ
  set z₁ := flatCoord Φ (Fin.last m) with hz₁
  have hgb' : g =ᶠ[𝓝 x₀] fun y => b (Fin.last m) y * z₁ y := by
    filter_upwards [hgb] with y hy
    rw [hy, Fin.sum_univ_castSucc]
    simp [hb0 _ (Fin.castSucc_lt_last _), z₁]
  -- `z₁ = a g` near `x₀`
  have hz₁Z : (vanishingIdeal (n := m + 1) (F.flag (1 : Fin (m + 2)))).mem x₀ z₁ :=
    flatCoord_mem_vanishingIdeal Φ hflat (by simp) hx₀f
  rw [← hDid] at hz₁Z
  obtain ⟨a, hahol, hza⟩ := exists_eq_mul_of_isInSpanAt ((hgen x₀ hx₀V z₁).mp hz₁Z)
  -- `a b = 1` at `x₀`
  have hab : a x₀ * b (Fin.last m) x₀ = 1 := by
    have hc : ContinuousAt (fun y => a y * b (Fin.last m) y) x₀ :=
      hahol.continuousAt.mul (hbhol _).continuousAt
    by_contra hne
    have hev : ∀ᶠ y in 𝓝 x₀, a y * b (Fin.last m) y ≠ 1 ∧ y ∈ flatDomain Φ ∧
        z₁ y = a y * g y ∧ g y = b (Fin.last m) y * z₁ y := by
      filter_upwards [hc.eventually (isOpen_ne.mem_nhds hne), (isOpen_flatDomain Φ).mem_nhds hx₀f,
        hza, hgb'] with y h1 h2 h3 h4
      exact ⟨h1, h2, h3, h4⟩
    obtain ⟨W, hWsub, hWo, hx₀W⟩ := mem_nhds_iff.mp hev
    -- a point of `W` off `Z`
    have hcl : x₀ ∈ closure (F.flag (1 : Fin (m + 2)))ᶜ := by
      rw [closure_compl, interior_firstFlag F]; exact notMem_empty x₀
    obtain ⟨y, hyW, hyZ⟩ := mem_closure_iff.mp hcl W hWo hx₀W
    obtain ⟨h1, h2, h3, h4⟩ := hWsub hyW
    have hz₁y : z₁ y ≠ 0 := by
      intro h0
      apply hyZ
      rw [hflat h2.1 h2.2]
      intro i hi
      have hi' : i = Fin.last m := Fin.ext (by have := i.2; simp only [Fin.val_last]; omega)
      subst hi'
      exact h0
    apply h1
    have : z₁ y = (a y * b (Fin.last m) y) * z₁ y := by rw [mul_assoc, ← h4, ← h3]
    have h5 : (1 - a y * b (Fin.last m) y) * z₁ y = 0 := by rw [sub_mul, one_mul, ← this, sub_self]
    rcases mul_eq_zero.mp h5 with h6 | h6
    · exact (sub_eq_zero.mp h6).symm
    · exact absurd h6 hz₁y
  have hbx₀ : b (Fin.last m) x₀ ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hab; exact zero_ne_one hab
  -- the neighbourhood
  set P : F.carrier → Prop := fun y => y ∈ V ∧ y ∈ flatDomain Φ ∧
    g y = b (Fin.last m) y * z₁ y ∧ b (Fin.last m) y ≠ 0 ∧ HolomorphicAt (m + 1) (b (Fin.last m)) y
    with hPdef
  have hP : ∀ᶠ y in 𝓝 x₀, P y := by
    have h1 := (hbhol (Fin.last m)).continuousAt.eventually (isOpen_ne.mem_nhds hbx₀)
    filter_upwards [hV.mem_nhds hx₀V, (isOpen_flatDomain Φ).mem_nhds hx₀f, hgb', h1,
      (hbhol (Fin.last m)).eventually] with y hy1 hy2 hy3 hy4 hy5
    exact ⟨hy1, hy2, hy3, hy4, hy5⟩
  set N := interior {y | P y} with hNdef
  have hNP : ∀ y ∈ N, P y := fun y hy => interior_subset (s := {y | P y}) hy
  refine ⟨N, isOpen_interior, mem_interior_iff_mem_nhds.mpr hP, fun y hy => (hNP y hy).2.1,
    fun y => ‖b (Fin.last m) y‖ ^ 2 * Real.exp (h y), fun y hy => ?_, ?_, fun e => ?_,
    fun y hy => ?_⟩
  · have := (hNP y hy).2.2.2.1
    positivity
  · intro y hy
    have hbc : ContinuousAt (b (Fin.last m)) y := (hNP y hy).2.2.2.2.continuousAt
    have hhc : ContinuousAt h y := by
      set e := complexChartAt (n := m + 1) y
      have hye : y ∈ e.val.source := mem_complexChartAt_source y
      have h1 : ContinuousAt (fun u => h (e.val.symm u)) (e.val y) :=
        ((hh e).continuousOn.continuousAt ((e.val.isOpen_inter_preimage_symm hV).mem_nhds
          ⟨e.val.map_source hye, by
            show e.val.symm (e.val y) ∈ V
            rw [e.val.left_inv hye]; exact (hNP y hy).1⟩))
      have h2 := h1.comp (e.val.continuousAt hye)
      refine h2.congr ?_
      filter_upwards [e.val.open_source.mem_nhds hye] with z hz
      simp [e.val.left_inv hz]
    exact ((hbc.norm.pow 2).mul (Real.continuous_exp.continuousAt.comp hhc)).continuousWithinAt
  · have h1 := contDiffOn_norm_sq_comp_chart_symm isOpen_interior
      (fun y hy => ((hNP y hy).2.2.2.2).mdifferentiableAt) e
    have h2 := ((hh e).exp).mono fun u (hu : u ∈ e.val.target ∩ e.val.symm ⁻¹' N) =>
      ⟨hu.1, (hNP _ hu.2).1⟩
    exact h1.mul h2
  · obtain ⟨hyV, -, hgy, -, -⟩ := hNP y hy
    rw [exp_weight_toReal_eq F (hw y hyV), hgy, norm_mul, mul_pow]
    ring

/-- **The twist** (`tok-wn-vf4:twist`, second half): `-log G` is a smooth local potential of
`η = E.curvature` in the chart at `x₀`. -/
theorem isSmoothLocalPotential_neg_log_factor {E : MeteredEffectiveQDivisor (m + 1) F.carrier}
    (hE : IsFirstDivisorUnitMetric F E) {x₀ : F.carrier}
    {Φ : LocalHolomorphicEquivAt (n := m + 1) (chartAt (ComplexModel (m + 1)) x₀ x₀)}
    (hflat : ∀ {y : F.carrier}, y ∈ (chartAt (ComplexModel (m + 1)) x₀).source →
      chartAt (ComplexModel (m + 1)) x₀ y ∈ Φ.source →
        (y ∈ F.flag (1 : Fin (m + 2)) ↔
          Φ.toFun (chartAt (ComplexModel (m + 1)) x₀ y) ∈ complexCoordinatePlane (m + 1) m))
    {N : Set F.carrier} (hN : IsOpen N) (hNf : N ⊆ flatDomain Φ) {G : F.carrier → ℝ}
    (hGpos : ∀ y ∈ N, 0 < G y)
    (hGs : ∀ e : ComplexChart (m + 1) F.carrier,
      ContDiffOn ℝ ∞ (fun u => G (e.val.symm u)) (e.val.target ∩ e.val.symm ⁻¹' N))
    (hfac : ∀ y ∈ N, (EReal.exp (E.weight y)).toReal = ‖flatCoord Φ (Fin.last m) y‖ ^ 2 * G y) :
    IsSmoothLocalPotential E.curvature.val (complexChartAt (n := m + 1) x₀)
      ((complexChartAt (n := m + 1) x₀).val.target ∩
        (complexChartAt (n := m + 1) x₀).val.symm ⁻¹' N)
      (fun u => -Real.log (G ((complexChartAt (n := m + 1) x₀).val.symm u))) := by
  set e := complexChartAt (n := m + 1) x₀ with hedef
  set U' := e.val.target ∩ e.val.symm ⁻¹' N with hU'
  have hU'o : IsOpen U' := e.val.isOpen_inter_preimage_symm hN
  have hfs : ContDiffOn ℝ ∞ (fun u => -Real.log (G (e.val.symm u))) U' :=
    ((hGs e).log fun u hu => (hGpos _ hu.2).ne').neg
  refine ⟨hU'o, inter_subset_left, hfs, ?_⟩
  obtain ⟨D, -, hsupp, -⟩ := id hE
  set Zc := (F.flag (1 : Fin (m + 2)))ᶜ with hZc
  have hoff : EqOn (smoothDDC fun u => -Real.log (G (e.val.symm u))) (E.curvature.val.coeff e)
      (U' ∩ e.val.symm ⁻¹' Zc) := by
    rintro u ⟨⟨hut, huN⟩, huZ⟩
    set y := e.val.symm u with hy
    have hyE : y ∉ E.support := by rw [hsupp]; exact huZ
    have hys : y ∈ e.val.source := e.val.map_target hut
    obtain ⟨W₁, hW₁, hpot⟩ :=
      MeteredDivisorSmoothOffSupport.exists_isSmoothLocalPotential_neg_curvature E hyE e hys
    rw [hy, e.val.right_inv hut] at hW₁
    -- the holomorphic normal coordinate in the chart
    set z : ComplexModel (m + 1) → ℂ := fun u' => Φ.toFun u' (Fin.last m) with hzdef
    have hyf : y ∈ flatDomain Φ := hNf huN
    have hz0 : z u ≠ 0 := by
      intro h0
      apply huZ
      have hyu : chartAt (ComplexModel (m + 1)) x₀ y = u := e.val.right_inv hut
      rw [hflat hyf.1 hyf.2, hyu]
      intro i hi
      have hi' : i = Fin.last m := Fin.ext (by have := i.2; simp only [Fin.val_last]; omega)
      subst hi'
      exact h0
    have huΦ : u ∈ Φ.source := by
      have := hyf.2
      rwa [mem_preimage, show chartAt (ComplexModel (m + 1)) x₀ y = u from e.val.right_inv hut]
        at this
    have hzhol : ∀ᶠ u' in 𝓝 u, DifferentiableAt ℂ z u' := by
      filter_upwards [Φ.isOpen_source.mem_nhds huΦ] with u' hu'
      exact ((EuclideanSpace.proj (Fin.last m) : ComplexModel (m + 1) →L[ℂ] ℂ).differentiableAt).comp
        u' (Φ.toFun_holomorphic.differentiableAt (Φ.isOpen_source.mem_nhds hu'))
    -- the formula near `u`
    have hzcont : ContinuousOn z Φ.source :=
      (PiLp.continuous_apply 2 _ (Fin.last m)).comp_continuousOn
        Φ.toFun_holomorphic.continuousOn
    set T := W₁ ∩ (Φ.source ∩ z ⁻¹' {0}ᶜ) with hTdef
    have hTo : IsOpen T :=
      hpot.1.inter (hzcont.isOpen_inter_preimage Φ.isOpen_source isOpen_compl_singleton)
    have huT : u ∈ T := ⟨hW₁, huΦ, hz0⟩
    have hs1 : ContDiffOn ℝ ∞ (fun u' => -(E.weight (e.val.symm u')).toReal) T :=
      (hpot.2.2.1.mono inter_subset_left).neg
    have hzs : ContDiffOn ℝ ∞ z Φ.source :=
      (contDiffOn_of_differentiableOn_complex
        (fun u' hu' => ((EuclideanSpace.proj (Fin.last m) : ComplexModel (m + 1) →L[ℂ] ℂ
          ).differentiableAt.comp u' (Φ.toFun_holomorphic.differentiableAt
            (Φ.isOpen_source.mem_nhds hu'))).differentiableWithinAt)
        Φ.isOpen_source).restrict_scalars ℝ
    have hs2 : ContDiffOn ℝ ∞ (fun u' => Real.log (Complex.normSq (z u'))) T := by
      have h1 : ContDiffOn ℝ ∞ (fun u' => Complex.normSq (z u')) T := by
        have := (hzs.mono fun u' (hu' : u' ∈ T) => hu'.2.1).norm_sq ℝ
        refine this.congr fun u' _ => ?_
        simp [Complex.normSq_eq_norm_sq]
      exact h1.log fun u' hu' => (Complex.normSq_pos.mpr hu'.2.2).ne'
    have hev : (fun u' => -Real.log (G (e.val.symm u'))) =ᶠ[𝓝 u]
        fun u' => -(E.weight (e.val.symm u')).toReal + Real.log (Complex.normSq (z u')) := by
      have hNev : ∀ᶠ u' in 𝓝 u, e.val.symm u' ∈ N :=
        (e.val.continuousAt_symm hut).eventually (hN.mem_nhds huN)
      have hZev : ∀ᶠ u' in 𝓝 u, e.val.symm u' ∈ Zc :=
        (e.val.continuousAt_symm hut).eventually
          (F.firstDivisor.1.isOpen_compl.mem_nhds huZ)
      filter_upwards [hNev, hZev, e.val.open_target.mem_nhds hut, hTo.mem_nhds huT]
        with u' h1 h2 h3 h4
      have hz₁ : flatCoord Φ (Fin.last m) (e.val.symm u') = z u' := by
        simp only [flatCoord, hzdef]
        rw [show chartAt (ComplexModel (m + 1)) x₀ (e.val.symm u') = u' from e.val.right_inv h3]
      have hfac' := hfac _ h1
      rw [exp_weight_toReal_eq_exp F hE h2, hz₁] at hfac'
      have hzpos : 0 < ‖z u'‖ ^ 2 := by
        have := h4.2.2
        positivity
      have hG : G (e.val.symm u') = Real.exp (E.weight (e.val.symm u')).toReal / ‖z u'‖ ^ 2 := by
        rw [hfac', mul_div_assoc, mul_div_cancel₀ _ hzpos.ne']
      rw [hG, Real.log_div (Real.exp_pos _).ne' hzpos.ne', Real.log_exp,
        Complex.normSq_eq_norm_sq]
      ring
    rw [smoothDDC_congr hev, smoothDDC_add hTo hs1 hs2 huT,
      PluriharmonicLogNorm.smoothDDC_log_normSq_eq_zero hzhol hz0, add_zero,
      smoothDDC_neg hTo (hpot.2.2.1.mono inter_subset_left) huT, hpot.2.2.2 hW₁,
      ClosedRealOneOneForm.coeff_neg, neg_neg]
  have hclos : U' ⊆ closure (U' ∩ e.val.symm ⁻¹' Zc) := by
    intro u hu
    have h1 := TranscendentalSlice.chart_target_subset_closure (interior_firstFlag F) e hu.1
    have h2 := hU'o.inter_closure ⟨hu, h1⟩
    refine closure_mono (fun v hv => ?_) h2
    exact ⟨hv.1, hv.2.2⟩
  exact hoff.of_subset_closure
    ((LogWeightFactorization.smoothDDC_contDiffOn hU'o hfs).continuousOn)
    ((E.curvature.val.smooth e).continuousOn.mono inter_subset_left) inter_subset_left hclos

end SGPT.Okounkov.TranscendentalWN
