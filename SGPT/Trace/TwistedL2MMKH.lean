import SGPT.Trace.TwistedL2MGauge

/-!
# The summed polarized Morrey--Kohn--Hörmander identity

Blueprint `claude-tl2-main.tex` (`claude-tl2-main:summed-mkh`).  For a weight `φ` and a vector
field `W` smooth on an open `D ⊆ ℂⁿ` and a smooth vector field `h` with compact support in `D`,

`∫ ϑ_φ W · conj(ϑ_φ h) e^{-φ} = ∫ tr(A_W Ā_h) e^{-φ} + ∫ Levi(φ)(W, h) e^{-φ}`,

with `ϑ_φ = chartTheta φ`, `A_W = ∂̄W` (`trS`) and the sesquilinear Levi form `leviS`.  This is
the polarized flat identity of TN (`integral_deltaDir_mul_conj_deltaDir`) summed over the
coordinate directions, with only one factor compactly supported (the other is extended from a
neighbourhood of `tsupport h`).
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Trace.TwistedL2

open Set Filter MeasureTheory
open scoped Topology ContDiff ComplexConjugate
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.Pending.CauchyGreen SGPT.Foundations.Analysis.Pending.Hormander

variable {n : ℕ}

theorem contDiff_coord' {k : WithTop ℕ∞} {a : ComplexModel n → ComplexModel n}
    (ha : ContDiff ℝ k a) (j : Fin n) : ContDiff ℝ k (fun y => a y j) :=
  ((EuclideanSpace.proj j : ComplexModel n →L[ℂ] ℂ).restrictScalars ℝ).contDiff.comp ha

theorem hasCompactSupport_coord {a : ComplexModel n → ComplexModel n}
    (ha : HasCompactSupport a) (j : Fin n) : HasCompactSupport (fun y => a y j) :=
  ha.comp_left (g := fun v : ComplexModel n => v j) (by simp)

/-- The product `ϑ_Φ a · conj(ϑ_Φ b)` as a double sum. -/
theorem chartTheta_mul_conj_eq_sum (Φ : ComplexModel n → ℝ) (a b : ComplexModel n → ComplexModel n)
    (z : ComplexModel n) :
    chartTheta Φ a z * conj (chartTheta Φ b z) =
      ∑ j, ∑ k, deltaDir (coordVec j) Φ (fun y => a y j) z *
        conj (deltaDir (coordVec k) Φ (fun y => b y k) z) := by
  simp only [chartTheta, map_neg, neg_mul_neg, map_sum, Finset.sum_mul_sum]

/-- **The summed polarized identity for globally smooth data.** -/
theorem integral_chartTheta_mul_conj_global {Φ : ComplexModel n → ℝ} (hΦ : ContDiff ℝ 2 Φ)
    {a b : ComplexModel n → ComplexModel n} (ha : ContDiff ℝ 2 a) (hb : ContDiff ℝ 2 b)
    (hac : HasCompactSupport a) (hbc : HasCompactSupport b) :
    ∫ z, chartTheta Φ a z * conj (chartTheta Φ b z) * cweight Φ z =
      (∫ z, trS a b z * cweight Φ z) + ∫ z, leviS Φ z (a z) (b z) * cweight Φ z := by
  have ha' : ∀ j, ContDiff ℝ 2 (fun y => a y j) := fun j => contDiff_coord' ha j
  have hb' : ∀ k, ContDiff ℝ 2 (fun y => b y k) := fun k => contDiff_coord' hb k
  have hac' : ∀ j, HasCompactSupport (fun y => a y j) := fun j => hasCompactSupport_coord hac j
  have hbc' : ∀ k, HasCompactSupport (fun y => b y k) := fun k => hasCompactSupport_coord hbc k
  have hΦ1 : ContDiff ℝ 1 Φ := hΦ.of_le (by norm_num)
  have hw : Continuous (cweight Φ) := (contDiff_cweight hΦ).continuous
  have hP : ∀ j k : Fin n,
      Continuous (dbarDir (coordVec k) (dDir (coordVec j) (fun y => (Φ y : ℂ)))) := by
    intro j k
    have h1 : ContDiff ℝ 1 (dDir (coordVec j) (fun y => (Φ y : ℂ))) :=
      contDiff_dDir (k := 1) (contDiff_ofReal_comp hΦ)
    exact (contDiff_dbarDir (k := 0) (by simpa using h1)).continuous
  -- integrability of the three families of integrands
  have I1 : ∀ j k : Fin n, Integrable (fun z => deltaDir (coordVec j) Φ (fun y => a y j) z *
      conj (deltaDir (coordVec k) Φ (fun y => b y k) z) * cweight Φ z) := by
    intro j k
    have hc : Continuous (fun z => deltaDir (coordVec j) Φ (fun y => a y j) z *
        conj (deltaDir (coordVec k) Φ (fun y => b y k) z) * cweight Φ z) :=
      ((continuous_deltaDir hΦ1 ((ha' j).of_le (by norm_num))).mul
        (Complex.continuous_conj.comp (continuous_deltaDir hΦ1 ((hb' k).of_le (by norm_num))))).mul hw
    exact hc.integrable_of_hasCompactSupport
      ((hasCompactSupport_deltaDir (hac' j)).mul_right.mul_right)
  have I2 : ∀ j k : Fin n, Integrable (fun z => dbarDir (coordVec k) (fun y => a y j) z *
      conj (dbarDir (coordVec j) (fun y => b y k) z) * cweight Φ z) := by
    intro j k
    have hc : Continuous (fun z => dbarDir (coordVec k) (fun y => a y j) z *
        conj (dbarDir (coordVec j) (fun y => b y k) z) * cweight Φ z) :=
      ((continuous_dbarDir ((ha' j).of_le (by norm_num))).mul
        (Complex.continuous_conj.comp (continuous_dbarDir ((hb' k).of_le (by norm_num))))).mul hw
    exact hc.integrable_of_hasCompactSupport
      ((hasCompactSupport_dbarDir (hac' j)).mul_right.mul_right)
  have I3 : ∀ j k : Fin n, Integrable (fun z =>
      dbarDir (coordVec k) (dDir (coordVec j) (fun y => (Φ y : ℂ))) z * a z j * conj (b z k) *
        cweight Φ z) := by
    intro j k
    have hc : Continuous (fun z =>
        dbarDir (coordVec k) (dDir (coordVec j) (fun y => (Φ y : ℂ))) z * a z j * conj (b z k) *
          cweight Φ z) :=
      ((((hP j k).mul (ha' j).continuous).mul
        (Complex.continuous_conj.comp (hb' k).continuous))).mul hw
    exact hc.integrable_of_hasCompactSupport ((hac' j).mul_left.mul_right.mul_right)
  have hL : (fun z => chartTheta Φ a z * conj (chartTheta Φ b z) * cweight Φ z) =
      fun z => ∑ j, ∑ k, deltaDir (coordVec j) Φ (fun y => a y j) z *
        conj (deltaDir (coordVec k) Φ (fun y => b y k) z) * cweight Φ z := by
    funext z
    rw [chartTheta_mul_conj_eq_sum, Finset.sum_mul]
    simp only [Finset.sum_mul]
  have hT : (fun z => trS a b z * cweight Φ z) = fun z => ∑ j, ∑ k,
      dbarDir (coordVec k) (fun y => a y j) z *
        conj (dbarDir (coordVec j) (fun y => b y k) z) * cweight Φ z := by
    funext z
    simp only [trS, Finset.sum_mul]
  have hLv : (fun z => leviS Φ z (a z) (b z) * cweight Φ z) = fun z => ∑ j, ∑ k,
      dbarDir (coordVec k) (dDir (coordVec j) (fun y => (Φ y : ℂ))) z * a z j * conj (b z k) *
        cweight Φ z := by
    funext z
    simp only [leviS, Finset.sum_mul]
  rw [hL, hT, hLv, integral_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ => I1 j k,
    integral_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ => I2 j k,
    integral_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ => I3 j k,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_finsetSum _ fun k _ => I1 j k, integral_finsetSum _ fun k _ => I2 j k,
    integral_finsetSum _ fun k _ => I3 j k, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  exact integral_deltaDir_mul_conj_deltaDir (μ := volume) hΦ (ha' j) (hb' k) (hac' j) (hbc' k)

/-! ### Locality -/

theorem chartTheta_congr_weight {p p' : ComplexModel n → ℝ} {u u' : ComplexModel n → ComplexModel n}
    {z : ComplexModel n} (hp : (fun y => (p y : ℂ)) =ᶠ[𝓝 z] fun y => (p' y : ℂ))
    (hu : u =ᶠ[𝓝 z] u') : chartTheta p u z = chartTheta p' u' z := by
  have hj : ∀ j : Fin n, (fun y => u y j) =ᶠ[𝓝 z] fun y => u' y j := fun j =>
    hu.mono fun y hy => by simp [hy]
  simp only [chartTheta, deltaDir, dDir_congr_of_eventuallyEq (hj _), (hj _).self_of_nhds,
    dDir_congr_of_eventuallyEq hp]

theorem leviS_congr_weight {p p' : ComplexModel n → ℝ} {z : ComplexModel n}
    (hp : p =ᶠ[𝓝 z] p') (u w : ComplexModel n) : leviS p z u w = leviS p' z u w := by
  have hev : ∀ᶠ y in 𝓝 z, p =ᶠ[𝓝 y] p' := hp.eventually_nhds
  have hk : ∀ j k : Fin n, dbarDir (coordVec k) (dDir (coordVec j) fun y => (p y : ℂ)) z =
      dbarDir (coordVec k) (dDir (coordVec j) fun y => (p' y : ℂ)) z := by
    intro j k
    refine dbarDir_congr_of_eventuallyEq (hev.mono fun y hy => ?_)
    exact dDir_congr_of_eventuallyEq (hy.mono fun y' hy' => by simp [hy'])
  simp only [leviS, hk]

theorem cweight_congr {p p' : ComplexModel n → ℝ} {z : ComplexModel n} (h : p z = p' z) :
    cweight p z = cweight p' z := by
  simp [cweight, h]

theorem continuous_of_continuousOn_of_eq_zero {f : ComplexModel n → ℂ}
    {D K : Set (ComplexModel n)} (hD : IsOpen D) (hf : ContinuousOn f D) (hK : IsClosed K)
    (hKD : K ⊆ D) (h0 : ∀ z ∉ K, f z = 0) : Continuous f := by
  refine continuous_iff_continuousAt.mpr fun z => ?_
  by_cases hz : z ∈ D
  · exact hf.continuousAt (hD.mem_nhds hz)
  · have hzK : z ∉ K := fun h => hz (hKD h)
    have hev : f =ᶠ[𝓝 z] fun _ => 0 := by
      filter_upwards [hK.isOpen_compl.mem_nhds hzK] with y hy
      exact h0 y hy
    exact continuousAt_const.congr hev.symm

/-- **The summed polarized flat identity with one compactly supported factor.** -/
theorem integral_chartTheta_mul_conj_local {D : Set (ComplexModel n)} (hD : IsOpen D)
    {φ : ComplexModel n → ℝ} (hφ : ContDiffOn ℝ ∞ φ D) {W : ComplexModel n → ComplexModel n}
    (hW : ContDiffOn ℝ ∞ W D) {h : ComplexModel n → ComplexModel n} (hh : ContDiff ℝ ∞ h)
    (hhc : HasCompactSupport h) (hhD : tsupport h ⊆ D) :
    ∫ z, chartTheta φ W z * conj (chartTheta φ h z) * cweight φ z =
      (∫ z, trS W h z * cweight φ z) + ∫ z, leviS φ z (W z) (h z) * cweight φ z := by
  obtain ⟨Φ, hΦ, hΦeq⟩ := exists_contDiff_eventuallyEq_nhdsSet hD hφ hhc hhD
  obtain ⟨α, hα, hαeq⟩ := exists_contDiff_eventuallyEq_nhdsSet hD hW hhc hhD
  obtain ⟨θ, hθ, hθc, -, hθ1, -⟩ := exists_contDiff_cutoff hhc hD hhD
  set α' : ComplexModel n → ComplexModel n := fun x => θ x • α x with hα'def
  have h2 : (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := WithTop.coe_le_coe.mpr le_top
  have hα' : ContDiff ℝ 2 α' := (hθ.smul hα).of_le h2
  have hα'c : HasCompactSupport α' := hθc.smul_right
  have hloc : ∀ x ∈ tsupport h, Φ =ᶠ[𝓝 x] φ ∧ α' =ᶠ[𝓝 x] W := by
    intro x hx
    have hx' : 𝓝 x ≤ 𝓝ˢ (tsupport h) := nhds_le_nhdsSet hx
    have e1 : ∀ᶠ y in 𝓝 x, Φ y = φ y := hΦeq.filter_mono hx'
    have e2 : ∀ᶠ y in 𝓝 x, α y = W y := hαeq.filter_mono hx'
    have e3 : ∀ᶠ y in 𝓝 x, θ y = 1 := hθ1.filter_mono hx'
    refine ⟨e1, (e2.and e3).mono fun y hy => ?_⟩
    simp only [hα'def, hy.1, hy.2, one_smul]
  have hz0 : ∀ x ∉ tsupport h, h =ᶠ[𝓝 x] 0 := fun x hx =>
    eventuallyEq_zero_of_notMem_tsupport hx
  have hglob := integral_chartTheta_mul_conj_global (hΦ.of_le h2) hα' (hh.of_le h2) hα'c hhc
  have i1 : ∀ x, chartTheta Φ α' x * conj (chartTheta Φ h x) * cweight Φ x =
      chartTheta φ W x * conj (chartTheta φ h x) * cweight φ x := by
    intro x
    by_cases hx : x ∈ tsupport h
    · obtain ⟨e1, e2⟩ := hloc x hx
      have e1' : (fun y => (Φ y : ℂ)) =ᶠ[𝓝 x] fun y => (φ y : ℂ) := e1.mono fun y hy => by simp [hy]
      rw [chartTheta_congr_weight e1' e2, chartTheta_congr_weight e1' (EventuallyEq.refl _ h),
        cweight_congr e1.self_of_nhds]
    · simp [chartTheta_eq_zero_of_eventuallyEq (hz0 x hx)]
  have i2 : ∀ x, trS α' h x * cweight Φ x = trS W h x * cweight φ x := by
    intro x
    by_cases hx : x ∈ tsupport h
    · obtain ⟨e1, e2⟩ := hloc x hx
      rw [trS_congr e2 (EventuallyEq.refl _ h), cweight_congr e1.self_of_nhds]
    · simp [trS_eq_zero_of_right (hz0 x hx)]
  have i3 : ∀ x, leviS Φ x (α' x) (h x) * cweight Φ x = leviS φ x (W x) (h x) * cweight φ x := by
    intro x
    by_cases hx : x ∈ tsupport h
    · obtain ⟨e1, e2⟩ := hloc x hx
      rw [leviS_congr_weight e1, e2.self_of_nhds, cweight_congr e1.self_of_nhds]
    · simp [(hz0 x hx).self_of_nhds, leviS_zero_right]
  simp only [i1, i2, i3] at hglob
  exact hglob

end SGPT.Trace.TwistedL2
