import SGPT.Foundations.Analysis.Pending.RawQuasiPshTestGenericLelongBound
import SGPT.Foundations.Analysis.Pending.MultiplierHaarLinearTransport
import SGPT.Foundations.Analysis.Pending.LocalHolomorphicLelongReaderCovariance

set_option autoImplicit false

/-! # A raw multiplier integral reads its actual given coordinate orders

The original integral directly bounds all local coordinate-hyperplane readers
using the same genuine factorization and residual, without choosing new orders.
Actual slice divergence and Haar coordinate transport retain all poles.
Reference: Demailly, Analytic Methods, multiplier integrability; supplementary
local raw-weight adaptation toward the Xia valuative criterion.
-/

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal NNReal ContDiff

namespace SGPT.Foundations.Analysis.Pending.RawQuasiPshGivenCoordinateOrderBounds

open FirstPass FirstPass.NonKahlerLocus HolomorphicGermReducednessBridge

noncomputable section

private theorem threshold_of_integrability {m : ℕ}
    {u : ComplexModel (m + 1) → EReal} (hu : QuasiPlurisubharmonicAt u 0)
    (a : Fin (m + 1) → ℕ) {F H : ComplexModel (m + 1) → ℂ}
    (hH : ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), DifferentiableAt ℂ H z)
    (hnot : ¬HolGerm.mk (fun z : ComplexModel (m + 1) => z (Fin.last m))
      (eventually_differentiableAt_coordinate (Fin.last m)) ∣ HolGerm.mk H hH)
    (heq : F =ᶠ[𝓝 0] fun z => H z * ∏ j : Fin (m + 1), z j ^ a j)
    {c : ℝ} (hint : MultiplierIntegrableAt u c F 0 volume)
    {R : ℝ} (hR : 0 < R) {γ : ℝ≥0}
    (hγ : (γ : ℝ≥0∞) < ⨅ q ∈ ball (0 : ComplexModel (m + 1)) R ∩
      {q | q (Fin.last m) = 0}, lelongNumber (n := m + 1) u q) :
    c * (γ : ℝ) < 2 * ((a (Fin.last m) : ℝ) + 1) := by
  classical
  obtain ⟨r, hr, _, C, hupper⟩ := RawQuasiPshDivisorialSliceBound.exists_slice_bound hu hR hγ
  let f : ComplexModel (m + 1) → ℂ := fun z =>
    H z * ∏ i : Fin m, z i.castSucc ^ a i.castSucc
  have htest : F =ᶠ[𝓝 (0 : ComplexModel (m + 1))]
      (fun z => z (Fin.last m) ^ a (Fin.last m) * f z) := by
    filter_upwards [heq] with z hz
    rw [hz, Fin.prod_univ_castSucc]
    dsimp only [f]
    ring
  obtain ⟨hc, U, hU, h0U, _, hL2⟩ := hint.congr EventuallyEq.rfl htest
  obtain ⟨V, hVsub, hV, h0V⟩ := _root_.mem_nhds_iff.mp hH
  have hnear : ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)),
      z ∈ (U ∩ V) ∩ ball 0 r :=
    ((show ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), z ∈ U from hU.mem_nhds h0U).and
      (show ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), z ∈ V from hV.mem_nhds h0V)).and
        (show ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), z ∈ ball 0 r from ball_mem_nhds _ hr)
  obtain ⟨y, hy, hyW⟩ :=
    ((SNCHolomorphicTestNecessity.frequently_last_zero_and_residual_and_other_coordinates_ne_zero
      hH hnot).and_eventually hnear).exists
  have hcontf : ContinuousAt f y := by
    apply (hVsub hyW.1.2).continuousAt.mul
    exact tendsto_finsetProd Finset.univ fun i _ =>
      (((EuclideanSpace.proj (𝕜 := ℂ) i.castSucc).continuous.continuousAt).pow (a i.castSucc))
  have hfy : f y ≠ 0 :=
    mul_ne_zero hy.2.1 (Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (hy.2.2 i))
  let W : Set (ComplexModel (m + 1)) := (U ∩ V) ∩ ball 0 r
  have hW : IsOpen W := (hU.inter hV).inter isOpen_ball
  have hWU : W ⊆ U := fun z hz => hz.1.1
  have hneg := DivisorialMultiplierOrder.neg_two_lt_of_lintegral_ne_top hy.1
    (hW.mem_nhds hyW) hc (fun z hz hz0 => hupper z hz.2 hz0) hcontf hfy
    (a (Fin.last m)) (hL2.mono hWU).2.ne
  nlinarith


private theorem last_reader_le_of_factorization {m : ℕ}
    {u : ComplexModel (m + 1) → EReal} (hu : QuasiPlurisubharmonicAt u 0)
    (a : Fin (m + 1) → ℕ) {F H : ComplexModel (m + 1) → ℂ}
    (hH : ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), DifferentiableAt ℂ H z)
    (hnot : ¬HolGerm.mk (fun z : ComplexModel (m + 1) => z (Fin.last m))
      (eventually_differentiableAt_coordinate (Fin.last m)) ∣ HolGerm.mk H hH)
    (heq : F =ᶠ[𝓝 0] fun z => H z * ∏ j : Fin (m + 1), z j ^ a j)
    {c : ℝ} (hint : MultiplierIntegrableAt u c F 0 volume)
    {R : ℝ} (hR : 0 < R) :
    (⨅ z ∈ ball (0 : ComplexModel (m + 1)) R ∩ {z | z (Fin.last m) = 0},
      lelongNumber (n := m + 1) u z) ≤
      ENNReal.ofReal (2 * ((a (Fin.last m) : ℝ) + 1) / c) := by
  have hc : 0 < c := hint.1
  by_contra hle
  have hlt := lt_of_not_ge hle
  obtain ⟨γ, hγlower, hγupper⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hlt
  have hγ0 : (0 : ℝ≥0∞) < γ := bot_le.trans_lt hγlower
  have hγr : (0 : ℝ) < γ := by exact_mod_cast hγ0
  have hγreal : 2 * ((a (Fin.last m) : ℝ) + 1) / c < (γ : ℝ) :=
    (ENNReal.ofReal_lt_ofReal_iff hγr).mp (by
      simpa only [ENNReal.ofReal_coe_nnreal] using hγlower)
  have hthresh := threshold_of_integrability hu a hH hnot heq hint hR hγupper
  have hbad := (div_lt_iff₀ hc).mp hγreal
  nlinarith

private theorem lelongNumber_comp_linearEquiv_eq {n : ℕ}
    (L : ComplexModel n ≃L[ℂ] ComplexModel n) (u : ComplexModel n → EReal)
    (z : ComplexModel n) :
    lelongNumber (n := n) (u ∘ L) z = lelongNumber (n := n) u (L z) := by
  let Φ : LocalHolomorphicEquivAt (n := n) (0 : ComplexModel n) := {
    source := univ
    target := univ
    isOpen_source := isOpen_univ
    isOpen_target := isOpen_univ
    center_mem_source := mem_univ _
    toFun := L.symm
    invFun := L
    toFun_holomorphic := L.symm.differentiable.differentiableOn
    invFun_holomorphic := L.differentiable.differentiableOn
    mapsTo_toFun := mapsTo_univ _ _
    mapsTo_invFun := mapsTo_univ _ _
    left_inv := fun w _ => L.apply_symm_apply w
    right_inv := fun w _ => L.symm_apply_apply w }
  have h := LocalHolomorphicLelongReaderCovariance.lelongNumber_comp_inv_eq
    Φ (x := L z) (mem_univ _) (u := u)
  simpa only [Φ, L.symm_apply_apply, Function.comp_def] using h

/-- The original finite integral bounds every coordinate reader using the
actual given orders, without extracting a second factorization. -/
theorem iInf_lelongNumber_coordinate_le_of_multiplier_integrable {n : ℕ}
    {u : ComplexModel n → EReal} (hu : QuasiPlurisubharmonicAt u 0)
    (a : Fin n → ℕ) {F H : ComplexModel n → ℂ}
    (hH : ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ H z)
    (hnot : ∀ j : Fin n, ¬HolGerm.mk (fun z : ComplexModel n => z j)
      (eventually_differentiableAt_coordinate j) ∣ HolGerm.mk H hH)
    (heq : F =ᶠ[𝓝 0] fun z => H z * ∏ j : Fin n, z j ^ a j)
    {c : ℝ} (hint : MultiplierIntegrableAt u c F 0 volume)
    {R : ℝ} (hR : 0 < R) :
    ∀ j : Fin n,
      (⨅ z ∈ ball (0 : ComplexModel n) R ∩ {z | z j = 0},
        lelongNumber (n := n) u z) ≤ ENNReal.ofReal (2 * ((a j : ℝ) + 1) / c) := by
  classical
  cases n with
  | zero => exact fun j => Fin.elim0 j
  | succ m =>
    intro j
    let e : Equiv.Perm (Fin (m + 1)) := Equiv.swap j (Fin.last m)
    let T : ComplexModel (m + 1) ≃ₗᵢ[ℂ] ComplexModel (m + 1) :=
      LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e
    let L : ComplexModel (m + 1) ≃L[ℂ] ComplexModel (m + 1) := T.toContinuousLinearEquiv
    have hL (z : ComplexModel (m + 1)) (i : Fin (m + 1)) : (L z) i = z (e.symm i) := rfl
    have hLj (z : ComplexModel (m + 1)) : (L z) j = z (Fin.last m) := by
      rw [hL]
      simp [e]
    have hT : Tendsto L (𝓝 (0 : ComplexModel (m + 1))) (𝓝 0) :=
      HolGerm.tendsto_clm_nhds_zero (L : ComplexModel (m + 1) →L[ℂ] ComplexModel (m + 1))
    have hH' : ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), DifferentiableAt ℂ (H ∘ L) z :=
      eventually_differentiableAt_comp_clm (L : ComplexModel (m + 1) →L[ℂ] ComplexModel (m + 1)) hH
    have hnot' : ¬HolGerm.mk (fun z : ComplexModel (m + 1) => z (Fin.last m))
        (eventually_differentiableAt_coordinate (Fin.last m)) ∣ HolGerm.mk (H ∘ L) hH' := by
      have hcoord : HolGerm.comapEquiv L
          (HolGerm.mk (fun z : ComplexModel (m + 1) => z j)
            (eventually_differentiableAt_coordinate j)) =
          HolGerm.mk (fun z : ComplexModel (m + 1) => z (Fin.last m))
            (eventually_differentiableAt_coordinate (Fin.last m)) := by
        rw [HolGerm.comapEquiv_mk]
        apply HolGerm.mk_eq_mk_iff.mpr
        exact Eventually.of_forall fun z => hLj z
      intro hdiv
      apply hnot j
      apply (map_dvd_iff (HolGerm.comapEquiv L)).mp
      rw [hcoord, HolGerm.comapEquiv_mk]
      exact hdiv
    let a' : Fin (m + 1) → ℕ := fun i => a (e i)
    have hprod (z : ComplexModel (m + 1)) :
        (∏ i : Fin (m + 1), (L z) i ^ a i) = ∏ i : Fin (m + 1), z i ^ a' i := by
      simp only [hL, a']
      exact Fintype.prod_equiv e.symm _ _ fun i => by simp only [e.apply_symm_apply]
    have heq' : (F ∘ L) =ᶠ[𝓝 (0 : ComplexModel (m + 1))]
        fun z => (H ∘ L) z * ∏ i : Fin (m + 1), z i ^ a' i := by
      filter_upwards [hT.eventually heq] with z hz
      exact hz.trans (congrArg (fun w : ℂ => H (L z) * w) (hprod z))
    have hqu : QuasiPlurisubharmonicAt (u ∘ L) 0 := by
      have h := HolomorphicPullback.quasiPlurisubharmonicAt_comp_holomorphic
        (F := (L : ComplexModel (m + 1) → ComplexModel (m + 1))) isOpen_univ
        (contDiffOn_of_differentiableOn_complex L.differentiable.differentiableOn isOpen_univ)
        (mem_univ (0 : ComplexModel (m + 1)))
        (by simpa only [L.map_zero] using hu)
      exact h
    have hint' := (MultiplierHaarLinearTransport.multiplierIntegrableAt_continuousLinearEquiv_iff
      volume volume L (x := (0 : ComplexModel (m + 1)))).mpr
        (by simpa only [L.map_zero] using hint)
    have hlast := last_reader_le_of_factorization hqu a' hH' hnot' heq' hint' hR
    have hwhole : (⨅ z ∈ ball (0 : ComplexModel (m + 1)) R ∩ {z | z j = 0},
        lelongNumber (n := m + 1) u z) ≤
        ⨅ z ∈ ball (0 : ComplexModel (m + 1)) R ∩ {z | z (Fin.last m) = 0},
          lelongNumber (n := m + 1) (u ∘ L) z := by
      refine le_iInf fun z => le_iInf fun hz => ?_
      have hzball : L z ∈ ball (0 : ComplexModel (m + 1)) R := by
        rw [mem_ball_zero_iff]
        change ‖T z‖ < R
        rw [T.norm_map]
        exact mem_ball_zero_iff.mp hz.1
      have hzj : (L z) j = 0 := (hLj z).trans hz.2
      exact (iInf₂_le (f := fun w (_ : w ∈ ball (0 : ComplexModel (m + 1)) R ∩
        {w | w j = 0}) => lelongNumber (n := m + 1) u w) (L z) ⟨hzball, hzj⟩).trans_eq
          (lelongNumber_comp_linearEquiv_eq L u z).symm
    exact hwhole.trans (by simpa only [a', e, Equiv.swap_apply_right] using hlast)

end
end SGPT.Foundations.Analysis.Pending.RawQuasiPshGivenCoordinateOrderBounds
