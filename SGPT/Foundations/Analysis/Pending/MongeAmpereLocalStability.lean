import SGPT.Foundations.Analysis.Pending.AlexandrovBakelmanPucci
import SGPT.Foundations.Analysis.Pending.ComplexHessianDeterminant

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Local stability of the complex Monge--Ampère equation (Błocki's Proposition 3)

Let `Ω ⊆ ℂⁿ` be open, `u` of class `C²` on `Ω` with `det(u_{jk̄}) ≤ F` on `Ω`, `z₀ ∈ Ω`, `a > 0`,
`‖z - z₀‖ ≤ d` on `Ω`, and suppose the closure of `Ω' = {z ∈ Ω : u z < u z₀ + a}` is compact and
contained in `Ω`.  Then (`volume_ball_mul_le_lintegral`)

`vol(B(0, a/d)) · (-u(z₀) - a) ≤ 4ⁿ F² ∫_Ω (-u)`.

This is Błocki's Proposition 3 (`blocki05-uniform-estimate:page-0003`; `lnm2038-monge-ampere:page-0220`,
Proposition 5.12) with the `L²`-stability of Theorem 1 / Corollary 2 (`page-0002`) unfolded: for
`u ≤ 0` it says `-u(z₀) ≤ a + (4ⁿ / vol B(0,1)) (d/a)^{2n} ‖u‖_{L¹(Ω)} ‖f‖²_∞`, i.e.
`‖u‖_∞ ≤ a + (c_n diam Ω / a)^{2n} ‖u‖_{L¹} ‖f‖²_∞` at a minimum point `z₀`.  No plurisubharmonicity
is assumed: on the contact set `D²u ≥ 0`, so `det(u_{jk̄}) ≥ 0` there.

## Proof

With `t = u(z₀) + a < 0` and `v = u - t`, the Alexandrov--Bakelman--Pucci estimate on
`K = closure Ω'` gives `vol B(0, a/d) ≤ ∫_Γ det D²u` with `Γ ⊆ Ω' ∩ {D²u ≥ 0}`; there
`det D²u ≤ 4ⁿ det(u_{jk̄})² ≤ 4ⁿ F²` (`ComplexHessianDeterminant.det_le_four_pow_mul_sq`), so
`vol B(0, a/d) ≤ 4ⁿ F² vol(Ω')`, and `|t| vol(Ω') ≤ ∫_{Ω'} (-u) ≤ ∫_Ω (-u)`.

TN.4 B5, nonlinear track N2 (c); blueprint label proposed `bou:yau-local-stability`.
-/

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.MongeAmpereLocalStability

open FirstPass FirstPass.MongeAmpere SemiconcaveHessian GramDeterminant AlexandrovBakelmanPucci
  ComplexHessianDeterminant

variable {n : ℕ}

theorem finrank_complexModel : Module.finrank ℝ (ComplexModel n) = 2 * n := by
  rw [finrank_real_of_complex, finrank_euclideanSpace, Fintype.card_fin]

/-- **Błocki's Proposition 3** (local stability; `blocki05-uniform-estimate:page-0003`,
`lnm2038-monge-ampere:page-0220`), in measure form. -/
theorem volume_ball_mul_le_lintegral {Ω : Set (ComplexModel n)} (hΩ : IsOpen Ω)
    {u : ComplexModel n → ℝ} (hu : ContDiffOn ℝ 2 u Ω) {F : ℝ}
    (hF : ∀ z ∈ Ω, (complexHessian u z).det.re ≤ F) {z₀ : ComplexModel n} (hz₀ : z₀ ∈ Ω)
    {a d : ℝ} (ha : 0 < a) (hd : ∀ z ∈ Ω, ‖z - z₀‖ ≤ d)
    (hK : IsCompact (closure {z | z ∈ Ω ∧ u z < u z₀ + a}))
    (hKΩ : closure {z | z ∈ Ω ∧ u z < u z₀ + a} ⊆ Ω) :
    volume (ball (0 : ComplexModel n) (a / d)) * ENNReal.ofReal (-u z₀ - a) ≤
      ENNReal.ofReal (4 ^ n * F ^ 2) * ∫⁻ z in Ω, ENNReal.ofReal (-u z) := by
  set t := u z₀ + a with ht
  rcases le_or_gt 0 t with ht0 | ht0
  · have : -u z₀ - a ≤ 0 := by linarith
    rw [ENNReal.ofReal_of_nonpos this, mul_zero]
    exact zero_le
  set Ω' := {z | z ∈ Ω ∧ u z < t} with hΩ'
  set K := closure Ω' with hKdef
  have hΩ'open : IsOpen Ω' := hu.continuousOn.isOpen_inter_preimage hΩ isOpen_Iio
  have hΩ'K : Ω' ⊆ interior K := hΩ'open.subset_interior_iff.mpr subset_closure
  set v : ComplexModel n → ℝ := fun z => u z - t with hvdef
  have hv : ContDiffOn ℝ 2 v Ω := hu.sub contDiffOn_const
  have hz₀Ω' : z₀ ∈ Ω' := ⟨hz₀, by rw [ht]; linarith⟩
  have hfr : ∀ x ∈ K, x ∉ interior K → 0 ≤ v x := by
    intro x hxK hx
    have hxΩ : x ∈ Ω := hKΩ hxK
    have : ¬ (u x < t) := fun h => hx (hΩ'K ⟨hxΩ, h⟩)
    simp only [hvdef]; linarith [not_lt.mp this]
  have hdK : ∀ x ∈ K, ‖x - z₀‖ ≤ d := fun x hx => hd x (hKΩ hx)
  have hv₀ : v z₀ ≤ -a := by simp only [hvdef, ht]; linarith
  set b := stdOrthonormalBasis ℝ (ComplexModel n) with hb
  have habp := addHaar_ball_le_lintegral_det volume b hΩ hK hKΩ hv (subset_closure hz₀Ω') hv₀
    hfr hdK
  -- `D²v = D²u`
  have hD2 : fderiv ℝ (fderiv ℝ v) = fderiv ℝ (fderiv ℝ u) := by
    have : fderiv ℝ v = fderiv ℝ u := by
      funext z; simp only [hvdef]; exact fderiv_sub_const _
    rw [this]
  simp only [hD2] at habp
  set Γ := {x | x ∈ interior K ∧ v x < 0 ∧ ∀ h, 0 ≤ fderiv ℝ (fderiv ℝ u) x h h} with hΓ
  have hΓΩ' : Γ ⊆ Ω' := fun x hx => by
    refine ⟨hKΩ (interior_subset hx.1), ?_⟩
    have := hx.2.1; simp only [hvdef] at this; linarith
  -- the pointwise bound on `Γ`
  have hpt : ∀ x ∈ Γ, ENNReal.ofReal
      (Matrix.of fun i j => fderiv ℝ (fderiv ℝ u) x (b i) (b j)).det ≤
        ENNReal.ofReal (4 ^ n * F ^ 2) := by
    intro x hx
    have hxΩ : x ∈ Ω := (hΓΩ' hx).1
    have hux : ContDiffAt ℝ 2 u x := hu.contDiffAt (hΩ.mem_nhds hxΩ)
    have hsymm : ∀ h k, fderiv ℝ (fderiv ℝ u) x h k = fderiv ℝ (fderiv ℝ u) x k h :=
      fun h k => hux.isSymmSndFDerivAt (by simp) h k
    have h1 := det_le_four_pow_mul_sq b (fderiv ℝ (fderiv ℝ u) x) hsymm hx.2.2
    have h0 := re_det_nonneg hsymm hx.2.2
    rw [← complexHessian_eq_complexHessianOfBilin] at h1 h0
    have hFx := hF x hxΩ
    refine ENNReal.ofReal_le_ofReal (h1.trans ?_)
    gcongr
  have hΓm : MeasurableSet Γ := by
    have := measurableSet_contact hKΩ hv
    rwa [hD2] at this
  have h2 : volume (ball (0 : ComplexModel n) (a / d)) ≤
      ENNReal.ofReal (4 ^ n * F ^ 2) * volume Ω' := by
    calc volume (ball (0 : ComplexModel n) (a / d))
        ≤ ∫⁻ x in Γ, ENNReal.ofReal
            (Matrix.of fun i j => fderiv ℝ (fderiv ℝ u) x (b i) (b j)).det := habp
      _ ≤ ∫⁻ _ in Γ, ENNReal.ofReal (4 ^ n * F ^ 2) := setLIntegral_mono' hΓm hpt
      _ = ENNReal.ofReal (4 ^ n * F ^ 2) * volume Γ := setLIntegral_const _ _
      _ ≤ ENNReal.ofReal (4 ^ n * F ^ 2) * volume Ω' := by gcongr
  -- Chebyshev on `Ω'`
  have h3 : volume Ω' * ENNReal.ofReal (-t) ≤ ∫⁻ z in Ω, ENNReal.ofReal (-u z) := by
    calc volume Ω' * ENNReal.ofReal (-t) = ∫⁻ _ in Ω', ENNReal.ofReal (-t) := by
          rw [setLIntegral_const, mul_comm]
      _ ≤ ∫⁻ z in Ω', ENNReal.ofReal (-u z) :=
          setLIntegral_mono' hΩ'open.measurableSet fun z hz =>
            ENNReal.ofReal_le_ofReal (by linarith [hz.2])
      _ ≤ ∫⁻ z in Ω, ENNReal.ofReal (-u z) := lintegral_mono_set fun z hz => hz.1
  have hneg : -u z₀ - a = -t := by rw [ht]; ring
  rw [hneg]
  calc volume (ball (0 : ComplexModel n) (a / d)) * ENNReal.ofReal (-t)
      ≤ ENNReal.ofReal (4 ^ n * F ^ 2) * volume Ω' * ENNReal.ofReal (-t) := by gcongr
    _ = ENNReal.ofReal (4 ^ n * F ^ 2) * (volume Ω' * ENNReal.ofReal (-t)) := by ring
    _ ≤ ENNReal.ofReal (4 ^ n * F ^ 2) * ∫⁻ z in Ω, ENNReal.ofReal (-u z) := by gcongr

/-- The same estimate in the form posted on I-0831 C-0049 (`0 < n`), with
`vol B(0, a/d) = (a/d)^{2n} vol B(0, 1)`. -/
theorem ofReal_mul_le_lintegral (hn : 0 < n) {Ω : Set (ComplexModel n)} (hΩ : IsOpen Ω)
    {u : ComplexModel n → ℝ} (hu : ContDiffOn ℝ 2 u Ω) {F : ℝ}
    (hF : ∀ z ∈ Ω, (complexHessian u z).det.re ≤ F) {z₀ : ComplexModel n} (hz₀ : z₀ ∈ Ω)
    {a d : ℝ} (ha : 0 < a) (hd : ∀ z ∈ Ω, ‖z - z₀‖ ≤ d)
    (hK : IsCompact (closure {z | z ∈ Ω ∧ u z < u z₀ + a}))
    (hKΩ : closure {z | z ∈ Ω ∧ u z < u z₀ + a} ⊆ Ω) :
    ENNReal.ofReal ((a / d) ^ (2 * n)) * volume (ball (0 : ComplexModel n) 1) *
        ENNReal.ofReal (-u z₀ - a) ≤
      ENNReal.ofReal (4 ^ n * F ^ 2) * ∫⁻ z in Ω, ENNReal.ofReal (-u z) := by
  have hd0 : 0 ≤ d := by simpa using hd z₀ hz₀
  have : Nontrivial (ComplexModel n) := by
    have : 0 < Module.finrank ℝ (ComplexModel n) := by rw [finrank_complexModel]; omega
    exact Module.nontrivial_of_finrank_pos this
  have hball := Measure.addHaar_ball (volume : Measure (ComplexModel n)) (0 : ComplexModel n)
    (div_nonneg ha.le hd0)
  rw [finrank_complexModel] at hball
  rw [← hball]
  exact volume_ball_mul_le_lintegral hΩ hu hF hz₀ ha hd hK hKΩ

end SGPT.Foundations.Analysis.Pending.MongeAmpereLocalStability
