import SGPT.Foundations.Analysis.Pending.KiselmanMinimumPrincipleProof
import SGPT.Foundations.Analysis.Pending.FiniteGeodesicMaximality
import SGPT.Foundations.Analysis.PlurisubharmonicLimits

/-!
# Actual Kiselman minima with a varying holomorphic logarithmic endpoint

The complete mathematical proofs precede this file in
`blueprint/src/dnt-big-holomorphic-radius.tex`. The domain and all infima are
actual subsets and values. Holomorphic change of variables transports each
moving finite window to the proved fixed strip; a decreasing exhaustion then
handles the whole varying logarithmic half-line. No quadratic smoothing bound
or regularity output is assumed.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric
open scoped Topology

namespace SGPT.NPP.DNTBig

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.FiniteGeodesicMaximality

variable {n : ℕ}

/-- The actual moving logarithmic half-plane in the product. -/
def holomorphicRadiusDomain (U : Set (ComplexModel n)) (h : ComplexModel n → ℂ) :
    Set (ComplexModel n × ℂ) :=
  {p | p.1 ∈ U ∧ p.2.re < (h p.1).re}

/-- The actual infimum on a finite window ending at `Re h(z)`. -/
def movingWindowMinimum (Φ : ComplexModel n × ℂ → EReal) (h : ComplexModel n → ℂ)
    (L : ℝ) (z : ComplexModel n) : EReal :=
  ⨅ t : ↥(Ioo ((h z).re - L) (h z).re), Φ (z, ((t : ℝ) : ℂ))

/-- The actual infimum on the full half-line below `Re h(z)`. -/
def movingHalfLineMinimum (Φ : ComplexModel n × ℂ → EReal)
    (h : ComplexModel n → ℂ) (z : ComplexModel n) : EReal :=
  ⨅ t : ↥(Iio (h z).re), Φ (z, ((t : ℝ) : ℂ))

/-- The actual infimum over positive radii below `exp (Re h(z))`. -/
def holomorphicRadiusMinimum (Φ : ComplexModel n × ℂ → EReal)
    (h : ComplexModel n → ℂ) (z : ComplexModel n) : EReal :=
  ⨅ r : ↥(Ioo (0 : ℝ) (Real.exp (h z).re)), Φ (z, ((Real.log (r : ℝ)) : ℂ))

private theorem plurisubharmonicOn_comp_product_holomorphic
    {F : ComplexModel n × ℂ → ComplexModel n × ℂ}
    {Φ : ComplexModel n × ℂ → EReal} {V W : Set (ComplexModel n × ℂ)}
    (hV : IsOpen V) (hF : DifferentiableOn ℂ F V) (hFW : MapsTo F V W)
    (hΦ : PlurisubharmonicOn Φ W) : PlurisubharmonicOn (fun p => Φ (F p)) V := by
  let e := stripModelEquiv n
  let A : Set (ComplexModel (n + 1)) := e ⁻¹' V
  let G : ComplexModel (n + 1) → ComplexModel (n + 1) := fun q => e.symm (F (e q))
  have hA : IsOpen A := hV.preimage e.continuous
  have hFe : DifferentiableOn ℂ (fun q => F (e q)) A :=
    hF.comp e.differentiable.differentiableOn (fun q hq => hq)
  have hG : DifferentiableOn ℂ G A :=
    e.symm.differentiable.comp_differentiableOn hFe
  have htarget := hΦ.comp_continuousLinearMap (e : ComplexModel (n + 1) →L[ℂ] _)
  have hGW : MapsTo G A (e ⁻¹' W) := by
    intro q hq
    change e (e.symm (F (e q))) ∈ W
    rw [e.apply_symm_apply]
    exact hFW hq
  have hp := HolomorphicPullback.plurisubharmonicOn_comp_holomorphic hA hG hGW htarget
  have hback := hp.comp_continuousLinearMap
    (e.symm : (ComplexModel n × ℂ) →L[ℂ] ComplexModel (n + 1))
  convert hback using 1
  · funext p
    change Φ (F p) = Φ (e (e.symm (F (e (e.symm p)))))
    rw [e.apply_symm_apply, e.apply_symm_apply]
  · ext p
    change p ∈ V ↔ e (e.symm p) ∈ V
    rw [e.apply_symm_apply]

/-- A holomorphic logarithmic endpoint gives genuine moving finite-window
minima; this is proved by holomorphic pullback and an exact parameter change. -/
theorem plurisubharmonicOn_movingWindowMinimum {U : Set (ComplexModel n)}
    (hU : IsOpen U) {h : ComplexModel n → ℂ} (hh : DifferentiableOn ℂ h U)
    {Φ : ComplexModel n × ℂ → EReal}
    (hΦ : PlurisubharmonicOn Φ (holomorphicRadiusDomain U h))
    (hinv : ∀ z (τ σ : ℂ), τ.re = σ.re → Φ (z, τ) = Φ (z, σ))
    {L : ℝ} (hL : 0 < L) : PlurisubharmonicOn (movingWindowMinimum Φ h L) U := by
  let F : ComplexModel n × ℂ → ComplexModel n × ℂ := fun p =>
    (p.1, h p.1 - (L : ℂ) + (L : ℂ) * p.2)
  have hS : IsOpen (U ×ˢ complexTimeStrip) := hU.prod isOpen_complexTimeStrip
  have hF : DifferentiableOn ℂ F (U ×ˢ complexTimeStrip) := by
    have hhfst : DifferentiableOn ℂ (fun p : ComplexModel n × ℂ => h p.1)
        (U ×ˢ complexTimeStrip) :=
      hh.comp differentiable_fst.differentiableOn (fun p hp => hp.1)
    exact differentiable_fst.differentiableOn.prodMk
      ((hhfst.sub_const (L : ℂ)).add
        ((differentiable_const (L : ℂ)).differentiableOn.mul
          differentiable_snd.differentiableOn))
  have hmaps : MapsTo F (U ×ˢ complexTimeStrip) (holomorphicRadiusDomain U h) := by
    intro p hp
    have ht := mem_complexTimeStrip.mp hp.2
    refine ⟨hp.1, ?_⟩
    change (h p.1 - (L : ℂ) + (L : ℂ) * p.2).re < (h p.1).re
    simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    nlinarith [ht.2]
  have hp := plurisubharmonicOn_comp_product_holomorphic hS hF hmaps hΦ
  have hinvF : ∀ z (τ σ : ℂ), τ.re = σ.re → Φ (F (z, τ)) = Φ (F (z, σ)) := by
    intro z τ σ hτσ
    apply hinv
    simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, zero_mul, sub_zero, hτσ]
  have hmin := KiselmanMinimumPrincipleProof.plurisubharmonicOn_iInf_slices hU hp hinvF
  have heq : ∀ z, movingWindowMinimum Φ h L z =
      ⨅ s : ↥(Ioo (0 : ℝ) 1), Φ (F (z, ((s : ℝ) : ℂ))) := by
    intro z
    apply le_antisymm
    · refine le_iInf fun s => ?_
      let t : ↥(Ioo ((h z).re - L) (h z).re) :=
        ⟨(h z).re - L + L * (s : ℝ), by constructor <;> nlinarith [s.2.1, s.2.2]⟩
      refine (iInf_le (fun t : ↥(Ioo ((h z).re - L) (h z).re) =>
        Φ (z, ((t : ℝ) : ℂ))) t).trans_eq ?_
      apply hinv
      simp only [t, Complex.ofReal_re, Complex.add_re, Complex.sub_re,
        Complex.mul_re, Complex.ofReal_im, zero_mul, sub_zero]
    · refine le_iInf fun t => ?_
      let s : ↥(Ioo (0 : ℝ) 1) :=
        ⟨((t : ℝ) - (h z).re + L) / L, div_pos (by linarith [t.2.1]) hL,
          (div_lt_one hL).mpr (by linarith [t.2.2])⟩
      refine (iInf_le (fun s : ↥(Ioo (0 : ℝ) 1) =>
        Φ (F (z, ((s : ℝ) : ℂ)))) s).trans_eq ?_
      apply hinv
      simp only [s, Complex.add_re, Complex.sub_re, Complex.ofReal_re,
        Complex.mul_re, Complex.ofReal_im, zero_mul, sub_zero]
      field_simp
      ring
  have hfun : movingWindowMinimum Φ h L =
      fun z => ⨅ s : ↥(Ioo (0 : ℝ) 1), Φ (F (z, ((s : ℝ) : ℂ))) := funext heq
  rw [hfun]
  exact hmin

/-- Finite moving windows exhaust the actual moving logarithmic half-line.
The decreasing PSH limit retains possible genuine poles. -/
theorem plurisubharmonicOn_movingHalfLineMinimum {U : Set (ComplexModel n)}
    (hU : IsOpen U) {h : ComplexModel n → ℂ} (hh : DifferentiableOn ℂ h U)
    {Φ : ComplexModel n × ℂ → EReal}
    (hΦ : PlurisubharmonicOn Φ (holomorphicRadiusDomain U h))
    (hinv : ∀ z (τ σ : ℂ), τ.re = σ.re → Φ (z, τ) = Φ (z, σ)) :
    PlurisubharmonicOn (movingHalfLineMinimum Φ h) U := by
  let f : ℕ → ComplexModel n → EReal := fun j => movingWindowMinimum Φ h ((j : ℝ) + 1)
  have hpsh : ∀ j, PlurisubharmonicOn (f j) U := fun j =>
    plurisubharmonicOn_movingWindowMinimum hU hh hΦ hinv (by positivity)
  have hanti : ∀ z ∈ U, Antitone (fun j => f j z) := by
    intro z _ i j hij
    refine le_iInf fun t => ?_
    have ht : (t : ℝ) ∈ Ioo ((h z).re - ((j : ℝ) + 1)) (h z).re := by
      refine ⟨?_, t.2.2⟩
      have hc : (i : ℝ) ≤ j := Nat.cast_le.mpr hij
      linarith [t.2.1]
    exact iInf_le (fun s : ↥(Ioo ((h z).re - ((j : ℝ) + 1)) (h z).re) =>
      Φ (z, ((s : ℝ) : ℂ))) ⟨t, ht⟩
  have hlim := DiscPshOn.plurisubharmonicOn_iInf_of_antitone hU
    (fun j => (hpsh j).discPshOn) hanti
  have heq : ∀ z, movingHalfLineMinimum Φ h z = ⨅ j, f j z := by
    intro z
    apply le_antisymm
    · refine le_iInf fun j => le_iInf fun t => ?_
      exact iInf_le (fun s : ↥(Iio (h z).re) => Φ (z, ((s : ℝ) : ℂ))) ⟨t, t.2.2⟩
    · refine le_iInf fun t => ?_
      obtain ⟨j, hj⟩ := exists_nat_gt ((h z).re - (t : ℝ))
      have ht : (t : ℝ) ∈ Ioo ((h z).re - ((j : ℝ) + 1)) (h z).re :=
        ⟨by linarith, t.2⟩
      exact (iInf_le (fun j => f j z) j).trans
        (iInf_le (fun s : ↥(Ioo ((h z).re - ((j : ℝ) + 1)) (h z).re) =>
          Φ (z, ((s : ℝ) : ℂ))) ⟨t, ht⟩)
  have hfun : movingHalfLineMinimum Φ h = fun z => ⨅ j, f j z := funext heq
  rw [hfun]
  exact hlim

/-- The actual positive-radius infimum below `exp (Re h(z))` is PSH.
The exponential/logarithm bijection is proved on its actual varying fibres. -/
theorem plurisubharmonicOn_holomorphicRadiusMinimum {U : Set (ComplexModel n)}
    (hU : IsOpen U) {h : ComplexModel n → ℂ} (hh : DifferentiableOn ℂ h U)
    {Φ : ComplexModel n × ℂ → EReal}
    (hΦ : PlurisubharmonicOn Φ (holomorphicRadiusDomain U h))
    (hinv : ∀ z (τ σ : ℂ), τ.re = σ.re → Φ (z, τ) = Φ (z, σ)) :
    PlurisubharmonicOn (holomorphicRadiusMinimum Φ h) U := by
  have heq : ∀ z, holomorphicRadiusMinimum Φ h z = movingHalfLineMinimum Φ h z := by
    intro z
    apply le_antisymm
    · refine le_iInf fun t => ?_
      let r : ↥(Ioo (0 : ℝ) (Real.exp (h z).re)) :=
        ⟨Real.exp (t : ℝ), Real.exp_pos _, Real.exp_lt_exp.mpr t.2⟩
      have h := iInf_le (fun r : ↥(Ioo (0 : ℝ) (Real.exp (h z).re)) =>
        Φ (z, ((Real.log (r : ℝ)) : ℂ))) r
      simpa only [holomorphicRadiusMinimum, r, Real.log_exp] using h
    · refine le_iInf fun r => ?_
      have ht : Real.log (r : ℝ) < (h z).re :=
        (Real.log_lt_iff_lt_exp r.2.1).mpr r.2.2
      exact iInf_le (fun t : ↥(Iio (h z).re) => Φ (z, ((t : ℝ) : ℂ)))
        ⟨Real.log (r : ℝ), ht⟩
  have hfun : holomorphicRadiusMinimum Φ h = movingHalfLineMinimum Φ h := funext heq
  rw [hfun]
  exact plurisubharmonicOn_movingHalfLineMinimum hU hh hΦ hinv

end SGPT.NPP.DNTBig
