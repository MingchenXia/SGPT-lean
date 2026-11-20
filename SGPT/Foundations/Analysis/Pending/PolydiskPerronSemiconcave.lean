import SGPT.Foundations.Analysis.Pending.PerronEnvelopeVanishingMass
import SGPT.Foundations.Analysis.Pending.PolydiskMobiusSemiconcave

set_option autoImplicit false

/-!
# Balayage on the polydisk, for `C²` data

`Pending.PerronEnvelopeVanishingMass` proves that the Perron--Bremermann
envelope of continuous boundary data on the unit polydisk carries no
Bedford--Taylor mass *provided it is locally semiconcave*, that hypothesis
being Blocki's `C^{1,1}` estimate (Theorem 2.3.2).  That module keeps the
hypothesis, and so does Blocki's maximality criterion
`Pending.MaximalPshVanishingMass`; neither is changed here.

This module discharges that hypothesis **on the `C²` stratum only**, and it
is worth saying exactly how far that is from what Xia's Lemma 2.4.3
(`xia-sgpt:page-0079`) balayages.  Both halves of Blocki's Theorem 2.3.2 are
now available:

* the pluripotential half, `IsPerronData.secondDifference_perronEnvelope_le`
  (`Pending.PolydiskSecondDifference`): the Mobius competitor transports a
  *boundary* second-difference bound to the envelope;
* the half about the data, `exists_secondDifference_bound`
  (`Pending.PolydiskMobiusSemiconcave`): one constant works for the whole
  family, by compactness of the parameter box.

The step left here is the bookkeeping that turns a point of the polydisk into
a box: a closed ball `closedBall z₀ (2r)` inside the polydisk is compact, so
each coordinate modulus attains a maximum `< 1` on it, and the finitely many
maxima have a supremum `rho < 1`.

**What is NOT proved here.**  Lemma 2.4.3 balayages a locally bounded
`theta`-PSH function, whose boundary values on a ball are bounded and upper
semicontinuous — neither `C²` nor even continuous.  The `C²` restriction is
intrinsic to Theorem 2.3.2 (for merely continuous data the envelope need not
be semiconcave), so Blocki reaches the general case by mollifying, solving for
each smooth `u_j`, and passing to the decreasing limit.  Two ingredients of
that passage are absent from this workspace and are what item 4 of the
Theorem 2.4.4 stack (inbox I-0267) still costs:

1. monotonicity of `perronEnvelope` in the data, and the identification of the
   decreasing limit of the envelopes;
2. stability of `Pending.BedfordTaylor.IsBTLimit` along a **decreasing
   sequence of locally bounded plurisubharmonic functions** — the predicate is
   defined through `IsAdmissible`/`IsDecApprox`, i.e. through decreasing
   *smooth* approximations of a single potential, and nothing lets the
   approximated potentials themselves vary along a decreasing sequence.

Until both exist, the statements below apply to `C²` data and to nothing
else.

Source: Z. Blocki, *The complex Monge--Ampere operator in pluripotential
theory*, lecture notes, Theorems 2.3.1 and 2.3.2.
-/

noncomputable section

open Set Filter Metric MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff

namespace SGPT.Foundations.Analysis.Pending.BedfordTaylor

open FirstPass FirstPass.MongeAmpere

variable {n : ℕ}

/-- **Blocki's `C^{1,1}` estimate on the polydisk.**  The Perron--Bremermann
envelope of `C²` data is locally semiconcave. -/
theorem IsPerronData.isLocallySemiconcaveOn_perronEnvelope {v : ComplexModel n → ℝ}
    (hv : IsPerronData v) (hv2 : ContDiff ℝ 2 v) :
    IsLocallySemiconcaveOn (unitPolydiskOpens n) (perronEnvelope v) := by
  classical
  intro z₀ hz₀
  have : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hv.pos
  have hz₀P : z₀ ∈ unitPolydisk n := hz₀
  obtain ⟨r₀, hr₀, hball⟩ := Metric.isOpen_iff.mp isOpen_unitPolydisk z₀ hz₀P
  set r : ℝ := r₀ / 4 with hrdef
  have hr : 0 < r := by positivity
  have h2r : closedBall z₀ (2 * r) ⊆ unitPolydisk n := by
    refine subset_trans (closedBall_subset_ball ?_) hball
    rw [hrdef]; linarith
  -- a uniform coordinate bound on the compact ball
  have hK : IsCompact (closedBall z₀ (2 * r)) := isCompact_closedBall _ _
  have hKne : (closedBall z₀ (2 * r)).Nonempty :=
    ⟨z₀, mem_closedBall_self (by positivity)⟩
  have hmaxpt : ∀ i : Fin n, ∃ c ∈ closedBall z₀ (2 * r),
      IsMaxOn (fun y : ComplexModel n => ‖y i‖) (closedBall z₀ (2 * r)) c :=
    fun i => hK.exists_isMaxOn hKne
      (continuous_norm.comp ((EuclideanSpace.proj (𝕜 := ℂ) i).continuous)).continuousOn
  choose c hc hcmax using hmaxpt
  set rho : ℝ := Finset.univ.sup' Finset.univ_nonempty (fun i => ‖c i i‖) with hrhodef
  have hrho1 : rho < 1 := by
    rw [hrhodef, Finset.sup'_lt_iff]
    exact fun i _ => h2r (hc i) i
  have hcoord : ∀ y ∈ closedBall z₀ (2 * r), ∀ i, ‖y i‖ ≤ rho := by
    intro y hy i
    refine le_trans (isMaxOn_iff.mp (hcmax i) y hy) ?_
    exact Finset.le_sup' (fun j => ‖c j j‖) (Finset.mem_univ i)
  obtain ⟨M, hM0, hMbd⟩ := exists_secondDifference_bound (n := n) v hv2 hrho1
  refine ⟨r, M, hr, hM0, h2r, ?_⟩
  intro y hy h hh
  have hyc : y ∈ closedBall z₀ (2 * r) :=
    (closedBall_subset_closedBall (by linarith)) hy
  have hydist : ‖y - z₀‖ ≤ r := by
    rw [← dist_eq_norm]; exact mem_closedBall.mp hy
  have hyp : y + h ∈ closedBall z₀ (2 * r) := by
    rw [mem_closedBall, dist_eq_norm]
    calc ‖y + h - z₀‖ = ‖(y - z₀) + h‖ := by
          rw [show y + h - z₀ = (y - z₀) + h from by abel]
      _ ≤ ‖y - z₀‖ + ‖h‖ := norm_add_le _ _
      _ ≤ 2 * r := by linarith
  have hym : y - h ∈ closedBall z₀ (2 * r) := by
    rw [mem_closedBall, dist_eq_norm]
    calc ‖y - h - z₀‖ = ‖(y - z₀) - h‖ := by
          rw [show y - h - z₀ = (y - z₀) - h from by abel]
      _ ≤ ‖y - z₀‖ + ‖h‖ := norm_sub_le _ _
      _ ≤ 2 * r := by linarith
  have ha : ∀ i, ‖y i‖ < 1 := fun i => h2r hyc i
  have hah : ∀ i, ‖y i + h i‖ < 1 := fun i => by
    have hmem := h2r hyp i
    rwa [complexModel_add_apply] at hmem
  have hah' : ∀ i, ‖y i + (-h : ComplexModel n) i‖ < 1 := fun i => by
    have hmem := h2r hym i
    rw [complexModel_sub_apply] at hmem
    simpa [sub_eq_add_neg] using hmem
  have hbnd : ∀ ζ ∈ closedUnitPolydisk n \ unitPolydisk n,
      v (polydiskAut y h ζ) + v (polydiskAut y (-h) ζ) - 2 * v ζ ≤
        2 * (M * ‖h‖ ^ 2 / 2) := by
    intro ζ hζ
    have hb := hMbd y h (hcoord y hyc)
      (fun i => by rw [← complexModel_add_apply]; exact hcoord _ hyp i)
      (fun i => by rw [← complexModel_sub_apply]; exact hcoord _ hym i) ζ hζ.1
    linarith
  have hfin := hv.secondDifference_perronEnvelope_le ha hah hah' hbnd
  linarith

/-- **Balayage on the polydisk, for `C²` data.**  The
Perron--Bremermann envelope of `C²` boundary data solves the homogeneous
Monge--Ampere equation: every Bedford--Taylor limit of the constant tuple
`(u, ..., u)` on the polydisk is the zero measure.

This is `Pending.PerronEnvelopeVanishingMass.IsPerronData.eq_zero_of_isBTLimit_perronEnvelope`
with its semiconcavity hypothesis discharged. -/
theorem IsPerronData.eq_zero_of_isBTLimit_perronEnvelope_of_contDiff
    {v : ComplexModel n → ℝ} (hv : IsPerronData v) (hv2 : ContDiff ℝ 2 v)
    {μ : Measure (ComplexModel n)}
    (hμ : IsBTLimit (unitPolydiskOpens n) (fun _ => perronEnvelope v) μ) :
    μ = 0 :=
  hv.eq_zero_of_isBTLimit_perronEnvelope
    (hv.isLocallySemiconcaveOn_perronEnvelope hv2) hμ

end SGPT.Foundations.Analysis.Pending.BedfordTaylor


end
