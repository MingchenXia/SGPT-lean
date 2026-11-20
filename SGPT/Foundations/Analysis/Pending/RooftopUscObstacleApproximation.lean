import SGPT.Foundations.Analysis.Pending.ContinuousObstacleEnvelopeContact
import SGPT.Foundations.Analysis.Pending.ThetaPshDecreasingLimit
import SGPT.Foundations.Analysis.Pending.DiagonalMeasureRegularity
import SGPT.Foundations.Analysis.FirstPass.ContinuousUscMajorants

set_option autoImplicit false

/-!
# The envelope of an upper semicontinuous obstacle as a decreasing limit

Xia's Theorem 2.4.4 (`xia-sgpt:page-0079`) is proved in the source by reducing
a quasi-continuous obstacle to a *lower* semicontinuous one: Step 2
(`xia-sgpt:page-0082`) applies Tietze on the small-capacity complements of `f`,
obtains continuous `f_k`, and runs Lemma 2.4.3 on `h_j = sup_{k >= j} f_k`.

For an **upper** semicontinuous obstacle — which is what the two obstacles of
Section 3.1 are, `min {phi, psi}` being a minimum of two `theta`-PSH functions
— there is a shorter and unconditional reduction, and it is what this module
proves.  A bounded-above upper semicontinuous function on a compact metrizable
space is the pointwise infimum of a *decreasing* sequence of continuous real
functions (`FirstPass.exists_continuous_antitone_majorants_on_compact`, the
metric sup-convolution), and the envelope commutes with that infimum:

  `P_theta(f) = inf_k P_theta(g_k)`   whenever `g_k` decreases to `f`.

The `<=` half is monotonicity of the envelope.  The `>=` half is the point:
`inf_k P_theta(g_k)` is `theta`-PSH (a decreasing limit of `theta`-PSH
functions) and lies below `g_k` for every `k` **pointwise**, because
`P_theta(g) <= g` holds *everywhere* for a continuous obstacle
(`Pending.ContinuousObstacleEnvelopeContact.rooftopEnvelope_le_of_continuous`).
So it lies below `f = inf_k g_k` everywhere, hence is a competitor for `f`.

No pluripolar set enters, so nothing here needs countable unions of pluripolar
sets — the obstruction that Xia's Step 1.2 hides in the phrase
"`inf_j P_theta(f_j) <= f` quasi-everywhere".

Two consequences are recorded: Xia's inequality (2.20) holds **everywhere** for
an upper semicontinuous obstacle, and the envelope of such an obstacle is a
genuine `theta`-PSH potential as soon as it has one competitor.
-/

open Set Filter
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.RooftopUscObstacleApproximation

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending.ThetaPshDecreasingLimit
open SGPT.Foundations.Analysis.Pending.DiagonalMeasureRegularity
open SGPT.Foundations.Analysis.Pending.ContinuousObstacleEnvelopeContact

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [Nonempty M]

/-! ### Decreasing continuous majorants on the manifold -/

/-- **A bounded-above upper semicontinuous function on a compact complex
manifold is the pointwise infimum of a decreasing sequence of continuous real
functions.**  This is the metric sup-convolution of
`FirstPass.exists_continuous_antitone_majorants_on_compact`, transported to the
manifold through its metrizability
(`Pending.DiagonalMeasureRegularity.metrizableSpace_of_isComplexManifold`). -/
theorem exists_continuous_antitone_majorants (n : ℕ) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]
    [Nonempty M] {f : M → EReal}
    (hf : UpperSemicontinuous f) (htop : ∀ x, f x ≠ ⊤) :
    ∃ (C : ℝ) (g : ℕ → M → ℝ),
      (∀ k, Continuous (g k)) ∧
      (∀ k x, f x ≤ ((g k x : ℝ) : EReal)) ∧
      (∀ k x, g k x ≤ C) ∧
      (∀ x, Antitone fun k => g k x) ∧
      (∀ x, (⨅ k : ℕ, ((g k x : ℝ) : EReal)) = f x) := by
  let _ := metrizableSpace_of_isComplexManifold n M
  let _ := TopologicalSpace.metrizableSpaceMetric M
  obtain ⟨C, g, hcont, hmaj, hbdd, hanti, hinf⟩ :=
    exists_continuous_antitone_majorants_on_compact (K := (univ : Set M))
      isCompact_univ univ_nonempty (hf.upperSemicontinuousOn univ)
      (fun x _ => htop x)
  exact ⟨C, g, hcont, fun k x => hmaj k x (mem_univ x), hbdd, hanti,
    fun x => hinf x (mem_univ x)⟩

/-! ### The envelope commutes with a decreasing limit of obstacles -/

variable {theta : ClosedRealOneOneForm n M}

/-- The infimum of the envelopes of a decreasing family of obstacles, as a
function on `M`. -/
private def iInfEnvelope (theta : ClosedRealOneOneForm n M) (g : ℕ → M → ℝ) :
    M → EReal :=
  fun x => ⨅ k : ℕ, rooftopEnvelope theta.val (fun y => ((g k y : ℝ) : EReal)) x

omit [CompactSpace M] [Nonempty M] in
/-- The envelopes of a decreasing family of obstacles decrease. -/
theorem antitone_rooftopEnvelope_of_antitone {g : ℕ → M → ℝ}
    (hanti : ∀ x, Antitone fun k => g k x) (x : M) :
    Antitone fun k => rooftopEnvelope theta.val (fun y => ((g k y : ℝ) : EReal)) x := by
  intro j k hjk
  exact rooftopEnvelope_mono (θ := theta.val)
    (fun y => EReal.coe_le_coe_iff.mpr (hanti y hjk)) x

omit [CompactSpace M] [Nonempty M] in
/-- The infimum of the envelopes is `theta`-PSH. -/
theorem thetaPlurisubharmonic_iInfEnvelope {g : ℕ → M → ℝ}
    (hanti : ∀ x, Antitone fun k => g k x)
    (hpsh : ∀ k, ThetaPlurisubharmonic theta.val
      (rooftopEnvelope theta.val (fun y => ((g k y : ℝ) : EReal)))) :
    ThetaPlurisubharmonic theta.val (iInfEnvelope theta g) :=
  thetaPlurisubharmonic_iInf_of_antitone hpsh
    (fun x => antitone_rooftopEnvelope_of_antitone hanti x)

omit [CompactSpace M] [Nonempty M] in
/-- Every competitor for the limit obstacle lies below the infimum of the
envelopes: it is a competitor for each member of the decreasing family. -/
theorem le_iInfEnvelope_of_mem_rooftopCompetitors {f : M → EReal} {g : ℕ → M → ℝ}
    (hgf : ∀ x, (⨅ k : ℕ, ((g k x : ℝ) : EReal)) = f x)
    {v : M → EReal} (hv : v ∈ rooftopCompetitors theta.val f) :
    v ≤ iInfEnvelope theta g := by
  intro x
  refine le_iInf fun k => ?_
  refine le_rooftopEnvelope hv.1 (hv.2.mono fun y hy => ?_) x
  exact hy.trans ((hgf y) ▸ iInf_le (fun j : ℕ => ((g j y : ℝ) : EReal)) k)

omit [CompactSpace M] [Nonempty M] in
/-- **The rooftop envelope commutes with a decreasing limit of obstacles whose
envelopes lie below them pointwise.**  The nontrivial half is `>=`: the
infimum of the envelopes is `theta`-PSH and lies below `f` *everywhere*, so it
is a competitor for `f`. -/
theorem rooftopEnvelope_eq_iInf_of_antitone {f : M → EReal} {g : ℕ → M → ℝ}
    (hgf : ∀ x, (⨅ k : ℕ, ((g k x : ℝ) : EReal)) = f x)
    (hanti : ∀ x, Antitone fun k => g k x)
    (hpsh : ∀ k, ThetaPlurisubharmonic theta.val
      (rooftopEnvelope theta.val (fun y => ((g k y : ℝ) : EReal))))
    (hple : ∀ k x,
      rooftopEnvelope theta.val (fun y => ((g k y : ℝ) : EReal)) x ≤ ((g k x : ℝ) : EReal))
    (hne : (rooftopCompetitors theta.val f).Nonempty) :
    rooftopEnvelope theta.val f = iInfEnvelope theta g := by
  obtain ⟨v, hv⟩ := hne
  have hvinf : v ≤ iInfEnvelope theta g := le_iInfEnvelope_of_mem_rooftopCompetitors hgf hv
  have hpot : IsThetaPshPotential theta.val (iInfEnvelope theta g) :=
    ⟨thetaPlurisubharmonic_iInfEnvelope hanti hpsh, hv.1.2.mono hvinf⟩
  have hlef : iInfEnvelope theta g ≤ f := by
    intro x
    rw [← hgf x]
    exact le_iInf fun k => (iInf_le _ k).trans (hple k x)
  refine le_antisymm ?_ (le_rooftopEnvelope hpot (quasiEverywhere_of_forall hlef))
  intro x
  refine le_iInf fun k => ?_
  refine rooftopEnvelope_mono (θ := theta.val) (fun y => ?_) x
  exact (hgf y) ▸ iInf_le (fun j : ℕ => ((g j y : ℝ) : EReal)) k

omit [CompactSpace M] [Nonempty M] in
/-- The **pointwise** reading of `rooftopEnvelope_eq_iInf_of_antitone`.  The
equality of functions there is stated against a private abbreviation for the
infimum; this is the form the concentration argument consumes. -/
theorem rooftopEnvelope_apply_eq_iInf_of_antitone {f : M → EReal} {g : ℕ → M → ℝ}
    (hgf : ∀ x, (⨅ k : ℕ, ((g k x : ℝ) : EReal)) = f x)
    (hanti : ∀ x, Antitone fun k => g k x)
    (hpsh : ∀ k, ThetaPlurisubharmonic theta.val
      (rooftopEnvelope theta.val (fun y => ((g k y : ℝ) : EReal))))
    (hple : ∀ k x,
      rooftopEnvelope theta.val (fun y => ((g k y : ℝ) : EReal)) x ≤ ((g k x : ℝ) : EReal))
    (hne : (rooftopCompetitors theta.val f).Nonempty) (x : M) :
    rooftopEnvelope theta.val f x =
      ⨅ k : ℕ, rooftopEnvelope theta.val (fun y => ((g k y : ℝ) : EReal)) x := by
  rw [rooftopEnvelope_eq_iInf_of_antitone hgf hanti hpsh hple hne]
  rfl

omit [CompactSpace M] [Nonempty M] in
/-- **The envelopes of the decreasing majorants converge to the envelope of the
limit obstacle**, pointwise.  This is the decreasing family that Xia's Theorem
2.4.4 runs the capacity argument along. -/
theorem tendsto_rooftopEnvelope_of_antitone {f : M → EReal} {g : ℕ → M → ℝ}
    (hgf : ∀ x, (⨅ k : ℕ, ((g k x : ℝ) : EReal)) = f x)
    (hanti : ∀ x, Antitone fun k => g k x)
    (hpsh : ∀ k, ThetaPlurisubharmonic theta.val
      (rooftopEnvelope theta.val (fun y => ((g k y : ℝ) : EReal))))
    (hple : ∀ k x,
      rooftopEnvelope theta.val (fun y => ((g k y : ℝ) : EReal)) x ≤ ((g k x : ℝ) : EReal))
    (hne : (rooftopCompetitors theta.val f).Nonempty) (x : M) :
    Tendsto (fun k => rooftopEnvelope theta.val (fun y => ((g k y : ℝ) : EReal)) x)
      atTop (𝓝 (rooftopEnvelope theta.val f x)) := by
  rw [rooftopEnvelope_apply_eq_iInf_of_antitone hgf hanti hpsh hple hne x]
  exact tendsto_atTop_iInf (antitone_rooftopEnvelope_of_antitone hanti x)

/-! ### Xia's (2.20) for an upper semicontinuous obstacle -/

/-- **Xia, SGPT, inequality (2.20) (`xia-sgpt:page-0078`) everywhere, for an
upper semicontinuous obstacle in a big class.**  `P_theta(f) <= f` pointwise,
with no quasi-everywhere exception, whenever `f` is upper semicontinuous and
never `+infinity`.

`Pending.ContinuousObstacleEnvelopeContact.rooftopEnvelope_le_of_continuous` is
the case of a continuous real obstacle; the general upper semicontinuous case
follows by writing `f` as a decreasing limit of continuous majorants.  For a
merely *lower* semicontinuous obstacle the statement is false — a single point
is pluripolar, so the envelope ignores a downward spike. -/
theorem rooftopEnvelope_le_of_upperSemicontinuous (hn : 0 < n)
    (theta : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative theta))
    {f : M → EReal} (hf : UpperSemicontinuous f) (htop : ∀ x, f x ≠ ⊤) :
    rooftopEnvelope theta.val f ≤ f := by
  classical
  rcases eq_empty_or_nonempty (rooftopCompetitors theta.val f) with hempty | hne
  · rw [rooftopEnvelope_of_empty hempty]
    exact fun _ => bot_le
  obtain ⟨C, g, hcont, -, -, hanti, hgf⟩ := exists_continuous_antitone_majorants n hf htop
  have hpotk : ∀ k, IsThetaPshPotential theta.val
      (rooftopEnvelope theta.val (fun y => ((g k y : ℝ) : EReal))) :=
    fun k => isThetaPshPotential_rooftopEnvelope_of_continuous hn theta hbig (hcont k)
  have hple : ∀ k x,
      rooftopEnvelope theta.val (fun y => ((g k y : ℝ) : EReal)) x ≤ ((g k x : ℝ) : EReal) :=
    fun k => rooftopEnvelope_le_of_continuous (hcont k)
      (rooftopCompetitors_nonempty_of_isBigClass hn theta hbig (hcont k)) (hpotk k).1
  rw [rooftopEnvelope_eq_iInf_of_antitone hgf hanti (fun k => (hpotk k).1) hple hne]
  intro x
  rw [← hgf x]
  exact le_iInf fun k => (iInf_le _ k).trans (hple k x)

/-- **The envelope of an upper semicontinuous obstacle in a big class is a
genuine `theta`-PSH potential** as soon as it has one competitor.  It is the
decreasing limit of the envelopes of the continuous majorants, each of which is
a potential by `isThetaPshPotential_rooftopEnvelope_of_continuous`. -/
theorem isThetaPshPotential_rooftopEnvelope_of_upperSemicontinuous (hn : 0 < n)
    (theta : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative theta))
    {f : M → EReal} (hf : UpperSemicontinuous f) (htop : ∀ x, f x ≠ ⊤)
    (hne : (rooftopCompetitors theta.val f).Nonempty) :
    IsThetaPshPotential theta.val (rooftopEnvelope theta.val f) := by
  classical
  obtain ⟨C, g, hcont, -, -, hanti, hgf⟩ := exists_continuous_antitone_majorants n hf htop
  have hpotk : ∀ k, IsThetaPshPotential theta.val
      (rooftopEnvelope theta.val (fun y => ((g k y : ℝ) : EReal))) :=
    fun k => isThetaPshPotential_rooftopEnvelope_of_continuous hn theta hbig (hcont k)
  have hple : ∀ k x,
      rooftopEnvelope theta.val (fun y => ((g k y : ℝ) : EReal)) x ≤ ((g k x : ℝ) : EReal) :=
    fun k => rooftopEnvelope_le_of_continuous (hcont k)
      (rooftopCompetitors_nonempty_of_isBigClass hn theta hbig (hcont k)) (hpotk k).1
  obtain ⟨v, hv⟩ := hne
  have hvinf : v ≤ iInfEnvelope theta g :=
    le_iInfEnvelope_of_mem_rooftopCompetitors hgf hv
  rw [rooftopEnvelope_eq_iInf_of_antitone hgf hanti (fun k => (hpotk k).1) hple ⟨v, hv⟩]
  exact ⟨thetaPlurisubharmonic_iInfEnvelope hanti (fun k => (hpotk k).1), hv.1.2.mono hvinf⟩

end

end SGPT.Foundations.Analysis.Pending.RooftopUscObstacleApproximation
