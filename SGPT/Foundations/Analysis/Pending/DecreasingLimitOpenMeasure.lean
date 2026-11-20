import SGPT.Foundations.Analysis.Pending.IncreasingLimitOpenMeasure
import SGPT.Foundations.Analysis.Pending.DecreasingTruncationLimit
import SGPT.Foundations.Analysis.Pending.GlobalNonPluripolarKahler

set_option autoImplicit false

/-!
# The semicontinuity theorem along decreasing sequences, on the manifold

Let `u_j` be a pointwise decreasing sequence of `theta`-PSH potentials on a compact
complex manifold with pointwise limit `v`, itself a `theta`-PSH potential.  Then:

* on every open set `G`, `theta^n_v(G) ≤ liminf_j theta^n_{u_j}(G)`
  (`diagonalPotentialMeasure_isOpen_le_liminf_of_antitone`);
* if moreover the total masses agree, `theta^n_{u_j}(X) = theta^n_v(X)`, then on
  every closed set `F`, `limsup_j theta^n_{u_j}(F) ≤ theta^n_v(F)`
  (`diagonalPotentialMeasure_limsup_le_of_antitone`) -- the portmanteau form of
  the weak convergence `theta^n_{u_j} ⇀ theta^n_v`.

This is Xia's Theorem 2.4.2 (`xia-sgpt:page-0074`, from DDNL25, Theorem 2.6) for
a decreasing sequence in the diagonal case with `chi_k = chi = 1_G`, and the
decreasing counterpart of `Pending.IncreasingLimitOpenMeasure`.  No boundedness,
no minimal singularities and no Kähler background are needed for the first
statement: it is local, and the local input is
`DecreasingTruncationLimit.mixedTruncationLimitMeasure_le_liminf_of_antitone`,
transported through a chart with a smooth local potential exactly as in
`IncreasingLimitMass.exists_nhds_diagonalPotentialMeasure_le_liminf`, then
globalized by `IncreasingLimitOpenMeasure.measure_isOpen_le_liminf_of_local`.
The second statement is pure measure theory (`limsup_measure_le_of_isClosed`)
given finiteness of the limit measure, which the Kähler background supplies.

In the source the equality of total masses is what the monotonicity theorem
gives for potentials of the same singularity type (Theorem 2.4.3); the
application to Xia's Corollary 2.4.2 is in `Pending.DecreasingContactMassLimit`.
-/

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace SGPT.Foundations.Analysis.Pending.DecreasingLimitOpenMeasure

open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Foundations.Analysis.Pending.IncreasingLimitMass
open SGPT.Foundations.Analysis.Pending.DecreasingTruncationLimit

noncomputable section

/-! ### Portmanteau on closed sets -/

/-- **Closed sets from open sets, with equal total masses.**  If a finite measure
`mu` is below the lower limit of `nu j` on every open set, and every `nu j` has
the total mass of `mu`, then the upper limit of `nu j` on every closed set is at
most `mu`.  (The probability-measure case is Mathlib's
`limsup_measure_closed_le_iff_liminf_measure_open_ge`.) -/
theorem limsup_measure_le_of_isClosed {X : Type*} [MeasurableSpace X]
    [TopologicalSpace X] [OpensMeasurableSpace X] {mu : Measure X} {nu : ℕ → Measure X}
    [IsFiniteMeasure mu] (hmass : ∀ j, nu j univ = mu univ)
    (hopen : ∀ G : Set X, IsOpen G → mu G ≤ liminf (fun j => nu j G) atTop)
    {F : Set X} (hF : IsClosed F) :
    limsup (fun j => nu j F) atTop ≤ mu F := by
  have hc : mu univ ≠ ⊤ := measure_ne_top mu univ
  have hFm : MeasurableSet F := hF.measurableSet
  have hnuF : ∀ j, nu j F = mu univ - nu j Fᶜ := by
    intro j
    have hfin : nu j Fᶜ ≠ ⊤ :=
      ne_top_of_le_ne_top (by rw [hmass j]; exact hc) (measure_mono (subset_univ _))
    rw [← hmass j, ← measure_compl hFm.compl hfin, compl_compl]
  have hmuF : mu F = mu univ - mu Fᶜ := by
    rw [← measure_compl hFm.compl (measure_ne_top mu _), compl_compl]
  simp_rw [hnuF]
  rw [hmuF]
  have key := Antitone.map_liminf_of_continuousAt (F := atTop)
    (f := fun x : ℝ≥0∞ => mu univ - x) (fun _ _ h => tsub_le_tsub_left h _)
    (fun j => nu j Fᶜ) (ENNReal.continuous_sub_left hc).continuousAt
  rw [show (limsup (fun j => mu univ - nu j Fᶜ) atTop) =
      limsup ((fun x : ℝ≥0∞ => mu univ - x) ∘ fun j => nu j Fᶜ) atTop from rfl, ← key]
  exact tsub_le_tsub_left (hopen Fᶜ hF.isOpen_compl) _

section Manifold

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

open FirstPass.PositiveClasses FirstPass.GlobalPotentialPatches
open GlobalNonPluripolar MixedNonPluripolar

/-- Near every point, the diagonal measure of the pointwise limit of a decreasing
sequence of potentials is, on open sets, below the lower limit of the measures of
the sequence. -/
theorem exists_nhds_diagonalPotentialMeasure_le_liminf_of_antitone
    {theta : ClosedRealOneOneForm n M} (u : ℕ → M → EReal)
    (hu : ∀ j, IsThetaPshPotential theta.val (u j)) (hanti : Antitone u)
    {v : M → EReal} (hv : IsThetaPshPotential theta.val v)
    (hlim : ∀ x, Tendsto (fun j => u j x) atTop (𝓝 (v x))) (x : M) :
    ∃ O : Set M, IsOpen O ∧ x ∈ O ∧ ∀ G : Set M, IsOpen G → G ⊆ O →
      diagonalPotentialMeasure theta v hv G ≤
        liminf (fun j => diagonalPotentialMeasure theta (u j) (hu j) G) atTop := by
  let e : ComplexChart n M := complexChartAt x
  have hx : x ∈ e.val.source := mem_complexChartAt_source x
  obtain ⟨W, ρ, hzW, hρ⟩ :=
    hv.1.hasSmoothLocalPotentials e (e.val x) (e.val.map_source hx)
  let PV := diagonalPatch hv e hρ
  refine ⟨PV.source, PV.source.isOpen, ⟨hx, hzW⟩, fun G hG hGO => ?_⟩
  -- Global measures on `G` are local measures on the chart image.
  have hglobal : ∀ {w : M → EReal} (hw : IsThetaPshPotential theta.val w),
      diagonalPotentialMeasure theta w hw G =
        mixedTruncationLimitMeasure (diagonalPatch hw e hρ).domain
          (diagonalPatch hw e hρ).corrected (diagonalPatch hw e hρ).plurisubharmonic
          (e.val '' G) := by
    intro w hw
    have hGs : G ∩ ((diagonalPatch hw e hρ).source : Set M) = G :=
      inter_eq_left.mpr hGO
    calc diagonalPotentialMeasure theta w hw G
        = (diagonalPotentialMeasure theta w hw).restrict
            ((diagonalPatch hw e hρ).source : Set M) G := by
          rw [Measure.restrict_apply' (diagonalPatch hw e hρ).source.isOpen.measurableSet,
            hGs]
      _ = patchMeasure (diagonalPatch hw e hρ) G := by
          rw [diagonalPotentialMeasure, globalMixedMeasure_restrict_patch]
      _ = _ := by
          rw [patchMeasure, Patch.pushMeasure_apply_image, hGs]
          rfl
  rw [hglobal hv]
  simp_rw [hglobal (hu _)]
  have hpsh : ∀ {w : M → EReal}, IsThetaPshPotential theta.val w →
      PlurisubharmonicOn (fun y => chartFunction w e y + (ρ y : EReal)) W := fun {w} hw =>
    chartCorrectedFamily_plurisubharmonicOn (F := {w})
      (fun _ h => by rw [mem_singleton_iff.mp h]; exact hw) e hρ _ ⟨w, mem_singleton _, rfl⟩
  have hlimW : ∀ y ∈ PV.domain, Tendsto
      (fun j => chartFunction (u j) e y + (ρ y : EReal)) atTop
        (𝓝 (chartFunction v e y + (ρ y : EReal))) := by
    intro y _
    have hc : ContinuousAt (fun p : EReal × EReal => p.1 + p.2)
        (chartFunction v e y, (ρ y : EReal)) :=
      EReal.continuousAt_add (Or.inr (EReal.coe_ne_bot _)) (Or.inr (EReal.coe_ne_top _))
    exact hc.tendsto.comp ((hlim (e.val.symm y)).prodMk_nhds tendsto_const_nhds)
  have hGimg : IsOpen (e.val '' G) :=
    e.val.isOpen_image_of_subset_source hG (hGO.trans PV.source_subset)
  have hGW : e.val '' G ⊆ W := by
    rintro _ ⟨y, hy, rfl⟩
    exact (hGO hy).2
  exact mixedTruncationLimitMeasure_le_liminf_of_antitone (Ω := PV.domain)
    (v := fun j y => chartFunction (u j) e y + (ρ y : EReal))
    (fun j => hpsh (hu j)) (fun y _ i j hij => add_le_add (hanti hij _) le_rfl)
    (hpsh hv) hlimW hGimg hGW

/-- **Xia, Theorem 2.4.2, decreasing diagonal case, on open sets.**  For a
pointwise decreasing sequence of `theta`-PSH potentials with pointwise limit `v`,
`theta^n_v(G) ≤ liminf_j theta^n_{u_j}(G)` on every open `G ⊆ X`. -/
theorem diagonalPotentialMeasure_isOpen_le_liminf_of_antitone
    {theta : ClosedRealOneOneForm n M} (u : ℕ → M → EReal)
    (hu : ∀ j, IsThetaPshPotential theta.val (u j)) (hanti : Antitone u)
    {v : M → EReal} (hv : IsThetaPshPotential theta.val v)
    (hlim : ∀ x, Tendsto (fun j => u j x) atTop (𝓝 (v x)))
    {G : Set M} (hG : IsOpen G) :
    diagonalPotentialMeasure theta v hv G ≤
      liminf (fun j => diagonalPotentialMeasure theta (u j) (hu j) G) atTop :=
  IncreasingLimitOpenMeasure.measure_isOpen_le_liminf_of_local _ _
    (exists_nhds_diagonalPotentialMeasure_le_liminf_of_antitone u hu hanti hv hlim) hG

/-- **Xia, Theorem 2.4.2, decreasing diagonal case, convergence part.**  If in
addition every `theta^n_{u_j}` has the total mass of `theta^n_v`, then on every
closed `F ⊆ X`, `limsup_j theta^n_{u_j}(F) ≤ theta^n_v(F)`. -/
theorem diagonalPotentialMeasure_limsup_le_of_antitone
    (omega : KahlerBackground n M)
    {theta : ClosedRealOneOneForm n M} (u : ℕ → M → EReal)
    (hu : ∀ j, IsThetaPshPotential theta.val (u j)) (hanti : Antitone u)
    {v : M → EReal} (hv : IsThetaPshPotential theta.val v)
    (hlim : ∀ x, Tendsto (fun j => u j x) atTop (𝓝 (v x)))
    (hmass : ∀ j, diagonalPotentialMass theta (u j) (hu j) = diagonalPotentialMass theta v hv)
    {F : Set M} (hF : IsClosed F) :
    limsup (fun j => diagonalPotentialMeasure theta (u j) (hu j) F) atTop ≤
      diagonalPotentialMeasure theta v hv F := by
  have : IsFiniteMeasure (diagonalPotentialMeasure theta v hv) :=
    globalMixedMeasure_isFiniteMeasure omega (fun _ => hv.1)
  exact limsup_measure_le_of_isClosed hmass
    (fun G hG => diagonalPotentialMeasure_isOpen_le_liminf_of_antitone u hu hanti hv hlim hG) hF

end Manifold

end

end SGPT.Foundations.Analysis.Pending.DecreasingLimitOpenMeasure
