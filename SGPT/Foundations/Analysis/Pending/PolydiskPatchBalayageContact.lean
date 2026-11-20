import SGPT.Foundations.Analysis.Pending.PolydiskPatchBalayage

set_option autoImplicit false

/-!
# The order half of Xia's Lemma 2.4.3, and the lemma itself

`Pending.PolydiskPatchVanishing` proved the **measure** half of Xia's Lemma
2.4.3 (`xia-sgpt:page-0079`, equation (2.21)): a `θ`-PSH potential which
coincides with its own balayage on a small polydisk around every point of a set
`S` gives no non-pluripolar Monge--Ampère mass to `S`.  The contact identity
itself was left as a hypothesis.  This module proves it, which completes Lemma
2.4.3.

The argument is Xia's own, with the holomorphic ball replaced throughout by the
polydisk `c + rP` (the human accepted that route when closing I-0362, and
Proposition 1.2.9 is available for it in `Pending.ScaledPolydiskBalayage`).  Let
`w` be the largest `θ`-PSH potential below an obstacle `f`, and let `x` be a
point with `w x < f x`.  Choose a real `t` strictly between them.  *All* four
constraints of the proof are neighbourhood conditions at the chart point
`c = e(x)`, so one application of `exists_pos_image_closedUnitPolydisk_subset`
to their intersection produces the radius:

* `c + rP̄ ⊆ P.domain` — the polydisk is a legitimate balayage domain;
* `f > t` on the polydisk, by **lower semicontinuity of `f`** (this is where the
  hypothesis is used, and it is why Lemma 2.4.3 needs an lsc obstacle);
* the corrected representative of `w` is `< correctedReal c + δ` on the
  polydisk, by **upper semicontinuity of a PSH function**;
* the smooth local potential `ρ` of `θ` varies by less than `δ` on the polydisk,
  by **continuity of `ρ`** — this is the oscillation Xia absorbs by shrinking
  the ball.

With `δ = (t - w x)/2` the last three combine into `patchBalayage ≤ t < f` on
the polydisk, because `correctedReal c = w x + ρ c`.  The glued modification
`gluedPatchBalayage` is then a `θ`-PSH potential lying below `f` everywhere, so
maximality of `w` forces it below `w`; since the modification is *above* `w` on
the patch source, the two agree there, which is the contact identity.

`exists_eqOn_scaledPolydiskBalayage` is that statement.  Its maximality
hypothesis is stated abstractly and is discharged for the rooftop envelope by
`FirstPass.le_rooftopEnvelope`, so no restatement is introduced: the concrete
corollary `diagonalPotentialMeasure_rooftopEnvelope_lt_eq_zero` is Xia's (2.21)
for `P_θ(f)`.

The remaining hypothesis of (2.21) is that `w` is *locally bounded* on the set
in question, in the patch form `IsBoundedPotentialOn w P.source`.  That is Xia's
Lemma 2.4.1, which holds away from `nK({θ})` and is not reproved here.
-/

open Set Filter TopologicalSpace
open scoped Topology ENNReal

noncomputable section

namespace SGPT.Foundations.Analysis.Pending.PolydiskPatchBalayageContact

open FirstPass FirstPass.MongeAmpere
open FirstPass.AnalyticGluingData
open FirstPass.GlobalPotentialPatches
open BedfordTaylor
open SGPT.Foundations.Analysis.Pending.BoundedGlobalProduct
open SGPT.Foundations.Analysis.Pending.PatchLocalBoundedMeasure
open SGPT.Foundations.Analysis.Pending.PolydiskPatchBalayage

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {theta : ClosedRealOneOneForm n M} {w f : M → EReal}

/-- **The contact identity of Xia's Lemma 2.4.3.**  If `w` is the largest
`θ`-PSH potential below the lower semicontinuous obstacle `f`, and `w x < f x`
at a point where `w` is bounded on a chart neighbourhood, then on a small
polydisk around `e(x)` the corrected local representative of `w` *is* its own
balayage. -/
theorem exists_eqOn_scaledPolydiskBalayage (hn : 0 < n)
    (hf : LowerSemicontinuous f)
    (hwf : ∀ y, w y ≤ f y)
    (hmax : ∀ v : M → EReal, IsThetaPshPotential theta.val v →
      (∀ y, v y ≤ f y) → v ≤ w)
    (hw : IsThetaPshPotential theta.val w)
    (P : Patch (fun _ : Fin n => theta) (fun _ => w)) (i₀ : Fin n)
    (hb : IsBoundedPotentialOn w P.source)
    {x : M} (hx : x ∈ P.source) (hlt : w x < f x) :
    ∃ r : ℝ, 0 < r ∧
      polydiskChart (P.chart.val x) r '' closedUnitPolydisk n ⊆
        (P.domain : Set (ComplexModel n)) ∧
      EqOn (correctedReal P i₀)
        (scaledPolydiskBalayage (P.chart.val x) r (correctedReal P i₀))
        (scaledPolydisk (P.chart.val x) r) := by
  classical
  set c : ComplexModel n := P.chart.val x with hc
  have hcD : c ∈ P.domain := hx.2
  have hsymmc : P.chart.val.symm c = x := P.chart.val.left_inv hx.1
  -- `w x` is a real number
  have hwx : w x = ((w x).toReal : EReal) :=
    (EReal.coe_toReal (hb.ne_top hx) (hb.ne_bot hx)).symm
  set a : ℝ := (w x).toReal with ha
  -- a real level strictly between `w x` and `f x`
  obtain ⟨t, hat, htf⟩ := EReal.lt_iff_exists_real_btwn.mp hlt
  have hat' : a < t := by
    rw [hwx] at hat; exact_mod_cast hat
  set δ : ℝ := (t - a) / 2 with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  -- the corrected representative at the centre
  have hu : IsLocallyBoundedPshOn P.domain (correctedReal P i₀) :=
    correctedReal_isLocallyBoundedPshOn_of_boundedOn (i := i₀) (P := P) hb
  have hcorr_c : correctedReal P i₀ c = a + P.potential i₀ c := by
    rw [correctedReal_eq_of_boundedOn (i := i₀) hb hcD, hsymmc]
  set Mb : ℝ := correctedReal P i₀ c + δ with hMbdef
  /- ### the four neighbourhood conditions at `c` -/
  have hN1 : (P.domain : Set (ComplexModel n)) ∈ 𝓝 c := P.domain.isOpen.mem_nhds hcD
  -- upper semicontinuity of the corrected representative
  have hN2 : {z : ComplexModel n | correctedReal P i₀ z < Mb} ∈ 𝓝 c := by
    have husc : UpperSemicontinuousAt
        (fun z => ((correctedReal P i₀ z : ℝ) : EReal)) c :=
      (hu.1 c hcD).upperSemicontinuousAt
    have hlt' : ((correctedReal P i₀ c : ℝ) : EReal) < ((Mb : ℝ) : EReal) := by
      rw [EReal.coe_lt_coe_iff, hMbdef]; linarith
    filter_upwards [husc _ hlt'] with z hz
    exact_mod_cast hz
  -- continuity of the smooth local potential
  have hN3 : {z : ComplexModel n | P.potential i₀ c - δ < P.potential i₀ z} ∈ 𝓝 c := by
    have hcont : ContinuousOn (P.potential i₀) (P.domain : Set (ComplexModel n)) :=
      ((P.localPotential i₀).2.2.1).continuousOn
    have hat0 : ContinuousAt (P.potential i₀) c :=
      (hcont c hcD).continuousAt hN1
    exact hat0 (Ioi_mem_nhds (by linarith))
  -- lower semicontinuity of the obstacle, read in the chart
  have hN4 : {z : ComplexModel n | (t : EReal) < f (P.chart.val.symm z)} ∈ 𝓝 c := by
    have htar : P.chart.val.target ∈ 𝓝 c :=
      P.chart.val.open_target.mem_nhds (P.domain_le_target hcD)
    have hsymmcont : ContinuousAt P.chart.val.symm c :=
      (P.chart.val.continuousOn_symm c (P.domain_le_target hcD)).continuousAt htar
    have hfx : ∀ᶠ y in 𝓝 x, (t : EReal) < f y := hf x (t : EReal) htf
    have := hsymmcont.eventually (p := fun y => (t : EReal) < f y) (by rwa [hsymmc])
    exact this
  obtain ⟨N, hNsub, hNopen, hcN⟩ :=
    mem_nhds_iff.mp (Filter.inter_mem (Filter.inter_mem hN1 hN2)
      (Filter.inter_mem hN3 hN4))
  obtain ⟨r, hr, hrN⟩ :=
    exists_pos_image_closedUnitPolydisk_subset (Ω := ⟨N, hNopen⟩) hcN
  have hr0 : r ≠ 0 := ne_of_gt hr
  have hPΩ : polydiskChart c r '' closedUnitPolydisk n ⊆
      (P.domain : Set (ComplexModel n)) := fun z hz => (hNsub (hrN hz)).1.1
  refine ⟨r, hr, hPΩ, ?_⟩
  /- ### the modification is a competitor -/
  have hopenpoly : scaledPolydisk c r ⊆ polydiskChart c r '' closedUnitPolydisk n :=
    Set.image_mono unitPolydisk_subset_closedUnitPolydisk
  have hMb : ∀ z ∈ polydiskChart c r '' closedUnitPolydisk n,
      correctedReal P i₀ z ≤ Mb := fun z hz => le_of_lt (hNsub (hrN hz)).1.2
  have hg : IsThetaPshPotential theta.val (gluedPatchBalayage P i₀ c r) :=
    isThetaPshPotential_gluedPatchBalayage hn P i₀ hw hb hr0 hPΩ
  have hgf : ∀ y, gluedPatchBalayage P i₀ c r y ≤ f y := by
    intro y
    by_cases hyS : y ∈ (P.source : Set M)
    · rw [gluedPatchBalayage, gluedMax_eq_max hyS]
      refine max_le ?_ (hwf y)
      by_cases hyc : P.chart.val y ∈ scaledPolydisk c r
      · have hmem := hNsub (hrN (hopenpoly hyc))
        have hbound := patchBalayage_le hn hb hr0 hPΩ hMb hyS hyc
        have hlt2 : Mb - P.potential i₀ (P.chart.val y) < t := by
          have h3 := hmem.2.1
          simp only [mem_ofPred_eq] at h3
          rw [hMbdef, hcorr_c, hδ]
          linarith [h3]
        have hylt : (t : EReal) < f y := by
          have h4 := hmem.2.2
          simp only [mem_ofPred_eq] at h4
          rwa [P.chart.val.left_inv hyS.1] at h4
        refine le_of_lt ?_
        calc patchBalayage P i₀ c r y
            ≤ ((Mb - P.potential i₀ (P.chart.val y) : ℝ) : EReal) := hbound
          _ < (t : EReal) := by exact_mod_cast hlt2
          _ ≤ f y := hylt.le
      · rw [patchBalayage_eq_of_notMem hb hr0 hyS hyc]
        exact hwf y
    · rw [gluedPatchBalayage, gluedMax, if_neg hyS]
      exact hwf y
  have hgw : gluedPatchBalayage P i₀ c r ≤ w := hmax _ hg hgf
  /- ### contact on the patch source -/
  have hcontact : ∀ y ∈ (P.source : Set M), patchBalayage P i₀ c r y = w y := by
    intro y hy
    refine le_antisymm ?_ (le_patchBalayage hn hb hr0 hPΩ hy)
    have := hgw y
    rw [gluedPatchBalayage, gluedMax_eq_max hy] at this
    exact le_trans (le_max_left _ _) this
  /- ### reading the contact identity back in the chart -/
  intro z hz
  have hzD : z ∈ P.domain := hPΩ (hopenpoly hz)
  set y : M := P.chart.val.symm z with hy
  have hyS : y ∈ (P.source : Set M) := P.map_target hzD
  have hzy : P.chart.val y = z := P.chart.val.right_inv (P.domain_le_target hzD)
  have h1 : ((scaledPolydiskBalayage c r (correctedReal P i₀) z : ℝ) : EReal) -
      (P.potential i₀ z : EReal) = w y := by
    have := hcontact y hyS
    rwa [patchBalayage_of_mem_source hyS, hzy] at this
  have h2 : ((correctedReal P i₀ z : ℝ) : EReal) - (P.potential i₀ z : EReal) = w y := by
    have := coe_correctedReal_sub (i₀ := i₀) hb hyS
    rwa [hzy] at this
  have h3 : ((scaledPolydiskBalayage c r (correctedReal P i₀) z -
      P.potential i₀ z : ℝ) : EReal) =
      ((correctedReal P i₀ z - P.potential i₀ z : ℝ) : EReal) := by
    rw [EReal.coe_sub, EReal.coe_sub, h1, h2]
  have h4 : scaledPolydiskBalayage c r (correctedReal P i₀) z - P.potential i₀ z =
      correctedReal P i₀ z - P.potential i₀ z := by exact_mod_cast h3
  show correctedReal P i₀ z = scaledPolydiskBalayage c r (correctedReal P i₀) z
  linarith [h4]

end SGPT.Foundations.Analysis.Pending.PolydiskPatchBalayageContact

/-! ### Xia's Lemma 2.4.3 -/

namespace SGPT.Foundations.Analysis.Pending.PolydiskPatchBalayageContact

open FirstPass FirstPass.MongeAmpere
open FirstPass.GlobalPotentialPatches
open BedfordTaylor
open SGPT.Foundations.Analysis.Pending.BoundedGlobalProduct
open SGPT.Foundations.Analysis.Pending.PatchLocalBoundedMeasure
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Foundations.Analysis.Pending.PolydiskPatchVanishing

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]
  {theta : ClosedRealOneOneForm n M} {w f : M → EReal}

/-- **Xia, SGPT, Lemma 2.4.3, equation (2.21).**  The non-pluripolar
Monge--Ampère measure of the largest `θ`-PSH potential `w` below a lower
semicontinuous obstacle `f` gives no mass to any subset of `{w < f}` on which
`w` is locally bounded (in the patch sense — Xia's Lemma 2.4.1 supplies that
away from `nK({θ})`). -/
theorem diagonalPotentialMeasure_lt_eq_zero (hn : 0 < n)
    (hf : LowerSemicontinuous f)
    (hwf : ∀ y, w y ≤ f y)
    (hmax : ∀ v : M → EReal, IsThetaPshPotential theta.val v →
      (∀ y, v y ≤ f y) → v ≤ w)
    (hw : IsThetaPshPotential theta.val w) {S : Set M}
    (hS : ∀ x ∈ S, w x < f x)
    (hloc : ∀ x ∈ S, ∃ (P : Patch (fun _ : Fin n => theta) (fun _ => w))
      (_ : Fin n), x ∈ P.source ∧ IsBoundedPotentialOn w P.source) :
    diagonalPotentialMeasure theta w hw S = 0 := by
  refine diagonalPotentialMeasure_eq_zero_of_locally_eqOn_balayage hn hw ?_
  intro x hxS
  obtain ⟨P, i₀, hxP, hb⟩ := hloc x hxS
  obtain ⟨r, hr, hPΩ, heq⟩ :=
    exists_eqOn_scaledPolydiskBalayage hn hf hwf hmax hw P i₀ hb hxP (hS x hxS)
  exact ⟨P, i₀, hxP, hb, P.chart.val x, r, hr, hPΩ,
    mem_scaledPolydisk_center (ne_of_gt hr), heq⟩

/-- **Xia's (2.21) for the rooftop envelope itself.**  The maximality hypothesis
is discharged by `FirstPass.le_rooftopEnvelope`. -/
theorem diagonalPotentialMeasure_rooftopEnvelope_lt_eq_zero (hn : 0 < n)
    (hf : LowerSemicontinuous f)
    (hwf : ∀ y, rooftopEnvelope theta.val f y ≤ f y)
    (hw : IsThetaPshPotential theta.val (rooftopEnvelope theta.val f)) {S : Set M}
    (hS : ∀ x ∈ S, rooftopEnvelope theta.val f x < f x)
    (hloc : ∀ x ∈ S, ∃ (P : Patch (fun _ : Fin n => theta)
        (fun _ => rooftopEnvelope theta.val f)) (_ : Fin n),
      x ∈ P.source ∧
        IsBoundedPotentialOn (rooftopEnvelope theta.val f) P.source) :
    diagonalPotentialMeasure theta (rooftopEnvelope theta.val f) hw S = 0 :=
  diagonalPotentialMeasure_lt_eq_zero hn hf hwf
    (fun _ hv hvf => le_rooftopEnvelope hv (quasiEverywhere_of_forall hvf)) hw hS hloc

end SGPT.Foundations.Analysis.Pending.PolydiskPatchBalayageContact

end
