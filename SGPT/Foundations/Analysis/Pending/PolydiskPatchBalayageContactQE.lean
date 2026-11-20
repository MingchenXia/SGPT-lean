import SGPT.Foundations.Analysis.Pending.PatchBoundedNeighborhood
import SGPT.Foundations.Analysis.Pending.NegligibleSetsPluripolarProof
import SGPT.Foundations.Analysis.Pending.RooftopMajorantFamilyConcentration

set_option autoImplicit false

/-!
# Xia's Lemma 2.4.3 with (2.20) only quasi-everywhere (step C6a of I-0510)

`Pending.PolydiskPatchBalayageContact` proves Xia's Lemma 2.4.3 / (2.21) for the largest
`θ`-PSH potential `w` below a lower semicontinuous obstacle `f`, assuming `w ≤ f` **everywhere**
and maximality among competitors below `f` everywhere.  For a merely lower semicontinuous
obstacle `P_θ(f) ≤ f` can fail on a pluripolar set, and the rooftop envelope is maximal among
competitors below `f` only **quasi-everywhere**.  The proof needs nothing more: the balayage
modification is `≤ f` on the polydisk by lower semicontinuity and equals `w` off it, so it is
`≤ f` quasi-everywhere, which is exactly what membership in the rooftop competitors asks.

* `exists_eqOn_scaledPolydiskBalayage_qe`, `diagonalPotentialMeasure_lt_eq_zero_qe`,
  `diagonalPotentialMeasure_lt_eq_zero_of_locallyBounded_qe`: the contact identity and (2.21)
  with (2.20) quasi-everywhere (verbatim proofs of the pointwise versions, `hwf` used only
  through `QuasiEverywhere.mono`).
* `rooftopEnvelope_le_quasiEverywhere_of_kahler`: Xia's (2.20) quasi-everywhere, unconditional
  on a compact connected Kähler manifold (inputs (a), (b) of I-0510 proved in
  `PluripolarOuterCapacity`, `NegligibleSetsPluripolarProof`).
* `diagonalPotentialMeasure_rooftopEnvelope_lt_eq_zero_of_lowerSemicontinuous_kahler`: **Xia's
  Theorem 2.4.4 for a bounded lower semicontinuous real obstacle**, with no (2.20) hypothesis —
  the member-level `hcontact` of
  `RooftopMajorantFamilyConcentration.diagonalPotentialMeasure_rooftopEnvelope_lt_add_eq_zero_of_majorants`
  for Xia's Step 2 (Tietze) family.
-/

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal

noncomputable section

namespace SGPT.Foundations.Analysis.Pending.PolydiskPatchBalayageContactQE

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

/-- **The contact identity of Xia's Lemma 2.4.3, with (2.20) quasi-everywhere.** -/
theorem exists_eqOn_scaledPolydiskBalayage_qe (hn : 0 < n)
    (hf : LowerSemicontinuous f)
    (hwf : QuasiEverywhere (n := n) (fun y => w y ≤ f y))
    (hmax : ∀ v : M → EReal, IsThetaPshPotential theta.val v →
      QuasiEverywhere (n := n) (fun y => v y ≤ f y) → v ≤ w)
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
  have hgf : QuasiEverywhere (n := n) (fun y => gluedPatchBalayage P i₀ c r y ≤ f y) := by
    refine hwf.mono fun y hwy => ?_
    by_cases hyS : y ∈ (P.source : Set M)
    · rw [gluedPatchBalayage, gluedMax_eq_max hyS]
      refine max_le ?_ hwy
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
        exact hwy
    · rw [gluedPatchBalayage, gluedMax, if_neg hyS]
      exact hwy
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


/-! ### Xia's (2.21) with (2.20) quasi-everywhere -/

section Measure

open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Foundations.Analysis.Pending.PolydiskPatchVanishing

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- **Xia's Lemma 2.4.3, (2.21), with (2.20) quasi-everywhere.** -/
theorem diagonalPotentialMeasure_lt_eq_zero_qe (hn : 0 < n)
    (hf : LowerSemicontinuous f)
    (hwf : QuasiEverywhere (n := n) (fun y => w y ≤ f y))
    (hmax : ∀ v : M → EReal, IsThetaPshPotential theta.val v →
      QuasiEverywhere (n := n) (fun y => v y ≤ f y) → v ≤ w)
    (hw : IsThetaPshPotential theta.val w) {S : Set M}
    (hS : ∀ x ∈ S, w x < f x)
    (hloc : ∀ x ∈ S, ∃ (P : Patch (fun _ : Fin n => theta) (fun _ => w))
      (_ : Fin n), x ∈ P.source ∧ IsBoundedPotentialOn w P.source) :
    diagonalPotentialMeasure theta w hw S = 0 := by
  refine diagonalPotentialMeasure_eq_zero_of_locally_eqOn_balayage hn hw ?_
  intro x hxS
  obtain ⟨P, i₀, hxP, hb⟩ := hloc x hxS
  obtain ⟨r, hr, hPΩ, heq⟩ :=
    exists_eqOn_scaledPolydiskBalayage_qe hn hf hwf hmax hw P i₀ hb hxP (hS x hxS)
  exact ⟨P, i₀, hxP, hb, P.chart.val x, r, hr, hPΩ,
    mem_scaledPolydisk_center (ne_of_gt hr), heq⟩

/-- The same with `hloc` in Xia's own form (local boundedness on neighbourhoods). -/
theorem diagonalPotentialMeasure_lt_eq_zero_of_locallyBounded_qe (hn : 0 < n)
    (hf : LowerSemicontinuous f)
    (hwf : QuasiEverywhere (n := n) (fun y => w y ≤ f y))
    (hmax : ∀ v : M → EReal, IsThetaPshPotential theta.val v →
      QuasiEverywhere (n := n) (fun y => v y ≤ f y) → v ≤ w)
    (hw : IsThetaPshPotential theta.val w) {S : Set M}
    (hS : ∀ x ∈ S, w x < f x)
    (hloc : ∀ x ∈ S, ∃ N ∈ 𝓝 x, IsBoundedPotentialOn w N) :
    diagonalPotentialMeasure theta w hw S = 0 := by
  refine diagonalPotentialMeasure_lt_eq_zero_qe hn hf hwf hmax hw hS ?_
  intro x hx
  obtain ⟨N, hN, hb⟩ := hloc x hx
  obtain ⟨P, hxP, hbP⟩ :=
    PatchBoundedNeighborhood.exists_patch_isBoundedPotentialOn hw.1 hN hb
  exact ⟨P, ⟨0, hn⟩, hxP, hbP⟩

end Measure

/-! ### Xia's (2.20) and Theorem 2.4.4 for bounded lsc obstacles on a Kähler manifold -/

section Kahler

open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Foundations.Analysis.Pending.ThetaCapacity
open FirstPass.PositiveClasses FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending.BigClassEnvelopeContact
open SGPT.Foundations.Analysis.Pending.BigClassNonKahlerLocusNull
open SGPT.Foundations.Analysis.Pending.RooftopUscEnvelopeConcentration
open SGPT.Foundations.Analysis.Pending.ContinuousObstacleEnvelopeContact

/-- **Xia, SGPT, (2.20) (`xia-sgpt:page-0078`), unconditional on a compact connected Kähler
manifold**: if `P_θ(f)` is a genuine `θ`-PSH potential then `P_θ(f) ≤ f` quasi-everywhere.
The two inputs of `RooftopObstacleQuasiEverywhere.rooftopEnvelope_le_quasiEverywhere` are
`PluripolarOuterCapacity.countablyStablePluripolar` and
`NegligibleSetsPluripolarProof.negligibleSetsPluripolar`. -/
theorem rooftopEnvelope_le_quasiEverywhere_of_kahler [CompactSpace M] [ConnectedSpace M]
    [Nonempty M] (omega : PositiveClasses.KahlerBackground n M)
    (theta : ClosedRealOneOneForm n M) {f : M → EReal}
    (hP : IsThetaPshPotential theta.val (rooftopEnvelope theta.val f)) :
    QuasiEverywhere (n := n) (fun x => rooftopEnvelope theta.val f x ≤ f x) :=
  RooftopObstacleQuasiEverywhere.rooftopEnvelope_le_quasiEverywhere
    (PluripolarOuterCapacity.countablyStablePluripolar omega)
    (NegligibleSetsPluripolarProof.negligibleSetsPluripolar omega theta) hP

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [Nonempty M]

/-- **Xia's Theorem 2.4.4 for a bounded lower semicontinuous real obstacle, with (2.20) only
quasi-everywhere.**  Same statement as
`RooftopMajorantFamilyConcentration.diagonalPotentialMeasure_rooftopEnvelope_lt_eq_zero_of_lowerSemicontinuous`
with its pointwise hypothesis `hule` weakened to quasi-everywhere. -/
theorem diagonalPotentialMeasure_rooftopEnvelope_lt_eq_zero_of_lowerSemicontinuous_qe
    (hn : 0 < n) (theta : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative theta))
    (hV : IsThetaPshPotential theta.val (thetaPshSupremum theta.val))
    {F : M → ℝ} (hF : LowerSemicontinuous F) {C : ℝ} (hCabs : ∀ x, |F x| ≤ C)
    (hu : IsThetaPshPotential theta.val
      (rooftopEnvelope theta.val fun x => ((F x : ℝ) : EReal)))
    (hule : QuasiEverywhere (n := n) (fun x =>
      rooftopEnvelope theta.val (fun y => ((F y : ℝ) : EReal)) x ≤ ((F x : ℝ) : EReal))) :
    diagonalPotentialMeasure theta
        (rooftopEnvelope theta.val fun x => ((F x : ℝ) : EReal)) hu
      {x : M | rooftopEnvelope theta.val (fun y => ((F y : ℝ) : EReal)) x <
        ((F x : ℝ) : EReal)} = 0 := by
  classical
  set u : M → EReal := rooftopEnvelope theta.val (fun x => ((F x : ℝ) : EReal)) with hudef
  set V : M → EReal := thetaPshSupremum theta.val with hVdef
  have hFle : ∀ x, F x ≤ C := fun x => (abs_le.mp (hCabs x)).2
  have hFge : ∀ x, (-C : ℝ) ≤ F x := fun x => (abs_le.mp (hCabs x)).1
  have huC : ∀ x, u x ≤ (C : EReal) := by
    refine le_coe_of_ae_in_charts_le (F := fun _ => C) hu.1 continuous_const ?_
    intro e
    filter_upwards [hule.ae_in_chart e volume] with z hz
    exact hz.trans (EReal.coe_le_coe_iff.mpr (hFle _))
  have hVu : ∀ x, V x + ((-C : ℝ) : EReal) ≤ u x := by
    have hcomp : ∀ x, V x + ((-C : ℝ) : EReal) ≤ ((F x : ℝ) : EReal) := by
      intro x
      have h0 : V x ≤ (0 : EReal) := by
        simpa [hVdef] using thetaPshSupremum_le_zero theta.val x
      calc V x + ((-C : ℝ) : EReal) ≤ 0 + ((-C : ℝ) : EReal) :=
            add_le_add h0 (le_refl _)
        _ = ((-C : ℝ) : EReal) := zero_add _
        _ ≤ ((F x : ℝ) : EReal) := EReal.coe_le_coe_iff.mpr (hFge x)
    exact le_rooftopEnvelope (hV.add_const _) (quasiEverywhere_of_forall hcomp)
  have hloc : ∀ x, x ∉ nonKahlerLocus (RealBottChern.ofRepresentative theta) →
      ∃ N ∈ 𝓝 x, IsBoundedPotentialOn u N := by
    intro x hx
    obtain ⟨N, hN, hb⟩ :=
      exists_isBoundedPotentialOn_thetaPshSupremum_offNonKahlerLocus hn theta hbig hV hx
    exact ⟨N, hN, isBoundedPotentialOn_of_le_add_const hb hVu huC⟩
  have hFlsc : LowerSemicontinuous (fun x => ((F x : ℝ) : EReal)) := by
    intro x r hr
    rcases EReal.lt_iff_exists_real_btwn.mp hr with ⟨q, hq1, hq2⟩
    have hq2' : q < F x := by
      simpa only [EReal.coe_lt_coe_iff] using hq2
    filter_upwards [hF x q hq2'] with y hy
    exact hq1.trans (EReal.coe_lt_coe_iff.mpr hy)
  have hgood : diagonalPotentialMeasure theta u hu
      ({x : M | u x < ((F x : ℝ) : EReal)} \
        nonKahlerLocus (RealBottChern.ofRepresentative theta)) = 0 :=
    diagonalPotentialMeasure_lt_eq_zero_of_locallyBounded_qe
      (f := fun x => ((F x : ℝ) : EReal)) hn hFlsc hule
      (fun v hv hvF => le_rooftopEnvelope hv hvF) hu
      (fun _ hx => hx.1) (fun x hx => hloc x hx.2)
  have hbad : diagonalPotentialMeasure theta u hu
      (nonKahlerLocus (RealBottChern.ofRepresentative theta)) = 0 :=
    diagonalPotentialMeasure_nonKahlerLocus_eq_zero hn theta hbig hu
  refine nonpos_iff_eq_zero.mp ?_
  calc diagonalPotentialMeasure theta u hu {x : M | u x < ((F x : ℝ) : EReal)}
      ≤ diagonalPotentialMeasure theta u hu
          (({x : M | u x < ((F x : ℝ) : EReal)} \
            nonKahlerLocus (RealBottChern.ofRepresentative theta)) ∪
            nonKahlerLocus (RealBottChern.ofRepresentative theta)) := by
        refine measure_mono fun y hy => ?_
        by_cases hyn : y ∈ nonKahlerLocus (RealBottChern.ofRepresentative theta)
        · exact Or.inr hyn
        · exact Or.inl ⟨hy, hyn⟩
    _ ≤ _ := measure_union_le _ _
    _ = 0 := by rw [hgood, hbad, add_zero]

/-- **Xia's Theorem 2.4.4 for a bounded lower semicontinuous real obstacle on a compact
connected Kähler manifold, with no (2.20) hypothesis.** -/
theorem diagonalPotentialMeasure_rooftopEnvelope_lt_eq_zero_of_lowerSemicontinuous_kahler
    [ConnectedSpace M] (hn : 0 < n) (omega : PositiveClasses.KahlerBackground n M)
    (theta : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative theta))
    (hV : IsThetaPshPotential theta.val (thetaPshSupremum theta.val))
    {F : M → ℝ} (hF : LowerSemicontinuous F) {C : ℝ} (hCabs : ∀ x, |F x| ≤ C)
    (hu : IsThetaPshPotential theta.val
      (rooftopEnvelope theta.val fun x => ((F x : ℝ) : EReal))) :
    diagonalPotentialMeasure theta
        (rooftopEnvelope theta.val fun x => ((F x : ℝ) : EReal)) hu
      {x : M | rooftopEnvelope theta.val (fun y => ((F y : ℝ) : EReal)) x <
        ((F x : ℝ) : EReal)} = 0 :=
  diagonalPotentialMeasure_rooftopEnvelope_lt_eq_zero_of_lowerSemicontinuous_qe hn theta hbig
    hV hF hCabs hu (rooftopEnvelope_le_quasiEverywhere_of_kahler omega theta hu)

end Kahler

end SGPT.Foundations.Analysis.Pending.PolydiskPatchBalayageContactQE

end
