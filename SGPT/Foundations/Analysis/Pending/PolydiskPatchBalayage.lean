import SGPT.Foundations.Analysis.Pending.PolydiskScaledBalayageOrder
import SGPT.Foundations.Analysis.Pending.PolydiskPatchVanishing
import SGPT.Foundations.Analysis.Pending.ThetaPshCollarGluing
import SGPT.Foundations.Analysis.Pending.HolomorphicPullback
import SGPT.Foundations.Analysis.FirstPass.LocalPotentialPullback
import SGPT.Foundations.Analysis.FirstPass.FormPullbackFunctorial
import SGPT.Foundations.Analysis.FirstPass.RooftopEnvelope

set_option autoImplicit false

/-!
# The local balayage of a `θ`-PSH potential on a polydisk inside a chart

Xia's Lemma 2.4.3 (`xia-sgpt:page-0079`) modifies `P_θ(f)` on a small
holomorphic ball `B` by its balayage and glues the result back.  This module
performs that modification for the polydisk `c + rP` sitting inside the domain
of a `Patch`, which is the ball Proposition 1.2.9 is available for in this
workspace (`Pending.PolydiskBalayagePshDatum`, affine-transported in
`Pending.ScaledPolydiskBalayage`).

`patchBalayage P i₀ c r` is the manifold function whose chart representative is
the balayage of the corrected local representative of `w`, with the smooth local
potential subtracted again; outside the patch source it is set to `0`, which is
invisible to every statement here (they all live on `P.source`, and the gluing
below only reads `patchBalayage` there).  Its `θ`-PSH-ness on `P.source` is
proved through an *arbitrary* chart, in the manner of
`Pending.QuasiEquisingularBergmanBranch.bergmanBranch_thetaPlurisubharmonicOn`:
the local potential is pulled back through the chart transition, and the
balayage — plurisubharmonic on the whole of `P.domain` — through the same
holomorphic coordinate map.

Three order facts follow, and they are exactly the three Xia uses:

* `le_patchBalayage` — the modification is above `w` (balayage dominates its
  datum);
* `patchBalayage_eq_of_notMem` — off the polydisk it *is* `w`, so the glued
  function has the `hcollar` shape of
  `Pending.QuasiEquisingularCollarGluing.isThetaPshPotential_gluedMax`;
* `patchBalayage_le` — on the polydisk it inherits an upper bound of the
  corrected datum on the *closed* polydisk.  The correction `ρ` reappears in
  the conclusion, which is the precise form of Xia's "shrink the ball": the
  oscillation of `ρ` on `c + rP̄` is what the consumer has to absorb.

Finally `isThetaPshPotential_gluedPatchBalayage` performs the gluing; the
closure hypothesis is discharged by compactness of the closed polydisk inside
the chart, which is where `c + rP̄ ⊆ P.domain` is used a second time.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

noncomputable section

namespace SGPT.Foundations.Analysis.Pending.PolydiskPatchBalayage

open FirstPass FirstPass.MongeAmpere
open FirstPass.AnalyticGluingData
open FirstPass.GlobalPotentialPatches
open FirstPass.HolomorphicMaps
open FirstPass.LocalPotentialPullback
open BedfordTaylor
open SGPT.Foundations.Analysis.Pending.BoundedGlobalProduct
open SGPT.Foundations.Analysis.Pending.PatchLocalBoundedMeasure
open SGPT.Foundations.Analysis.Pending.QuasiEquisingularCollarGluing

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {theta : ClosedRealOneOneForm n M} {w : M → EReal}

/-- **The local balayage, read on the manifold.**  Inside the patch source it is
the balayage of the corrected representative with the correction removed;
outside it is `0`, a value no statement of this file reads. -/
def patchBalayage (P : Patch (fun _ : Fin n => theta) (fun _ => w)) (i₀ : Fin n)
    (c : ComplexModel n) (r : ℝ) : M → EReal := by
  classical
  exact fun x => if x ∈ P.source then
      ((scaledPolydiskBalayage c r (correctedReal P i₀) (P.chart.val x) : ℝ) : EReal) -
        (P.potential i₀ (P.chart.val x) : EReal)
    else 0

theorem patchBalayage_of_mem_source {P : Patch (fun _ : Fin n => theta) (fun _ => w)}
    {i₀ : Fin n} {c : ComplexModel n} {r : ℝ} {x : M} (hx : x ∈ P.source) :
    patchBalayage P i₀ c r x =
      ((scaledPolydiskBalayage c r (correctedReal P i₀) (P.chart.val x) : ℝ) : EReal) -
        (P.potential i₀ (P.chart.val x) : EReal) := by
  simp [patchBalayage, hx]

/-! ### `θ`-plurisubharmonicity on the patch source -/

/-- **The local balayage is `θ`-PSH on the whole patch source.**  Proved through
an arbitrary chart: the smooth local potential is pulled back along the chart
transition (`isSmoothLocalPotential_pullback`), and the balayage — which is
plurisubharmonic on all of `P.domain` by Proposition 1.2.9 — along the same
holomorphic coordinate map. -/
theorem thetaPlurisubharmonicOn_patchBalayage (hn : 0 < n)
    (P : Patch (fun _ : Fin n => theta) (fun _ => w)) (i₀ : Fin n)
    (hb : IsBoundedPotentialOn w P.source)
    {c : ComplexModel n} {r : ℝ} (hr : r ≠ 0)
    (hPΩ : polydiskChart c r '' closedUnitPolydisk n ⊆
      (P.domain : Set (ComplexModel n))) :
    ThetaPlurisubharmonicOn theta.val (patchBalayage P i₀ c r)
      (P.source : Set M) := by
  have hu : IsLocallyBoundedPshOn P.domain (correctedReal P i₀) :=
    correctedReal_isLocallyBoundedPshOn_of_boundedOn (i := i₀) (P := P) hb
  have hbal := plurisubharmonicOn_scaledPolydiskBalayage hn hu hr hPΩ
  intro e z hz hzsource
  have hid : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ (id : M → M) :=
    contMDiff_id
  set F : ComplexModel n → ComplexModel n :=
    coordinateMap (id : M → M) e P.chart with hF
  set W : Set (ComplexModel n) :=
    potentialDomain (id : M → M) e P.chart (P.domain : Set (ComplexModel n)) with hWdef
  set ρe : ComplexModel n → ℝ := P.potential i₀ ∘ F with hρe
  have hW : IsOpen W := potentialDomain_isOpen hid e P.chart P.domain.isOpen
  have hzW : z ∈ W := by
    constructor
    · exact ⟨hz, hzsource.1⟩
    · exact hzsource.2
  have hρpull : IsSmoothLocalPotential (SmoothRealForm.pullback hid theta.val) e W ρe :=
    isSmoothLocalPotential_pullback hid e (P.localPotential i₀)
  have hρ : IsSmoothLocalPotential theta.val e W ρe :=
    (SmoothRealForm.pullback_id_geometricallyEq theta.val).localPotential_iff e W ρe
      |>.mp hρpull
  refine ⟨W, ρe, hzW, hρ, ?_⟩
  have hdiff : DifferentiableOn ℂ F W :=
    ((coordinateMap_contDiffOn hid e P.chart).differentiableOn (by simp)).mono
      inter_subset_left
  intro y hy
  have hyD : F y ∈ (P.domain : Set (ComplexModel n)) := hy.2
  have hpull : PlurisubharmonicAt
      (fun v => ((scaledPolydiskBalayage c r (correctedReal P i₀) (F v) : ℝ) : EReal)) y :=
    HolomorphicPullback.plurisubharmonicAt_comp_holomorphic hW hdiff hy (hbal (F y) hyD)
  refine hpull.congr ?_
  filter_upwards [hW.mem_nhds hy] with v hv
  have hvsource : e.val.symm v ∈ P.source := ⟨hv.1.2, hv.2⟩
  change ((scaledPolydiskBalayage c r (correctedReal P i₀) (F v) : ℝ) : EReal) =
    patchBalayage P i₀ c r (e.val.symm v) + (ρe v : EReal)
  rw [patchBalayage_of_mem_source hvsource]
  change ((scaledPolydiskBalayage c r (correctedReal P i₀) (F v) : ℝ) : EReal) =
    (((scaledPolydiskBalayage c r (correctedReal P i₀) (F v) : ℝ) : EReal) -
      (P.potential i₀ (F v) : EReal)) + (P.potential i₀ (F v) : EReal)
  exact EReal.sub_add_cancel.symm

/-! ### The three order facts -/

theorem coe_correctedReal_sub {P : Patch (fun _ : Fin n => theta) (fun _ => w)}
    {i₀ : Fin n} (hb : IsBoundedPotentialOn w P.source) {x : M} (hx : x ∈ P.source) :
    ((correctedReal P i₀ (P.chart.val x) : ℝ) : EReal) -
      (P.potential i₀ (P.chart.val x) : EReal) = w x := by
  have hxd : P.chart.val x ∈ P.domain := hx.2
  have hsymm : P.chart.val.symm (P.chart.val x) = x :=
    P.chart.val.left_inv hx.1
  rw [correctedReal_eq_of_boundedOn (i := i₀) hb hxd, hsymm, EReal.coe_add,
    EReal.add_sub_cancel_right]
  exact EReal.coe_toReal (hb.ne_top hx) (hb.ne_bot hx)

/-- **Off the polydisk the modification is the potential itself.**  This is the
`hcollar` hypothesis of the gluing. -/
theorem patchBalayage_eq_of_notMem {P : Patch (fun _ : Fin n => theta) (fun _ => w)}
    {i₀ : Fin n} (hb : IsBoundedPotentialOn w P.source)
    {c : ComplexModel n} {r : ℝ} (hr : r ≠ 0) {x : M} (hx : x ∈ P.source)
    (hxc : P.chart.val x ∉ scaledPolydisk c r) :
    patchBalayage P i₀ c r x = w x := by
  rw [patchBalayage_of_mem_source hx,
    scaledPolydiskBalayage_eqOn_compl hr (correctedReal P i₀) hxc]
  exact coe_correctedReal_sub hb hx

/-- **The modification lies above the potential.** -/
theorem le_patchBalayage (hn : 0 < n)
    {P : Patch (fun _ : Fin n => theta) (fun _ => w)} {i₀ : Fin n}
    (hb : IsBoundedPotentialOn w P.source)
    {c : ComplexModel n} {r : ℝ} (hr : r ≠ 0)
    (hPΩ : polydiskChart c r '' closedUnitPolydisk n ⊆
      (P.domain : Set (ComplexModel n)))
    {x : M} (hx : x ∈ P.source) : w x ≤ patchBalayage P i₀ c r x := by
  have hu : IsLocallyBoundedPshOn P.domain (correctedReal P i₀) :=
    correctedReal_isLocallyBoundedPshOn_of_boundedOn (i := i₀) (P := P) hb
  by_cases hxc : P.chart.val x ∈ scaledPolydisk c r
  · have hle := le_scaledPolydiskBalayage hn hu hr hPΩ hxc
    rw [patchBalayage_of_mem_source hx, ← coe_correctedReal_sub (i₀ := i₀) hb hx]
    exact EReal.sub_le_sub (by exact_mod_cast hle) le_rfl
  · rw [patchBalayage_eq_of_notMem hb hr hx hxc]

/-- **On the polydisk the modification inherits an upper bound of the corrected
datum on the closed polydisk.**  The correction reappears in the bound; that is
Xia's "after shrinking `B`", where the oscillation of `ρ` is absorbed. -/
theorem patchBalayage_le (hn : 0 < n)
    {P : Patch (fun _ : Fin n => theta) (fun _ => w)} {i₀ : Fin n}
    (hb : IsBoundedPotentialOn w P.source)
    {c : ComplexModel n} {r : ℝ} (hr : r ≠ 0)
    (hPΩ : polydiskChart c r '' closedUnitPolydisk n ⊆
      (P.domain : Set (ComplexModel n)))
    {Mb : ℝ}
    (hMb : ∀ z ∈ polydiskChart c r '' closedUnitPolydisk n,
      correctedReal P i₀ z ≤ Mb)
    {x : M} (hx : x ∈ P.source) (hxc : P.chart.val x ∈ scaledPolydisk c r) :
    patchBalayage P i₀ c r x ≤ ((Mb - P.potential i₀ (P.chart.val x) : ℝ) : EReal) := by
  have hu : IsLocallyBoundedPshOn P.domain (correctedReal P i₀) :=
    correctedReal_isLocallyBoundedPshOn_of_boundedOn (i := i₀) (P := P) hb
  have hle := scaledPolydiskBalayage_le hn hu hr hPΩ hMb hxc
  rw [patchBalayage_of_mem_source hx, EReal.coe_sub]
  exact EReal.sub_le_sub (by exact_mod_cast hle) le_rfl

/-! ### The gluing -/

/-- The part of the patch source lying over the open polydisk. -/
def polydiskSource (P : Patch (fun _ : Fin n => theta) (fun _ => w))
    (c : ComplexModel n) (r : ℝ) : Set M :=
  (P.source : Set M) ∩ P.chart.val ⁻¹' scaledPolydisk c r

/-- The part of the patch source lying over the *closed* polydisk. -/
def closedPolydiskSource (P : Patch (fun _ : Fin n => theta) (fun _ => w))
    (c : ComplexModel n) (r : ℝ) : Set M :=
  P.chart.val.symm '' (polydiskChart c r '' closedUnitPolydisk n)

theorem closedPolydiskSource_subset_source
    {P : Patch (fun _ : Fin n => theta) (fun _ => w)} {c : ComplexModel n} {r : ℝ}
    (hPΩ : polydiskChart c r '' closedUnitPolydisk n ⊆
      (P.domain : Set (ComplexModel n))) :
    closedPolydiskSource P c r ⊆ (P.source : Set M) := by
  rintro _ ⟨z, hz, rfl⟩
  exact P.map_target (hPΩ hz)

theorem polydiskSource_subset_closed
    {P : Patch (fun _ : Fin n => theta) (fun _ => w)} {c : ComplexModel n} {r : ℝ} :
    polydiskSource P c r ⊆ closedPolydiskSource P c r := by
  rintro x ⟨hxs, hxc⟩
  obtain ⟨v, hv, hvx⟩ := hxc
  exact ⟨P.chart.val x, ⟨v, unitPolydisk_subset_closedUnitPolydisk hv, hvx⟩,
    P.chart.val.left_inv hxs.1⟩

theorem isCompact_closedPolydiskSource
    {P : Patch (fun _ : Fin n => theta) (fun _ => w)} {c : ComplexModel n} {r : ℝ}
    (hPΩ : polydiskChart c r '' closedUnitPolydisk n ⊆
      (P.domain : Set (ComplexModel n))) :
    IsCompact (closedPolydiskSource P c r) := by
  refine (isCompact_closedUnitPolydisk.image
    (continuous_polydiskChart c r)).image_of_continuousOn ?_
  exact P.chart.val.continuousOn_symm.mono
    fun z hz => P.domain_le_target (hPΩ hz)

/-- The closure hypothesis of the collar gluing, discharged by compactness of
the closed polydisk inside the chart. -/
theorem closure_polydiskSource_subset
    {P : Patch (fun _ : Fin n => theta) (fun _ => w)} {c : ComplexModel n} {r : ℝ}
    (hPΩ : polydiskChart c r '' closedUnitPolydisk n ⊆
      (P.domain : Set (ComplexModel n))) :
    closure (polydiskSource P c r) ⊆ (P.source : Set M) :=
  ((closure_minimal polydiskSource_subset_closed
    (isCompact_closedPolydiskSource hPΩ).isClosed).trans
      (closedPolydiskSource_subset_source hPΩ))

/-- **The modified potential.**  `gluedMax` of the local balayage against `w`
over the patch source. -/
def gluedPatchBalayage (P : Patch (fun _ : Fin n => theta) (fun _ => w))
    (i₀ : Fin n) (c : ComplexModel n) (r : ℝ) : M → EReal :=
  gluedMax (P.source : Set M) (patchBalayage P i₀ c r) w

/-- **The glued modification is a genuine `θ`-PSH potential on `M`.**  This is
the `φ` of Xia's proof of Lemma 2.4.3. -/
theorem isThetaPshPotential_gluedPatchBalayage (hn : 0 < n)
    (P : Patch (fun _ : Fin n => theta) (fun _ => w)) (i₀ : Fin n)
    (hw : IsThetaPshPotential theta.val w)
    (hb : IsBoundedPotentialOn w P.source)
    {c : ComplexModel n} {r : ℝ} (hr : r ≠ 0)
    (hPΩ : polydiskChart c r '' closedUnitPolydisk n ⊆
      (P.domain : Set (ComplexModel n))) :
    IsThetaPshPotential theta.val (gluedPatchBalayage P i₀ c r) :=
  isThetaPshPotential_gluedMax P.source.isOpen
    (closure_polydiskSource_subset hPΩ)
    (fun _ hx => le_of_eq
      (patchBalayage_eq_of_notMem hb hr hx.1 fun hc => hx.2 ⟨hx.1, hc⟩))
    (thetaPlurisubharmonicOn_patchBalayage hn P i₀ hb hr hPΩ) hw

end SGPT.Foundations.Analysis.Pending.PolydiskPatchBalayage

end
