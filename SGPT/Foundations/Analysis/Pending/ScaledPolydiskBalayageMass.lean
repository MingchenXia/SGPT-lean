import SGPT.Foundations.Analysis.Pending.ScaledPolydiskBalayage
import SGPT.Foundations.Analysis.Pending.PolydiskPshMollifierData
import SGPT.Foundations.Analysis.Pending.BedfordTaylorHolomorphic

set_option autoImplicit false

/-!
# The homogeneous Monge--Ampere equation for the balayage on an arbitrary polydisk

`Pending.ScaledPolydiskBalayage` transports Xia's Proposition 1.2.9 to the
polydisk `c + r P` of arbitrary centre and radius: the transported balayage is
plurisubharmonic on the same open set as its datum.  This file transports the
*measure* half, which is what Lemma 2.4.3 actually uses: the Bedford--Taylor
measure of the transported balayage vanishes on the open polydisk.

The transport is the holomorphic covariance of Bedford--Taylor limits
(`Pending.BedfordTaylorHolomorphic.IsBTLimit.comp_biholomorphic`) applied to the
affine biholomorphism `T w = c + r w` of `Pending.ScaledPolydiskBalayage`.  No
new analytic content: everything is pulled back to
`Pending.PolydiskPshMollifierData.eq_zero_of_isBTLimit_perronEnvelope_of_isLocallyBoundedPshOn`
on the unit polydisk.

Two order facts about the balayage are proved here as well, because Lemma 2.4.3
uses them at exactly this place and they were only available for a continuous
(`IsPerronData`) datum: the balayage dominates its datum, and it inherits any
upper bound the datum has on the closed polydisk.  Both are read off the
competitor definition, once the competitor family is known to be nonempty --
which it is, since a locally bounded datum is bounded below on the closed
polydisk and constants are competitors.  These two are stated on the UNIT
polydisk, where Lemma 2.4.3 applies them after the affine transport; the scaled
statements are not needed and are not recorded.

The second of them, `perronEnvelope_le_of_isLocallyBoundedPshOn`, is what makes
the domination principle (Xia Prop 1.2.10) unnecessary at the one place Lemma
2.4.3 invokes it: Xia applies 1.2.10 only against a CONSTANT, and the balayage
of this workspace IS the Perron envelope, which inherits the upper bounds of its
datum outright.  See I-0384.
-/

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.BedfordTaylor

open FirstPass FirstPass.MongeAmpere

variable {n : ℕ}

/-! ### The competitor family of a locally bounded plurisubharmonic datum -/

/-- A locally bounded plurisubharmonic datum near `P̄` is its own competitor:
plurisubharmonicity gives the interior condition and upper semicontinuity gives
the boundary condition. -/
theorem isPerronCompetitor_self_of_isLocallyBoundedPshOn {Ω : Opens (ComplexModel n)}
    {u : ComplexModel n → ℝ} (hu : IsLocallyBoundedPshOn Ω u)
    (hPΩ : closedUnitPolydisk n ⊆ (Ω : Set (ComplexModel n))) :
    IsPerronCompetitor u u := by
  refine ⟨hu.1.mono (fun z hz => hPΩ (unitPolydisk_subset_closedUnitPolydisk hz)),
    fun ζ hζ ε hε => ?_⟩
  have hζΩ : ζ ∈ (Ω : Set (ComplexModel n)) := hPΩ hζ.1
  have husc := (hu.1 ζ hζΩ).upperSemicontinuousAt
  have hlt : ((u ζ : ℝ) : EReal) < ((u ζ + ε : ℝ) : EReal) := by
    exact_mod_cast by linarith
  have := husc _ hlt
  exact (this.filter_mono nhdsWithin_le_nhds).mono fun z hz => by
    have hz' : ((u z : ℝ) : EReal) < ((u ζ + ε : ℝ) : EReal) := hz
    exact_mod_cast hz'.le

/-- The competitor family of such a datum is nonempty: a constant below the
datum on `P̄` is a competitor. -/
theorem nonempty_perronCompetitors_of_isLocallyBoundedPshOn {Ω : Opens (ComplexModel n)}
    {u : ComplexModel n → ℝ} (hu : IsLocallyBoundedPshOn Ω u)
    (hPΩ : closedUnitPolydisk n ⊆ (Ω : Set (ComplexModel n))) :
    Nonempty {w : ComplexModel n → ℝ // IsPerronCompetitor u w} :=
  ⟨⟨u, isPerronCompetitor_self_of_isLocallyBoundedPshOn hu hPΩ⟩⟩

/-- **The balayage dominates its datum.**  The unit-polydisk case, for a locally
bounded plurisubharmonic datum. -/
theorem le_perronEnvelope_of_isLocallyBoundedPshOn (hn : 0 < n)
    {Ω : Opens (ComplexModel n)}
    {u : ComplexModel n → ℝ} (hu : IsLocallyBoundedPshOn Ω u)
    (hPΩ : closedUnitPolydisk n ⊆ (Ω : Set (ComplexModel n)))
    {z : ComplexModel n} (hz : z ∈ unitPolydisk n) : u z ≤ perronEnvelope u z := by
  obtain ⟨C, -, hC⟩ :=
    hu.exists_compact_abs_bound (isCompact_closedUnitPolydisk (n := n)) hPΩ
  refine le_ciSup_of_le ⟨C, ?_⟩
    ⟨u, isPerronCompetitor_self_of_isLocallyBoundedPshOn hu hPΩ⟩ le_rfl
  rintro y ⟨w, rfl⟩
  exact w.2.le_of_forall_le (fun x hx => (le_abs_self _).trans (hC x hx)) hz ⟨0, hn⟩

/-- **The balayage inherits an upper bound of its datum on `P̄`.**  Every
competitor does, by the one-variable maximum principle, and the family is
nonempty. -/
theorem perronEnvelope_le_of_isLocallyBoundedPshOn (hn : 0 < n)
    {Ω : Opens (ComplexModel n)}
    {u : ComplexModel n → ℝ} (hu : IsLocallyBoundedPshOn Ω u)
    (hPΩ : closedUnitPolydisk n ⊆ (Ω : Set (ComplexModel n)))
    {Mb : ℝ} (hMb : ∀ x ∈ closedUnitPolydisk n, u x ≤ Mb)
    {z : ComplexModel n} (hz : z ∈ unitPolydisk n) : perronEnvelope u z ≤ Mb := by
  have := nonempty_perronCompetitors_of_isLocallyBoundedPshOn hu hPΩ
  exact ciSup_le fun w => w.2.le_of_forall_le hMb hz ⟨0, hn⟩


/-! ### The measure half of the transport -/

/-- **The polydisk of radius `r` centred at `c` as an open set.**  It is the
preimage of the unit polydisk under the inverse chart, so openness is automatic
and needs no `r ≠ 0`. -/
def scaledPolydiskOpens (c : ComplexModel n) (r : ℝ) : Opens (ComplexModel n) :=
  Opens.comap ⟨polydiskChartInv c r, continuous_polydiskChartInv c r⟩
    (unitPolydiskOpens n)

theorem coe_scaledPolydiskOpens {c : ComplexModel n} {r : ℝ} (hr : r ≠ 0) :
    (scaledPolydiskOpens c r : Set (ComplexModel n)) = scaledPolydisk c r := by
  ext z
  exact (mem_scaledPolydisk_iff hr).symm

/-- The affine parametrization is a biholomorphism of the scaled polydisk onto
the unit polydisk. -/
theorem isBiholomorphicPair_scaledPolydisk {c : ComplexModel n} {r : ℝ}
    (hr : r ≠ 0) :
    IsBiholomorphicPair (scaledPolydiskOpens c r) (unitPolydiskOpens n)
      (polydiskChartInv c r) (polydiskChart c r) where
  holo := by unfold polydiskChartInv; fun_prop
  holo_inv := by unfold polydiskChart; fun_prop
  mapsTo := fun _ hz => hz
  mapsTo_inv := fun w hw => by
    show polydiskChartInv c r (polydiskChart c r w) ∈ unitPolydisk n
    rwa [polydiskChartInv_polydiskChart hr]
  left_inv := fun z _ => polydiskChart_polydiskChartInv hr z
  right_inv := fun w _ => polydiskChartInv_polydiskChart hr w

/-- **The measure half of Xia's Proposition 1.2.9 on an arbitrary polydisk.**
The Bedford--Taylor measure of the transported balayage vanishes on the open
polydisk `c + r P`: there the balayage solves the homogeneous Monge--Ampere
equation.  This is the half Lemma 2.4.3 uses.

Pure affine transport of
`Pending.PolydiskPshMollifierData.eq_zero_of_isBTLimit_perronEnvelope_of_isLocallyBoundedPshOn`
along `Pending.BedfordTaylor.IsBTLimit.comp_biholomorphic`; no new analytic
content.  The transported measure is computed on the unit polydisk, where it
vanishes, and uniqueness of Bedford--Taylor limits brings the conclusion back. -/
theorem eq_zero_of_isBTLimit_scaledPolydiskBalayage (hn : 0 < n)
    {Ω : Opens (ComplexModel n)} {u : ComplexModel n → ℝ}
    (hu : IsLocallyBoundedPshOn Ω u) {c : ComplexModel n} {r : ℝ} (hr : r ≠ 0)
    (hPΩ : polydiskChart c r '' closedUnitPolydisk n ⊆ (Ω : Set (ComplexModel n)))
    {μ : Measure (ComplexModel n)}
    (hμ : IsBTLimit (scaledPolydiskOpens c r)
      (fun _ => scaledPolydiskBalayage c r u) μ) :
    μ = 0 := by
  have hu' := isLocallyBoundedPshOn_comp_polydiskChart hu c r
  have hPΩ' : closedUnitPolydisk n ⊆
      ((Opens.comap ⟨polydiskChart c r, continuous_polydiskChart c r⟩ Ω :
        Opens (ComplexModel n)) : Set (ComplexModel n)) :=
    fun w hw => hPΩ ⟨w, hw, rfl⟩
  obtain ⟨ν, hν⟩ := exists_isBTLimit_of_isLocallyBoundedPshOn
    (u := fun _ : Fin n => perronEnvelope fun w => u (polydiskChart c r w))
    (fun _ => isLocallyBoundedPshOn_perronEnvelope_of_isLocallyBoundedPshOn hn hu' hPΩ')
  have hν0 : ν = 0 :=
    eq_zero_of_isBTLimit_perronEnvelope_of_isLocallyBoundedPshOn hn hu' hPΩ' hν
  have htrans := hν.comp_biholomorphic (isBiholomorphicPair_scaledPolydisk (c := c) hr)
  rw [hν0] at htrans
  simp only [Measure.restrict_zero, Measure.map_zero] at htrans
  refine hμ.unique (htrans.congr fun _ z hz => ?_)
  have hz' : z ∈ scaledPolydisk c r := by
    rwa [← coe_scaledPolydiskOpens hr]
  exact (scaledPolydiskBalayage_of_mem hr u hz').symm

end SGPT.Foundations.Analysis.Pending.BedfordTaylor

end
