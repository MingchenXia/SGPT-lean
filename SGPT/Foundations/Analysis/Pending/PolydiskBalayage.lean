import SGPT.Foundations.Analysis.Pending.PolydiskPshMollifierData

set_option autoImplicit false

/-!
# The balayage of a plurisubharmonic function on the unit polydisk

`Pending.PolydiskPshMollifierData` proves that the Perron--Bremermann envelope
`perronEnvelope u` of a locally bounded plurisubharmonic datum solves the
homogeneous Monge--Ampère equation **inside** the polydisk.  Xia's
Proposition 1.2.9 (following [BT82, Prop. 9.1]) asks for more: the function

  `û = perronEnvelope u` on `P`,  `û = u` off `P`

must be plurisubharmonic on the **whole** of the ambient domain.  That is the
statement proved here, `plurisubharmonicOn_polydiskBalayage`.

## The gluing, and why no new maximum principle is needed

Plurisubharmonicity of `û` is clear on the open polydisk and on the open
complement of the closed polydisk; the content is at a boundary point `ζ ∈ ∂P`,
where every neighbourhood contains interior points whose analytic discs cross
the boundary.  The device used here removes the difficulty instead of
confronting it.  For `ε > 0` put

  `û_ε = max (u, perronEnvelope u - ε)` on `P`,  `û_ε = u` off `P`.

For a datum that is **continuous** near `P̄` the envelope obeys
`limsup_{z→ζ, z∈P} perronEnvelope u z ≤ u ζ`
(`IsPerronData.eventually_perronEnvelope_le`), while `u z ≥ u ζ - ε/2` near `ζ`
by continuity.  Hence `perronEnvelope u - ε < u` on a *whole neighbourhood* of
`ζ`, so `û_ε = u` there: `û_ε` is plurisubharmonic at `ζ` for the trivial
reason that it coincides with `u` near `ζ`.  Since `u ≤ perronEnvelope u` on
`P`, the family `û_ε` increases to `û` as `ε ↓ 0`, and `û` is upper
semicontinuous, so `û` is its own upper-semicontinuous regularization and
`FirstPass.plurisubharmonicOn_uscRegularization_sSup` finishes the continuous
case.

A general locally bounded plurisubharmonic datum is then handled by the
decreasing `C²` approximation of `PolydiskPshMollifierData`: the balayage of
the limit is the pointwise infimum of the balayages, and a decreasing limit of
plurisubharmonic functions is plurisubharmonic.

Source: M. Xia, *Sheaves and geometry of pluripotential theory*, Prop. 1.2.9
and Lemma 2.4.3; E. Bedford and B. A. Taylor, *A new capacity for
plurisubharmonic functions*, Prop. 9.1.
-/

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ContDiff

namespace SGPT.Foundations.Analysis.Pending.BedfordTaylor

open FirstPass FirstPass.MongeAmpere

variable {n : ℕ}

/-! ### The glued function -/

open scoped Classical in
/-- **The balayage of `u` on the unit polydisk**: the Perron--Bremermann
envelope inside, the datum itself outside. -/
def polydiskBalayage (u : ComplexModel n → ℝ) : ComplexModel n → ℝ :=
  fun z ↦ if z ∈ unitPolydisk n then perronEnvelope u z else u z

open scoped Classical in
/-- The `ε`-shifted balayage, which coincides with `u` near `∂P`. -/
def shiftedPolydiskBalayage (u : ComplexModel n → ℝ) (ε : ℝ) :
    ComplexModel n → ℝ :=
  fun z ↦ if z ∈ unitPolydisk n then max (u z) (perronEnvelope u z - ε) else u z

theorem polydiskBalayage_of_mem {u : ComplexModel n → ℝ} {z : ComplexModel n}
    (hz : z ∈ unitPolydisk n) : polydiskBalayage u z = perronEnvelope u z :=
  if_pos hz

theorem polydiskBalayage_of_notMem {u : ComplexModel n → ℝ} {z : ComplexModel n}
    (hz : z ∉ unitPolydisk n) : polydiskBalayage u z = u z :=
  if_neg hz

theorem shiftedPolydiskBalayage_of_mem {u : ComplexModel n → ℝ} {ε : ℝ}
    {z : ComplexModel n} (hz : z ∈ unitPolydisk n) :
    shiftedPolydiskBalayage u ε z = max (u z) (perronEnvelope u z - ε) :=
  if_pos hz

theorem shiftedPolydiskBalayage_of_notMem {u : ComplexModel n → ℝ} {ε : ℝ}
    {z : ComplexModel n} (hz : z ∉ unitPolydisk n) :
    shiftedPolydiskBalayage u ε z = u z :=
  if_neg hz

/-- The datum lies below its balayage. -/
theorem le_polydiskBalayage {u : ComplexModel n → ℝ} (hu : IsPerronData u)
    (z : ComplexModel n) : u z ≤ polydiskBalayage u z := by
  by_cases hz : z ∈ unitPolydisk n
  · rw [polydiskBalayage_of_mem hz]; exact hu.self_le_perronEnvelope hz
  · rw [polydiskBalayage_of_notMem hz]

theorem shiftedPolydiskBalayage_le_polydiskBalayage {u : ComplexModel n → ℝ}
    (hu : IsPerronData u) {ε : ℝ} (hε : 0 ≤ ε) (z : ComplexModel n) :
    shiftedPolydiskBalayage u ε z ≤ polydiskBalayage u z := by
  by_cases hz : z ∈ unitPolydisk n
  · rw [shiftedPolydiskBalayage_of_mem hz, polydiskBalayage_of_mem hz]
    exact max_le (hu.self_le_perronEnvelope hz) (by linarith)
  · rw [shiftedPolydiskBalayage_of_notMem hz, polydiskBalayage_of_notMem hz]

theorem le_shiftedPolydiskBalayage {u : ComplexModel n → ℝ} {ε : ℝ}
    (z : ComplexModel n) : u z ≤ shiftedPolydiskBalayage u ε z := by
  by_cases hz : z ∈ unitPolydisk n
  · rw [shiftedPolydiskBalayage_of_mem hz]; exact le_max_left _ _
  · rw [shiftedPolydiskBalayage_of_notMem hz]

/-! ### Near the boundary the shifted balayage *is* the datum -/

/-- **Off the open polydisk the `ε`-shifted balayage coincides with the datum on
a whole neighbourhood.**  Away from `P̄` this is the definition; at a boundary
point `ζ` it is the envelope's boundary estimate
`limsup_{z → ζ} perronEnvelope u z ≤ u ζ` together with the continuity of `u`,
which between them push `perronEnvelope u - ε` strictly below `u` near `ζ`. -/
theorem eventually_shiftedPolydiskBalayage_eq
    {u : ComplexModel n → ℝ} (hu : IsPerronData u) {Ω : Set (ComplexModel n)}
    (hΩ : IsOpen Ω) (hcont : ContinuousOn u Ω) {ζ : ComplexModel n}
    (hζΩ : ζ ∈ Ω) (hζ : ζ ∉ unitPolydisk n) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ z in 𝓝 ζ, shiftedPolydiskBalayage u ε z = u z := by
  by_cases hcl : ζ ∈ closedUnitPolydisk n
  · have hb : ζ ∈ closedUnitPolydisk n \ unitPolydisk n := ⟨hcl, hζ⟩
    have hhalf : (0 : ℝ) < ε / 2 := by linarith
    have h1 : ∀ᶠ z in 𝓝 ζ, z ∈ unitPolydisk n → perronEnvelope u z ≤ u ζ + ε / 2 :=
      eventually_nhdsWithin_iff.mp (hu.eventually_perronEnvelope_le hb hhalf)
    have hca : ContinuousAt u ζ := hcont.continuousAt (hΩ.mem_nhds hζΩ)
    have h2 : ∀ᶠ z in 𝓝 ζ, u ζ - ε / 2 < u z :=
      hca.tendsto.eventually (eventually_gt_nhds (by linarith))
    filter_upwards [h1, h2] with z hz1 hz2
    by_cases hzP : z ∈ unitPolydisk n
    · rw [shiftedPolydiskBalayage_of_mem hzP]
      have hle := hz1 hzP
      exact max_eq_left (by linarith)
    · exact shiftedPolydiskBalayage_of_notMem hzP
  · filter_upwards [isClosed_closedUnitPolydisk.isOpen_compl.mem_nhds hcl] with z hz
    exact shiftedPolydiskBalayage_of_notMem fun h =>
      hz (unitPolydisk_subset_closedUnitPolydisk h)

/-- **The shifted balayage is plurisubharmonic on the ambient domain.**  On the
polydisk it is the maximum of two plurisubharmonic functions; at every other
point of `Ω` — the boundary `∂P` included — it agrees with `u` on a whole
neighbourhood, so no maximum principle across `∂P` is needed. -/
theorem plurisubharmonicOn_shiftedPolydiskBalayage
    {u : ComplexModel n → ℝ} (hu : IsPerronData u) {Ω : Set (ComplexModel n)}
    (hΩ : IsOpen Ω) (hcont : ContinuousOn u Ω)
    (hupsh : PlurisubharmonicOn (fun z ↦ (u z : EReal)) Ω) {ε : ℝ} (hε : 0 < ε) :
    PlurisubharmonicOn (fun z ↦ (shiftedPolydiskBalayage u ε z : EReal)) Ω := by
  intro x hx
  by_cases hxP : x ∈ unitPolydisk n
  · have hmax := (hu.psh.max (hu.plurisubharmonicOn_perronEnvelope.add_const (-ε))) x hxP
    refine hmax.congr ?_
    filter_upwards [isOpen_unitPolydisk.mem_nhds hxP] with y hy
    rw [shiftedPolydiskBalayage_of_mem hy]
    have hcoe : ((perronEnvelope u y : EReal) + ((-ε : ℝ) : EReal))
        = ((perronEnvelope u y - ε : ℝ) : EReal) := by
      rw [← EReal.coe_add, sub_eq_add_neg]
    rw [hcoe]
    rcases le_total (u y) (perronEnvelope u y - ε) with h | h
    · rw [max_eq_right h, max_eq_right (EReal.coe_le_coe_iff.mpr h)]
    · rw [max_eq_left h, max_eq_left (EReal.coe_le_coe_iff.mpr h)]
  · refine (hupsh x hx).congr ?_
    filter_upwards [eventually_shiftedPolydiskBalayage_eq hu hΩ hcont hx hxP hε] with y hy
    rw [hy]

/-! ### The balayage is upper semicontinuous -/

/-- Upper semicontinuity of the balayage, in real form.  Inside `P` it is that
of the envelope; at a boundary point the envelope's boundary estimate supplies
it from inside and the continuity of `u` from outside. -/
theorem eventually_polydiskBalayage_lt
    {u : ComplexModel n → ℝ} (hu : IsPerronData u) {Ω : Set (ComplexModel n)}
    (hΩ : IsOpen Ω) (hcont : ContinuousOn u Ω) {x : ComplexModel n} (hx : x ∈ Ω)
    {b : ℝ} (hb : polydiskBalayage u x < b) :
    ∀ᶠ z in 𝓝 x, polydiskBalayage u z < b := by
  by_cases hxP : x ∈ unitPolydisk n
  · have husc : UpperSemicontinuousAt (fun z ↦ (perronEnvelope u z : EReal)) x :=
      (hu.plurisubharmonicOn_perronEnvelope x hxP).upperSemicontinuousAt
    rw [polydiskBalayage_of_mem hxP] at hb
    have hlt : ((perronEnvelope u x : ℝ) : EReal) < ((b : ℝ) : EReal) :=
      EReal.coe_lt_coe_iff.mpr hb
    filter_upwards [husc _ hlt, isOpen_unitPolydisk.mem_nhds hxP] with z hz hzP
    rw [polydiskBalayage_of_mem hzP]
    exact EReal.coe_lt_coe_iff.mp hz
  · rw [polydiskBalayage_of_notMem hxP] at hb
    have hca : ContinuousAt u x := hcont.continuousAt (hΩ.mem_nhds hx)
    have hu2 : ∀ᶠ z in 𝓝 x, u z < b := hca.tendsto.eventually (eventually_lt_nhds hb)
    by_cases hcl : x ∈ closedUnitPolydisk n
    · have hbd : x ∈ closedUnitPolydisk n \ unitPolydisk n := ⟨hcl, hxP⟩
      have hε : (0 : ℝ) < (b - u x) / 2 := by linarith
      have h1 : ∀ᶠ z in 𝓝 x, z ∈ unitPolydisk n →
          perronEnvelope u z ≤ u x + (b - u x) / 2 :=
        eventually_nhdsWithin_iff.mp (hu.eventually_perronEnvelope_le hbd hε)
      filter_upwards [h1, hu2] with z hz1 hz2
      by_cases hzP : z ∈ unitPolydisk n
      · rw [polydiskBalayage_of_mem hzP]
        have hle := hz1 hzP
        linarith
      · rw [polydiskBalayage_of_notMem hzP]; exact hz2
    · filter_upwards [isClosed_closedUnitPolydisk.isOpen_compl.mem_nhds hcl, hu2]
        with z hz hz2
      rw [polydiskBalayage_of_notMem fun h =>
        hz (unitPolydisk_subset_closedUnitPolydisk h)]
      exact hz2

/-- The balayage is upper semicontinuous at every point of the ambient
domain. -/
theorem upperSemicontinuousAt_coe_polydiskBalayage
    {u : ComplexModel n → ℝ} (hu : IsPerronData u) {Ω : Set (ComplexModel n)}
    (hΩ : IsOpen Ω) (hcont : ContinuousOn u Ω) {x : ComplexModel n} (hx : x ∈ Ω) :
    UpperSemicontinuousAt (fun z ↦ ((polydiskBalayage u z : ℝ) : EReal)) x := by
  intro c hc
  obtain ⟨b, hb1, hb2⟩ := EReal.lt_iff_exists_real_btwn.mp hc
  have hb : polydiskBalayage u x < b := EReal.coe_lt_coe_iff.mp hb1
  filter_upwards [eventually_polydiskBalayage_lt hu hΩ hcont hx hb] with z hz
  exact lt_trans (EReal.coe_lt_coe_iff.mpr hz) hb2

/-! ### The balayage is the supremum of its shifts -/

/-- The family of `ε`-shifted balayages, as `EReal`-valued functions. -/
def shiftedPolydiskBalayageFamily (u : ComplexModel n → ℝ) :
    Set (ComplexModel n → EReal) :=
  {f | ∃ ε : ℝ, 0 < ε ∧ f = fun z ↦ ((shiftedPolydiskBalayage u ε z : ℝ) : EReal)}

/-- **The shifts increase to the balayage.**  Inside `P` the supremum over
`ε > 0` of `max (u, perronEnvelope u - ε)` is `perronEnvelope u`, because
`u ≤ perronEnvelope u` there; outside, every shift already equals `u`. -/
theorem sSup_shiftedPolydiskBalayageFamily_apply {u : ComplexModel n → ℝ}
    (hu : IsPerronData u) (z : ComplexModel n) :
    sSup (shiftedPolydiskBalayageFamily u) z
      = ((polydiskBalayage u z : ℝ) : EReal) := by
  rw [sSup_apply]
  refine le_antisymm (iSup_le ?_) ?_
  · rintro ⟨f, ε, hε, rfl⟩
    exact EReal.coe_le_coe_iff.mpr
      (shiftedPolydiskBalayage_le_polydiskBalayage hu hε.le z)
  · by_contra hcon
    push Not at hcon
    obtain ⟨b, hb1, hb2⟩ := EReal.lt_iff_exists_real_btwn.mp hcon
    have hbz : b < polydiskBalayage u z := EReal.coe_lt_coe_iff.mp hb2
    have key : ∃ ε : ℝ, 0 < ε ∧ b ≤ shiftedPolydiskBalayage u ε z := by
      by_cases hzP : z ∈ unitPolydisk n
      · rw [polydiskBalayage_of_mem hzP] at hbz
        refine ⟨perronEnvelope u z - b, by linarith, ?_⟩
        rw [shiftedPolydiskBalayage_of_mem hzP]
        exact le_max_of_le_right (by linarith)
      · refine ⟨1, one_pos, ?_⟩
        rw [shiftedPolydiskBalayage_of_notMem hzP]
        rw [polydiskBalayage_of_notMem hzP] at hbz
        exact hbz.le
    obtain ⟨ε, hε, hle⟩ := key
    have hge : ((b : ℝ) : EReal)
        ≤ ⨆ f : shiftedPolydiskBalayageFamily u, (f : ComplexModel n → EReal) z :=
      le_iSup_of_le ⟨_, ⟨ε, hε, rfl⟩⟩ (EReal.coe_le_coe_iff.mpr hle)
    exact absurd hb1 (not_lt.mpr hge)

/-! ### The gluing -/

/-- **Xia's Proposition 1.2.9 on the unit polydisk: the balayage is
plurisubharmonic on the whole ambient domain.**  The datum `u` is
plurisubharmonic and continuous on an open `Ω`; its balayage `û`, equal to
`perronEnvelope u` inside `P` and to `u` outside, is plurisubharmonic on `Ω`.
No relation between `Ω` and the polydisk is required: at a point of `Ω` outside
`P̄` the balayage simply *is* `u`, and the boundary points of `P` that lie in
`Ω` are handled by the shift.  In the intended application `Ω` contains `P̄`.

The proof never crosses `∂P` with a maximum principle.  The `ε`-shifted
balayages are plurisubharmonic (`plurisubharmonicOn_shiftedPolydiskBalayage`)
because each of them *equals* `u` near `∂P`; they increase to `û`
(`sSup_shiftedPolydiskBalayageFamily_apply`); and `û` is already upper
semicontinuous (`upperSemicontinuousAt_coe_polydiskBalayage`), so the
upper-semicontinuous regularization of their supremum — plurisubharmonic by
`FirstPass.plurisubharmonicOn_uscRegularization_sSup` — is `û` itself. -/
theorem plurisubharmonicOn_polydiskBalayage
    {u : ComplexModel n → ℝ} (hu : IsPerronData u) {Ω : Set (ComplexModel n)}
    (hΩ : IsOpen Ω) (hcont : ContinuousOn u Ω)
    (hupsh : PlurisubharmonicOn (fun z ↦ (u z : EReal)) Ω) :
    PlurisubharmonicOn (fun z ↦ ((polydiskBalayage u z : ℝ) : EReal)) Ω := by
  set F := shiftedPolydiskBalayageFamily u with hFdef
  have hne : F.Nonempty := ⟨_, ⟨1, one_pos, rfl⟩⟩
  have hpshF : ∀ f ∈ F, PlurisubharmonicOn f Ω := by
    rintro f ⟨ε, hε, rfl⟩
    exact plurisubharmonicOn_shiftedPolydiskBalayage hu hΩ hcont hupsh hε
  have hbdd : LocallyUniformlyBoundedAbove F Ω := by
    intro x hx
    have h := eventually_polydiskBalayage_lt hu hΩ hcont hx
      (b := polydiskBalayage u x + 1) (by linarith)
    obtain ⟨U, hUsub, hUo, hxU⟩ := _root_.mem_nhds_iff.mp h
    refine ⟨U, nhdsWithin_le_nhds (hUo.mem_nhds hxU), polydiskBalayage u x + 1, ?_⟩
    rintro f ⟨ε, hε, rfl⟩ y ⟨hyU, -⟩
    exact EReal.coe_le_coe_iff.mpr
      ((shiftedPolydiskBalayage_le_polydiskBalayage hu hε.le y).trans (hUsub hyU).le)
  have hreg := plurisubharmonicOn_uscRegularization_sSup hΩ hne hpshF hbdd
  intro x hx
  refine (hreg x hx).congr ?_
  filter_upwards [hΩ.mem_nhds hx] with y hy
  refine le_antisymm ?_ ?_
  · refine uscRegularization_le_of_eventually_le
      (upperSemicontinuousAt_coe_polydiskBalayage hu hΩ hcont hy) ?_
    exact Eventually.of_forall fun w =>
      (sSup_shiftedPolydiskBalayageFamily_apply hu w).le
  · calc ((polydiskBalayage u y : ℝ) : EReal)
        = sSup F y := (sSup_shiftedPolydiskBalayageFamily_apply hu y).symm
      _ ≤ uscRegularization (sSup F) y := le_uscRegularization _ y

end SGPT.Foundations.Analysis.Pending.BedfordTaylor

end
