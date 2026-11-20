import SGPT.Foundations.Analysis.Pending.PolydiskBalayagePshDatum

set_option autoImplicit false

/-!
# The balayage on an arbitrary polydisk, by affine transport

`Pending.PolydiskBalayagePshDatum.plurisubharmonicOn_polydiskBalayage_of_isLocallyBoundedPshOn`
(Xia, Proposition 1.2.9) solves the balayage problem on the **unit** polydisk.
Xia's Lemma 2.4.3 (`xia-sgpt:page-0078`--`xia-sgpt:page-0079`) uses it on a
*small* polydisk around an arbitrary point of a chart, which is the shape this
file supplies: for a centre `c` and a radius `r > 0`,

  `scaledPolydiskBalayage c r u = polydiskBalayage (u ∘ T) ∘ T⁻¹`,
  `T w = c + r • w`,

is plurisubharmonic on the same open set as `u`, and agrees with `u` off the
closed polydisk `c + r P`.

The transport is an equality of definitions, not a new analytic argument: `T`
is an invertible complex-affine map, and `PlurisubharmonicOn.comp_affine`
transports plurisubharmonicity both ways.  It is recorded separately because
the two halves of the gluing step of Lemma 2.4.3 then meet: this file gives the
locally modified potential, and
`Pending.QuasiEquisingularCollarGluing.isThetaPshPotential_gluedMax` glues it to
a global `θ`-PSH function — its `hcollar` hypothesis is exactly
`scaledPolydiskBalayage_eqOn_compl` below.

The datum is real valued and locally bounded, which is the class Proposition
1.2.9 is available for in this workspace (the human accepted that route when
closing I-0362).  A `θ`-PSH potential with poles therefore has to be truncated
before it is fed in; the truncation laws are in
`Pending.RooftopEnvelopeNormalization`.
-/

noncomputable section

open Set Filter TopologicalSpace

namespace SGPT.Foundations.Analysis.Pending.BedfordTaylor

open FirstPass FirstPass.MongeAmpere

variable {n : ℕ}

/-! ### The affine parametrization -/

/-- The affine parametrization of the polydisk of radius `r` centred at `c` by
the unit polydisk. -/
def polydiskChart (c : ComplexModel n) (r : ℝ) : ComplexModel n → ComplexModel n :=
  fun w => c + (r : ℂ) • w

/-- Its inverse, for `r ≠ 0`. -/
def polydiskChartInv (c : ComplexModel n) (r : ℝ) :
    ComplexModel n → ComplexModel n :=
  fun z => ((r : ℂ))⁻¹ • (z - c)

theorem continuous_polydiskChart (c : ComplexModel n) (r : ℝ) :
    Continuous (polydiskChart c r) :=
  continuous_const.add (continuous_const_smul _)

theorem continuous_polydiskChartInv (c : ComplexModel n) (r : ℝ) :
    Continuous (polydiskChartInv c r) := by
  have h : Continuous fun z : ComplexModel n => z - c :=
    continuous_id.sub continuous_const
  exact h.const_smul ((r : ℂ)⁻¹)

theorem polydiskChartInv_polydiskChart {c : ComplexModel n} {r : ℝ} (hr : r ≠ 0)
    (w : ComplexModel n) :
    polydiskChartInv c r (polydiskChart c r w) = w := by
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  simp only [polydiskChart, polydiskChartInv, add_sub_cancel_left, smul_smul,
    inv_mul_cancel₀ hr', one_smul]

theorem polydiskChart_polydiskChartInv {c : ComplexModel n} {r : ℝ} (hr : r ≠ 0)
    (z : ComplexModel n) :
    polydiskChart c r (polydiskChartInv c r z) = z := by
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  simp only [polydiskChart, polydiskChartInv, smul_smul, mul_inv_cancel₀ hr',
    one_smul, add_sub_cancel]

/-- The open polydisk of radius `r` centred at `c`. -/
def scaledPolydisk (c : ComplexModel n) (r : ℝ) : Set (ComplexModel n) :=
  polydiskChart c r '' unitPolydisk n

theorem mem_scaledPolydisk_iff {c : ComplexModel n} {r : ℝ} (hr : r ≠ 0)
    {z : ComplexModel n} :
    z ∈ scaledPolydisk c r ↔ polydiskChartInv c r z ∈ unitPolydisk n := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    rwa [polydiskChartInv_polydiskChart hr]
  · intro hz
    exact ⟨polydiskChartInv c r z, hz, polydiskChart_polydiskChartInv hr z⟩

/-! ### The transported balayage -/

/-- **The balayage of `u` on the polydisk of radius `r` centred at `c`**: the
unit-polydisk balayage of the pulled-back datum, pushed forward again. -/
def scaledPolydiskBalayage (c : ComplexModel n) (r : ℝ)
    (u : ComplexModel n → ℝ) : ComplexModel n → ℝ :=
  fun z => polydiskBalayage (fun w => u (polydiskChart c r w))
    (polydiskChartInv c r z)

/-- **The collar identity.**  Off the polydisk the transported balayage is the
datum itself.  This is the hypothesis `hcollar` of
`Pending.QuasiEquisingularCollarGluing.isThetaPshPotential_gluedMax`. -/
theorem scaledPolydiskBalayage_eqOn_compl {c : ComplexModel n} {r : ℝ}
    (hr : r ≠ 0) (u : ComplexModel n → ℝ) {z : ComplexModel n}
    (hz : z ∉ scaledPolydisk c r) :
    scaledPolydiskBalayage c r u z = u z := by
  rw [scaledPolydiskBalayage,
    polydiskBalayage_of_notMem ((mem_scaledPolydisk_iff hr).not.mp hz),
    polydiskChart_polydiskChartInv hr]

/-- Inside the polydisk it is the transported Perron envelope. -/
theorem scaledPolydiskBalayage_of_mem {c : ComplexModel n} {r : ℝ} (hr : r ≠ 0)
    (u : ComplexModel n → ℝ) {z : ComplexModel n}
    (hz : z ∈ scaledPolydisk c r) :
    scaledPolydiskBalayage c r u z =
      perronEnvelope (fun w => u (polydiskChart c r w))
        (polydiskChartInv c r z) :=
  polydiskBalayage_of_mem ((mem_scaledPolydisk_iff hr).mp hz)

/-! ### Transport of the two hypotheses -/

theorem isLocallyBoundedPshOn_comp_polydiskChart {Ω : Opens (ComplexModel n)}
    {u : ComplexModel n → ℝ} (hu : IsLocallyBoundedPshOn Ω u)
    (c : ComplexModel n) (r : ℝ) :
    IsLocallyBoundedPshOn
      (Opens.comap ⟨polydiskChart c r, continuous_polydiskChart c r⟩ Ω)
      (fun w => u (polydiskChart c r w)) := by
  constructor
  · have hpsh := hu.1.comp_affine ((r : ℂ) • ContinuousLinearMap.id ℂ (ComplexModel n)) c
    exact hpsh.mono (fun w hw => by simpa [polydiskChart] using hw)
  · intro w hw
    obtain ⟨V, hV, hVΩ, C, hC⟩ := hu.2 (polydiskChart c r w) hw
    refine ⟨Opens.comap ⟨polydiskChart c r, continuous_polydiskChart c r⟩ V, hV,
      ?_, C, fun w' hw' => hC _ hw'⟩
    exact fun w' hw' => hVΩ hw'

/-- **Xia's Proposition 1.2.9 on an arbitrary polydisk.**  For a locally
bounded plurisubharmonic datum on an open `Ω` containing the closed polydisk of
radius `r > 0` around `c`, the transported balayage is plurisubharmonic on all
of `Ω`. -/
theorem plurisubharmonicOn_scaledPolydiskBalayage (hn : 0 < n)
    {Ω : Opens (ComplexModel n)} {u : ComplexModel n → ℝ}
    (hu : IsLocallyBoundedPshOn Ω u) {c : ComplexModel n} {r : ℝ} (hr : r ≠ 0)
    (hPΩ : polydiskChart c r '' closedUnitPolydisk n ⊆ (Ω : Set (ComplexModel n))) :
    PlurisubharmonicOn (fun z => ((scaledPolydiskBalayage c r u z : ℝ) : EReal))
      (Ω : Set (ComplexModel n)) := by
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  set Ω' : Opens (ComplexModel n) :=
    Opens.comap ⟨polydiskChart c r, continuous_polydiskChart c r⟩ Ω with hΩ'
  have hu' := isLocallyBoundedPshOn_comp_polydiskChart hu c r
  have hPΩ' : closedUnitPolydisk n ⊆ (Ω' : Set (ComplexModel n)) := by
    intro w hw
    exact hPΩ ⟨w, hw, rfl⟩
  have hbal :=
    plurisubharmonicOn_polydiskBalayage_of_isLocallyBoundedPshOn hn hu' hPΩ'
  have hcomp := hbal.comp_affine
    (((r : ℂ))⁻¹ • ContinuousLinearMap.id ℂ (ComplexModel n))
    (((r : ℂ))⁻¹ • (-c))
  have key : ∀ z : ComplexModel n,
      ((r : ℂ))⁻¹ • (-c) +
          (((r : ℂ))⁻¹ • ContinuousLinearMap.id ℂ (ComplexModel n)) z
        = polydiskChartInv c r z := by
    intro z
    simp only [smul_apply, ContinuousLinearMap.id_apply,
      polydiskChartInv, ← smul_add, neg_add_eq_sub]
  intro z hz
  have hmem : z ∈ (fun y => ((r : ℂ))⁻¹ • (-c) +
      (((r : ℂ))⁻¹ • ContinuousLinearMap.id ℂ (ComplexModel n)) y) ⁻¹'
      (Ω' : Set (ComplexModel n)) := by
    have hz' : ((r : ℂ))⁻¹ • (-c) +
        (((r : ℂ))⁻¹ • ContinuousLinearMap.id ℂ (ComplexModel n)) z
        ∈ (Ω' : Set (ComplexModel n)) := by
      rw [key z]
      show polydiskChart c r (polydiskChartInv c r z) ∈ (Ω : Set (ComplexModel n))
      rw [polydiskChart_polydiskChartInv hr]
      exact hz
    exact hz'
  refine (hcomp z hmem).congr (Filter.Eventually.of_forall fun y => ?_)
  show (((polydiskBalayage (fun w => u (polydiskChart c r w))
      (((r : ℂ))⁻¹ • (-c) +
        (((r : ℂ))⁻¹ • ContinuousLinearMap.id ℂ (ComplexModel n)) y) : ℝ)) : EReal)
    = (((scaledPolydiskBalayage c r u y : ℝ)) : EReal)
  rw [key y]
  rfl

end SGPT.Foundations.Analysis.Pending.BedfordTaylor
