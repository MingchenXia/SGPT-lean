import SGPT.Foundations.Analysis.Pending.ScaledPolydiskBalayageMass
import SGPT.Foundations.Analysis.Pending.PatchLocalVanishingMass

set_option autoImplicit false

/-!
# From a balayage contact identity on one small polydisk to (2.21)

Xia's Lemma 2.4.3 (`xia-sgpt:page-0079`, equation (2.21)) concludes that the
non-pluripolar Monge--Ampère measure of `P_θ(f)` vanishes on the open set
`U = {P_θ(f) < f} \ nK({θ})`.  Its proof is local and has exactly two halves:

* an **order** half — around each point of `U` the potential *coincides with its
  own balayage* on a small holomorphic ball (Xia runs the domination principle
  and the extremality of `P_θ(f)` to get this), and
* a **measure** half — a potential which is its own balayage on a ball carries
  no Monge--Ampère mass there, and local vanishing on a neighbourhood of each
  point of `U` gives vanishing on `U`.

This module discharges the measure half completely, for the polydisk version of
the ball that this workspace has Proposition 1.2.9 for.  What is left of Lemma
2.4.3 is the order half alone, isolated as the single hypothesis
`EqOn (correctedReal P i₀) (scaledPolydiskBalayage c r (correctedReal P i₀))`
of `diagonalPotentialMeasure_eq_zero_of_locally_eqOn_balayage`.

The three ingredients were all present and are only joined here:

* `Pending.ScaledPolydiskBalayageMass.eq_zero_of_isBTLimit_scaledPolydiskBalayage`
  (Proposition 1.2.9 on `c + r P`, measure half),
* `Pending.PatchLocalVanishingMass.diagonalPotentialMeasure_eq_zero_of_locally_isBTLimit_zero`
  (the global-to-local bridge that needs no bound on `M`),
* the elementary geometry of the polydisk inside a chart domain, proved below:
  every point of an open subset of `ℂⁿ` is the centre of a *closed* polydisk
  contained in it.

The diagonalization step is needed because a `Patch` carries one smooth local
potential per slot, while the local Bedford--Taylor theorems are stated for a
constant tuple.  For a diagonal tuple `θ i = θ`, `u i = w` any one slot's
potential serves for all of them; `diagPatch` records that.
-/

open Set Filter MeasureTheory TopologicalSpace Metric
open scoped ENNReal Topology

noncomputable section

namespace SGPT.Foundations.Analysis.Pending.BedfordTaylor

open FirstPass FirstPass.MongeAmpere

variable {n : ℕ}

/-! ### Elementary geometry of the scaled polydisk -/

/-- The closed unit polydisk sits in the ball of radius `√n`. -/
theorem norm_le_sqrt_of_mem_closedUnitPolydisk {w : ComplexModel n}
    (hw : w ∈ closedUnitPolydisk n) : ‖w‖ ≤ Real.sqrt n := by
  rw [EuclideanSpace.norm_eq]
  refine Real.sqrt_le_sqrt ?_
  calc ∑ i : Fin n, ‖w i‖ ^ 2 ≤ ∑ _i : Fin n, (1 : ℝ) := by
        refine Finset.sum_le_sum fun i _ => ?_
        have := hw i
        nlinarith [norm_nonneg (w i)]
    _ = n := by simp

/-- The centre lies in the open polydisk. -/
theorem mem_scaledPolydisk_center {c : ComplexModel n} {r : ℝ} (hr : r ≠ 0) :
    c ∈ scaledPolydisk c r := by
  rw [mem_scaledPolydisk_iff hr]
  intro i
  have h0 : polydiskChartInv c r c = 0 := by
    simp [polydiskChartInv]
  rw [h0]
  simp

/-- **Every point of an open subset of `ℂⁿ` is the centre of a closed polydisk
contained in it.**  This is the shrinking step of Lemma 2.4.3 ("take holomorphic
balls `B ⋐ B' ⋐ U`"), in the polydisk form the workspace's Proposition 1.2.9 is
available for. -/
theorem exists_pos_image_closedUnitPolydisk_subset {Ω : Opens (ComplexModel n)}
    {c : ComplexModel n} (hc : c ∈ Ω) :
    ∃ r : ℝ, 0 < r ∧
      polydiskChart c r '' closedUnitPolydisk n ⊆ (Ω : Set (ComplexModel n)) := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp Ω.isOpen c hc
  have hs : (0 : ℝ) ≤ Real.sqrt n := Real.sqrt_nonneg _
  have hpos : (0 : ℝ) < 2 * (Real.sqrt n + 1) := by positivity
  set r : ℝ := ε / (2 * (Real.sqrt n + 1)) with hrdef
  have hr : 0 < r := by rw [hrdef]; exact div_pos hε hpos
  refine ⟨r, hr, ?_⟩
  rintro _ ⟨w, hw, rfl⟩
  refine hball ?_
  rw [Metric.mem_ball, dist_eq_norm]
  have hsub : polydiskChart c r w - c = (r : ℂ) • w := by simp [polydiskChart]
  have hnr : ‖(r : ℂ)‖ = r := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  rw [hsub, norm_smul, hnr]
  have hw' := norm_le_sqrt_of_mem_closedUnitPolydisk hw
  rw [hrdef, div_mul_eq_mul_div, div_lt_iff₀ hpos]
  nlinarith [norm_nonneg w]

/-- A closed polydisk inside `Ω` makes the *open* polydisk an open subset of
`Ω`. -/
theorem scaledPolydiskOpens_le {Ω : Opens (ComplexModel n)} {c : ComplexModel n}
    {r : ℝ} (hr : r ≠ 0)
    (hPΩ : polydiskChart c r '' closedUnitPolydisk n ⊆ (Ω : Set (ComplexModel n))) :
    scaledPolydiskOpens c r ≤ Ω := by
  intro z hz
  have hz' : z ∈ scaledPolydisk c r := by rwa [← coe_scaledPolydiskOpens hr]
  obtain ⟨w, hw, rfl⟩ := hz'
  exact hPΩ ⟨w, unitPolydisk_subset_closedUnitPolydisk hw, rfl⟩

/-! ### The measure half, from the contact identity -/

/-- **A locally bounded psh function which agrees with its own balayage on the
polydisk carries no Bedford--Taylor mass there.**  Pure transport: the datum is
replaced by its balayage on the open polydisk by
`Pending.BedfordTaylor.IsBTLimit.congr`, and
`eq_zero_of_isBTLimit_scaledPolydiskBalayage` applies. -/
theorem eq_zero_of_isBTLimit_of_eqOn_scaledPolydiskBalayage (hn : 0 < n)
    {Ω : Opens (ComplexModel n)} {u : ComplexModel n → ℝ}
    (hu : IsLocallyBoundedPshOn Ω u) {c : ComplexModel n} {r : ℝ} (hr : r ≠ 0)
    (hPΩ : polydiskChart c r '' closedUnitPolydisk n ⊆ (Ω : Set (ComplexModel n)))
    (heq : EqOn u (scaledPolydiskBalayage c r u) (scaledPolydisk c r))
    {μ : Measure (ComplexModel n)}
    (hμ : IsBTLimit (scaledPolydiskOpens c r) (fun _ => u) μ) :
    μ = 0 :=
  eq_zero_of_isBTLimit_scaledPolydiskBalayage hn hu hr hPΩ
    (hμ.congr fun _ z hz => heq (by rwa [← coe_scaledPolydiskOpens hr]))

end SGPT.Foundations.Analysis.Pending.BedfordTaylor

/-! ### The global criterion -/

namespace SGPT.Foundations.Analysis.Pending.PolydiskPatchVanishing

open FirstPass FirstPass.MongeAmpere
open FirstPass.GlobalPotentialPatches
open BedfordTaylor
open SGPT.Foundations.Analysis.Pending.BoundedGlobalProduct
open SGPT.Foundations.Analysis.Pending.PatchLocalBoundedMeasure
open SGPT.Foundations.Analysis.Pending.PatchLocalVanishingMass
open SGPT.Foundations.Analysis.Pending.DiagonalMass

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]

/-- **One slot's smooth local potential serves for a diagonal tuple.**  For
`θ i = θ` and `u i = w` a patch may be rebuilt with the same correction in every
slot; that turns `correctedReal` into a constant tuple, which is the shape the
local Bedford--Taylor theorems consume. -/
def diagPatch {theta : ClosedRealOneOneForm n M} {w : M → EReal}
    (P : Patch (fun _ : Fin n => theta) (fun _ => w)) (i₀ : Fin n) :
    Patch (fun _ : Fin n => theta) (fun _ => w) where
  chart := P.chart
  domain := P.domain
  domain_le_target := P.domain_le_target
  potential := fun _ => P.potential i₀
  localPotential := fun _ => P.localPotential i₀
  plurisubharmonic := fun _ => P.plurisubharmonic i₀

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
@[simp] theorem diagPatch_source {theta : ClosedRealOneOneForm n M} {w : M → EReal}
    (P : Patch (fun _ : Fin n => theta) (fun _ => w)) (i₀ : Fin n) :
    (diagPatch P i₀).source = P.source := rfl

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
theorem correctedReal_diagPatch {theta : ClosedRealOneOneForm n M} {w : M → EReal}
    (P : Patch (fun _ : Fin n => theta) (fun _ => w)) (i₀ i : Fin n) :
    correctedReal (diagPatch P i₀) i = correctedReal P i₀ := rfl

/-- **The measure half of Xia's Lemma 2.4.3.**  If around every point of `S`
the local representative of the `θ`-PSH potential `w` agrees with its own
balayage on some closed polydisk contained in a chart domain on which `w` is
bounded, then `θⁿ_w` gives no mass to `S`.

`S` need not be measurable, open, or contained in one chart, and no bound on
`w` over all of `M` is required — which is the point, since Xia's datum
`P_θ(f)` is only locally bounded away from `nK({θ})`. -/
theorem diagonalPotentialMeasure_eq_zero_of_locally_eqOn_balayage (hn : 0 < n)
    {theta : ClosedRealOneOneForm n M} {w : M → EReal}
    (hw : IsThetaPshPotential theta.val w) {S : Set M}
    (h : ∀ x ∈ S, ∃ (P : Patch (fun _ : Fin n => theta) (fun _ => w)) (i₀ : Fin n),
      x ∈ P.source ∧ IsBoundedPotentialOn w P.source ∧
      ∃ c : ComplexModel n, ∃ r : ℝ, 0 < r ∧
        polydiskChart c r '' closedUnitPolydisk n ⊆ (P.domain : Set (ComplexModel n)) ∧
        P.chart.val x ∈ scaledPolydisk c r ∧
        EqOn (correctedReal P i₀)
          (scaledPolydiskBalayage c r (correctedReal P i₀)) (scaledPolydisk c r)) :
    diagonalPotentialMeasure theta w hw S = 0 := by
  refine diagonalPotentialMeasure_eq_zero_of_locally_isBTLimit_zero hw ?_
  intro x hx
  obtain ⟨P, i₀, hxP, hb, c, r, hr, hPΩ, hxc, heq⟩ := h x hx
  have hr0 : r ≠ 0 := ne_of_gt hr
  have hle : scaledPolydiskOpens c r ≤ (diagPatch P i₀).domain :=
    scaledPolydiskOpens_le hr0 hPΩ
  refine ⟨(diagPatch P i₀).restrict (scaledPolydiskOpens c r) hle, ?_, ?_, ?_⟩
  · rw [Patch.mem_source_restrict]
    exact ⟨hxP, by rwa [← coe_scaledPolydiskOpens hr0] at hxc⟩
  · intro _
    exact hb.mono fun y hy => (Patch.mem_source_restrict _ _ hle |>.mp hy).1
  · intro μ hμ
    have hu : IsLocallyBoundedPshOn P.domain (correctedReal P i₀) :=
      correctedReal_isLocallyBoundedPshOn_of_boundedOn (i := i₀) (P := P) hb
    exact eq_zero_of_isBTLimit_of_eqOn_scaledPolydiskBalayage hn hu hr0 hPΩ heq hμ

end SGPT.Foundations.Analysis.Pending.PolydiskPatchVanishing

end
