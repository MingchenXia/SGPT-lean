import SGPT.Foundations.Analysis.Pending.ScaledPolydiskBalayageMass

set_option autoImplicit false

/-!
# The two order facts of the balayage, on a polydisk of arbitrary centre

`Pending.ScaledPolydiskBalayageMass` proves, on the **unit** polydisk and for a
locally bounded plurisubharmonic datum, that the balayage dominates its datum
(`le_perronEnvelope_of_isLocallyBoundedPshOn`) and inherits any upper bound the
datum has on `P̄` (`perronEnvelope_le_of_isLocallyBoundedPshOn`).  Xia's Lemma
2.4.3 (`xia-sgpt:page-0079`) uses both on a *small* polydisk around an arbitrary
point of a chart, which is what this file supplies.

The second one is what replaces the domination principle (Xia Prop 1.2.10) at
the one place Lemma 2.4.3 invokes it: Xia compares the balayage with a
**constant** `f(x) - ε`, and the balayage of this workspace *is* a Perron
envelope, so it inherits the bound outright (I-0267, folded from I-0384).

Pure affine transport along `polydiskChart c r`; no new analytic content.
-/

open Set TopologicalSpace

noncomputable section

namespace SGPT.Foundations.Analysis.Pending.BedfordTaylor

open FirstPass FirstPass.MongeAmpere

variable {n : ℕ}

section

variable {Ω : Opens (ComplexModel n)} {u : ComplexModel n → ℝ}
  {c : ComplexModel n} {r : ℝ}

/-- The pulled-back datum is locally bounded psh on the pulled-back open set,
and the closed unit polydisk lands inside it. -/
private theorem closedUnitPolydisk_subset_comap
    (hPΩ : polydiskChart c r '' closedUnitPolydisk n ⊆ (Ω : Set (ComplexModel n))) :
    closedUnitPolydisk n ⊆
      ((Opens.comap ⟨polydiskChart c r, continuous_polydiskChart c r⟩ Ω :
        Opens (ComplexModel n)) : Set (ComplexModel n)) :=
  fun w hw => hPΩ ⟨w, hw, rfl⟩

/-- **The balayage on `c + rP` dominates its datum.** -/
theorem le_scaledPolydiskBalayage (hn : 0 < n) (hu : IsLocallyBoundedPshOn Ω u)
    (hr : r ≠ 0)
    (hPΩ : polydiskChart c r '' closedUnitPolydisk n ⊆ (Ω : Set (ComplexModel n)))
    {z : ComplexModel n} (hz : z ∈ scaledPolydisk c r) :
    u z ≤ scaledPolydiskBalayage c r u z := by
  have hzu : polydiskChartInv c r z ∈ unitPolydisk n :=
    (mem_scaledPolydisk_iff hr).mp hz
  have h := le_perronEnvelope_of_isLocallyBoundedPshOn hn
    (isLocallyBoundedPshOn_comp_polydiskChart hu c r)
    (closedUnitPolydisk_subset_comap hPΩ) hzu
  rw [scaledPolydiskBalayage_of_mem hr u hz]
  rwa [polydiskChart_polydiskChartInv hr] at h

/-- **The balayage on `c + rP` inherits an upper bound of its datum on the
closed polydisk.**  This is the statement Xia takes from the domination
principle. -/
theorem scaledPolydiskBalayage_le (hn : 0 < n) (hu : IsLocallyBoundedPshOn Ω u)
    (hr : r ≠ 0)
    (hPΩ : polydiskChart c r '' closedUnitPolydisk n ⊆ (Ω : Set (ComplexModel n)))
    {Mb : ℝ}
    (hMb : ∀ y ∈ polydiskChart c r '' closedUnitPolydisk n, u y ≤ Mb)
    {z : ComplexModel n} (hz : z ∈ scaledPolydisk c r) :
    scaledPolydiskBalayage c r u z ≤ Mb := by
  have hzu : polydiskChartInv c r z ∈ unitPolydisk n :=
    (mem_scaledPolydisk_iff hr).mp hz
  have hMb' : ∀ x ∈ closedUnitPolydisk n, u (polydiskChart c r x) ≤ Mb :=
    fun x hx => hMb _ ⟨x, hx, rfl⟩
  have h := perronEnvelope_le_of_isLocallyBoundedPshOn hn
    (isLocallyBoundedPshOn_comp_polydiskChart hu c r)
    (closedUnitPolydisk_subset_comap hPΩ) hMb' hzu
  rw [scaledPolydiskBalayage_of_mem hr u hz]
  exact h

/-- Off the closed polydisk the balayage is the datum, so any bound of the datum
on a set meeting the polydisk only where the closed-polydisk bound holds is a
bound of the balayage.  The convenient packaged form: a datum bounded above by
`Mb` on all of `Ω` gives a balayage bounded above by `Mb` on `Ω`. -/
theorem scaledPolydiskBalayage_le_of_forall (hn : 0 < n)
    (hu : IsLocallyBoundedPshOn Ω u) (hr : r ≠ 0)
    (hPΩ : polydiskChart c r '' closedUnitPolydisk n ⊆ (Ω : Set (ComplexModel n)))
    {Mb : ℝ} (hMb : ∀ y ∈ (Ω : Set (ComplexModel n)), u y ≤ Mb)
    {z : ComplexModel n} (hz : z ∈ (Ω : Set (ComplexModel n))) :
    scaledPolydiskBalayage c r u z ≤ Mb := by
  by_cases hzP : z ∈ scaledPolydisk c r
  · exact scaledPolydiskBalayage_le hn hu hr hPΩ (fun y hy => hMb y (hPΩ hy)) hzP
  · rw [scaledPolydiskBalayage_eqOn_compl hr u hzP]
    exact hMb z hz

end

end SGPT.Foundations.Analysis.Pending.BedfordTaylor

end
