import SGPT.NPP.NonPluripolarCurrentNonCharging

/-!
# Trace masses of products of degree `p` controlled by top-degree measures

Source: `chapter_npp.tex`, `prop:nppwelldef` (the reduction of the local mass condition
`eq:welldefinepluri` in degree `p` to top-degree measures); Xia, *Foundations of pluripotential
theory*, `thm:compact-nonpluripolar-finiteness` ("on a neighborhood of `K` we have `β ≤ c ω` …
by `eq:trace-measure-form-comparison`").

Let `U ⊆ ℂⁿ` be open, `n = q + p`, `v₁, …, v_p` locally bounded psh on `U` and
`S = dd^c v₁ ∧ ⋯ ∧ dd^c v_p` (the recursive product `btProduct p q v [U]`, a closed positive current
of bidimension `(q,q)`).  If `ρ` is a function on `U` such that `ρ - c ℓ₀` is locally bounded psh,
where `ℓ₀ = quadPot ω₀` is the quadratic potential of the Euclidean Kähler form (`dd^c ℓ₀ = ω₀`)
and `c ≥ 0` — for instance a smooth local potential `ρ` of a Kähler form `ω ≥ c ω₀` — then

`c^q σ_S ≤ (dd^c ρ)^q ∧ dd^c v₁ ∧ ⋯ ∧ dd^c v_p`

as measures on `U` (`smul_traceMeasure_le_recursiveMixedTraceMeasure`), where the right side is
the top-degree mixed Bedford–Taylor measure of the tuple `(ρ, …, ρ, v₁, …, v_p)`
(`recursiveMixedTraceMeasure`, which is TN's canonical mixed measure by
`canonicalMixedBedfordTaylorMeasure_eq_recursiveMixedTraceMeasure`).

Proof: `(ρ, …, ρ, v) = (cℓ₀, …, cℓ₀, v) + (ρ - cℓ₀, …, ρ - cℓ₀, 0, …, 0)` slotwise, so by the
monotonicity of top-degree products (`LocalBedfordTaylorCalculus.traceMeasure_btProduct_le_add`)
the right side dominates the measure of `(cℓ₀, …, cℓ₀, v)`, which is `S ∧ (c ω₀)^q = c^q σ_S`
by the reduction of products of degree `p` to top degree
(`BedfordTaylorTopDegree.btProduct_apply_wedgeProd`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff ENNReal

namespace SGPT.NPP.NonPluripolarCurrent

open SGPT.Foundations.Analysis
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.StronglyPositiveForms
open SGPT.Foundations.Analysis.Pending.LocalProductCurrents
open SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorProducts
open SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorSmoothTraceMeasure
open SGPT.NPP.BedfordTaylorTopDegree

variable {n : ℕ}

/-- The quadratic potential is linear in the form. -/
theorem quadPot_smul (c : ℝ) (β : RealForm n 2) :
    quadPot (c • β) = fun z => c * quadPot β z := by
  funext z
  simp only [quadPot, ContinuousAlternatingMap.smul_apply, smul_eq_mul]
  ring

/-- `recursiveMixedTraceMeasure` only depends on the potentials on `U`. -/
theorem recursiveMixedTraceMeasure_congr {U : Opens (ComplexModel n)}
    {u u' : Fin n → ComplexModel n → ℝ} (hu : ∀ i, IsLocallyBoundedPshOn U (u i))
    (hu' : ∀ i, IsLocallyBoundedPshOn U (u' i)) (h : ∀ i, ∀ x ∈ (U : Set (ComplexModel n)),
      u i x = u' i x) :
    recursiveMixedTraceMeasure U u hu = recursiveMixedTraceMeasure U u' hu' :=
  traceMeasure_congr _ _ (LocalBedfordTaylorDecreasing.btProduct_congr n 0 u u' _ h)

/-- The zero function is locally bounded psh. -/
theorem isLocallyBoundedPshOn_zero (U : Opens (ComplexModel n)) :
    IsLocallyBoundedPshOn U (fun _ => (0 : ℝ)) := by
  have h := isLocallyBoundedPshOn_quadPot (IsSemipositiveOneOne.zero (n := n)) U
  have e : quadPot (0 : RealForm n 2) = fun _ => (0 : ℝ) := by
    funext z
    simp [quadPot]
  rwa [e] at h

/-- **The trace mass of a product of degree `p` is controlled by a top-degree measure**: if
`ρ - c ℓ₀` is locally bounded psh (`ℓ₀ = quadPot ω₀`, `c ≥ 0`), then
`c^q σ_S ≤ (dd^c ρ)^q ∧ dd^c v₁ ∧ ⋯ ∧ dd^c v_p` for `S = dd^c v₁ ∧ ⋯ ∧ dd^c v_p`. -/
theorem smul_traceMeasure_le_recursiveMixedTraceMeasure (p q : ℕ)
    {U : Opens (ComplexModel (q + p))} {v : Fin p → ComplexModel (q + p) → ℝ}
    (hv : ∀ i, IsLocallyBoundedPshOn U (v i)) {ρ : ComplexModel (q + p) → ℝ} {c : ℝ}
    (hc : 0 ≤ c)
    (hρc : IsLocallyBoundedPshOn U fun z => ρ z - c * quadPot (kahlerForm (q + p)) z)
    (hw : ∀ i, IsLocallyBoundedPshOn U (Fin.append (fun _ : Fin q => ρ) v i)) :
    ENNReal.ofReal (c ^ q) • (isPositive_btProduct p q v (oneCurrentOf (U := U) rfl)
        (isPositive_oneCurrentOf rfl) (isClosedAny_oneCurrentOf rfl) hv).1.traceMeasure ≤
      recursiveMixedTraceMeasure U (Fin.append (fun _ : Fin q => ρ) v) hw := by
  set ω₀ := kahlerForm (q + p)
  have hβ : IsSemipositiveOneOne (c • ω₀) := isSemipositiveOneOne_kahlerForm.smul hc
  set a : Fin (q + p) → ComplexModel (q + p) → ℝ :=
    Fin.append (fun _ : Fin q => quadPot (c • ω₀)) v with ha_def
  set b : Fin (q + p) → ComplexModel (q + p) → ℝ :=
    Fin.append (fun _ : Fin q => fun z => ρ z - c * quadPot ω₀ z)
      (fun _ : Fin p => fun _ => (0 : ℝ)) with hb_def
  have ha : ∀ i, IsLocallyBoundedPshOn U (a i) :=
    isLocallyBoundedPshOn_append (fun _ => isLocallyBoundedPshOn_quadPot hβ U) hv
  have hb : ∀ i, IsLocallyBoundedPshOn U (b i) :=
    isLocallyBoundedPshOn_append (fun _ => hρc) (fun _ => isLocallyBoundedPshOn_zero U)
  have hab : (fun i z => a i z + b i z) = Fin.append (fun _ : Fin q => ρ) v := by
    funext i z
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [ha_def, hb_def, Fin.append_left, quadPot_smul]
      ring
    · simp only [ha_def, hb_def, Fin.append_right, add_zero]
  have hS := isPositive_btProduct p q v (oneCurrentOf (U := U) rfl)
    (isPositive_oneCurrentOf rfl) (isClosedAny_oneCurrentOf rfl) hv
  have hL := isPositive_btProduct (q + p) 0 a (oneCurrentOf (U := U) (Nat.zero_add (q + p)))
    (isPositive_oneCurrentOf _) (isClosedAny_oneCurrentOf _) ha
  have habp : ∀ i, IsLocallyBoundedPshOn U ((fun i z => a i z + b i z) i) := fun i =>
    LocalBedfordTaylorCalculus.isLocallyBoundedPshOn_add (ha i) (hb i)
  have hR := isPositive_btProduct (q + p) 0 (fun i z => a i z + b i z)
    (oneCurrentOf (U := U) (Nat.zero_add (q + p))) (isPositive_oneCurrentOf _)
    (isClosedAny_oneCurrentOf _) habp
  have hle := LocalBedfordTaylorCalculus.traceMeasure_btProduct_le_add a b ha hb hL.1 hR.1
  have hRw : hR.1.traceMeasure = recursiveMixedTraceMeasure U (Fin.append (fun _ : Fin q => ρ) v) hw :=
    traceMeasure_congr _ _ (congrArg (fun w => btProduct (q + p) 0 w
      (oneCurrentOf (U := U) (Nat.zero_add (q + p)))) hab)
  -- the measure of `(cℓ₀, …, cℓ₀, v)` is `c^q σ_S`
  have hP : TopDegreeDensity.wedgeProd q (fun _ : Fin q => c • ω₀) ∈ formSpan (q + p) q := by
    rw [wedgeProd_const]
    exact mem_formSpan_of_mem_spCone (formPower_mem_spCone hβ q)
  have hγ : (⟨TopDegreeDensity.wedgeProd q (fun _ : Fin q => c • ω₀), hP⟩ : formSpan (q + p) q) =
      c ^ q • kahlerPower (q + p) q := by
    apply Subtype.ext
    change TopDegreeDensity.wedgeProd q (fun _ : Fin q => c • ω₀) =
      c ^ q • formPower (kahlerForm (q + p)) q
    rw [wedgeProd_const, formPower_smul]
  have hLeq : hL.1.traceMeasure = ENNReal.ofReal (c ^ q) • hS.1.traceMeasure := by
    apply LocalBedfordTaylorLocality.eq_of_forall_testFunction_integral_eq (U := U)
    · exact hL.1.traceMeasure_compl
    · rw [Measure.smul_apply, hS.1.traceMeasure_compl, smul_zero]
    · exact fun K hK hKU => hL.1.traceMeasure_lt_top hK hKU
    · intro K hK hKU
      rw [Measure.smul_apply, smul_eq_mul]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hS.1.traceMeasure_lt_top hK hKU)
    · intro φ
      have h1 := btProduct_apply_wedgeProd p q v hv (fun _ : Fin q => c • ω₀) (fun _ => hβ) hP φ
      rw [hγ, map_smul, _root_.smul_apply, smul_eq_mul] at h1
      rw [integral_smul_measure, ENNReal.toReal_ofReal (pow_nonneg hc q), hS.1.integral_traceMeasure,
        smul_eq_mul, h1]
      rfl
  rw [← hLeq, ← hRw]
  exact hle

/-- **The comparison in the form used for non-pluripolar products** (`q + p = n`, the top-degree
tuple indexed by `Fin n`): if `w = (ρ, …, ρ, v₁, …, v_p)` and `ρ - c ℓ₀` is locally bounded psh,
then `c^q σ_S ≤ μ_w` for `S = dd^c v₁ ∧ ⋯ ∧ dd^c v_p` and the top-degree mixed measure `μ_w`. -/
theorem smul_traceMeasure_le_recursiveMixedTraceMeasure_of_eq {p q : ℕ} (hqp : q + p = n)
    {U : Opens (ComplexModel n)} {v : Fin p → ComplexModel n → ℝ}
    (hv : ∀ i, IsLocallyBoundedPshOn U (v i)) {ρ : ComplexModel n → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hρc : IsLocallyBoundedPshOn U fun z => ρ z - c * quadPot (kahlerForm n) z)
    (w : Fin n → ComplexModel n → ℝ) (hw : ∀ i, IsLocallyBoundedPshOn U (w i))
    (hwdef : ∀ i, w i = Fin.append (fun _ : Fin q => ρ) v (Fin.cast hqp.symm i)) :
    ENNReal.ofReal (c ^ q) • (isPositive_btProduct p q v (oneCurrentOf (U := U) hqp)
        (isPositive_oneCurrentOf hqp) (isClosedAny_oneCurrentOf hqp) hv).1.traceMeasure ≤
      recursiveMixedTraceMeasure U w hw := by
  subst hqp
  have e : w = Fin.append (fun _ : Fin q => ρ) v := funext fun i => (hwdef i).trans (by simp)
  subst e
  exact smul_traceMeasure_le_recursiveMixedTraceMeasure p q hv hc hρc hw

end SGPT.NPP.NonPluripolarCurrent
