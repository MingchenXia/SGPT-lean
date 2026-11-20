import SGPT.NPP.DN2KiselmanManifold
import SGPT.Okounkov.TranscendentalLiftingExtension
import SGPT.Foundations.Analysis.Pending.PshConvexCone
import SGPT.Foundations.Analysis.FirstPass.RooftopEnvelope

/-!
# The competitor argument of FPT `thm:big-metric-laplacian-rooftop`

Lane DN2, `thm:DNT23_C11bar`.  Both smoothing bounds of FPT `thm:big-metric-laplacian-rooftop`
end with the same argument: a function `Q`, `(κθ + eω)`-psh off the pole divisor `A` of a Kähler
current `θ + ddᶜφ ≥ ω` (`φ ≤ 0`) and lying below the obstacle `f ≥ 0`, is corrected by
`ν = e/(κ + e)`:

  `W = ((1 - ν) Q + ν κ φ)/κ`

is `θ`-psh off `A`, bounded above, below `f`; it extends across `A`
(`thetaPsh_extend_across_analytic`, the Grauert–Remmert type removable singularity theorem), the
extension stays below the continuous `f`, hence below the envelope `u = P_θ(f)` by maximality.

## Main results

* `thetaPshOff_combination`: positive combinations of potentials psh off `A`.
* `competitor_le_envelope`: `(1 - ν) Q + ν κ φ ≤ κ u` off `A`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric
open scoped Topology ContDiff

namespace SGPT.NPP.DN2

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending.ThetaPshCodimTwoExtension
open SGPT.Foundations.Analysis.Pending.PshAnalyticSetExtension

variable {N : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel N) Y]
  [IsComplexManifold N Y]

theorem plurisubharmonicOn_congr_of_isOpen {u w : ComplexModel N → EReal}
    {V : Set (ComplexModel N)} (hV : IsOpen V) (hu : PlurisubharmonicOn u V) (heq : EqOn u w V) :
    PlurisubharmonicOn w V := by
  intro x hx
  obtain ⟨U', hU', hxU', hdisc⟩ := hu x hx
  exact ⟨U' ∩ V, hU'.inter hV, ⟨hxU', hx⟩, (hdisc.mono inter_subset_left).congr
    fun y hy => heq hy.2⟩

/-- **Positive combinations of potentials psh off a closed set.** -/
theorem thetaPshOff_combination {θ₁ θ₂ θ : ClosedRealOneOneForm N Y} {A : Set Y}
    (hA : IsClosed A) {g₁ g₂ : Y → ℝ}
    (h₁ : ThetaPshOff θ₁.val A (fun y => (g₁ y : EReal)))
    (h₂ : ThetaPshOff θ₂.val A (fun y => (g₂ y : EReal))) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hθ : a • θ₁ + b • θ₂ = θ) :
    ThetaPshOff θ.val A (fun y => ((a * g₁ y + b * g₂ y : ℝ) : EReal)) := by
  intro e z hz hzA
  obtain ⟨W₁, ρ₁, hz₁, hp₁, hs₁⟩ := h₁ e z hz hzA
  obtain ⟨W₂, ρ₂, hz₂, hp₂, hs₂⟩ := h₂ e z hz hzA
  set V := W₁ ∩ W₂ ∩ (e.val.target ∩ e.val.symm ⁻¹' Aᶜ) with hV
  have hVopen : IsOpen V := (hp₁.1.inter hp₂.1).inter
    (e.val.continuousOn_symm.isOpen_inter_preimage e.val.open_target hA.isOpen_compl)
  have hzV : z ∈ V := ⟨⟨hz₁, hz₂⟩, hz, hzA⟩
  refine ⟨V, fun y => a * ρ₁ y + b * ρ₂ y, hzV, ⟨hVopen, fun y hy => hy.2.1,
    (contDiffOn_const.mul (hp₁.2.2.1.mono fun y hy => hy.1.1)).add
      (contDiffOn_const.mul (hp₂.2.2.1.mono fun y hy => hy.1.2)), fun y hy => ?_⟩, ?_⟩
  · have hs1 : ContDiffOn ℝ ∞ (fun y => a • ρ₁ y) V :=
      (hp₁.2.2.1.mono fun y hy => hy.1.1).const_smul a
    have hs2 : ContDiffOn ℝ ∞ (fun y => b • ρ₂ y) V :=
      (hp₂.2.2.1.mono fun y hy => hy.1.2).const_smul b
    have hsum := smoothDDC_add hVopen hs1 hs2 hy
    have hm1 := smoothDDC_smul hVopen (hp₁.2.2.1.mono fun y hy => hy.1.1) a hy
    have hm2 := smoothDDC_smul hVopen (hp₂.2.2.1.mono fun y hy => hy.1.2) b hy
    simp only [smul_eq_mul] at hsum hm1 hm2
    rw [hsum, hm1, hm2, hp₁.2.2.2 hy.1.1, hp₂.2.2.2 hy.1.2, ← hθ]
    simp [ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.coeff_smul]
  · have hc₁ := (hs₁.const_mul ha).mono (fun y (hy : y ∈ V) => hy.1.1)
    have hc₂ := (hs₂.const_mul hb).mono (fun y (hy : y ∈ V) => hy.1.2)
    refine plurisubharmonicOn_congr_of_isOpen hVopen (hc₁.add hc₂) fun y _ => ?_
    simp only [chartFunction]
    rw [← EReal.coe_add, ← EReal.coe_add, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add,
      ← EReal.coe_add]
    congr 1
    ring

/-- A `θ`-psh potential which is finite off `A`, read as a real function, is `θ`-psh off `A`. -/
theorem thetaPshOff_toReal {θ : ClosedRealOneOneForm N Y} {A : Set Y} (hA : IsClosed A)
    {φ : Y → EReal} (hφ : ThetaPlurisubharmonic θ.val φ) (hφA : ∀ y ∉ A, φ y ≠ ⊥) :
    ThetaPshOff θ.val A (fun y => (((φ y).toReal : ℝ) : EReal)) := by
  intro e z hz hzA
  obtain ⟨W, ρ, hzW, hp, hs⟩ := hφ e z hz
  set V := W ∩ (e.val.target ∩ e.val.symm ⁻¹' Aᶜ)
  have hVopen : IsOpen V := hp.1.inter
    (e.val.continuousOn_symm.isOpen_inter_preimage e.val.open_target hA.isOpen_compl)
  refine ⟨V, ρ, ⟨hzW, hz, hzA⟩, hp.mono hVopen fun y hy => hy.1, ?_⟩
  refine plurisubharmonicOn_congr_of_isOpen hVopen (fun y hy => hs y hy.1) fun y hy => ?_
  simp only [chartFunction]
  rw [EReal.coe_toReal (hφ.quasiPlurisubharmonic.ne_top _) (hφA _ hy.2.2)]

variable [CompactSpace Y]

/-- **The competitor argument** (FPT `thm:big-metric-laplacian-rooftop`, both smoothing bounds).
Let `θ + ddᶜφ ≥ ω` with `φ ≤ 0` finite off the analytic set `A` (empty interior), `f ≥ 0`
continuous, `κ ≥ 1`, `e > 0`, and `Q` be `(κθ + eω)`-psh off `A` with `Q ≤ f` off `A`.  Then off
`A`, with `ν = e/(κ + e)`: `((1 - ν) Q + ν κ φ)/κ ≤ P_θ(f)`. -/
theorem competitor_le_envelope (wY : KahlerBackground N Y) {θ : ClosedRealOneOneForm N Y}
    {f : Y → ℝ} (hf : Continuous f) (hf0 : ∀ y, 0 ≤ f y) {φ : Y → EReal}
    (hφ : ThetaPlurisubharmonic (θ - wY.form).val φ) (hφ0 : ∀ y, φ y ≤ 0) {A : Set Y}
    (hA : IsComplexAnalyticSubset (n := N) A) (hAi : interior A = ∅) (hφA : ∀ y ∉ A, φ y ≠ ⊥)
    {κ e : ℝ} (hκ : 1 ≤ κ) (he : 0 < e) {Q : Y → ℝ}
    (hQ : ThetaPshOff (κ • θ + e • wY.form).val A (fun y => (Q y : EReal)))
    (hQf : ∀ y ∉ A, Q y ≤ f y) :
    ∀ y ∉ A, ((((1 - e / (κ + e)) / κ) * Q y + (e / (κ + e)) * (φ y).toReal : ℝ) : EReal) ≤
      rooftopEnvelope θ.val (fun y => (f y : EReal)) y := by
  classical
  have hAc : IsClosed A := hA.isClosed
  have hκ0 : 0 < κ := by linarith
  have hke : 0 < κ + e := by linarith
  set ν := e / (κ + e) with hν
  have hν0 : 0 < ν := div_pos he hke
  have hν1 : ν < 1 := (div_lt_one hke).mpr (by linarith)
  have ha : 0 < (1 - ν) / κ := div_pos (by linarith) hκ0
  set W : Y → ℝ := fun y => (1 - ν) / κ * Q y + ν * (φ y).toReal with hW
  -- `W` is `θ`-psh off `A`
  have hφoff := thetaPshOff_toReal hAc hφ hφA
  have hform : ((1 - ν) / κ) • (κ • θ + e • wY.form) + ν • (θ - wY.form) = θ := by
    have h1 : (1 - ν) * e = ν * κ := by
      rw [hν]; field_simp; ring
    have h2 : (1 - ν) / κ * κ + ν = 1 := by field_simp; ring
    have h3 : (1 - ν) / κ * e - ν = 0 := by
      rw [div_mul_eq_mul_div, h1]; field_simp; ring
    rw [smul_add, smul_smul, smul_smul, smul_sub, sub_eq_add_neg]
    calc ((1 - ν) / κ * κ) • θ + ((1 - ν) / κ * e) • wY.form + (ν • θ + -(ν • wY.form))
        = ((1 - ν) / κ * κ + ν) • θ + ((1 - ν) / κ * e - ν) • wY.form := by
          rw [add_smul, sub_smul]; abel
      _ = θ := by rw [h2, h3, one_smul, zero_smul, add_zero]
  have hWoff : ThetaPshOff θ.val A (fun y => (W y : EReal)) :=
    thetaPshOff_combination hAc hQ hφoff ha hν0 hform
  -- bounds
  obtain ⟨B, hB⟩ : ∃ B, ∀ y, f y ≤ B := by
    obtain ⟨B, hB⟩ := (isCompact_univ.image hf).isBounded.bddAbove
    exact ⟨B, fun y => hB ⟨y, mem_univ _, rfl⟩⟩
  have hWf : ∀ y ∉ A, W y ≤ f y := by
    intro y hy
    have h1 := hQf y hy
    have h2 : (φ y).toReal ≤ 0 := EReal.toReal_nonpos (hφ0 y)
    have h3 : (1 - ν) / κ ≤ 1 := by
      rw [div_le_one hκ0]; linarith
    have h4 := hf0 y
    simp only [hW]
    nlinarith
  have hbdd : SGPT.Foundations.Analysis.Pending.PshAnalyticSetExtension.LocallyBoundedAboveOff A (fun y => (W y : EReal)) :=
    fun x => ⟨univ, univ_mem, B, fun y _ hy => EReal.coe_le_coe_iff.mpr ((hWf y hy).trans (hB y))⟩
  obtain ⟨hext, hoffeq, -⟩ :=
    SGPT.Okounkov.TranscendentalLifting.thetaPsh_extend_across_analytic θ hA hAi hWoff hbdd
  set V := extensionAcross A (fun y => (W y : EReal)) with hVdef
  -- the extension stays below `f`
  have hVf : ∀ y, V y ≤ (f y : EReal) := by
    have hle : (fun y => if y ∈ A then (⊥ : EReal) else (W y : EReal)) ≤ fun y => (f y : EReal) := by
      intro y
      by_cases hy : y ∈ A
      · simp only [if_pos hy]; exact bot_le
      · simp only [if_neg hy]; exact EReal.coe_le_coe_iff.mpr (hWf y hy)
    have := uscRegularization_le (continuous_coe_real_ereal.comp hf).upperSemicontinuous hle
    intro y; exact this y
  -- it is a genuine potential
  have hVpot : IsThetaPshPotential θ.val V := by
    refine ⟨hext, fun x U hU hxU => ?_⟩
    by_contra hcon
    push Not at hcon
    have hsub : U ⊆ A := by
      intro y hy
      by_contra hyA
      exact (EReal.coe_ne_bot (W y)) ((hoffeq y hyA).symm.trans (hcon y hy))
    have : x ∈ interior A := interior_mono hsub (by rw [hU.interior_eq]; exact hxU)
    rw [hAi] at this
    exact this
  have hle := le_rooftopEnvelope hVpot (quasiEverywhere_of_forall (n := N) hVf)
  intro y hy
  have := hle y
  rw [hoffeq y hy] at this
  exact this

end SGPT.NPP.DN2
