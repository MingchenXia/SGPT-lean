import SGPT.Foundations.Analysis.Pending.ActualLocalMixedCapacityContinuity

set_option autoImplicit false

/-! # Actual finite-box local mixed weak continuity

Normalization, genuine constant gauge invariance and positive homogeneity
produce the original local canonical integral limits. The natural finite
box is only on the actual coordinate domain, not on global potentials.
-/

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.ActualLocalBoundedMixedCapacityContinuity

open FirstPass FirstPass.PositiveClasses FirstPass.MongeAmpere
  FirstPass.MixedMongeAmpere BedfordTaylor MixedMongeAmpere

noncomputable section

variable {n : ℕ}

private theorem normalized_integral {D : Opens (ComplexModel n)}
    {u : Fin n → ComplexModel n → ℝ} (hu : IsLocallyBoundedMixedPshOn D u)
    {c B : ℝ} (hc : 0 < c)
    (hN : IsLocallyBoundedMixedPshOn D (fun i z => c * (u i z - B)))
    (h : ComplexModel n → ℝ) :
    (∫ z, h z ∂canonicalMixedBedfordTaylorMeasure D (fun i z => c * (u i z - B)) hN) =
      c ^ n * ∫ z, h z ∂canonicalMixedBedfordTaylorMeasure D u hu := by
  have hlim : IsBTLimit D u (canonicalMixedBedfordTaylorMeasure D u hu) :=
    IsLocalMixedBedfordTaylorMeasure.isBTLimit (canonicalMixedBedfordTaylorMeasure_spec D u hu)
  have hconst : ∀ i : Fin n, IsSmoothPluriharmonicOn D (fun _ : ComplexModel n => -B) :=
    fun _ => ⟨contDiffOn_const, fun z _ => complexHessian_const (-B) z⟩
  have hshift := hlim.add_pluriharmonic hconst
  have hscaled := (hshift.const_mul_all hc.le).congr
    (fun i z _ => by change c * (u i z + -B) = c * (u i z - B); ring)
  have hμ : canonicalMixedBedfordTaylorMeasure D (fun i z => c * (u i z - B)) hN =
      (ENNReal.ofReal c ^ n) • canonicalMixedBedfordTaylorMeasure D u hu :=
    (IsLocalMixedBedfordTaylorMeasure.isBTLimit
      (canonicalMixedBedfordTaylorMeasure_spec D (fun i z => c * (u i z - B)) hN)).unique hscaled
  rw [hμ, integral_smul_measure, ENNReal.toReal_pow, ENNReal.toReal_ofReal hc.le, smul_eq_mul]

variable {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

/-- Natural finite bounds on the actual local domain suffice for genuine
canonical mixed weak continuity against all continuous compact tests. -/
theorem tendsto_integral_of_relative_capacity (omega : KahlerBackground n M)
    (e : ComplexChart n M) {D : Opens (ComplexModel n)}
    (hDt : (D : Set (ComplexModel n)) ⊆ e.val.target)
    {ρ : ComplexModel n → ℝ} (hρ : IsSmoothLocalPotential omega.form.val e D ρ)
    {K : Set (ComplexModel n)} (hK : IsCompact K) (hKD : K ⊆ D)
    {u : ℕ → Fin n → ComplexModel n → ℝ} {v : Fin n → ComplexModel n → ℝ}
    (hu : ∀ j, IsLocallyBoundedMixedPshOn D (u j))
    (hv : IsLocallyBoundedMixedPshOn D v) {B : ℝ} (hB : 0 ≤ B)
    (huB : ∀ j i z, z ∈ D → -B ≤ u j i z ∧ u j i z ≤ B)
    (hvB : ∀ i z, z ∈ D → -B ≤ v i z ∧ v i z ≤ B)
    (hcap : ∀ i (V : Opens (ComplexModel n)), V ≤ D → ∀ T : Set (ComplexModel n),
      IsCompact T → T ⊆ V → ∀ a : ℝ, 0 < a →
      Tendsto (fun j => relCapacity V {z | z ∈ T ∧ a < |u j i z - v i z|})
        atTop (𝓝 0))
    {h : ComplexModel n → ℝ} (hc : Continuous h) (hk : HasCompactSupport h)
    (ht : tsupport h ⊆ K) :
    Tendsto (fun j => ∫ z, h z ∂canonicalMixedBedfordTaylorMeasure D (u j) (hu j))
      atTop (𝓝 (∫ z, h z ∂canonicalMixedBedfordTaylorMeasure D v hv)) := by
  let c : ℝ := (2 * (B + 1))⁻¹
  have hden : 0 < 2 * (B + 1) := by positivity
  have hcpos : 0 < c := inv_pos.mpr hden
  have hceq : c * (2 * (B + 1)) = 1 := inv_mul_cancel₀ hden.ne'
  let norm (a : Fin n → ComplexModel n → ℝ) : Fin n → ComplexModel n → ℝ :=
    fun i z => c * (a i z - B)
  have hbox (a : Fin n → ComplexModel n → ℝ)
      (ha : ∀ i z, z ∈ D → -B ≤ a i z ∧ a i z ≤ B) :
      ∀ i z, z ∈ D → -1 ≤ norm a i z ∧ norm a i z ≤ 0 := by
    intro i z hz
    obtain ⟨hl, hr⟩ := ha i z hz
    constructor
    · calc
        (-1 : ℝ) = c * (-(2 * (B + 1))) := by nlinarith [hceq]
        _ ≤ norm a i z := mul_le_mul_of_nonneg_left (by linarith) hcpos.le
    · exact mul_nonpos_of_nonneg_of_nonpos hcpos.le (by linarith)
  have hpsh (a : Fin n → ComplexModel n → ℝ) (ha : IsLocallyBoundedMixedPshOn D a)
      (haB : ∀ i z, z ∈ D → -B ≤ a i z ∧ a i z ≤ B) :
      IsLocallyBoundedMixedPshOn D (norm a) := by
    intro i
    have hshift : PlurisubharmonicOn (fun z => ((a i z - B : ℝ) : EReal))
        (D : Set (ComplexModel n)) := by
      simpa only [sub_eq_add_neg, EReal.coe_add, EReal.coe_neg] using (ha i).1.add_const (-B)
    exact isLocallyBoundedPshOn_of_abs_le (plurisubharmonicOn_coe_const_mul hshift hcpos)
      (C := 1) (fun z hz => abs_le.mpr ⟨(hbox a haB i z hz).1,
        (hbox a haB i z hz).2.trans zero_le_one⟩)
  let hNu : ∀ j, IsLocallyBoundedMixedPshOn D (norm (u j)) :=
    fun j => hpsh (u j) (hu j) (huB j)
  let hNv : IsLocallyBoundedMixedPshOn D (norm v) := hpsh v hv hvB
  have hcapN : ∀ i (V : Opens (ComplexModel n)), V ≤ D → ∀ T : Set (ComplexModel n),
      IsCompact T → T ⊆ V → ∀ a : ℝ, 0 < a → Tendsto
      (fun j => relCapacity V {z | z ∈ T ∧ a < |norm (u j) i z - norm v i z|}) atTop (𝓝 0) := by
    intro i V hVD T hT hTV a ha
    have heq (j : ℕ) : {z | z ∈ T ∧ a < |norm (u j) i z - norm v i z|} =
        {z | z ∈ T ∧ a / c < |u j i z - v i z|} := by
      ext z
      change (z ∈ T ∧ a < |norm (u j) i z - norm v i z|) ↔
        (z ∈ T ∧ a / c < |u j i z - v i z|)
      rw [show norm (u j) i z - norm v i z = c * (u j i z - v i z) by dsimp [norm]; ring,
        abs_mul, abs_of_pos hcpos]
      simp only [div_lt_iff₀ hcpos, mul_comm c]
    exact (hcap i V hVD T hT hTV (a / c) (div_pos ha hcpos)).congr
      (fun j => congrArg (relCapacity V) (heq j).symm)
  have hl := ActualLocalMixedCapacityContinuity.tendsto_integral_of_relative_capacity
    omega e hDt hρ hK hKD hNu hNv (fun j => hbox (u j) (huB j)) (hbox v hvB)
      hcapN hc hk ht
  have hIu (j : ℕ) :
      (∫ z, h z ∂canonicalMixedBedfordTaylorMeasure D (norm (u j)) (hNu j)) =
        c ^ n * ∫ z, h z ∂canonicalMixedBedfordTaylorMeasure D (u j) (hu j) :=
    normalized_integral (hu j) hcpos (hNu j) h
  have hIv : (∫ z, h z ∂canonicalMixedBedfordTaylorMeasure D (norm v) hNv) =
      c ^ n * ∫ z, h z ∂canonicalMixedBedfordTaylorMeasure D v hv :=
    normalized_integral hv hcpos hNv h
  have hh := hl.div_const (c ^ n)
  simpa only [hIu, hIv, mul_div_cancel_left₀ _ (pow_ne_zero n hcpos.ne')] using hh

end
end SGPT.Foundations.Analysis.Pending.ActualLocalBoundedMixedCapacityContinuity
