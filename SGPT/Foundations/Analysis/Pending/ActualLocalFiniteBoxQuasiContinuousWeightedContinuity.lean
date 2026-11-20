import SGPT.Foundations.Analysis.Pending.ActualLocalQuasiContinuousCutoffWeightedContinuity

set_option autoImplicit false

/-! # Actual finite-box local cutoff continuity with Borel QC multipliers

Actual normalization of both mixed slots and independent cutoff seeds,
Lipschitz inverse reconstruction, canonical constant-gauge invariance and
positive homogeneity produce the original weighted local integrals.
Finite bounds are only on the actual coordinate domain.
-/

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.ActualLocalFiniteBoxQuasiContinuousWeightedContinuity

open FirstPass FirstPass.PositiveClasses FirstPass.MongeAmpere
  FirstPass.MixedMongeAmpere BedfordTaylor MixedMongeAmpere
  ThetaCapacity CapacityWeightedConvergence

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

private theorem lipschitz_reconstruct {m : ℕ} {δ : ℝ} (hδ : 0 < δ) (B : ℝ) :
    LipschitzWith ⟨δ⁻¹, inv_nonneg.mpr hδ.le⟩
      (fun y : Fin m → ℝ => fun i => δ⁻¹ * y i + B) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  apply (dist_pi_le_iff (mul_nonneg (inv_nonneg.mpr hδ.le) dist_nonneg)).mpr
  intro i
  change |(δ⁻¹ * x i + B) - (δ⁻¹ * y i + B)| ≤ δ⁻¹ * dist x y
  have heq : (δ⁻¹ * x i + B) - (δ⁻¹ * y i + B) = δ⁻¹ * (x i - y i) := by ring
  rw [heq, abs_mul, abs_of_pos (inv_pos.mpr hδ)]
  exact mul_le_mul_of_nonneg_left (by simpa only [Real.dist_eq] using dist_le_pi_dist x y i)
    (inv_nonneg.mpr hδ.le)

variable {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

/-- Natural finite local bounds and genuine capacity convergence of mixed
slots and independent cutoff seeds produce their actual weighted integral limit. -/
theorem tendsto_integral_quasiContinuous_classifier_of_relative_capacity (omega : KahlerBackground n M)
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
    {m : ℕ} {w : ℕ → Fin m → ComplexModel n → ℝ}
    {z : Fin m → ComplexModel n → ℝ}
    (hw : ∀ j i, IsLocallyBoundedPshOn D (w j i))
    (hz : ∀ i, IsLocallyBoundedPshOn D (z i))
    (hwB : ∀ j i y, y ∈ D → -B ≤ w j i y ∧ w j i y ≤ B)
    (hzB : ∀ i y, y ∈ D → -B ≤ z i y ∧ z i y ≤ B)
    (hseedcap : ∀ i (V : Opens (ComplexModel n)), V ≤ D → ∀ T : Set (ComplexModel n),
      IsCompact T → T ⊆ V → ∀ a : ℝ, 0 < a →
      Tendsto (fun j => relCapacity V {y | y ∈ T ∧ a < |w j i y - z i y|})
        atTop (𝓝 0))
    {Φ : (Fin m → ℝ) → ℝ} {L : NNReal} (hΦ : LipschitzWith L Φ)
    {χ : M → ℝ} {C : ℝ} (hC : 0 ≤ C) (hχC : ∀ x, |χ x| ≤ C)
    (hχm : Measurable χ)
    (hχ : QuasiContinuousFor (thetaCapacity omega.form (fun _ => 0)) χ)
    {h : ComplexModel n → ℝ} (hc : Continuous h) (hk : HasCompactSupport h)
    (ht : tsupport h ⊆ K) :
    Tendsto (fun j => ∫ y, χ (e.val.symm y) * h y * Φ (fun i => w j i y)
      ∂canonicalMixedBedfordTaylorMeasure D (u j) (hu j))
      atTop (𝓝 (∫ y, χ (e.val.symm y) * h y * Φ (fun i => z i y) ∂canonicalMixedBedfordTaylorMeasure D v hv)) := by
  let c : ℝ := (2 * (B + 1))⁻¹
  have hden : 0 < 2 * (B + 1) := by positivity
  have hcpos : 0 < c := inv_pos.mpr hden
  have hceq : c * (2 * (B + 1)) = 1 := inv_mul_cancel₀ hden.ne'
  let norm (d : ℕ) (a : Fin d → ComplexModel n → ℝ) : Fin d → ComplexModel n → ℝ :=
    fun i z => c * (a i z - B)
  have hbox (d : ℕ) (a : Fin d → ComplexModel n → ℝ)
      (ha : ∀ i z, z ∈ D → -B ≤ a i z ∧ a i z ≤ B) :
      ∀ i z, z ∈ D → -1 ≤ norm d a i z ∧ norm d a i z ≤ 0 := by
    intro i z hz
    obtain ⟨hl, hr⟩ := ha i z hz
    constructor
    · calc
        (-1 : ℝ) = c * (-(2 * (B + 1))) := by nlinarith [hceq]
        _ ≤ norm d a i z := mul_le_mul_of_nonneg_left (by linarith) hcpos.le
    · exact mul_nonpos_of_nonneg_of_nonpos hcpos.le (by linarith)
  have hpsh (d : ℕ) (a : Fin d → ComplexModel n → ℝ) (ha : ∀ i, IsLocallyBoundedPshOn D (a i))
      (haB : ∀ i z, z ∈ D → -B ≤ a i z ∧ a i z ≤ B) :
      ∀ i, IsLocallyBoundedPshOn D (norm d a i) := by
    intro i
    have hshift : PlurisubharmonicOn (fun z => ((a i z - B : ℝ) : EReal))
        (D : Set (ComplexModel n)) := by
      simpa only [sub_eq_add_neg, EReal.coe_add, EReal.coe_neg] using (ha i).1.add_const (-B)
    exact isLocallyBoundedPshOn_of_abs_le (plurisubharmonicOn_coe_const_mul hshift hcpos)
      (C := 1) (fun z hz => abs_le.mpr ⟨(hbox d a haB i z hz).1,
        (hbox d a haB i z hz).2.trans zero_le_one⟩)
  let hNu : ∀ j, IsLocallyBoundedMixedPshOn D (norm n (u j)) :=
    fun j => hpsh n (u j) (hu j) (huB j)
  let hNv : IsLocallyBoundedMixedPshOn D (norm n v) := hpsh n v hv hvB
  have hnormalizeCap (d : ℕ) {f : ℕ → Fin d → ComplexModel n → ℝ}
      {g : Fin d → ComplexModel n → ℝ}
      (horig : ∀ i (V : Opens (ComplexModel n)), V ≤ D → ∀ T : Set (ComplexModel n),
        IsCompact T → T ⊆ V → ∀ a : ℝ, 0 < a → Tendsto
        (fun j => relCapacity V {y | y ∈ T ∧ a < |f j i y - g i y|}) atTop (𝓝 0)) :
      ∀ i (V : Opens (ComplexModel n)), V ≤ D → ∀ T : Set (ComplexModel n),
        IsCompact T → T ⊆ V → ∀ a : ℝ, 0 < a → Tendsto
        (fun j => relCapacity V {y | y ∈ T ∧ a < |norm d (f j) i y - norm d g i y|})
          atTop (𝓝 0) := by
    intro i V hVD T hT hTV a ha
    have heq (j : ℕ) : {y | y ∈ T ∧ a < |norm d (f j) i y - norm d g i y|} =
        {y | y ∈ T ∧ a / c < |f j i y - g i y|} := by
      ext y
      change (y ∈ T ∧ a < |norm d (f j) i y - norm d g i y|) ↔
        (y ∈ T ∧ a / c < |f j i y - g i y|)
      rw [show norm d (f j) i y - norm d g i y = c * (f j i y - g i y) by
        dsimp [norm]; ring, abs_mul, abs_of_pos hcpos]
      simp only [div_lt_iff₀ hcpos, mul_comm c]
    exact (horig i V hVD T hT hTV (a / c) (div_pos ha hcpos)).congr
      (fun j => congrArg (relCapacity V) (heq j).symm)
  let hNw : ∀ j i, IsLocallyBoundedPshOn D (norm m (w j) i) :=
    fun j => hpsh m (w j) (hw j) (hwB j)
  let hNz : ∀ i, IsLocallyBoundedPshOn D (norm m z i) := hpsh m z hz hzB
  let Ψ : (Fin m → ℝ) → ℝ := fun y => Φ (fun i => c⁻¹ * y i + B)
  have hΨ : LipschitzWith (L * ⟨c⁻¹, inv_nonneg.mpr hcpos.le⟩) Ψ :=
    hΦ.comp (lipschitz_reconstruct hcpos B)
  have hrec (a : Fin m → ComplexModel n → ℝ) (y : ComplexModel n) :
      Ψ (fun i => norm m a i y) = Φ (fun i => a i y) := by
    apply congrArg Φ
    funext i
    dsimp [norm]
    field_simp [hcpos.ne']
    ring
  have hl := ActualLocalQuasiContinuousCutoffWeightedContinuity.tendsto_integral_quasiContinuous_classifier_of_relative_capacity
    omega e hDt hρ hK hKD hNu hNv (fun j => hbox n (u j) (huB j)) (hbox n v hvB)
      (hnormalizeCap n hcap) hNw hNz (fun j => hbox m (w j) (hwB j)) (hbox m z hzB)
      (hnormalizeCap m hseedcap) hΨ hC hχC hχm hχ hc hk ht
  have hlim := hl.2.2
  simp only [hrec] at hlim
  have hIu (j : ℕ) :
      (∫ y, χ (e.val.symm y) * h y * Φ (fun i => w j i y) ∂canonicalMixedBedfordTaylorMeasure D (norm n (u j)) (hNu j)) =
        c ^ n * ∫ y, χ (e.val.symm y) * h y * Φ (fun i => w j i y) ∂canonicalMixedBedfordTaylorMeasure D (u j) (hu j) :=
    normalized_integral (hu j) hcpos (hNu j) (fun y => χ (e.val.symm y) * h y * Φ (fun i => w j i y))
  have hIv : (∫ y, χ (e.val.symm y) * h y * Φ (fun i => z i y) ∂canonicalMixedBedfordTaylorMeasure D (norm n v) hNv) =
      c ^ n * ∫ y, χ (e.val.symm y) * h y * Φ (fun i => z i y) ∂canonicalMixedBedfordTaylorMeasure D v hv :=
    normalized_integral hv hcpos hNv (fun y => χ (e.val.symm y) * h y * Φ (fun i => z i y))
  have hh := hlim.div_const (c ^ n)
  simpa only [hIu, hIv, mul_div_cancel_left₀ _ (pow_ne_zero n hcpos.ne')] using hh

end
end SGPT.Foundations.Analysis.Pending.ActualLocalFiniteBoxQuasiContinuousWeightedContinuity
