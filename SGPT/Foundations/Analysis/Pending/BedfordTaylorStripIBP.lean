import SGPT.Foundations.Analysis.Pending.BedfordTaylorDefectPairing
import SGPT.Foundations.Analysis.Pending.BedfordTaylorTimeSlot
import SGPT.Foundations.Analysis.Pending.BedfordTaylorStripCovariance

set_option autoImplicit false

/-!
# Integration by parts for the homogeneous complex Monge--Ampère equation, through defect pairings

For a tuple `v` on `Ω ⊆ ℂᴺ`, a slot `i₀`, a function `G` and a bounded compactly supported weight
`F`, `defectPairing Ω v i₀ G F` is the value of the pairing `∫ F d(ddᶜG ∧ T)` of
`BedfordTaylorDefectPairing` (`0` when there is none).

* Calculus of pairing values: `defectPairing_eq`, `isDefectPairing_defectPairing`,
  `IsDefectPairing.mono`, `IsDefectPairing.restrict`, `IsDefectPairing.congr` (only the values on
  `Ω` matter), `IsDefectPairing.congr_weight'` (only the weight near `supp G ∩ Ω` matters),
  `defectPairing_add`, `defectPairing_sum`, `defectPairing_add_weight`, `defectPairing_sum_weight`.
* `isDefectPairing_timeLift` — **the time slot as a pairing**: on `Ω ⊆ ℂⁿ⁺¹`, for `ψ̂(z, τ) = ψ(τ)`,
  the pairing of `χ (w₁ - w₂)` with `ddᶜψ̂ ∧ T` is `∫ χ (Δψ/4)(τ) (w₁ - w₂) dBT(T, |τ|²)`.
* `sum_defectPairing_endpointTuple_eq_zero` — **the local integration by parts**: if `h` and `Φ` are
  locally bounded plurisubharmonic on `Ω ⊆ ℂⁿ⁺¹` with `(ddᶜh)ⁿ⁺¹ = (ddᶜΦ)ⁿ⁺¹ = 0`, then for every
  test function `g` and every weight `F` equal to `h - Φ` near `supp g`,

    `Σ_{j=0}^{n} ∫ F d(ddᶜg ∧ (ddᶜh)ʲ ∧ (ddᶜΦ)ⁿ⁻ʲ) = 0`.

  Each term is `∫ g d(ddᶜh)ʲ⁺¹ ∧ (ddᶜΦ)ⁿ⁻ʲ - ∫ g d(ddᶜh)ʲ ∧ (ddᶜΦ)ⁿ⁺¹⁻ʲ`
  (`exists_integral_sub_eq_slotDefect_last` and a slot permutation), and the sum telescopes.

This is the local content of `ddᶜ_τ E(U_τ) = π_*((ddᶜU)ⁿ⁺¹ - (ddᶜφ)ⁿ⁺¹) = 0` along a geodesic
(Xia, SGPT, proof of Proposition 4.3.3, `xia-sgpt:page-0171`).
-/

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ContDiff ComplexOrder

namespace SGPT.Foundations.Analysis.Pending.BedfordTaylorStripIBP

open FirstPass FirstPass.MongeAmpere FirstPass.MixedMongeAmpere BedfordTaylor
  BedfordTaylorDefectPairing BedfordTaylorTimeSlot MixedDensityRankOneSlot BedfordTaylorFibreSlicing
  BedfordTaylorStripCovariance

noncomputable section

/-! ### Pairing values -/

section Pairing

variable {N : ℕ} {Ω : Opens (ComplexModel N)} {v : Fin N → ComplexModel N → ℝ} {i₀ : Fin N}
  {G F : ComplexModel N → ℝ} {I : ℝ}

open Classical in
/-- The value of the pairing `∫ F d(ddᶜG ∧ T)` (`0` when there is none). -/
def defectPairing (Ω : Opens (ComplexModel N)) (v : Fin N → ComplexModel N → ℝ) (i₀ : Fin N)
    (G F : ComplexModel N → ℝ) : ℝ :=
  if h : ∃ I, IsDefectPairing Ω v i₀ G F I then h.choose else 0

theorem defectPairing_eq (hF : IsBoundedTest F) (h : IsDefectPairing Ω v i₀ G F I) :
    defectPairing Ω v i₀ G F = I := by
  have hex : ∃ I, IsDefectPairing Ω v i₀ G F I := ⟨I, h⟩
  unfold defectPairing
  rw [dif_pos hex]
  exact IsDefectPairing.unique hF hex.choose_spec h

theorem isDefectPairing_defectPairing (hv : SlotsAdmissible Ω v i₀) (hG : ContDiffOn ℝ ∞ G Ω)
    (hF : IsBoundedTest F) (hFΩ : tsupport F ⊆ Ω) :
    IsDefectPairing Ω v i₀ G F (defectPairing Ω v i₀ G F) := by
  obtain ⟨I, hI⟩ := exists_isDefectPairing hv hG hF hFΩ
  rwa [defectPairing_eq hF hI]

theorem IsDefectPairing.mono {Ω' : Opens (ComplexModel N)} (hΩ : Ω ≤ Ω')
    (h : IsDefectPairing Ω v i₀ G F I) : IsDefectPairing Ω' v i₀ G F I := by
  obtain ⟨V, p, ν₁, ν₂, hVΩ, hFV, h₁, h₂, rfl⟩ := h
  exact ⟨V, p, ν₁, ν₂, hVΩ.trans hΩ, hFV, h₁, h₂, rfl⟩

theorem IsDefectPairing.restrict {Ω' : Opens (ComplexModel N)} (hFΩ' : tsupport F ⊆ Ω') (h : IsDefectPairing Ω v i₀ G F I) :
    IsDefectPairing Ω' v i₀ G F I := by
  obtain ⟨V, p, ν₁, ν₂, -, hFV, h₁, h₂, rfl⟩ := h
  have hW : tsupport F ⊆ (V ⊓ Ω' : Opens (ComplexModel N)) := fun z hz => ⟨hFV hz, hFΩ' hz⟩
  refine ⟨V ⊓ Ω', p, _, _, inf_le_right, hW, h₁.restrict_opens inf_le_left,
    h₂.restrict_opens inf_le_left, ?_⟩
  rw [integral_restrict_of_tsupport hW, integral_restrict_of_tsupport hW]

/-- Only the values of the slots and of `G` on `Ω` matter. -/
theorem IsDefectPairing.congr {v' : Fin N → ComplexModel N → ℝ} {G' : ComplexModel N → ℝ}
    (hv : ∀ i, i ≠ i₀ → EqOn (v i) (v' i) Ω) (hG : EqOn G G' Ω)
    (h : IsDefectPairing Ω v i₀ G F I) : IsDefectPairing Ω v' i₀ G' F I := by
  classical
  obtain ⟨V, p, ν₁, ν₂, hVΩ, hFV, h₁, h₂, rfl⟩ := h
  refine ⟨V, p, ν₁, ν₂, hVΩ, hFV, h₁.congr fun i => ?_, h₂.congr fun i => ?_, rfl⟩
  · by_cases hi : i = i₀
    · subst hi
      intro z hz
      simp only [Function.update_self]
      rw [hG (hVΩ hz)]
    · simp only [Function.update_of_ne hi]
      exact (hv i hi).mono hVΩ
  · by_cases hi : i = i₀
    · subst hi
      intro z _
      simp only [Function.update_self]
    · simp only [Function.update_of_ne hi]
      exact (hv i hi).mono hVΩ

/-- **Locality in the weight**, only near `supp G ∩ Ω`. -/
theorem IsDefectPairing.congr_weight' (hv : SlotsAdmissible Ω v i₀) (hG : ContDiffOn ℝ ∞ G Ω)
    {F' : ComplexModel N → ℝ} {I' : ℝ} (hF : IsBoundedTest F) (hF' : IsBoundedTest F')
    (hFΩ : tsupport F ⊆ Ω) (hF'Ω : tsupport F' ⊆ Ω) {O : Set (ComplexModel N)} (hO : IsOpen O)
    (hGO : ∀ z ∈ Ω, z ∈ tsupport G → z ∈ O) (hFF' : EqOn F F' O)
    (h : IsDefectPairing Ω v i₀ G F I) (h' : IsDefectPairing Ω v i₀ G F' I') : I = I' := by
  have hK : IsCompact (tsupport F ∪ tsupport F') := hF.2.1.union hF'.2.1
  refine IsDefectPairing.congr_weight hv hG hF hF' hFΩ hF'Ω
    (O := O ∪ (tsupport F ∪ tsupport F')ᶜ) (hO.union hK.isClosed.isOpen_compl) ?_ ?_ h h'
  · intro z hz
    by_cases hzK : z ∈ tsupport F ∪ tsupport F'
    · exact Or.inl (hGO z (hzK.elim (fun h => hFΩ h) fun h => hF'Ω h) hz)
    · exact Or.inr hzK
  · rintro z (hz | hz)
    · exact hFF' hz
    · rw [image_eq_zero_of_notMem_tsupport fun h => hz (Or.inl h),
        image_eq_zero_of_notMem_tsupport fun h => hz (Or.inr h)]

theorem defectPairing_add (hv : SlotsAdmissible Ω v i₀) {G₁ G₂ : ComplexModel N → ℝ}
    (hG₁ : ContDiffOn ℝ ∞ G₁ Ω) (hG₂ : ContDiffOn ℝ ∞ G₂ Ω) (hF : IsBoundedTest F)
    (hFΩ : tsupport F ⊆ Ω) :
    defectPairing Ω v i₀ (fun z => G₁ z + G₂ z) F =
      defectPairing Ω v i₀ G₁ F + defectPairing Ω v i₀ G₂ F :=
  defectPairing_eq hF ((isDefectPairing_defectPairing hv hG₁ hF hFΩ).add hF
    (isDefectPairing_defectPairing hv hG₂ hF hFΩ))

theorem defectPairing_sum (hv : SlotsAdmissible Ω v i₀) {ι : Type*} (s : Finset ι)
    {G : ι → ComplexModel N → ℝ} (hG : ∀ b ∈ s, ContDiffOn ℝ ∞ (G b) Ω) (hF : IsBoundedTest F)
    (hFΩ : tsupport F ⊆ Ω) :
    defectPairing Ω v i₀ (fun z => ∑ b ∈ s, G b z) F = ∑ b ∈ s, defectPairing Ω v i₀ (G b) F := by
  obtain ⟨V, p, ν₁, ν₂, hVΩ, hFV, -, h₂⟩ :=
    exists_witness hv (G := fun _ => 0) contDiffOn_const hF.2.1 hFΩ
  exact defectPairing_eq hF (IsDefectPairing.sum hF hVΩ hFV h₂ s G _
    fun b hb => isDefectPairing_defectPairing hv (hG b hb) hF hFΩ)

theorem defectPairing_add_weight (hv : SlotsAdmissible Ω v i₀) (hG : ContDiffOn ℝ ∞ G Ω)
    {F₁ F₂ : ComplexModel N → ℝ} (hF₁ : IsBoundedTest F₁) (hF₂ : IsBoundedTest F₂)
    (hF₁Ω : tsupport F₁ ⊆ Ω) (hF₂Ω : tsupport F₂ ⊆ Ω) :
    defectPairing Ω v i₀ G (fun z => F₁ z + F₂ z) =
      defectPairing Ω v i₀ G F₁ + defectPairing Ω v i₀ G F₂ :=
  defectPairing_eq (hF₁.add hF₂) (IsDefectPairing.add_weight hv hG hF₁ hF₂ hF₁Ω hF₂Ω
    (isDefectPairing_defectPairing hv hG hF₁ hF₁Ω) (isDefectPairing_defectPairing hv hG hF₂ hF₂Ω))

theorem isBoundedTest_sum {ι : Type*} (s : Finset ι) {F : ι → ComplexModel N → ℝ}
    (hF : ∀ b ∈ s, IsBoundedTest (F b)) : IsBoundedTest fun z => ∑ b ∈ s, F b z := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact ⟨measurable_const, HasCompactSupport.zero, 0, fun z => by simp⟩
  | insert b s hb ih =>
    simp only [Finset.sum_insert hb]
    exact (hF b (Finset.mem_insert_self b s)).add
      (ih fun c hc => hF c (Finset.mem_insert_of_mem hc))

theorem tsupport_sum_subset {ι : Type*} (s : Finset ι) {F : ι → ComplexModel N → ℝ}
    {S : Set (ComplexModel N)} (hF : ∀ b ∈ s, tsupport (F b) ⊆ S) :
    tsupport (fun z => ∑ b ∈ s, F b z) ⊆ S := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert b s hb ih =>
    simp only [Finset.sum_insert hb]
    exact (tsupport_add _ _).trans (union_subset (hF b (Finset.mem_insert_self b s))
      (ih fun c hc => hF c (Finset.mem_insert_of_mem hc)))

theorem defectPairing_sum_weight (hv : SlotsAdmissible Ω v i₀) (hG : ContDiffOn ℝ ∞ G Ω)
    {ι : Type*} (s : Finset ι) {F : ι → ComplexModel N → ℝ} (hF : ∀ b ∈ s, IsBoundedTest (F b))
    (hFΩ : ∀ b ∈ s, tsupport (F b) ⊆ Ω) :
    defectPairing Ω v i₀ G (fun z => ∑ b ∈ s, F b z) = ∑ b ∈ s, defectPairing Ω v i₀ G (F b) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    obtain ⟨V, p, ν₁, ν₂, hVΩ, -, h₁, h₂⟩ :=
      exists_witness hv hG (K := ∅) isCompact_empty (empty_subset _)
    exact defectPairing_eq ⟨measurable_const, HasCompactSupport.zero, 0,
      fun z => by simp⟩ ⟨V, p, ν₁, ν₂, hVΩ, by simp, h₁, h₂, by simp⟩
  | insert b s hb ih =>
    simp only [Finset.sum_insert hb]
    rw [defectPairing_add_weight hv hG (hF b (Finset.mem_insert_self b s))
      (isBoundedTest_sum s fun c hc => hF c (Finset.mem_insert_of_mem hc))
      (hFΩ b (Finset.mem_insert_self b s))
      (tsupport_sum_subset s fun c hc => hFΩ c (Finset.mem_insert_of_mem hc)),
      ih (fun c hc => hF c (Finset.mem_insert_of_mem hc))
        fun c hc => hFΩ c (Finset.mem_insert_of_mem hc)]

end Pairing

/-! ### Weights from locally bounded plurisubharmonic functions -/

section Weights

variable {N : ℕ}

theorem isBoundedTest_mul_sub {Ω : Opens (ComplexModel N)} {w₁ w₂ : ComplexModel N → ℝ}
    (hw₁ : IsLocallyBoundedPshOn Ω w₁) (hw₂ : IsLocallyBoundedPshOn Ω w₂)
    {χ : ComplexModel N → ℝ} (hχ : Continuous χ) (hχc : HasCompactSupport χ)
    (hχΩ : tsupport χ ⊆ Ω) : IsBoundedTest fun z => χ z * (w₁ z - w₂ z) := by
  have hm : Measurable fun z => χ z * w₁ z - χ z * w₂ z :=
    (measurable_mul_of_plurisubharmonicOn hw₁.1 hχ hχΩ).sub
      (measurable_mul_of_plurisubharmonicOn hw₂.1 hχ hχΩ)
  obtain ⟨C₁, hC₁⟩ := IsLocallyBoundedPshOn.exists_abs_le hw₁ hχc hχΩ
  obtain ⟨C₂, hC₂⟩ := IsLocallyBoundedPshOn.exists_abs_le hw₂ hχc hχΩ
  obtain ⟨B, hB⟩ := hχc.exists_bound_of_continuous hχ
  refine ⟨by simpa only [mul_sub] using hm, hχc.mul_right, B * (max C₁ 0 + max C₂ 0), fun z => ?_⟩
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB z)
  by_cases hz : z ∈ tsupport χ
  · rw [abs_mul]
    refine mul_le_mul (by simpa [Real.norm_eq_abs] using hB z) ?_ (abs_nonneg _) hB0
    calc |w₁ z - w₂ z| ≤ |w₁ z| + |w₂ z| := abs_sub _ _
      _ ≤ max C₁ 0 + max C₂ 0 :=
        add_le_add ((hC₁ z hz).trans (le_max_left _ _)) ((hC₂ z hz).trans (le_max_left _ _))
  · show |χ z * (w₁ z - w₂ z)| ≤ _
    rw [image_eq_zero_of_notMem_tsupport hz, zero_mul, abs_zero]
    exact mul_nonneg hB0 (add_nonneg (le_max_right _ _) (le_max_right _ _))

end Weights

/-! ### The time slot as a pairing -/

section TimeSlot

variable {n : ℕ}

theorem timeLaplacian_eq_zero_of_notMem_tsupport {ψ : ℂ → ℝ} {τ : ℂ} (hτ : τ ∉ tsupport ψ) :
    timeLaplacian ψ τ = 0 := by
  have h : iteratedFDeriv ℝ 2 ψ τ = 0 := by
    by_contra h
    exact hτ (support_iteratedFDeriv_subset 2 h)
  simp [timeLaplacian, realHessian, h]

theorem hasCompactSupport_timeLaplacian {ψ : ℂ → ℝ} (hψc : HasCompactSupport ψ) :
    HasCompactSupport (timeLaplacian ψ) :=
  hψc.mono' fun τ hτ => by
    by_contra h
    exact hτ (timeLaplacian_eq_zero_of_notMem_tsupport h)

theorem contDiff_lastNormSq : ContDiff ℝ ∞ (lastNormSq n) :=
  (contDiff_norm_sq ℝ).comp (lastCoordinate n).contDiff

/-- `ψ̂ + C |τ|²` is smooth plurisubharmonic when `|Δψ/4| ≤ C`. -/
theorem isSmoothPsdOn_timeLift_add {ψ : ℂ → ℝ} (hψ : ContDiff ℝ ∞ ψ) {C : ℝ}
    (hC : ∀ τ, |timeLaplacian ψ τ| ≤ C) (U : Opens (ComplexModel (n + 1))) :
    IsSmoothPsdOn U fun q => timeLift n ψ q + C * lastNormSq n q := by
  have h2 : (2 : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
  have hL : ContDiff ℝ ∞ (lastNormSq n) := contDiff_lastNormSq
  refine ⟨((contDiff_timeLift hψ).add (contDiff_const.mul hL)).contDiffOn, fun q _ => ?_⟩
  have hfun : (fun q => timeLift n ψ q + C * lastNormSq n q) = timeLift n ψ + C • lastNormSq n := by
    funext q; simp
  have hCL : ContDiffAt ℝ 2 (C • lastNormSq n) q := (hL.const_smul C).contDiffAt.of_le h2
  rw [hfun, complexHessian_add ((contDiff_timeLift hψ).contDiffAt.of_le h2) hCL,
    complexHessian_smul (hL.contDiffAt.of_le h2),
    complexHessian_timeLift (hψ.of_le h2), complexHessian_lastNormSq]
  have hc : 0 ≤ timeLaplacian ψ (q (Fin.last n)) + C := by
    have := hC (q (Fin.last n))
    linarith [neg_abs_le (timeLaplacian ψ (q (Fin.last n)))]
  have hpsd := (lastUnit_posSemidef (n := n)).smul
    (show (0 : ℂ) ≤ ((timeLaplacian ψ (q (Fin.last n)) + C : ℝ) : ℂ) from Complex.zero_le_real.mpr hc)
  convert hpsd using 1
  rw [Complex.ofReal_add, add_smul]
  simp only [Complex.coe_smul]

/-- **The time slot as a pairing.** On `Ω ⊆ ℂⁿ⁺¹`, the pairing of `χ (w₁ - w₂)` with
`ddᶜψ̂ ∧ T` (`ψ̂(z, τ) = ψ(τ)`) is `∫ χ (Δψ/4)(τ) (w₁ - w₂) dBT(T, |τ|²)`. -/
theorem isDefectPairing_timeLift {Ω : Opens (ComplexModel (n + 1))}
    {v : Fin (n + 1) → ComplexModel (n + 1) → ℝ}
    (hv : ∀ i, i ≠ Fin.last n → IsLocallyBoundedPshOn Ω (v i)) {ψ : ℂ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) {ν : Measure (ComplexModel (n + 1))}
    (hν : IsBTLimit Ω (Function.update v (Fin.last n) (lastNormSq n)) ν)
    {w₁ w₂ : ComplexModel (n + 1) → ℝ} (hw₁ : IsLocallyBoundedPshOn Ω w₁)
    (hw₂ : IsLocallyBoundedPshOn Ω w₂) {χ : ComplexModel (n + 1) → ℝ} (hχ : Continuous χ)
    (hχc : HasCompactSupport χ) (hχΩ : tsupport χ ⊆ Ω) :
    IsDefectPairing Ω v (Fin.last n) (timeLift n ψ) (fun q => χ q * (w₁ q - w₂ q))
      (∫ q, (χ q * timeLaplacian ψ (q (Fin.last n))) * (w₁ q - w₂ q) ∂ν) := by
  classical
  obtain ⟨C₀, hC₀⟩ := (hasCompactSupport_timeLaplacian hψc).exists_bound_of_continuous
    (continuous_timeLaplacian hψ)
  have hC : ∀ τ, |timeLaplacian ψ τ| ≤ C₀ := fun τ => by simpa [Real.norm_eq_abs] using hC₀ τ
  have hC0 : 0 ≤ C₀ := (abs_nonneg _).trans (hC 0)
  set p : ComplexModel (n + 1) → ℝ := fun q => C₀ * lastNormSq n q with hp_def
  have hp : IsSmoothPsdOn Ω p := by
    have h := isSmoothPsdOn_timeLift_add (n := n) (contDiff_const (c := (0 : ℝ))) (C := C₀)
      (fun τ => by
        have : timeLaplacian (fun _ : ℂ => (0 : ℝ)) τ = 0 := by simp [timeLaplacian]
        rw [this, abs_zero]; exact hC0) Ω
    simpa [timeLift] using h
  have hψp : IsSmoothPsdOn Ω fun q => timeLift n ψ q + p q := isSmoothPsdOn_timeLift_add hψ hC Ω
  have hslots : ∀ s : ComplexModel (n + 1) → ℝ, IsSmoothPsdOn Ω s →
      ∃ μ, IsBTLimit Ω (Function.update v (Fin.last n) s) μ := fun s hs =>
    exists_isBTLimit_of_isLocallyBoundedPshOn fun i => by
      by_cases hi : i = Fin.last n
      · subst hi; simpa using hs.isLocallyBoundedPshOn
      · simpa [Function.update_of_ne hi] using hv i hi
  obtain ⟨ν₁, hν₁⟩ := hslots _ hψp
  obtain ⟨ν₂, hν₂⟩ := hslots _ hp
  have hdec : ∀ {w : ComplexModel (n + 1) → ℝ}, IsLocallyBoundedPshOn Ω w →
      ∀ V, RelativelyCompactIn V Ω → ∃ G, IsDecApprox V w G := fun hw V hV =>
    exists_isDecApprox_of_isLocallyBoundedPshOn hw V hV
  have h₁ := integral_isBTLimit_timeLift_sub hψ hp hψp hν₁ hν₂ hν (hdec hw₁) hχ hχc hχΩ
  have h₂ := integral_isBTLimit_timeLift_sub hψ hp hψp hν₁ hν₂ hν (hdec hw₂) hχ hχc hχΩ
  -- integrability of the four pairings and of the two right-hand sides
  obtain ⟨U, hUo, hKU, hUΩ, hUc⟩ := exists_open_between_and_isCompact_closure hχc Ω.isOpen hχΩ
  set UO : Opens (ComplexModel (n + 1)) := ⟨U, hUo⟩
  have hUrc : RelativelyCompactIn UO Ω := ⟨hUc, hUΩ⟩
  have hUOΩ : UO ≤ Ω := subset_closure.trans hUΩ
  have hint : ∀ {w : ComplexModel (n + 1) → ℝ}, IsLocallyBoundedPshOn Ω w →
      ∀ {μ : Measure (ComplexModel (n + 1))}, (∀ K, IsCompact K → K ⊆ Ω → μ K < ⊤) →
        ∀ {ζ : ComplexModel (n + 1) → ℝ}, Continuous ζ → tsupport ζ ⊆ tsupport χ →
          Integrable (fun q => ζ q * w q) μ := by
    intro w hw μ hμ ζ hζ hζχ
    obtain ⟨G, hG⟩ := hdec hw UO hUrc
    exact hG.integrable_mul (fun K hK hKU => hμ K hK (hKU.trans hUOΩ)) hζ
      (hχc.mono' ((subset_tsupport ζ).trans hζχ)) (hζχ.trans hKU)
  have hχlap : Continuous fun q => χ q * timeLaplacian ψ (q (Fin.last n)) :=
    hχ.mul ((continuous_timeLaplacian hψ).comp (lastCoordinate n).continuous)
  have hχlapS : tsupport (fun q => χ q * timeLaplacian ψ (q (Fin.last n))) ⊆ tsupport χ :=
    tsupport_mul_subset_left
  refine ⟨Ω, p, ν₁, ν₂, le_rfl, tsupport_mul_subset_left.trans hχΩ, hν₁, hν₂, ?_⟩
  have e₁ : (∫ q, χ q * (w₁ q - w₂ q) ∂ν₁) = (∫ q, χ q * w₁ q ∂ν₁) - ∫ q, χ q * w₂ q ∂ν₁ := by
    simp only [mul_sub]
    exact integral_sub (hint hw₁ hν₁.2.1 hχ subset_rfl) (hint hw₂ hν₁.2.1 hχ subset_rfl)
  have e₂ : (∫ q, χ q * (w₁ q - w₂ q) ∂ν₂) = (∫ q, χ q * w₁ q ∂ν₂) - ∫ q, χ q * w₂ q ∂ν₂ := by
    simp only [mul_sub]
    exact integral_sub (hint hw₁ hν₂.2.1 hχ subset_rfl) (hint hw₂ hν₂.2.1 hχ subset_rfl)
  have e₃ : (∫ q, (χ q * timeLaplacian ψ (q (Fin.last n))) * (w₁ q - w₂ q) ∂ν) =
      (∫ q, (χ q * timeLaplacian ψ (q (Fin.last n))) * w₁ q ∂ν) -
        ∫ q, (χ q * timeLaplacian ψ (q (Fin.last n))) * w₂ q ∂ν := by
    simp only [mul_sub]
    exact integral_sub (hint hw₁ hν.2.1 hχlap hχlapS) (hint hw₂ hν.2.1 hχlap hχlapS)
  rw [e₁, e₂, e₃, ← h₁, ← h₂]
  ring

end TimeSlot

/-! ### The local integration by parts -/

section IBP

variable {n : ℕ}

/-- `h` in the slots `i < j`, `Φ` in the others. -/
def endpointTuple {N : ℕ} (h Φ : ComplexModel N → ℝ) (j : ℕ) : Fin N → ComplexModel N → ℝ :=
  fun i => if (i : ℕ) < j then h else Φ

theorem update_endpointTuple_last_right (h Φ : ComplexModel (n + 1) → ℝ) (j : Fin (n + 1)) :
    Function.update (endpointTuple h Φ j) (Fin.last n) Φ = endpointTuple h Φ j := by
  funext i
  by_cases hi : i = Fin.last n
  · subst hi
    have : ¬ n < (j : ℕ) := not_lt.mpr (Nat.lt_succ_iff.mp j.isLt)
    simp [endpointTuple, this]
  · simp [Function.update_of_ne hi]

theorem update_endpointTuple_last_left (h Φ : ComplexModel (n + 1) → ℝ) (j : Fin (n + 1)) :
    Function.update (endpointTuple h Φ j) (Fin.last n) h =
      fun i => endpointTuple h Φ ((j : ℕ) + 1) (Equiv.swap j (Fin.last n) i) := by
  funext i
  by_cases hi : i = Fin.last n
  · subst hi
    simp [endpointTuple]
  · rw [Function.update_of_ne hi]
    by_cases hij : i = j
    · subst hij
      have hlt : (i : ℕ) < n := by
        have := i.isLt
        have hne : (i : ℕ) ≠ n := fun h => hi (Fin.ext (by simpa using h))
        omega
      simp [endpointTuple, Equiv.swap_apply_left, hlt]
    · rw [Equiv.swap_apply_of_ne_of_ne hij hi]
      have hne : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Fin.ext h)
      simp only [endpointTuple]
      by_cases h1 : (i : ℕ) < j
      · rw [if_pos h1, if_pos (by omega)]
      · rw [if_neg h1, if_neg (by omega)]

theorem isLocallyBoundedPshOn_endpointTuple {N : ℕ} {Ω : Opens (ComplexModel N)}
    {h Φ : ComplexModel N → ℝ} (hh : IsLocallyBoundedPshOn Ω h) (hΦ : IsLocallyBoundedPshOn Ω Φ)
    (j : ℕ) (i : Fin N) : IsLocallyBoundedPshOn Ω (endpointTuple h Φ j i) := by
  unfold endpointTuple
  split_ifs
  exacts [hh, hΦ]

theorem slotsAdmissible_endpointTuple {N : ℕ} {Ω : Opens (ComplexModel N)}
    {h Φ : ComplexModel N → ℝ} (hh : IsLocallyBoundedPshOn Ω h) (hΦ : IsLocallyBoundedPshOn Ω Φ)
    (j : ℕ) (i₀ : Fin N) : SlotsAdmissible Ω (endpointTuple h Φ j) i₀ :=
  slotsAdmissible_of_isLocallyBoundedPshOn fun i _ => isLocallyBoundedPshOn_endpointTuple hh hΦ j i

/-- **The local integration by parts.** If `(ddᶜh)ⁿ⁺¹ = (ddᶜΦ)ⁿ⁺¹ = 0` on `Ω ⊆ ℂⁿ⁺¹`, then
`Σ_j ∫ F d(ddᶜg ∧ (ddᶜh)ʲ ∧ (ddᶜΦ)ⁿ⁻ʲ) = 0` for every test function `g` and every weight `F` equal to
`h - Φ` near `supp g`. -/
theorem sum_defectPairing_endpointTuple_eq_zero {Ω : Opens (ComplexModel (n + 1))}
    {h Φ : ComplexModel (n + 1) → ℝ} (hh : IsLocallyBoundedPshOn Ω h)
    (hΦ : IsLocallyBoundedPshOn Ω Φ) (hh0 : IsBTLimit Ω (fun _ => h) 0)
    (hΦ0 : IsBTLimit Ω (fun _ => Φ) 0) {g : ComplexModel (n + 1) → ℝ} (hg : ContDiff ℝ ∞ g)
    (hgc : HasCompactSupport g) (hgΩ : tsupport g ⊆ Ω) {F : ComplexModel (n + 1) → ℝ}
    (hF : IsBoundedTest F) (hFΩ : tsupport F ⊆ Ω) {O : Set (ComplexModel (n + 1))}
    (hO : IsOpen O) (hgO : tsupport g ⊆ O) (hFO : ∀ z ∈ O, z ∈ Ω → F z = h z - Φ z) :
    ∑ j : Fin (n + 1), defectPairing Ω (endpointTuple h Φ j) (Fin.last n) g F = 0 := by
  classical
  have hslot := isLocallyBoundedPshOn_endpointTuple hh hΦ
  choose μ hμ using fun k : ℕ => exists_isBTLimit_of_isLocallyBoundedPshOn (hslot k)
  have hμ0 : μ 0 = 0 := by
    have heq : endpointTuple h Φ 0 = fun _ => Φ := by
      funext i; simp [endpointTuple]
    exact (hμ 0).unique (heq ▸ hΦ0)
  have hμn : μ (n + 1) = 0 := by
    have heq : endpointTuple h Φ (n + 1) = fun _ => h := by
      funext i; simp [endpointTuple, i.isLt]
    exact (hμ (n + 1)).unique (heq ▸ hh0)
  have hstep : ∀ j : Fin (n + 1), defectPairing Ω (endpointTuple h Φ j) (Fin.last n) g F =
      (∫ z, g z ∂μ ((j : ℕ) + 1)) - ∫ z, g z ∂μ j := by
    intro j
    obtain ⟨C, hC0, hCpsd⟩ := exists_isSmoothPsdOn_add_norm_sq hg hgc
    set p : ComplexModel (n + 1) → ℝ := fun z => C * ‖z‖ ^ 2 with hp_def
    have hp : IsSmoothPsdOn Ω p := by
      simpa using (isSmoothPsdOn_const Ω 0).add_smul_norm_sq hC0
    have hgp : IsSmoothPsdOn Ω fun z => g z + p z :=
      ⟨hCpsd.1.mono (subset_univ _), fun z _ => hCpsd.2 z trivial⟩
    have hupd : ∀ s : ComplexModel (n + 1) → ℝ, IsSmoothPsdOn Ω s →
        ∃ ν, IsBTLimit Ω (Function.update (endpointTuple h Φ j) (Fin.last n) s) ν := fun s hs =>
      exists_isBTLimit_of_isLocallyBoundedPshOn fun i => by
        by_cases hi : i = Fin.last n
        · subst hi; simpa using hs.isLocallyBoundedPshOn
        · simpa [Function.update_of_ne hi] using hslot j i
    obtain ⟨ν₁, hν₁⟩ := hupd _ hgp
    obtain ⟨ν₂, hν₂⟩ := hupd _ hp
    have hμa : IsBTLimit Ω (Function.update (endpointTuple h Φ j) (Fin.last n) h)
        (μ ((j : ℕ) + 1)) := by
      rw [update_endpointTuple_last_left]
      exact (hμ _).comp_perm _
    have hμb : IsBTLimit Ω (Function.update (endpointTuple h Φ j) (Fin.last n) Φ) (μ j) := by
      rw [update_endpointTuple_last_right]
      exact hμ _
    obtain ⟨χ, hχs, hχc, hχΩ, hχ1, heq⟩ :=
      exists_integral_sub_eq_slotDefect_last (j := Fin.last n) (by simp) hμa hμb hν₁ hν₂ hg hgc hgΩ
    have hBT : IsBoundedTest fun z => χ z * (h z - Φ z) :=
      isBoundedTest_mul_sub hh hΦ hχs.continuous hχc hχΩ
    have hpair : IsDefectPairing Ω (endpointTuple h Φ j) (Fin.last n) g
        (fun z => χ z * (h z - Φ z)) ((∫ z, g z ∂μ ((j : ℕ) + 1)) - ∫ z, g z ∂μ j) :=
      ⟨Ω, p, ν₁, ν₂, le_rfl, tsupport_mul_subset_left.trans hχΩ, hν₁, hν₂, heq⟩
    have hadm := slotsAdmissible_endpointTuple hh hΦ j (Fin.last n)
    have hdp := isDefectPairing_defectPairing hadm hg.contDiffOn hF hFΩ
    obtain ⟨N', hN'o, hgN', hN'1⟩ := mem_nhdsSet_iff_exists.mp hχ1
    exact IsDefectPairing.congr_weight' hadm hg.contDiffOn hF hBT hFΩ
      (tsupport_mul_subset_left.trans hχΩ) ((hO.inter hN'o).inter Ω.isOpen)
      (fun z hzΩ hz => ⟨⟨hgO hz, hgN' hz⟩, hzΩ⟩)
      (fun z hz => by
        have h1 : χ z = 1 := hN'1 hz.1.2
        simp only [hFO z hz.1.1 hz.2, h1, one_mul]) hdp hpair
  rw [Finset.sum_congr rfl fun j _ => hstep j,
    Fin.sum_univ_eq_sum_range (fun k => (∫ z, g z ∂μ (k + 1)) - ∫ z, g z ∂μ k) (n + 1),
    Finset.sum_range_sub (fun k => ∫ z, g z ∂μ k), hμn, hμ0]
  simp

end IBP

end

end SGPT.Foundations.Analysis.Pending.BedfordTaylorStripIBP
