import SGPT.Foundations.Analysis.Pending.BedfordTaylorSlotStokes
import SGPT.Foundations.Analysis.Pending.BedfordTaylorHolomorphic
import SGPT.Foundations.Analysis.Pending.BedfordTaylorCapacity
import SGPT.Foundations.Analysis.Pending.BedfordTaylorCollarSymmetry
import SGPT.Foundations.Analysis.Pending.BedfordTaylorFixedWeight
import SGPT.Foundations.Analysis.Pending.BedfordTaylorCompactMassEquality

set_option autoImplicit false

/-!
# Pairings with a regularized slot defect

For a tuple `v` of slots on an open set `Ω ⊆ ℂᴺ`, a slot index `i₀`, a function `G` and a bounded
measurable compactly supported weight `F`, the number

  `∫ F d(ddᶜG ∧ T) = ∫ F dν₁ - ∫ F dν₂`,   `ν₁ = BT(v; G + p in slot i₀)`, `ν₂ = BT(v; p in slot i₀)`,

is read on any open `V ⊆ Ω` containing `supp F`, with any regularizer `p` for which the two
Bedford--Taylor limits exist on `V` (`IsDefectPairing`). Here `T` is the Bedford--Taylor product of
the other slots. This module shows that the number is a well-defined, linear, local and
coordinate-free object:

* `IsDefectPairing.unique` — it does not depend on `V` or on the regularizer
  (`IsBTLimit.slotDefect_regularizer_congr`);
* `IsDefectPairing.add`, `isDefectPairing_zero`, `IsDefectPairing.sum` — it is additive in `G`
  (`IsBTLimit.slotDefect_add`; regularizers add, so no smoothness is needed);
* `exists_isDefectPairing`, `IsDefectPairing.add_weight`, `IsDefectPairing.smul_weight`,
  `IsDefectPairing.congr_weight` — for `G` smooth on `Ω` and slots admitting Bedford--Taylor limits
  with smooth plurisubharmonic last slots (`SlotsAdmissible`), it exists, is linear in `F` and only
  sees `F` near `supp G`;
* `IsDefectPairing.comp_biholomorphic` — it is invariant under biholomorphic changes of
  coordinates, the other slots being allowed to change by smooth pluriharmonic gauges.

This is what a partition-of-unity argument needs to glue chartwise integrations by parts on a
non-compact manifold such as `X × (strip)` (Xia, SGPT, proof of Proposition 4.3.3,
`xia-sgpt:page-0171`).
-/

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ContDiff ComplexOrder

namespace SGPT.Foundations.Analysis.Pending.BedfordTaylorDefectPairing

open FirstPass FirstPass.MongeAmpere FirstPass.MixedMongeAmpere BedfordTaylor

noncomputable section

variable {N : ℕ}

/-- A bounded measurable weight with compact support. -/
def IsBoundedTest (F : ComplexModel N → ℝ) : Prop :=
  Measurable F ∧ HasCompactSupport F ∧ ∃ C, ∀ z, |F z| ≤ C

/-- **The defect pairing** `I = ∫ F d(ddᶜG ∧ T)`, witnessed on an open `V ⊆ Ω` containing `supp F`
with a regularizer `p`. -/
def IsDefectPairing (Ω : Opens (ComplexModel N)) (v : Fin N → ComplexModel N → ℝ) (i₀ : Fin N)
    (G F : ComplexModel N → ℝ) (I : ℝ) : Prop :=
  ∃ (V : Opens (ComplexModel N)) (p : ComplexModel N → ℝ) (ν₁ ν₂ : Measure (ComplexModel N)),
    V ≤ Ω ∧ tsupport F ⊆ V ∧
    IsBTLimit V (Function.update v i₀ fun z => G z + p z) ν₁ ∧
    IsBTLimit V (Function.update v i₀ p) ν₂ ∧
    I = (∫ z, F z ∂ν₁) - ∫ z, F z ∂ν₂

/-- The slots other than `i₀` admit Bedford--Taylor limits with any smooth plurisubharmonic function
in slot `i₀`, on every open subset of `Ω`. -/
def SlotsAdmissible (Ω : Opens (ComplexModel N)) (v : Fin N → ComplexModel N → ℝ) (i₀ : Fin N) :
    Prop :=
  ∀ (V : Opens (ComplexModel N)) (s : ComplexModel N → ℝ), V ≤ Ω → IsSmoothPsdOn V s →
    ∃ μ, IsBTLimit V (Function.update v i₀ s) μ

theorem slotsAdmissible_of_isLocallyBoundedPshOn {Ω : Opens (ComplexModel N)}
    {v : Fin N → ComplexModel N → ℝ} {i₀ : Fin N}
    (hv : ∀ i, i ≠ i₀ → IsLocallyBoundedPshOn Ω (v i)) : SlotsAdmissible Ω v i₀ := by
  classical
  intro V s hVΩ hs
  refine exists_isBTLimit_of_isLocallyBoundedPshOn fun i => ?_
  by_cases h : i = i₀
  · subst h; simpa using hs.isLocallyBoundedPshOn
  · simpa [Function.update_of_ne h] using BedfordTaylor.IsLocallyBoundedPshOn.mono_opens (hv i h) hVΩ

theorem IsBoundedTest.integrable {F : ComplexModel N → ℝ} (hF : IsBoundedTest F)
    {V : Opens (ComplexModel N)} {μ : Measure (ComplexModel N)}
    (hμ : ∀ K, IsCompact K → K ⊆ V → μ K < ⊤) (hFV : tsupport F ⊆ V) : Integrable F μ := by
  obtain ⟨C, hC⟩ := hF.2.2
  rw [← integrableOn_iff_integrable_of_support_subset (subset_tsupport F)]
  exact Measure.integrableOn_of_bounded (M := C) (hμ _ hF.2.1 hFV).ne
    hF.1.aestronglyMeasurable (Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs]; exact hC z)

theorem IsBoundedTest.add {F F' : ComplexModel N → ℝ} (hF : IsBoundedTest F)
    (hF' : IsBoundedTest F') : IsBoundedTest fun z => F z + F' z := by
  obtain ⟨C, hC⟩ := hF.2.2
  obtain ⟨C', hC'⟩ := hF'.2.2
  exact ⟨hF.1.add hF'.1, hF.2.1.add hF'.2.1, C + C', fun z =>
    (abs_add_le _ _).trans (add_le_add (hC z) (hC' z))⟩

theorem IsBoundedTest.sub {F F' : ComplexModel N → ℝ} (hF : IsBoundedTest F)
    (hF' : IsBoundedTest F') : IsBoundedTest fun z => F z - F' z := by
  obtain ⟨C, hC⟩ := hF.2.2
  obtain ⟨C', hC'⟩ := hF'.2.2
  exact ⟨hF.1.sub hF'.1, hF.2.1.sub hF'.2.1, C + C', fun z =>
    (abs_sub _ _).trans (add_le_add (hC z) (hC' z))⟩

theorem IsBoundedTest.const_mul {F : ComplexModel N → ℝ} (hF : IsBoundedTest F) (c : ℝ) :
    IsBoundedTest fun z => c * F z := by
  obtain ⟨C, hC⟩ := hF.2.2
  exact ⟨hF.1.const_mul c, hF.2.1.mul_left, |c| * C, fun z => by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hC z) (abs_nonneg c)⟩

/-- Integrals of a weight supported in `V` do not see the restriction to `V`. -/
theorem integral_restrict_of_tsupport {F : ComplexModel N → ℝ} {V : Set (ComplexModel N)}
    (hFV : tsupport F ⊆ V) (μ : Measure (ComplexModel N)) :
    ∫ z, F z ∂(μ.restrict V) = ∫ z, F z ∂μ :=
  setIntegral_eq_integral_of_forall_compl_eq_zero fun _ hz =>
    image_eq_zero_of_notMem_tsupport fun h => hz (hFV h)

/-- **The core of uniqueness**: on one domain, two regularizers give the same pairing. -/
theorem integral_sub_eq_of_regularizers {V : Opens (ComplexModel N)}
    {v : Fin N → ComplexModel N → ℝ} {i₀ : Fin N} {G F p q : ComplexModel N → ℝ}
    {μ₁ μ₂ ν₁ ν₂ : Measure (ComplexModel N)}
    (hμ₁ : IsBTLimit V (Function.update v i₀ fun z => G z + p z) μ₁)
    (hμ₂ : IsBTLimit V (Function.update v i₀ p) μ₂)
    (hν₁ : IsBTLimit V (Function.update v i₀ fun z => G z + q z) ν₁)
    (hν₂ : IsBTLimit V (Function.update v i₀ q) ν₂)
    (hF : IsBoundedTest F) (hFV : tsupport F ⊆ V) :
    (∫ z, F z ∂μ₁) - ∫ z, F z ∂μ₂ = (∫ z, F z ∂ν₁) - ∫ z, F z ∂ν₂ := by
  have h := IsBTLimit.slotDefect_regularizer_congr i₀ hμ₁ hμ₂ hν₁ hν₂
  have hI := congrArg (fun μ : Measure (ComplexModel N) => ∫ z, F z ∂μ) h
  rw [integral_add_measure (hF.integrable hμ₁.2.1 hFV) (hF.integrable hν₂.2.1 hFV),
    integral_add_measure (hF.integrable hν₁.2.1 hFV) (hF.integrable hμ₂.2.1 hFV)] at hI
  linarith

/-- **Uniqueness of the defect pairing.** -/
theorem IsDefectPairing.unique {Ω : Opens (ComplexModel N)} {v : Fin N → ComplexModel N → ℝ}
    {i₀ : Fin N} {G F : ComplexModel N → ℝ} {I I' : ℝ} (hF : IsBoundedTest F)
    (h : IsDefectPairing Ω v i₀ G F I) (h' : IsDefectPairing Ω v i₀ G F I') : I = I' := by
  obtain ⟨V, p, ν₁, ν₂, -, hFV, h₁, h₂, rfl⟩ := h
  obtain ⟨V', p', ν₁', ν₂', -, hFV', h₁', h₂', rfl⟩ := h'
  have hW : tsupport F ⊆ (V ⊓ V' : Opens (ComplexModel N)) := fun z hz => ⟨hFV hz, hFV' hz⟩
  have e := integral_sub_eq_of_regularizers (h₁.restrict_opens inf_le_left)
    (h₂.restrict_opens inf_le_left) (h₁'.restrict_opens inf_le_right)
    (h₂'.restrict_opens inf_le_right) hF hW
  simp only [integral_restrict_of_tsupport hW] at e
  exact e

/-- The pairing with `G = 0` is `0`, given any witness domain with a regularizer. -/
theorem isDefectPairing_zero {Ω : Opens (ComplexModel N)} {v : Fin N → ComplexModel N → ℝ}
    {i₀ : Fin N} {F : ComplexModel N → ℝ} {V : Opens (ComplexModel N)} {p : ComplexModel N → ℝ}
    {ν : Measure (ComplexModel N)} (hVΩ : V ≤ Ω) (hFV : tsupport F ⊆ V)
    (hν : IsBTLimit V (Function.update v i₀ p) ν) : IsDefectPairing Ω v i₀ (fun _ => 0) F 0 :=
  ⟨V, p, ν, ν, hVΩ, hFV, by simpa using hν, hν, by ring⟩

/-- **Additivity in the slot function.** Regularizers add, so no smoothness is needed. -/
theorem IsDefectPairing.add {Ω : Opens (ComplexModel N)} {v : Fin N → ComplexModel N → ℝ}
    {i₀ : Fin N} {G₁ G₂ F : ComplexModel N → ℝ} {I₁ I₂ : ℝ} (hF : IsBoundedTest F)
    (h₁ : IsDefectPairing Ω v i₀ G₁ F I₁) (h₂ : IsDefectPairing Ω v i₀ G₂ F I₂) :
    IsDefectPairing Ω v i₀ (fun z => G₁ z + G₂ z) F (I₁ + I₂) := by
  obtain ⟨V₁, p₁, ν₁, ν₂, hV₁, hFV₁, hν₁, hν₂, rfl⟩ := h₁
  obtain ⟨V₂, p₂, μ₁, μ₂, hV₂, hFV₂, hμ₁, hμ₂, rfl⟩ := h₂
  obtain ⟨W, hWdef⟩ : ∃ W : Opens (ComplexModel N), W = V₁ ⊓ V₂ := ⟨_, rfl⟩
  have hW₁ : W ≤ V₁ := hWdef ▸ inf_le_left
  have hW₂ : W ≤ V₂ := hWdef ▸ inf_le_right
  have hFW : tsupport F ⊆ W := fun z hz => by rw [hWdef]; exact ⟨hFV₁ hz, hFV₂ hz⟩
  have a₁ := hν₁.restrict_opens hW₁
  have a₂ := hν₂.restrict_opens hW₁
  have b₁ := hμ₁.restrict_opens hW₂
  have b₂ := hμ₂.restrict_opens hW₂
  -- the common regularizer `p₁ + p₂`
  obtain ⟨σP, hσP⟩ := exists_isBTLimit_update_add i₀ a₂ b₂
  obtain ⟨σ₁, hσ₁⟩ := exists_isBTLimit_update_add i₀ a₁ b₂
  obtain ⟨σ₂, hσ₂⟩ := exists_isBTLimit_update_add i₀ a₂ b₁
  obtain ⟨σ₁₂, hσ₁₂⟩ := exists_isBTLimit_update_add i₀ a₁ b₁
  have e₁ : (fun z => (G₁ z + p₁ z) + p₂ z) = fun z => G₁ z + (p₁ z + p₂ z) := by
    funext z; ring
  have e₂ : (fun z => p₁ z + (G₂ z + p₂ z)) = fun z => G₂ z + (p₁ z + p₂ z) := by
    funext z; ring
  have e₁₂ : (fun z => (G₁ z + p₁ z) + (G₂ z + p₂ z)) =
      fun z => (G₁ z + G₂ z) + (p₁ z + p₂ z) := by
    funext z; ring
  rw [e₁] at hσ₁
  rw [e₂] at hσ₂
  rw [e₁₂] at hσ₁₂
  have hadd := IsBTLimit.slotDefect_add (φ := G₁) (ψ := G₂) i₀ hσ₁₂ hσ₁ hσ₂ hσP
  have hI := congrArg (fun μ : Measure (ComplexModel N) => ∫ z, F z ∂μ) hadd
  rw [integral_add_measure (hF.integrable hσ₁₂.2.1 hFW) (hF.integrable hσP.2.1 hFW),
    integral_add_measure (hF.integrable hσ₁.2.1 hFW) (hF.integrable hσ₂.2.1 hFW)] at hI
  have r₁ := integral_sub_eq_of_regularizers a₁ a₂ hσ₁ hσP hF hFW
  have r₂ := integral_sub_eq_of_regularizers b₁ b₂ hσ₂ hσP hF hFW
  simp only [integral_restrict_of_tsupport hFW] at r₁ r₂
  refine ⟨W, fun z => p₁ z + p₂ z, σ₁₂, σP, hW₁.trans hV₁, hFW, hσ₁₂, hσP, ?_⟩
  linarith

/-- **Finite sums.** -/
theorem IsDefectPairing.sum {Ω : Opens (ComplexModel N)} {v : Fin N → ComplexModel N → ℝ}
    {i₀ : Fin N} {F : ComplexModel N → ℝ} (hF : IsBoundedTest F) {V : Opens (ComplexModel N)}
    {p : ComplexModel N → ℝ} {ν : Measure (ComplexModel N)} (hVΩ : V ≤ Ω) (hFV : tsupport F ⊆ V)
    (hν : IsBTLimit V (Function.update v i₀ p) ν) {ι : Type*} (s : Finset ι)
    (G : ι → ComplexModel N → ℝ) (I : ι → ℝ) (h : ∀ b ∈ s, IsDefectPairing Ω v i₀ (G b) F (I b)) :
    IsDefectPairing Ω v i₀ (fun z => ∑ b ∈ s, G b z) F (∑ b ∈ s, I b) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isDefectPairing_zero hVΩ hFV hν
  | insert b s hb ih =>
    simp only [Finset.sum_insert hb]
    exact (h b (Finset.mem_insert_self b s)).add hF (ih fun c hc => h c (Finset.mem_insert_of_mem hc))

/-- **Linearity in the weight, scalar part** (same witness). -/
theorem IsDefectPairing.smul_weight {Ω : Opens (ComplexModel N)}
    {v : Fin N → ComplexModel N → ℝ} {i₀ : Fin N} {G F : ComplexModel N → ℝ} {I : ℝ}
    (h : IsDefectPairing Ω v i₀ G F I) (c : ℝ) :
    IsDefectPairing Ω v i₀ G (fun z => c * F z) (c * I) := by
  obtain ⟨V, p, ν₁, ν₂, hVΩ, hFV, h₁, h₂, rfl⟩ := h
  refine ⟨V, p, ν₁, ν₂, hVΩ, (tsupport_mul_subset_right).trans hFV, h₁, h₂, ?_⟩
  rw [integral_const_mul, integral_const_mul]
  ring

/-! ### Existence for smooth slot functions, and locality in the weight -/

/-- **Witnesses on a domain containing a given compact set**, for `G` smooth on `Ω`. -/
theorem exists_witness {Ω : Opens (ComplexModel N)} {v : Fin N → ComplexModel N → ℝ}
    {i₀ : Fin N} (hv : SlotsAdmissible Ω v i₀) {G : ComplexModel N → ℝ} (hG : ContDiffOn ℝ ∞ G Ω)
    {K : Set (ComplexModel N)} (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ (V : Opens (ComplexModel N)) (p : ComplexModel N → ℝ) (ν₁ ν₂ : Measure (ComplexModel N)),
      V ≤ Ω ∧ K ⊆ V ∧ IsBTLimit V (Function.update v i₀ fun z => G z + p z) ν₁ ∧
      IsBTLimit V (Function.update v i₀ p) ν₂ := by
  obtain ⟨W, hWo, hKW, hWΩ, hWc⟩ := exists_open_between_and_isCompact_closure hK Ω.isOpen hKΩ
  set V : Opens (ComplexModel N) := ⟨W, hWo⟩
  have hVΩ : V ≤ Ω := subset_closure.trans hWΩ
  obtain ⟨η, hη1, -⟩ := exists_testFunction_eq_one_nhds_compact hWc hWΩ
  set G' : ComplexModel N → ℝ := fun z => η z • G z with hG'def
  have hG's : ContDiff ℝ ∞ G' :=
    LocalPotentials.contDiff_smul_of_tsupport_subset Ω.isOpen η.contDiff η.tsupport_subset hG
  have hG'c : HasCompactSupport G' :=
    η.hasCompactSupport.mono' ((tsupport_smul_subset_left _ _).trans subset_rfl |>
      fun h => (subset_tsupport _).trans h)
  obtain ⟨C, hC0, hCpsd⟩ := exists_isSmoothPsdOn_add_norm_sq hG's hG'c
  set p : ComplexModel N → ℝ := fun z => C * ‖z‖ ^ 2
  have hpV : IsSmoothPsdOn V p := IsSmoothPsdOn.mono (isSmoothPsdOn_const_mul_norm_sq hC0) le_top
  have hG'pV : IsSmoothPsdOn V fun z => G' z + p z := IsSmoothPsdOn.mono hCpsd le_top
  obtain ⟨ν₁, hν₁⟩ := hv V _ hVΩ hG'pV
  obtain ⟨ν₂, hν₂⟩ := hv V _ hVΩ hpV
  have hηW : ∀ z ∈ W, η z = 1 := fun z hz =>
    (hη1.filter_mono (nhds_le_nhdsSet (subset_closure hz))).self_of_nhds
  refine ⟨V, p, ν₁, ν₂, hVΩ, hKW, hν₁.congr fun i z hz => ?_, hν₂⟩
  classical
  by_cases h : i = i₀
  · subst h
    simp [hG'def, hηW z hz]
  · simp [Function.update_of_ne h]

theorem exists_isDefectPairing {Ω : Opens (ComplexModel N)} {v : Fin N → ComplexModel N → ℝ}
    {i₀ : Fin N} (hv : SlotsAdmissible Ω v i₀) {G : ComplexModel N → ℝ} (hG : ContDiffOn ℝ ∞ G Ω)
    {F : ComplexModel N → ℝ} (hF : IsBoundedTest F) (hFΩ : tsupport F ⊆ Ω) :
    ∃ I, IsDefectPairing Ω v i₀ G F I := by
  obtain ⟨V, p, ν₁, ν₂, hVΩ, hFV, h₁, h₂⟩ := exists_witness hv hG hF.2.1 hFΩ
  exact ⟨_, V, p, ν₁, ν₂, hVΩ, hFV, h₁, h₂, rfl⟩

/-- **Additivity in the weight.** -/
theorem IsDefectPairing.add_weight {Ω : Opens (ComplexModel N)}
    {v : Fin N → ComplexModel N → ℝ} {i₀ : Fin N} (hv : SlotsAdmissible Ω v i₀)
    {G : ComplexModel N → ℝ} (hG : ContDiffOn ℝ ∞ G Ω) {F₁ F₂ : ComplexModel N → ℝ} {I₁ I₂ : ℝ}
    (hF₁ : IsBoundedTest F₁) (hF₂ : IsBoundedTest F₂) (hF₁Ω : tsupport F₁ ⊆ Ω)
    (hF₂Ω : tsupport F₂ ⊆ Ω) (h₁ : IsDefectPairing Ω v i₀ G F₁ I₁)
    (h₂ : IsDefectPairing Ω v i₀ G F₂ I₂) :
    IsDefectPairing Ω v i₀ G (fun z => F₁ z + F₂ z) (I₁ + I₂) := by
  obtain ⟨V, p, ν₁, ν₂, hVΩ, hKV, hν₁, hν₂⟩ := exists_witness hv hG
    (hF₁.2.1.union hF₂.2.1) (union_subset hF₁Ω hF₂Ω)
  have hF₁V : tsupport F₁ ⊆ V := subset_union_left.trans hKV
  have hF₂V : tsupport F₂ ⊆ V := subset_union_right.trans hKV
  have e₁ := h₁.unique hF₁ ⟨V, p, ν₁, ν₂, hVΩ, hF₁V, hν₁, hν₂, rfl⟩
  have e₂ := h₂.unique hF₂ ⟨V, p, ν₁, ν₂, hVΩ, hF₂V, hν₁, hν₂, rfl⟩
  refine ⟨V, p, ν₁, ν₂, hVΩ, (tsupport_add _ _).trans (union_subset hF₁V hF₂V), hν₁, hν₂, ?_⟩
  rw [integral_add (hF₁.integrable hν₁.2.1 hF₁V) (hF₂.integrable hν₁.2.1 hF₂V),
    integral_add (hF₁.integrable hν₂.2.1 hF₁V) (hF₂.integrable hν₂.2.1 hF₂V), e₁, e₂]
  ring

/-- **Locality in the weight.** Two weights that agree near `supp G` have the same pairing. -/
theorem IsDefectPairing.congr_weight {Ω : Opens (ComplexModel N)}
    {v : Fin N → ComplexModel N → ℝ} {i₀ : Fin N} (hv : SlotsAdmissible Ω v i₀)
    {G : ComplexModel N → ℝ} (hG : ContDiffOn ℝ ∞ G Ω) {F F' : ComplexModel N → ℝ} {I I' : ℝ}
    (hF : IsBoundedTest F) (hF' : IsBoundedTest F') (hFΩ : tsupport F ⊆ Ω)
    (hF'Ω : tsupport F' ⊆ Ω) {O : Set (ComplexModel N)} (hO : IsOpen O)
    (hGO : tsupport G ⊆ O) (hFF' : EqOn F F' O)
    (h : IsDefectPairing Ω v i₀ G F I) (h' : IsDefectPairing Ω v i₀ G F' I') : I = I' := by
  classical
  obtain ⟨V, p, ν₁, ν₂, hVΩ, hKV, hν₁, hν₂⟩ := exists_witness hv hG
    (hF.2.1.union hF'.2.1) (union_subset hFΩ hF'Ω)
  have hFV : tsupport F ⊆ V := subset_union_left.trans hKV
  have hF'V : tsupport F' ⊆ V := subset_union_right.trans hKV
  rw [h.unique hF ⟨V, p, ν₁, ν₂, hVΩ, hFV, hν₁, hν₂, rfl⟩,
    h'.unique hF' ⟨V, p, ν₁, ν₂, hVΩ, hF'V, hν₁, hν₂, rfl⟩]
  -- off `supp G` the two limits agree
  set D : Opens (ComplexModel N) := V ⊓ ⟨(tsupport G)ᶜ, (isClosed_tsupport G).isOpen_compl⟩
  have hres : ν₁.restrict D = ν₂.restrict D := by
    refine IsBTLimit.restrict_eq_of_eqOn hν₁ hν₂ inf_le_left fun i z hz => ?_
    by_cases hi : i = i₀
    · subst hi
      have : G z = 0 := image_eq_zero_of_notMem_tsupport hz.2
      simp [this]
    · simp [Function.update_of_ne hi]
  have hdiff : IsBoundedTest fun z => F z - F' z := hF.sub hF'
  have hdD : tsupport (fun z => F z - F' z) ⊆ D := by
    have hsub : tsupport (fun z => F z - F' z) ⊆ Oᶜ :=
      closure_minimal (fun z hz hzO => hz (by simp [hFF' hzO])) hO.isClosed_compl
    intro z hz
    refine ⟨(tsupport_sub _ _ |>.trans (union_subset hFV hF'V)) hz, fun hzG => hsub hz (hGO hzG)⟩
  have hint := congrArg (fun μ : Measure (ComplexModel N) => ∫ z, (F z - F' z) ∂μ) hres
  simp only [integral_restrict_of_tsupport hdD] at hint
  rw [integral_sub (hF.integrable hν₁.2.1 hFV) (hF'.integrable hν₁.2.1 hF'V),
    integral_sub (hF.integrable hν₂.2.1 hFV) (hF'.integrable hν₂.2.1 hF'V)] at hint
  linarith

/-! ### Biholomorphic invariance -/

/-- **The defect pairing is invariant under biholomorphic changes of coordinates.** If `τ : A → B`
is biholomorphic with inverse `σ`, the slots other than `i₀` satisfy `vb ∘ τ = va + π` with smooth
pluriharmonic gauges `π`, and the slot functions and weights correspond (`Gb ∘ τ = Ga`,
`Fb ∘ τ = Fa` on `A`), then the pairings on `B` and on `A` are equal. -/
theorem IsDefectPairing.comp_biholomorphic {A B : Opens (ComplexModel N)}
    {τ σ : ComplexModel N → ComplexModel N} (hAB : IsBiholomorphicPair A B τ σ)
    {va vb : Fin N → ComplexModel N → ℝ} {i₀ : Fin N} {π : Fin N → ComplexModel N → ℝ}
    (hπ : ∀ i, IsSmoothPluriharmonicOn A (π i))
    (hv : ∀ i, i ≠ i₀ → ∀ x ∈ A, vb i (τ x) = va i x + π i x)
    {Ga Gb Fa Fb : ComplexModel N → ℝ} (hG : ∀ x ∈ A, Gb (τ x) = Ga x)
    (hF : ∀ x ∈ A, Fb (τ x) = Fa x) (hFa : IsBoundedTest Fa) (hFaA : tsupport Fa ⊆ A)
    {I : ℝ} (hb : IsDefectPairing B vb i₀ Gb Fb I) : IsDefectPairing A va i₀ Ga Fa I := by
  classical
  obtain ⟨V, p, ν₁, ν₂, hVB, hFbV, h₁, h₂, rfl⟩ := hb
  have hτc : ContinuousOn τ A := hAB.holo.continuousOn
  have hσc : ContinuousOn σ B := hAB.holo_inv.continuousOn
  set A' : Opens (ComplexModel N) := ⟨A ∩ τ ⁻¹' V, hτc.isOpen_inter_preimage A.isOpen V.isOpen⟩
  have hA'A : A' ≤ A := fun x hx => hx.1
  have hpair : IsBiholomorphicPair A' V τ σ :=
    { holo := hAB.holo.mono hA'A
      holo_inv := hAB.holo_inv.mono hVB
      mapsTo := fun x hx => hx.2
      mapsTo_inv := fun w hw => ⟨hAB.mapsTo_inv (hVB hw), by
        show τ (σ w) ∈ V
        rw [hAB.right_inv w (hVB hw)]; exact hw⟩
      left_inv := fun x hx => hAB.left_inv x hx.1
      right_inv := fun w hw => hAB.right_inv w (hVB hw) }
  -- the gauge, vanishing in slot `i₀`
  set π' : Fin N → ComplexModel N → ℝ := Function.update π i₀ fun _ => 0
  have hπ' : ∀ i, IsSmoothPluriharmonicOn A' (fun z => -π' i z) := by
    intro i
    by_cases hi : i = i₀
    · subst hi
      have : (fun z => -π' i z) = fun _ => (0 : ℝ) := by funext z; simp [π']
      rw [this]
      exact ⟨contDiffOn_const, fun z _ => complexHessian_const 0 z⟩
    · have := ((hπ i).mono hA'A).neg
      simpa [π', Function.update_of_ne hi] using this
  have htrans (s : ComplexModel N → ℝ) (μ : Measure (ComplexModel N))
      (hμ : IsBTLimit V (Function.update vb i₀ fun z => s z) μ) (s' : ComplexModel N → ℝ)
      (hs : ∀ x ∈ A', s (τ x) = s' x) :
      IsBTLimit A' (Function.update va i₀ s') ((μ.restrict V).map σ) := by
    have h1 := hμ.comp_biholomorphic hpair
    have h2 := h1.add_pluriharmonic hπ'
    refine h2.congr fun i x hx => ?_
    by_cases hi : i = i₀
    · subst hi
      simp [π', hs x hx]
    · simp only [Function.update_of_ne hi, π']
      rw [hv i hi x hx.1]
      ring
  have hν₁' := htrans _ ν₁ h₁ (fun x => Ga x + p (τ x)) fun x hx => by rw [hG x hx.1]
  have hν₂' := htrans _ ν₂ h₂ (fun x => p (τ x)) fun x _ => rfl
  -- the weight lives in `A'`
  have hFaA' : tsupport Fa ⊆ A' := by
    intro x hx
    refine ⟨hFaA hx, ?_⟩
    have himg : τ '' tsupport Fa ⊆ tsupport Fb := by
      refine ((hτc.mono hFaA).image_closure).trans (closure_mono ?_)
      rintro _ ⟨y, hy, rfl⟩
      have hyA : y ∈ A := hFaA (subset_tsupport _ hy)
      show Fb (τ y) ≠ 0
      rw [hF y hyA]; exact hy
    exact hFbV (himg ⟨x, hx, rfl⟩)
  refine ⟨A', fun x => p (τ x), _, _, hA'A, hFaA', hν₁', hν₂', ?_⟩
  -- change of variables
  have hcv (μ : Measure (ComplexModel N)) :
      ∫ x, Fa x ∂((μ.restrict V).map σ) = ∫ w, Fb w ∂μ := by
    rw [integral_map ((hσc.mono hVB).aemeasurable V.isOpen.measurableSet)
      hFa.1.aestronglyMeasurable, ← integral_restrict_of_tsupport hFbV μ]
    refine setIntegral_congr_fun V.isOpen.measurableSet fun w hw => ?_
    rw [← hF (σ w) (hAB.mapsTo_inv (hVB hw)), hAB.right_inv w (hVB hw)]
  rw [hcv, hcv]

end

end SGPT.Foundations.Analysis.Pending.BedfordTaylorDefectPairing
