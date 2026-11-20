import SGPT.Envelopes.DNTC11Density
import SGPT.Envelopes.DNTMixedContact

/-!
# The Di Nezza–Trapani contact formula for mixed products, obstacles with bounded complex Hessian

Lane S53 (`claude-dnt-c11`).  Book `thm:DNTcontact` in its mixed form: `θ₁, …, θₙ` closed real
`(1,1)`-forms, `φᵢ ∈ PSH(X, θᵢ)` and continuous `fᵢ ≥ φᵢ` with bounded complex Hessian;
`E = ⋂ᵢ {φᵢ = fᵢ}`.

The mixed Monge–Ampère measure `θ_{1,f₁} ∧ ⋯ ∧ θ_{n,fₙ}` of the obstacles is the polarization of the
top powers: for `S ⊆ {1, …, n}`, `θ_S = ∑_{i∈S} θᵢ`, `f_S = ∑_{i∈S} fᵢ`,

  `θ_{1,f₁} ∧ ⋯ ∧ θ_{n,fₙ} = (1/n!) ∑_S (-1)^{n-|S|} (θ_S + ddᶜf_S)ⁿ`

(the polarization identity of the symmetric `n`-linear form `(α₁, …, αₙ) ↦ α₁ ∧ ⋯ ∧ αₙ` on
`(1,1)`-forms, applied to the measurable forms `θᵢ + ddᶜfᵢ`), each `(θ_S + ddᶜf_S)ⁿ` being the
absolutely continuous measure `c11TopMeasure ω θ_S f_S` of `DNTC11Main` (density formula
`c11TopMeasure_image_eq`).  `c11MixedReal ω θ f A` is this signed measure of a set `A`.

* `globalMixedMeasure_restrict_mixedContact_toReal_eq`: for every measurable `A`,
  `⟨θ_{1,φ₁} ∧ ⋯ ∧ θ_{n,φₙ}⟩(A ∩ E) = c11MixedReal ω θ f (A ∩ E)`, i.e.
  `𝟙_E ⟨θ_{1,φ₁} ∧ ⋯ ∧ θ_{n,φₙ}⟩ = 𝟙_E θ_{1,f₁} ∧ ⋯ ∧ θ_{n,fₙ}`; on `E` all the top powers involved
  have nonnegative densities (`ae_c11Ratio_nonneg_of_contact`), so no positive part matters.

Proof: the book's Step 1 (polarization from the diagonal case), as in lane S48's
`DNT.globalMixedMeasure_restrict_mixedContact_eq`, with the diagonal formula for obstacles with
bounded complex Hessian (`diagonalPotentialMeasure_restrict_contact_eq`) applied to `θ_S, φ_S, f_S`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Envelopes.DNTC11

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.GlobalNonPluripolar
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Foundations.Analysis.Pending.ManifoldTubePositivity
open SGPT.Foundations.Analysis.Pending.GlobalMultilinearExpansion
open SGPT.Okounkov SGPT.Okounkov.TranscendentalWNReg
open SGPT.PSH.VariableComplexAtlas
open SGPT.Envelopes.DNT

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-! ### Closure of the class under finite sums -/

omit [IsComplexManifold n M] in
theorem HasBoundedComplexHessian.add {f g : M → ℝ} (hf : HasBoundedComplexHessian (n := n) f)
    (hg : HasBoundedComplexHessian (n := n) g) :
    HasBoundedComplexHessian (n := n) (fun x => f x + g x) := by
  refine ⟨hf.1.add hg.1, fun e => ?_⟩
  obtain ⟨h, hh⟩ := hf.2 e
  obtain ⟨h', hh'⟩ := hg.2 e
  exact ⟨_, hh.add hh'⟩

theorem HasBoundedComplexHessian.finset_sum {ι : Type*} (S : Finset ι) {f : ι → M → ℝ}
    (hf : ∀ i, HasBoundedComplexHessian (n := n) (f i)) :
    HasBoundedComplexHessian (n := n) (fun x => ∑ i ∈ S, f i x) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simpa only [Finset.sum_empty] using
        HasBoundedComplexHessian.of_chartSmooth (ProductTestForms.chartSmooth_const (n := n)
          (M := M) 0)
  | insert j S hj ih =>
      have h := (hf j).add ih
      have heq : (fun x => f j x + ∑ i ∈ S, f i x) = fun x => ∑ i ∈ insert j S, f i x := by
        funext x
        rw [Finset.sum_insert hj]
      exact heq ▸ h

/-! ### The mixed measure -/

section Measures

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- **The mixed Monge–Ampère measure `θ_{1,f₁} ∧ ⋯ ∧ θ_{n,fₙ}`** of obstacles with bounded complex
Hessian, as a signed measure of the set `A`: the polarization
`(1/n!) ∑_S (-1)^{n-|S|} (θ_S + ddᶜf_S)ⁿ(A)` of the top powers `c11TopMeasure ω θ_S f_S`. -/
def c11MixedReal (w : KahlerBackground n M) (θ : Fin n → ClosedRealOneOneForm n M)
    (f : Fin n → M → ℝ) (A : Set M) : ℝ :=
  ((n.factorial : ℝ))⁻¹ * ∑ S : Finset (Fin n), (-1 : ℝ) ^ (n - S.card) *
    (c11TopMeasure w (sumForm S (fun _ => (1 : ℝ)) θ) (fun x => ∑ i ∈ S, f i x) A).toReal

/-- **The Di Nezza–Trapani contact formula for mixed products** (book `thm:DNTcontact`), for obstacles
with bounded complex Hessian: `⟨θ_{1,φ₁} ∧ ⋯ ∧ θ_{n,φₙ}⟩(A ∩ E) = (θ_{1,f₁} ∧ ⋯ ∧ θ_{n,fₙ})(A ∩ E)` for
every measurable `A`, `E = ⋂ᵢ {φᵢ = fᵢ}`. -/
theorem globalMixedMeasure_restrict_mixedContact_toReal_eq (w : KahlerBackground n M)
    (θ : Fin n → ClosedRealOneOneForm n M) {u : Fin n → M → EReal}
    (hu : ∀ i, IsThetaPshPotential (θ i).val (u i)) {f : Fin n → M → ℝ}
    (hf : ∀ i, HasBoundedComplexHessian (n := n) (f i)) (hle : ∀ i x, u i x ≤ (f i x : EReal))
    {A : Set M} (hA : MeasurableSet A) :
    ((globalMixedMeasure θ u fun i => (hu i).1).restrict (mixedContactSet u f) A).toReal =
      c11MixedReal w θ f (A ∩ mixedContactSet u f) := by
  classical
  set E := mixedContactSet u f with hE
  have hEm : MeasurableSet E := by
    rw [hE, mixedContactSet_eq_iInter]
    exact (isClosed_iInter fun i =>
      isClosed_contact_of_continuous (hu i).1 (hf i).1 (hle i)).measurableSet
  rw [Measure.restrict_apply hA]
  set μ : (Fin n → Fin n) → Measure M := fun g =>
    globalMixedMeasure (fun j => θ (g j)) (fun j => u (g j)) (fun j => (hu (g j)).1) with hμ
  have hfin : ∀ g, μ g (A ∩ E) ≠ ⊤ := fun g => by
    have := globalMixedMeasure_isFiniteMeasure w (fun j => (hu (g j)).1)
    exact measure_ne_top _ _
  set d : (Fin n → Fin n) → ℝ := fun g => (μ g (A ∩ E)).toReal with hd
  -- the diagonal identities for `θ_S, φ_S, f_S`
  have hS : ∀ S : Finset (Fin n), ∑ g : Fin n → Fin n with ∀ j, g j ∈ S, d g =
      (c11TopMeasure w (sumForm S (fun _ => (1 : ℝ)) θ) (fun x => ∑ i ∈ S, f i x)
        (A ∩ E)).toReal := by
    intro S
    have hfS := HasBoundedComplexHessian.finset_sum (n := n) S hf
    have hleS : ∀ x, sumPot S (fun _ => (1 : ℝ)) u x ≤ ((∑ i ∈ S, f i x : ℝ) : EReal) := by
      intro x
      simp only [sumPot, EReal.coe_one, one_mul]
      rw [ereal_coe_finset_sum]
      exact Finset.sum_le_sum fun i _ => hle i x
    have hES : E ⊆ {x | sumPot S (fun _ => (1 : ℝ)) u x = ((∑ i ∈ S, f i x : ℝ) : EReal)} := by
      intro x hx
      simp only [mem_ofPred_eq, sumPot, EReal.coe_one, one_mul]
      rw [ereal_coe_finset_sum]
      exact Finset.sum_congr rfl fun i _ => hx i
    have hdnt := diagonalPotentialMeasure_restrict_contact_eq w (sumForm S (fun _ => (1 : ℝ)) θ)
      (MixedProductIntegralPolarization.isThetaPshPotential_subsetSum hu S) hfS hleS
    have h2 := congrArg (fun ν : Measure M => ν (A ∩ E)) hdnt
    simp only at h2
    rw [Measure.restrict_apply (hA.inter hEm), Measure.restrict_apply (hA.inter hEm),
      inter_eq_left.mpr (inter_subset_right.trans hES),
      MixedProductIntegralPolarization.diagonal_subsetSum_eq_sum_selected w hu S,
      Measure.finsetSum_apply] at h2
    rw [← h2, ENNReal.toReal_sum fun g _ => hfin g]
  have hperm : ∀ σ : Equiv.Perm (Fin n), d σ = d id := by
    intro σ
    have h1 : μ σ = μ id := GlobalSlotPerm.globalMixedMeasure_perm (fun i => (hu i).1) σ
    simp only [hd, h1]
  have hpol := PolarizationAlgebra.sum_powerset_signed_eq_factorial_mul d hperm
  simp only [hS] at hpol
  have hn : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have hid : d id = (μ id (A ∩ E)).toReal := rfl
  have hμid : μ id = globalMixedMeasure θ u fun i => (hu i).1 := rfl
  rw [← hμid, ← hid, c11MixedReal, hpol, ← mul_assoc, inv_mul_cancel₀ hn, one_mul]

/-- The mixed measure of the obstacles is nonnegative on subsets of the common contact set. -/
theorem c11MixedReal_nonneg_of_mixedContact (w : KahlerBackground n M)
    (θ : Fin n → ClosedRealOneOneForm n M) {u : Fin n → M → EReal}
    (hu : ∀ i, IsThetaPshPotential (θ i).val (u i)) {f : Fin n → M → ℝ}
    (hf : ∀ i, HasBoundedComplexHessian (n := n) (f i)) (hle : ∀ i x, u i x ≤ (f i x : EReal))
    {A : Set M} (hA : MeasurableSet A) :
    0 ≤ c11MixedReal w θ f (A ∩ mixedContactSet u f) := by
  rw [← globalMixedMeasure_restrict_mixedContact_toReal_eq w θ hu hf hle hA]
  exact ENNReal.toReal_nonneg

/-- **`thm:DNTcontact` for mixed products, source-facing form**, for obstacles with bounded complex
Hessian: the source mixed non-pluripolar product `sourceMixedNonPluripolarMeasure` restricted to
`E = ⋂ᵢ {φᵢ = fᵢ}` is the mixed measure `θ_{1,f₁} ∧ ⋯ ∧ θ_{n,fₙ}` restricted to `E`. -/
theorem sourceMixedNonPluripolarMeasure_restrict_mixedContact_toReal_eq (w : KahlerBackground n M)
    (θ : Fin n → AtlasClosedRealOneOneForm (ofFixedModel n M)) {u : Fin n → M → EReal}
    (hu : ∀ i, (ofFixedModel n M).IsThetaPSH (θ i) (u i)) {f : Fin n → M → ℝ}
    (hf : ∀ i, HasBoundedComplexHessian (n := n) (f i)) (hle : ∀ i x, u i x ≤ (f i x : EReal))
    {A : Set M} (hA : MeasurableSet A) :
    ((sourceMixedNonPluripolarMeasure θ u hu).restrict (mixedContactSet u f) A).toReal =
      c11MixedReal w (fun i => atlasClosedFormToNative (θ i)) f (A ∩ mixedContactSet u f) :=
  globalMixedMeasure_restrict_mixedContact_toReal_eq w (fun i => atlasClosedFormToNative (θ i))
    (fun i => (isThetaPSH_iff_nativeThetaPotential (θ i) (u i)).mp (hu i)) hf hle hA

end Measures

end SGPT.Envelopes.DNTC11
