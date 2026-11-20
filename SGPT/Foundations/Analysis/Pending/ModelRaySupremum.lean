import SGPT.Foundations.Analysis.Pending.FiniteUpperGapGeodesicSupremum
import SGPT.Foundations.Analysis.Pending.RelativePreceqRays

set_option autoImplicit false

/-!
# Actual model difference supremum and ray normalization

Xia SGPT PDF0103 Proposition 3.1.4 and PDF0159 Proposition 4.2.4.
The actual envelope competitor u-sup u identifies the nonpole EReal
difference supremum with the genuine global supremum. Model mass
produces nonemptiness. Source rays explicitly start from the model.
-/

open Set MeasureTheory

namespace SGPT.Foundations.Analysis.Pending.ModelRaySupremum

open FirstPass FirstPass.PositiveClasses DiagonalMass
  FiniteUpperGapGeodesicSupremum RelativePreceqClasses RelativePreceqRays

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]

/-- Genuine local nondegeneracy and the compact upper bound make the
actual global extended-real supremum finite. -/
theorem iSup_ne_top_ne_bot [Nonempty M] {θ : SmoothRealForm n M 2}
    {u : M → EReal} (hu : IsThetaPshPotential θ u) :
    (⨆ x, u x) ≠ ⊤ ∧ (⨆ x, u x) ≠ ⊥ := by
  obtain ⟨K, hK⟩ := hu.exists_global_upper_bound
  obtain ⟨y, _, hybot, _⟩ := hu.quasiPshPotential.exists_finite
    (Classical.arbitrary M) isOpen_univ (mem_univ _)
  exact ⟨ne_top_of_le_ne_top (EReal.coe_ne_top K) (iSup_le hK),
    ne_bot_of_le_ne_bot hybot (le_iSup u y)⟩

/-- The actual normalized translate is a genuine envelope competitor,
producing the model nonpole difference/global supremum identity. -/
theorem differenceSup_eq_iSup_of_envelope_eq [Nonempty M]
    {θ : SmoothRealForm n M 2} {φ u : M → EReal}
    (hφ : IsThetaPshPotential θ φ) (hfix : φ = singularityEnvelope θ φ)
    (hu : IsThetaPshPotential θ u) (hmore : MoreSingularOn u φ univ) :
    differenceSup u φ = ⨆ x, u x := by
  let S : ℝ := (⨆ x, u x).toReal
  have hf := iSup_ne_top_ne_bot hu
  have hS : (S : EReal) = ⨆ x, u x := EReal.coe_toReal hf.1 hf.2
  have hnonpos : (fun x => u x - (S : EReal)) ≤ 0 :=
    sub_const_nonpositive_of_le fun x => hS.symm ▸ le_iSup u x
  have htranslated : MoreSingularOn (fun x => u x - (S : EReal)) φ univ := by
    have h := (sameSingularityTypeOn_add_const u univ (-S)).1.trans hmore
    simpa only [sub_eq_add_neg, EReal.coe_neg] using h
  have hle : (fun x => u x - (S : EReal)) ≤ φ := by
    rw [hfix]
    exact le_singularityEnvelope (hu.sub_const S) hnonpos htranslated
  have hbound : u ≤ fun x => φ x + (S : EReal) := by
    intro x
    exact (EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot S))
      (Or.inl (EReal.coe_ne_top S))).mp (hle x)
  have hφ0 : φ ≤ 0 := hfix ▸ singularityEnvelope_le_zero θ φ
  apply le_antisymm
  · rw [← hS]
    exact iSup_le fun x => EReal.sub_le_of_le_add' (hbound x.val)
  · apply iSup_le
    intro x
    calc
      u x ≤ φ x + differenceSup u φ := le_add_differenceSup hφ hmore x
      _ ≤ 0 + differenceSup u φ := add_le_add (hφ0 x) le_rfl
      _ = differenceSup u φ := zero_add _

variable [MeasurableSpace M]

/-- Strictly positive actual model mass supplies a point of the
manifold, so model normalization needs no additional nonemptiness input. -/
theorem nonempty_of_modelPotential {θ : ClosedRealOneOneForm n M} {φ : M → EReal}
    (hφ : IsModelPotential θ φ) : Nonempty M := by
  obtain ⟨x, _⟩ := nonempty_of_measure_ne_zero
    (μ := diagonalPotentialMeasure θ φ hφ.plurisubharmonic)
    (ne_of_gt hφ.positive_mass)
  exact ⟨x⟩

/-- Source Proposition 3.1.4 for the actual positive-mass model predicate. -/
theorem differenceSup_eq_iSup {θ : ClosedRealOneOneForm n M} {φ u : M → EReal}
    (hφ : IsModelPotential θ φ) (hu : RelativePSHPreceq θ φ u) :
    differenceSup u φ = ⨆ x, u x := by
  let : Nonempty M := nonempty_of_modelPotential hφ
  exact differenceSup_eq_iSup_of_envelope_eq hφ.plurisubharmonic
    hφ.envelope_eq hu.1 hu.2

/-- The actual global supremum of a model is zero, without a bounded
reference or model-contact hypothesis. -/
theorem iSup_model_eq_zero {θ : ClosedRealOneOneForm n M} {φ : M → EReal}
    (hφ : IsModelPotential θ φ) : (⨆ x, φ x) = 0 := by
  let : Nonempty M := nonempty_of_modelPotential hφ
  rw [← differenceSup_eq_iSup hφ ⟨hφ.plurisubharmonic, .refl φ univ⟩]
  exact differenceSup_self hφ.plurisubharmonic

/-- Source Proposition 4.2.4: the actual ray beginning at its model has
a linear global supremum, produced from its genuine Perron restrictions. -/
theorem iSup_ray_eq {θ : ClosedRealOneOneForm n M} {φ : M → EReal}
    {hφ : IsModelPotential θ φ} {ℓ : ℝ → M → EReal}
    (hℓ : IsRayFromModel θ φ hφ ℓ) {t : ℝ} (ht : 0 ≤ t) :
    (⨆ x, ℓ t x) = ((t * (⨆ x, ℓ 1 x).toReal : ℝ) : EReal) := by
  let : Nonempty M := nonempty_of_modelPotential hφ
  let S : ℝ → ℝ := fun a => (⨆ x, ℓ a x).toReal
  have hscaled : ∀ b : ℝ, 0 < b → ∀ a : ℝ, 0 < a → a < b →
      S a = (a / b) * S b := by
    intro b hb a ha hab
    have hs : a / b ∈ Ioo (0 : ℝ) 1 :=
      ⟨div_pos ha hb, (div_lt_one hb).mpr hab⟩
    have htime : (0 : ℝ) + (a / b) * (b - 0) = a := by
      rw [sub_zero, zero_add, div_mul_cancel₀ _ hb.ne']
    have hg : ℓ a = finiteGeodesic θ.val φ (ℓ b) (a / b) := by
      have h := hℓ.1.2 0 b (by norm_num) hb (a / b) hs
      rwa [htime, hℓ.2] at h
    have hpa := (hℓ.1.1 a ha.le).relativePSHPreceq
    have hpb := (hℓ.1.1 b hb.le).relativePSHPreceq
    have hf := differenceSup_finiteGeodesic hφ.plurisubharmonic hpb.1 hpb.2 hs
    rw [← hg, differenceSup_eq_iSup hφ hpa, differenceSup_eq_iSup hφ hpb] at hf
    simpa only [S, EReal.toReal_coe] using congrArg EReal.toReal hf
  by_cases h0 : t = 0
  · subst t
    simp only [hℓ.2, iSup_model_eq_zero hφ, zero_mul, EReal.coe_zero]
  have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm h0)
  have hb : 0 < t + 1 := by linarith
  have hst := hscaled (t + 1) hb t htpos (by linarith)
  have hs1 := hscaled (t + 1) hb 1 (by norm_num) (by linarith)
  have heq : S t = t * S 1 := by
    rw [hst, hs1]
    ring
  have hf := iSup_ne_top_ne_bot (hℓ.1.1 t ht).plurisubharmonic
  calc
    (⨆ x, ℓ t x) = (S t : EReal) := (EReal.coe_toReal hf.1 hf.2).symm
    _ = ((t * S 1 : ℝ) : EReal) := congrArg (fun r : ℝ => (r : EReal)) heq

/-- The actual difference supremum also produces the pointwise linear
model bound for every time, without an input linear-bound contract. -/
theorem ray_le_model_add_linear {θ : ClosedRealOneOneForm n M} {φ : M → EReal}
    {hφ : IsModelPotential θ φ} {ℓ : ℝ → M → EReal}
    (hℓ : IsRayFromModel θ φ hφ ℓ) {t : ℝ} (ht : 0 ≤ t) :
    ℓ t ≤ fun x => φ x + ((t * (⨆ x, ℓ 1 x).toReal : ℝ) : EReal) := by
  have hp := (hℓ.1.1 t ht).relativePSHPreceq
  have h := le_add_differenceSup hφ.plurisubharmonic hp.2
  rwa [differenceSup_eq_iSup hφ hp, iSup_ray_eq hℓ ht] at h

/-- A genuine model-origin ray supplies the existing linear-bound
predicate with its actual time-one supremum and zero intercept. -/
theorem hasLinearBound_of_rayFromModel {θ : ClosedRealOneOneForm n M}
    {φ : M → EReal} {hφ : IsModelPotential θ φ} {ℓ : ℝ → M → EReal}
    (hℓ : IsRayFromModel θ φ hφ ℓ) : HasLinearBound φ ℓ := by
  refine ⟨(⨆ x, ℓ 1 x).toReal, 0, ?_⟩
  intro t ht x
  simpa only [add_zero, mul_comm] using ray_le_model_add_linear hℓ ht x

end

end SGPT.Foundations.Analysis.Pending.ModelRaySupremum
