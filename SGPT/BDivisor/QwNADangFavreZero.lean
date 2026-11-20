import SGPT.BDivisor.BDivNSDangFavre
import SGPT.NPP.DimensionZero
import SGPT.Foundations.Analysis.Pending.ZeroDimensionalGlobalMixedMass
import SGPT.Foundations.Analysis.Pending.ConcentratedCurrentNef

/-!
# The Dang--Favre comparison in dimension zero


Source `rmk:bdiv:L749` (`chapter_bdiv.tex`): the transcendental intersection theory of nef
b-divisors coincides with the Dang--Favre one.  `SGPT.BDivisor.DangFavre` (file
`BDivNSDangFavre.lean`) proves the transcendental content of the comparison over a compact
Kähler manifold of positive dimension `m + 1`: (a) the product equals the classical
intersection number `∫_Y θ_1 ∧ ⋯ ∧ θ_n` of every common nef realization, (b) the Dang--Favre limit
formula along decreasing nets, (c) the infimum formula, (d) the uniqueness of a function with
these properties.  Here the same four statements are proved in **dimension zero** (`X` a
compact connected complex manifold of dimension `0`, i.e. a point): the tuple of b-divisors is
empty, its product is `1` (`source_nefIntersection_dim_zero`), and so is the classical intersection
number `∫_Y 1 = ∫_Y ω⁰` on every model `Y` (`slotIntegral_eq_one_of_dim_zero`; a model of a point
is a point).  In dimension zero the realization conditions on the (empty) tuples of forms are
vacuous, so they are not repeated.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.BDivisor.DangFavre

open Filter Set MeasureTheory
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending
  SGPT.Hodge.BDivChain.NativeDraft SGPT.Hodge.BDivChain.NativeDraft.VolumeNetDraft
  SGPT.Hodge.BDivChain.SourceNefIntersectionDraft
  SGPT.Foundations.Analysis.Pending.NefMixedMass SGPT.Foundations.Analysis.Pending.IntegrationCurrent

/-- **The classical intersection number in dimension zero**: on a compact connected complex
manifold `Y` of dimension `0` (a point), the slot integral of the empty tuple of forms,
`∫_Y ω⁰ = ∫_Y 1`, is `1`. -/
theorem slotIntegral_eq_one_of_dim_zero {Y : Type*} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel 0) Y] [IsComplexManifold 0 Y] [CompactSpace Y] [ConnectedSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] (w : KahlerBackground 0 Y)
    (θ : Fin 0 → ClosedRealOneOneForm 0 Y) : slotIntegral w θ = 1 := by
  have hθ : θ = fun _ => w.form := funext fun i => i.elim0
  subst hθ
  rw [ConcentratedCurrentNef.slotIntegral_const_form_eq]
  have hω : ∀ _ : Fin 0, ThetaPlurisubharmonic w.form.val (fun _ => (0 : EReal)) := fun _ =>
    ((LocalPotentials.isThetaPshPotential_zero_iff w.form).mpr w.isSemipositive).1
  have hvol : kahlerVolume w = GlobalNonPluripolar.globalMixedMeasure (fun _ : Fin 0 => w.form)
      (fun _ _ => (0 : EReal)) hω := rfl
  have h := (ZeroDimensionalGlobalMixedMass.global_empty_mixed_measure_eq_count
    (fun _ : Fin 0 => w.form) (fun _ _ => (0 : EReal)) hω).2.1
  have : Subsingleton Y := SGPT.NPP.subsingleton_of_dim_zero
  have hcard : Nat.card Y = 1 := Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩
  rw [Measure.real, hvol, h, hcard]
  simp

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel 0) X]
  [IsComplexManifold 0 X] [CompactSpace X] [ConnectedSpace X]

local notation "Sys0" => ModelSystem.blowup 0 X

/-- The classical intersection number `∫_Y θ_1 ∧ ⋯ ∧ θ_n` of a tuple of forms on a model `Y`
(read with the Borel structure of `Y`), here for `n = 0`. -/
theorem modelSlotIntegral_eq_one_of_dim_zero (π : (Sys0).Model)
    (κ : KahlerBackground 0 π.1.carrier) (θ : Fin 0 → ClosedRealOneOneForm 0 π.1.carrier) :
    (letI : MeasurableSpace π.1.carrier := borel π.1.carrier
     slotIntegral κ θ) = 1 := by
  let : MeasurableSpace π.1.carrier := borel π.1.carrier
  have : BorelSpace π.1.carrier := ⟨rfl⟩
  have : ConnectedSpace π.1.carrier := Modification.IsBlowupModel.connectedSpace π.2
  exact slotIntegral_eq_one_of_dim_zero κ θ

/-- **`rmk:bdiv:L749`, (a) in dimension zero**: the b-divisor product of the (empty) tuple `C`
equals the classical intersection number on every model `Y` with every Kähler form (the
realization conditions are vacuous), both being `1`. -/
theorem nefIntersection_toReal_eq_slotIntegral_of_dim_zero (C : Fin 0 → WeilFamilyAny Sys0)
    (π : (Sys0).Model) (κ : KahlerBackground 0 π.1.carrier)
    (θ : Fin 0 → ClosedRealOneOneForm 0 π.1.carrier) :
    (nefIntersection C).toReal =
      (letI : MeasurableSpace π.1.carrier := borel π.1.carrier
       slotIntegral κ θ) := by
  rw [modelSlotIntegral_eq_one_of_dim_zero π κ θ, source_nefIntersection_dim_zero C]
  rfl

/-- **`rmk:bdiv:L749`, (b) in dimension zero (the Dang--Favre limit formula)**: for nets `_C` of
(empty) tuples of b-divisors and any choice of models and Kähler forms realizing them, the `D i`
are nef and the classical intersection numbers converge to the b-divisor product `(D)`.  (In
dimension zero the monotonicity and convergence hypotheses of the positive-dimensional statement
`tendsto_intersection_of_antitone` are not needed.) -/
theorem tendsto_slotIntegral_of_dim_zero {J : Type*} [Preorder J]
    (_C : Fin 0 → J → WeilFamilyAny Sys0) (D : Fin 0 → WeilFamilyAny Sys0)
    (π : J → (Sys0).Model) (κ : ∀ j, KahlerBackground 0 (π j).1.carrier)
    (θ : ∀ j, Fin 0 → ClosedRealOneOneForm 0 (π j).1.carrier) :
    (∀ i, IsNefAny (D i)) ∧
      Tendsto (fun j => (letI : MeasurableSpace (π j).1.carrier := borel (π j).1.carrier
        slotIntegral (κ j) (θ j))) atTop (𝓝 (nefIntersection D).toReal) := by
  refine ⟨fun i => i.elim0, ?_⟩
  have h : (fun j => (letI : MeasurableSpace (π j).1.carrier := borel (π j).1.carrier
      slotIntegral (κ j) (θ j))) = fun _ => (nefIntersection D).toReal := by
    funext j
    rw [modelSlotIntegral_eq_one_of_dim_zero (π j) (κ j) (θ j), source_nefIntersection_dim_zero D]
    rfl
  rw [h]
  exact tendsto_const_nhds

/-- **`rmk:bdiv:L749`, (c) in dimension zero (the infimum formula)**: the product is the infimum
of the classical intersection numbers of the tuples dominating it, on the models with Kähler
forms (`X` Kähler). -/
theorem nefIntersection_toReal_eq_sInf_of_dim_zero (ω : KahlerBackground 0 X)
    (D : Fin 0 → WeilFamilyAny Sys0) :
    (nefIntersection D).toReal = sInf {x : ℝ | ∃ (C : Fin 0 → WeilFamilyAny Sys0)
      (π : (Sys0).Model) (κ : KahlerBackground 0 π.1.carrier)
      (θ : Fin 0 → ClosedRealOneOneForm 0 π.1.carrier), (∀ i, LEAny (D i) (C i)) ∧
        x = (letI : MeasurableSpace π.1.carrier := borel π.1.carrier
             slotIntegral κ θ)} := by
  have hS : {x : ℝ | ∃ (C : Fin 0 → WeilFamilyAny Sys0)
      (π : (Sys0).Model) (κ : KahlerBackground 0 π.1.carrier)
      (θ : Fin 0 → ClosedRealOneOneForm 0 π.1.carrier), (∀ i, LEAny (D i) (C i)) ∧
        x = (letI : MeasurableSpace π.1.carrier := borel π.1.carrier
             slotIntegral κ θ)} = {1} := by
    ext x
    rw [mem_singleton_iff]
    constructor
    · rintro ⟨C, π, κ, θ, -, rfl⟩
      exact modelSlotIntegral_eq_one_of_dim_zero π κ θ
    · rintro rfl
      exact ⟨D, ModelSystem.Model.root, ω, Fin.elim0, fun i => i.elim0,
        (modelSlotIntegral_eq_one_of_dim_zero ModelSystem.Model.root ω Fin.elim0).symm⟩
  rw [hS, csInf_singleton, source_nefIntersection_dim_zero D]
  rfl

/-- **`rmk:bdiv:L749`, (d) in dimension zero (uniqueness)**: a real function on tuples of
b-divisors which equals the classical intersection number on every tuple with a realization
coincides with the b-divisor product (`X` Kähler). -/
theorem eq_nefIntersection_of_dim_zero (ω : KahlerBackground 0 X)
    (I : (Fin 0 → WeilFamilyAny Sys0) → ℝ)
    (hcart : ∀ (C : Fin 0 → WeilFamilyAny Sys0) (π : (Sys0).Model)
      (κ : KahlerBackground 0 π.1.carrier) (θ : Fin 0 → ClosedRealOneOneForm 0 π.1.carrier),
      I C = (letI : MeasurableSpace π.1.carrier := borel π.1.carrier
             slotIntegral κ θ))
    (D : Fin 0 → WeilFamilyAny Sys0) :
    I D = (nefIntersection D).toReal := by
  rw [hcart D ModelSystem.Model.root ω Fin.elim0,
    nefIntersection_toReal_eq_slotIntegral_of_dim_zero D ModelSystem.Model.root ω Fin.elim0]

end SGPT.BDivisor.DangFavre

end
