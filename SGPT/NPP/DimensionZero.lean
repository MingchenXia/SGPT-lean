import SGPT.PSH.SourceCapacity
import SGPT.Foundations.Analysis.Pending.ZeroDimensionalGlobalMixedMass
import SGPT.Foundations.Analysis.Pending.RooftopDimZero

/-!
# Non-pluripolar products on a zero-dimensional connected manifold

Source `rmk:npp:L275` (chapter `chapter_npp.tex`, Section "Properties of
non-pluripolar products"): when the connected compact manifold `X` has dimension
`0`, it is a single point, the non-pluripolar product `θ_φ^n` (the empty wedge
product) is the current of integration at that point, every `θ`-psh function has
mass `1`, so `PSH(X,θ)_{>0} = PSH(X,θ)`, and `PSH(X,θ) ≅ ℝ`.

All statements use the source objects: the original `θ`-psh predicate
`IsThetaPSH` on the fixed-model atlas, and the original diagonal non-pluripolar
measure `sourcePotentialNonPluripolarMeasure`.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.NPP

open Set MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open SGPT.PSH.VariableComplexAtlas

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel 0) M]
  [IsComplexManifold 0 M]

/-- A connected complex manifold of dimension `0` has exactly one point. -/
theorem subsingleton_of_dim_zero [ConnectedSpace M] : Subsingleton M := by
  let : DiscreteTopology M := discreteTopology_iff_isOpen_singleton.mpr
    (RooftopDimZero.isOpen_singleton_of_dim_zero rfl)
  exact subsingleton_of_preconnected_totallyDisconnected

/-- In dimension `0`, a function is `θ`-psh in the source sense iff it is
finite everywhere. -/
theorem isThetaPSH_iff_finite_of_dim_zero
    (θ : AtlasClosedRealOneOneForm (ofFixedModel 0 M)) (u : M → EReal) :
    (ofFixedModel 0 M).IsThetaPSH θ u ↔ ∀ x, u x ≠ ⊤ ∧ u x ≠ ⊥ := by
  rw [isThetaPSH_iff_nativeThetaPotential]
  constructor
  · intro hu x
    exact ⟨hu.1.quasiPlurisubharmonic.ne_top x,
      RooftopDimZero.ne_bot_of_locallyNondegenerate_of_dim_zero rfl hu.2 x⟩
  · intro hu
    exact RooftopDimZero.isThetaPshPotential_of_dim_zero rfl
      (LocalPotentials.closedRealOneOne_hasLocalPotentials _)
      (fun x => (hu x).1) (fun x => (hu x).2)

/-- Every real constant is `θ`-psh in dimension `0`. -/
theorem isThetaPSH_const_of_dim_zero
    (θ : AtlasClosedRealOneOneForm (ofFixedModel 0 M)) (c : ℝ) :
    (ofFixedModel 0 M).IsThetaPSH θ (fun _ => (c : EReal)) :=
  (isThetaPSH_iff_finite_of_dim_zero θ _).mpr fun _ =>
    ⟨EReal.coe_ne_top c, EReal.coe_ne_bot c⟩

/-- Source `rmk:npp:L275`, `PSH(X,θ) ≅ ℝ`: on a connected zero-dimensional
manifold, evaluation at the unique point is a bijection from the source
`θ`-psh functions onto `ℝ`, with inverse the constant functions. -/
def sourceThetaPSHEquivReal_of_dim_zero [ConnectedSpace M]
    (θ : AtlasClosedRealOneOneForm (ofFixedModel 0 M)) (x₀ : M) :
    {u : M → EReal // (ofFixedModel 0 M).IsThetaPSH θ u} ≃ ℝ where
  toFun u := (u.1 x₀).toReal
  invFun c := ⟨fun _ => (c : EReal), isThetaPSH_const_of_dim_zero θ c⟩
  left_inv u := by
    let : Subsingleton M := subsingleton_of_dim_zero
    apply Subtype.ext
    funext y
    have hfin := (isThetaPSH_iff_finite_of_dim_zero θ u.1).mp u.2 x₀
    rw [Subsingleton.elim y x₀]
    exact EReal.coe_toReal hfin.1 hfin.2
  right_inv c := by
    simp only [EReal.toReal_coe]

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- Source `rmk:npp:L275`: on a connected zero-dimensional compact manifold the
non-pluripolar product `θ_φ^0` of every source `θ`-psh `φ` is the Dirac mass
(the current of integration) at the unique point. -/
theorem sourcePotentialNonPluripolarMeasure_eq_dirac_of_dim_zero [ConnectedSpace M]
    (θ : AtlasClosedRealOneOneForm (ofFixedModel 0 M)) (u : M → EReal)
    (hu : (ofFixedModel 0 M).IsThetaPSH θ u) (x₀ : M) :
    sourcePotentialNonPluripolarMeasure θ u hu = Measure.dirac x₀ := by
  let : Subsingleton M := subsingleton_of_dim_zero
  have hcount := (ZeroDimensionalGlobalMixedMass.global_empty_mixed_measure_eq_count
    (M := M) (fun _ => atlasClosedFormToNative θ) (fun _ => u)
    (fun _ => ((isThetaPSH_iff_nativeThetaPotential θ u).mp hu).1)).1
  have hc : sourcePotentialNonPluripolarMeasure θ u hu = Measure.count := hcount
  rw [hc]
  ext s hs
  rw [Measure.count_apply hs, Measure.dirac_apply' _ hs]
  by_cases hx : x₀ ∈ s
  · have hsu : s = univ := eq_univ_of_forall fun y => Subsingleton.elim x₀ y ▸ hx
    subst hsu
    have hU : Nonempty (Unique M) := ⟨uniqueOfSubsingleton x₀⟩
    rw [Set.encard_univ, ENat.card_eq_one_iff_unique.mpr hU]
    simp
  · have hse : s = ∅ := eq_empty_of_forall_notMem fun y hy =>
      hx (Subsingleton.elim y x₀ ▸ hy)
    subst hse
    simp

/-- Source `rmk:npp:L275`: every source `θ`-psh function has total
non-pluripolar mass `1` on a connected zero-dimensional compact manifold. -/
theorem sourcePotentialNonPluripolarMass_eq_one_of_dim_zero [ConnectedSpace M]
    (θ : AtlasClosedRealOneOneForm (ofFixedModel 0 M)) (u : M → EReal)
    (hu : (ofFixedModel 0 M).IsThetaPSH θ u) :
    sourcePotentialNonPluripolarMeasure θ u hu univ = 1 := by
  obtain ⟨x₀⟩ := (inferInstance : Nonempty M)
  rw [sourcePotentialNonPluripolarMeasure_eq_dirac_of_dim_zero θ u hu x₀,
    Measure.dirac_apply_of_mem (mem_univ x₀)]

/-- Source `rmk:npp:L275`, `PSH(X,θ)_{>0} = PSH(X,θ)`: in dimension `0` every
source `θ`-psh function has positive non-pluripolar mass. -/
theorem sourcePositiveMass_of_dim_zero [ConnectedSpace M]
    (θ : AtlasClosedRealOneOneForm (ofFixedModel 0 M)) (u : M → EReal)
    (hu : (ofFixedModel 0 M).IsThetaPSH θ u) :
    0 < sourcePotentialNonPluripolarMeasure θ u hu univ := by
  rw [sourcePotentialNonPluripolarMass_eq_one_of_dim_zero θ u hu]
  exact zero_lt_one

end SGPT.NPP
