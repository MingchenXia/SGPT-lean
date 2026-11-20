import SGPT.PSH.SourceSubgeodesicEndpoints
import SGPT.PSH.SourceGeodesicOrder
import SGPT.Foundations.Analysis.Pending.ManifoldPluripolar

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set Filter
open scoped Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Actual source pole-witness equality of genuine original theta-PSH
potentials is EVERYWHERE equality, with no measure representative change. -/
theorem sourceThetaPSH_eq_of_quasiEverywhereEq
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {u v : M → EReal}
    (hu : (ofFixedModel n M).IsThetaPSH θ u)
    (hv : (ofFixedModel n M).IsThetaPSH θ v)
    (heq : SourceQuasiEverywhere (n := n) (fun x ↦ u x = v x)) : u = v := by
  have hn := (sourceQuasiEverywhere_iff_native _).mp heq
  apply le_antisymm
  · exact (sourceQuasiEverywhere_le_iff hu hv).mp
      ((sourceQuasiEverywhere_iff_native _).mpr (hn.mono fun _ hx ↦ hx.le))
  · exact (sourceQuasiEverywhere_le_iff hv hu).mp
      ((sourceQuasiEverywhere_iff_native _).mpr (hn.mono fun _ hx ↦ hx.ge))

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]
  {omega : KahlerBackground n M}
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

/-- A SAME genuine original normalized interior curve determines BOTH
assigned endpoint functions, using actual original pluripolar witnesses. -/
theorem SourceSubgeodesicFrom.endpoints_unique
    {curve : ℝ → M → EReal} {u₀ u₁ v₀ v₁ : M → EReal}
    (h : SourceSubgeodesicFrom omega θ curve u₀ u₁)
    (k : SourceSubgeodesicFrom omega θ curve v₀ v₁) : u₀ = v₀ ∧ u₁ = v₁ := by
  have hleft : QuasiEverywhereEq (n := n) u₀ v₀ :=
    quasiEverywhereEq_trans
      (QuasiEverywhereEq.symm ((sourceQuasiEverywhere_iff_native _).mp
        (sourceSubgeodesicLeftLimit_quasiEverywhere h)))
      ((sourceQuasiEverywhere_iff_native _).mp (sourceSubgeodesicLeftLimit_quasiEverywhere k))
  have hright : QuasiEverywhereEq (n := n) u₁ v₁ :=
    quasiEverywhereEq_trans
      (QuasiEverywhereEq.symm ((sourceQuasiEverywhere_iff_native _).mp
        (sourceSubgeodesicRightLimit_quasiEverywhere h)))
      ((sourceQuasiEverywhere_iff_native _).mp (sourceSubgeodesicRightLimit_quasiEverywhere k))
  exact ⟨sourceThetaPSH_eq_of_quasiEverywhereEq h.1 k.1
      ((sourceQuasiEverywhere_iff_native _).mpr hleft),
    sourceThetaPSH_eq_of_quasiEverywhereEq h.2.1 k.2.1
      ((sourceQuasiEverywhere_iff_native _).mpr hright)⟩

/-- Equality ONLY on the actual open unit interval suffices; the existing
genuine source product/GLOBAL-L1 congruence removes off-time values. -/
theorem SourceSubgeodesicFrom.endpoints_unique_of_eqOn_Ioo
    {curve other : ℝ → M → EReal} {u₀ u₁ v₀ v₁ : M → EReal}
    (h : SourceSubgeodesicFrom omega θ curve u₀ u₁)
    (k : SourceSubgeodesicFrom omega θ other v₀ v₁)
    (heq : EqOn curve other (Ioo (0 : ℝ) 1)) : u₀ = v₀ ∧ u₁ = v₁ :=
  h.endpoints_unique (k.congr_Ioo fun _ ht ↦ (heq ht).symm)

/-- The original open-family endpoint uniqueness on its NONEMPTY physical
interval. Strict a<b is essential; the actual empty-interval obstruction
is proved below instead of silently claiming the unrestricted remark. -/
theorem SourceSubgeodesicClosedInterval.endpoints_unique_of_eqOn_Ioo
    {a b : ℝ} {curve other : ℝ → M → EReal}
    (h : SourceSubgeodesicClosedInterval omega θ a b curve)
    (k : SourceSubgeodesicClosedInterval omega θ a b other)
    (hab : a < b) (heq : EqOn curve other (Ioo a b)) :
    curve a = other a ∧ curve b = other b := by
  apply h.2.endpoints_unique_of_eqOn_Ioo k.2
  intro t ht
  apply heq
  have hpos := mul_pos ht.1 (sub_pos.mpr hab)
  have hpos' := mul_pos (sub_pos.mpr ht.2) (sub_pos.mpr hab)
  exact ⟨by nlinarith, by nlinarith⟩

/-- A CONCRETE produced obstruction to an unrestricted a≤b open-family
uniqueness claim. Two genuine constant closed[a,a] completions agree on
EMPTY(a,a), yet their actual endpoint functions differ at a produced
nonpole finite point. The valid closed degenerate convention is preserved. -/
theorem sourceOpenDegenerate_endpoint_obstruction
    (omega : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {u : M → EReal}
    (hu : (ofFixedModel n M).IsThetaPSH θ u) (a : ℝ) :
    ∃ curve other : ℝ → M → EReal,
      SourceSubgeodesicClosedInterval omega θ a a curve ∧
      SourceSubgeodesicClosedInterval omega θ a a other ∧
      EqOn curve other (Ioo a a) ∧ curve a ≠ other a := by
  let v : M → EReal := fun x ↦ u x + ((1 : ℝ) : EReal)
  have hn := (isThetaPSH_iff_nativeThetaPotential θ u).mp hu
  have hv : (ofFixedModel n M).IsThetaPSH θ v :=
    (isThetaPSH_iff_nativeThetaPotential θ v).mpr (hn.add_const 1)
  refine ⟨fun _ ↦ u, fun _ ↦ v,
    (sourceSubgeodesicClosedInterval_self_iff omega θ a _).mpr hu,
    (sourceSubgeodesicClosedInterval_self_iff omega θ a _).mpr hv, ?_, ?_⟩
  · intro t ht
    exact False.elim ((lt_irrefl a) (ht.1.trans ht.2))
  · change u ≠ v
    intro heq
    obtain ⟨x⟩ : Nonempty M := inferInstance
    obtain ⟨y, _hy, hbot⟩ := hn.2 x univ isOpen_univ (mem_univ x)
    have htop := hn.1.quasiPlurisubharmonic.ne_top y
    have hf : ((u y).toReal : EReal) = u y := EReal.coe_toReal htop hbot
    have hpoint : u y = u y + ((1 : ℝ) : EReal) := congrFun heq y
    have hadd : u y + ((1 : ℝ) : EReal) = (((u y).toReal + 1 : ℝ) : EReal) := by
      rw [EReal.coe_add]
      exact congrArg (fun z : EReal ↦ z + ((1 : ℝ) : EReal)) hf.symm
    have hreal := congrArg EReal.toReal hpoint
    rw [hadd, EReal.toReal_coe] at hreal
    linarith

end SGPT.PSH.VariableComplexAtlas
