import SGPT.Foundations.Analysis.Pending.PositiveCurrentPrescribedBottChernRepresentation
import SGPT.Foundations.Analysis.FirstPass.GlobalPotentialTransforms
import SGPT.Foundations.Analysis.FirstPass.ERealChordUSC
import Mathlib.Topology.Connected.LocallyConnected

set_option autoImplicit false

/-! # Natural componentwise normalization of original-current potentials

Full mathematical statements and ENTIRE proofs precede this source.
The original compact manifold need not be connected or nonempty.
Weak class preservation and degenerate Calabi--Yau remain separate obligations. -/

noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Distributions Topology ContDiff
namespace SGPT.Foundations.Analysis.Pending.ComponentwiseNormalizedCurrentPotentials
open FirstPass GlobalPotentialTransforms CurrentBottChernClass
  PositiveCurrentPrescribedBottChernRepresentation NaturalThetaPshGeometricCurrent
  GlobalPositiveCurrentACRestriction GlobalCurrentPotentials ThetaPshChartLimitGluing
  FiniteGlobalCurrentSmoothLocalDensity CanonicalCurrentFrame LelongPoincareDivisor
  StronglyPositiveForms
  _root_.SGPT.Foundations.Analysis.LocalCurrents

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

omit [IsComplexManifold n M] in
private theorem locally_constant_chart (c : M → ℝ)
    (hc : ∀ x, ∀ᶠ y in 𝓝 x, c y = c x) (e : ComplexChart n M)
    (z : ComplexModel n) (hz : z ∈ e.val.target) :
    (fun y => c (e.val.symm y)) =ᶠ[𝓝 z] fun _ => c (e.val.symm z) :=
  (e.val.symm.continuousAt hz).eventually (hc _)

/-- Actual finite component maxima normalize every genuine global quasi-PSH
potential without a connectedness or nonempty-manifold hypothesis. -/
theorem exists_componentwise_normalization [CompactSpace M]
    (u : M → EReal) (hu : IsGlobalQuasiPshPotential (n := n) u) :
    ∃ c : M → ℝ, (∀ x, ∀ᶠ y in 𝓝 x, c y = c x) ∧ ChartSmooth (n := n) c ∧
      (∀ x, u x - (c x : EReal) ≤ 0) ∧
      ∀ x, ∃ y ∈ connectedComponent x, u y - (c y : EReal) = 0 := by
  let : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace (ComplexModel n) M
  have hmax (x : M) : ∃ a ∈ connectedComponent x,
      IsMaxOn u (connectedComponent x) a ∧ u a ≠ ⊤ ∧ u a ≠ ⊥ := by
    obtain ⟨a,ha,hamax⟩ := UpperSemicontinuousOn.exists_isMaxOn
      ⟨x,mem_connectedComponent⟩ isClosed_connectedComponent.isCompact
      (hu.1.upperSemicontinuous.upperSemicontinuousOn (connectedComponent x))
    obtain ⟨y,hy,hyfin⟩ := hu.2 x (connectedComponent x)
      isOpen_connectedComponent mem_connectedComponent
    exact ⟨a,ha,hamax,hu.1.ne_top a,ne_bot_of_le_ne_bot hyfin (hamax hy)⟩
  let c (x : M) : ℝ := (sSup (u '' connectedComponent x)).toReal
  have hsup (x : M) : ∃ a ∈ connectedComponent x,
      (c x : EReal) = u a ∧ IsMaxOn u (connectedComponent x) a := by
    obtain ⟨a,ha,hamax,hat,hab⟩ := hmax x
    have hs : sSup (u '' connectedComponent x) = u a :=
      le_antisymm (sSup_le fun t ht => by obtain ⟨y,hy,rfl⟩ := ht; exact hamax hy)
        (le_sSup ⟨a,ha,rfl⟩)
    refine ⟨a,ha,?_,hamax⟩
    change ((sSup (u '' connectedComponent x)).toReal : EReal) = u a
    rw [hs,EReal.coe_toReal hat hab]
  have hc : ∀ x, ∀ᶠ y in 𝓝 x, c y = c x := by
    intro x
    filter_upwards [isOpen_connectedComponent.mem_nhds
      (mem_connectedComponent : x ∈ connectedComponent x)] with y hy
    dsimp only [c]
    rw [← connectedComponent_eq hy]
  refine ⟨c,hc,?_,?_,?_⟩
  · intro e z hz
    exact contDiffAt_const.congr_of_eventuallyEq (locally_constant_chart c hc e z hz)
      |>.contDiffWithinAt
  · intro x
    obtain ⟨a,ha,hcval,hamax⟩ := hsup x
    have hx : u x ≤ (c x : EReal) := (hamax mem_connectedComponent).trans_eq hcval.symm
    induction hux : u x using EReal.rec with
    | bot => simp
    | top => exact False.elim (hu.1.ne_top x hux)
    | coe t =>
      rw [← EReal.coe_sub]
      exact EReal.coe_le_coe_iff.mpr (sub_nonpos.mpr (EReal.coe_le_coe_iff.mp (hux ▸ hx)))
  · intro x
    obtain ⟨a,ha,hcval,_⟩ := hsup x
    have hca : c a = c x := by dsimp only [c]; rw [← connectedComponent_eq ha]
    refine ⟨a,ha,?_⟩
    rw [hca,← hcval,← EReal.coe_sub,sub_self,EReal.coe_zero]

omit [IsComplexManifold n M] in
private theorem smooth_ddc_zero_of_locally_constant (c : M → ℝ)
    (hc : ∀ x, ∀ᶠ y in 𝓝 x, c y = c x) (e : ComplexChart n M)
    (z : ComplexModel n) (hz : z ∈ e.val.target) :
    smoothDDC (fun y => c (e.val.symm y)) z = 0 := by
  rw [smoothDDC_congr (locally_constant_chart c hc e z hz),smoothDDC_const]

private theorem ddC_regular_zero (c : M → ℝ)
    (hc : ∀ x, ∀ᶠ y in 𝓝 x, c y = c x) (hs : ChartSmooth (n := n) c)
    (e : ComplexChart n M)
    (b : Module.Basis (Fin (Module.finrank ℝ (ComplexModel n))) ℝ (ComplexModel n)) :
    ddC (regularDistribution (Ω := chartTarget e) b.addHaar (fun z => c (e.val.symm z))
      ((hs e).continuousOn.locallyIntegrableOn (chartTarget e).isOpen.measurableSet)) = 0 := by
  rw [ddC_regular_eq_regularForm b.addHaar (hs e)]
  ext v φ
  rw [regularFormDistribution_apply]
  have hi : (fun z => φ z • smoothDDC (fun y => c (e.val.symm y)) z) =
      fun _ => (0 : RealForm n 2) := by
    funext z
    by_cases hz : z ∈ e.val.target
    · rw [smooth_ddc_zero_of_locally_constant c hc e z hz,smul_zero]
    · rw [image_eq_zero_of_notMem_tsupport (fun ht => hz (φ.tsupport_subset ht)),zero_smul]
  rw [hi,integral_zero]
  rfl

variable {m : ℕ} {X : Type*} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
  [CompactSpace X]

/-- Genuine componentwise normalization preserves theta and the literal SAME
original full-test current, including poles and disconnected manifolds. -/
theorem exists_normalized_theta_current (θ : ClosedRealOneOneForm (m + 1) X)
    (u : X → EReal) (hu : IsThetaPshPotential θ.val u) :
    ∃ (v : X → EReal) (hv : IsThetaPshPotential θ.val v),
      thetaPotentialCurrent θ.val v hv = thetaPotentialCurrent θ.val u hu ∧
      (∀ x, v x ≤ 0) ∧ ∀ x, ∃ y ∈ connectedComponent x, v y = 0 := by
  obtain ⟨c,hc,hs,hle,hzero⟩ := exists_componentwise_normalization u hu.quasiPshPotential
  let v : X → EReal := fun x => u x - (c x : EReal)
  have hv : IsThetaPshPotential θ.val v := by
    refine ⟨thetaPlurisubharmonic_sub_smooth hs ?_ hu.1,?_⟩
    · intro e z hz
      rw [smooth_ddc_zero_of_locally_constant c hc e z hz,add_zero]
    · intro x U hU hx
      obtain ⟨y,hy,huy⟩ := hu.2 x U hU hx
      refine ⟨y,hy,?_⟩
      change u y + -(c y : EReal) ≠ ⊥
      exact EReal.add_ne_bot_iff.mpr ⟨huy,by simp⟩
  refine ⟨v,hv,?_,hle,hzero⟩
  apply globalCurrent_ext (canonicalBasis (m + 1))
  intro e
  rw [thetaPotentialCurrent,thetaPotentialCurrent,GlobalCurrent.coefficients_add,
    GlobalCurrent.coefficients_add,globalDDC_coefficients,globalDDC_coefficients]
  apply congrArg (fun A => _ + A)
  let b := canonicalBasis (m + 1)
  let hL := quasiPsh_chart_locallyIntegrable b (Nat.succ_pos m) u hu.quasiPshPotential e
  let hV := quasiPsh_chart_locallyIntegrable b (Nat.succ_pos m) v hv.quasiPshPotential e
  let hC : LocallyIntegrableOn (fun z => c (e.val.symm z)) (chartTarget e) b.addHaar :=
    (hs e).continuousOn.locallyIntegrableOn (chartTarget e).isOpen.measurableSet
  have hreg : regularDistribution b.addHaar (fun z => (chartFunction v e z).toReal) hV =
      regularDistribution b.addHaar (fun z => (chartFunction u e z).toReal) hL -
      regularDistribution b.addHaar (fun z => c (e.val.symm z)) hC := by
    rw [← regularDistribution_sub hL hC]
    apply regularDistribution_congr_ae_on
    filter_upwards [quasiPsh_chart_ae_finite b (Nat.succ_pos m) u hu.quasiPshPotential e]
      with z hz
    exact EReal.toReal_sub hz.1 hz.2 (EReal.coe_ne_top _) (EReal.coe_ne_bot _)
  change ddC (regularDistribution b.addHaar _ hV) =
    ddC (regularDistribution b.addHaar _ hL)
  rw [hreg]
  change ddCLM _ = ddCLM _
  rw [map_sub]
  change ddC _ - ddC _ = ddC _
  rw [ddC_regular_zero c hc hs e b,sub_zero]

/-- ONE actual smooth representative, before ALL original currents in their
common class, supplies componentwise-normalized SAME-current theta potentials. -/
theorem exists_normalized_representations_of_common_class {ι : Type*}
    (β : RealBottChern (m + 1) X)
    (T : ι → ClosedOneOneCurrent (M := X) (canonicalBasis (m + 1)) (Nat.succ_pos m))
    (hT : ∀ i, IsFullPositive (T i).val)
    (hclass : ∀ i, bottChernClass (canonicalBasis (m + 1)) (Nat.succ_pos m) (T i) = β) :
    ∃ θ : ClosedRealOneOneForm (m + 1) X, RealBottChern.ofRepresentative θ = β ∧
      ∀ i, ∃ (v : X → EReal) (hv : IsThetaPshPotential θ.val v),
        (T i).val = thetaPotentialCurrent θ.val v hv ∧
        (∀ x, v x ≤ 0) ∧ ∀ x, ∃ y ∈ connectedComponent x, v y = 0 := by
  have hex : ∃ θ : ClosedRealOneOneForm (m + 1) X,
      RealBottChern.ofRepresentative θ = β :=
    Quotient.inductionOn β (fun θ => ⟨θ,rfl⟩)
  obtain ⟨θ,hθ⟩ := hex
  refine ⟨θ,hθ,?_⟩
  intro i
  obtain ⟨u,hu,heq,_⟩ := exists_theta_representation_of_class_eq (T i) θ (hT i)
    ((hclass i).trans hθ.symm)
  obtain ⟨v,hv,hvu,hle,hzero⟩ := exists_normalized_theta_current θ u hu
  exact ⟨v,hv,heq.trans hvu.symm,hle,hzero⟩

end SGPT.Foundations.Analysis.Pending.ComponentwiseNormalizedCurrentPotentials
