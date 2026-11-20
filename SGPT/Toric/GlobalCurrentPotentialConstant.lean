import SGPT.Hodge.ExceptionalNegativity
import SGPT.Foundations.Analysis.Pending.GlobalSmoothScalarDistribution
import SGPT.Foundations.Analysis.Pending.ThetaPotentialCurrentBottChernClass
import SGPT.Foundations.Analysis.Pending.PolydiskPerronDataComparison

set_option autoImplicit false
noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ContDiff Distributions Manifold

namespace SGPT.Toric.CurrentPotential

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open CanonicalCurrentFrame GlobalPositiveCurrentACRestriction NaturalThetaPshGeometricCurrent
open FiniteScalarDistributionGluing GlobalSmoothScalarDistribution
open ThetaPotentialCurrentBottChernClass GlobalCurrentPotentials
open _root_.SGPT.Foundations.Analysis.LocalCurrents

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

local notation "b" => canonicalBasis (m + 1)
local notation "μ" => (Module.Basis.addHaar (canonicalBasis (m + 1)))

private theorem regular_sub {Ω : Opens (ComplexModel (m + 1))}
    {f g : ComplexModel (m + 1) → ℝ}
    (hf : LocallyIntegrableOn f Ω μ) (hg : LocallyIntegrableOn g Ω μ) :
    regularDistribution μ (fun z => f z - g z) (hf.sub hg) =
      regularDistribution μ f hf - regularDistribution μ g hg := by
  ext φ
  change _ = regularDistribution μ f hf φ - regularDistribution μ g hg φ
  simp only [regularDistribution_apply, mul_sub]
  exact integral_sub (φ.integrable_bilin (ContinuousLinearMap.mul ℝ ℝ) hf)
    (φ.integrable_bilin (ContinuousLinearMap.mul ℝ ℝ) hg)

private theorem ddC_sub {Ω : Opens (ComplexModel (m + 1))} (R S : 𝓓'(Ω, ℝ)) :
    ddC (R - S) = ddC R - ddC S := by
  ext v : 1
  have hv : v = ![v 0, v 1] := by ext i; fin_cases i <;> rfl
  rw [hv, AlternatingMap.sub_apply, ddC_apply, ddC_apply, ddC_apply]
  simp only [map_sub, smul_sub]
  abel

/-- Equality of actual SAME-background original currents manufactures a
global smooth scalar difference with zero ddC, without an incoming
smooth-difference or compatibility certificate. -/
theorem exists_global_smooth_difference_of_current_eq
    {θ : SmoothRealForm (m + 1) M 2} {u v : M → EReal}
    (hu : IsThetaPshPotential θ u) (hv : IsThetaPshPotential θ v)
    (heq : thetaPotentialCurrent θ u hu = thetaPotentialCurrent θ v hv) :
    ∃ h : M → ℝ, ChartSmooth (n := m + 1) h ∧
      (∀ e : ComplexChart (m + 1) M,
        (fun z => (chartFunction u e z).toReal - (chartFunction v e z).toReal)
          =ᵐ[(μ).restrict (chartTarget e)] (fun z => h (e.val.symm z))) ∧
      ∀ (e : ComplexChart (m + 1) M) z, z ∈ e.val.target →
        smoothDDC (fun y => h (e.val.symm y)) z = 0 := by
  let hLu := quasiPsh_chart_locallyIntegrable b (Nat.succ_pos m) u hu.quasiPshPotential
  let hLv := quasiPsh_chart_locallyIntegrable b (Nat.succ_pos m) v hv.quasiPshPotential
  let Ru := fun e : ComplexChart (m + 1) M =>
    regularDistribution μ (fun z => (chartFunction u e z).toReal) (hLu e)
  let Rv := fun e : ComplexChart (m + 1) M =>
    regularDistribution μ (fun z => (chartFunction v e z).toReal) (hLv e)
  have hRu : ScalarFamilyCompatible Ru :=
    scalarFamilyCompatible_regular μ (fun x => (u x).toReal) hLu
  have hRv : ScalarFamilyCompatible Rv :=
    scalarFamilyCompatible_regular μ (fun x => (v x).toReal) hLv
  have hR : ScalarFamilyCompatible (fun e => Ru e - Rv e) := by
    intro e f η ψ hrel
    change Ru e (TestFunction.monoCLM ℝ η) - Rv e (TestFunction.monoCLM ℝ η) =
      Ru f (TestFunction.monoCLM ℝ ψ) - Rv f (TestFunction.monoCLM ℝ ψ)
    rw [hRu e f η ψ hrel, hRv e f η ψ hrel]
  have hdd (e : ComplexChart (m + 1) M) :
      ddC (Ru e - Rv e) =
        smoothFormDistribution b (0 : ClosedRealOneOneForm (m + 1) M).val e := by
    have hglobal : globalDDC b (Nat.succ_pos m) u hu.quasiPshPotential =
        globalDDC b (Nat.succ_pos m) v hv.quasiPshPotential := add_left_cancel heq
    have hc := congrArg (fun T => T.coefficients b e) hglobal
    have hd : ddC (Ru e) = ddC (Rv e) := by
      simpa only [GlobalCurrentPotentials.globalDDC_coefficients, chartDDC,
        Ru, Rv, hLu, hLv] using hc
    rw [ddC_sub, hd, sub_self]
    ext w φ
    simp [smoothFormDistribution_apply, ClosedRealOneOneForm.coeff_zero]
  obtain ⟨h, hsm, hreg, hzero⟩ :=
    exists_global_smooth_of_smooth_ddC b (0 : ClosedRealOneOneForm (m + 1) M)
      (fun e => Ru e - Rv e) hR hdd
  refine ⟨h, hsm, ?_, ?_⟩
  · intro e
    obtain ⟨hL, hr⟩ := hreg e
    apply ae_eq_of_regularDistribution_eq μ ((hLu e).sub (hLv e)) hL
    exact (regular_sub (hLu e) (hLv e)).trans hr
  · intro e z hz
    simpa only [ClosedRealOneOneForm.coeff_zero] using hzero e z hz

/-- A manufactured smooth zero-ddC scalar is genuinely 0-psh. -/
private theorem isThetaPsh_of_smooth_zero_ddC (h : M → ℝ)
    (hsm : ChartSmooth (n := m + 1) h)
    (hzero : ∀ (e : ComplexChart (m + 1) M) z, z ∈ e.val.target →
      smoothDDC (fun y => h (e.val.symm y)) z = 0) :
    IsThetaPshPotential (0 : ClosedRealOneOneForm (m + 1) M).val
      (fun x => (h x : EReal)) := by
  refine ⟨(LocalPotentials.thetaPlurisubharmonic_smooth_iff _ h hsm).mpr ?_, ?_⟩
  · intro e z hz w
    rw [hzero e z hz, ClosedRealOneOneForm.coeff_zero]
    simp
  · intro x U hU hx
    exact ⟨x, hx, EReal.coe_ne_bot _⟩

/-- Same actual whole current, SAME background, compact connected original
manifold: the actual potentials differ by ONE real constant pointwise,
including their poles. No supplied smooth difference or a.e.-only output. -/
theorem exists_const_difference_of_current_eq [CompactSpace M] [ConnectedSpace M]
    {θ : SmoothRealForm (m + 1) M 2} {u v : M → EReal}
    (hu : IsThetaPshPotential θ u) (hv : IsThetaPshPotential θ v)
    (heq : thetaPotentialCurrent θ u hu = thetaPotentialCurrent θ v hv) :
    ∃ c : ℝ, ∀ x, u x = v x + (c : EReal) := by
  obtain ⟨h, hsm, hae, hzero⟩ := exists_global_smooth_difference_of_current_eq hu hv heq
  obtain ⟨c, hc⟩ := SGPT.Hodge.Exceptional.eq_const_of_isThetaPshPotential_zero
    (isThetaPsh_of_smooth_zero_ddC h hsm hzero)
  have hhc : ∀ x, h x = c := fun x => EReal.coe_injective (hc x)
  refine ⟨c, ?_⟩
  intro x
  let e := complexChartAt (n := m + 1) x
  have hx : x ∈ e.val.source := mem_complexChartAt_source x
  have hxe : e.val x ∈ e.val.target := e.val.map_source hx
  obtain ⟨W, ρ, hxW, hρ, _⟩ := hu.1 e (e.val x) hxe
  have hpu : PlurisubharmonicOn
      (fun z => chartFunction u e z + (ρ z : EReal)) W :=
    chartCorrectedFamily_plurisubharmonicOn (F := {u})
      (fun f hf => by rw [mem_singleton_iff.mp hf]; exact hu) e hρ _
      ⟨u, mem_singleton _, rfl⟩
  have hpv : PlurisubharmonicOn
      (fun z => chartFunction v e z + (ρ z : EReal)) W :=
    chartCorrectedFamily_plurisubharmonicOn (F := {v})
      (fun f hf => by rw [mem_singleton_iff.mp hf]; exact hv) e hρ _
      ⟨v, mem_singleton _, rfl⟩
  have hd := ae_restrict_of_ae_restrict_of_subset hρ.2.1 (hae e)
  have huf := ae_restrict_of_ae_restrict_of_subset hρ.2.1
    (quasiPsh_chart_ae_finite b (Nat.succ_pos m) u hu.quasiPshPotential e)
  have hvf := ae_restrict_of_ae_restrict_of_subset hρ.2.1
    (quasiPsh_chart_ae_finite b (Nat.succ_pos m) v hv.quasiPshPotential e)
  have hAE : (fun z => chartFunction u e z + (ρ z : EReal))
      =ᵐ[(μ).restrict W] (fun z => (chartFunction v e z + (ρ z : EReal)) + (c : EReal)) := by
    filter_upwards [hd, huf, hvf] with z hz huz hvz
    rw [hhc] at hz
    have hr : (chartFunction u e z).toReal = (chartFunction v e z).toReal + c := by
      linarith
    have huv : chartFunction u e z = chartFunction v e z + (c : EReal) := by
      rw [← EReal.coe_toReal huz.1 huz.2, hr, EReal.coe_add,
        EReal.coe_toReal hvz.1 hvz.2]
    rw [huv, add_right_comm]
  have hpoint := hpu.eqOn_of_ae_eq (hpv.add_const c) hρ.1 μ hAE hxW
  have hpoint' : u x + (ρ (e.val x) : EReal) =
      (v x + (c : EReal)) + (ρ (e.val x) : EReal) := by
    simpa only [chartFunction, e.val.left_inv hx, add_right_comm] using hpoint
  exact le_antisymm
    ((EReal.addLECancellable_coe _).add_le_add_iff_right.mp hpoint'.le)
    ((EReal.addLECancellable_coe _).add_le_add_iff_right.mp hpoint'.ge)

/-- Sup-normalized actual potentials of the same original current are equal.
The normalization is expressed by a real upper bound and an attained zero,
so no hidden finite-supremum convention or pole subtraction is needed. -/
theorem normalized_eq_of_current_eq [CompactSpace M] [ConnectedSpace M]
    {θ : SmoothRealForm (m + 1) M 2} {u v : M → EReal}
    (hu : IsThetaPshPotential θ u) (hv : IsThetaPshPotential θ v)
    (heq : thetaPotentialCurrent θ u hu = thetaPotentialCurrent θ v hv)
    (hu_le : ∀ x, u x ≤ 0) (hv_le : ∀ x, v x ≤ 0)
    (hu_zero : ∃ x, u x = 0) (hv_zero : ∃ x, v x = 0) : u = v := by
  obtain ⟨c, hc⟩ := exists_const_difference_of_current_eq hu hv heq
  obtain ⟨x, hx⟩ := hu_zero
  obtain ⟨y, hy⟩ := hv_zero
  have hup : (c : EReal) ≤ 0 := by simpa only [hc y, hy, zero_add] using hu_le y
  have hlo : (0 : EReal) ≤ (c : EReal) := by
    calc 0 = v x + (c : EReal) := hx.symm.trans (hc x)
      _ ≤ 0 + (c : EReal) := add_le_add (hv_le x) le_rfl
      _ = _ := zero_add _
  have hc0 : c = 0 := EReal.coe_injective (le_antisymm hup hlo)
  funext z
  simpa only [hc0, EReal.coe_zero, add_zero] using hc z

end SGPT.Toric.CurrentPotential
