import SGPT.Okounkov.OF12ValCurrNormal
import SGPT.Trace.TY4CurrentEquality
import SGPT.Unibranch.HironakaG11ModificationCalculus
import SGPT.Unibranch.ComplexSpaceThetaRegularity
import SGPT.Foundations.Analysis.Pending.PositiveCurrentPrescribedBottChernRepresentation
import SGPT.Foundations.Analysis.PshRegularDistribution
import SGPT.Foundations.Analysis.Pending.ThetaPshChartLimitGluing

/-!
# `rmk:valcurr` for a normal projective variety: `ν(T)` depends only on the current `T`

A closed positive `(1,1)`-current on the normal space `X^an` is a presentation `θ + dd^c ψ`, two
presentations being equal when their local potentials differ by pluriharmonic functions
(`SpaceForm.SameCurrent`, Eyssidieux–Guedj–Zeriahi; lane TY4). We prove that the value
`ν_{Y•}(π^*T) g` of `rmk:valcurr` only depends on the current:

* `thetaPotentialCurrent_eq_of_coeff_add_ddc` (manifolds): if `σ = θ + dd^c g` with `g` smooth and
  `u = v + g`, then `θ + dd^c u = σ + dd^c v` as currents;
* `nativePullback_coeff_of_sameForm_add_ddcOf`, `chartSmooth_comp_nativePoint`: for a morphism
  `h : W → Z` from a manifold and `θ₂ = θ₁ + dd^c f` on `Z` (`f` smooth), `h^*θ₂ = h^*θ₁ +
  dd^c (f ∘ h)` with `f ∘ h` smooth;
* `Presentation.value_eq_of_sameCurrent`: two presentations of the same current on `X^an` have the
  same value, for every presentation of `ν`; hence `valuationCurrentValue_eq_of_sameCurrent`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.Okounkov.OF12

open Set Filter MeasureTheory TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Distributions Topology ContDiff Manifold
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.LocalCurrents
open LelongPoincareDivisor FiniteGlobalCurrentSmoothLocalDensity
open NaturalThetaPshGeometricCurrent CanonicalCurrentFrame GlobalPositiveCurrentACRestriction

/-! ### Changing the presentation of a current on a manifold -/

section Manifold

variable {m : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel (m + 1)) M]
  [IsComplexManifold (m + 1) M]

/-- The distribution of `θ + dd^c g` is that of `θ` plus `dd^c` of the regular distribution of
`g` (after `PositiveCurrentPrescribedBottChernRepresentation.smooth_reading_of_geometric_ddC`). -/
theorem smoothFormDistribution_add_ddc
    (b : Module.Basis (Fin (Module.finrank ℝ (ComplexModel (m + 1)))) ℝ (ComplexModel (m + 1)))
    {θ σ : SmoothRealForm (m + 1) M 2} {g : M → ℝ} (hg : ChartSmooth (n := m + 1) g)
    (heq : ∀ (e : ComplexChart (m + 1) M) (z : ComplexModel (m + 1)), z ∈ e.val.target →
      σ.coeff e z = θ.coeff e z + smoothDDC (fun y => g (e.val.symm y)) z)
    (e : ComplexChart (m + 1) M) :
    smoothFormDistribution b σ e = smoothFormDistribution b θ e +
      ddC (regularDistribution b.addHaar (fun z => g (e.val.symm z))
        ((hg e).continuousOn.locallyIntegrableOn (chartTarget e).isOpen.measurableSet)) := by
  rw [ddC_regular_eq_regularForm b.addHaar (hg e)]
  ext v φ
  rw [AlternatingMap.add_apply, add_apply, smoothFormDistribution_apply,
    smoothFormDistribution_apply, regularFormDistribution_apply]
  have hiθ : Integrable (fun z => φ z • θ.coeff e z) b.addHaar :=
    φ.integrable_bilin (ContinuousLinearMap.lsmul ℝ ℝ)
      (smoothForm_coeff_locallyIntegrable b θ e)
  have hid : Integrable
      (fun z => φ z • smoothDDC (fun y => g (e.val.symm y)) z) b.addHaar :=
    φ.integrable_bilin (ContinuousLinearMap.lsmul ℝ ℝ)
      ((LogWeightFactorization.smoothDDC_contDiffOn (chartTarget e).isOpen
        (hg e)).continuousOn.locallyIntegrableOn (chartTarget e).isOpen.measurableSet)
  change (∫ z, φ z • σ.coeff e z ∂b.addHaar) v =
    ((∫ z, φ z • θ.coeff e z ∂b.addHaar) +
      (∫ z, φ z • smoothDDC (fun y => g (e.val.symm y)) z ∂b.addHaar)) v
  rw [← integral_add hiθ hid]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with z
  by_cases hz : z ∈ e.val.target
  · rw [heq e z hz, smul_add]
  · have hφ : φ z = 0 := image_eq_zero_of_notMem_tsupport
      (fun ht => hz (φ.tsupport_subset ht))
    rw [hφ, zero_smul, zero_smul, zero_smul, add_zero]

/-- **`θ + dd^c u = (θ + dd^c g) + dd^c (u - g)`.** If `σ = θ + dd^c g` in every chart with `g`
smooth and `u = v + g`, the currents `θ + dd^c u` and `σ + dd^c v` coincide. -/
theorem thetaPotentialCurrent_eq_of_coeff_add_ddc {θ σ : SmoothRealForm (m + 1) M 2}
    {g : M → ℝ} (hg : ChartSmooth (n := m + 1) g)
    (heq : ∀ (e : ComplexChart (m + 1) M) (z : ComplexModel (m + 1)), z ∈ e.val.target →
      σ.coeff e z = θ.coeff e z + smoothDDC (fun y => g (e.val.symm y)) z)
    {u v : M → EReal} (huv : ∀ x, u x = v x + (g x : EReal))
    (hu : IsThetaPshPotential θ u) (hv : IsThetaPshPotential σ v) :
    thetaPotentialCurrent θ u hu = thetaPotentialCurrent σ v hv := by
  set b := canonicalBasis (m + 1)
  apply globalCurrent_ext b
  intro e
  unfold thetaPotentialCurrent
  rw [GlobalCurrent.coefficients_add, GlobalCurrent.coefficients_add,
    coefficients_smoothGlobalCurrent, coefficients_smoothGlobalCurrent,
    GlobalCurrentPotentials.globalDDC_coefficients, GlobalCurrentPotentials.globalDDC_coefficients,
    smoothFormDistribution_add_ddc b hg heq e]
  have hLv := GlobalCurrentPotentials.quasiPsh_chart_locallyIntegrable b (Nat.succ_pos m) v
    hv.quasiPshPotential e
  have hLu := GlobalCurrentPotentials.quasiPsh_chart_locallyIntegrable b (Nat.succ_pos m) u
    hu.quasiPshPotential e
  have hLg : LocallyIntegrableOn (fun z => g (e.val.symm z)) (chartTarget e) b.addHaar :=
    (hg e).continuousOn.locallyIntegrableOn (chartTarget e).isOpen.measurableSet
  have hreg : regularDistribution b.addHaar (fun z => (chartFunction u e z).toReal) hLu =
      regularDistribution b.addHaar (fun z => (chartFunction v e z).toReal) hLv +
        regularDistribution b.addHaar (fun z => g (e.val.symm z)) hLg := by
    rw [← ThetaPshChartLimitGluing.regularDistribution_add hLv hLg]
    apply regularDistribution_congr_ae_on
    filter_upwards [GlobalCurrentPotentials.quasiPsh_chart_ae_finite b (Nat.succ_pos m) v
      hv.quasiPshPotential e] with z hz
    change (u (e.val.symm z)).toReal = (v (e.val.symm z)).toReal + g (e.val.symm z)
    rw [huv]
    lift v (e.val.symm z) to ℝ using ⟨hz.1, hz.2⟩ with r
    rw [← EReal.coe_add, EReal.toReal_coe, EReal.toReal_coe]
  unfold chartDDC
  rw [hreg, show ∀ R S : 𝓓'(chartTarget e, ℝ), ddC (R + S) = ddC R + ddC S from
    fun R S => map_add ddCLM R S]
  abel

end Manifold

/-! ### Pull-back of `θ + dd^c f` from a complex space to a manifold -/

section Pullback

open SGPT.Unibranch SGPT.Unibranch.SourceReducedComplexSpace SGPT.Unibranch.SpaceForm
  SGPT.Unibranch.OriginalNativeModification SGPT.Okounkov.OCSpaceFormNative

variable {n : ℕ} {W : Type} [TopologicalSpace W] [ChartedSpace (ComplexModel n) W]
  [IsComplexManifold n W] {Z : SourceReducedComplexSpace} (h : wholeModel (n := n) W ⟶ Z)

/-- **`f ∘ h` is smooth** for a smooth function `f` on `Z` and a morphism `h` from a manifold:
locally `f ∘ h = F ∘ G` with `F` a smooth ambient extension and `G` a holomorphic lift. -/
theorem chartSmooth_comp_nativePoint {f : Z.obj.left → ℝ} (hf : Z.IsSmoothFunction f) :
    ChartSmooth (n := n) (fun w : W => f (h.hom.left.base ⟨w, mem_univ w⟩)) := by
  intro e
  apply contDiffOn_of_locally_contDiffOn
  intro z hz
  obtain ⟨e₀, hx, F, hF, hFeq⟩ := hf (h.hom.left.base ⟨e.val.symm z, mem_univ _⟩)
  obtain ⟨D, hD, hzD, hDe, G, hG, hmaps, hfac⟩ := exists_chart_lift h e e₀ hz hx
  refine ⟨D, hD, hzD, ?_⟩
  have hFG : ContDiffOn ℝ ∞ (fun y => F (G y)) D := hF.comp (hG.restrict_scalars ℝ) hmaps
  refine (hFG.mono inter_subset_right).congr fun w hw => ?_
  obtain ⟨c, hc, hpc⟩ := hfac w hw.2
  change f (h.hom.left.base ⟨e.val.symm w, mem_univ _⟩) = F (G w)
  rw [← hc, hFeq c, hpc]

/-- **`h^*(θ + dd^c f) = h^*θ + dd^c(f ∘ h)`.** If `θ₂` is the same form as `θ₁ + dd^c f` on `Z`
(`f` smooth), then in every chart of `W` the coefficient of the native pull-back `h^*θ₂` is that
of `h^*θ₁` plus `dd^c` of `f ∘ h`. -/
theorem nativePullback_coeff_of_sameForm_add_ddcOf {θ₁ θ₂ : SpaceForm Z 2}
    {f : Z.obj.left → ℝ} (hf : Z.IsSmoothFunction f) (hS : SameForm (θ₁.add (ddcOf f hf)) θ₂)
    (e : ComplexChart n W) {z : ComplexModel n} (hz : z ∈ e.val.target) :
    (nativePullback h θ₂).coeff e z = (nativePullback h θ₁).coeff e z +
      smoothDDC (fun y => f (h.hom.left.base ⟨e.val.symm y, mem_univ _⟩)) z := by
  obtain ⟨i, c, hc⟩ := θ₁.covers (h.hom.left.base ⟨e.val.symm z, mem_univ _⟩)
  obtain ⟨T, hT, hcT, F, hF, hFeq⟩ := hf.exists_local_extension (θ₁.chart i) c
  set e' := (θ₁.chart i).restrict T hT with he'
  have h₁ : θ₁.RestrictsTo e' (θ₁.rep i) := (θ₁.restrictsTo_rep i).restrict T hT
  have hv₁ : ContDiffOn ℝ ∞ (θ₁.rep i) (T : Set (ComplexModel (θ₁.chart i).dim)) :=
    (θ₁.smooth i).mono hT
  have hdF : ContDiffOn ℝ ∞ (smoothDDC F) (T : Set (ComplexModel (θ₁.chart i).dim)) :=
    Pending.LogWeightFactorization.smoothDDC_contDiffOn T.isOpen hF
  have hext : ∀ c' : e'.carrier, F c'.val.val = f (e'.toPoint c') := fun c' =>
    hFeq ⟨Opens.inclusion hT c'.val, c'.property⟩ c'.val.property
  have h₂ : θ₂.RestrictsTo e' (θ₁.rep i + smoothDDC F) :=
    hS.restrictsTo (restrictsTo_add hv₁ hdF h₁ (restrictsTo_ddcOf hf hF hext))
  have hx : h.hom.left.base ⟨e.val.symm z, mem_univ _⟩ ∈ range e'.toPoint :=
    ⟨⟨⟨c.val.val, hcT⟩, c.property⟩, hc⟩
  obtain ⟨D, hD, hzD, hDe, G, hG, hmaps, hfac⟩ := exists_chart_lift h e e' hz hx
  have hGd : DifferentiableOn ℂ G D := hG.differentiableOn (by simp)
  rw [nativePullback_coeff_eq_of_restrictsTo h θ₂ h₂ e hD hDe hGd hfac hzD,
    nativePullback_coeff_eq_of_restrictsTo h θ₁ h₁ e hD hDe hGd hfac hzD,
    pullbackForm_add, Pi.add_apply]
  congr 1
  rw [show pullbackForm G (smoothDDC F) z = smoothDDC (fun y => F (G y)) z from
    (HolomorphicDDC.smoothDDC_comp hD T.isOpen hG hF hmaps hzD).symm]
  apply smoothDDC_congr
  filter_upwards [hD.mem_nhds hzD] with w hw
  obtain ⟨c', hc', hpc'⟩ := hfac w hw
  rw [← hc', hext c', hpc']

end Pullback

/-! ### `ν(T)` only depends on the current `T` -/

section Value

open SGPT.Unibranch SGPT.Unibranch.SourceReducedComplexSpace SGPT.Unibranch.SpaceForm
  SGPT.Unibranch.OriginalNativeModification SGPT.Okounkov.OCSpaceFormNative
  SGPT.Okounkov.OCModelCurrentValuation SGPT.Foundations.Schemes

variable {X : Scheme.{0}} [IsIntegral X] {f : X ⟶ Spec (.of ℂ)} [IsSeparated f] [QuasiCompact f]
  [LocallyOfFiniteType f] {m : ℕ}

local instance of12CTop (R : Resolution f m) : TopologicalSpace (SchemeComplexPoint R.fY) :=
  schemeAnalyticPointTopology R.fY
local instance of12CCharts (R : Resolution f m) :
    ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint R.fY) :=
  schemeAnalyticTNChartedSpace R.fY (m + 1)
local instance of12CManifold (R : Resolution f m) :
    IsComplexManifold (m + 1) (SchemeComplexPoint R.fY) :=
  schemeAnalyticTN_isComplexManifold R.fY (m + 1)

/-- A `θ`-psh function on `X^an` is finite on a dense set: read it on a resolution, where it is
quasi-psh, and push forward by the (surjective, continuous) resolution map. -/
theorem Resolution.dense_ne_bot (R : Resolution f m) (hXu : (UnibAn.analytification f).IsUnibranch)
    {θ : SpaceForm (UnibAn.analytification f) 2} (hθ : PD.IsLocallyClosedOneOne θ)
    {ψ : (UnibAn.analytification f).obj.left → EReal}
    (hψ : (UnibAn.analytification f).IsThetaPSH θ ψ) :
    Dense {x : (UnibAn.analytification f).obj.left | ψ x ≠ ⊥} := by
  have hu := R.isThetaPshPotential_pullback hXu θ hθ ψ hψ
  have hV : Dense {y : SchemeComplexPoint R.fY | R.pullbackPotential ψ y ≠ ⊥} := by
    refine dense_iff_inter_open.mpr fun U hU ⟨y, hy⟩ => ?_
    obtain ⟨w, hwU, hw⟩ := hu.quasiPshPotential.2 y U hU hy
    exact ⟨w, hwU, hw⟩
  let p : SchemeComplexPoint R.fY → (UnibAn.analytification f).obj.left :=
    fun y => R.π.hom.left.base ⟨y, mem_univ y⟩
  have hp : Continuous p :=
    R.π.hom.left.base.hom.continuous.comp (continuous_id.subtype_mk fun y => mem_univ y)
  have hps : Function.Surjective p := by
    intro x
    obtain ⟨⟨y, hy0⟩, hy⟩ := R.isProperBimeromorphic.surjective x
    exact ⟨y, hy⟩
  refine (hps.denseRange.dense_image hp hV).mono ?_
  rintro _ ⟨y, hy, rfl⟩
  exact hy

/-- **`rmk:valcurr`: the value only depends on the current.** If `θ₁ + dd^c ψ₁` and
`θ₂ + dd^c ψ₂` present the same closed positive current on `X^an` (`SpaceForm.SameCurrent`, local
potentials differing by pluriharmonic functions), every presentation `ν = ν_{Y•} g` gives them the
same value. -/
theorem Presentation.value_eq_of_sameCurrent
    {v : AddValuation X.functionField (WithTop (Lex (Fin (m + 1) → ℤ)))}
    (Q : Presentation f m v) (hXu : (UnibAn.analytification f).IsUnibranch)
    {θ₁ θ₂ : SpaceForm (UnibAn.analytification f) 2} (hθ₁ : PD.IsLocallyClosedOneOne θ₁)
    (hθ₂ : PD.IsLocallyClosedOneOne θ₂) {ψ₁ ψ₂ : (UnibAn.analytification f).obj.left → EReal}
    (hψ₁ : (UnibAn.analytification f).IsThetaPSH θ₁ ψ₁)
    (hψ₂ : (UnibAn.analytification f).IsThetaPSH θ₂ ψ₂) (hT : SameCurrent θ₁ ψ₁ θ₂ ψ₂) :
    Q.value hXu θ₁ hθ₁ ψ₁ hψ₁ = Q.value hXu θ₂ hθ₂ ψ₂ hψ₂ := by
  obtain ⟨F, hF, hS, hψ⟩ := hT.exists_smooth (Q.R.dense_ne_bot hXu hθ₁ hψ₁) hψ₁.ne_top
  unfold Presentation.value
  apply OF2.modificationPresentationValue_eq_of_eq
  exact thetaPotentialCurrent_eq_of_coeff_add_ddc (chartSmooth_comp_nativePoint Q.R.π hF)
    (fun e z hz => nativePullback_coeff_of_sameForm_add_ddcOf Q.R.π hF hS e hz)
    (fun y => hψ _) _ _

/-- **`rmk:valcurr`: `ν(T)` is a function of the current `T`.** -/
theorem valuationCurrentValue_eq_of_sameCurrent
    (hX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (v : AddValuation X.functionField (WithTop (Lex (Fin (m + 1) → ℤ))))
    {θ₁ θ₂ : SpaceForm (UnibAn.analytification f) 2} (hθ₁ : PD.IsLocallyClosedOneOne θ₁)
    (hθ₂ : PD.IsLocallyClosedOneOne θ₂) {ψ₁ ψ₂ : (UnibAn.analytification f).obj.left → EReal}
    (hψ₁ : (UnibAn.analytification f).IsThetaPSH θ₁ ψ₁)
    (hψ₂ : (UnibAn.analytification f).IsThetaPSH θ₂ ψ₂) (hT : SameCurrent θ₁ ψ₁ θ₂ ψ₂) :
    valuationCurrentValue f m hX v θ₁ hθ₁ ψ₁ hψ₁ =
      valuationCurrentValue f m hX v θ₂ hθ₂ ψ₂ hψ₂ := by
  classical
  unfold valuationCurrentValue
  split_ifs with h
  · exact h.some.value_eq_of_sameCurrent _ hθ₁ hθ₂ hψ₁ hψ₂ hT
  · rfl

end Value

end SGPT.Okounkov.OF12
