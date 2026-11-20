import SGPT.Foundations.Analysis.Pending.KahlerRestrictedMassBound
import SGPT.Foundations.Analysis.Pending.RestrictedVolumeKahlerIndependence
import SGPT.Foundations.Analysis.FirstPass.GlobalPotentialTransforms

set_option autoImplicit false

/-!
# Uniform bound for restricted absolutely continuous masses

Source: CT22, Lemma 2.1 (`ct22-restricted-volumes:finite`), a combination of
Boucksom, *Divisorial Zariski decompositions*, Proposition 2.6, and Matsumura,
Proposition 4.1; Copy-4, `eq:def-restricted-volume`; blueprint
`ana:locus-properties` ("finiteness follows from ... the uniform bound of
Collins--Tosatti for restricted absolutely continuous masses of currents bounded
below").

Let `(X, ω)` be compact Kähler and `V ⊆ X` an irreducible analytic subvariety of
dimension `k`.  For closed real `(1,1)`-currents `T ≥ -Aω` in a fixed class that
restrict to `V`, the masses `∫_{V_reg} ((T + εω)|_{V_reg})_ac^k` with `0 < ε ≤ A`
are bounded by a constant depending only on `X, V, ω, A` and the class.

**Proof.**  CT22 argue through an embedded resolution of `V`, Demailly
regularization and Boucksom's Lelong-number bound.  Here the lemma is PROVED from
its Kähler-class case at error `1`
(`Pending.KahlerRestrictedMassBound.exists_acTopMass_le_of_zero_representative`,
the remaining classical input: Stokes against `[V]`).  Fix a representative `θ₀` of
the class and a multiple `β` of `ω` dominating `θ₀ + Aω`.  An `ε`-admissible
`θ' + ddᶜu` with `θ₀ = θ' + ddᶜh` becomes the presentation `β + ddᶜ(u - h)` of the zero
class (`shiftPresentation`), with the same poles.  Off the poles its restricted form
is the old one plus the semipositive `β - θ₀ - εω`, so every top-power density
grows (`acTopMass_le_shiftPresentation`).  No regularization is used.

`Pending.LocusProperties.numericalRestrictedVolume_ne_top` is PROVED from this lemma.
No module in the root import closure imports this file.
-/

open Set Filter MeasureTheory
open scoped ENNReal Topology ContDiff

namespace SGPT.Foundations.Analysis.Pending.RestrictedMassFiniteness

open FirstPass FirstPass.PositiveClasses FirstPass.NumericalRestrictedVolumeScaffold
  FirstPass.NumericalRestrictedVolume FirstPass.AdmissibleCurrentFormPositivity FirstPass.MongeAmpere
  RestrictedMassEnvelopeMonotone

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Subtracting a real function never creates or removes a pole. -/
theorem sub_coe_eq_bot_iff (a : EReal) (r : ℝ) : a - (r : EReal) = ⊥ ↔ a = ⊥ := by
  induction a using EReal.rec with
  | bot => simp
  | top => simp
  | coe x => simp [← EReal.coe_sub]

/-- Smooth analytic singularities survive subtracting a chart-smooth function. -/
theorem hasManifoldSmoothAnalyticSingularities_sub {u : M → EReal} {h : M → ℝ}
    (hu : HasManifoldSmoothAnalyticSingularities (n := n) u) (hh : ChartSmooth (n := n) h) :
    HasManifoldSmoothAnalyticSingularities (n := n) (fun x => u x - (h x : EReal)) := by
  intro e z hz
  obtain ⟨c, m, f, hc, hf, b, hb, heq⟩ := hu e z hz
  refine ⟨c, m, f, hc, hf, fun y => b y - h (e.val.symm y), ?_, ?_⟩
  · filter_upwards [hb, e.val.open_target.mem_nhds hz] with y hy hyt
    exact hy.sub ((hh e y hyt).contDiffAt (e.val.open_target.mem_nhds hyt))
  · filter_upwards [heq] with y hy
    change u (e.val.symm y) - (h (e.val.symm y) : EReal) = _
    change chartFunction u e y = _ at hy
    change chartFunction u e y - (h (e.val.symm y) : EReal) = _
    rw [hy, EReal.coe_sub, sub_eq_add_neg, sub_eq_add_neg, add_assoc]

/-- **Analytic singularities in the bounded-remainder convention survive subtracting a chart-smooth
function.**  The generators are unchanged, so the pole set is unchanged; the new remainder
`b - h` is bounded because a chart-smooth function is continuous, and it is smooth wherever
`b` is. -/
theorem hasManifoldAnalyticSingularitiesSmoothOffPole_sub {u : M → EReal} {h : M → ℝ}
    (hu : HasManifoldAnalyticSingularitiesSmoothOffPole (n := n) u)
    (hh : ChartSmooth (n := n) h) :
    HasManifoldAnalyticSingularitiesSmoothOffPole (n := n) (fun x => u x - (h x : EReal)) := by
  intro e z hz
  obtain ⟨c, m, f, hc, hf, b, hbdd, hb, heq⟩ := hu e z hz
  have hhsmooth : ∀ᶠ y in 𝓝 z, ContDiffAt ℝ ∞ (fun y => h (e.val.symm y)) y := by
    filter_upwards [e.val.open_target.mem_nhds hz] with y hyt
    exact (hh e y hyt).contDiffAt (e.val.open_target.mem_nhds hyt)
  refine ⟨c, m, f, hc, hf, fun y => b y - h (e.val.symm y),
    hbdd.sub (boundedRealGermAt_of_continuousAt hhsmooth.self_of_nhds.continuousAt), ?_, ?_⟩
  · filter_upwards [hb, hhsmooth] with y hy hy' hne
    exact (hy hne).sub hy'
  · filter_upwards [heq] with y hy
    change u (e.val.symm y) - (h (e.val.symm y) : EReal) = _
    change chartFunction u e y = _ at hy
    change chartFunction u e y - (h (e.val.symm y) : EReal) = _
    rw [hy, EReal.coe_sub, sub_eq_add_neg, sub_eq_add_neg, add_assoc]

section Shift

variable {omega : KahlerBackground n M} {θ₀ : ClosedRealOneOneForm n M}
  {V : ClosedIrreducibleAnalyticSubvariety n M} {ε : PositiveError}

/-- An `ε`-admissible presentation `θ' + ddᶜu` of `{θ₀}` for `ω`, with
`θ₀ = θ' + ddᶜh`, gives the admissible presentation `0 + β + ddᶜ(u - h)` of the zero
class at error `1` for any Kähler form `β ≥ θ₀ + εω`. -/
def shiftPresentation
    (p : AdmissibleRestrictedCurrentPresentation omega (RealBottChern.ofRepresentative θ₀) V ε)
    (beta : KahlerBackground n M) {h : M → ℝ} (hh : ChartSmooth (n := n) h)
    (hrel : ∀ (e : ComplexChart n M) (z : ComplexModel n), z ∈ e.val.target →
      θ₀.val.coeff e z = p.representative.val.coeff e z + smoothDDC (fun y => h (e.val.symm y)) z)
    (hD : ((0 + (1 : ℝ) • beta.form) - (θ₀ + (ε : ℝ) • omega.form)).val.IsSemipositive) :
    AdmissibleRestrictedCurrentPresentation beta (RealBottChern.ofRepresentative 0) V
      ⟨1, one_pos⟩ where
  representative := 0
  represents := rfl
  potential := fun x => p.potential x - (h x : EReal)
  potential_psh := by
    have h1 : ThetaPlurisubharmonic (θ₀ + (ε : ℝ) • omega.form).val
        (fun x => p.potential x - (h x : EReal)) := by
      refine GlobalPotentialTransforms.thetaPlurisubharmonic_sub_smooth hh
        (fun e z hz => ?_) p.potential_psh.1
      simp only [ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.coeff_smul, hrel e z hz]
      abel
    have h2 : IsThetaPshPotential (θ₀ + (ε : ℝ) • omega.form).val
        (fun x => p.potential x - (h x : EReal)) := by
      refine ⟨h1, fun x U hU hx => ?_⟩
      obtain ⟨y, hyU, hy⟩ := p.potential_psh.2 x U hU hx
      exact ⟨y, hyU, fun hbot => hy ((sub_coe_eq_bot_iff _ _).mp hbot)⟩
    have h3 := LocalPotentials.isThetaPshPotential_add_of_semipositive h2 hD
    rwa [add_sub_cancel] at h3
  smoothAnalyticSingularities :=
    hasManifoldAnalyticSingularitiesSmoothOffPole_sub p.smoothAnalyticSingularities hh
  not_carrier_subset_poleSet := by
    intro hsub
    exact p.not_carrier_subset_poleSet fun x hx =>
      (sub_coe_eq_bot_iff _ _).mp (hsub hx)

theorem poleSet_shiftPresentation
    (p : AdmissibleRestrictedCurrentPresentation omega (RealBottChern.ofRepresentative θ₀) V ε)
    (beta : KahlerBackground n M) {h : M → ℝ} (hh : ChartSmooth (n := n) h)
    (hrel : ∀ (e : ComplexChart n M) (z : ComplexModel n), z ∈ e.val.target →
      θ₀.val.coeff e z = p.representative.val.coeff e z + smoothDDC (fun y => h (e.val.symm y)) z)
    (hD : ((0 + (1 : ℝ) • beta.form) - (θ₀ + (ε : ℝ) • omega.form)).val.IsSemipositive) :
    poleSet (shiftPresentation p beta hh hrel hD).potential = poleSet p.potential := by
  ext x
  exact sub_coe_eq_bot_iff _ _

/-- Off the poles, the coordinate form of the shifted presentation is that of the
original one plus the semipositive difference `β - (θ₀ + εω)`. -/
theorem coordinateCurrentForm_shiftPresentation
    (p : AdmissibleRestrictedCurrentPresentation omega (RealBottChern.ofRepresentative θ₀) V ε)
    (beta : KahlerBackground n M) {h : M → ℝ} (hh : ChartSmooth (n := n) h)
    (hrel : ∀ (e : ComplexChart n M) (z : ComplexModel n), z ∈ e.val.target →
      θ₀.val.coeff e z = p.representative.val.coeff e z + smoothDDC (fun y => h (e.val.symm y)) z)
    (hD : ((0 + (1 : ℝ) • beta.form) - (θ₀ + (ε : ℝ) • omega.form)).val.IsSemipositive)
    (e : ComplexChart n M) {z : ComplexModel n} (hz : z ∈ e.val.target)
    (hpole : e.val.symm z ∉ poleSet p.potential) :
    coordinateCurrentForm (shiftPresentation p beta hh hrel hD) e z =
      coordinateCurrentForm p e z +
        ((0 + (1 : ℝ) • beta.form) - (θ₀ + (ε : ℝ) • omega.form)).val.coeff e z := by
  obtain ⟨g, hg, hug⟩ := exists_smooth_eventuallyEq_of_hasAnalyticSingularitiesSmoothOffPoleAt
    (p.smoothAnalyticSingularities e z hz) hpole
  obtain ⟨U, hUg, hU, hzU⟩ := eventually_nhds_iff.mp hg
  set W := U ∩ e.val.target
  have hW : IsOpen W := hU.inter e.val.open_target
  have hzW : z ∈ W := ⟨hzU, hz⟩
  have hgW : ContDiffOn ℝ ∞ g W := fun y hy => (hUg y hy.1).contDiffWithinAt
  have hhW : ContDiffOn ℝ ∞ (fun y => h (e.val.symm y)) W := (hh e).mono inter_subset_right
  have hreal : (fun y => (p.potential (e.val.symm y)).toReal) =ᶠ[𝓝 z] g := by
    filter_upwards [hug] with y hy
    change (chartFunction p.potential e y).toReal = g y
    rw [hy, EReal.toReal_coe]
  have hreal' : (fun y => ((shiftPresentation p beta hh hrel hD).potential
      (e.val.symm y)).toReal) =ᶠ[𝓝 z] fun y => g y - h (e.val.symm y) := by
    filter_upwards [hug] with y hy
    change (chartFunction p.potential e y - (h (e.val.symm y) : EReal)).toReal = _
    rw [hy, ← EReal.coe_sub, EReal.toReal_coe]
  have hddc := smoothDDC_congr hreal
  have hddc' := (smoothDDC_congr hreal').trans (smoothDDC_sub hW hgW hhW hzW)
  simp only [coordinateCurrentForm, perturbedRepresentative, hddc, hddc']
  simp only [shiftPresentation, sub_eq_add_neg, ClosedRealOneOneForm.coeff_add,
    ClosedRealOneOneForm.coeff_smul, ClosedRealOneOneForm.coeff_neg,
    ClosedRealOneOneForm.coeff_zero, hrel e z hz]
  module

/-- Shifting does not decrease the restricted mass. -/
theorem acTopMass_le_shiftPresentation
    (p : AdmissibleRestrictedCurrentPresentation omega (RealBottChern.ofRepresentative θ₀) V ε)
    (beta : KahlerBackground n M) {h : M → ℝ} (hh : ChartSmooth (n := n) h)
    (hrel : ∀ (e : ComplexChart n M) (z : ComplexModel n), z ∈ e.val.target →
      θ₀.val.coeff e z = p.representative.val.coeff e z + smoothDDC (fun y => h (e.val.symm y)) z)
    (hD : ((0 + (1 : ℝ) • beta.form) - (θ₀ + (ε : ℝ) • omega.form)).val.IsSemipositive) :
    acTopMass p ≤ acTopMass (shiftPresentation p beta hh hrel hD) := by
  have hpoles := poleSet_shiftPresentation p beta hh hrel hD
  refine iSup_le fun F => ?_
  let F' : RegularPieceFamily V (poleSet (shiftPresentation p beta hh hrel hD).potential) :=
    { F with image_disjoint_avoid := fun i => by rw [hpoles]; exact F.image_disjoint_avoid i }
  refine le_trans ?_ (le_iSup _ F')
  refine Finset.sum_le_sum fun i _ => lintegral_mono_ae ?_
  refine (ae_restrict_iff' (F.measurableSet_piece i)).mpr (Eventually.of_forall ?_)
  intro w hw
  apply ENNReal.ofReal_le_ofReal
  set P := F.patch i
  set e := complexChartAt (n := n) P.center
  set L := fderiv ℝ P.coordinateParametrization w
  have hdom : w ∈ P.parameterDomain := F.piece_subset i hw
  have hz : P.coordinateParametrization w ∈ e.val.target :=
    P.source_subset (P.flattening.mapsTo_invFun hdom)
  have hpole : e.val.symm (P.coordinateParametrization w) ∉ poleSet p.potential := by
    intro hmem
    exact Set.disjoint_left.mp (F.image_disjoint_avoid i) ⟨w, hw, rfl⟩ hmem
  have hL := RegularPatchDerivative.fderiv_coordinateParametrization_I_smul P hdom
  obtain ⟨hA1, hA2⟩ := coordinateCurrentForm_isOneOne_and_semipositive p e hz hpole
  set D := (0 + (1 : ℝ) • beta.form) - (θ₀ + (ε : ℝ) • omega.form) with hDdef
  have hB1 : IsOneOne (D.val.coeff e (P.coordinateParametrization w)) := fun a b =>
    D.2.2 e _ hz a b
  have hB2 : CoefficientSemipositive (D.val.coeff e (P.coordinateParametrization w)) :=
    fun v => hD e _ hz v
  have key := actualTopPowerDensity_le_add (isOneOne_compContinuousLinearMap hA1 L hL)
    (coefficientSemipositive_compContinuousLinearMap hA2 L hL)
    (isOneOne_compContinuousLinearMap hB1 L hL)
    (coefficientSemipositive_compContinuousLinearMap hB2 L hL)
  simp only [patchDensity]
  rw [coordinateCurrentForm_shiftPresentation p beta hh hrel hD e hz hpole]
  convert key using 2
  ext v
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply,
    ContinuousAlternatingMap.add_apply, e, L, P, hDdef]

end Shift

/-- **Uniform bound for restricted masses** (CT22, Lemma 2.1).  On a compact complex
manifold with a Kähler form `ω`, the absolutely continuous restricted top masses of
the admissible presentations of a class along `V` are bounded uniformly for all
errors `0 < ε ≤ A`.

PROVED from the Kähler-class case
`KahlerRestrictedMassBound.exists_acTopMass_le_of_zero_representative`: fix a
representative `θ₀` of the class and `c > 0` with `cω - θ₀ ≥ 0`, and put
`β = (c + max A 0 + 1)ω`.  An `ε`-admissible `θ' + ddᶜu` with `θ₀ = θ' + ddᶜh` becomes
the presentation `β + ddᶜ(u - h)` of the zero class, whose restricted form exceeds
that of `θ' + εω + ddᶜu` by the semipositive `β - θ₀ - εω`; top-power densities are
monotone (`actualTopPowerDensity_le_add`). -/
theorem exists_acTopMass_le [CompactSpace M] (omega : KahlerBackground n M)
    (alpha : RealBottChern n M) (V : ClosedIrreducibleAnalyticSubvariety n M) (A : ℝ) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ epsilon : PositiveError, (epsilon : ℝ) ≤ A →
      ∀ p : AdmissibleRestrictedCurrentPresentation omega alpha V epsilon,
        acTopMass p ≤ C := by
  obtain ⟨θ₀, rfl⟩ := Quotient.exists_rep alpha
  obtain ⟨c, hc, hsemi⟩ := KahlerDomination.exists_pos_isSemipositive_add_smul omega (-θ₀)
  set K : ℝ := c + max A 0 with hKdef
  have hK0 : 0 ≤ K := by positivity
  have hK : (0 + K • omega.form).val.IsSemipositive := by
    rw [zero_add]
    exact KahlerDomination.isSemipositive_smul omega.isSemipositive hK0
  let beta : KahlerBackground n M :=
    ⟨0 + (K + 1) • omega.form, KahlerDomination.isKahler_add_smul_succ omega hK⟩
  obtain ⟨C, hC, hle⟩ :=
    KahlerRestrictedMassBound.exists_acTopMass_le_of_zero_representative beta V
  refine ⟨C, hC, fun ε hε p => ?_⟩
  obtain ⟨h, hh, hrel⟩ := (RealBottChern.ofRepresentative_eq_iff _ _).mp p.represents
  have hD : ((0 + (1 : ℝ) • beta.form) - (θ₀ + (ε : ℝ) • omega.form)).val.IsSemipositive := by
    have heq : (0 + (1 : ℝ) • beta.form) - (θ₀ + (ε : ℝ) • omega.form) =
        -θ₀ + (K + 1 - ε) • omega.form := by
      simp only [beta]
      module
    rw [heq]
    refine KahlerDomination.isSemipositive_add_smul_mono omega.isSemipositive ?_ hsemi
    have : (ε : ℝ) ≤ max A 0 := hε.trans (le_max_left _ _)
    linarith
  exact (acTopMass_le_shiftPresentation p beta hh hrel hD).trans (hle _ rfl)

/-- The admissible mass envelope at a positive error is finite. -/
theorem restrictedMassEnvelope_ne_top [CompactSpace M] (omega : KahlerBackground n M)
    (alpha : RealBottChern n M) (V : ClosedIrreducibleAnalyticSubvariety n M)
    (epsilon : PositiveError) :
    restrictedMassEnvelope (acTopMassData omega) alpha V epsilon ≠ ⊤ := by
  obtain ⟨C, hC, hle⟩ := exists_acTopMass_le omega alpha V epsilon
  exact ne_top_of_le_ne_top hC (iSup_le fun p => hle epsilon le_rfl p)

end

end SGPT.Foundations.Analysis.Pending.RestrictedMassFiniteness
