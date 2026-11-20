import SGPT.Foundations.Analysis.Pending.SubgeodesicInfimum
import SGPT.Foundations.Analysis.Pending.KiselmanMinimumPrincipleInterface
import SGPT.Foundations.Analysis.Pending.ThetaPshIdentityPrinciple

set_option autoImplicit false

/-!
# The slice infimum of a subgeodesic is a theta-PSH potential

This completes assertion 2 of Xia's Proposition 4.1.2
(`xia-sgpt:page-0149`--`xia-sgpt:page-0150`):

  `inf_{t in (0,1)} u_t in PSH(X, theta)`

for a subgeodesic `(u_t)`.  Xia derives it from Kiselman's minimum principle,
his Proposition 1.2.8 (`xia-sgpt:page-0029`, cited to Demailly, *Complex
Analytic and Differential Geometry*, Theorem I.7.5).

The two halves are split along exactly that line:

* the *raw* criterion `ThetaPlurisubharmonic theta (sliceInfimum curve)` is the
  Kiselman half, and it is proved here from
  `Pending.KiselmanMinimumPrinciple.plurisubharmonicOn_iInf_slices` -- filed in
  run 0093 as a named classical input, a theorem since run 0095
  (`Pending.KiselmanMinimumPrincipleProof`);
* the *nondegeneracy* half is `Pending.SubgeodesicInfimum`, proved outright.

The chart bookkeeping between them is elementary and is done here.  Fix a
chart `e` and a smooth local potential `rho` of `theta` on `W`.  The
subgeodesic condition says precisely that

  `Phi (z, tau) = chartFunction (curve tau.re) e z + rho z`

is PSH on `W x complexTimeStrip`, and `Phi` depends on `tau` only through
`tau.re`.  Kiselman applies verbatim and returns
`PlurisubharmonicOn (fun z => inf_t Phi (z, t)) W`; the additive constant
`rho z` then moves out of the infimum, which is `iInf_add_coe` below, and what
is left is the raw criterion for `sliceInfimum curve` in the chart `e`.
-/

open Filter Set

namespace SGPT.Foundations.Analysis.Pending.SubgeodesicInfimumThetaPsh

open FirstPass
open SGPT.Foundations.Analysis.Pending.SubgeodesicInfimum

noncomputable section

/-! ### Moving a real constant out of an extended-real infimum -/

/-- Adding a real constant commutes with an infimum over a nonempty index
type.  The value `⊥` is allowed among the `f i`, and the statement is false
for `c = ⊤` (the right-hand side would be `⊤` even when some `f i = ⊥`), so
the hypothesis that `c` is a genuine real number is used. -/
theorem iInf_add_coe {ι : Sort*} [Nonempty ι] (f : ι → EReal) (c : ℝ) :
    (⨅ i, f i) + (c : EReal) = ⨅ i, (f i + (c : EReal)) := by
  have key : ∀ (g : ι → EReal) (d : ℝ),
      (⨅ i, g i) + (d : EReal) ≤ ⨅ i, (g i + (d : EReal)) :=
    fun g d => le_iInf fun i => add_le_add (iInf_le g i) le_rfl
  have cancel : ∀ (a : EReal) (p q : ℝ), p + q = 0 →
      a + (p : EReal) + (q : EReal) = a := by
    intro a p q hpq
    induction a using EReal.rec with
    | bot => simp
    | coe x =>
        rw [← EReal.coe_add, ← EReal.coe_add]
        norm_cast
        linarith
    | top => simp
  refine le_antisymm (key f c) ?_
  have h1 := key (fun i => f i + (c : EReal)) (-c)
  have h2 : (⨅ i, (f i + (c : EReal) + ((-c : ℝ) : EReal))) = ⨅ i, f i := by
    exact iInf_congr fun i => cancel (f i) c (-c) (by ring)
  rw [h2] at h1
  calc (⨅ i, (f i + (c : EReal)))
      = (⨅ i, (f i + (c : EReal))) + ((-c : ℝ) : EReal) + (c : EReal) :=
        (cancel _ (-c) c (by ring)).symm
    _ ≤ (⨅ i, f i) + (c : EReal) := add_le_add h1 le_rfl

/-! ### Xia's Proposition 4.1.2, assertion 2 -/

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

instance : Nonempty ↥(Ioo (0 : ℝ) 1) := ⟨⟨1 / 2, by norm_num⟩⟩

/-- **The Kiselman half of Xia, Proposition 4.1.2, assertion 2.**  The
pointwise infimum of the interior slices of a subgeodesic satisfies the raw
`theta`-PSH criterion.  The analytic input is Kiselman's minimum principle,
`Pending.KiselmanMinimumPrinciple.plurisubharmonicOn_iInf_slices`, which is
proved (`Pending.KiselmanMinimumPrincipleProof`). -/
theorem thetaPlurisubharmonic_sliceInfimum {theta : SmoothRealForm n M 2}
    {curve : ℝ → M → EReal} (h : IsSubgeodesicInterior theta curve) :
    ThetaPlurisubharmonic theta (sliceInfimum curve) := by
  intro e z hz
  obtain ⟨W, ρ, hzW, hρ, hpsh⟩ := h.complexified_psh e hz
  refine ⟨W, ρ, hzW, hρ, ?_⟩
  have hinv : ∀ (y : ComplexModel n) (τ σ : ℂ), τ.re = σ.re →
      subgeodesicChartFunction curve e ρ (y, τ) =
        subgeodesicChartFunction curve e ρ (y, σ) := by
    intro y τ σ hre
    simp only [subgeodesicChartFunction_apply, hre]
  have hkis :=
    KiselmanMinimumPrinciple.plurisubharmonicOn_iInf_slices hρ.1 hpsh hinv
  have hfun : (fun y : ComplexModel n =>
      ⨅ t : ↥(Ioo (0 : ℝ) 1),
        subgeodesicChartFunction curve e ρ (y, ((t : ℝ) : ℂ))) =
      fun y : ComplexModel n => chartFunction (sliceInfimum curve) e y + (ρ y : EReal) := by
    funext y
    simp only [subgeodesicChartFunction_apply, Complex.ofReal_re]
    rw [← iInf_add_coe (fun t : ↥(Ioo (0 : ℝ) 1) =>
      chartFunction (curve (t : ℝ)) e y) (ρ y)]
    rfl
  rwa [hfun] at hkis

/-- **Xia, Proposition 4.1.2, assertion 2.**  On a connected complex manifold
the pointwise infimum of the interior slices of a subgeodesic is a genuine
`theta`-PSH potential.  The nondegeneracy input is proved outright in
`Pending.SubgeodesicInfimum`; only the raw criterion uses Kiselman. -/
theorem isThetaPshPotential_sliceInfimum [ConnectedSpace M] [Nonempty M]
    {theta : SmoothRealForm n M 2} {curve : ℝ → M → EReal}
    (h : IsSubgeodesicInterior theta curve) :
    IsThetaPshPotential theta (sliceInfimum curve) :=
  ThetaPshIdentityPrinciple.isThetaPshPotential_of_exists_ne_bot
    (thetaPlurisubharmonic_sliceInfimum h) (exists_sliceInfimum_ne_bot h)

end

end SGPT.Foundations.Analysis.Pending.SubgeodesicInfimumThetaPsh
