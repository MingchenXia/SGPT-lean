import SGPT.Foundations.Analysis.FirstPass.FiniteGeodesics
import SGPT.Foundations.Analysis.FirstPass.LocalPotentialIndependence
import SGPT.Foundations.Analysis.FirstPass.PshSupremumRegularization
import SGPT.Foundations.Analysis.FirstPass.ThetaPshEnvelopes

set_option autoImplicit false

/-!
# One local potential tests every Perron competitor on the chart strip

`IsSubgeodesicInterior` supplies, for each chart point, *some* neighbourhood
`W'` and *some* smooth local potential `rho'` of `theta` on which the
corrected complexification is PSH.  A regularized-supremum argument for the
Perron finite geodesic needs the opposite: one fixed pair `(W, rho)` testing
*every* competitor at once.  That is the first of the two inputs named in the
docstring of `Pending.FiniteGeodesics.finiteGeodesicCompetitors_chart_locallyUniformlyBoundedAbove`
("put every competitor into this fixed local-potential PSH family and identify
its regularized supremum with the spatially regularized `finiteGeodesic`"), and
it is proved here.

Two facts do it.  Plurisubharmonicity is a pointwise property, so it is enough
to test each point of `geodesicChartDomain W` on `W ∩ W'`.  And two smooth
local potentials of `theta` differ by a pluriharmonic function on the spatial
factor, whose pullback under the complex-linear projection
`ComplexModel n × ℂ → ComplexModel n` is pluriharmonic on the product; adding
it exchanges `rho'` for `rho` exactly as `smoothLocalPotential_psh_iff` does in
the spatial case.

The companion `sSup_image_subgeodesicChartFunction_apply` records that the raw
supremum of the corrected family is the corrected raw slice supremum.  The
second input is Xia's Proposition 4.1.3
(`xia-sgpt:page-0150`--`xia-sgpt:page-0152`), the interchange of the *joint*
strip USC regularization with the *slicewise* spatial one; it is proved in
`Pending.FiniteGeodesicsJointUsc`.
-/

open Set
open scoped ContDiff

namespace SGPT.Foundations.Analysis.Pending.SubgeodesicChartPotential

open FirstPass

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Exchange the smooth local potential in the strip-PSH test.  This is the
product-chart form of `smoothLocalPotential_psh_iff`; only the direction used
below is stated. -/
theorem plurisubharmonicOn_subgeodesicChartFunction_congr_potential
    {theta : SmoothRealForm n M 2} {curve : ℝ → M → EReal}
    (e : ComplexChart n M) {V : Set (ComplexModel n)}
    {rho rho' : ComplexModel n → ℝ}
    (hrho : IsSmoothLocalPotential theta e V rho)
    (hrho' : IsSmoothLocalPotential theta e V rho')
    (h : PlurisubharmonicOn (subgeodesicChartFunction curve e rho')
      (geodesicChartDomain V)) :
    PlurisubharmonicOn (subgeodesicChartFunction curve e rho)
      (geodesicChartDomain V) := by
  have hsmooth : ContDiffOn ℝ ∞ (fun y => rho y - rho' y) V :=
    hrho.2.2.1.sub hrho'.2.2.1
  have hddc : ∀ z ∈ V, smoothDDC (fun y => rho y - rho' y) z = 0 := by
    intro z hz
    rw [PositiveClasses.smoothDDC_sub hrho'.1 hrho.2.2.1 hrho'.2.2.1 hz,
      hrho.2.2.2 hz, hrho'.2.2.2 hz, sub_self]
  have hdiff : PlurisubharmonicOn
      (fun y => ((rho y - rho' y : ℝ) : EReal)) V :=
    plurisubharmonicOn_coe_of_smoothDDC_eq_zero hrho'.1 hsmooth hddc
  have hpull := hdiff.comp_continuousLinearMap
    (ContinuousLinearMap.fst ℂ (ComplexModel n) ℂ)
  have hmono : geodesicChartDomain V ⊆
      (ContinuousLinearMap.fst ℂ (ComplexModel n) ℂ) ⁻¹' V := fun p hp => hp.1
  have hadd := SGPT.Foundations.Analysis.PlurisubharmonicOn.add h (hpull.mono hmono)
  intro p hp
  refine (hadd p hp).congr (Filter.Eventually.of_forall fun q => ?_)
  exact corrected_add_sub (chartFunction (curve q.2.re) e q.1) (rho' q.1) (rho q.1)

/-- **One fixed local potential tests the whole strip.**  For any smooth local
potential `rho` of `theta` on `W`, the corrected complexification of an
interior subgeodesic is PSH on all of `geodesicChartDomain W`. -/
theorem plurisubharmonicOn_subgeodesicChartFunction
    {theta : SmoothRealForm n M 2} {curve : ℝ → M → EReal}
    (h : IsSubgeodesicInterior theta curve) (e : ComplexChart n M)
    {W : Set (ComplexModel n)} {rho : ComplexModel n → ℝ}
    (hrho : IsSmoothLocalPotential theta e W rho) :
    PlurisubharmonicOn (subgeodesicChartFunction curve e rho)
      (geodesicChartDomain W) := by
  rintro p ⟨hp1, hp2⟩
  obtain ⟨W', rho', hp1', hrho', hpsh'⟩ := h.complexified_psh e (hrho.2.1 hp1)
  have hVopen : IsOpen (W ∩ W') := hrho.1.inter hrho'.1
  have hsub : geodesicChartDomain (W ∩ W') ⊆ geodesicChartDomain W' :=
    fun q hq => ⟨hq.1.2, hq.2⟩
  have hpV : PlurisubharmonicOn (subgeodesicChartFunction curve e rho)
      (geodesicChartDomain (W ∩ W')) :=
    plurisubharmonicOn_subgeodesicChartFunction_congr_potential e
      (hrho.mono hVopen inter_subset_left) (hrho'.mono hVopen inter_subset_right)
      (fun q hq => hpsh' q (hsub hq))
  exact hpV p ⟨⟨hp1, hp1'⟩, hp2⟩

/-- Every Perron competitor of `finiteGeodesicCompetitors` lies in the fixed
local-potential PSH family on the chart strip. -/
theorem plurisubharmonicOn_image_subgeodesicChartFunction
    {theta : SmoothRealForm n M 2} {u₀ u₁ : M → EReal}
    (e : ComplexChart n M) {W : Set (ComplexModel n)}
    {rho : ComplexModel n → ℝ} (hrho : IsSmoothLocalPotential theta e W rho) :
    ∀ f ∈ (fun curve => subgeodesicChartFunction curve e rho) ''
        finiteGeodesicCompetitors theta u₀ u₁,
      PlurisubharmonicOn f (geodesicChartDomain W) := by
  rintro f ⟨curve, ⟨v₀, v₁, -, -, -, -, hsub⟩, rfl⟩
  exact plurisubharmonicOn_subgeodesicChartFunction hsub.2.2.1 e hrho

/-- The raw supremum of the corrected competitor family is the corrected raw
slice supremum.  No regularization is involved on either side, so this is the
identity that the remaining strip/slice interchange has to survive. -/
theorem iSup_subgeodesicChartFunction_apply
    (theta : SmoothRealForm n M 2) (u₀ u₁ : M → EReal)
    (e : ComplexChart n M) (rho : ComplexModel n → ℝ)
    (p : ComplexModel n × ℂ) :
    (⨆ curve ∈ finiteGeodesicCompetitors theta u₀ u₁,
        subgeodesicChartFunction curve e rho p) =
      subgeodesicChartFunction (finiteGeodesicSliceSupremum theta u₀ u₁) e rho p := by
  have hlhs : (⨆ curve ∈ finiteGeodesicCompetitors theta u₀ u₁,
      subgeodesicChartFunction curve e rho p)
      = ⨆ curve ∈ finiteGeodesicCompetitors theta u₀ u₁,
          (curve p.2.re (e.val.symm p.1) + (rho p.1 : EReal)) := rfl
  have hrhs : subgeodesicChartFunction (finiteGeodesicSliceSupremum theta u₀ u₁)
        e rho p
      = (⨆ curve ∈ finiteGeodesicCompetitors theta u₀ u₁,
          curve p.2.re (e.val.symm p.1)) + (rho p.1 : EReal) := by
    change finiteGeodesicSliceSupremum theta u₀ u₁ p.2.re (e.val.symm p.1)
        + (rho p.1 : EReal) = _
    rw [finiteGeodesicSliceSupremum_apply]
  rw [hlhs, hrhs, iSup_subtype'
      (p := fun curve : ℝ → M → EReal => curve ∈ finiteGeodesicCompetitors theta u₀ u₁)
      (f := fun curve _ => curve p.2.re (e.val.symm p.1) + (rho p.1 : EReal)),
    iSup_subtype'
      (p := fun curve : ℝ → M → EReal => curve ∈ finiteGeodesicCompetitors theta u₀ u₁)
      (f := fun curve _ => curve p.2.re (e.val.symm p.1))]
  exact iSup_add_coe _ _


/-- **The joint strip envelope of the Perron family is PSH.**  With the fixed
local potential supplied by `plurisubharmonicOn_image_subgeodesicChartFunction`
and the local uniform upper bound of
`Pending.FiniteGeodesics.finiteGeodesicCompetitors_chart_locallyUniformlyBoundedAbove`,
the *joint* USC regularization of the corrected competitor family is PSH on the
chart strip.  The interchange of this joint regularization with the slicewise
spatial one — Xia's Proposition 4.1.3
(`xia-sgpt:page-0150`--`xia-sgpt:page-0152`) — is
`Pending.subgeodesicChartFunction_finiteGeodesic_eq_strip_envelope`, so this
is exactly the strip half of
`finiteGeodesic_isSubgeodesicInterior_of_relativeFullMass`. -/
theorem plurisubharmonicOn_uscRegularization_sSup_image
    {theta : SmoothRealForm n M 2} {u₀ u₁ : M → EReal}
    (e : ComplexChart n M) {W : Set (ComplexModel n)}
    {rho : ComplexModel n → ℝ} (hrho : IsSmoothLocalPotential theta e W rho)
    (hne : (finiteGeodesicCompetitors theta u₀ u₁).Nonempty)
    (hbdd : LocallyUniformlyBoundedAbove
      ((fun curve => subgeodesicChartFunction curve e rho) ''
        finiteGeodesicCompetitors theta u₀ u₁) (geodesicChartDomain W)) :
    PlurisubharmonicOn (uscRegularization (sSup
      ((fun curve => subgeodesicChartFunction curve e rho) ''
        finiteGeodesicCompetitors theta u₀ u₁))) (geodesicChartDomain W) :=
  plurisubharmonicOn_uscRegularization_sSup (isOpen_geodesicChartDomain hrho.1)
    (hne.image _) (plurisubharmonicOn_image_subgeodesicChartFunction e hrho) hbdd

end

end SGPT.Foundations.Analysis.Pending.SubgeodesicChartPotential
