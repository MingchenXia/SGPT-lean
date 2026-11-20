import SGPT.Foundations.Analysis.Pending.SubgeodesicSupremumSlices
import SGPT.Foundations.Analysis.FirstPass.ThetaPshEnvelopes

/-!
# Interior Perron stability for arbitrary bounded-above families

The spatially regularized supremum of a nonempty uniformly bounded-above
family of interior subgeodesics is an interior subgeodesic. The time-slice
interchange is proved before adding the smooth chart correction, whose bound
is only local. Endpoint L1 convergence is a separate obligation.

Source: Xia, SGPT Proposition 4.1.3, PDF page 0151.
-/

set_option autoImplicit false

open Filter Set
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.SubgeodesicSupremumInterior

open FirstPass

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- A nonempty theta-psh family with a common finite upper bound has a genuine
theta-psh regularized supremum, with no countability assumption. -/
theorem isThetaPshPotential_uscRegularization_iSup {ι : Type*} [Nonempty ι]
    {theta : SmoothRealForm n M 2} {u : ι → M → EReal}
    (hu : ∀ i, IsThetaPshPotential theta (u i)) {C : ℝ}
    (hC : ∀ i x, u i x ≤ (C : EReal)) :
    IsThetaPshPotential theta (uscRegularization (fun x => ⨆ i, u i x)) := by
  classical
  let i₀ : ι := Classical.choice inferInstance
  let v : ι → M → EReal := fun i x => u i x + ((-C : ℝ) : EReal)
  have hv : ∀ i, IsThetaPshPotential theta (v i) := fun i => (hu i).add_const (-C)
  have hv₀ : ∀ i, v i ≤ 0 := fun i x => by
    calc u i x + ((-C : ℝ) : EReal)
        ≤ (C : EReal) + ((-C : ℝ) : EReal) := add_le_add (hC i x) le_rfl
      _ = 0 := by rw [← EReal.coe_add]; simp
  have hp := thetaPlurisubharmonic_uscRegularization_sSup
    (hu i₀).1.hasSmoothLocalPotentials (F := range v) (range_nonempty v)
    (by rintro _ ⟨i, rfl⟩; exact hv i) (by rintro _ ⟨i, rfl⟩; exact hv₀ i)
  have hsup : sSup (range v) = fun x => (⨆ i, u i x) + ((-C : ℝ) : EReal) := by
    funext x
    rw [sSup_range, iSup_apply]
    exact iSup_add_coe (fun i => u i x) (-C)
  rw [hsup, uscRegularization_add_coe_const] at hp
  have hnd : LocallyNondegenerate (uscRegularization (fun x => ⨆ i, u i x)) :=
    (hu i₀).2.mono fun x => (le_iSup (fun i => u i x) i₀).trans
      (le_uscRegularization (fun x => ⨆ i, u i x) x)
  have hfin : IsThetaPshPotential theta
      (fun x => uscRegularization (fun x => ⨆ i, u i x) x + ((-C : ℝ) : EReal)) :=
    ⟨hp, fun x U hU hx => by
      obtain ⟨y, hy, hne⟩ := hnd x U hU hx
      refine ⟨y, hy, fun hbot => ?_⟩
      rcases EReal.add_eq_bot_iff.mp hbot with hbot | hbot
      · exact hne hbot
      · exact EReal.coe_ne_bot _ hbot⟩
  have hresult := hfin.add_const C
  convert hresult using 1
  funext x
  rw [add_assoc, ← EReal.coe_add]
  simp

/-- The corrected chart representative of the slice-wise regularized family
is the joint regularization of its corrected complexifications. The generic
interchange is applied before the merely locally bounded correction is added. -/
theorem subgeodesicChartFunction_uscRegularization_iSup_eq {ι : Type*}
    {theta : SmoothRealForm n M 2} {curve : ι → ℝ → M → EReal}
    (h : ∀ i, IsSubgeodesicInterior theta (curve i)) {C : ℝ}
    (hC : ∀ i t, t ∈ Ioo (0 : ℝ) 1 → ∀ x, curve i t x ≤ (C : EReal))
    (e : ComplexChart n M) {W : Set (ComplexModel n)} {rho : ComplexModel n → ℝ}
    (hrho : IsSmoothLocalPotential theta e W rho)
    {p : ComplexModel n × ℂ} (hp : p ∈ geodesicChartDomain W) :
    subgeodesicChartFunction
        (fun t => uscRegularization (fun x => ⨆ i, curve i t x)) e rho p =
      uscRegularization (fun q => ⨆ i, subgeodesicChartFunction (curve i) e rho q) p := by
  have hsup : (fun q => ⨆ i, subgeodesicChartFunction (curve i) e rho q) =
      fun q : ComplexModel n × ℂ => (⨆ i, curve i q.2.re (e.val.symm q.1)) +
        (rho q.1 : EReal) := by
    funext q
    exact iSup_add_coe (fun i => curve i q.2.re (e.val.symm q.1)) (rho q.1)
  have hrhoc : ContinuousAt (fun q : ComplexModel n × ℂ => rho q.1) p :=
    (((hrho.2.2.1 p.1 hp.1).contDiffAt (hrho.1.mem_nhds hp.1)).continuousAt).comp
      continuousAt_fst
  symm
  rw [hsup, uscRegularization_add_coe_continuousAt_apply
    (fun q : ComplexModel n × ℂ => ⨆ i, curve i q.2.re (e.val.symm q.1)) hrhoc]
  rw [SubgeodesicSupremumSlices.uscRegularization_time_slice_eq
    (fun (t : ℝ) (z : ComplexModel n) => ⨆ i, curve i t (e.val.symm z))
    Complex.re Complex.continuous_re
    (fun t ht z => iSup_le fun i => hC i t ht (e.val.symm z))
    (fun a t b ha ht hb hat htb z =>
      SubgeodesicSupremumSlices.iSup_le_eRealChord_between h ha ht hb hat htb
        (e.val.symm z)) p.1 hp.2]
  rw [show (fun z => ⨆ i, curve i p.2.re (e.val.symm z)) =
      chartFunction (fun x => ⨆ i, curve i p.2.re x) e from rfl,
    uscRegularization_chartFunction_apply _ e (hrho.2.1 hp.1)]
  rfl

/-- A common finite upper bound for the uncorrected slices gives a local
uniform upper bound for the whole corrected family on a chart strip. -/
theorem locallyUniformlyBoundedAbove_chartFamily {ι : Type*}
    {theta : SmoothRealForm n M 2} {curve : ι → ℝ → M → EReal} {C : ℝ}
    (hC : ∀ i t, t ∈ Ioo (0 : ℝ) 1 → ∀ x, curve i t x ≤ (C : EReal))
    (e : ComplexChart n M) {W : Set (ComplexModel n)} {rho : ComplexModel n → ℝ}
    (hrho : IsSmoothLocalPotential theta e W rho) :
    LocallyUniformlyBoundedAbove (range (fun i => subgeodesicChartFunction (curve i) e rho))
      (geodesicChartDomain W) := by
  intro p hp
  have hrhoc : ContinuousAt (fun q : ComplexModel n × ℂ => rho q.1) p :=
    (((hrho.2.2.1 p.1 hp.1).contDiffAt (hrho.1.mem_nhds hp.1)).continuousAt).comp
      continuousAt_fst
  have hU : {q : ComplexModel n × ℂ | rho q.1 < rho p.1 + 1} ∈ 𝓝 p :=
    hrhoc (isOpen_Iio.mem_nhds (lt_add_one _))
  refine ⟨_, mem_nhdsWithin_of_mem_nhds hU, C + (rho p.1 + 1), ?_⟩
  rintro _ ⟨i, rfl⟩ q ⟨hqU, hqW⟩
  change curve i q.2.re (e.val.symm q.1) + (rho q.1 : EReal) ≤ _
  calc curve i q.2.re (e.val.symm q.1) + (rho q.1 : EReal)
      ≤ (C : EReal) + ((rho p.1 + 1 : ℝ) : EReal) :=
        add_le_add (hC i _ hqW.2 _) (EReal.coe_le_coe_iff.mpr hqU.le)
    _ = ((C + (rho p.1 + 1) : ℝ) : EReal) := (EReal.coe_add _ _).symm

/-- Interior Perron stability for an arbitrary nonempty family with a finite
common upper bound. Both genuine potential slices and strip psh are produced. -/
theorem isSubgeodesicInterior_uscRegularization_iSup {ι : Type*} [Nonempty ι]
    {theta : SmoothRealForm n M 2} {curve : ι → ℝ → M → EReal}
    (h : ∀ i, IsSubgeodesicInterior theta (curve i)) {C : ℝ}
    (hC : ∀ i t, t ∈ Ioo (0 : ℝ) 1 → ∀ x, curve i t x ≤ (C : EReal)) :
    IsSubgeodesicInterior theta
      (fun t => uscRegularization (fun x => ⨆ i, curve i t x)) := by
  classical
  refine ⟨fun t ht => isThetaPshPotential_uscRegularization_iSup
    (fun i => (h i).thetaPshPotential ht) (fun i x => hC i t ht x), ?_⟩
  intro e z hz
  let i₀ : ι := Classical.choice inferInstance
  obtain ⟨W, rho, hzW, hrho, -⟩ := (h i₀).complexified_psh e hz
  refine ⟨W, rho, hzW, hrho, ?_⟩
  have hpsh : ∀ f ∈ range (fun i => subgeodesicChartFunction (curve i) e rho),
      PlurisubharmonicOn f (geodesicChartDomain W) := by
    rintro _ ⟨i, rfl⟩
    exact SubgeodesicChartPotential.plurisubharmonicOn_subgeodesicChartFunction
      (h i) e hrho
  have hjoint := plurisubharmonicOn_uscRegularization_sSup
    (isOpen_geodesicChartDomain hrho.1) (range_nonempty _)
    hpsh (locallyUniformlyBoundedAbove_chartFamily hC e hrho)
  rw [sSup_range] at hjoint
  have hfun : (⨆ i, subgeodesicChartFunction (curve i) e rho) =
      (fun q => ⨆ i, subgeodesicChartFunction (curve i) e rho q) := by
    funext q
    exact iSup_apply
  rw [hfun] at hjoint
  intro p hp
  refine (hjoint p hp).congr ?_
  filter_upwards [(isOpen_geodesicChartDomain hrho.1).mem_nhds hp] with q hq
  exact (subgeodesicChartFunction_uscRegularization_iSup_eq h hC e hrho hq).symm

end

end SGPT.Foundations.Analysis.Pending.SubgeodesicSupremumInterior
