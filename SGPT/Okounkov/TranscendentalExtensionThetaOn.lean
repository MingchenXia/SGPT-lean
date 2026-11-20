import SGPT.Foundations.Analysis.Pending.IdealFunctionMaxGluing
import SGPT.Foundations.Analysis.Pending.BoundedGlobalTruncation
import SGPT.Foundations.Analysis.Pending.ThetaPshCollarGluing
import SGPT.Foundations.Analysis.Pending.OpensRestriction

/-!
# `θ`-plurisubharmonicity on an open set: closure properties

Auxiliary API for the extension of Kähler currents (blueprint `tok:ct-extension`, package EXT
of the formalization of `thm:Okounkovtranmain`). TN's `ThetaPlurisubharmonicOn θ u Ω` tests the
chartwise `θ`-psh criterion at the chart points over `Ω`. We record the elementary closure
properties used in the gluing argument of DRWNXZ Theorem 6.1 / FPT
`thm:holder-positive-potential-extension`, Steps 2, 4 and 5:

* restriction to smaller sets, sums (`θ₁`-psh plus `θ₂`-psh is `(θ₁ + θ₂)`-psh), enlarging the
  background by a semipositive form, maxima and real constant shifts;
* upper semicontinuity and boundedness above on compact subsets of the open set;
* gluing by locally finite maxima (`thetaPlurisubharmonicOn_of_locally_finset_sup`, the
  `Ω`-version of TN's `IdealFunctionMaxGluing.thetaPlurisubharmonic_of_locally_finset_sup`);
* transport of a single chart witness to all charts (`thetaPlurisubharmonicOn_of_chart`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology

namespace SGPT.Okounkov.TranscendentalExtension

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.Pending

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

theorem thetaOn_mono {θ : SmoothRealForm n M 2} {u : M → EReal}
    {Ω Ω' : Set M} (h : ThetaPlurisubharmonicOn θ u Ω) (hΩ : Ω' ⊆ Ω) :
    ThetaPlurisubharmonicOn θ u Ω' :=
  fun e z hz hzΩ => h e z hz (hΩ hzΩ)

theorem thetaOn_of_global {θ : SmoothRealForm n M 2}
    {u : M → EReal} (h : ThetaPlurisubharmonic θ u) (Ω : Set M) :
    ThetaPlurisubharmonicOn θ u Ω :=
  fun e z hz _ => h e z hz

/-- `θ`-psh on `Ω` is a property of the germs at the points of `Ω`. -/
theorem thetaOn_congr {θ : SmoothRealForm n M 2} {u v : M → EReal}
    {Ω : Set M} (hΩ : IsOpen Ω) (h : ThetaPlurisubharmonicOn θ u Ω) (huv : EqOn u v Ω) :
    ThetaPlurisubharmonicOn θ v Ω := by
  intro e z hz hzΩ
  obtain ⟨W, ρ, hzW, hρ, hp⟩ := h e z hz hzΩ
  let D : Set (ComplexModel n) := e.val.target ∩ e.val.symm ⁻¹' Ω
  have hD : IsOpen D := e.val.isOpen_inter_preimage_symm hΩ
  refine ⟨W ∩ D, ρ, ⟨hzW, hz, hzΩ⟩, hρ.mono (hρ.1.inter hD) inter_subset_left, ?_⟩
  intro y hy
  refine (hp y hy.1).congr ?_
  filter_upwards [(hρ.1.inter hD).mem_nhds hy] with w hw
  simp only [chartFunction, huv hw.2.2]

/-- The sum of a `θ₁`-psh and a `θ₂`-psh function on `Ω` is `(θ₁ + θ₂)`-psh on `Ω`. -/
theorem thetaOn_add {a b : ClosedRealOneOneForm n M} {u v : M → EReal}
    {Ω : Set M} (hu : ThetaPlurisubharmonicOn a.val u Ω)
    (hv : ThetaPlurisubharmonicOn b.val v Ω) :
    ThetaPlurisubharmonicOn (a + b).val (fun x => u x + v x) Ω := by
  intro e z hz hzΩ
  obtain ⟨W, ρ, hzW, hρ, hp⟩ := hu e z hz hzΩ
  obtain ⟨V, σ, hzV, hσ, hq⟩ := hv e z hz hzΩ
  have hWV : IsOpen (W ∩ V) := hρ.1.inter hσ.1
  refine ⟨W ∩ V, fun y => ρ y + σ y, ⟨hzW, hzV⟩,
    LocalPotentials.localPotential_add (hρ.mono hWV inter_subset_left)
      (hσ.mono hWV inter_subset_right), ?_⟩
  have hfun :
      (fun y => chartFunction (fun x => u x + v x) e y + ((ρ y + σ y : ℝ) : EReal)) =
      (fun y => (chartFunction u e y + (ρ y : EReal)) +
        (chartFunction v e y + (σ y : EReal))) := by
    funext y
    simp only [chartFunction, EReal.coe_add]
    ac_rfl
  rw [hfun]
  exact (hp.mono inter_subset_left).add (hq.mono inter_subset_right)

/-- Enlarging the background by a semipositive form keeps `θ`-psh on `Ω`. -/
theorem thetaOn_add_semipositive {a b : ClosedRealOneOneForm n M}
    {u : M → EReal} {Ω : Set M} (hu : ThetaPlurisubharmonicOn a.val u Ω)
    (hb : b.val.IsSemipositive) : ThetaPlurisubharmonicOn (a + b).val u Ω := by
  have h0 : ThetaPlurisubharmonicOn b.val (fun _ => (0 : EReal)) Ω :=
    thetaOn_of_global ((LocalPotentials.thetaPlurisubharmonic_zero_iff b).mpr hb) Ω
  simpa only [add_zero] using thetaOn_add hu h0

/-- The maximum of two `θ`-psh functions on `Ω` is `θ`-psh on `Ω`. -/
theorem thetaOn_max {θ : SmoothRealForm n M 2} {u v : M → EReal}
    {Ω : Set M} (hu : ThetaPlurisubharmonicOn θ u Ω) (hv : ThetaPlurisubharmonicOn θ v Ω) :
    ThetaPlurisubharmonicOn θ (fun x => Max.max (u x) (v x)) Ω := by
  intro e z hz hzΩ
  obtain ⟨W, ρ, hzW, hρ, hp⟩ := hu e z hz hzΩ
  obtain ⟨V, σ, hzV, hσ, hq⟩ := hv e z hz hzΩ
  have hWV : IsOpen (W ∩ V) := hρ.1.inter hσ.1
  refine ⟨W ∩ V, ρ, ⟨hzW, hzV⟩, hρ.mono hWV inter_subset_left, ?_⟩
  have hq' : PlurisubharmonicOn (fun y => chartFunction v e y + (ρ y : EReal)) (W ∩ V) :=
    (FirstPass.smoothLocalPotential_psh_iff θ e (W ∩ V) ρ σ (hρ.mono hWV inter_subset_left)
      (hσ.mono hWV inter_subset_right) (chartFunction v e)).mpr
      (hq.mono inter_subset_right)
  have h := (hp.mono inter_subset_left).max hq'
  convert h using 2 with y
  exact (max_add_add_right _ _ _).symm

/-- A real constant shift keeps `θ`-psh on `Ω`. -/
theorem thetaOn_add_const {θ : SmoothRealForm n M 2} {u : M → EReal}
    {Ω : Set M} (hu : ThetaPlurisubharmonicOn θ u Ω) (c : ℝ) :
    ThetaPlurisubharmonicOn θ (fun x => u x + (c : EReal)) Ω := by
  intro e z hz hzΩ
  obtain ⟨W, ρ, hzW, hρ, hp⟩ := hu e z hz hzΩ
  refine ⟨W, ρ, hzW, hρ, ?_⟩
  have hc : PlurisubharmonicOn (fun _ : ComplexModel n => (c : EReal)) W :=
    fun x _ => plurisubharmonicAt_const _ (EReal.coe_ne_top c) x
  have h := hp.add hc
  intro y hy
  refine (h y hy).congr (Eventually.of_forall fun w => ?_)
  simp only [chartFunction]
  ac_rfl

/-- A `θ`-psh witness at a chart point gives upper semicontinuity at the corresponding point. -/
theorem thetaOn_upperSemicontinuousAt {θ : SmoothRealForm n M 2}
    {u : M → EReal} {Ω : Set M} (hu : ThetaPlurisubharmonicOn θ u Ω) {x : M} (hx : x ∈ Ω) :
    UpperSemicontinuousAt u x ∧ u x ≠ ⊤ := by
  let e := complexChartAt (n := n) x
  have hxe : x ∈ e.val.source := mem_complexChartAt_source x
  have hz : e.val x ∈ e.val.target := e.val.map_source hxe
  have hzΩ : e.val.symm (e.val x) ∈ Ω := by rw [e.val.left_inv hxe]; exact hx
  obtain ⟨W, ρ, hzW, hρ, hp⟩ := hu e (e.val x) hz hzΩ
  have hpx := hp _ hzW
  have h1 := hpx.upperSemicontinuousAt
  have hρc : ContinuousAt ρ (e.val x) :=
    (hρ.2.2.1.continuousOn).continuousAt (hρ.1.mem_nhds hzW)
  have hneg : ContinuousAt (fun y => ((-ρ y : ℝ) : EReal)) (e.val x) :=
    continuous_coe_real_ereal.continuousAt.comp hρc.neg
  have hne := hpx.ne_top
  have h2 : UpperSemicontinuousAt
      (fun y => (chartFunction u e y + (ρ y : EReal)) + ((-ρ y : ℝ) : EReal)) (e.val x) := by
    refine h1.add' hneg.upperSemicontinuousAt ?_
    exact EReal.continuousAt_add (Or.inl hne) (Or.inr (EReal.coe_ne_top _))
  have h3 : (fun y => (chartFunction u e y + (ρ y : EReal)) + ((-ρ y : ℝ) : EReal)) =
      chartFunction u e := by
    funext y
    have := FirstPass.corrected_add_sub (chartFunction u e y) (ρ y) 0
    simpa using this
  rw [h3] at h2
  have h4 : UpperSemicontinuousAt (chartFunction u e ∘ e.val) x :=
    UpperSemicontinuousAt.comp (by simpa only using h2) (e.val.continuousAt hxe)
  have hloc : chartFunction u e ∘ e.val =ᶠ[𝓝 x] u := by
    filter_upwards [e.val.open_source.mem_nhds hxe] with y hy
    simp only [Function.comp_apply, chartFunction, e.val.left_inv hy]
  refine ⟨?_, ?_⟩
  · intro c hc
    have hc' : (chartFunction u e ∘ e.val) x < c := by
      simpa only [hloc.eq_of_nhds] using hc
    filter_upwards [h4 c hc', hloc] with y hy hyeq
    rwa [← hyeq]
  · have : chartFunction u e (e.val x) + (ρ (e.val x) : EReal) ≠ ⊤ := hne
    intro htop
    apply this
    simp only [chartFunction, e.val.left_inv hxe, htop, EReal.top_add_coe]

/-- A `θ`-psh function on an open set is bounded above by a real number on every compact
subset. -/
theorem thetaOn_exists_le_of_isCompact {θ : SmoothRealForm n M 2}
    {u : M → EReal} {Ω : Set M} (hu : ThetaPlurisubharmonicOn θ u Ω) {K : Set M}
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) : ∃ B : ℝ, ∀ x ∈ K, u x ≤ (B : EReal) := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨0, fun x hx => absurd hx (Set.notMem_empty x)⟩
  have husc : UpperSemicontinuousOn u K := fun x hx =>
    (thetaOn_upperSemicontinuousAt hu (hKΩ hx)).1.upperSemicontinuousWithinAt K
  obtain ⟨a, ha, hmax⟩ := husc.exists_isMaxOn hne hK
  have hat : u a ≠ ⊤ := (thetaOn_upperSemicontinuousAt hu (hKΩ ha)).2
  refine ⟨(u a).toReal, fun x hx => (hmax hx).trans ?_⟩
  exact EReal.le_coe_toReal hat

/-- **Gluing by locally finite maxima on an open set.** If near every point of `Ω` the function
`Ψ` coincides with the maximum of finitely many branches, each `θ`-psh on that neighbourhood,
then `Ψ` is `θ`-psh on `Ω`. -/
theorem thetaPlurisubharmonicOn_of_locally_finset_sup {ι : Type*}
    (θ : ClosedRealOneOneForm n M) {Ψ : M → EReal} {b : ι → M → EReal} {Ω : Set M}
    (hloc : ∀ p ∈ Ω, ∃ N : Set M, IsOpen N ∧ p ∈ N ∧ ∃ J : Finset ι,
      (∀ j ∈ J, ThetaPlurisubharmonicOn θ.val (b j) N) ∧
      ∀ y ∈ N, Ψ y = J.sup fun j => b j y) :
    ThetaPlurisubharmonicOn θ.val Ψ Ω := by
  intro e z hz hzΩ
  obtain ⟨N, hN, hpN, J, hJ, hΨ⟩ := hloc (e.val.symm z) hzΩ
  obtain ⟨W₀, ρ, hzW₀, hρ⟩ := LocalPotentials.closedRealOneOne_hasLocalPotentials θ e z hz
  set W : Set (ComplexModel n) := W₀ ∩ (e.val.target ∩ e.val.symm ⁻¹' N) with hWdef
  have hWopen : IsOpen W := hρ.1.inter (e.val.isOpen_inter_preimage_symm hN)
  refine ⟨W, ρ, ⟨hzW₀, hz, hpN⟩, hρ.mono hWopen inter_subset_left, ?_⟩
  intro y hy
  have hρW : IsSmoothLocalPotential θ.val e W ρ := hρ.mono hWopen inter_subset_left
  have hsup : PlurisubharmonicAt
      (fun x => J.sup fun j => chartFunction (b j) e x + (ρ x : EReal)) y :=
    IdealFunctionMaxGluing.plurisubharmonicAt_finset_sup J fun j hj =>
      IdealFunctionMaxGluing.ThetaPlurisubharmonicOn.plurisubharmonicAt_add_potential
        (hJ j hj) e hρW hy hy.2.2
  refine hsup.congr ?_
  filter_upwards [hWopen.mem_nhds hy] with x hx
  rw [← IdealFunctionMaxGluing.finset_sup_add_coe]
  simp only [chartFunction]
  rw [hΨ _ hx.2.2]

/-- **One chart decides `θ`-psh on its domain.** If a single atlas chart `d` covers `Ω` and at
every point of `Ω` the function has a `θ`-psh witness in `d`, then it is `θ`-psh on `Ω`. -/
theorem thetaPlurisubharmonicOn_of_chart {θ : SmoothRealForm n M 2} {u : M → EReal}
    {Ω : Set M} (d : ComplexChart n M) (hΩd : Ω ⊆ d.val.source)
    (h : ∀ x ∈ Ω, ∃ W ρ, d.val x ∈ W ∧ IsSmoothLocalPotential θ d W ρ ∧
      PlurisubharmonicOn (fun y => chartFunction u d y + (ρ y : EReal)) W) :
    ThetaPlurisubharmonicOn θ u Ω := by
  intro e z hz hzΩ
  obtain ⟨W', ρ', hxW, hρ, hp⟩ := h _ hzΩ
  have hxe : e.val.symm z ∈ e.val.source := e.val.map_target hz
  obtain ⟨W, ρ, hW, hρW, hpW⟩ :=
    OpensRestriction.exists_witness_of_chart e d hxe (hΩd hzΩ) hxW hρ hp
  rw [e.val.right_inv hz] at hW
  exact ⟨W, ρ, hW, hρW, hpW⟩

end SGPT.Okounkov.TranscendentalExtension
