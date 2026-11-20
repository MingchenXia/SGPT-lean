import SGPT.Foundations.Analysis.Pending.GlobalQuasiPshMultiplierCoherence
import SGPT.Foundations.Analysis.Pending.MultiplierIdealNonzeroGerm
import SGPT.Foundations.Analysis.Pending.HironakaAPI

set_option autoImplicit false

/-! # Natural nonzero multiplier germs and local principalization for global quasi-PSH -/

open Set Filter TopologicalSpace MeasureTheory
open scoped Topology Manifold

universe u

namespace SGPT.Foundations.Analysis.Pending.GlobalQuasiPshMultiplierPrincipalization

open FirstPass FirstPass.HolomorphicIdealSheaves FirstPass.BlowupSequences
  NormalCrossings HironakaAdmissibleSequence

noncomputable section

/-- Actual local nondegeneracy supplies a nonzero germ without a background form. -/
theorem exists_nonzero_germ_of_isGlobalQuasiPshPotential
    {n : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    {u : X → EReal} (hu : IsGlobalQuasiPshPotential (n := n) u)
    {c : ℝ} (hc : 0 < c) (x : X) :
    ∃ g : X → ℂ, (multiplierIdeal (n := n) c u).mem x g ∧
      ∃ᶠ y in 𝓝 x, g y ≠ 0 := by
  classical
  let e : ComplexChart n X := complexChartAt (n := n) x
  have hxs : x ∈ e.val.source := mem_complexChartAt_source x
  obtain ⟨W, P, ρ, hW, hzW, hpsh, hρc, heq⟩ :=
    GlobalQuasiPshMultiplierCoherence.exists_open_psh_decomposition
      (hu.1 e (e.val x) (e.val.map_source hxs))
  have hrawfinite : ∃ᶠ z in 𝓝 (e.val x), chartFunction u e z ≠ ⊥ := by
    apply Filter.frequently_iff_forall_eventually_exists_and.mpr
    intro q hq
    obtain ⟨T, hTsub, hTopen, hzT⟩ := mem_nhds_iff.mp hq
    have hVopen : IsOpen (e.val.source ∩ e.val ⁻¹' T) :=
      e.val.isOpen_inter_preimage hTopen
    obtain ⟨y, hy, hny⟩ := hu.2 x _ hVopen ⟨hxs, hzT⟩
    refine ⟨e.val y, ?_, hTsub hy.2⟩
    change u (e.val.symm (e.val y)) ≠ ⊥
    simpa only [e.val.left_inv hy.1] using hny
  have hfinite : ∃ᶠ z in 𝓝 (e.val x), P z ≠ ⊥ := by
    apply (hrawfinite.and_eventually (hW.mem_nhds hzW)).mono
    intro z hz
    have hnz := hz.1
    rw [heq z hz.2] at hnz
    exact (EReal.add_ne_bot_iff.mp hnz).1
  obtain ⟨h, hh, hnz⟩ :=
    MultiplierIdealNonzeroGerm.exists_multiplierIntegrableAt_frequently_ne_zero
      W P hW hpsh (e.val x) hzW c hc hfinite
  have hmore : MoreSingularAt P (chartFunction u e) (e.val x) := by
    obtain ⟨C, hC⟩ := QuantitativeRegularizationChartGermTransfer.moreSingularAt_add_continuous
      (u := P) hW hρc hzW
    refine ⟨C, ?_⟩
    filter_upwards [hC, hW.mem_nhds hzW] with z hz hzW'
    rw [heq z hzW']
    exact hz
  have hraw : MultiplierIntegrableAt (chartFunction u e) c h (e.val x) volume :=
    multiplierIntegrableAt_of_moreSingularAt
      (hu.1 e (e.val x) (e.val.map_source hxs)) hmore hh
  have hhol : ∀ᶠ z in 𝓝 (e.val x), DifferentiableAt ℂ h z := by
    obtain ⟨_, O, hO, hzO, hd, _⟩ := hh
    filter_upwards [hO.mem_nhds hzO] with z hz
    exact hd.differentiableAt (hO.mem_nhds hz)
  let g : X → ℂ := fun y => h (e.val y)
  have hchart : h =ᶠ[𝓝 (e.val x)] fun z => g (e.val.symm z) := by
    filter_upwards [e.val.open_target.mem_nhds (e.val.map_source hxs)] with z hz
    simp only [g, e.val.right_inv hz]
  have hT : Tendsto e.val.symm (𝓝 (e.val x)) (𝓝 x) := by
    have ht := e.val.continuousAt_symm (e.val.map_source hxs)
    rw [ContinuousAt, e.val.left_inv hxs] at ht
    exact ht
  refine ⟨g, ⟨MultiplierIdealBergmanNadelManifold.holomorphicAt_comp_chart hxs hhol,
    hraw.congr (EventuallyEq.refl _ _) hchart⟩, ?_⟩
  apply Filter.frequently_iff_forall_eventually_exists_and.mpr
  intro q hq
  have hnear : ∀ᶠ z in 𝓝 (e.val x), z ∈ e.val.target ∧ q (e.val.symm z) :=
    (show ∀ᶠ z in 𝓝 (e.val x), z ∈ e.val.target from
      e.val.open_target.mem_nhds (e.val.map_source hxs)).and (hT.eventually hq)
  obtain ⟨z, hz, hzT, hzq⟩ := (hnz.and_eventually hnear).exists
  refine ⟨e.val.symm z, ?_, hzq⟩
  simpa only [g, e.val.right_inv hzT] using hz


/-- Actual Nadel coherence and nonzero germs supply compact principalization for raw QPSH. -/
theorem exists_principalization_of_isGlobalQuasiPshPotential
    {n : ℕ} (hn : 0 < n) {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] [CompactSpace X]
    {u : X → EReal} (hu : IsGlobalQuasiPshPotential (n := n) u)
    {c : ℝ} (hc : 0 < c) :
    ∃ (X' : Type u) (_ : TopologicalSpace X') (_ : ChartedSpace (ComplexModel n) X')
      (_ : IsComplexManifold n X') (f : X' → X) (D : EffectiveDivisor n X')
      (E : List (Set X')),
      IsAdmissibleBlowupSequence n X [] (multiplierIdeal (n := n) c u).zeroLocus X' f E ∧
      GermIdeal.pullback (m := n) f (multiplierIdeal (n := n) c u) = D.ideal ∧
      IsSNCDivisor n E ∧ D.support = ⋃ H ∈ E, H ∧
      D.support = f ⁻¹' (multiplierIdeal (n := n) c u).zeroLocus ∧
      IsIsomorphismOver n f (multiplierIdeal (n := n) c u).zeroLocusᶜ :=
  HironakaAPI.exists_principalization
    (GlobalQuasiPshMultiplierCoherence.isCoherent_multiplierIdeal_of_manifoldQuasiPlurisubharmonic
      hn hu.1 hc)
    (fun x => exists_nonzero_germ_of_isGlobalQuasiPshPotential hu hc x)

/-- On any complex manifold the actual local consumer supplies the relatively compact domain. -/
theorem exists_principalization_local_of_isGlobalQuasiPshPotential
    {n : ℕ} (hn : 0 < n) {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    {u : X → EReal} (hu : IsGlobalQuasiPshPotential (n := n) u)
    {c : ℝ} (hc : 0 < c) {K : Set X} (hK : IsCompact K) :
    ∃ U : Opens X, K ⊆ U ∧ IsCompact (closure (U : Set X)) ∧
    ∃ (U' : Type u) (_ : TopologicalSpace U') (_ : ChartedSpace (ComplexModel n) U')
      (_ : IsComplexManifold n U') (f : U' → U) (D : EffectiveDivisor n U')
      (E : List (Set U')),
      IsAdmissibleBlowupSequence n U []
        ((Subtype.val : U → X) ⁻¹' (multiplierIdeal (n := n) c u).zeroLocus) U' f E ∧
      GermIdeal.pullback (m := n) f
        (GermIdeal.pullback (m := n) (Subtype.val : U → X) (multiplierIdeal (n := n) c u)) = D.ideal ∧
      IsSNCDivisor n E ∧ D.support = ⋃ H ∈ E, H ∧
      D.support = f ⁻¹' ((Subtype.val : U → X) ⁻¹' (multiplierIdeal (n := n) c u).zeroLocus) ∧
      IsIsomorphismOver n f ((Subtype.val : U → X) ⁻¹' (multiplierIdeal (n := n) c u).zeroLocus)ᶜ :=
  HironakaAPI.exists_principalization_local
    (GlobalQuasiPshMultiplierCoherence.isCoherent_multiplierIdeal_of_manifoldQuasiPlurisubharmonic
      hn hu.1 hc)
    (fun x => exists_nonzero_germ_of_isGlobalQuasiPshPotential hu hc x) hK

end
end SGPT.Foundations.Analysis.Pending.GlobalQuasiPshMultiplierPrincipalization
