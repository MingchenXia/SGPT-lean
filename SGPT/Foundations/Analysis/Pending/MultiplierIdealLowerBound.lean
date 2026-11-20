import SGPT.Foundations.Analysis.Pending.MultiplierPullbackNonzero
import SGPT.Foundations.Analysis.Pending.UniformLocalCanonicalNecessity


set_option autoImplicit false
noncomputable section

open Set Filter
open scoped Topology Manifold ContDiff

namespace SGPT.Foundations.Analysis.Pending.MultiplierIdealLowerBound

open Set Filter
open scoped Topology Manifold ContDiff
open FirstPass FirstPass.HolomorphicMaps FirstPass.HolomorphicIdealSheaves FirstPass.BlowupSequences
  DemaillyApproximantDivisorialLelong FixedGermNormalOrder
  IdealPowerNormalOrder IntrinsicJacobianCoefficient
  HironakaHolomorphicJetRankLoci HironakaHolomorphicJetChartInvariance

universe u

variable {m : ℕ} {X Y : Type u}
  [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y]
  {π : Y → X} {E : Set Y} {u : X → EReal} {c : ℝ}

/-- Genuine nonzero/coherent whole pullback and connected continuation produce a unique finite coefficient. -/
theorem existsUnique_multiplierCoefficient
    (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := m + 1) π)
    (hE : IsClosedConnectedSubmanifold (m + 1) E m)
    (hu : IsGlobalQuasiPshPotential (n := m + 1) u) (hc : 0 < c) :
    ∃! a : ℕ, ∀ y ∈ E, ∀ Φ : DivisorFlattening (m := m) E y,
      originalStalkNormalOrder Φ (GermIdeal.pullback (m := m + 1) π (multiplierIdeal (n := m + 1) c u)) =
        (a : ℕ∞) := by
  have hcoh := MultiplierPullbackNonzero.isCoherent_pullback_multiplierIdeal hπ
    (Nat.succ_pos m) hu.1 hc
  have hnon := MultiplierPullbackNonzero.isNonzeroAt_pullback_multiplierIdeal hπ hu hc
  obtain ⟨a, ha⟩ := exists_originalStalkNormalOrder_on_connected_hypersurface hE _ hcoh hnon
  refine ⟨a, ha, ?_⟩
  intro b hb
  obtain ⟨y, hy⟩ := hE.2.1.nonempty
  obtain ⟨Φ⟩ := DivisorFlattening.nonempty_of_regularAtDim (hE.2.2 y hy)
  exact ENat.natCast_inj.mp ((hb y hy Φ).symm.trans (ha y hy Φ))

/-- The produced coefficient of the ENTIRE original pulled multiplier ideal. -/
def actualMultiplierCoefficient
    (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := m + 1) π)
    (hE : IsClosedConnectedSubmanifold (m + 1) E m)
    (hu : IsGlobalQuasiPshPotential (n := m + 1) u) (hc : 0 < c) : ℕ :=
  Classical.choose (existsUnique_multiplierCoefficient hπ hE hu hc)

/-- Every original point and every genuine flattening reads the same produced whole-ideal coefficient. -/
theorem originalStalkNormalOrder_eq_actualMultiplierCoefficient
    (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := m + 1) π)
    (hE : IsClosedConnectedSubmanifold (m + 1) E m)
    (hu : IsGlobalQuasiPshPotential (n := m + 1) u) (hc : 0 < c)
    (y : Y) (hy : y ∈ E) (Φ : DivisorFlattening (m := m) E y) :
    originalStalkNormalOrder Φ (GermIdeal.pullback (m := m + 1) π (multiplierIdeal (n := m + 1) c u)) =
      (actualMultiplierCoefficient hπ hE hu hc : ℕ∞) :=
  (Classical.choose_spec (existsUnique_multiplierCoefficient hπ hE hu hc)).1 y hy Φ

/-- All actual original vanishing-ideal powers are read by the produced coefficient. -/
theorem isDivNear_iff_le_actualMultiplierCoefficient
    (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := m + 1) π)
    (hE : IsClosedConnectedSubmanifold (m + 1) E m)
    (hu : IsGlobalQuasiPshPotential (n := m + 1) u) (hc : 0 < c)
    (y : Y) (hy : y ∈ E) (k : ℕ) :
    DivisorExponent.IsDivNear (m + 1)
      (GermIdeal.pullback (m := m + 1) π (multiplierIdeal (n := m + 1) c u)) E k y ↔
      k ≤ actualMultiplierCoefficient hπ hE hu hc := by
  obtain ⟨Φ⟩ := DivisorFlattening.nonempty_of_regularAtDim (hE.2.2 y hy)
  have hcoh := MultiplierPullbackNonzero.isCoherent_pullback_multiplierIdeal hπ
    (Nat.succ_pos m) hu.1 hc
  have hb := natCast_le_originalStalkNormalOrder_iff_isDivNear Φ _ hcoh k
  rw [originalStalkNormalOrder_eq_actualMultiplierCoefficient hπ hE hu hc y hy Φ] at hb
  exact hb.symm.trans ENat.natCast_le_natCast

/-- Coherence INTERNALLY selects an ORIGINAL nonzero member attaining the finite ENTIRE pullback order. -/
theorem exists_original_member_attaining_finite_pullback_order
    (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := m + 1) π)
    {y : Y} (Φ : DivisorFlattening (m := m) E y)
    (I : GermIdeal (m + 1) X) (hI : I.IsCoherent) (a : ℕ)
    (horder : originalStalkNormalOrder Φ (GermIdeal.pullback (m := m + 1) π I) = (a : ℕ∞)) :
    ∃ (F : X → ℂ) (hF : HolomorphicAt (m + 1) F (π y)),
      I.mem (π y) F ∧ (∃ᶠ z in 𝓝 (π y), F z ≠ 0) ∧
        pullbackNormalOrder hπ Φ F hF = (a : ℕ∞) := by
  classical
  obtain ⟨U, hU, hyU, s, G, hG, hgen, hpull⟩ :=
    FiniteGermIdealPullbackGenerators.exists_finite_generators_pullback_of_isCoherent
      (Eventually.of_forall fun _ => hπ.1.contMDiffAt) I hI
  let hGs : ∀ i, HolomorphicAt (m + 1) (G i) (π y) :=
    fun i => InvertibleIdealQuotient.holomorphicAt_of_mdifferentiableOn hU (hG i) hyU
  let hGt : ∀ i, HolomorphicAt (m + 1) (G i ∘ π) y :=
    fun i => (hGs i).comp_contMDiff (Eventually.of_forall fun _ => hπ.1.contMDiffAt)
  have hmin : (a : ℕ∞) = ⨅ i, pullbackNormalOrder hπ Φ (G i) (hGs i) := by
    exact horder.symm.trans (originalStalkNormalOrder_eq_generators Φ _
      (fun i => G i ∘ π) hGt hpull)
  have hsome : ∃ i, pullbackNormalOrder hπ Φ (G i) (hGs i) = (a : ℕ∞) := by
    by_contra hn
    push Not at hn
    have hs : ((a + 1 : ℕ) : ℕ∞) ≤ ⨅ i, pullbackNormalOrder hπ Φ (G i) (hGs i) := by
      apply le_iInf
      intro i
      have hle : (a : ℕ∞) ≤ pullbackNormalOrder hπ Φ (G i) (hGs i) := by
        rw [hmin]
        exact iInf_le _ i
      have hlt := lt_of_le_of_ne hle (Ne.symm (hn i))
      simpa only [ENat.natCast_add, ENat.natCast_one] using
        (ENat.natCast_add_one_le_iff.mpr hlt)
    rw [← hmin] at hs
    exact Nat.not_succ_le_self a (ENat.natCast_le_natCast.mp hs)
  obtain ⟨i, hi⟩ := hsome
  have hiI : I.mem (π y) (G i) :=
    (hgen (π y) hyU (G i)).mpr
      (InvertibleIdealQuotient.isInSpanAt_self ⟨i, rfl⟩ (hGs i))
  refine ⟨G i, hGs i, hiI, ?_, hi⟩
  by_contra hn
  have hzero : G i =ᶠ[𝓝 (π y)] (fun _ => 0) := by
    filter_upwards [Filter.not_frequently.mp hn] with z hz
    exact not_ne_iff.mp hz
  have hzHol : HolomorphicAt (m + 1) (fun _ : X => (0 : ℂ)) (π y) :=
    Eventually.of_forall fun _ => mdifferentiableAt_const
  have hcongr := pullbackNormalOrder_congr hπ Φ (hGs i) hzHol hzero
  have hzGerm : chartTranslatedGerm y y (mem_chart_source _ y)
      ((fun _ : X => (0 : ℂ)) ∘ π)
      (hzHol.comp_contMDiff (Eventually.of_forall fun _ => hπ.1.contMDiffAt)) = 0 := by
    apply Subtype.ext
    rfl
  have hzorder : pullbackNormalOrder hπ Φ (fun _ : X => (0 : ℂ)) hzHol = ⊤ := by
    change normalOrder Φ _ = ⊤
    rw [hzGerm, normalOrder_zero]
  have haTop : (a : ℕ∞) = ⊤ := hi.symm.trans (hcongr.trans hzorder)
  exact ENat.natCast_ne_top a haTop

/-- The actual multiplier input supplies all finiteness/generation premises of original-member attainment. -/
theorem exists_original_multiplier_member_attaining_coefficient
    (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := m + 1) π)
    (hE : IsClosedConnectedSubmanifold (m + 1) E m)
    (hu : IsGlobalQuasiPshPotential (n := m + 1) u) (hc : 0 < c)
    (y : Y) (hy : y ∈ E) (Φ : DivisorFlattening (m := m) E y) :
    ∃ (F : X → ℂ) (hF : HolomorphicAt (m + 1) F (π y)),
      (multiplierIdeal (n := m + 1) c u).mem (π y) F ∧
        (∃ᶠ z in 𝓝 (π y), F z ≠ 0) ∧
        pullbackNormalOrder hπ Φ F hF = (actualMultiplierCoefficient hπ hE hu hc : ℕ∞) := by
  exact exists_original_member_attaining_finite_pullback_order hπ Φ _
    (GlobalQuasiPshMultiplierCoherence.isCoherent_multiplierIdeal_of_manifoldQuasiPlurisubharmonic
      (Nat.succ_pos m) hu.1 hc) _
    (originalStalkNormalOrder_eq_actualMultiplierCoefficient hπ hE hu hc y hy Φ)

/-- The genuine ENTIRE pulled multiplier coefficient satisfies the canonical strict raw-Lelong lower bound. -/
theorem actualMultiplierCoefficient_strict_raw_lelong_bound
    (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := m + 1) π)
    (hE : IsClosedConnectedSubmanifold (m + 1) E m)
    (hu : IsGlobalQuasiPshPotential (n := m + 1) u) (hc : 0 < c) :
    ENNReal.ofReal c *
      (⨅ z ∈ E, FirstPass.NonKahlerLocus.lelongNumber (n := m + 1) (fun t => u (π t)) z) <
        ENNReal.ofReal (2 * ((actualMultiplierCoefficient hπ hE hu hc +
          representedLogDiscrepancy hπ hE : ℕ) : ℝ)) := by
  obtain ⟨y, hy⟩ := hE.2.1.nonempty
  obtain ⟨Φ⟩ := DivisorFlattening.nonempty_of_regularAtDim (hE.2.2 y hy)
  obtain ⟨F, hF, hFI, hFnon, hForder⟩ :=
    exists_original_multiplier_member_attaining_coefficient hπ hE hu hc y hy Φ
  obtain ⟨δ, hδ, hmodels⟩ :=
    UniformLocalCanonicalNecessity.exists_uniform_canonical_local_bound hu.1 hFI hFnon
  obtain ⟨b, hb, hbound⟩ := hmodels Y π hπ E hE y rfl Φ
  have hbEq : b = actualMultiplierCoefficient hπ hE hu hc :=
    ENat.natCast_inj.mp (hb.symm.trans hForder)
  rw [hbEq] at hbound
  have hcδ : c ≤ (1 + δ) * c := by nlinarith
  apply lt_of_le_of_lt ?_ hbound
  exact mul_le_mul (ENNReal.ofReal_le_ofReal hcδ) le_rfl zero_le zero_le

end SGPT.Foundations.Analysis.Pending.MultiplierIdealLowerBound
