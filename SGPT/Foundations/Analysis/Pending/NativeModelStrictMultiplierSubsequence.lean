import SGPT.Foundations.Analysis.Pending.GenuineMultiplierStrictGap
import SGPT.Foundations.Analysis.Pending.IEnvelopeModelSubsequenceNativeLimit
import SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityMassLipschitz

set_option autoImplicit false

/-! # Actual strict-gap multiplier subsequences from native model geometry -/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.NativeModelStrictMultiplierSubsequence
open FirstPass FirstPass.HolomorphicIdealSheaves FirstPass.PositiveClasses
  FirstPass.NonKahlerLocus FirstPass.IEnvelope ThetaPshL1Topology
  DiagonalMass MixedMass SingularCanonicalSingularityDistance SingularCanonicalSingularityIncreasing
  SingularCanonicalSingularityMassLipschitz SingularCanonicalSingularityModelSandwich
  ConvexCombEnvelopeMass ThetaPshConvexCombination ActualDecreasingModelInfimum IncreasingMixedDirectedNets

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

/-- Actual native model geometry and mass limits internally supply the affine
barriers and eventually every prescribed strict-gap ideal inclusion. -/
theorem exists_strictMono_eventually_multiplierIdeal_le
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    (ui : ℕ → ThetaPshL1 θ.val) (u : ThetaPshL1 θ.val)
    (hmodels : ∀ j, IsModelPotential θ (ui j).val) {δ : ℝ}
    (hδ : 0 < δ) (hstage : ∀ j, ENNReal.ofReal δ ≤
      diagonalPotentialMass θ (ui j).val (ui j).property)
    (hpos : HasPositivePotentialMass θ u.val u.property)
    {p q : ℝ} (hp : 0 < p) (hpq : p < q)
    (hlim : Tendsto ui atTop (@nhds (ThetaPshL1 θ.val)
      (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace u)) :
    ∃ f : ℕ → ℕ, StrictMono f ∧ ∀ᶠ j in atTop,
      (multiplierIdeal (n := n) q (ui (f j)).val).Le
        (multiplierIdeal (n := n) p u.val) := by
  let := singularityPseudoMetricSpace omega θ hbig
  let : TopologicalSpace (ThetaPshL1 θ.val) :=
    (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace
  obtain ⟨f, hf, η, ψ, _, _, hηmodel, hηmono, _, hbetween, hηlim, _⟩ :=
    exists_strictMono_monotone_sandwich_of_tendsto omega θ hbig ui u
      hmodels hδ hstage hlim
  have hη0 (j : ℕ) (x : M) : (η j).val x ≤ (0 : EReal) := by
    rw [(hηmodel j).envelope_eq]
    exact singularityEnvelope_le_zero θ.val (η j).val x
  let S : ThetaPshL1 θ.val := ⟨uscRegularization (⨆ j, (η j).val),
    isThetaPshPotential_regularized_of_uniformlyBounded (fun j => (η j).property) hη0⟩
  have hηS (j : ℕ) : (η j).val ≤ S.val :=
    (le_iSup (fun j => (η j).val) j).trans (le_uscRegularization _)
  have hSlim : Tendsto η atTop (𝓝 S) :=
    tendsto_native_of_monotone_uniformlyBounded omega θ hbig η hηmono hη0
  have hdSu : dist S u = 0 := by
    have h := hSlim.dist hηlim
    simp only [dist_self] at h
    exact tendsto_nhds_unique h tendsto_const_nhds
  obtain ⟨m, _, _, _, hm⟩ := exists_tendsto_singularityDistance omega θ hbig S.property u.property
  have hm0 : m = 0 := by
    simpa only [dist_eq_singularityDistance_toReal omega θ hbig, hm,
      EReal.toReal_coe] using hdSu
  have hz : singularityDistance omega θ hbig S.val u.val = 0 := by
    rw [hm, hm0, EReal.coe_zero]
  have heq := (SingularCanonicalDistanceZeroPEquivalence.singularityDistance_eq_zero_iff_sourcePEquivalent
    omega θ hbig S.property u.property).mp hz
  have hISu := PositiveCurrentTraceMultiplier.multiplierIdeal_le_of_iOrderOnManifold
    (GlobalPMultiplierOrder.iEquivalentOnManifold_of_sourcePEquivalent heq).1 hp
  obtain ⟨t₀, ht₀, hcompare⟩ :=
    GenuineMultiplierStrictGap.exists_multiplierIdeal_le_of_convexComb_le θ hp hpq
  let a : ℝ := 2 + 1 / t₀
  have ha : 1 < a := by dsimp [a]; have := one_div_pos.mpr ht₀; linarith
  have ha0 : 0 < a := zero_lt_one.trans ha
  have ht : 0 < a⁻¹ := inv_pos.mpr ha0
  have htt : a⁻¹ ≤ t₀ := by
    rw [← one_div]
    apply (div_le_iff₀ ha0).mpr
    have hprod : t₀ * a = 2 * t₀ + 1 := by dsimp [a]; field_simp
    rw [hprod]
    linarith
  let L : ℝ≥0∞ := diagonalPotentialMass θ u.val u.property
  have hLtop : L ≠ ⊤ := (globalMixedMass_lt_top omega (fun _ : Fin n => u.property.1)).ne
  have hnativeReal (w : ℕ → ThetaPshL1 θ.val) (hw : Tendsto w atTop (𝓝 u)) :
      Tendsto (fun j => (diagonalPotentialMass θ (w j).val (w j).property).toReal)
        atTop (𝓝 L.toReal) :=
    ((diagonalPotentialMass_uniformContinuous omega θ hbig).continuous.tendsto u).comp hw
  have hnativeENN (w : ℕ → ThetaPshL1 θ.val) (hw : Tendsto w atTop (𝓝 u)) :
      Tendsto (fun j => diagonalPotentialMass θ (w j).val (w j).property)
        atTop (𝓝 L) := by
    have h := ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hnativeReal w hw)
    have hread : (fun j => ENNReal.ofReal
        (diagonalPotentialMass θ (w j).val (w j).property).toReal) =
        fun j => diagonalPotentialMass θ (w j).val (w j).property := by
      funext j
      exact ENNReal.ofReal_toReal
        (globalMixedMass_lt_top omega (fun _ : Fin n => (w j).property.1)).ne
    simpa only [Function.comp_def, hread, ENNReal.ofReal_toReal hLtop] using h
  have hupper := hnativeENN (fun j => ui (f j)) (hlim.comp hf.tendsto_atTop)
  have hlower := hnativeENN η hηlim
  have hgap : Tendsto (fun j => diagonalPotentialMass θ (ui (f j)).val (ui (f j)).property -
      diagonalPotentialMass θ (η j).val (η j).property) atTop (𝓝 (0 : ℝ≥0∞)) := by
    simpa only [tsub_self] using ENNReal.Tendsto.sub hupper hlower (Or.inl hLtop)
  have hmul : Tendsto (fun j => ENNReal.ofReal (a ^ n) *
      (diagonalPotentialMass θ (ui (f j)).val (ui (f j)).property -
        diagonalPotentialMass θ (η j).val (η j).property)) atTop (𝓝 0) := by
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul
      (a := ENNReal.ofReal (a ^ n)) hgap (Or.inr ENNReal.ofReal_ne_top)
  have hadm : ∀ᶠ j in atTop, ConvexCombEnvelopeMass.IsAdmissibleWeight n
      (diagonalPotentialMass θ (η j).val (η j).property)
      (diagonalPotentialMass θ (ui (f j)).val (ui (f j)).property) a :=
    (hmul.eventually_lt hupper hpos).mono fun j hj => ⟨ha, hj⟩
  refine ⟨f, hf, hadm.mono fun j hj => ?_⟩
  obtain ⟨w, hw, hb⟩ := PositiveCurrentRooftop.exists_thetaPsh_convexCombBarrier_of_isBigClass
    omega θ hbig (η j).property (ui (f j)).property (hbetween j).1
      (hηmodel j).positive_mass hj
  have hconv : ∀ x, ((1 - a⁻¹ : ℝ) : EReal) * (ui (f j)).val x +
      (a⁻¹ : ℝ) * w x ≤ S.val x := by
    intro x
    have hpoint : ((1 - a⁻¹ : ℝ) : EReal) * (ui (f j)).val x +
        (a⁻¹ : ℝ) * w x ≤ (η j).val x := by
      simpa only [convexComb, add_comm] using hb x
    exact hpoint.trans (hηS j x)
  have hI := hcompare a⁻¹ ht htt (ui (f j)).property hw S.property hconv
  intro x g hg
  exact hISu x g (hI x g hg)

end
end SGPT.Foundations.Analysis.Pending.NativeModelStrictMultiplierSubsequence
