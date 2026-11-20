import SGPT.Foundations.Analysis.Pending.SingularNativeCommonBackground
import SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityFiniteMaximumChains

set_option autoImplicit false

/-! # Actual original pair distances from a common limit in another background

SGPT PDF0238 paired-distance consequence and PDF0275 (8.1): actual
selected-background difference polynomials recover the original join
gap. The common candidate is genuine only in the given limit background.
-/

open Set Filter MeasureTheory Polynomial
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.SingularNativePairedBackground

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
  ThetaPshL1Topology RelativeEnergy MixedMass GlobalNonPluripolar GlobalDiagonalScaling
  SingularMinimalCanonicalRay SingularCanonicalSingularityDistance
  SingularNativeCommonBackground SingularCanonicalSingularityFiniteMaximumChains
  SingularCanonicalSingularityMassComparison ActualMixedMassJoinGap
  ActualNativeMixedMassContinuity ActualPartialBackgroundMassPolynomial
  FinitePolynomialEvaluationContinuity

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

private theorem tendsto_max_of_common_native_limit (omega : KahlerBackground n M)
    (γ : ClosedRealOneOneForm n M) (hγ : IsBigClass (RealBottChern.ofRepresentative γ))
    {I : Type*} (F : Filter I) (a b : I → ThetaPshL1 γ.val) (τ : ThetaPshL1 γ.val)
    (ha : Tendsto a F (@nhds (ThetaPshL1 γ.val)
      (singularityPseudoMetricSpace omega γ hγ).toUniformSpace.toTopologicalSpace τ))
    (hb : Tendsto b F (@nhds (ThetaPshL1 γ.val)
      (singularityPseudoMetricSpace omega γ hγ).toUniformSpace.toTopologicalSpace τ)) :
    Tendsto (fun i => (⟨fun x => max ((a i).val x) ((b i).val x),
      IsThetaPshPotential.max (a i).property (b i).property⟩ : ThetaPshL1 γ.val)) F
      (@nhds (ThetaPshL1 γ.val)
        (singularityPseudoMetricSpace omega γ hγ).toUniformSpace.toTopologicalSpace τ) := by
  let := singularityPseudoMetricSpace omega γ hγ
  let : TopologicalSpace (ThetaPshL1 γ.val) :=
    (singularityPseudoMetricSpace omega γ hγ).toUniformSpace.toTopologicalSpace
  let C : ℝ := 3 * (2 : ℝ) ^ (n + 2) * ((n : ℝ) + 1)
  let Z : I → ThetaPshL1 γ.val := fun i =>
    ⟨fun x => max ((a i).val x) ((b i).val x),
      IsThetaPshPotential.max (a i).property (b i).property⟩
  have hda := tendsto_iff_dist_tendsto_zero.mp ha
  have hdb := tendsto_iff_dist_tendsto_zero.mp hb
  have hab : Tendsto (fun i => dist (a i) (b i)) F (𝓝 0) := by
    have h := hda.add hdb
    simp only [add_zero] at h
    apply squeeze_zero (fun _ => dist_nonneg) (fun i => ?_) h
    simpa only [dist_comm τ (b i)] using dist_triangle (a i) τ (b i)
  have hupper : Tendsto (fun i => C * dist (a i) (b i) + dist (a i) τ) F (𝓝 0) := by
    simpa only [mul_zero, add_zero] using (hab.const_mul C).add hda
  have hbound (i : I) : dist (Z i) τ ≤ C * dist (a i) (b i) + dist (a i) τ := by
    have hm : dist (a i) (Z i) + dist (b i) (Z i) ≤ C * dist (a i) (b i) :=
      dist_max_sum_le_mul omega γ hγ (a i) (b i)
    have hZ : dist (Z i) (a i) ≤ C * dist (a i) (b i) := by
      rw [dist_comm]
      exact (le_add_of_nonneg_right dist_nonneg).trans hm
    have ht : dist (Z i) τ ≤ dist (Z i) (a i) + dist (a i) τ := dist_triangle _ _ _
    exact ht.trans (add_le_add hZ (le_refl (dist (a i) τ)))
  change Tendsto Z F (𝓝 τ)
  exact tendsto_iff_dist_tendsto_zero.mpr
    (squeeze_zero (fun _ => dist_nonneg) hbound hupper)

private theorem tendsto_endpoint_difference_of_common_native_limit
    (omega : KahlerBackground n M) (θ γ : ClosedRealOneOneForm n M)
    (hθ : IsBigClass (RealBottChern.ofRepresentative θ))
    (hγ : IsBigClass (RealBottChern.ofRepresentative γ))
    {I : Type*} (F : Filter I) {a b : I → M → EReal} {τ : M → EReal}
    (haθ : ∀ i, IsThetaPshPotential θ.val (a i))
    (hbθ : ∀ i, IsThetaPshPotential θ.val (b i))
    (haγ : ∀ i, IsThetaPshPotential γ.val (a i))
    (hbγ : ∀ i, IsThetaPshPotential γ.val (b i))
    (hτ : IsThetaPshPotential γ.val τ)
    (ha : Tendsto (fun i => (⟨a i, haγ i⟩ : ThetaPshL1 γ.val)) F
      (@nhds (ThetaPshL1 γ.val)
        (singularityPseudoMetricSpace omega γ hγ).toUniformSpace.toTopologicalSpace ⟨τ, hτ⟩))
    (hb : Tendsto (fun i => (⟨b i, hbγ i⟩ : ThetaPshL1 γ.val)) F
      (@nhds (ThetaPshL1 γ.val)
        (singularityPseudoMetricSpace omega γ hγ).toUniformSpace.toTopologicalSpace ⟨τ, hτ⟩))
    (j : Fin (n + 1)) :
    Tendsto (fun i =>
      (endpointMixedMass θ (thetaPshSupremum θ.val) (a i)
        (isModelPotential_thetaPshSupremum omega θ hθ).plurisubharmonic (haθ i) j).toReal -
      (endpointMixedMass θ (thetaPshSupremum θ.val) (b i)
        (isModelPotential_thetaPshSupremum omega θ hθ).plurisubharmonic (hbθ i) j).toReal) F (𝓝 0) := by
  classical
  let φ := thetaPshSupremum θ.val
  have hφ : IsThetaPshPotential θ.val φ :=
    (isModelPotential_thetaPshSupremum omega θ hθ).plurisubharmonic
  let S : Finset (Fin n) := Finset.univ.filter fun k => k.val < j.val
  let endpoint : (I → M → EReal) → I → Fin n → M → EReal :=
    fun r i => endpointMixedPotential j (r i) φ
  have hendpoint (r : I → M → EReal) (hr : ∀ i, IsThetaPshPotential θ.val (r i))
      (i : I) (k : Fin n) : IsThetaPshPotential θ.val (endpoint r i k) := by
    dsimp [endpoint, endpointMixedPotential]
    split_ifs <;> first | exact hr i | exact hφ
  let poly (r : I → M → EReal) (hr : ∀ i, IsThetaPshPotential θ.val (r i)) (i : I) : ℝ[X] :=
    partialBackgroundMassPolynomial omega (fun _ => θ) (endpoint r i) (hendpoint r hr i) S
  let p : I → ℝ[X] := fun i => poly a haθ i - poly b hbθ i
  obtain ⟨C, hC, hK⟩ := KahlerDomination.exists_pos_isKahler_add_smul omega (θ - γ)
  let κ : KahlerBackground n M := ⟨θ - γ + C • omega.form, hK⟩
  have hτlarge : IsThetaPshPotential (γ + κ.form).val τ :=
    LocalPotentials.isThetaPshPotential_add_of_semipositive hτ κ.isSemipositive
  have hpositive (c : ℝ) (hc : C < c) :
      Tendsto (fun i => (p i).eval c) F (𝓝 0) := by
    have hc0 : 0 < c := hC.trans hc
    let θc := θ + c • omega.form
    have hθc : IsBigClass (RealBottChern.ofRepresentative θc) :=
      PositiveCurrentAssembly.isBigClass_add_smul_of_isThetaPshPotential omega θ hφ hc0
    have hτc : IsThetaPshPotential θc.val τ := by
      have h := LocalPotentials.isThetaPshPotential_add_of_semipositive hτlarge
        (KahlerDomination.isSemipositive_smul omega.isSemipositive (sub_pos.mpr hc).le)
      have e : (γ + κ.form) + (c - C) • omega.form = θc := by
        dsimp only [κ, θc]
        module
      simpa only [e] using h
    let θB : Bool → ClosedRealOneOneForm n M := fun s => if s then θc else θ
    let vB : Bool → M → EReal := fun s => if s then τ else φ
    have hB (s : Bool) : IsBigClass (RealBottChern.ofRepresentative (θB s)) := by
      cases s <;> first | exact hθ | exact hθc
    have hvB (s : Bool) : IsThetaPshPotential (θB s).val (vB s) := by
      cases s <;> first | exact hφ | exact hτc
    let η : Fin n → ClosedRealOneOneForm n M := fun k => θB (decide (k.val < j.val))
    let T : Fin n → M → EReal := fun k => vB (decide (k.val < j.val))
    have hη (k : Fin n) : IsBigClass (RealBottChern.ofRepresentative (η k)) :=
      hB (decide (k.val < j.val))
    have hT (k : Fin n) : IsThetaPshPotential (η k).val (T k) :=
      hvB (decide (k.val < j.val))
    have hforms : η = fun k => θ + (if k ∈ S then c else 0) • omega.form := by
      funext k
      by_cases hk : k.val < j.val <;> simp [η, θB, θc, S, hk]
    have hconst : Tendsto (fun _ : I => (⟨φ, hφ⟩ : ThetaPshL1 θ.val)) F
        (@nhds (ThetaPshL1 θ.val)
          (singularityPseudoMetricSpace omega θ hθ).toUniformSpace.toTopologicalSpace ⟨φ, hφ⟩) := by
      let := singularityPseudoMetricSpace omega θ hθ
      let : TopologicalSpace (ThetaPshL1 θ.val) :=
        (singularityPseudoMetricSpace omega θ hθ).toUniformSpace.toTopologicalSpace
      let z : ThetaPshL1 θ.val := ⟨φ, hφ⟩
      change Tendsto (fun _ : I => z) F (𝓝 z)
      exact tendsto_const_nhds
    have hmass (r : I → M → EReal) (hrθ : ∀ i, IsThetaPshPotential θ.val (r i))
        (hrγ : ∀ i, IsThetaPshPotential γ.val (r i))
        (hlimr : Tendsto (fun i => (⟨r i, hrγ i⟩ : ThetaPshL1 γ.val)) F
          (@nhds (ThetaPshL1 γ.val)
            (singularityPseudoMetricSpace omega γ hγ).toUniformSpace.toTopologicalSpace ⟨τ, hτ⟩)) :
        Tendsto (fun i => (poly r hrθ i).eval c) F
          (𝓝 (globalMixedMass η T (fun k => (hT k).1)).toReal) := by
      have hrc (i : I) : IsThetaPshPotential θc.val (r i) :=
        LocalPotentials.isThetaPshPotential_add_of_semipositive (hrθ i)
          (KahlerDomination.isSemipositive_smul omega.isSemipositive hc0.le)
      have hlimc := (tendsto_native_iff_common_backgrounds omega γ θc hγ hθc F
        hrγ hτ hrc hτc).mp hlimr
      let rB : I → Bool → M → EReal := fun i s => if s then r i else φ
      have hrB (i : I) (s : Bool) : IsThetaPshPotential (θB s).val (rB i s) := by
        cases s <;> first | exact hφ | exact hrc i
      have hlimB (s : Bool) : Tendsto
          (fun i => (⟨rB i s, hrB i s⟩ : ThetaPshL1 (θB s).val)) F
          (@nhds (ThetaPshL1 (θB s).val)
            (singularityPseudoMetricSpace omega (θB s) (hB s)).toUniformSpace.toTopologicalSpace
            ⟨vB s, hvB s⟩) := by
        cases s
        · exact hconst
        · exact hlimc
      let R : I → Fin n → M → EReal := fun i k => rB i (decide (k.val < j.val))
      have hR (i : I) (k : Fin n) : IsThetaPshPotential (η k).val (R i k) :=
        hrB i (decide (k.val < j.val))
      have hslot (k : Fin n) : Tendsto
          (fun i => (⟨R i k, hR i k⟩ : ThetaPshL1 (η k).val)) F
          (@nhds (ThetaPshL1 (η k).val)
            (singularityPseudoMetricSpace omega (η k) (hη k)).toUniformSpace.toTopologicalSpace
            ⟨T k, hT k⟩) := hlimB (decide (k.val < j.val))
      have hm := tendsto_globalMixedMass_of_native omega hη F hR hT hslot
      have ht := (ENNReal.tendsto_toReal (globalMixedMass_lt_top omega
        (fun k => (hT k).1)).ne).comp hm
      have hQU (i : I) : R i = endpoint r i := by
        funext k
        by_cases hk : k.val < j.val <;> simp [R, rB, endpoint, endpointMixedPotential, hk]
      have heval (i : I) : (poly r hrθ i).eval c =
          (globalMixedMass η (R i) (fun k => (hR i k).1)).toReal := by
        rw [← globalMixedMass_partial_background_toReal_eq_eval omega (hendpoint r hrθ i) S hc0.le]
        unfold globalMixedMass
        exact congrArg (fun μ : Measure M => (μ univ).toReal)
          (globalMixedMeasure_congr hforms (hQU i) _ _).symm
      simpa only [heval, Function.comp_def] using ht
    have h := (hmass a haθ haγ ha).sub (hmass b hbθ hbγ hb)
    simpa only [sub_self, p, eval_sub] using h
  let nodes : Fin (n + 1) → ℝ := fun k => C + 2 + (k.val : ℝ)
  have hnodes : Function.Injective nodes := by
    intro k l h
    apply Fin.ext
    have he : (k.val : ℝ) = l.val := by dsimp [nodes] at h; linarith
    exact_mod_cast he
  have hn (k : Fin (n + 1)) : C < nodes k := by
    dsimp [nodes]
    have hk : (0 : ℝ) ≤ k.val := Nat.cast_nonneg _
    linarith
  have hpdegree (i : I) : (p i).natDegree ≤ n :=
    (natDegree_sub_le _ _).trans (max_le
      (natDegree_partialBackgroundMassPolynomial_le omega (fun _ => θ)
        (endpoint a i) (hendpoint a haθ i) S)
      (natDegree_partialBackgroundMassPolynomial_le omega (fun _ => θ)
        (endpoint b i) (hendpoint b hbθ i) S))
  have ht := tendsto_eval_of_finite_evaluations F nodes hnodes p 0 hpdegree
    (by simp) (fun k => by simpa only [eval_zero] using hpositive (nodes k) (hn k)) 0
  have hzero (r : I → M → EReal) (hr : ∀ i, IsThetaPshPotential θ.val (r i)) (i : I) :
      (poly r hr i).eval 0 = (endpointMixedMass θ φ (r i) hφ (hr i) j).toReal := by
    have h := (globalMixedMass_partial_background_toReal_eq_eval omega
      (hendpoint r hr i) S (a := 0) le_rfl).symm
    simpa only [ite_self, zero_smul, add_zero, globalMixedMass,
      endpointMixedMass, endpointMixedMeasure] using h
  simpa only [p, eval_sub, eval_zero, hzero] using ht

/-- Actual enlarged common-limit mass differences recover the original join
gap, without requiring the common candidate to be original-background PSH. -/
theorem tendsto_singularityDistance_toReal_zero_of_common_native_limit
    (omega : KahlerBackground n M) (θ γ : ClosedRealOneOneForm n M)
    (hθ : IsBigClass (RealBottChern.ofRepresentative θ))
    (hγ : IsBigClass (RealBottChern.ofRepresentative γ))
    {I : Type*} (F : Filter I) {a b : I → M → EReal} {τ : M → EReal}
    (haθ : ∀ i, IsThetaPshPotential θ.val (a i))
    (hbθ : ∀ i, IsThetaPshPotential θ.val (b i))
    (haγ : ∀ i, IsThetaPshPotential γ.val (a i))
    (hbγ : ∀ i, IsThetaPshPotential γ.val (b i))
    (hτ : IsThetaPshPotential γ.val τ)
    (ha : Tendsto (fun i => (⟨a i, haγ i⟩ : ThetaPshL1 γ.val)) F
      (@nhds (ThetaPshL1 γ.val)
        (singularityPseudoMetricSpace omega γ hγ).toUniformSpace.toTopologicalSpace ⟨τ, hτ⟩))
    (hb : Tendsto (fun i => (⟨b i, hbγ i⟩ : ThetaPshL1 γ.val)) F
      (@nhds (ThetaPshL1 γ.val)
        (singularityPseudoMetricSpace omega γ hγ).toUniformSpace.toTopologicalSpace ⟨τ, hτ⟩)) :
    Tendsto (fun i => (singularityDistance omega θ hθ (a i) (b i)).toReal) F (𝓝 0) := by
  let φ := thetaPshSupremum θ.val
  have hφ : IsThetaPshPotential θ.val φ :=
    (isModelPotential_thetaPshSupremum omega θ hθ).plurisubharmonic
  let z : I → M → EReal := fun i x => max (a i x) (b i x)
  have hzθ (i : I) : IsThetaPshPotential θ.val (z i) :=
    IsThetaPshPotential.max (haθ i) (hbθ i)
  have hzγ (i : I) : IsThetaPshPotential γ.val (z i) :=
    IsThetaPshPotential.max (haγ i) (hbγ i)
  have hzlim : Tendsto (fun i => (⟨z i, hzγ i⟩ : ThetaPshL1 γ.val)) F
      (@nhds (ThetaPshL1 γ.val)
        (singularityPseudoMetricSpace omega γ hγ).toUniformSpace.toTopologicalSpace ⟨τ, hτ⟩) :=
    tendsto_max_of_common_native_limit omega γ hγ F
      (fun i => ⟨a i, haγ i⟩) (fun i => ⟨b i, hbγ i⟩) ⟨τ, hτ⟩ ha hb
  let m (r : I → M → EReal) (hr : ∀ i, IsThetaPshPotential θ.val (r i))
      (i : I) (j : Fin (n + 1)) : ℝ := (endpointMixedMass θ φ (r i) hφ (hr i) j).toReal
  have hdefA (j : Fin (n + 1)) : Tendsto (fun i => m z hzθ i j - m a haθ i j) F (𝓝 0) :=
    tendsto_endpoint_difference_of_common_native_limit omega θ γ hθ hγ F
      hzθ haθ hzγ haγ hτ hzlim ha j
  have hdefB (j : Fin (n + 1)) : Tendsto (fun i => m z hzθ i j - m b hbθ i j) F (𝓝 0) :=
    tendsto_endpoint_difference_of_common_native_limit omega θ γ hθ hγ F
      hzθ hbθ hzγ hbγ hτ hzlim hb j
  have hsum : Tendsto (fun i => ∑ j : Fin (n + 1),
      ((m z hzθ i j - m a haθ i j) + (m z hzθ i j - m b hbθ i j))) F (𝓝 0) := by
    simpa only [add_zero, Finset.sum_const_zero] using
      (tendsto_finsetSum Finset.univ fun j _ => (hdefA j).add (hdefB j))
  have hJ : Tendsto (fun i => mixedMassJoinGap hφ (haθ i) (hbθ i)) F (𝓝 0) := by
    have heq (i : I) : mixedMassJoinGap hφ (haθ i) (hbθ i) =
        (∑ j : Fin (n + 1),
          ((m z hzθ i j - m a haθ i j) + (m z hzθ i j - m b hbθ i j))) / (n + 1 : ℝ) := by
      unfold mixedMassJoinGap
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      change 2 * m z hzθ i j - m a haθ i j - m b hbθ i j =
        (m z hzθ i j - m a haθ i j) + (m z hzθ i j - m b hbθ i j)
      ring
    simpa only [← heq, zero_div] using hsum.div_const (n + 1 : ℝ)
  have hbound (i : I) : 0 ≤ (singularityDistance omega θ hθ (a i) (b i)).toReal ∧
      (singularityDistance omega θ hθ (a i) (b i)).toReal ≤ mixedMassJoinGap hφ (haθ i) (hbθ i) := by
    obtain ⟨d, hd, _, _, he⟩ := exists_tendsto_singularityDistance omega θ hθ (haθ i) (hbθ i)
    have h := (singularityDistance_le_mixedMassJoinGap_le omega θ hθ (haθ i) (hbθ i)).1
    rw [he, EReal.coe_le_coe_iff] at h
    simpa only [he, EReal.toReal_coe] using And.intro hd h
  exact squeeze_zero (fun i => (hbound i).1) (fun i => (hbound i).2) hJ

/-- Actual finiteness embeds the real pair limit into the defining extended
radial distance, with no original-background common-limit certificate. -/
theorem tendsto_singularityDistance_zero_of_common_native_limit
    (omega : KahlerBackground n M) (θ γ : ClosedRealOneOneForm n M)
    (hθ : IsBigClass (RealBottChern.ofRepresentative θ))
    (hγ : IsBigClass (RealBottChern.ofRepresentative γ))
    {I : Type*} (F : Filter I) {a b : I → M → EReal} {τ : M → EReal}
    (haθ : ∀ i, IsThetaPshPotential θ.val (a i))
    (hbθ : ∀ i, IsThetaPshPotential θ.val (b i))
    (haγ : ∀ i, IsThetaPshPotential γ.val (a i))
    (hbγ : ∀ i, IsThetaPshPotential γ.val (b i))
    (hτ : IsThetaPshPotential γ.val τ)
    (ha : Tendsto (fun i => (⟨a i, haγ i⟩ : ThetaPshL1 γ.val)) F
      (@nhds (ThetaPshL1 γ.val)
        (singularityPseudoMetricSpace omega γ hγ).toUniformSpace.toTopologicalSpace ⟨τ, hτ⟩))
    (hb : Tendsto (fun i => (⟨b i, hbγ i⟩ : ThetaPshL1 γ.val)) F
      (@nhds (ThetaPshL1 γ.val)
        (singularityPseudoMetricSpace omega γ hγ).toUniformSpace.toTopologicalSpace ⟨τ, hτ⟩)) :
    Tendsto (fun i => singularityDistance omega θ hθ (a i) (b i)) F (𝓝 0) := by
  have hreal := tendsto_singularityDistance_toReal_zero_of_common_native_limit
    omega θ γ hθ hγ F haθ hbθ haγ hbγ hτ ha hb
  have heq (i : I) : ((singularityDistance omega θ hθ (a i) (b i)).toReal : EReal) =
      singularityDistance omega θ hθ (a i) (b i) := by
    obtain ⟨d, _, _, _, hd⟩ := exists_tendsto_singularityDistance omega θ hθ (haθ i) (hbθ i)
    rw [hd, EReal.toReal_coe]
  simpa only [Function.comp_def, EReal.coe_zero, heq] using EReal.tendsto_coe.mpr hreal

end
end SGPT.Foundations.Analysis.Pending.SingularNativePairedBackground
