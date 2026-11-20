import SGPT.Foundations.Analysis.Pending.ActualNativeMixedMassContinuity
import SGPT.Foundations.Analysis.Pending.MixedSummandCapacityDomination
import SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityMaximumCriterion

set_option autoImplicit false

/-! # Actual arbitrary-filter native addition continuity

SGPT PDF0241--0242 Theorem 6.2.2, forward implication. Actual genuine
sum potentials, the big sum class and all finite endpoint selector mass
limits are internally produced. The cancellation implications are separate.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.SingularNativeAdditionContinuity

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
  ThetaPshL1Topology SingularCanonicalSingularityDistance
  SingularCanonicalSingularityMassComparison SingularCanonicalSingularityMaximumCriterion
  SingularMinimalCanonicalRay RelativeEnergy MixedMass GlobalNonPluripolar
  GlobalMultilinearExpansion GlobalDiagonalScaling MixedMassProductCalculus MixedSummandCapacityDomination
  ActualNativeMixedMassContinuity GlobalMixedMassMonotone

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
private theorem genuine_add {θ σ : ClosedRealOneOneForm n M} {u v : M → EReal}
    (hu : IsThetaPshPotential θ.val u) (hv : IsThetaPshPotential σ.val v) :
    IsThetaPshPotential (θ + σ).val (fun x => u x + v x) := by
  classical
  let α : Bool → ClosedRealOneOneForm n M := fun b => if b then θ else σ
  let f : Bool → M → EReal := fun b => if b then u else v
  have hf (b : Bool) : IsThetaPshPotential (α b).val (f b) := by
    cases b
    · exact hv
    · exact hu
  have h := isThetaPshPotential_sumPot (T := Finset.univ)
    (w := fun _ : Bool => (1 : ℝ)) Finset.univ_nonempty (fun _ => zero_lt_one) hf
  have hQ : sumPot Finset.univ (fun _ : Bool => (1 : ℝ)) f = fun x => u x + v x := by
    funext x
    simp only [sumPot, Fintype.sum_bool, f, Bool.false_eq_true,
      ↓reduceIte, EReal.coe_one, one_mul]
  rw [hQ] at h
  simpa only [sumForm, Fintype.sum_bool, α, Bool.true_eq_false,
    Bool.false_eq_true, ↓reduceIte, one_smul] using h

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
private theorem big_add_genuine {θ σ : ClosedRealOneOneForm n M} {v : M → EReal}
    (hθ : IsBigClass (RealBottChern.ofRepresentative θ))
    (hv : IsThetaPshPotential σ.val v) :
    IsBigClass (RealBottChern.ofRepresentative (θ + σ)) := by
  obtain ⟨T⟩ := hθ
  refine ⟨{
    representative := T.representative + σ
    represents := by simp only [RealBottChern.ofRepresentative_add, T.represents]
    potential := fun x => T.potential x + v x
    lowerBound := T.lowerBound
    strictlyPsh := ?_ }⟩
  have h := genuine_add T.strictlyPsh hv
  have heq : (T.representative - T.lowerBound.form) + σ =
      (T.representative + σ) - T.lowerBound.form := by abel
  simpa only [heq] using h

private theorem tendsto_sumPot_mass_toReal
    {ι : Type*} [Fintype ι] [DecidableEq ι] (omega : KahlerBackground n M)
    (α : ι → ClosedRealOneOneForm n M)
    (hbig : ∀ o, IsBigClass (RealBottChern.ofRepresentative (α o)))
    {I : Type*} (F : Filter I) (c : Fin n → ι → ℝ) (hc : ∀ k o, 0 ≤ c k o)
    (f : I → ι → M → EReal) (g : ι → M → EReal)
    (hf : ∀ i o, IsThetaPshPotential (α o).val (f i o))
    (hg : ∀ o, IsThetaPshPotential (α o).val (g o))
    (hlim : ∀ o, Tendsto (fun i => (⟨f i o, hf i o⟩ : ThetaPshL1 (α o).val)) F
      (@nhds (ThetaPshL1 (α o).val)
        (singularityPseudoMetricSpace omega (α o) (hbig o)).toUniformSpace.toTopologicalSpace
        ⟨g o, hg o⟩)) :
    Tendsto (fun i => (globalMixedMass
      (fun k => sumForm Finset.univ (c k) α)
      (fun k => sumPot Finset.univ (c k) (f i))
      (fun k => thetaPlurisubharmonic_sumPot_of_nonneg (hc k) fun o => (hf i o).1)).toReal) F
      (𝓝 ((globalMixedMass (fun k => sumForm Finset.univ (c k) α)
        (fun k => sumPot Finset.univ (c k) g)
        (fun k => thetaPlurisubharmonic_sumPot_of_nonneg (hc k) fun o => (hg o).1)).toReal)) := by
  classical
  have hsel (s : Fin n → ι) : Tendsto (fun i => (globalMixedMass
      (fun k => α (s k)) (fun k => f i (s k)) (fun k => (hf i (s k)).1)).toReal) F
      (𝓝 ((globalMixedMass (fun k => α (s k)) (fun k => g (s k))
        (fun k => (hg (s k)).1)).toReal)) :=
    (ENNReal.tendsto_toReal (globalMixedMass_lt_top omega (fun k => (hg (s k)).1)).ne).comp
      (tendsto_globalMixedMass_of_native omega (fun k => hbig (s k)) F
        (fun i k => hf i (s k)) (fun k => hg (s k)) (fun k => hlim (s k)))
  have hs := tendsto_finsetSum Finset.univ fun s (_ : s ∈ Finset.univ) =>
    (hsel s).const_mul (∏ k, c k (s k))
  have hfun : (fun i => (globalMixedMass
      (fun k => sumForm Finset.univ (c k) α)
      (fun k => sumPot Finset.univ (c k) (f i))
      (fun k => thetaPlurisubharmonic_sumPot_of_nonneg (hc k) fun o => (hf i o).1)).toReal) =
      fun i => ∑ s : Fin n → ι, (∏ k, c k (s k)) *
        (globalMixedMass (fun k => α (s k)) (fun k => f i (s k))
          (fun k => (hf i (s k)).1)).toReal := by
    funext i
    exact globalMixedMass_sumPot_expand_toReal omega hc (hf i)
  rw [hfun, globalMixedMass_sumPot_expand_toReal omega hc hg]
  exact hs

private theorem tendsto_endpoint_add_mass_toReal
    (omega : KahlerBackground n M) (θ σ : ClosedRealOneOneForm n M)
    (hθ : IsBigClass (RealBottChern.ofRepresentative θ))
    (hσ : IsBigClass (RealBottChern.ofRepresentative σ)) {I : Type*} (F : Filter I)
    (a : I → ThetaPshL1 θ.val) (b : I → ThetaPshL1 σ.val)
    (p : ThetaPshL1 θ.val) (q : ThetaPshL1 σ.val)
    (ha : Tendsto a F (@nhds (ThetaPshL1 θ.val)
      (singularityPseudoMetricSpace omega θ hθ).toUniformSpace.toTopologicalSpace p))
    (hb : Tendsto b F (@nhds (ThetaPshL1 σ.val)
      (singularityPseudoMetricSpace omega σ hσ).toUniformSpace.toTopologicalSpace q))
    {R : M → EReal} (hR : IsThetaPshPotential (θ + σ).val R) (j : Fin (n + 1)) :
    Tendsto (fun i => (endpointMixedMass (θ + σ) R
      (fun x => (a i).val x + (b i).val x) hR
      (genuine_add (a i).property (b i).property) j).toReal) F
      (𝓝 ((endpointMixedMass (θ + σ) R (fun x => p.val x + q.val x)
        hR (genuine_add p.property q.property) j).toReal)) := by
  classical
  let α : Option Bool → ClosedRealOneOneForm n M :=
    fun o => o.elim (θ + σ) (fun z => if z then θ else σ)
  let Q (r : ThetaPshL1 θ.val) (s : ThetaPshL1 σ.val) : Option Bool → M → EReal :=
    fun o => o.elim R (fun z => if z then r.val else s.val)
  have H (r : ThetaPshL1 θ.val) (s : ThetaPshL1 σ.val) (o : Option Bool) :
      IsThetaPshPotential (α o).val (Q r s o) := by
    cases o with
    | none => exact hR
    | some z => cases z <;> first | exact s.property | exact r.property
  have hα (o : Option Bool) : IsBigClass (RealBottChern.ofRepresentative (α o)) := by
    cases o with
    | none => exact big_add_genuine hθ q.property
    | some z => cases z <;> first | exact hσ | exact hθ
  let c : Fin n → Option Bool → ℝ := fun k o =>
    if k.val < j.val then o.elim 0 (fun _ => 1) else o.elim 1 (fun _ => 0)
  have hc (k : Fin n) (o : Option Bool) : 0 ≤ c k o := by
    cases o <;> dsimp only [c] <;> split_ifs <;> norm_num
  have hlim (o : Option Bool) : Tendsto
      (fun i => (⟨Q (a i) (b i) o, H (a i) (b i) o⟩ : ThetaPshL1 (α o).val)) F
      (@nhds (ThetaPshL1 (α o).val)
        (singularityPseudoMetricSpace omega (α o) (hα o)).toUniformSpace.toTopologicalSpace
        ⟨Q p q o, H p q o⟩) := by
    cases o with
    | none =>
      change Tendsto (fun _ : I => (⟨R, hR⟩ : ThetaPshL1 (θ + σ).val)) F
        (@nhds (ThetaPshL1 (θ + σ).val)
          (singularityPseudoMetricSpace omega (θ + σ) (big_add_genuine hθ q.property)).toUniformSpace.toTopologicalSpace
          ⟨R, hR⟩)
      exact @tendsto_const_nhds (ThetaPshL1 (θ + σ).val)
        (singularityPseudoMetricSpace omega (θ + σ) (big_add_genuine hθ q.property)).toUniformSpace.toTopologicalSpace
        I ⟨R, hR⟩ F
    | some z => cases z <;> first | exact hb | exact ha
  have hF : (fun k => sumForm Finset.univ (c k) α) = fun _ : Fin n => θ + σ := by
    funext k
    by_cases hk : k.val < j.val <;>
      simp [sumForm, Fintype.sum_option, c, α, hk]
  have hQ (r : ThetaPshL1 θ.val) (s : ThetaPshL1 σ.val) :
      (fun k => sumPot Finset.univ (c k) (Q r s)) =
        endpointMixedPotential j (fun x => r.val x + s.val x) R := by
    funext k x
    by_cases hk : k.val < j.val <;>
      simp [sumPot, Fintype.sum_option, c, Q, hk, endpointMixedPotential]
  have heq (r : ThetaPshL1 θ.val) (s : ThetaPshL1 σ.val) :
      (globalMixedMass (fun k => sumForm Finset.univ (c k) α)
        (fun k => sumPot Finset.univ (c k) (Q r s))
        (fun k => thetaPlurisubharmonic_sumPot_of_nonneg (hc k) fun o => (H r s o).1)).toReal =
      (endpointMixedMass (θ + σ) R (fun x => r.val x + s.val x)
        hR (genuine_add r.property s.property) j).toReal := by
    exact congrArg (fun μ : Measure M => (μ univ).toReal)
      (globalMixedMeasure_congr hF (hQ r s) _
        (endpointMixedPotential_thetaPlurisubharmonic (θ + σ) j
          (fun x => r.val x + s.val x) R (genuine_add r.property s.property) hR))
  have h := tendsto_sumPot_mass_toReal omega α hα F c hc
    (fun i => Q (a i) (b i)) (Q p q) (fun i => H (a i) (b i)) (H p q) hlim
  have hfun : (fun i => (globalMixedMass (fun k => sumForm Finset.univ (c k) α)
      (fun k => sumPot Finset.univ (c k) (Q (a i) (b i)))
      (fun k => thetaPlurisubharmonic_sumPot_of_nonneg (hc k)
        fun o => (H (a i) (b i) o).1)).toReal) =
      fun i => (endpointMixedMass (θ + σ) R
        (fun x => (a i).val x + (b i).val x) hR
        (genuine_add (a i).property (b i).property) j).toReal := by
    funext i
    exact heq (a i) (b i)
  rw [hfun, heq p q] at h
  exact h

/-- Actual genuine addition and finite independent mixed-product expansion
produce the native sum limit, including zero original target masses. -/
theorem tendsto_native_add
    (omega : KahlerBackground n M) (θ σ : ClosedRealOneOneForm n M)
    (hθ : IsBigClass (RealBottChern.ofRepresentative θ))
    (hσ : IsBigClass (RealBottChern.ofRepresentative σ)) {I : Type*} (F : Filter I)
    (a : I → ThetaPshL1 θ.val) (b : I → ThetaPshL1 σ.val)
    (p : ThetaPshL1 θ.val) (q : ThetaPshL1 σ.val)
    (ha : Tendsto a F (@nhds (ThetaPshL1 θ.val)
      (singularityPseudoMetricSpace omega θ hθ).toUniformSpace.toTopologicalSpace p))
    (hb : Tendsto b F (@nhds (ThetaPshL1 σ.val)
      (singularityPseudoMetricSpace omega σ hσ).toUniformSpace.toTopologicalSpace q)) :
    let γ := θ + σ
    let hγ := big_add_genuine hθ q.property
    let S : I → ThetaPshL1 γ.val := fun i =>
      ⟨fun x => (a i).val x + (b i).val x, genuine_add (a i).property (b i).property⟩
    let T : ThetaPshL1 γ.val :=
      ⟨fun x => p.val x + q.val x, genuine_add p.property q.property⟩
    Tendsto S F (@nhds (ThetaPshL1 γ.val)
      (singularityPseudoMetricSpace omega γ hγ).toUniformSpace.toTopologicalSpace T) := by
  let γ := θ + σ
  have hγ : IsBigClass (RealBottChern.ofRepresentative γ) := big_add_genuine hθ q.property
  let S : I → ThetaPshL1 γ.val := fun i =>
    ⟨fun x => (a i).val x + (b i).val x, genuine_add (a i).property (b i).property⟩
  let T : ThetaPshL1 γ.val :=
    ⟨fun x => p.val x + q.val x, genuine_add p.property q.property⟩
  let R := thetaPshSupremum γ.val
  have hR : IsThetaPshPotential γ.val R :=
    (isModelPotential_thetaPshSupremum omega γ hγ).plurisubharmonic
  let A : I → ThetaPshL1 θ.val := fun i =>
    ⟨fun x => max ((a i).val x) (p.val x), IsThetaPshPotential.max (a i).property p.property⟩
  let B : I → ThetaPshL1 σ.val := fun i =>
    ⟨fun x => max ((b i).val x) (q.val x), IsThetaPshPotential.max (b i).property q.property⟩
  have hA : Tendsto A F (@nhds (ThetaPshL1 θ.val)
      (singularityPseudoMetricSpace omega θ hθ).toUniformSpace.toTopologicalSpace p) :=
    ((tendsto_native_iff_max_and_endpointMixedMass omega θ hθ F a p).mp ha).1
  have hB : Tendsto B F (@nhds (ThetaPshL1 σ.val)
      (singularityPseudoMetricSpace omega σ hσ).toUniformSpace.toTopologicalSpace q) :=
    ((tendsto_native_iff_max_and_endpointMixedMass omega σ hσ F b q).mp hb).1
  let X : I → ThetaPshL1 γ.val := fun i =>
    ⟨fun x => (A i).val x + (B i).val x, genuine_add (A i).property (B i).property⟩
  let W : I → ThetaPshL1 γ.val := fun i =>
    ⟨fun x => max ((S i).val x) (T.val x), IsThetaPshPotential.max (S i).property T.property⟩
  let mass (j : Fin (n + 1)) (w : ThetaPshL1 γ.val) : ℝ≥0∞ :=
    endpointMixedMass γ R w.val hR w.property j
  have hE (j : Fin (n + 1)) (w : ThetaPshL1 γ.val) (k : Fin n) :
      IsThetaPshPotential γ.val (endpointMixedPotential j w.val R k) := by
    dsimp only [endpointMixedPotential]
    split_ifs <;> first | exact w.property | exact hR
  have hfinite (j : Fin (n + 1)) (w : ThetaPshL1 γ.val) : mass j w ≠ ⊤ := by
    change globalMixedMass (fun _ : Fin n => γ) (endpointMixedPotential j w.val R)
      (endpointMixedPotential_thetaPlurisubharmonic γ j w.val R w.property hR) ≠ ⊤
    exact (globalMixedMass_lt_top omega
      (endpointMixedPotential_thetaPlurisubharmonic γ j w.val R w.property hR)).ne
  have hmono (j : Fin (n + 1)) (r s : ThetaPshL1 γ.val) (hrs : r.val ≤ s.val) :
      mass j r ≤ mass j s := by
    change globalMixedMass (fun _ : Fin n => γ) (endpointMixedPotential j r.val R)
      (endpointMixedPotential_thetaPlurisubharmonic γ j r.val R r.property hR) ≤
      globalMixedMass (fun _ : Fin n => γ) (endpointMixedPotential j s.val R)
        (endpointMixedPotential_thetaPlurisubharmonic γ j s.val R s.property hR)
    exact globalMixedMass_mono_of_isThetaPshPotential omega
      (θ := fun _ : Fin n => γ)
      (u := endpointMixedPotential j r.val R) (v := endpointMixedPotential j s.val R)
      (hE j r) (hE j s)
      (fun k => MoreSingularOn.of_le fun x _ => by
        dsimp only [endpointMixedPotential]
        split_ifs <;> first | exact hrs x | exact le_rfl)
  have hreal_S (j : Fin (n + 1)) : Tendsto (fun i => (mass j (S i)).toReal) F
      (𝓝 (mass j T).toReal) :=
    tendsto_endpoint_add_mass_toReal omega θ σ hθ hσ F a b p q ha hb hR j
  have hreal_X (j : Fin (n + 1)) : Tendsto (fun i => (mass j (X i)).toReal) F
      (𝓝 (mass j T).toReal) :=
    tendsto_endpoint_add_mass_toReal omega θ σ hθ hσ F A B p q hA hB hR j
  have hTW (i : I) : T.val ≤ (W i).val := fun x => le_max_right ((S i).val x) (T.val x)
  have hWX (i : I) : (W i).val ≤ (X i).val := fun x =>
    max_le
      (add_le_add (le_max_left ((a i).val x) (p.val x))
        (le_max_left ((b i).val x) (q.val x)))
      (add_le_add (le_max_right ((a i).val x) (p.val x))
        (le_max_right ((b i).val x) (q.val x)))
  have hreal_W (j : Fin (n + 1)) : Tendsto (fun i => (mass j (W i)).toReal) F
      (𝓝 (mass j T).toReal) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hreal_X j)
      (fun i => ENNReal.toReal_mono (hfinite j (W i)) (hmono j T (W i) (hTW i)))
      (fun i => ENNReal.toReal_mono (hfinite j (X i)) (hmono j (W i) (X i) (hWX i)))
  have embed (j : Fin (n + 1)) {r : I → ThetaPshL1 γ.val}
      (hr : Tendsto (fun i => (mass j (r i)).toReal) F (𝓝 (mass j T).toReal)) :
      Tendsto (fun i => mass j (r i)) F (𝓝 (mass j T)) := by
    have h := ENNReal.tendsto_ofReal hr
    simpa only [ENNReal.ofReal_toReal (hfinite j _)] using h
  let := singularityPseudoMetricSpace omega γ hγ
  let : TopologicalSpace (ThetaPshL1 γ.val) :=
    (singularityPseudoMetricSpace omega γ hγ).toUniformSpace.toTopologicalSpace
  change Tendsto S F (𝓝 T)
  apply (tendsto_native_iff_endpointMixedMass omega γ hγ F S T).mpr
  intro j
  exact ⟨embed j (r := S) (hreal_S j), embed j (r := W) (hreal_W j)⟩

end
end SGPT.Foundations.Analysis.Pending.SingularNativeAdditionContinuity
