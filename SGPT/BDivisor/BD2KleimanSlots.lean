import SGPT.BDivisor.BD2CurveNefCI
import SGPT.BDivisor.BDAmpleKahler
import SGPT.Bergman.SiuUniformGenerationWeights
import SGPT.Projective.NativePositiveRestriction

/-!
# Mixed integrals of a curve-nef form against pulled-back ample classes

Toward the Kleiman half of `rmk:bdiv:L749`.  Let `ψ : W → Y` be a holomorphic map from a compact
complex manifold `W` of dimension `d ≥ 1` carrying a positive line bundle `A`, to a compact
manifold `Y`, and `a` a curve-nef form on `W`.  Fix a form `δ` on `Y`.

* `slotIntegral_cons_positiveFamily_nonneg`: `∫_W a ∧ B₁ ∧ ⋯ ∧ B_{d-1} ≥ 0` when every `B_i` is
  (up to `ddᶜ`) a nonnegative combination of curvature forms of positive line bundles
  (multilinearity and `slotIntegral_cons_positive_nonneg`).
* `slotIntegral_pullback_nonneg`: the same when the slots other than the one holding `a` are
  pull-backs `ψ^*γ` of forms `γ` with `{γ + εδ}` an ample real class
  (`DFAlg.IsAmpleRealClass`) for every `ε > 0`.  Writing `{γ + εδ} = ∑ s_j c₁(L_j)`, the class
  `ψ^*{γ + εδ} + (∑ s_j / M) c₁(A)` is `∑ (s_j / M) c₁((ψ^*L_j)^M ⊗ A)` with positive bundles
  `(ψ^*L_j)^M ⊗ A`; let `M → ∞`, then `ε → 0`.
* `slotIntegral_pullback_le`: **monotonicity along a curve-nef direction**: if `{δ + εδ}` and
  `{δ + s₀ θ + εδ}` are ample for all `ε > 0` and `ψ^*θ` is curve-nef, then
  `∫_W (ψ^*δ)^d ≤ ∫_W (ψ^*(δ + s₀ θ))^d` (telescoping one slot at a time,
  `MultilinearMap.map_sub_map_piecewise`).  This is the polynomial step of Kleiman's argument.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter
open scoped Topology Manifold ContDiff BigOperators

namespace SGPT.BDivisor.Kleiman

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.NefMixedMass
open SGPT.Projective.NumEq SGPT.Projective.NumEq.CompleteIntersections
open SGPT.Hodge.BDivChain.SourceMixedOrderDraft
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth SGPT.PSH.GlobalL2
open SGPT.Bergman.NativeHermitianMetric SGPT.Toric.F1IntersectionDraft
open HermitianHolomorphicLineBundle

section Algebra

variable {k n : ℕ} {V M : Type*} [TopologicalSpace V] [ChartedSpace (ComplexModel k) V]
  [IsComplexManifold k V] [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- The pull-back of closed real `(1,1)`-forms along a holomorphic map, as a linear map. -/
def pullbackLinear {f : V → M} (hf : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ f) :
    ClosedRealOneOneForm n M →ₗ[ℝ] ClosedRealOneOneForm k V where
  toFun := ClosedRealOneOneForm.pullback hf
  map_add' a c := by
    apply ClosedRealOneOneForm.ext
    intro e z
    ext v
    rfl
  map_smul' t c := by
    apply ClosedRealOneOneForm.ext
    intro e z
    ext v
    rfl

@[simp] theorem pullbackLinear_apply {f : V → M}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ f)
    (a : ClosedRealOneOneForm n M) : pullbackLinear hf a = ClosedRealOneOneForm.pullback hf a :=
  rfl

/-- A nonnegative multiple of a semipositive form is semipositive. -/
theorem isSemipositive_smul {θ : ClosedRealOneOneForm k V} (hθ : θ.val.IsSemipositive)
    {c : ℝ} (hc : 0 ≤ c) : (c • θ).val.IsSemipositive := by
  intro e z hz v
  have h := hθ e z hz v
  simp only [ClosedRealOneOneForm.coeff_smul, ContinuousAlternatingMap.smul_apply,
    smul_eq_mul]
  exact mul_nonneg hc h

end Algebra

section Limits

variable {N : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel N) M]
  [IsComplexManifold N M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- If `∫ (A + t B) ≥ 0` along `t = 1/(j+1)`, then `∫ A ≥ 0`. -/
theorem slotIntegral_nonneg_of_seq (w : KahlerBackground N M)
    (A B : Fin N → ClosedRealOneOneForm N M)
    (h : ∀ j : ℕ, 0 ≤ slotIntegral w (fun i => A i + (1 / ((j : ℝ) + 1)) • B i)) :
    0 ≤ slotIntegral w A := by
  have hcont := (continuous_slotIntegral_add_smul w A B).tendsto 0
  have hseq : Tendsto (fun j : ℕ => 1 / ((j : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have h0 : slotIntegral w (fun i => A i + (0 : ℝ) • B i) = slotIntegral w A := by
    simp only [zero_smul, add_zero]
  rw [← h0]
  exact ge_of_tendsto (hcont.comp hseq) (Eventually.of_forall h)

/-- If `∫ (A + t B) ≥ 0` for every `t > 0`, then `∫ A ≥ 0`. -/
theorem slotIntegral_nonneg_of_pos (w : KahlerBackground N M)
    (A B : Fin N → ClosedRealOneOneForm N M)
    (h : ∀ t : ℝ, 0 < t → 0 ≤ slotIntegral w (fun i => A i + t • B i)) :
    0 ≤ slotIntegral w A :=
  slotIntegral_nonneg_of_seq w A B fun j => h _ (by positivity)

end Limits

section Combination

variable {k : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel (k + 1)) X]
  [IsComplexManifold (k + 1) X] [CompactSpace X]

/-- **A curve-nef form against nonnegative combinations of positive bundles.**  If each slot
`θᵢ` is, up to `ddᶜ`, a nonnegative combination `∑_j c_{ij} c₁(P_{ij})` of curvature forms of
positive Hermitian line bundles, then `∫_X a ∧ θ₁ ∧ ⋯ ∧ θ_k ≥ 0` for every curve-nef `a`. -/
theorem slotIntegral_cons_positiveFamily_nonneg {J : Fin k → Type} [∀ i, Fintype (J i)]
    (P : ∀ i, J i → NativePositiveLine (k + 1) X) (c : ∀ i, J i → ℝ)
    (hc : ∀ i j, 0 ≤ c i j) (κ : KahlerBackground (k + 1) X) (a : ClosedRealOneOneForm (k + 1) X)
    (ha : ∀ (C : Type) [TopologicalSpace C] [ChartedSpace (ComplexModel 1) C]
      [IsComplexManifold 1 C] [CompactSpace C] [ConnectedSpace C] (κC : KahlerBackground 1 C)
      (g : C → X) (hg : ContMDiff 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ComplexModel (k + 1)) ∞ g),
      0 ≤ degreeAlong κC hg a)
    (θ : Fin k → ClosedRealOneOneForm (k + 1) X)
    (hθ : ∀ i, ClosedRealOneOneForm.BottChernRel (θ i) (∑ j, c i j • (P i j).curvature)) :
    let : MeasurableSpace X := borel X
    0 ≤ slotIntegral κ (Fin.cons a θ) := by
  classical
  let : MeasurableSpace X := borel X
  have : BorelSpace X := ⟨rfl⟩
  dsimp only
  have hrel : ∀ i : Fin (k + 1), ClosedRealOneOneForm.BottChernRel
      ((Fin.cons a θ : Fin (k + 1) → ClosedRealOneOneForm (k + 1) X) i)
      ((Fin.cons a (fun i => ∑ j, c i j • (P i j).curvature) :
        Fin (k + 1) → ClosedRealOneOneForm (k + 1) X) i) := by
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · simpa only [Fin.cons_zero] using ClosedRealOneOneForm.BottChernRel.refl a
    · simpa only [Fin.cons_succ] using hθ i
  rw [slotIntegral_eq_of_bottChernRel κ _ _ hrel]
  let F := (slotIntegralMultilinear κ).curryLeft a
  have hF : ∀ v : Fin k → ClosedRealOneOneForm (k + 1) X,
      F v = slotIntegral κ (Fin.cons a v) := fun v => by
    simp only [F, MultilinearMap.curryLeft_apply]
    rfl
  rw [← hF, MultilinearMap.map_sum]
  refine Finset.sum_nonneg fun r _ => ?_
  rw [MultilinearMap.map_smul_univ, smul_eq_mul, hF]
  exact mul_nonneg (Finset.prod_nonneg fun i _ => hc i (r i))
    (slotIntegral_cons_positive_nonneg (fun i => P i (r i)) κ a ha)

end Combination

section Pullback

variable {N : ℕ} {Y : Type} [TopologicalSpace Y] [ChartedSpace (ComplexModel N) Y]
  [IsComplexManifold N Y]

section Fixed

variable {k : ℕ} {W : Type} [TopologicalSpace W] [ChartedSpace (ComplexModel (k + 1)) W]
  [IsComplexManifold (k + 1) W] [CompactSpace W]

omit [CompactSpace W] in
/-- The pull-back `ψ^*L` of a smooth Hermitian line bundle has own Chern form `ψ^*θ_L`. -/
theorem isOwnFirstChernForm_pullback {ψ : W → Y}
    (hψ : ContMDiff 𝓘(ℂ, ComplexModel (k + 1)) 𝓘(ℂ, ComplexModel N) ∞ ψ)
    (L : HermitianHolomorphicLineBundle.{0, 0} N Y) (hL : IsSourceSmoothHermitianMetric L)
    (θ : ClosedRealOneOneForm N Y) (hθ : IsOwnFirstChernForm L θ) :
    IsOwnFirstChernForm (nativeHolomorphicPullbackBundle L ⟨ψ, hψ⟩)
      (ClosedRealOneOneForm.pullback hψ θ) := by
  have hgeo := nativeHolomorphicPullback_firstChern_geometrically L ⟨ψ, hψ⟩ hL θ hθ
  intro c e z hz he
  exact (hgeo c hz).symm.trans (sourceNativeFirstChernForm_isOwn _
    (nativeHolomorphicPullback_smooth L ⟨ψ, hψ⟩ hL) c e z hz he)

/-- The positive bundle `(ψ^*L)^M ⊗ A` on `W`, with curvature `M ψ^*θ_L + θ_A`. -/
def twistedPullbackPositive {ψ : W → Y}
    (hψ : ContMDiff 𝓘(ℂ, ComplexModel (k + 1)) 𝓘(ℂ, ComplexModel N) ∞ ψ)
    (L : HermitianHolomorphicLineBundle.{0, 0} N Y) (hL : IsSourceSmoothHermitianMetric L)
    (θ : ClosedRealOneOneForm N Y) (hθ : IsOwnFirstChernForm L θ) (hθK : θ.val.IsKahler)
    (A : NativePositiveLine (k + 1) W) (M : ℕ) : NativePositiveLine (k + 1) W where
  bundle := twistedPower (nativeHolomorphicPullbackBundle L ⟨ψ, hψ⟩) (positivePower A.bundle (1 - 1)) M
  smooth := sourceNativeTwistedPower_smooth _ (positivePower A.bundle (1 - 1))
    (nativeHolomorphicPullback_smooth L ⟨ψ, hψ⟩ hL)
    (sourceNativePositivePower_smooth A.bundle A.smooth (1 - 1)) M
  curvature := (M : ℝ) • ClosedRealOneOneForm.pullback hψ θ + ((1 : ℕ) : ℝ) • A.curvature
  own := SGPT.Bergman.SiuUniformGeneration.twistedPower_isOwnFirstChernForm _ A.bundle
    (nativeHolomorphicPullback_smooth L ⟨ψ, hψ⟩ hL) A.smooth
    (isOwnFirstChernForm_pullback hψ L hL θ hθ) A.own le_rfl M
  positive := NefCoreKahlerCurrent.isKahler_add_smul_of_isSemipositive A.background
    (isSemipositive_smul (ClosedRealOneOneForm.pullback_isSemipositive hψ
      (KahlerBackground.isSemipositive ⟨θ, hθK⟩)) (Nat.cast_nonneg M)) (by norm_num)

omit [CompactSpace W] in
@[simp] theorem twistedPullbackPositive_curvature {ψ : W → Y}
    (hψ : ContMDiff 𝓘(ℂ, ComplexModel (k + 1)) 𝓘(ℂ, ComplexModel N) ∞ ψ)
    (L : HermitianHolomorphicLineBundle.{0, 0} N Y) (hL : IsSourceSmoothHermitianMetric L)
    (θ : ClosedRealOneOneForm N Y) (hθ : IsOwnFirstChernForm L θ) (hθK : θ.val.IsKahler)
    (A : NativePositiveLine (k + 1) W) (M : ℕ) :
    (twistedPullbackPositive hψ L hL θ hθ hθK A M).curvature =
      (M : ℝ) • ClosedRealOneOneForm.pullback hψ θ + ((1 : ℕ) : ℝ) • A.curvature := rfl

/-- **Pulled-back ample-approximable slots.**  If `a` is curve-nef on `W` and every `γᵢ` has
`{γᵢ + εδ}` ample for all `ε > 0`, then `∫_W a ∧ ψ^*γ₁ ∧ ⋯ ∧ ψ^*γ_k ≥ 0`. -/
theorem slotIntegral_cons_pullback_nonneg {ψ : W → Y}
    (hψ : ContMDiff 𝓘(ℂ, ComplexModel (k + 1)) 𝓘(ℂ, ComplexModel N) ∞ ψ)
    (A : NativePositiveLine (k + 1) W) (κ : KahlerBackground (k + 1) W)
    (a : ClosedRealOneOneForm (k + 1) W)
    (ha : ∀ (C : Type) [TopologicalSpace C] [ChartedSpace (ComplexModel 1) C]
      [IsComplexManifold 1 C] [CompactSpace C] [ConnectedSpace C] (κC : KahlerBackground 1 C)
      (g : C → W) (hg : ContMDiff 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ComplexModel (k + 1)) ∞ g),
      0 ≤ degreeAlong κC hg a)
    (δ : ClosedRealOneOneForm N Y) (γ : Fin k → ClosedRealOneOneForm N Y)
    (hγ : ∀ i, ∀ ε : ℝ, 0 < ε →
      DFAlg.IsAmpleRealClass (RealBottChern.ofRepresentative (γ i + ε • δ))) :
    let : MeasurableSpace W := borel W
    0 ≤ slotIntegral κ (Fin.cons a (fun i => ClosedRealOneOneForm.pullback hψ (γ i))) := by
  classical
  let : MeasurableSpace W := borel W
  have : BorelSpace W := ⟨rfl⟩
  dsimp only
  -- the base and direction tuples
  have hcons : ∀ (v d : Fin k → ClosedRealOneOneForm (k + 1) W) (t : ℝ),
      (fun i => (Fin.cons a v : Fin (k + 1) → ClosedRealOneOneForm (k + 1) W) i +
        t • (Fin.cons 0 d : Fin (k + 1) → ClosedRealOneOneForm (k + 1) W) i) =
        Fin.cons a (fun i => v i + t • d i) := by
    intro v d t
    funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp only [Fin.cons_zero, smul_zero, add_zero]
    · simp only [Fin.cons_succ]
  -- Step 1: `ε > 0` fixed
  have hε : ∀ ε : ℝ, 0 < ε → 0 ≤ slotIntegral κ
      (Fin.cons a (fun i => ClosedRealOneOneForm.pullback hψ (γ i + ε • δ))) := by
    intro ε hεpos
    choose K L θ s hLθ hrep using fun i => hγ i ε hεpos
    let S : Fin k → ℝ := fun i => ∑ j, s i j
    apply slotIntegral_nonneg_of_seq κ _ (Fin.cons 0 (fun i => S i • A.curvature))
    intro m
    rw [hcons]
    let Mm : ℕ := m + 1
    have hM : (0 : ℝ) < (Mm : ℝ) := by positivity
    have hMinv : (1 / ((m : ℝ) + 1)) = 1 / (Mm : ℝ) := by simp [Mm]
    refine slotIntegral_cons_positiveFamily_nonneg (J := fun i => Fin (K i + 1))
      (fun i j => twistedPullbackPositive hψ (L i j) (hLθ i j).1 (θ i j) (hLθ i j).2.1
        (hLθ i j).2.2.1 A Mm)
      (fun i j => s i j / Mm) (fun i j => div_nonneg (hLθ i j).2.2.2.le hM.le) κ a ha _ ?_
    intro i
    -- `γᵢ + εδ ∼ ∑ s_j θ_j` on `Y`
    have hY : ClosedRealOneOneForm.BottChernRel (γ i + ε • δ) (∑ j, s i j • θ i j) := by
      apply (RealBottChern.ofRepresentative_eq_iff _ _).mp
      rw [hrep i]
      change _ = RealBottChern.ofRepresentativeLinearMap (∑ j, s i j • θ i j)
      simp only [map_sum, map_smul]
      rfl
    have hW := (bottChernRel_pullback hψ hY).add
      (ClosedRealOneOneForm.BottChernRel.refl ((1 / ((m : ℝ) + 1)) • (S i • A.curvature)))
    refine hW.trans ?_
    have hp : ClosedRealOneOneForm.pullback hψ (∑ j, s i j • θ i j) =
        ∑ j, s i j • ClosedRealOneOneForm.pullback hψ (θ i j) := by
      rw [← pullbackLinear_apply hψ, map_sum]
      simp only [map_smul, pullbackLinear_apply]
    have hform : ClosedRealOneOneForm.pullback hψ (∑ j, s i j • θ i j) +
        (1 / ((m : ℝ) + 1)) • (S i • A.curvature) =
        ∑ j, (s i j / Mm) • (twistedPullbackPositive hψ (L i j) (hLθ i j).1 (θ i j)
          (hLθ i j).2.1 (hLθ i j).2.2.1 A Mm).curvature := by
      simp only [twistedPullbackPositive_curvature, smul_add, smul_smul, Nat.cast_one, mul_one,
        Finset.sum_add_distrib]
      rw [hp, hMinv]
      congr 1
      · refine Finset.sum_congr rfl fun j _ => ?_
        rw [div_mul_cancel₀ _ hM.ne']
      · rw [← Finset.sum_smul]
        congr 1
        simp only [S]
        rw [one_div_mul_eq_div, Finset.sum_div]
    rw [hform]
    exact ClosedRealOneOneForm.BottChernRel.refl _
  -- Step 2: `ε → 0`
  apply slotIntegral_nonneg_of_pos κ _ (Fin.cons 0 (fun _ => ClosedRealOneOneForm.pullback hψ δ))
  intro t ht
  rw [hcons]
  have := hε t ht
  simpa only [NefCoreKahlerCurrent.pullback_add_smul] using this

end Fixed

/-- **The slot holding the curve-nef form may be anywhere** (slot integrals are symmetric). -/
theorem slotIntegral_pullback_nonneg {d : ℕ} {W : Type} [TopologicalSpace W]
    [ChartedSpace (ComplexModel d) W] [IsComplexManifold d W] [CompactSpace W]
    {ψ : W → Y} (hψ : ContMDiff 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel N) ∞ ψ)
    (A : NativePositiveLine d W) (κ : KahlerBackground d W) (a : ClosedRealOneOneForm d W)
    (ha : ∀ (C : Type) [TopologicalSpace C] [ChartedSpace (ComplexModel 1) C]
      [IsComplexManifold 1 C] [CompactSpace C] [ConnectedSpace C] (κC : KahlerBackground 1 C)
      (g : C → W) (hg : ContMDiff 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ComplexModel d) ∞ g),
      0 ≤ degreeAlong κC hg a)
    (δ : ClosedRealOneOneForm N Y) (T : Fin d → ClosedRealOneOneForm d W) (i₀ : Fin d)
    (hT₀ : T i₀ = a)
    (hT : ∀ j, j ≠ i₀ → ∃ γ : ClosedRealOneOneForm N Y, T j = ClosedRealOneOneForm.pullback hψ γ ∧
      ∀ ε : ℝ, 0 < ε → DFAlg.IsAmpleRealClass (RealBottChern.ofRepresentative (γ + ε • δ))) :
    let : MeasurableSpace W := borel W
    0 ≤ slotIntegral κ T := by
  classical
  let : MeasurableSpace W := borel W
  have : BorelSpace W := ⟨rfl⟩
  dsimp only
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 1 := Nat.exists_eq_succ_of_ne_zero (Fin.pos i₀).ne'
  let σ : Equiv.Perm (Fin (k + 1)) := Equiv.swap 0 i₀
  rw [← slotIntegral_perm κ T σ]
  have hne : ∀ i : Fin k, σ i.succ ≠ i₀ := by
    intro i h
    have : i.succ = σ i₀ := by rw [← h, Equiv.swap_apply_self]
    rw [Equiv.swap_apply_right] at this
    exact Fin.succ_ne_zero i this
  choose γ hγ hγamp using fun i : Fin k => hT (σ i.succ) (hne i)
  have heq : (fun i => T (σ i)) = Fin.cons a (fun i => ClosedRealOneOneForm.pullback hψ (γ i)) := by
    funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp only [Fin.cons_zero, σ, Equiv.swap_apply_left, hT₀]
    · simp only [Fin.cons_succ, hγ i]
  rw [heq]
  exact slotIntegral_cons_pullback_nonneg hψ A κ a ha δ γ hγamp

/-- **Monotonicity along a curve-nef direction** (the polynomial step of Kleiman's argument).
If `ψ^*θ` is curve-nef on `W`, and `{δ + εδ}`, `{δ + s₀θ + εδ}` are ample for all `ε > 0`, then
`∫_W (ψ^*δ)^d ≤ ∫_W (ψ^*(δ + s₀θ))^d`. -/
theorem slotIntegral_pullback_le {d : ℕ} {W : Type} [TopologicalSpace W]
    [ChartedSpace (ComplexModel d) W] [IsComplexManifold d W] [CompactSpace W]
    {ψ : W → Y} (hψ : ContMDiff 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel N) ∞ ψ)
    (A : NativePositiveLine d W) (κ : KahlerBackground d W)
    (θ δ : ClosedRealOneOneForm N Y) {s₀ : ℝ} (hs₀ : 0 ≤ s₀)
    (ha : ∀ (C : Type) [TopologicalSpace C] [ChartedSpace (ComplexModel 1) C]
      [IsComplexManifold 1 C] [CompactSpace C] [ConnectedSpace C] (κC : KahlerBackground 1 C)
      (g : C → W) (hg : ContMDiff 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ComplexModel d) ∞ g),
      0 ≤ degreeAlong κC hg (ClosedRealOneOneForm.pullback hψ θ))
    (h₀ : ∀ ε : ℝ, 0 < ε → DFAlg.IsAmpleRealClass (RealBottChern.ofRepresentative (δ + ε • δ)))
    (h₁ : ∀ ε : ℝ, 0 < ε →
      DFAlg.IsAmpleRealClass (RealBottChern.ofRepresentative ((δ + s₀ • θ) + ε • δ))) :
    let : MeasurableSpace W := borel W
    slotIntegral κ (fun _ => ClosedRealOneOneForm.pullback hψ δ) ≤
      slotIntegral κ (fun _ => ClosedRealOneOneForm.pullback hψ (δ + s₀ • θ)) := by
  classical
  let : MeasurableSpace W := borel W
  have : BorelSpace W := ⟨rfl⟩
  dsimp only
  set x := ClosedRealOneOneForm.pullback hψ δ with hx
  set x' := ClosedRealOneOneForm.pullback hψ (δ + s₀ • θ) with hx'
  set a := ClosedRealOneOneForm.pullback hψ θ with ha'
  have hdiff : x' - x = s₀ • a := by
    rw [hx', hx, ha', NefCoreKahlerCurrent.pullback_add_smul]
    abel
  let F := slotIntegralMultilinear (n := d) (X := W) κ
  have hF : ∀ v, F v = slotIntegral κ v := fun v => rfl
  have htel := F.map_sub_map_piecewise (fun _ => x') (fun _ => x) Finset.univ
  rw [Finset.piecewise_univ] at htel
  rw [← sub_nonneg, ← hF, ← hF, htel]
  refine Finset.sum_nonneg fun i _ => ?_
  simp only [Finset.mem_univ, true_implies]
  -- the `i`-th term is `s₀ ∫ (x', …, x', a, x, …, x)`
  have hupd : (fun j => if j < i then x' else if i = j then x' - x else x) =
      Function.update (fun j => if j < i then x' else x) i (s₀ • a) := by
    funext j
    by_cases hji : j = i
    · subst hji
      simp only [lt_irrefl, if_false, if_true, Function.update_self, hdiff]
    · rw [Function.update_of_ne hji]
      by_cases hlt : j < i
      · simp only [hlt, if_true]
      · simp only [hlt, if_false, Ne.symm hji]
  rw [hupd, F.map_update_smul, smul_eq_mul, hF]
  refine mul_nonneg hs₀ ?_
  refine slotIntegral_pullback_nonneg hψ A κ a ha δ _ i (Function.update_self _ _ _) ?_
  intro j hj
  rw [Function.update_of_ne hj]
  by_cases hlt : j < i
  · simp only [hlt, if_true]
    exact ⟨δ + s₀ • θ, rfl, h₁⟩
  · simp only [hlt, if_false]
    exact ⟨δ, rfl, h₀⟩

end Pullback

end SGPT.BDivisor.Kleiman
