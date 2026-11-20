import SGPT.PSH.HermitianProductsCorrectionShift
import SGPT.PSH.HermitianProductsDomination

/-!
# Splitting a smooth summand from a nonclosed background

Finite multilinearity of the actual smooth exterior product gives the
subset splitting, and decreasing Bedford--Taylor continuity extends it to
the literal bounded product currents. The residual forms may be nonclosed.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianProducts

open Set Filter MeasureTheory TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open FirstPass.MongeAmpere StronglyPositiveForms LocalProductCurrents
  LocalBedfordTaylorProducts LocalBedfordTaylorSmooth LocalBedfordTaylorForms
  LocalBedfordTaylorCalculus LocalBedfordTaylorContinuity LocalBedfordTaylorLocality
  LocalBedfordTaylorSmoothProductDensity LocalBedfordTaylorCollar
  LocalBedfordTaylorDecreasing TopDegreeDensity ConstantFormProducts
open scoped Topology Distributions ContDiff

variable {n : ℕ} {U V : Opens (ComplexModel n)}

/-- The selected Hermitian subproduct wedged with the complementary smooth
background power; every factor is an actual current or smooth form. -/
def residualSplitTerm (p r : ℕ) (v : Fin p → ComplexModel n → ℝ)
    {σ τ : ComplexModel n → RealForm n 2}
    (hσ : ContDiffOn ℝ ∞ σ U) (hτ : ContDiffOn ℝ ∞ τ U)
    (T : LocalProductCurrent n U (r + p)) (s : Finset (Fin p)) :
    LocalProductCurrent n U r :=
  have hc : s.card ≤ p := by simpa using Finset.card_le_univ s
  wedgeForm rfl
    (backgroundExpansion s.card (r + (p - s.card))
      (fun i => v (s.orderEmbOfFin rfl i)) hσ
      (castLPC (by omega : r + p = r + (p - s.card) + s.card) T))
    (contDiffOn_wedgeProd (p - s.card) (fun _ => τ) (fun _ => hτ))

private theorem wedgeForm_wedge_cast_total {r k l p : ℕ} (hklp : k + l = p)
    (hdeg : r + p = r + l + k) (T : LocalProductCurrent n U (r + p))
    {α : ComplexModel n → RealForm n (2 * k)}
    {β : ComplexModel n → RealForm n (2 * l)}
    (hα : ContDiffOn ℝ ∞ α U) (hβ : ContDiffOn ℝ ∞ β U)
    (hαS : ∀ z ∈ U, α z ∈ formSpan n k)
    (hβS : ∀ z ∈ U, β z ∈ formSpan n l) :
    wedgeForm rfl (wedgeForm rfl (castLPC hdeg T) hα) hβ =
      wedgeForm rfl T (HermitianSmoothWedgeAssociation.contDiffOn_wedgeTo
        (by omega : 2 * k + 2 * l = 2 * p) hα hβ) := by
  subst p
  rw [HermitianSmoothWedgeAssociation.wedgeForm_wedge rfl _ hα hβ hαS hβS]
  have hcast : ∀ {a b r k : ℕ} (hab : a = b) (h : r + k = a)
      (T : LocalProductCurrent n U a) {η : ComplexModel n → RealForm n (2 * k)}
      (hη : ContDiffOn ℝ ∞ η U),
      wedgeForm (h.trans hab) (castLPC hab T) hη = wedgeForm h T hη := by
    intro a b r k hab
    subst hab
    intro h T η hη
    rfl
  exact hcast hdeg rfl T _

theorem residualSplitTerm_smooth (p r : ℕ)
    (v : Fin p → ComplexModel n → ℝ)
    (hv : ∀ i, ContDiffOn ℝ ∞ (v i) U)
    (hvp : ∀ i, PlurisubharmonicOn (fun z => (v i z : EReal)) U)
    {σ τ : ComplexModel n → RealForm n 2}
    (hσ : ContDiffOn ℝ ∞ σ U) (hτ : ContDiffOn ℝ ∞ τ U)
    (hσS : ∀ z ∈ U, σ z ∈ formSpan n 1)
    (hτS : ∀ z ∈ U, τ z ∈ formSpan n 1)
    (T : LocalProductCurrent n U (r + p)) (hT : IsPositive T)
    (hTc : IsClosedAny (r + p) T) (s : Finset (Fin p)) :
    residualSplitTerm p r v hσ hτ T s =
      wedgeForm rfl T (smoothFormProduct p (s.piecewise
        (fun i => (⟨fun z => ddcForm (v i) z + σ z,
          (contDiffOn_ddcForm (hv i)).add hσ⟩ : smoothFormSpace n U 1))
        (fun _ => ⟨τ, hτ⟩))).property := by
  classical
  have hc : s.card ≤ p := by simpa using Finset.card_le_univ s
  dsimp only [residualSplitTerm]
  rw [backgroundExpansion_smooth s.card (r + (p - s.card)) _
    (fun i => hv _) (fun i => hvp _) hσ hσS _
    (isPositive_castLPC _ hT) (isClosedAny_castLPC _ hTc),
    wedgeForm_wedge_cast_total (by omega : s.card + (p - s.card) = p) _ T _ _
      (fun z hz => wedgeProd_mem_formSpan _ _ (fun i =>
        (formSpan n 1).add_mem (smooth_ddcForm_mem_formSpan (hv _) z hz) (hσS z hz)))
      (fun z hz => wedgeProd_mem_formSpan _ _ (fun _ => hτS z hz))]
  apply wedgeForm_congr
  intro z _
  change wedgeTo (by omega : 2 * s.card + 2 * (p - s.card) = 2 * p)
    (wedgeProd s.card (fun i => ddcForm (v (s.orderEmbOfFin rfl i)) z + σ z))
    (wedgeProd (p - s.card) (fun _ => τ z)) =
    wedgeProd p (fun i => (s.piecewise
      (fun i => (⟨fun z => ddcForm (v i) z + σ z,
        (contDiffOn_ddcForm (hv i)).add hσ⟩ : smoothFormSpace n U 1))
      (fun _ => ⟨τ, hτ⟩) i) z)
  have heq : (fun i => (s.piecewise
      (fun i => (⟨fun z => ddcForm (v i) z + σ z,
        (contDiffOn_ddcForm (hv i)).add hσ⟩ : smoothFormSpace n U 1))
      (fun _ => ⟨τ, hτ⟩) i) z) =
      s.piecewise (fun i => ddcForm (v i) z + σ z) (fun _ => τ z) := by
    funext i
    by_cases hi : i ∈ s <;> simp [Finset.piecewise, hi]
  rw [heq, wedgeProd_selected_const]

/-- Exact common-background splitting for actual smooth potentials. -/
theorem backgroundExpansion_split_smooth (p r : ℕ)
    (v : Fin p → ComplexModel n → ℝ)
    (hv : ∀ i, ContDiffOn ℝ ∞ (v i) U)
    (hvp : ∀ i, PlurisubharmonicOn (fun z => (v i z : EReal)) U)
    {σ τ : ComplexModel n → RealForm n 2}
    (hσ : ContDiffOn ℝ ∞ σ U) (hτ : ContDiffOn ℝ ∞ τ U)
    (hσS : ∀ z ∈ U, σ z ∈ formSpan n 1)
    (hτS : ∀ z ∈ U, τ z ∈ formSpan n 1)
    (T : LocalProductCurrent n U (r + p)) (hT : IsPositive T)
    (hTc : IsClosedAny (r + p) T) :
    backgroundExpansion p r v (hσ.add hτ) T =
      ∑ s : Finset (Fin p), residualSplitTerm p r v hσ hτ T s := by
  classical
  rw [backgroundExpansion_smooth p r v hv hvp _
    (fun z hz => (formSpan n 1).add_mem (hσS z hz) (hτS z hz)) T hT hTc]
  ext γ φ
  let α : Fin p → smoothFormSpace n U 1 := fun i =>
    ⟨fun z => ddcForm (v i) z + σ z, (contDiffOn_ddcForm (hv i)).add hσ⟩
  let β : Fin p → smoothFormSpace n U 1 := fun _ => ⟨τ, hτ⟩
  have hsum := smoothWedgeTest_product_add p r T γ φ α β
  have heq : wedgeForm rfl T (contDiffOn_wedgeProd p
      (fun i z => ddcForm (v i) z + (σ z + τ z))
      (fun i => (contDiffOn_ddcForm (hv i)).add (hσ.add hτ))) =
      wedgeForm rfl T (smoothFormProduct p (α + β)).property := by
    apply wedgeForm_congr
    intro z _
    change wedgeProd p (fun i => ddcForm (v i) z + (σ z + τ z)) =
      wedgeProd p (fun i => (ddcForm (v i) z + σ z) + τ z)
    simp only [add_assoc]
  rw [congrArg (fun R : LocalProductCurrent n U r => R γ φ) heq]
  change smoothWedgeTest rfl T γ φ (smoothFormProduct p (α + β)) = _
  rw [hsum]
  simp only [LinearMap.sum_apply, _root_.sum_apply]
  apply Finset.sum_congr rfl
  intro s _
  exact (congrArg (fun R : LocalProductCurrent n U r => R γ φ)
    (residualSplitTerm_smooth p r v hv hvp hσ hτ hσS hτS T hT hTc s)).symm

theorem residualSplitTerm_decreasing (p r : ℕ)
    (T : LocalProductCurrent n U (r + p)) (hT : IsPositive T)
    (hTc : IsClosedAny (r + p) T)
    (v : ℕ → Fin p → ComplexModel n → ℝ) (v₀ : Fin p → ComplexModel n → ℝ)
    (hv : ∀ j i, IsLocallyBoundedPshOn U (v j i))
    (hv₀ : ∀ i, IsLocallyBoundedPshOn U (v₀ i))
    (hanti : ∀ i z, z ∈ U → Antitone (fun j => v j i z))
    (hlim : ∀ i z, z ∈ U → Tendsto (fun j => v j i z) atTop (𝓝 (v₀ i z)))
    {σ τ : ComplexModel n → RealForm n 2}
    (hσ : ContDiffOn ℝ ∞ σ U) (hτ : ContDiffOn ℝ ∞ τ U)
    (s : Finset (Fin p)) :
    WeakTendsto (fun j => residualSplitTerm p r (v j) hσ hτ T s)
      (residualSplitTerm p r v₀ hσ hτ T s) := by
  dsimp only [residualSplitTerm]
  apply weakTendsto_wedgeForm
  exact backgroundExpansion_decreasing s.card (r + (p - s.card)) _
    (isPositive_castLPC _ hT) (isClosedAny_castLPC _ hTc)
    (fun j i => v j (s.orderEmbOfFin rfl i)) (fun i => v₀ (s.orderEmbOfFin rfl i))
    (fun j i => hv j _) (fun i => hv₀ _) (fun i z hz => hanti _ z hz)
    (fun i z hz => hlim _ z hz) hσ

/-- Exact background splitting, obtained from any actual decreasing smooth
PSH approximation of the bounded corrected tuple. -/
theorem backgroundExpansion_split_of_approximation (p r : ℕ)
    (T : LocalProductCurrent n U (r + p)) (hT : IsPositive T)
    (hTc : IsClosedAny (r + p) T)
    (v : Fin p → ComplexModel n → ℝ) (hv : ∀ i, IsLocallyBoundedPshOn U (v i))
    (f : ℕ → Fin p → ComplexModel n → ℝ)
    (hf : ∀ i, IsDecreasingApproximation U (v i) (fun j => f j i))
    {σ τ : ComplexModel n → RealForm n 2}
    (hσ : ContDiffOn ℝ ∞ σ U) (hτ : ContDiffOn ℝ ∞ τ U)
    (hσS : ∀ z ∈ U, σ z ∈ formSpan n 1)
    (hτS : ∀ z ∈ U, τ z ∈ formSpan n 1) :
    backgroundExpansion p r v (hσ.add hτ) T =
      ∑ s : Finset (Fin p), residualSplitTerm p r v hσ hτ T s := by
  classical
  have heq (j : ℕ) := backgroundExpansion_split_smooth p r (f j)
    (fun i => ((hf i).1 j).1) (fun i => ((hf i).1 j).2.1) hσ hτ hσS hτS T hT hTc
  have hleft := backgroundExpansion_decreasing p r T hT hTc f v
    (fun j i => isLocallyBoundedPshOn_of_isSmoothPshOn ((hf i).1 j)) hv
    (fun i z hz => (hf i).2.1 z hz) (fun i z hz => (hf i).2.2 z hz) (hσ.add hτ)
  ext γ φ
  apply tendsto_nhds_unique (hleft γ φ)
  simp_rw [heq, LinearMap.sum_apply, _root_.sum_apply]
  exact tendsto_finsetSum _ fun s _ => residualSplitTerm_decreasing p r T hT hTc f v
    (fun j i => isLocallyBoundedPshOn_of_isSmoothPshOn ((hf i).1 j)) hv
    (fun i z hz => (hf i).2.1 z hz) (fun i z hz => (hf i).2.2 z hz) hσ hτ s γ φ

theorem residualSplitTerm_restrict (hVU : V ≤ U) (p r : ℕ)
    (T : LocalProductCurrent n U (r + p)) (hT : IsPositive T)
    (hTc : IsClosedAny (r + p) T)
    (v : Fin p → ComplexModel n → ℝ) (hv : ∀ i, IsLocallyBoundedPshOn U (v i))
    {σ τ : ComplexModel n → RealForm n 2}
    (hσ : ContDiffOn ℝ ∞ σ U) (hτ : ContDiffOn ℝ ∞ τ U)
    (s : Finset (Fin p)) :
    restrict hVU (residualSplitTerm p r v hσ hτ T s) =
      residualSplitTerm p r v (hσ.mono hVU) (hτ.mono hVU) (restrict hVU T) s := by
  dsimp only [residualSplitTerm]
  rw [wedgeForm_restrict, backgroundExpansion_restrict hVU _ _ _
    (isPositive_castLPC _ hT) (isClosedAny_castLPC _ hTc) _ (fun i => hv _)]
  have hcast : ∀ {a b : ℕ} (h : a = b) (T : LocalProductCurrent n U a),
      restrict hVU (castLPC h T) = castLPC h (restrict hVU T) := by
    intro a b h
    subst h
    intro T
    rfl
  rw [hcast]

/-- Exact common-background splitting for actual bounded product currents
on an arbitrary open set. No positivity or closedness of the residuals is
required. -/
theorem backgroundExpansion_split (p r : ℕ)
    (T : LocalProductCurrent n U (r + p)) (hT : IsPositive T)
    (hTc : IsClosedAny (r + p) T)
    (v : Fin p → ComplexModel n → ℝ) (hv : ∀ i, IsLocallyBoundedPshOn U (v i))
    {σ τ : ComplexModel n → RealForm n 2}
    (hσ : ContDiffOn ℝ ∞ σ U) (hτ : ContDiffOn ℝ ∞ τ U)
    (hσS : ∀ z ∈ U, σ z ∈ formSpan n 1)
    (hτS : ∀ z ∈ U, τ z ∈ formSpan n 1) :
    backgroundExpansion p r v (hσ.add hτ) T =
      ∑ s : Finset (Fin p), residualSplitTerm p r v hσ hτ T s := by
  classical
  apply eq_of_local
  intro x hx
  obtain ⟨a, ha, hball⟩ := Metric.isOpen_iff.mp U.isOpen x hx
  let A : Opens (ComplexModel n) := ⟨Metric.ball x (a / 2), Metric.isOpen_ball⟩
  have hAU : A ≤ U := fun z hz => hball (Metric.ball_subset_ball (by linarith) hz)
  have hArel : RelativelyCompactIn A U := relativelyCompactIn_half_ball ha hball
  refine ⟨A, hAU, Metric.mem_ball_self (half_pos ha), ?_⟩
  have happrox : ∀ i, ∃ f : ℕ → ComplexModel n → ℝ,
      IsDecreasingApproximation A (v i) f := fun i =>
    HolomorphicPullback.exists_decreasingMollifierApproximation (hv i) hArel
  choose f hf using happrox
  have hsum : restrict hAU (∑ s : Finset (Fin p), residualSplitTerm p r v hσ hτ T s) =
      ∑ s : Finset (Fin p), residualSplitTerm p r v (hσ.mono hAU) (hτ.mono hAU)
        (restrict hAU T) s := by
    ext γ φ
    simp only [LocalBedfordTaylorLocality.restrict_apply, LinearMap.sum_apply, _root_.sum_apply]
    apply Finset.sum_congr rfl
    intro s _
    exact congrArg (fun R : LocalProductCurrent n A r => R γ φ)
      (residualSplitTerm_restrict hAU p r T hT hTc v hv hσ hτ s)
  rw [hsum, backgroundExpansion_restrict hAU p r T hT hTc v hv]
  exact backgroundExpansion_split_of_approximation p r (restrict hAU T)
    (isPositive_restrict hT hAU) (isClosedAny_restrict hTc hAU) v
    (fun i => isLocallyBoundedPshOn_mono (hv i) hAU) (fun j i => f i j) hf
    (hσ.mono hAU) (hτ.mono hAU)
    (fun z hz => hσS z (hAU hz)) (fun z hz => hτS z (hAU hz))

/-- The zero-residual identity for the actual bounded product on any open
domain. -/
theorem backgroundExpansion_zero (p r : ℕ)
    (T : LocalProductCurrent n U (r + p)) (hT : IsPositive T)
    (hTc : IsClosedAny (r + p) T)
    (v : Fin p → ComplexModel n → ℝ) (hv : ∀ i, IsLocallyBoundedPshOn U (v i)) :
    backgroundExpansion p r v (contDiffOn_const (c := (0 : RealForm n 2))) T =
      btProduct p r v T := by
  classical
  apply eq_of_local
  intro x hx
  obtain ⟨a, ha, hball⟩ := Metric.isOpen_iff.mp U.isOpen x hx
  let A : Opens (ComplexModel n) := ⟨Metric.ball x (a / 2), Metric.isOpen_ball⟩
  have hAU : A ≤ U := fun z hz => hball (Metric.ball_subset_ball (by linarith) hz)
  have hArel : RelativelyCompactIn A U := relativelyCompactIn_half_ball ha hball
  refine ⟨A, hAU, Metric.mem_ball_self (half_pos ha), ?_⟩
  rw [backgroundExpansion_restrict hAU p r T hT hTc v hv,
    ← btProduct_restrict hAU p r v T hT hTc hv]
  have happrox : ∀ i, ∃ f : ℕ → ComplexModel n → ℝ,
      IsDecreasingApproximation A (v i) f := fun i =>
    HolomorphicPullback.exists_decreasingMollifierApproximation (hv i) hArel
  choose f hf using happrox
  exact backgroundExpansion_zero_of_approximation p r (restrict hAU T)
    (isPositive_restrict hT hAU) (isClosedAny_restrict hTc hAU) v
    (fun i => isLocallyBoundedPshOn_mono (hv i) hAU) (fun j i => f i j) hf

/-- The corrected ordinary product is exactly the sum of genuine Hermitian
subproducts wedged with complementary powers of minus the residual. This
is the lower-product expansion used in torsion trace estimates. -/
theorem btProduct_eq_sum_backgroundExpansion (p r : ℕ)
    (T : LocalProductCurrent n U (r + p)) (hT : IsPositive T)
    (hTc : IsClosedAny (r + p) T)
    (v : Fin p → ComplexModel n → ℝ) (hv : ∀ i, IsLocallyBoundedPshOn U (v i))
    {σ : ComplexModel n → RealForm n 2} (hσ : ContDiffOn ℝ ∞ σ U)
    (hσS : ∀ z ∈ U, σ z ∈ formSpan n 1) :
    btProduct p r v T =
      ∑ s : Finset (Fin p), residualSplitTerm p r v hσ hσ.neg T s := by
  have hsum := backgroundExpansion_split p r T hT hTc v hv hσ hσ.neg hσS
    (fun z hz => (formSpan n 1).neg_mem (hσS z hz))
  have hzero : backgroundExpansion p r v (hσ.add hσ.neg) T =
      backgroundExpansion p r v (contDiffOn_const (c := (0 : RealForm n 2))) T := by
    apply backgroundExpansion_congr p r T v v (fun _ _ _ => rfl)
    intro z _
    exact add_neg_cancel _
  rw [hzero, backgroundExpansion_zero p r T hT hTc v hv] at hsum
  exact hsum

/-- Every actual summand in the background splitting is positive when
the selected Hermitian factors and the complementary smooth form are
positive. The subproduct positivity is proved internally. -/
theorem isPositive_residualSplitTerm {m : ℕ} {U : Opens (ComplexModel (m + 1))}
    (p r : ℕ) (T : LocalProductCurrent (m + 1) U (r + p))
    (hT : IsPositive T) (hTc : IsClosedAny (r + p) T)
    (v : Fin p → ComplexModel (m + 1) → ℝ)
    (hv : ∀ i, IsLocallyBoundedPshOn U (v i))
    {σ τ : ComplexModel (m + 1) → RealForm (m + 1) 2}
    (hσ : ContDiffOn ℝ ∞ σ U) (hτ : ContDiffOn ℝ ∞ τ U)
    (hσ11 : ∀ z ∈ U, IsOneOne (σ z))
    (hfactor : ∀ i, IsPositive
      (ddcMul (oneCurrent U) (v i) + wedgeForm rfl (oneCurrent U) hσ))
    (hτpos : ∀ z ∈ U, IsSemipositiveOneOne (τ z)) (s : Finset (Fin p)) :
    IsPositive (residualSplitTerm p r v hσ hτ T s) := by
  dsimp only [residualSplitTerm]
  exact isPositive_wedgeForm_smooth_product rfl
    (isPositive_backgroundExpansion s.card (r + (p - s.card)) _
      (isPositive_castLPC _ hT) (isClosedAny_castLPC _ hTc) _ (fun i => hv _)
      hσ hσ11 (fun i => hfactor _)) (fun _ => τ) (fun _ => hτ)
    (fun _ z hz => hτpos z hz)

end SGPT.PSH.HermitianProducts
