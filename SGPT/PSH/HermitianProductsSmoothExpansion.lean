import SGPT.PSH.HermitianProductsResidualParameter
import SGPT.PSH.HermitianProductsFiniteSelection
import SGPT.PSH.HermitianSmoothWedgeAssociation
import SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorSmoothProductDensity

/-!
# The actual smooth form represented by the Hermitian subset expansion

The residual form may be nonclosed. Smooth Bedford--Taylor factors are
identified with their true exterior forms, then finite multilinearity
reassembles the subset expansion into the full smooth exterior product.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianProducts

open Set Filter MeasureTheory TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open FirstPass.MongeAmpere StronglyPositiveForms LocalProductCurrents
  LocalBedfordTaylorProducts LocalBedfordTaylorSmooth LocalBedfordTaylorForms
  LocalBedfordTaylorSmoothProductDensity LocalBedfordTaylorContinuity
  LocalBedfordTaylorCollar TopDegreeDensity ConstantFormProducts
open scoped Topology Distributions ContDiff

variable {n : ℕ} {U : Opens (ComplexModel n)}

/-- Finite multilinearity is applied to the actual smooth wedge tested
against the given current. No positivity or closedness is used here. -/
theorem smoothWedgeTest_product_add (p r : ℕ)
    (T : LocalProductCurrent n U (r + p)) (γ : formSpan n r) (φ : 𝓓(U, ℝ))
    (α β : Fin p → smoothFormSpace n U 1) :
    smoothWedgeTest rfl T γ φ (smoothFormProduct p (α + β)) =
      ∑ s : Finset (Fin p),
        smoothWedgeTest rfl T γ φ (smoothFormProduct p (s.piecewise α β)) := by
  classical
  exact ((smoothWedgeTest rfl T γ φ).compMultilinearMap
    (smoothFormProduct p)).map_add_univ α β

private theorem wedgeForm_cast_source {a b r k : ℕ} (hab : a = b) (h : r + k = a)
    (T : LocalProductCurrent n U a) {α : ComplexModel n → RealForm n (2 * k)}
    (hα : ContDiffOn ℝ ∞ α U) :
    wedgeForm (h.trans hab) (castLPC hab T) hα = wedgeForm h T hα := by
  subst hab
  rfl

private theorem wedgeForm_eq_of_function_eq {r k m : ℕ} (h : r + k = m)
    (T : LocalProductCurrent n U m)
    {α β : ComplexModel n → RealForm n (2 * k)}
    (hα : ContDiffOn ℝ ∞ α U) (hβ : ContDiffOn ℝ ∞ β U) (heq : α = β) :
    wedgeForm h T hα = wedgeForm h T hβ := by
  subst β
  rfl

private theorem wedgeForm_wedge_cast_target {r k l p : ℕ} (hklp : k + l = p)
    (hdeg : r + p = r + l + k) (T : LocalProductCurrent n U (r + p))
    {α : ComplexModel n → RealForm n (2 * k)}
    {β : ComplexModel n → RealForm n (2 * l)}
    (hα : ContDiffOn ℝ ∞ α U) (hβ : ContDiffOn ℝ ∞ β U)
    (hαS : ∀ z ∈ U, α z ∈ formSpan n k)
    (hβS : ∀ z ∈ U, β z ∈ formSpan n l) :
    wedgeForm rfl (wedgeForm rfl (castLPC hdeg T) hα) hβ =
      wedgeForm rfl T
        (HermitianSmoothWedgeAssociation.contDiffOn_wedgeTo
          (by omega : 2 * k + 2 * l = 2 * p) hα hβ) := by
  subst p
  rw [HermitianSmoothWedgeAssociation.wedgeForm_wedge rfl _ hα hβ hαS hβS]
  exact wedgeForm_cast_source hdeg rfl T _

private theorem smoothFormProduct_selected_const_value (p : ℕ) (s : Finset (Fin p))
    (α : Fin p → smoothFormSpace n U 1) (β : smoothFormSpace n U 1)
    (z : ComplexModel n) :
    smoothFormProduct p (s.piecewise α (fun _ => β)) z =
      wedgeTo (by
        have hc : s.card ≤ p := by simpa using Finset.card_le_univ s
        omega :
        2 * s.card + 2 * (p - s.card) = 2 * p)
        (wedgeProd s.card (fun i => α (s.orderEmbOfFin rfl i) z))
        (wedgeProd (p - s.card) (fun _ => β z)) := by
  classical
  change wedgeProd p (fun i => (s.piecewise α (fun _ => β) i) z) = _
  have ht : (fun i => (s.piecewise α (fun _ => β) i) z) =
      s.piecewise (fun i => α i z) (fun _ => β z) := by
    funext i
    by_cases hi : i ∈ s <;> simp [Finset.piecewise, hi]
  rw [ht]
  exact wedgeProd_selected_const p s (fun i => α i z) (β z)

private theorem smooth_selected_wedge (p r : ℕ)
    (T : LocalProductCurrent n U (r + p)) (s : Finset (Fin p))
    (α : Fin p → smoothFormSpace n U 1) (β : smoothFormSpace n U 1) :
    wedgeForm rfl T
      (HermitianSmoothWedgeAssociation.contDiffOn_wedgeTo
        (by
          have hc : s.card ≤ p := by simpa using Finset.card_le_univ s
          omega : 2 * s.card + 2 * (p - s.card) = 2 * p)
        (contDiffOn_wedgeProd s.card (fun i => α (s.orderEmbOfFin rfl i))
          (fun i => (α _).property))
        (contDiffOn_wedgeProd (p - s.card) (fun _ => β) (fun _ => β.property))) =
      wedgeForm rfl T (smoothFormProduct p (s.piecewise α (fun _ => β))).property := by
  classical
  apply wedgeForm_eq_of_function_eq
  funext z
  exact (smoothFormProduct_selected_const_value p s α β z).symm

/-- The selected smooth Bedford--Taylor term and residual power form one
actual smooth wedge against the original, uncast base current. -/
theorem backgroundExpansionTerm_smooth_eq_block (p r : ℕ)
    (v : Fin p → ComplexModel n → ℝ)
    (hv : ∀ i, ContDiffOn ℝ ∞ (v i) U)
    (hvp : ∀ i, PlurisubharmonicOn (fun z => (v i z : EReal)) U)
    {σ : ComplexModel n → RealForm n 2} (hσ : ContDiffOn ℝ ∞ σ U)
    (hσS : ∀ z ∈ U, σ z ∈ formSpan n 1)
    (T : LocalProductCurrent n U (r + p)) (hT : IsPositive T)
    (hTc : IsClosedAny (r + p) T) (s : Finset (Fin p)) :
    backgroundExpansionTerm p r v hσ T s =
      wedgeForm rfl T
        (HermitianSmoothWedgeAssociation.contDiffOn_wedgeTo
          (by
            have hc : s.card ≤ p := by simpa using Finset.card_le_univ s
            omega : 2 * s.card + 2 * (p - s.card) = 2 * p)
          (contDiffOn_wedgeProd s.card (fun i => ddcForm (v (s.orderEmbOfFin rfl i)))
            (fun i => contDiffOn_ddcForm (hv _)))
          (contDiffOn_wedgeProd (p - s.card) (fun _ => σ) (fun _ => hσ))) := by
  classical
  have hcard : s.card ≤ p := by simpa using Finset.card_le_univ s
  have hsum : s.card + (p - s.card) = p := by omega
  have hdeg : r + p = r + (p - s.card) + s.card := by omega
  let w : Fin s.card → ComplexModel n → ℝ := fun i => v (s.orderEmbOfFin rfl i)
  have hw : ∀ i, ContDiffOn ℝ ∞ (w i) U := fun i => hv _
  have hwp : ∀ i, PlurisubharmonicOn (fun z => (w i z : EReal)) U := fun i => hvp _
  let hD := contDiffOn_wedgeProd s.card (fun i => ddcForm (w i))
    (fun i => contDiffOn_ddcForm (hw i))
  let hP := contDiffOn_wedgeProd (p - s.card) (fun _ => σ) (fun _ => hσ)
  have hDS : ∀ z ∈ U, wedgeProd s.card (fun i => ddcForm (w i) z) ∈ formSpan n s.card := by
    intro z hz
    exact wedgeProd_mem_formSpan _ _ fun i =>
      ddcForm_mem_formSpan (hw i)
        (fun y hy d => leviForm_nonneg_of_contDiffOn_plurisubharmonicOn (hw i) (hwp i) hy d)
        z hz
  have hPS : ∀ z ∈ U, wedgeProd (p - s.card) (fun _ => σ z) ∈ formSpan n (p - s.card) :=
    fun z hz => wedgeProd_mem_formSpan _ _ (fun _ => hσS z hz)
  have hbt := btProduct_eq_wedgeForm s.card (r + (p - s.card)) w hw hwp
    (castLPC hdeg T) (isPositive_castLPC hdeg hT) (isClosedAny_castLPC hdeg hTc)
  unfold backgroundExpansionTerm
  change wedgeForm rfl (btProduct s.card (r + (p - s.card)) w (castLPC hdeg T)) hP = _
  rw [hbt, wedgeForm_wedge_cast_target hsum hdeg T hD hP hDS hPS]

/-- Each genuine smooth subset term equals the wedge by the corresponding
full selected tuple. The smooth residual needs only its actual `(1,1)`
type; it may have arbitrary sign and may be nonclosed. -/
theorem backgroundExpansionTerm_smooth_eq_selected (p r : ℕ)
    (v : Fin p → ComplexModel n → ℝ)
    (hv : ∀ i, ContDiffOn ℝ ∞ (v i) U)
    (hvp : ∀ i, PlurisubharmonicOn (fun z => (v i z : EReal)) U)
    {σ : ComplexModel n → RealForm n 2} (hσ : ContDiffOn ℝ ∞ σ U)
    (hσS : ∀ z ∈ U, σ z ∈ formSpan n 1)
    (T : LocalProductCurrent n U (r + p)) (hT : IsPositive T)
    (hTc : IsClosedAny (r + p) T) (s : Finset (Fin p)) :
    backgroundExpansionTerm p r v hσ T s =
      wedgeForm rfl T
        (smoothFormProduct p
          (s.piecewise
            (fun i => (⟨ddcForm (v i), contDiffOn_ddcForm (hv i)⟩ : smoothFormSpace n U 1))
            (fun _ => (⟨σ, hσ⟩ : smoothFormSpace n U 1)))).property := by
  classical
  let α : Fin p → smoothFormSpace n U 1 := fun i => ⟨ddcForm (v i), contDiffOn_ddcForm (hv i)⟩
  let β : smoothFormSpace n U 1 := ⟨σ, hσ⟩
  exact (backgroundExpansionTerm_smooth_eq_block p r v hv hvp hσ hσS T hT hTc s).trans
    (smooth_selected_wedge p r T s α β)

/-- For smooth PSH potentials, the full literal Hermitian expansion is the
actual exterior product of their full `ddᶜvᵢ + σ` forms. No closedness of
the residual form and no positivity of the desired product are assumed. -/
theorem backgroundExpansion_smooth (p r : ℕ)
    (v : Fin p → ComplexModel n → ℝ)
    (hv : ∀ i, ContDiffOn ℝ ∞ (v i) U)
    (hvp : ∀ i, PlurisubharmonicOn (fun z => (v i z : EReal)) U)
    {σ : ComplexModel n → RealForm n 2} (hσ : ContDiffOn ℝ ∞ σ U)
    (hσS : ∀ z ∈ U, σ z ∈ formSpan n 1)
    (T : LocalProductCurrent n U (r + p)) (hT : IsPositive T)
    (hTc : IsClosedAny (r + p) T) :
    backgroundExpansion p r v hσ T =
      wedgeForm rfl T (contDiffOn_wedgeProd p
        (fun i z => ddcForm (v i) z + σ z)
        (fun i => (contDiffOn_ddcForm (hv i)).add hσ)) := by
  classical
  ext γ φ
  let α : Fin p → smoothFormSpace n U 1 := fun i => ⟨ddcForm (v i), contDiffOn_ddcForm (hv i)⟩
  let β : Fin p → smoothFormSpace n U 1 := fun _ => ⟨σ, hσ⟩
  simp only [backgroundExpansion, LinearMap.sum_apply, _root_.sum_apply]
  change (∑ s : Finset (Fin p), backgroundExpansionTerm p r v hσ T s γ φ) =
    smoothWedgeTest rfl T γ φ (smoothFormProduct p (α + β))
  calc
    _ = ∑ s : Finset (Fin p),
        smoothWedgeTest rfl T γ φ (smoothFormProduct p (s.piecewise α β)) := by
      apply Finset.sum_congr rfl
      intro s _
      exact congrArg (fun R : LocalProductCurrent n U r => R γ φ)
        (backgroundExpansionTerm_smooth_eq_selected p r v hv hvp hσ hσS T hT hTc s)
    _ = _ := (smoothWedgeTest_product_add p r T γ φ α β).symm

end SGPT.PSH.HermitianProducts
