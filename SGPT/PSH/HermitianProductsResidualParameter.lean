import SGPT.PSH.HermitianProducts
import SGPT.Foundations.Analysis.Pending.ClosedCurrentLocalTests
import SGPT.Foundations.Analysis.Pending.DistributionTranslationJets

/-!
# Weak continuity in an affine smooth residual

The smooth forms on the original coordinate domain form their usual real
vector space. Exterior product is multilinear there. For a fixed current and
compact test its values along finitely many fixed affine real lines are
continuous, by reducing the parameter space to finitely many copies of ℝ².
This proves that adding a Euclidean error tending to zero to the residual
leaves the actual Hermitian expansion unchanged in the weak limit.
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
  ClosedCurrentLocalTests
open scoped Topology Distributions ContDiff

variable {n : ℕ} {U : Opens (ComplexModel n)}

/-- The ordinary real vector space of smooth degree-`2k` forms on an actual
coordinate open set. No closedness or positivity is stored. -/
def smoothFormSpace (n : ℕ) (U : Opens (ComplexModel n)) (k : ℕ) :
    Submodule ℝ (ComplexModel n → RealForm n (2 * k)) where
  carrier := {α | ContDiffOn ℝ ∞ α U}
  zero_mem' := contDiffOn_const
  add_mem' := fun hα hβ => hα.add hβ
  smul_mem' := fun c _ hα => hα.const_smul c

instance {k : ℕ} : CoeFun (smoothFormSpace n U k)
    (fun _ => ComplexModel n → RealForm n (2 * k)) := ⟨fun α => α.val⟩

private def smoothProductValue (p : ℕ)
    (α : Fin p → smoothFormSpace n U 1) : smoothFormSpace n U p :=
  ⟨fun z => TopDegreeDensity.wedgeProd p (fun i => α i z),
    contDiffOn_wedgeProd p (fun i => α i) (fun i => (α i).property)⟩

private theorem smoothProduct_update_add (p : ℕ)
    (α : Fin p → smoothFormSpace n U 1) (i : Fin p) (x y : smoothFormSpace n U 1) :
    smoothProductValue p (Function.update α i (x + y)) =
      smoothProductValue p (Function.update α i x) +
        smoothProductValue p (Function.update α i y) := by
  classical
  apply Subtype.ext
  funext z
  have he (c : smoothFormSpace n U 1) :
      (fun j => Function.update α i c j z) = Function.update (fun j => α j z) i (c z) := by
    ext j
    by_cases hj : j = i <;> simp [hj]
  change TopDegreeDensity.wedgeProd p (fun j => Function.update α i (x + y) j z) =
    TopDegreeDensity.wedgeProd p (fun j => Function.update α i x j z) +
      TopDegreeDensity.wedgeProd p (fun j => Function.update α i y j z)
  rw [he, he, he]
  exact wedgeProd_update_add p (fun j => α j z) i (x z) (y z)

private theorem smoothProduct_update_smul (p : ℕ)
    (α : Fin p → smoothFormSpace n U 1) (i : Fin p) (c : ℝ) (x : smoothFormSpace n U 1) :
    smoothProductValue p (Function.update α i (c • x)) =
      c • smoothProductValue p (Function.update α i x) := by
  classical
  apply Subtype.ext
  funext z
  have he (b : smoothFormSpace n U 1) :
      (fun j => Function.update α i b j z) = Function.update (fun j => α j z) i (b z) := by
    ext j
    by_cases hj : j = i <;> simp [hj]
  change TopDegreeDensity.wedgeProd p (fun j => Function.update α i (c • x) j z) =
    c • TopDegreeDensity.wedgeProd p (fun j => Function.update α i x j z)
  rw [he, he]
  exact wedgeProd_update_smul p (fun j => α j z) i c (x z)

/-- The actual smooth exterior product, as an algebraic multilinear map on
the ordinary smooth form spaces. -/
def smoothFormProduct (p : ℕ) :
    MultilinearMap ℝ (fun _ : Fin p => smoothFormSpace n U 1) (smoothFormSpace n U p) :=
  MultilinearMap.mk' (smoothProductValue p) (smoothProduct_update_add p)
    (smoothProduct_update_smul p)

/-- Wedging a fixed current and reading a fixed compact test is a real
linear map on the actual smooth form space. -/
def smoothWedgeTest {r k m : ℕ} (h : r + k = m)
    (T : LocalProductCurrent n U m) (γ : formSpan n r) (φ : 𝓓(U, ℝ)) :
    smoothFormSpace n U k →ₗ[ℝ] ℝ where
  toFun α := wedgeForm h T α.property γ φ
  map_add' α β := by
    have he := congrArg (fun C => C γ φ) (wedgeForm_add h T α.property β.property)
    exact he
  map_smul' c α := by
    have he := congrArg (fun C => C γ φ) (wedgeForm_smul h T α.property c)
    exact he

/-- An algebraic multilinear scalar map is continuous along any fixed
finite family of affine real lines, even if its original module has no
topology. The proof uses the genuine finite-dimensional parameter space. -/
theorem multilinear_affine_tendsto_zero {A : Type*} [AddCommGroup A] [Module ℝ A]
    (p : ℕ) (f : MultilinearMap ℝ (fun _ : Fin p => A) ℝ)
    (a b : Fin p → A) {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun j => f (fun i => a i + ε j • b i)) atTop (𝓝 (f a)) := by
  let L (i : Fin p) : (ℝ × ℝ) →ₗ[ℝ] A :=
    { toFun x := x.1 • a i + x.2 • b i
      map_add' x y := by
        change (x.1 + y.1) • a i + (x.2 + y.2) • b i =
          (x.1 • a i + x.2 • b i) + (y.1 • a i + y.2 • b i)
        module
      map_smul' c x := by
        change (c * x.1) • a i + (c * x.2) • b i = c • (x.1 • a i + x.2 • b i)
        module }
  let g := f.compLinearMap L
  let G := multilinearMapToContinuousOfFiniteDimensional g
  have hval (x : Fin p → ℝ × ℝ) : G x = f (fun i => (x i).1 • a i + (x i).2 • b i) :=
    multilinearMapToContinuousOfFiniteDimensional_apply g x
  have hparam : Tendsto (fun j => fun _ : Fin p => ((1 : ℝ), ε j)) atTop
      (𝓝 (fun _ : Fin p => ((1 : ℝ), (0 : ℝ)))) :=
    tendsto_pi_nhds.mpr fun _ => by
      simpa only [nhds_prod_eq] using
        ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).prodMk hε)
  have hlim := G.cont.continuousAt.tendsto.comp hparam
  change Tendsto (fun j => G (fun _ => ((1 : ℝ), ε j))) atTop
    (𝓝 (G (fun _ => ((1 : ℝ), (0 : ℝ))))) at hlim
  simpa only [hval, one_smul, zero_smul, add_zero] using hlim

/-- Every fixed current sees weak convergence of powers of an affine smooth
residual when its real scalar parameter tends to zero. No current positivity
or closedness is needed. -/
theorem weakTendsto_wedgePower_affine {r k m : ℕ} (h : r + k = m)
    (T : LocalProductCurrent n U m)
    {σ β : ComplexModel n → RealForm n 2}
    (hσ : ContDiffOn ℝ ∞ σ U) (hβ : ContDiffOn ℝ ∞ β U)
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0)) :
    WeakTendsto
      (fun j => wedgeForm h T (contDiffOn_wedgeProd k
        (fun _ z => σ z + ε j • β z) (fun _ => hσ.add (hβ.const_smul (ε j)))))
      (wedgeForm h T (contDiffOn_wedgeProd k (fun _ => σ) (fun _ => hσ))) := by
  intro γ φ
  let f := (smoothWedgeTest h T γ φ).compMultilinearMap (smoothFormProduct (n := n) (U := U) k)
  let a : Fin k → smoothFormSpace n U 1 := fun _ => ⟨σ, hσ⟩
  let b : Fin k → smoothFormSpace n U 1 := fun _ => ⟨β, hβ⟩
  convert multilinear_affine_tendsto_zero k f a b hε using 1 <;> rfl

/-- Every literal subset term of the Hermitian expansion is weakly
continuous when an affine smooth residual error tends to zero. -/
theorem backgroundExpansionTerm_affine_residual (p r : ℕ)
    (v : Fin p → ComplexModel n → ℝ) (T : LocalProductCurrent n U (r + p))
    {σ β : ComplexModel n → RealForm n 2}
    (hσ : ContDiffOn ℝ ∞ σ U) (hβ : ContDiffOn ℝ ∞ β U)
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0)) (s : Finset (Fin p)) :
    WeakTendsto
      (fun j => backgroundExpansionTerm p r v (hσ.add (hβ.const_smul (ε j))) T s)
      (backgroundExpansionTerm p r v hσ T s) := by
  classical
  dsimp only [backgroundExpansionTerm]
  exact weakTendsto_wedgePower_affine rfl _ hσ hβ hε

/-- The actual finite nonclosed-background expansion has its original weak
limit when an affine smooth residual error tends to zero. The currents in
the fixed Bedford--Taylor subset terms do not vary in this limit. -/
theorem backgroundExpansion_affine_residual (p r : ℕ)
    (v : Fin p → ComplexModel n → ℝ) (T : LocalProductCurrent n U (r + p))
    {σ β : ComplexModel n → RealForm n 2}
    (hσ : ContDiffOn ℝ ∞ σ U) (hβ : ContDiffOn ℝ ∞ β U)
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0)) :
    WeakTendsto
      (fun j => backgroundExpansion p r v (hσ.add (hβ.const_smul (ε j))) T)
      (backgroundExpansion p r v hσ T) := by
  classical
  intro γ φ
  simp only [backgroundExpansion, LinearMap.sum_apply, _root_.sum_apply]
  exact tendsto_finsetSum _ fun s _ =>
    backgroundExpansionTerm_affine_residual p r v T hσ hβ hε s γ φ

/-- Positivity is retained in the zero-error limit of the actual Hermitian
expansion. The hypothesis concerns the whole positive-error family and must
be supplied by the smooth regularization argument. -/
theorem isPositive_backgroundExpansion_of_positive_errors (p r : ℕ)
    (v : Fin p → ComplexModel n → ℝ) (T : LocalProductCurrent n U (r + p))
    {σ β : ComplexModel n → RealForm n 2}
    (hσ : ContDiffOn ℝ ∞ σ U) (hβ : ContDiffOn ℝ ∞ β U)
    (hpos : ∀ ε : ℝ, 0 < ε →
      IsPositive (backgroundExpansion p r v (hσ.add (hβ.const_smul ε)) T)) :
    IsPositive (backgroundExpansion p r v hσ T) := by
  apply LocalBedfordTaylorContinuity.isPositive_of_weakTendsto
    (T := fun j => backgroundExpansion p r v
      (hσ.add (hβ.const_smul (1 / ((j : ℝ) + 1)))) T)
  · intro j
    exact hpos _ (by positivity)
  · exact backgroundExpansion_affine_residual p r v T hσ hβ
      tendsto_one_div_add_atTop_nhds_zero_nat

end SGPT.PSH.HermitianProducts
