import SGPT.Foundations.Analysis.Pending.NaturalComplexPPProjector
import SGPT.Foundations.Analysis.Pending.NaturalSmoothPurePPTransport
import SGPT.Foundations.Analysis.Pending.DistributionTranslationJets
import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional

/-!
# An internally constructed original smooth pure-type projector

The actual complex projector is restricted to real tensors, upgraded without
changing its evaluations, and bundled as a real CLM. Its naturality produces
the original smooth tensor overlap field and explicit geometric quotient map.
No type, projector, continuity, compatibility or descent certificate is supplied.
No global function-space topology or exterior closedness preservation is claimed.
-/

noncomputable section

namespace SGPT.Foundations.Analysis.Pending.NaturalSmoothPPProjector

open SGPT.Foundations.Analysis.FirstPass
open NaturalComplexBidegreeTransport NaturalRealAlternatingComplexification
open NaturalComplexPPProjector NaturalSmoothPurePPTransport
open scoped Manifold ContDiff

def algebraicRealProjector {n p : ℕ} (A : ComplexModel n [⋀^Fin (p + p)]→ₗ[ℝ] ℝ) :
    ComplexModel n [⋀^Fin (p + p)]→ₗ[ℝ] ℝ := by
  let F := ppProjector (complexify A)
  let G : complexification n [⋀^Fin (p + p)]→ₗ[ℝ] ℂ :=
    { F.toMultilinearMap.restrictScalars ℝ with
      map_eq_zero_of_eq' := fun v _ _ h hij => F.map_eq_zero_of_eq v h hij }
  exact Complex.reCLM.toLinearMap.compAlternatingMap (G.compLinearMap (realEmbedding n))

theorem algebraicRealProjector_apply {n p : ℕ}
    (A : ComplexModel n [⋀^Fin (p + p)]→ₗ[ℝ] ℝ) (v : Fin (p + p) → ComplexModel n) :
    algebraicRealProjector A v =
      (ppProjector (complexify A) (fun j => realEmbedding n (v j))).re := rfl

theorem complexify_algebraicRealProjector {n p : ℕ}
    (A : ComplexModel n [⋀^Fin (p + p)]→ₗ[ℝ] ℝ) :
    complexify (algebraicRealProjector A) = ppProjector (complexify A) := by
  symm
  apply complexify_unique
  intro v
  rw [algebraicRealProjector_apply]
  apply Complex.ext
  · simp
  · simp [ppProjector_complexify_im]

private def continuousUpgrade {n d : ℕ} (A : ComplexModel n [⋀^Fin d]→ₗ[ℝ] ℝ) :
    ComplexModel n [⋀^Fin d]→L[ℝ] ℝ where
  toContinuousMultilinearMap := multilinearMapToContinuousOfFiniteDimensional A.toMultilinearMap
  map_eq_zero_of_eq' v i j h hij := by
    simpa using A.map_eq_zero_of_eq v h hij

private theorem continuousUpgrade_apply {n d : ℕ}
    (A : ComplexModel n [⋀^Fin d]→ₗ[ℝ] ℝ) (v : Fin d → ComplexModel n) :
    continuousUpgrade A v = A v :=
  multilinearMapToContinuousOfFiniteDimensional_apply _ v

def realProjector {n p : ℕ} (A : ComplexModel n [⋀^Fin (2 * p)]→L[ℝ] ℝ) :
    ComplexModel n [⋀^Fin (2 * p)]→L[ℝ] ℝ :=
  continuousUpgrade ((algebraicRealProjector
    (A.toAlternatingMap.domDomCongr (finCongr (two_mul p)))).domDomCongr
      (finCongr (two_mul p)).symm)

theorem realProjector_apply {n p : ℕ} (A : ComplexModel n [⋀^Fin (2 * p)]→L[ℝ] ℝ)
    (v : Fin (2 * p) → ComplexModel n) :
    realProjector A v = algebraicRealProjector
      (A.toAlternatingMap.domDomCongr (finCongr (two_mul p)))
      (v ∘ (finCongr (two_mul p)).symm) := by
  simp only [realProjector, continuousUpgrade_apply, AlternatingMap.domDomCongr_apply]

private theorem realProjector_reindex {n p : ℕ}
    (A : ComplexModel n [⋀^Fin (2 * p)]→L[ℝ] ℝ) :
    (realProjector A).toAlternatingMap.domDomCongr (finCongr (two_mul p)) =
      algebraicRealProjector (A.toAlternatingMap.domDomCongr (finCongr (two_mul p))) := by
  ext v
  simp [AlternatingMap.domDomCongr_apply, realProjector_apply, Function.comp_def]

private theorem ppProjector_add {n p : ℕ}
    (F G : complexification n [⋀^Fin (p + p)]→ₗ[ℂ] ℂ) :
    ppProjector (F + G) = ppProjector F + ppProjector G := by
  classical
  ext v
  simp only [ppProjector_apply, AlternatingMap.add_apply]
  have hite (b : Prop) [Decidable b] (x y : ℂ) :
      (if b then x + y else 0) = (if b then x else 0) + (if b then y else 0) := by
    split <;> simp_all
  simp_rw [hite, Finset.sum_add_distrib, smul_add]
  simp only [Finset.sum_add_distrib, smul_eq_mul, mul_add]

private theorem ppProjector_real_smul {n p : ℕ} (c : ℝ)
    (F : complexification n [⋀^Fin (p + p)]→ₗ[ℂ] ℂ) :
    ppProjector (c • F) = c • ppProjector F := by
  classical
  ext v
  simp only [ppProjector_apply, AlternatingMap.smul_apply]
  have hite (b : Prop) [Decidable b] (x : ℂ) :
      (if b then c • x else 0) = c • (if b then x else 0) := by
    split <;> simp_all
  simp_rw [hite, ← Finset.smul_sum, smul_comm (Equiv.Perm.sign _) c]
  rw [← Finset.smul_sum, smul_comm]

private theorem algebraicRealProjector_add {n p : ℕ}
    (A B : ComplexModel n [⋀^Fin (p + p)]→ₗ[ℝ] ℝ) :
    algebraicRealProjector (A + B) = algebraicRealProjector A + algebraicRealProjector B := by
  ext v
  simp [algebraicRealProjector_apply, NaturalRealPPSubmodule.complexify_add, ppProjector_add]

private theorem algebraicRealProjector_smul {n p : ℕ} (c : ℝ)
    (A : ComplexModel n [⋀^Fin (p + p)]→ₗ[ℝ] ℝ) :
    algebraicRealProjector (c • A) = c • algebraicRealProjector A := by
  ext v
  simp [algebraicRealProjector_apply, NaturalRealPPSubmodule.complexify_real_smul,
    ppProjector_real_smul]

private def realProjectorLM (n p : ℕ) :
    (ComplexModel n [⋀^Fin (2 * p)]→L[ℝ] ℝ) →ₗ[ℝ]
      (ComplexModel n [⋀^Fin (2 * p)]→L[ℝ] ℝ) where
  toFun := realProjector
  map_add' A B := by
    ext v
    simp [realProjector_apply, algebraicRealProjector_add]
  map_smul' c A := by
    ext v
    simp [realProjector_apply, algebraicRealProjector_smul]

private instance tensorFiniteDimensional (n d : ℕ) :
    FiniteDimensional ℝ (ComplexModel n [⋀^Fin d]→L[ℝ] ℝ) := by
  let L : (ComplexModel n [⋀^Fin d]→L[ℝ] ℝ) →ₗ[ℝ]
      MultilinearMap ℝ (fun _ : Fin d => ComplexModel n) ℝ :=
    { toFun := fun A => A.toAlternatingMap.toMultilinearMap
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  apply FiniteDimensional.of_injective L
  intro A B h
  ext v
  exact congrArg (fun F => F v) h

def realProjectorCLM (n p : ℕ) :
    (ComplexModel n [⋀^Fin (2 * p)]→L[ℝ] ℝ) →L[ℝ]
      (ComplexModel n [⋀^Fin (2 * p)]→L[ℝ] ℝ) :=
  LinearMap.toContinuousLinearMap (realProjectorLM n p)

theorem realProjector_isPure {n p : ℕ} (A : ComplexModel n [⋀^Fin (2 * p)]→L[ℝ] ℝ) :
    IsPureRealPP p ((realProjector A).toAlternatingMap.domDomCongr (finCongr (two_mul p))) := by
  unfold IsPureRealPP
  rw [realProjector_reindex, complexify_algebraicRealProjector]
  exact ppProjector_isPure _

theorem realProjector_of_isPure {n p : ℕ} (A : ComplexModel n [⋀^Fin (2 * p)]→L[ℝ] ℝ)
    (hA : IsPureRealPP p (A.toAlternatingMap.domDomCongr (finCongr (two_mul p)))) :
    realProjector A = A := by
  have he : algebraicRealProjector
      (A.toAlternatingMap.domDomCongr (finCongr (two_mul p))) =
        A.toAlternatingMap.domDomCongr (finCongr (two_mul p)) := by
    apply complexify_injective
    rw [complexify_algebraicRealProjector]
    exact ppProjector_of_isPure _ hA
  ext v
  simp [realProjector_apply, he, AlternatingMap.domDomCongr_apply, Function.comp_def]

theorem realProjector_idempotent {n p : ℕ} (A : ComplexModel n [⋀^Fin (2 * p)]→L[ℝ] ℝ) :
    realProjector (realProjector A) = realProjector A :=
  realProjector_of_isPure _ (realProjector_isPure A)

theorem realProjector_compContinuousLinearMap {m n p : ℕ}
    (A : ComplexModel n [⋀^Fin (2 * p)]→L[ℝ] ℝ)
    (L : ComplexModel m →L[ℝ] ComplexModel n)
    (hL : ∀ v, L (Complex.I • v) = Complex.I • L v) :
    realProjector (A.compContinuousLinearMap L) = (realProjector A).compContinuousLinearMap L := by
  have he : algebraicRealProjector
      ((A.toAlternatingMap.domDomCongr (finCongr (two_mul p))).compLinearMap L.toLinearMap) =
      (algebraicRealProjector (A.toAlternatingMap.domDomCongr
        (finCongr (two_mul p)))).compLinearMap L.toLinearMap := by
    apply complexify_injective
    rw [complexify_algebraicRealProjector, complexify_compLinearMap,
      ppProjector_compLinearMap _ L.toLinearMap hL, complexify_compLinearMap,
      complexify_algebraicRealProjector]
  have hreindex : (A.compContinuousLinearMap L).toAlternatingMap.domDomCongr
      (finCongr (two_mul p)) =
      (A.toAlternatingMap.domDomCongr (finCongr (two_mul p))).compLinearMap L.toLinearMap := by
    ext v
    rfl
  ext v
  simpa [realProjector_apply, hreindex, AlternatingMap.compLinearMap_apply,
    AlternatingMap.domDomCongr_apply, ContinuousAlternatingMap.compContinuousLinearMap_apply,
    Function.comp_def] using congrArg (fun F => F (v ∘ (finCongr (two_mul p)).symm)) he

variable {n p : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

def smoothProjector (a : SmoothRealForm n M (2 * p)) : SmoothRealForm n M (2 * p) where
  coeff e z := realProjector (a.coeff e z)
  smooth e := (realProjectorCLM n p).contDiff.comp_contDiffOn (a.smooth e)
  compatible e f z hz v := by
    have he := coeff_eq_transition_pullback a e f z hz
    rw [he, realProjector_compContinuousLinearMap _ _
      (fun w => chartTransitionDerivative_complex_smul e f z hz Complex.I w)]
    rfl

theorem smoothProjector_coeff (a : SmoothRealForm n M (2 * p)) (e : ComplexChart n M)
    (z : ComplexModel n) : (smoothProjector a).coeff e z = realProjector (a.coeff e z) := rfl

theorem smoothProjector_isPure (a : SmoothRealForm n M (2 * p)) : IsPurePP (smoothProjector a) :=
  fun e z _ => realProjector_isPure (a.coeff e z)

private theorem smooth_eq_of_coeff_eq {a b : SmoothRealForm n M (2 * p)}
    (h : a.coeff = b.coeff) : a = b := by
  cases a
  cases b
  cases h
  rfl

theorem smoothProjector_idempotent (a : SmoothRealForm n M (2 * p)) :
    smoothProjector (smoothProjector a) = smoothProjector a := by
  apply smooth_eq_of_coeff_eq
  funext e z
  exact realProjector_idempotent (a.coeff e z)

theorem smoothProjector_geometricallyEq_of_isPure (a : SmoothRealForm n M (2 * p))
    (ha : IsPurePP a) : (smoothProjector a).GeometricallyEq a :=
  fun e z hz => realProjector_of_isPure _ (ha e z hz)

theorem smoothProjector_geometricallyEq {a b : SmoothRealForm n M (2 * p)}
    (h : a.GeometricallyEq b) : (smoothProjector a).GeometricallyEq (smoothProjector b) := by
  intro e z hz
  change realProjector (a.coeff e z) = realProjector (b.coeff e z)
  rw [h e hz]

variable {m : ℕ} {V : Type*} [TopologicalSpace V]
  [ChartedSpace (ComplexModel m) V] [IsComplexManifold m V]

theorem smoothProjector_pullback {f : V → M}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (a : SmoothRealForm n M (2 * p)) :
    (smoothProjector (SmoothRealForm.pullback hf a)).GeometricallyEq
      (SmoothRealForm.pullback hf (smoothProjector a)) := by
  intro e z hz
  let d := complexChartAt (n := n) (f (e.val.symm z))
  have hzd : z ∈ HolomorphicMaps.coordinateDomain f e d := ⟨hz, mem_complexChartAt_source _⟩
  change realProjector ((SmoothRealForm.pullback hf a).coeff e z) = _
  rw [SmoothRealForm.pullback_coeff hf a e d hzd,
    SmoothRealForm.pullback_coeff hf (smoothProjector a) e d hzd]
  exact realProjector_compContinuousLinearMap _ _
    (fun v => HolomorphicMaps.coordinateMap_fderiv_map_smul_complex hf e d hzd Complex.I v)

def geometricProjector : GeometricRealForm n M (2 * p) → GeometricRealForm n M (2 * p) :=
  Quotient.map smoothProjector (fun _ _ h => smoothProjector_geometricallyEq h)

theorem geometricProjector_ofRepresentative (a : SmoothRealForm n M (2 * p)) :
    geometricProjector (GeometricRealForm.ofRepresentative a) =
      GeometricRealForm.ofRepresentative (smoothProjector a) := rfl

theorem geometricProjector_isPure (a : GeometricRealForm n M (2 * p)) :
    geometricIsPurePP (geometricProjector a) := by
  refine Quotient.inductionOn a ?_
  intro b
  exact smoothProjector_isPure b

theorem geometricProjector_of_isPure (a : GeometricRealForm n M (2 * p))
    (ha : geometricIsPurePP a) : geometricProjector a = a := by
  refine Quotient.inductionOn a ?_ ha
  intro b hb
  apply Quotient.sound
  exact smoothProjector_geometricallyEq_of_isPure b hb

theorem geometricProjector_idempotent (a : GeometricRealForm n M (2 * p)) :
    geometricProjector (geometricProjector a) = geometricProjector a :=
  geometricProjector_of_isPure _ (geometricProjector_isPure a)

theorem geometricProjector_pullback {f : V → M}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (a : GeometricRealForm n M (2 * p)) :
    geometricProjector (geometricPullback hf a) = geometricPullback hf (geometricProjector a) := by
  refine Quotient.inductionOn a ?_
  intro b
  exact Quotient.sound (smoothProjector_pullback hf b)

end SGPT.Foundations.Analysis.Pending.NaturalSmoothPPProjector
