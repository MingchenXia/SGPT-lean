import SGPT.Projective.AlgebraicNativeRegularCut

/-! A FIXED original algebraic section produces its actual literal native
positive-power section; no analytic section/readback equality is input.
Blueprint: algebraic-native-section-forward.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI

open Set Filter Bundle CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open scoped Topology Manifold ContDiff TensorProduct
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves SGPT.Foundations.Analysis.Pending
open SGPT.Okounkov SGPT.NAPotential.GAGAMult SGPT.NAPotential.Berkovich
open SGPT.GAGA.H0L
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.QuantizationDraft
open SGPT.Bergman.CompactHolomorphicSectionsDraft HermitianHolomorphicLineBundle
open SGPT.BDivisor.NSKodaira

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  (E : ClosedProjectiveEmbedding f) [SmoothOfRelativeDimension n f]
  [IsSeparated f] [QuasiCompact f]
  {L : X.Modules} (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f n E L)

local instance forwardPointTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance forwardPointCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance forwardPointManifold : IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n

/-- Actual ORIGINAL algebraic coefficient, realized as its original regular function. -/
def algebraicPowerCoefficient (k : ℕ) (σ : bundlePowerGlobalSections L (k + 1))
    (i : a.I) (p : SchemeComplexPoint f) : ℂ :=
  schemeOpenRegularFunction f n E (a.opens i) (algCoef (a.frame i) (k + 1) σ) p

/-- The original algebraic power coefficients have exactly their original
transition, before any native section is manufactured. -/
theorem algebraicPowerCoefficient_transition (k : ℕ) (σ : bundlePowerGlobalSections L (k + 1))
    (i j : a.I) {p : SchemeComplexPoint f}
    (hi : schemeComplexPointImage f p ∈ a.opens i) (hj : schemeComplexPointImage f p ∈ a.opens j) :
    algebraicPowerCoefficient f n E a k σ j p =
      schemeFrameTransition f n E (a.frame i) (a.frame j) p ^ (k + 1) *
        algebraicPowerCoefficient f n E a k σ i p := by
  let U : X.Opens := a.opens i ⊓ a.opens j
  let l : U ⟶ a.opens i := homOfLE inf_le_left
  let r : U ⟶ a.opens j := homOfLE inf_le_right
  have hpU : schemeComplexPointImage f p ∈ U := ⟨hi, hj⟩
  have h := LocalBundleFrame.global_coefficients_transition (a.frame i) (a.frame j) l r (k + 1) σ
  have he := congrArg (fun c : Γ(X, U) => schemeOpenRegularFunction f n E U c p) h
  let tr : Γ(X, U) := (localBundleFrameTransition (a.frame i) (a.frame j) l r).val
  change schemeOpenRegularFunction f n E U (X.presheaf.map r.op (algCoef (a.frame j) (k + 1) σ)) p =
    schemeOpenRegularFunction f n E U
      (tr ^ (k + 1) *
        X.presheaf.map l.op (algCoef (a.frame i) (k + 1) σ)) p at he
  rw [schemeOpenRegularFunction_mul' f E n U _ _ hpU,
    schemeOpenRegularFunction_pow' f E n U _ _ hpU,
    schemeOpenRegularFunction_restrict f n E U (a.opens j) inf_le_right _ hpU,
    schemeOpenRegularFunction_restrict f n E U (a.opens i) inf_le_left _ hpU] at he
  exact he

private def nativePowerIndex (p : SchemeComplexPoint f) : a.I :=
  Classical.choose (a.covers (schemeComplexPointImage f p))

omit [IsSeparated f] [QuasiCompact f] in
private theorem nativePowerIndex_mem (p : SchemeComplexPoint f) :
    schemeComplexPointImage f p ∈ a.opens (nativePowerIndex f a p) :=
  Classical.choose_spec (a.covers (schemeComplexPointImage f p))

private def nativeAlgebraicPowerValue (k : ℕ) (σ : bundlePowerGlobalSections L (k + 1))
    (p : SchemeComplexPoint f) :
    (positivePower (schemeHermitianLineBundle f n E a H) k).Fiber p :=
  (positivePowerAtlasFrame (schemeHermitianAtlasFrame f n E a H
    (a.frame (nativePowerIndex f a p))) k).val.symm p
      (algebraicPowerCoefficient f n E a k σ (nativePowerIndex f a p) p)

private theorem nativeAlgebraicPowerValue_frame (k : ℕ) (σ : bundlePowerGlobalSections L (k + 1))
    (i : a.I) {p : SchemeComplexPoint f} (hi : schemeComplexPointImage f p ∈ a.opens i) :
    ((positivePowerAtlasFrame (schemeHermitianAtlasFrame f n E a H (a.frame i)) k).val
      ⟨p, nativeAlgebraicPowerValue f n E a H k σ p⟩).2 =
        algebraicPowerCoefficient f n E a k σ i p := by
  let j := nativePowerIndex f a p
  let e := schemeHermitianAtlasFrame f n E a H (a.frame j)
  let e' := schemeHermitianAtlasFrame f n E a H (a.frame i)
  let q := positivePowerAtlasFrame e k
  let q' := positivePowerAtlasFrame e' k
  have hj : schemeComplexPointImage f p ∈ a.opens j := nativePowerIndex_mem f a p
  have hq : p ∈ q.val.baseSet := mem_positivePowerAtlasFrame_baseSet _ hj k
  have hq' : p ∈ q'.val.baseSet := mem_positivePowerAtlasFrame_baseSet _ hi k
  change (q'.val ⟨p, q.val.symm p (algebraicPowerCoefficient f n E a k σ j p)⟩).2 = _
  rw [← Trivialization.coordChangeL_apply (R := ℂ) q.val q'.val ⟨hq, hq'⟩]
  have hlin : (q.val.coordChangeL ℂ q'.val p) (algebraicPowerCoefficient f n E a k σ j p) =
      algebraicPowerCoefficient f n E a k σ j p * (q.val.coordChangeL ℂ q'.val p) 1 := by
    rw [← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one]
  rw [hlin]
  change _ * ((positivePowerAtlasFrame e k).val.coordChangeL ℂ
    (positivePowerAtlasFrame e' k).val p) 1 = _
  rw [positivePower_frame_transition e e' hj hi k,
    SGPT.GAGA.H0L.coordChangeL_schemeHermitianAtlasFrame' a H (a.frame j) (a.frame i) hj hi]
  exact (mul_comm _ _).trans (algebraicPowerCoefficient_transition f n E a k σ j i hj hi).symm

/-- A FIXED original algebraic section manufactures its literal native
positive-power section. Exact readback is a theorem, not an input. -/
def nativeSectionOfAlgebraicPositivePower (k : ℕ) (σ : bundlePowerGlobalSections L (k + 1)) :
    HolomorphicSections (n := n) (positivePower (schemeHermitianLineBundle f n E a H) k).Fiber where
  toFun := nativeAlgebraicPowerValue f n E a H k σ
  contMDiff_toFun := by
    intro p
    let i := nativePowerIndex f a p
    let e := positivePowerAtlasFrame (schemeHermitianAtlasFrame f n E a H (a.frame i)) k
    have hi : schemeComplexPointImage f p ∈ a.opens i := nativePowerIndex_mem f a p
    have he : p ∈ e.val.baseSet := mem_positivePowerAtlasFrame_baseSet _ hi k
    apply (e.val.contMDiffAt_section_iff he).mpr
    have hhol := schemeOpenRegularFunction_holomorphicAt f n E (a.opens i)
      (algCoef (a.frame i) (k + 1) σ) p hi
    have hsm := contMDiffAt_of_eventually_mdifferentiableAt hhol
    apply hsm.congr_of_eventuallyEq
    have hO : IsOpen (schemeComplexPointImage f ⁻¹' (a.opens i : Set X)) :=
      (a.opens i).isOpen.preimage (schemeComplexPointImage_continuous f)
    filter_upwards [hO.mem_nhds hi] with y hy
    exact nativeAlgebraicPowerValue_frame f n E a H k σ i hy

/-- EXACT physical coefficient of the manufactured section in EVERY
original algebraic positive-power frame. -/
theorem nativeSectionOfAlgebraicPositivePower_frame (k : ℕ) (σ : bundlePowerGlobalSections L (k + 1))
    (i : a.I) {p : SchemeComplexPoint f} (hi : schemeComplexPointImage f p ∈ a.opens i) :
    sectionCoefficient (positivePower (schemeHermitianLineBundle f n E a H) k).Fiber
      (positivePowerAtlasFrame (schemeHermitianAtlasFrame f n E a H (a.frame i)) k).val
        (nativeSectionOfAlgebraicPositivePower f n E a H k σ) p =
          algebraicPowerCoefficient f n E a k σ i p :=
  nativeAlgebraicPowerValue_frame f n E a H k σ i hi

end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
