import SGPT.Projective.OkounkovOriginalUnitPowers
import SGPT.Projective.OkounkovOriginalIdealProducts
import SGPT.Okounkov.ValGen2Atlas

/-! Actual original tensor multiplier products and SAME raw value inclusions from genuine ample unit factors.
Blueprint: okounkov-original-tensor-multiplier.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Okounkov.OriginalTensorMultiplier
open Set Filter CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open MultiplierIdealProductComparison
open SGPT.Okounkov.AlgebraicValuation SGPT.Okounkov.ValGen2
open SGPT.AlmostSemigroup
open scoped Topology
variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
    [SmoothOfRelativeDimension n f] (E : ClosedProjectiveEmbedding f) [IsSeparated f] [QuasiCompact f]
local instance tensorMultiplierTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance tensorMultiplierCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance tensorMultiplierManifold : IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n

/-- The literal genuine original tensor-power product preserves the SAME multiplier ideal in EVERY target frame. -/
theorem isIdealSection_tensorPowerSectionProduct {L N : X.Modules}
    (a : LineBundleAtlas L) (b : LineBundleAtlas N) (φ : SchemeComplexPoint f → EReal) (k : ℕ)
    (s : bundlePowerGlobalSections L k)
    (hs : IsIdealSection f n E (multiplierIdeal (n:=n) (k:ℝ) φ) k s)
    (t : bundlePowerGlobalSections N k) :
    IsIdealSection f n E (multiplierIdeal (n:=n) (k:ℝ) φ) k (tensorPowerSectionProduct a b k s t) := by
  refine isIdealSection_of_atlas f n E (isGermLocalIdeal_multiplierIdeal _ _) (pairwiseTensorAtlas a b)
    fun ij p hp => ?_
  have hmem := hs _ (leftRestrictedFrame a b ij) p hp
  have ht : HolomorphicAt n (sectionFrameCoefficient f n E (rightRestrictedFrame a b ij) k t) p :=
    schemeOpenRegularFunction_holomorphicAt f n E _ _ p hp
  apply mem_multiplierIdeal_congr (mem_multiplierIdeal_holomorphic_mul ht hmem)
  have hO : IsOpen (schemeComplexPointImage f ⁻¹' (((pairwiseTensorAtlas a b).opens ij : X.Opens) : Set X)) :=
    ((pairwiseTensorAtlas a b).opens ij).isOpen.preimage (schemeComplexPointImage_continuous f)
  filter_upwards [hO.mem_nhds hp] with y hy
  exact (mul_comm _ _).trans (sectionFrameCoefficient_tensorPowerSectionProduct f n E a b k ij s t hy).symm

/-- Actual original unit factors preserve the ENTIRE literal original multiplier carrier, SAME value and degree. -/
theorem multiplierSectionSet_subset_tensor_of_units {L N : X.Modules}
    (a : LineBundleAtlas L) (b : LineBundleAtlas N) (d : LineBundleAtlas (bundleTensor L N))
    (v : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ)))) {c : X} (hc : IsNonnegAt v c)
    (t : ∀ k : ℕ, bundlePowerGlobalSections N k)
    (ht : ∀ k, c∉(sectionZeroIdealSheaf (b.tensorPower k) (t k)).support)
    (φ : SchemeComplexPoint f → EReal) :
    AlgebraicValuation.multiplierSectionSet f n E v c a φ ⊆
      AlgebraicValuation.multiplierSectionSet f n E v c d φ := by
  rintro z ⟨k,s,hs,hI,hz⟩
  have hzero : sectionValue v c b k (t k)=0 :=
    (sectionValue_eq_plainSectionValue (a:=b) (v:=v) hc k (t k)).trans
      (OriginalUnits.plainSectionValue_eq_zero_of_not_mem_zeroSupport v (b.tensorPower k) (t k) c hc (ht k))
  have hvalue := sectionValue_tensorPowerSectionProduct hc a b d k s (t k)
  rw [hzero,add_zero] at hvalue
  have hprod : tensorPowerSectionProduct a b k s (t k)≠0 := by
    intro h0
    have htop := (sectionValue_eq_top_iff (v:=v) c d k _).mpr h0
    exact ((sectionValue_eq_top_iff (v:=v) c a k s).not.mpr hs) (hvalue.symm.trans htop)
  have hideal : IsMultiplierSection f n E φ k (tensorPowerSectionProduct a b k s (t k)) := by
    rcases hI with hk | hI
    · exact Or.inl hk
    · exact Or.inr (isIdealSection_tensorPowerSectionProduct f n E a b φ k s hI (t k))
  have hvec : sectionVector v c d k (tensorPowerSectionProduct a b k s (t k)) hprod=sectionVector v c a k s hs := by
    rw [sectionValue_eq_vector c d k _ hprod,sectionValue_eq_vector c a k s hs] at hvalue
    exact toLex.injective (WithTop.coe_injective hvalue)
  refine ⟨k,tensorPowerSectionProduct a b k s (t k),hprod,hideal,?_⟩
  rw [hvec]
  exact hz

/-- ONE actual ample power BEFORE ALL lines/weights/valuations gives literal SAME raw multiplier inclusions. -/
theorem exists_ample_multiple_multiplier_inclusions {A : X.Modules}
    (aA : LineBundleAtlas A) (P : SGPT.LineBundle.AmplePolarization f A) :
    ∃ d : ℕ, 0<d ∧ ∀ m : ℕ, ∀ {L : X.Modules} (a : LineBundleAtlas L)
      (b : LineBundleAtlas (bundleTensor L (bundleTensorPower A (d*m))))
      (v : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ)))) (c : X) (_hc : IsNonnegAt v c)
      (φ : SchemeComplexPoint f → EReal),
      AlgebraicValuation.multiplierSectionSet f n E v c a φ ⊆
        AlgebraicValuation.multiplierSectionSet f n E v c b φ := by
  obtain ⟨d,hd,hunit⟩ := OriginalUnitPowers.exists_fixed_ample_power_units_all_multiples f aA P
  refine ⟨d,hd,?_⟩
  intro m L a b v c hc φ
  obtain ⟨s,hs⟩ := hunit c m
  let N := bundleTensorPower A (d*m)
  let aN := aA.tensorPower (d*m)
  exact multiplierSectionSet_subset_tensor_of_units f n E a aN b v hc
    (bundleGlobalSectionTensorPower N s)
    (fun k => OriginalUnitPowers.not_mem_zeroSupport_tensorPower aN s c (hs aN) k) φ
end SGPT.Okounkov.OriginalTensorMultiplier
