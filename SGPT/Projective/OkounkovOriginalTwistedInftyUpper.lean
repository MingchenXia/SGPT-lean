import SGPT.Projective.OkounkovOriginalIdealProducts
import SGPT.Projective.OkounkovOriginalBookVolume
import SGPT.Okounkov.TranscendentalCoreAlgebra

/-! Genuine original fixed translated infinity-semigroup upper bounds for ACTUAL twisted multiplier values.
Blueprint: okounkov-original-twisted-infty-upper.tex. No resolution or desired geometric certificate input. -/
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Okounkov.OriginalTwistedInftyUpper
open Set Filter CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.QuasiEquisingularApproximation
open SGPT.Okounkov.AlgebraicValuation SGPT.Okounkov.ValGen2 SGPT.AlmostSemigroup
open scoped Topology
variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ))
  {m : ℕ} [SmoothOfRelativeDimension (m+1) f] (E : ClosedProjectiveEmbedding f)
  [IsSeparated f] [QuasiCompact f] {L T : X.Modules} (a : LineBundleAtlas L) (aT : LineBundleAtlas T)
local instance twistedInftyUpperTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance twistedInftyUpperCharts : ChartedSpace (ComplexModel (m+1)) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f (m+1)
local instance twistedInftyUpperManifold : IsComplexManifold (m+1) (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f (m+1)

/-- Actual original upper product preserves the SAME k-weight multiplier ideal in EVERY target power frame. -/
theorem upperProduct_isIdealSection (φ : SchemeComplexPoint f → EReal) (k j : ℕ)
    (s : Γ(bundleTensor T (bundleTensorPower L k),⊤))
    (hs : IsPlainIdealSection f (m+1) E (multiplierIdeal (n:=m+1) (k:ℝ) φ) s)
    (t : Γ(bundleTensor (bundleDual T) (bundleTensorPower L j),⊤)) :
    IsIdealSection f (m+1) E (multiplierIdeal (n:=m+1) (k:ℝ) φ) (k+j) (upperProduct a aT k j s t) := by
  have hplain : IsPlainIdealSection f (m+1) E (multiplierIdeal (n:=m+1) (k:ℝ) φ)
      (upperProduct a aT k j s t) := by
    unfold upperProduct
    apply OriginalIdealProducts.coverProduct_isPlainMultiplierIdealSection f (m+1) E
    exact hs
  intro U e p hp
  exact hplain U (e.tensorPower (k+j)) p hp

variable (H : SchemeLineBundleMetric f (m+1) E L) {φ : SchemeComplexPoint f → EReal}
  (hφ : IsThetaPshPotential (H.curvature a).val φ)
  (hφan : HasManifoldAnalyticSingularityType (n:=m+1) φ)
  (q : ℚ) (hq0 : 0<q) (hq1 : q<1)

include H hφ hφan hq0 hq1

/-- Actual analytic ideal comparison upgrades the SAME genuine upper product, uniformly for ALL later sections. -/
theorem exists_eventual_upperProduct_isInftySection (j : ℕ)
    (t : Γ(bundleTensor (bundleDual T) (bundleTensorPower L j),⊤)) :
    ∃ k₀ : ℕ, 0<k₀ ∧ ∀ k : ℕ, k₀≤k →
      ∀ s : Γ(bundleTensor T (bundleTensorPower L k),⊤),
      IsPlainIdealSection f (m+1) E (multiplierIdeal (n:=m+1) (k:ℝ) φ) s →
        IsInftySection f (m+1) E (fun x => ((q:ℝ):EReal)*φ x) (k+j) (upperProduct a aT k j s t) := by
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  have hqR0 : (0:ℝ)<q := by exact_mod_cast hq0
  have hqR1 : (q:ℝ)<1 := by exact_mod_cast hq1
  have hqi : 1<(q:ℝ)⁻¹ := (one_lt_inv₀ hqR0).mpr hqR1
  let ψ : SchemeComplexPoint f → EReal := fun x => ((q:ℝ):EReal)*φ x
  have hψ := TranscendentalCore.isThetaPshPotential_nonneg_smul hφ hqR0.le
  have hψan := TranscendentalCore.hasManifoldAnalyticSingularityType_nonneg_rat_smul hφan hq0.le
  let ε : ℝ := ((q:ℝ)⁻¹-1)/2
  have hε : 0<ε := by dsimp only [ε]; linarith
  obtain ⟨b,hb,hI⟩ := ValGen.exists_mem_inftyIdeal_of_mem_multiplierIdeal
    hψ.1.quasiPlurisubharmonic hψan hε
  let B : ℕ := max b (⌈(j:ℝ)*(1+ε)/ε⌉₊+1)
  have hB : 0<B := lt_of_lt_of_le hb (le_max_left _ _)
  refine ⟨B,hB,?_⟩
  intro k hk s hs
  have hk0 : 0<k := lt_of_lt_of_le hB hk
  have hkb : b≤k+j := (le_max_left _ _).trans (hk.trans (Nat.le_add_right _ _))
  have hkceil : ⌈(j:ℝ)*(1+ε)/ε⌉₊≤k :=
    (Nat.le_succ _).trans ((le_max_right _ _).trans hk)
  have hbound : (j:ℝ)*(1+ε)/ε ≤ (k:ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hkceil)
  have hle : ((k+j:ℕ):ℝ)*(1+ε) ≤ (k:ℝ)*(q:ℝ)⁻¹ := by
    have h := (div_le_iff₀ hε).mp hbound
    have he : (q:ℝ)⁻¹=1+2*ε := by dsimp only [ε]; ring
    push_cast
    rw [he]
    nlinarith
  have hfun : (fun x => ((((q:ℝ)⁻¹:ℝ):EReal))*ψ x)=φ := by
    funext x
    dsimp only [ψ]
    rw [←mul_assoc,←EReal.coe_mul,inv_mul_cancel₀ hqR0.ne',EReal.coe_one,one_mul]
  have hprod := upperProduct_isIdealSection f E a aT φ k j s hs t
  intro U e p hp
  apply hI (k+j) hkb k (q:ℝ)⁻¹ hk0 (inv_pos.mpr hqR0) hle p
  exact (congrArg (fun χ : SchemeComplexPoint f → EReal =>
    (multiplierIdeal (n:=m+1) (k:ℝ) χ).mem p
      (sectionFrameCoefficient f (m+1) E e (k+j) (upperProduct a aT k j s t))) hfun).mpr
        (hprod U e p hp)

include aT in
/-- ONE ACTUAL original section/degree/translate sends ALL later raw twisted multiplier values into SAME scaled Γ∞. -/
theorem exists_fixed_translate_twistedMultiplierValues_infty [Nonempty (SchemeComplexPoint f)]
    (hbig : SGPT.LineBundle.IsBig f L (m+1))
    (v : AddValuation X.functionField (WithTop (Lex (Fin (m+1) → ℤ)))) {c : X} (hc : IsNonnegAt v c) :
    ∃ j : ℕ, ∃ w : Fin (m+1) → ℤ, ∃ k₀ : ℕ, 0<k₀ ∧ ∀ k : ℕ, k₀≤k →
      ∀ r : LineBundleAtlas (bundleTensor T (bundleTensorPower L k)),
      ∀ x∈AlgebraicValuation.twistedMultiplierValues f (m+1) E v c k r φ,
        (x+w,((k+j:ℕ):ℤ))∈ValGen.inftySemigroup f E a c v (fun y => ((q:ℝ):EReal)*φ y) := by
  obtain ⟨Y,hY⟩ := OriginalBook.exists_original_smoothFlag_allDimensions f (m+1) E
  obtain ⟨j,t,ht⟩ := (exists_twisted_section_ne_zero f E Y hY a hbig hbig.volume_pos (dualAtlas aT)).exists
  let rD := pairwiseTensorAtlas (dualAtlas aT) (a.tensorPower j)
  let w := plainSectionVector v c rD t ht
  obtain ⟨k₀,hk₀,hupper⟩ := exists_eventual_upperProduct_isInftySection f E a aT H hφ hφan q hq0 hq1 j t
  refine ⟨j,w,k₀,hk₀,?_⟩
  rintro k hk r x ⟨s,hs,hI,hx⟩
  have hk0 : k≠0 := Nat.ne_of_gt (lt_of_lt_of_le hk₀ hk)
  have hinf := hupper k hk s (hI.resolve_left hk0)
  obtain ⟨hprod,hvec⟩ := upperProduct_vector a aT v hc k j r rD hs ht
  refine ⟨k+j,upperProduct a aT k j s t,hprod,hinf,?_⟩
  exact Prod.ext ((congrArg (fun z => z+w) hx).trans hvec.symm) rfl

end SGPT.Okounkov.OriginalTwistedInftyUpper
