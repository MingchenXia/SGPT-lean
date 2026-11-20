import SGPT.PSH.AtlasLogComponentCartier
import SGPT.PSH.LocalRationalDivisorGrouping

/-! The original finite logarithmic tuple produces a genuine component
Cartier divisor/product, its full coefficients and every full generator. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas.SourceLogTransportDraft
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending
open scoped Topology Manifold ContDiff Classical
universe u

private theorem nativeCartierCoefficientAny_sum {n : ℕ} {M ι : Type*}
    [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    (s : Finset ι) (H : ι → EffectiveDivisor n M) (b : ι → ℕ)
    (Q : GeometricPrimeCarrier n M) :
    nativeCartierCoefficientAny (∑ i∈s,b i • H i) Q=
      ∑ i∈s,b i*nativeCartierCoefficientAny (H i) Q := by
  cases n with
  | zero => exact isEmptyElim Q
  | succ m => exact cartierGeometricPrimeCoefficient_finset_sum s H b Q

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
  {A : VariableComplexAtlas X}

/-- ORIGINAL finite equations, ALL original divisor coefficients and actual
whole-open logarithms internally produce an actual native Cartier divisor,
its actual holomorphic generator and SAME bounded-remainder equation.
There is no supplied native logarithmic or coefficient certificate. -/
theorem original_finite_logs_component_integral
    (D : AtlasEffectiveGeometricQDivisor A) (u : X → EReal) {r : ℕ}
    (W : Fin r → AtlasGeometricPrimeCarrier A) (w : Fin r → ℚ)
    (hw : ∀ i,0<w i) (p : Fin r → X → ℂ)
    (hp : ∀ i,A.ChartHolomorphicOn (p i) univ)
    (hgen : ∀ i y g,(atlasVanishingIdeal A (W i).val).mem y g ↔
      A.AtlasIsInSpanAt (· = p i) y g)
    (hcoeff : ∀ P : AtlasGeometricPrimeCarrier A,
      D.coefficient P=∑ i,if W i=P then w i else 0)
    (R : X → ℝ)
    (hlog : ∀ y,u y=(∑ i,((w i : ℝ) : EReal)*logNormSq (p i y))+(R y : EReal))
    (x : X) :
    letI := A.componentChartedSpace x
    letI := A.componentComplexManifold_of_paracompact x
    ∃ (d : ℕ) (H : EffectiveDivisor (A.pointDimension x) (A.componentOpen x))
      (G : A.componentOpen x → ℂ),0<d ∧
      (∀ Q : GeometricPrimeCarrier (A.pointDimension x) (A.componentOpen x),
        (D.nativeComponent x).coefficient Q=(nativeCartierCoefficientAny H Q : ℚ)/(d : ℚ)) ∧
      (∀ q,HolomorphicAt (A.pointDimension x) G q ∧ ∀ g,
        H.ideal.mem q g ↔ IsInSpanAt (n := A.pointDimension x) (· = G) q g) ∧
      ∀ q : A.componentOpen x,u q.val=
        (((1/(d : ℚ) : ℚ) : ℝ) : EReal)*logNormSq (G q)+(R q.val : EReal) := by
  classical
  let := A.componentChartedSpace x
  let := A.componentComplexManifold_of_paracompact x
  obtain ⟨d,b,hd,hb,hgroup⟩ := exists_finite_rational_logarithmic_product_grouping
    (Finset.univ : Finset (Fin r)) w (fun i _ => hw i)
  let F : Fin r → EffectiveDivisor (A.pointDimension x) (A.componentOpen x) :=
    fun i => componentPrimeCartier (W i) x
  let g : Fin r → A.componentOpen x → ℂ := fun i => p i ∘ Subtype.val
  let H := ∑ i,b i • F i
  let G : A.componentOpen x → ℂ := fun q => ∏ i,g i q^b i
  have hg (i : Fin r) (q : A.componentOpen x) : HolomorphicAt (A.pointDimension x) (g i) q :=
    original_holomorphic_component (p i) (hp i) x q
  have hG (q : A.componentOpen x) : HolomorphicAt (A.pointDimension x) G q := by
    exact MonomialPart.holomorphicAt_finset_prod Finset.univ
      (fun i _ => CompanionReduction.holomorphicAt_pow_of (hg i q) (b i))
  have hHgen (q : A.componentOpen x) (f : A.componentOpen x → ℂ) :
      H.ideal.mem q f ↔ IsInSpanAt (n := A.pointDimension x) (· = G) q f := by
    exact finite_cartier_sum_generator_product Finset.univ F b g q
      (fun i _ => hg i q)
      (fun i _ f => original_equation_component_cartier (W i) (p i) (hgen i) x q f) f
  refine ⟨d,H,G,hd,?_,(fun q => ⟨hG q,hHgen q⟩),?_⟩
  · intro Q
    rw [AtlasEffectiveGeometricQDivisor.nativeComponent_coefficient,hcoeff]
    change (∑ i,if W i=A.nativePrimeOriginalCarrier x Q then w i else 0)=
      (nativeCartierCoefficientAny (∑ i,b i • F i) Q : ℚ)/(d : ℚ)
    rw [nativeCartierCoefficientAny_sum,Nat.cast_sum,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    rw [Nat.cast_mul,componentPrimeCartier_coefficient]
    by_cases hi : W i=A.nativePrimeOriginalCarrier x Q
    · rw [if_pos hi,if_pos hi.symm]
      simp only [Nat.cast_one,mul_one]
      exact (hb i (Finset.mem_univ _)).2
    · rw [if_neg hi,if_neg (Ne.symm hi)]
      simp only [Nat.cast_zero,mul_zero,zero_div]
  · intro q
    have hgroupq : (∑ i,((w i : ℝ) : EReal)*logNormSq (p i q.val))=
        (((1/(d : ℚ) : ℚ) : ℝ) : EReal)*logNormSq (G q) := by
      simpa [Finset.sum_coe_sort,Finset.prod_coe_sort,G,g] using hgroup (fun i => p i q.val)
    exact (hlog q.val).trans (congrArg (fun t => t+(R q.val : EReal)) hgroupq)

end SGPT.PSH.VariableComplexAtlas.SourceLogTransportDraft
