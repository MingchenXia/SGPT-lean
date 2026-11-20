import SGPT.Foundations.Analysis.Pending.FiniteGlobalCurrentSmoothLocalDensity
import SGPT.Foundations.Analysis.Pending.ActualLocallyIntegrableFormDensityUniqueness
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Topology.Compactness.LocallyFinite

set_option autoImplicit false

/-! Original LF distribution locality and complete smooth alternating density
on a whole open chart domain. ENTIRE BP proof precedes first baseline. -/
noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Distributions ContDiff Topology Manifold

namespace SGPT.Foundations.Analysis.Pending.LocalSmoothFormDensityGluing
open FirstPass _root_.SGPT.Foundations.Analysis.LocalCurrents LelongPoincareDivisor

variable {n : ℕ} {Ω : Opens (ComplexModel n)}

/-- Local equality on actual included tests implies full original distribution equality. -/
theorem eq_of_restrict_eq_locally (R S : 𝓓'(Ω, ℝ))
    (hloc : ∀ x ∈ Ω, ∃ (V : Opens (ComplexModel n)) (hV : V ≤ Ω),
      x ∈ V ∧ restrictDistribution R hV = restrictDistribution S hV) : R = S := by
  classical
  have hp : ∀ i : Ω, ∃ (V : Opens (ComplexModel n)) (hV : V ≤ Ω),
      (i : ComplexModel n) ∈ V ∧ restrictDistribution R hV = restrictDistribution S hV :=
    fun i => hloc i i.property
  choose V hV hxV heq using hp
  ext φ
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (I := 𝓘(ℝ, ComplexModel n)) φ.hasCompactSupport.isClosed
    (fun i : Ω => (V i : Set (ComplexModel n))) (fun i => (V i).isOpen) (by
      intro x hx
      exact mem_iUnion_of_mem ⟨x, φ.tsupport_subset hx⟩ (hxV _))
  have hfin := ρ.locallyFinite.finite_nonempty_inter_compact φ.hasCompactSupport
  let I := hfin.toFinset
  let ψ (i : Ω) : 𝓓(V i, ℝ) :=
    ⟨fun z => ρ i z * φ z, (ρ i).contMDiff.contDiff.mul φ.contDiff,
      φ.hasCompactSupport.mul_left, tsupport_mul_subset_left.trans (hρ i)⟩
  have hφ : (∑ i ∈ I, (TestFunction.monoCLM ℝ (ψ i) : 𝓓(Ω, ℝ))) = φ := by
    apply TestFunction.ext
    intro z
    simp only [_root_.sum_apply]
    simp_rw [congrFun (testFunction_inclusion_coe (hV _) (ψ _)) z]
    change (∑ i ∈ I, ρ i z * φ z) = φ z
    by_cases hz : z ∈ tsupport (φ : ComplexModel n → ℝ)
    · have hsupport : Function.support (fun i : Ω => ρ i z) ⊆ (I : Set Ω) := by
        intro i hi
        exact hfin.mem_toFinset.mpr ⟨z, hi, hz⟩
      have hsum : ∑ i ∈ I, ρ i z = 1 :=
        (finsum_eq_finsetSum_of_support_subset (fun i : Ω => ρ i z) hsupport).symm.trans
          (ρ.sum_eq_one hz)
      rw [← Finset.sum_mul, hsum, one_mul]
    · have hz0 : φ z = 0 := by
        by_contra hn
        exact hz (subset_tsupport φ hn)
      simp only [hz0, mul_zero, Finset.sum_const_zero]
  calc
    R φ = R (∑ i ∈ I, (TestFunction.monoCLM ℝ (ψ i) : 𝓓(Ω, ℝ))) := congrArg R hφ.symm
    _ = ∑ i ∈ I, restrictDistribution R (hV i) (ψ i) := by rw [map_sum]; rfl
    _ = ∑ i ∈ I, restrictDistribution S (hV i) (ψ i) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [heq i]
    _ = S (∑ i ∈ I, (TestFunction.monoCLM ℝ (ψ i) : 𝓓(Ω, ℝ))) := by rw [map_sum]; rfl
    _ = S φ := congrArg S hφ

/-- Haar-almost-everywhere equality is genuine pointwise equality for full continuous fields. -/
theorem eqOn_of_regularForm_eq {r : ℕ}
    (μ : Measure (ComplexModel n)) [μ.IsAddHaarMeasure]
    {a b : ComplexModel n → (ComplexModel n) [⋀^Fin r]→L[ℝ] ℝ}
    (ha : ContinuousOn a Ω) (hb : ContinuousOn b Ω)
    (hLa : LocallyIntegrableOn a Ω μ) (hLb : LocallyIntegrableOn b Ω μ)
    (heq : regularFormDistribution μ a hLa = regularFormDistribution μ b hLb) :
    EqOn a b Ω :=
  MeasureTheory.Measure.eqOn_open_of_ae_eq
    (ActualLocallyIntegrableFormDensityUniqueness.ae_eq_of_regularFormDistribution_eq
      μ hLa hLb heq) Ω.isOpen ha hb

private theorem restrictForm_trans {r : ℕ} {U V : Opens (ComplexModel n)}
    (hUV : U ≤ V) (hVΩ : V ≤ Ω) (A : DistributionForm Ω r) :
    restrictForm (restrictForm A hVΩ) hUV = restrictForm A (hUV.trans hVΩ) := by
  ext v φ
  change restrictDistribution (restrictDistribution (A v) hVΩ) hUV φ = _
  rw [restrictDistribution_trans]
  rfl

private theorem restrict_regularForm {r : ℕ} {V : Opens (ComplexModel n)}
    (μ : Measure (ComplexModel n)) {a : ComplexModel n → (ComplexModel n) [⋀^Fin r]→L[ℝ] ℝ}
    (ha : LocallyIntegrableOn a Ω μ) (hV : V ≤ Ω) :
    restrictForm (regularFormDistribution μ a ha) hV =
      regularFormDistribution μ a (ha.mono_set hV) := by
  ext v φ
  rw [restrictForm_apply, regularFormDistribution_apply, regularFormDistribution_apply]
  rw [testFunction_inclusion_coe hV φ]

private theorem regularForm_congr {r : ℕ} (μ : Measure (ComplexModel n))
    {a b : ComplexModel n → (ComplexModel n) [⋀^Fin r]→L[ℝ] ℝ}
    (ha : LocallyIntegrableOn a Ω μ) (hb : LocallyIntegrableOn b Ω μ)
    (heq : EqOn a b Ω) : regularFormDistribution μ a ha = regularFormDistribution μ b hb := by
  ext v φ
  rw [regularFormDistribution_apply, regularFormDistribution_apply]
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall fun z => by
    by_cases hz : z ∈ Ω
    · change φ z • a z = φ z • b z
      rw [heq hz]
    · have h0 : φ z = 0 := by
        by_contra hn
        exact hz (φ.tsupport_subset (subset_tsupport φ hn))
      simp only [h0, zero_smul]

/-- Actual local full smooth densities internally glue to one smooth density
and equality on EVERY original test on the whole open domain. -/
theorem exists_smooth_density {r : ℕ}
    (μ : Measure (ComplexModel n)) [μ.IsAddHaarMeasure] (A : DistributionForm Ω r)
    (hloc : ∀ x ∈ Ω, ∃ (V : Opens (ComplexModel n)) (hV : V ≤ Ω)
      (a : ComplexModel n → (ComplexModel n) [⋀^Fin r]→L[ℝ] ℝ),
      x ∈ V ∧ ContDiffOn ℝ ∞ a V ∧ ∃ hL : LocallyIntegrableOn a V μ,
        restrictForm A hV = regularFormDistribution μ a hL) :
    ∃ a : ComplexModel n → (ComplexModel n) [⋀^Fin r]→L[ℝ] ℝ,
      ContDiffOn ℝ ∞ a Ω ∧ ∃ hL : LocallyIntegrableOn a Ω μ,
        A = regularFormDistribution μ a hL := by
  classical
  have hp : ∀ i : Ω, ∃ (V : Opens (ComplexModel n)) (hV : V ≤ Ω)
      (a : ComplexModel n → (ComplexModel n) [⋀^Fin r]→L[ℝ] ℝ),
      (i : ComplexModel n) ∈ V ∧ ContDiffOn ℝ ∞ a V ∧
      ∃ hL : LocallyIntegrableOn a V μ, restrictForm A hV = regularFormDistribution μ a hL :=
    fun i => hloc i i.property
  choose V hV α hxV hα hLα hreg using hp
  let a : ComplexModel n → (ComplexModel n) [⋀^Fin r]→L[ℝ] ℝ :=
    fun z => if hz : z ∈ Ω then α ⟨z, hz⟩ z else 0
  have hagree (i : Ω) : EqOn a (α i) (V i) := by
    intro z hz
    have hzΩ := hV i hz
    let j : Ω := ⟨z, hzΩ⟩
    let U := V i ⊓ V j
    have hui : U ≤ V i := inf_le_left
    have huj : U ≤ V j := inf_le_right
    have hh : regularFormDistribution μ (α i) ((hLα i).mono_set hui) =
        regularFormDistribution μ (α j) ((hLα j).mono_set huj) := by
      rw [← restrict_regularForm μ (hLα i) hui, ← restrict_regularForm μ (hLα j) huj,
        ← hreg i, ← hreg j, restrictForm_trans, restrictForm_trans]
    have he := eqOn_of_regularForm_eq μ ((hα i).continuousOn.mono hui)
      ((hα j).continuousOn.mono huj) ((hLα i).mono_set hui) ((hLα j).mono_set huj) hh
    have hzU : z ∈ U := ⟨hz, hxV j⟩
    have ha : a z = α j z := by simp only [a, hzΩ, ↓reduceDIte]; rfl
    exact ha.trans (he hzU).symm
  have hsmooth : ContDiffOn ℝ ∞ a Ω := by
    apply contDiffOn_of_locally_contDiffOn
    intro x hx
    let i : Ω := ⟨x, hx⟩
    refine ⟨V i, (V i).isOpen, hxV i, ?_⟩
    apply ((hα i).mono (inter_subset_right)).congr
    intro z hz
    exact hagree i hz.2
  have hLa : LocallyIntegrableOn a Ω μ :=
    hsmooth.continuousOn.locallyIntegrableOn Ω.isOpen.measurableSet
  refine ⟨a, hsmooth, hLa, ?_⟩
  ext v : 1
  apply eq_of_restrict_eq_locally
  intro x hx
  let i : Ω := ⟨x, hx⟩
  refine ⟨V i, hV i, hxV i, ?_⟩
  change restrictForm A (hV i) v =
    restrictForm (regularFormDistribution μ a hLa) (hV i) v
  rw [hreg i, restrict_regularForm]
  exact congrArg (fun B : DistributionForm (V i) r => B v)
    (regularForm_congr μ (hLα i) (hLa.mono_set (hV i)) (hagree i).symm)

end SGPT.Foundations.Analysis.Pending.LocalSmoothFormDensityGluing
