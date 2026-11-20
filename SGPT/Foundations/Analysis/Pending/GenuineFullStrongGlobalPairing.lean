import SGPT.Foundations.Analysis.Pending.GenuineSingularDdcFunctional
import SGPT.Foundations.Analysis.Pending.FullLocalSmoothCurrentDensity
import SGPT.Foundations.Analysis.Pending.SmoothTopFormChartIntegration
import SGPT.Foundations.Analysis.Pending.ScalarAdjointDomainCongruence
import SGPT.Foundations.Analysis.Pending.NaturalThetaPshFullCurrentTests

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff

namespace SGPT.Foundations.Analysis.Pending.GenuineFullStrongGlobalPairing

open FirstPass FirstPass.PositiveClasses StronglyPositiveForms ProductTestForms
  ChartPartition XiaoGauduchonKernel XiaoComplexDifferential
  GenuineSingularDdcFunctional FullLocalSmoothCurrentDensity SmoothTopFormChartIntegration
  ScalarAdjointDomainCongruence NaturalThetaPshFullCurrentTests
  CompactVariableCurrentTests ScalarFullTestTranspose SingularTopFormLocalization
  LocalCurrentLebesgue LocalProductCurrents LocalBedfordTaylorProducts LocalBedfordTaylorSmooth
  XiaoPositiveGauduchonExtension

attribute [local instance] LocalCurrentLebesgue.addCommGroupFormSpan

/-- The full actual second differential preserves finite sums on every chart target. -/
theorem ddc_finset_sum_geometricallyEq {n k : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] {ι : Type*}
    (s : Finset ι) (A : ι → SmoothRealForm n M k) :
    (ddc (∑ i ∈ s, A i)).GeometricallyEq (∑ i ∈ s, ddc (A i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using
      (ddc_zero_geometricallyEq (n := n) (M := M) (k := k))
  | @insert i s hi ih =>
    intro e z hz
    simp only [Finset.sum_insert hi]
    rw [ddc_add_geometricallyEq (A i) (∑ j ∈ s, A j) e hz]
    simp only [coeff_add, ih e hz]

/-- The original genuine potential produces the inequality on every full strong smooth test. -/
theorem exists_genuine_full_strong_global_pairing {m : ℕ} {M : Type*}
    [TopologicalSpace M] [ChartedSpace (ComplexModel (m + 1)) M]
    [IsComplexManifold (m + 1) M] [CompactSpace M]
    [MeasurableSpace M] [BorelSpace M]
    (w : KahlerBackground (m + 1) M) (θ : SmoothRealForm (m + 1) M 2)
    (u : M → EReal) (hu : IsThetaPshPotential θ u) :
    ∃ L : SmoothRealForm (m + 1) M (2 * (m + 1)) →ₗ[ℝ] ℝ,
      (∀ Φ, Φ.GeometricallyEq 0 → L Φ = 0) ∧
      ∀ G : SmoothRealForm (m + 1) M (2 * m),
        (∀ e z, z ∈ e.val.target → G.coeff e z ∈ spCone m) →
          0 ≤ smoothPairing w θ G + L (ddc G) := by
  classical
  obtain ⟨L, hzero, hloc⟩ := exists_genuine_singular_ddc_functional θ u hu
  let e (x : M) := complexChartAt (n := m + 1) x
  choose W hW ρ hpot hxW hineq using fun x : M =>
    exists_full_compact_test_integral_nonnegative θ u hu (e x) ((e x).val x)
      ((e x).val.map_source (mem_complexChartAt_source x))
  let S (x : M) : Opens M :=
    ⟨(e x).val.source ∩ (e x).val ⁻¹' (W x : Set (ComplexModel (m + 1))),
      (e x).val.isOpen_inter_preimage (W x).isOpen⟩
  have hcover : ∀ x : M, ∃ y, x ∈ S y := fun x =>
    ⟨x, mem_complexChartAt_source x, hxW x⟩
  obtain ⟨N, χ, idx, hχ, hnonneg, hsupport, hcompact, hsumχ⟩ :=
    exists_chartSmooth_partitionOfUnity (n := m + 1) S hcover
  have hs (i : Fin N) : tsupport (χ i) ⊆ (e (idx i)).val.source :=
    fun x hx => (hsupport i hx).1
  have hU (i : Fin N) : (e (idx i)).val '' tsupport (χ i) ⊆ W (idx i) := by
    rintro _ ⟨x, hx, rfl⟩
    exact (hsupport i hx).2
  refine ⟨L, hzero, ?_⟩
  intro G hG
  have hspan (i : Fin N) : ∀ z ∈ (e (idx i)).val.target,
      G.coeff (e (idx i)) z ∈ formSpan (m + 1) m :=
    fun z hz => mem_formSpan_of_mem_spCone (hG _ z hz)
  have hpiece (i : Fin N) :
      0 ≤ smoothPairing w θ (smulFun (χ i) (hχ i) G) +
        L (ddc (smulFun (χ i) (hχ i) G)) := by
    let α := chartTest (e (idx i)) (χ i) (hχ i) G (hcompact i) (hs i) (hU i)
    have hα : ∀ z, α z ∈ spCone m :=
      chartTest_mem_spCone _ _ _ _ _ _ _ (hnonneg i) (hG (e (idx i)))
    have hp := hineq (idx i) α hα
    have hwhole : (∫ z in (W (idx i) : Set (ComplexModel (m + 1))),
        scalarAdjointTest α z * (chartFunction u (e (idx i)) z).toReal) =
        ∫ z, scalarAdjointTest α z * (chartFunction u (e (idx i)) z).toReal := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro z hz
      rw [image_eq_zero_of_notMem_tsupport
        (fun h => hz ((scalarAdjointTest α).tsupport_subset h)), zero_mul]
    rw [hwhole] at hp
    have hadjoint := scalarAdjoint_chartTest_eq_localizedTensorTest
      (e (idx i)) (χ i) (hχ i) G (hcompact i) (hs i) (hU i)
    change (scalarAdjointTest α : ComplexModel (m + 1) → ℝ) = _ at hadjoint
    simp_rw [congrFun hadjoint] at hp
    rw [← hloc _ _ _ _ _ G (hspan i)] at hp
    have hcorrection := localPotential_full_chart_wedge_correction
      θ (e (idx i)) (ρ (idx i)) (hpot (idx i)) (χ i) (hχ i) G
      (hcompact i) (hs i) (hU i) (hspan i)
    change (∑ j, ddcWedge (oneCurrent (W (idx i))) (hpot (idx i)).2.2.1
      (formBasis (m + 1) m j) (coeffTest α j)) = _ at hcorrection
    rw [hcorrection, ← smoothPairing_smulFun_eq_localized_wedge_integral
      w (e (idx i)) (χ i) (hχ i) (hs i) θ G] at hp
    simpa only [add_comm] using hp
  have hcoeffsum (s : Finset (Fin N))
      (A : Fin N → SmoothRealForm (m + 1) M (2 * m))
      (f : ComplexChart (m + 1) M) (z : ComplexModel (m + 1)) :
      (∑ i ∈ s, A i).coeff f z = ∑ i ∈ s, (A i).coeff f z := by
    induction s using Finset.induction_on with
    | empty => simp only [Finset.sum_empty, coeff_zero]
    | @insert i s hi ih => simp only [Finset.sum_insert hi, coeff_add, ih]
  have hsum : (∑ i, smulFun (χ i) (hχ i) G) = G := by
    apply smoothRealForm_ext
    intro f z
    rw [hcoeffsum Finset.univ (fun i => smulFun (χ i) (hχ i) G) f z]
    simp only [smulFun_coeff]
    rw [← Finset.sum_smul, hsumχ, one_smul]
  have hddc : L (ddc G) = ∑ i, L (ddc (smulFun (χ i) (hχ i) G)) := by
    calc
      L (ddc G) = L (ddc (∑ i, smulFun (χ i) (hχ i) G)) := by rw [hsum]
      _ =
          L (∑ i, ddc (smulFun (χ i) (hχ i) G)) :=
        linearFunctional_congr_of_geometricallyEq L hzero
          (ddc_finset_sum_geometricallyEq Finset.univ _)
      _ = _ := map_sum L _ _
  have hp := Finset.sum_nonneg fun (i : Fin N) (_ : i ∈ Finset.univ) => hpiece i
  rw [Finset.sum_add_distrib, ← map_sum, hsum, ← hddc] at hp
  exact hp

/-- Full strongly positive Gauduchon forms pair nonnegatively with the genuine potential class. -/
theorem smoothPairing_nonnegative_of_genuine_full_gauduchon {m : ℕ} {M : Type*}
    [TopologicalSpace M] [ChartedSpace (ComplexModel (m + 1)) M]
    [IsComplexManifold (m + 1) M] [CompactSpace M]
    [MeasurableSpace M] [BorelSpace M]
    (w : KahlerBackground (m + 1) M) (θ : SmoothRealForm (m + 1) M 2)
    (u : M → EReal) (hu : IsThetaPshPotential θ u)
    (G : SmoothRealForm (m + 1) M (2 * m))
    (hG : ∀ e z, z ∈ e.val.target → G.coeff e z ∈ spCone m)
    (hddc : (ddc G).GeometricallyEq 0) : 0 ≤ smoothPairing w θ G := by
  obtain ⟨L, hzero, hpairing⟩ := exists_genuine_full_strong_global_pairing w θ u hu
  simpa only [hzero (ddc G) hddc, add_zero] using hpairing G hG

end SGPT.Foundations.Analysis.Pending.GenuineFullStrongGlobalPairing
