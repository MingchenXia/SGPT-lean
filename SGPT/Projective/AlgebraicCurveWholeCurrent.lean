import SGPT.Projective.AlgebraicCurveZeroGeometry
import SGPT.Projective.NativeCurveWeightedPointMass
import SGPT.Bergman.SourceNativeTensorSmoothMetric

/-! The SAME actual structural algebraic zero-cycle degree is the SAME FULL
physical native curve divisor current mass, all actual zeros retained.
Blueprint: algebraic-curve-whole-current.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.AlgebraicCurveDegree
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set Filter Bundle
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Okounkov SGPT.NAPotential.GAGAMult SGPT.BDivisor.NSKodaira
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.QuantizationDraft
open SGPT.Bergman.CompactHolomorphicSectionsDraft SGPT.Bergman.PolynomialH0Growth
open SGPT.Bergman.NativeHermitianMetric HermitianHolomorphicLineBundle
open SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
open SGPT.Projective.NumEq.CompleteIntersections
open LelongPoincareDivisor CanonicalCurrentFrame ProductTestForms StronglyPositiveForms
open ActualCompactGlobalPairingCalibration
open _root_.SGPT.Foundations.Analysis.LocalCurrents
open scoped Topology Manifold BigOperators Distributions
variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ))
  (E : ClosedProjectiveEmbedding f) [SmoothOfRelativeDimension 1 f]
  [IsSeparated f] [QuasiCompact f]
  {L : X.Modules} (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f 1 E L)
local instance wholePointTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance wholePointCharts : ChartedSpace (ComplexModel 1) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f 1
local instance wholePointManifold : IsComplexManifold 1 (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f 1

namespace AlgebraicCurveZeroGeometry
variable {f E a H} {k : ℕ} {σ : bundlePowerGlobalSections L (k + 1)}
  (G : AlgebraicCurveZeroGeometry f E a H k σ)

omit [IsIntegral X] in
/-- SAME original smooth physical metric, with actual tensor smoothness internally proved. -/
theorem nativeSmooth : IsSourceSmoothHermitianMetric G.nativeBundle :=
  sourceNativePositivePower_smooth (schemeHermitianLineBundle f 1 E a H)
    (isSourceSmoothHermitianMetric_schemeHermitianLineBundle f 1 E a H) k

/-- Actual nonzero original section internally supplies dense nonzero native values. -/
theorem nativeDense (hσ : σ ≠ 0) :
    ∀ U : Set (SchemeComplexPoint f), IsOpen U → U.Nonempty → ∃ y ∈ U, G.nativeSection y ≠ 0 :=
  nativeSectionOfAlgebraicPositivePower_dense f 1 E a H k σ hσ

private theorem point_not_other_zero_domain (hσ : σ ≠ 0)
    (z w : sectionZeroSubscheme (a.tensorPower (k + 1)) σ) (hw : w ≠ z) :
    G.point w ∉ G.coverDomain hσ (.inl z) := by
  intro hO
  have hsz : G.nativeSection (G.point w) = 0 := by
    change G.point w ∈ {p | G.nativeSection p = 0}
    rw [← G.point_range]
    exact ⟨w, rfl⟩
  have hcoef : sectionCoefficient G.nativeBundle.Fiber (G.frame z).val G.nativeSection (G.point w) = 0 := by
    change (G.frame z).val.linearEquivAt ℂ (G.point w) hO.1 (G.nativeSection (G.point w)) = 0
    rw [hsz, map_zero]
  have hcg : (sectionCoefficient G.nativeBundle.Fiber (G.frame z).val G.nativeSection ∘
      (G.chart z).val.symm) ((G.chart z).val (G.point w)) = 0 := by
    simpa only [Function.comp_apply, (G.chart z).val.left_inv hO.2.1] using hcoef
  have hc := G.isolated z _ hO.2.2 hcg
  exact hw (G.point_injective ((G.chart z).val.injOn hO.2.1 (mem_complexChartAt_source _) hc))

private theorem weighted_forms_sum {M : Type} [TopologicalSpace M]
    [ChartedSpace (ComplexModel 1) M] [IsComplexManifold 1 M]
    {r q : ℕ} (χ : Fin r → M → ℝ) (hχ : ∀ i, ChartSmooth (n := 1) (χ i))
    (hsum : ∀ x, ∑ i, χ i x = 1) (γ : SmoothRealForm 1 M q) :
    (∑ i, smulFun (χ i) (hχ i) γ) = γ := by
  apply smoothRealForm_ext
  intro c z
  let ev : SmoothRealForm 1 M q →+ RealForm 1 q :=
    { toFun := fun F => F.coeff c z, map_zero' := rfl, map_add' := fun _ _ => rfl }
  rw [show (∑ i, smulFun (χ i) (hχ i) γ).coeff c z =
    ∑ i, (smulFun (χ i) (hχ i) γ).coeff c z from map_sum ev _ _]
  simp only [smulFun_coeff, ← Finset.sum_smul, hsum, one_smul]

/-- Entire SAME full native current mass is the genuine full original zero-stalk length sum. -/
theorem pairing_unit_eq_sum_lengths (hσ : σ ≠ 0)
    [Fintype (sectionZeroSubscheme (a.tensorPower (k + 1)) σ)] :
    let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    pairingLM (integrationCurrent (canonicalBasis 1) (Nat.succ_pos 0)
      (nativeSectionDivisorMetric G.nativeBundle G.nativeSmooth G.nativeSection (G.nativeDense hσ)))
      (curveCurrentComplement ▸ (unitForm : SmoothRealForm 1 (SchemeComplexPoint f) 0)) =
      ∑ z : sectionZeroSubscheme (a.tensorPower (k + 1)) σ,
        ((Module.length ((sectionZeroSubscheme (a.tensorPower (k + 1)) σ).presheaf.stalk z)
          ((sectionZeroSubscheme (a.tensorPower (k + 1)) σ).presheaf.stalk z)).toNat : ℝ) := by
  classical
  let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  let : ChartedSpace (ComplexModel (0 + 1)) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f (0 + 1)
  let : IsComplexManifold (0 + 1) (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f (0 + 1)
  dsimp only
  obtain ⟨r, χ, idx, hχ, _hχ0, hsupp, hc, hsum⟩ := G.exists_partition hσ
  let T := integrationCurrent (canonicalBasis 1) (Nat.succ_pos 0)
    (nativeSectionDivisorMetric G.nativeBundle G.nativeSmooth G.nativeSection (G.nativeDense hσ))
  let γ : SmoothRealForm 1 (SchemeComplexPoint f) (Module.finrank ℝ (ComplexModel 1) - 2) :=
    curveCurrentComplement ▸ unitForm
  let length (z : sectionZeroSubscheme (a.tensorPower (k + 1)) σ) : ℝ :=
    ((Module.length ((sectionZeroSubscheme (a.tensorPower (k + 1)) σ).presheaf.stalk z)
      ((sectionZeroSubscheme (a.tensorPower (k + 1)) σ).presheaf.stalk z)).toNat : ℝ)
  have hlen (z : sectionZeroSubscheme (a.tensorPower (k + 1)) σ) : length z = ((G.presentation z).m : ℝ) := by
    dsimp only [length]
    rw [G.length_eq z, ENat.toNat_natCast]
  have hterm (i : Fin r) : pairingLM T (smulFun (χ i) (hχ i) γ) =
      ∑ z : sectionZeroSubscheme (a.tensorPower (k + 1)) σ, length z * χ i (G.point z) := by
    cases hidx : idx i with
    | inl z =>
      have hdom : tsupport (χ i) ⊆ (G.coverDomain hσ (.inl z) : Set (SchemeComplexPoint f)) := by
        simpa only [hidx] using hsupp i
      have hmass := native_curve_weighted_pairing_point_mass G.nativeBundle G.nativeSmooth
        G.nativeSection (G.nativeDense hσ) (G.frame z) (G.chart z) (G.point z)
        ⟨mem_positivePowerAtlasFrame_baseSet _ (G.inFrame z) k, mem_complexChartAt_source _⟩
        (G.presentation z) (G.isolated z) (χ i) (hχ i) (hc i)
        (fun y hy => ⟨(hdom hy).1, (hdom hy).2.1⟩)
        (fun y hy => (hdom hy).2.2) unitForm
      change pairingLM T (smulFun (χ i) (hχ i) γ) = _ at hmass
      have hvalue : (unitForm : SmoothRealForm 1 (SchemeComplexPoint f) 0).coeff
          (G.chart z) ((G.chart z).val (G.point z)) ![] = 1 := rfl
      rw [hvalue, mul_one, ← hlen z] at hmass
      rw [hmass]
      symm
      apply Finset.sum_eq_single z
      · intro w _ hw
        have hnot : G.point w ∉ tsupport (χ i) :=
          fun h => G.point_not_other_zero_domain hσ z w hw (hdom h)
        rw [image_eq_zero_of_notMem_tsupport hnot, mul_zero]
      · intro hz
        exact False.elim (hz (Finset.mem_univ z))
    | inr x =>
      have hdom : tsupport (χ i) ⊆ (G.coverDomain hσ (.inr x) : Set (SchemeComplexPoint f)) := by
        simpa only [hidx] using hsupp i
      have hnonzero : ∀ y ∈ tsupport (χ i), G.nativeSection y ≠ 0 := by
        intro y hy hzero
        have hyr : y ∈ Set.range G.point := by rw [G.point_range]; exact hzero
        exact (hdom hy).2 hyr
      have hoff := nativeSection_weighted_pairing_eq_zero_of_nonzero G.nativeBundle G.nativeSmooth
        G.nativeSection (G.nativeDense hσ) (G.coverFrame (.inr x)) (G.coverChart (.inr x))
        (χ i) (hχ i) (hc i) (fun y hy => (hdom hy).1) hnonzero γ
      change pairingLM T (smulFun (χ i) (hχ i) γ) = 0 at hoff
      rw [hoff]
      symm
      apply Finset.sum_eq_zero
      intro z _
      have hnot : G.point z ∉ tsupport (χ i) := fun h => (hdom h).2 ⟨z, rfl⟩
      rw [image_eq_zero_of_notMem_tsupport hnot, mul_zero]
  have hforms := weighted_forms_sum χ hχ hsum γ
  calc
    _ = ∑ i : Fin r, pairingLM T (smulFun (χ i) (hχ i) γ) := by
      change pairingLM T γ = _
      calc
        pairingLM T γ = pairingLM T (∑ i : Fin r, smulFun (χ i) (hχ i) γ) :=
          congrArg (pairingLM T) hforms.symm
        _ = _ := by rw [map_sum]
    _ = ∑ i : Fin r, ∑ z : sectionZeroSubscheme (a.tensorPower (k + 1)) σ,
        length z * χ i (G.point z) := Finset.sum_congr rfl (fun i _ => hterm i)
    _ = ∑ z : sectionZeroSubscheme (a.tensorPower (k + 1)) σ, length z := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro z _
      rw [← Finset.mul_sum, hsum, mul_one]

end AlgebraicCurveZeroGeometry
/-- Independent ACTUAL structural algebraic degree of the SAME original section
is the FULL SAME physical native section divisor current mass. Every auxiliary
geometric, finiteness, multiplicity, current and metric datum is manufactured. -/
theorem sectionZeroCycleDegree_eq_fullCurrent
    (k : ℕ) (σ : bundlePowerGlobalSections L (k + 1)) (hσ : σ ≠ 0)
    (b : Spec (.of ℂ)) :
    let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    let B := positivePower (schemeHermitianLineBundle f 1 E a H) k
    let hB := sourceNativePositivePower_smooth (schemeHermitianLineBundle f 1 E a H)
      (isSourceSmoothHermitianMetric_schemeHermitianLineBundle f 1 E a H) k
    let s := nativeSectionOfAlgebraicPositivePower f 1 E a H k σ
    let hdense := nativeSectionOfAlgebraicPositivePower_dense f 1 E a H k σ hσ
    ((sectionZeroCycleDegree f E (a.tensorPower (k + 1)) σ hσ b : ℤ) : ℝ) =
      pairingLM (integrationCurrent (canonicalBasis 1) (Nat.succ_pos 0)
        (nativeSectionDivisorMetric B hB s hdense))
        (curveCurrentComplement ▸ (unitForm : SmoothRealForm 1 (SchemeComplexPoint f) 0)) := by
  classical
  let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  let := sectionZero_isArtinian f E (a.tensorPower (k + 1)) σ hσ
  let Z := sectionZeroSubscheme (a.tensorPower (k + 1)) σ
  let : Fintype Z := Fintype.ofFinite _
  dsimp only
  let G := algebraicCurveZeroGeometry f E a H k σ hσ
  have hcurrent := G.pairing_unit_eq_sum_lengths hσ
  let len (z : Z) := Module.length (Z.presheaf.stalk z) (Z.presheaf.stalk z)
  have hlenfinite (z : Z) : len z ≠ ⊤ := artinianLocalLength_ne_top Z z
  have hsum : ((∑ z : Z, (len z).toNat : ℕ) : ℕ∞) = ∑ z : Z, len z := by
    rw [Nat.cast_sum]
    exact Finset.sum_congr rfl (fun z _ => ENat.natCast_toNat (hlenfinite z))
  have hnat := congrArg ENat.toNat hsum
  simp only [ENat.toNat_natCast] at hnat
  have hdegree : ((sectionZeroCycleDegree f E (a.tensorPower (k + 1)) σ hσ b : ℤ) : ℝ) =
      ∑ z : Z, ((len z).toNat : ℝ) := by
    rw [sectionZeroCycleDegree_eq_sum_lengths f E (a.tensorPower (k + 1)) σ hσ b]
    change (((∑ z : Z, len z).toNat : ℤ) : ℝ) = _
    rw [← hnat]
    simp only [Int.cast_sum, Int.cast_natCast, Nat.cast_sum]
  exact hdegree.trans hcurrent.symm

end SGPT.Projective.NumEq.AlgebraicCurveDegree
