import SGPT.Checks.Comparison.ThinApprox.BJChargeFS
import SGPT.Checks.Comparison.BJPairClass
import SGPT.Foundations.Envelope.Vanishing.NadelNefBigSingleExceptionalAmple
import SGPT.Foundations.Envelope.AlgGeom.ProjectiveSegrePullbackSections
import SGPT.Foundations.Envelope.AlgGeom.AmpleLineTwistGeneration
import SGPT.Foundations.Envelope.AlgGeom.PLModelAuxiliaryPolarizationFinitePullback
import SGPT.Foundations.Envelope.AlgGeom.CurveAmpleLineDegrees
import SGPT.Checks.Comparison.SourceNumericalAmpleness

namespace SGPT.NAPotential.BJ
end SGPT.NAPotential.BJ
namespace SGPT.NAPotential.BJ.AppSeq
end SGPT.NAPotential.BJ.AppSeq
namespace SGPT.NAPotential.BJ.FixedRay
end SGPT.NAPotential.BJ.FixedRay
namespace SGPT.NAPotential.BJ.MaxClosure
end SGPT.NAPotential.BJ.MaxClosure
namespace SGPT.NAPotential.BJ.Pair3ClassStability
end SGPT.NAPotential.BJ.Pair3ClassStability
namespace SGPT.NAPotential.BJ.Pair3Div
end SGPT.NAPotential.BJ.Pair3Div
namespace SGPT.NAPotential.BJ.Printed
end SGPT.NAPotential.BJ.Printed
namespace SGPT.NAPotential.BJ.RationalPromotion
end SGPT.NAPotential.BJ.RationalPromotion
namespace SGPT.NAPotential.BJ.SourceDXZPositive
end SGPT.NAPotential.BJ.SourceDXZPositive
namespace SGPT.NAPotential.BJ.SourceDivUnique
end SGPT.NAPotential.BJ.SourceDivUnique
namespace SGPT.NAPotential.BJ.SourceNet
end SGPT.NAPotential.BJ.SourceNet
namespace SGPT.NAPotential.BJ.SourceRationalPromotion
end SGPT.NAPotential.BJ.SourceRationalPromotion
namespace SGPT.NAPotential.BJCycle
end SGPT.NAPotential.BJCycle
namespace SGPT.NAPotential.BJModel
end SGPT.NAPotential.BJModel
namespace SGPT.NAPotential.ThinApprox.BJ
end SGPT.NAPotential.ThinApprox.BJ
namespace SGPT.NAPotential.ThinApprox.BJ.AppSeq
end SGPT.NAPotential.ThinApprox.BJ.AppSeq
namespace SGPT.NAPotential.ThinApprox.BJ.FixedRay
end SGPT.NAPotential.ThinApprox.BJ.FixedRay
namespace SGPT.NAPotential.ThinApprox.BJ.MaxClosure
end SGPT.NAPotential.ThinApprox.BJ.MaxClosure
namespace SGPT.NAPotential.ThinApprox.BJ.Pair3ClassStability
end SGPT.NAPotential.ThinApprox.BJ.Pair3ClassStability
namespace SGPT.NAPotential.ThinApprox.BJ.Pair3Div
end SGPT.NAPotential.ThinApprox.BJ.Pair3Div
namespace SGPT.NAPotential.ThinApprox.BJ.Printed
end SGPT.NAPotential.ThinApprox.BJ.Printed
namespace SGPT.NAPotential.ThinApprox.BJ.SourceDXZPositive
end SGPT.NAPotential.ThinApprox.BJ.SourceDXZPositive
namespace SGPT.NAPotential.ThinApprox.BJ.SourceDivUnique
end SGPT.NAPotential.ThinApprox.BJ.SourceDivUnique
namespace SGPT.NAPotential.ThinApprox.BJ.SourceNet
end SGPT.NAPotential.ThinApprox.BJ.SourceNet
namespace SGPT.NAPotential.ThinApprox.BJCycle
end SGPT.NAPotential.ThinApprox.BJCycle
namespace SGPT.NAPotential.ThinApprox.BJModel
end SGPT.NAPotential.ThinApprox.BJModel


/-!
# Ample classes on the blow-up models

Source: [BJ22] (`references/bj22-trivval`), `lem:relamp` (`π^*ω - ε E` is relatively ample on a
blow-up model for `0 < ε ≪ 1`); Lazarsfeld, *Positivity I*, Example 1.2.11 (Segre:
`pr₁^*A ⊗ pr₂^*𝒪(1)` is very ample on `X × ℙ¹` for a very ample `A`). Towards the hypothesis
`RelAmplePositive` of `bjAppSeq_of_cycleLowerBound` (`thm:BJappseq` of `chapter_NApotential.tex`).
Blueprint: `claude-bj-relample.tex`.

* `exists_isAmple_smul_eq_picQ`: a rational class `ω` with ample numerical class has a positive
  multiple `m ω = [L]` with `L` ample (Kleiman's criterion, SGPT.Foundations.Envelope);
* `isAmple_segre`: for a closed embedding `i : X ⟶ ℙ^N` over `k`, `pr₁^* i^*𝒪(1) ⊗ pr₂^*𝒪(1)` is
  ample on `X × ℙ¹` (Segre embedding);
* `nonempty_pullback_twistOne_iso`: `𝒪_{ℙ¹}(1)` is trivial on every scheme mapping into `{0}`
  (it is trivial on the chart `D₊(x₀) ∋ 0`);
* `lineTwistClass`, `picPullbackQ_lineTwistClass_eq_zero`, `neg_lineTwistClass_mem_relNefCone`: the
  class `μ` of the pull-back of `𝒪_{ℙ¹}(1)` to a blow-up model vanishes on every scheme mapping into
  the central fibre, and `-μ` is nef on the central fibre;
* `isNefOn_of_isAmple`: ample invertible sheaves are nef on every set;
* `exceptionalDatum`: the exceptional divisor `(t^c 𝔠) · 𝒪` of the model `(𝔠, c)` as a flag datum.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.NAPotential.ThinApprox.BJ
open SGPT.NAPotential.BJ

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open MvPolynomial SGPT.Support.Alterations SGPT.Support.Alterations.Geometry
open SGPT.Foundations.Envelope SGPT.NAPotential.BJIntersect SGPT.NAPotential.BJModel SGPT.NAPotential.ThinApprox.BJModel FlagIdealBound

attribute [local instance] Scheme.Modules.monoidalCategory

/-! ### Ample representatives of ample rational classes -/

section representative

open SGPT.NAPotential.BJ.NativePicard

variable {X : Scheme.{0}} (p : X ⟶ Spec (.of ℂ)) [IsProjective p] [IsIntegral X]

/-- **Ample rational classes are rational multiples of ample invertible sheaves**: if the
numerical class of `ω ∈ Pic(X)_ℚ` lies in the ample cone, then `m ω = [L]` for some `m > 0` and
an ample invertible sheaf `L` (Kleiman's criterion: ampleness is numerical). -/
theorem exists_isAmple_smul_eq_picQ (ω : RationalPicardSpace X)
    (hω : numericalClass p ω ∈ NativeRealNumericalClasses.ampleCone p) :
    ∃ (m : ℕ) (L : X.Modules) (hL : SchemeLineAmpleness.IsAmple p L), 0 < m ∧
      (m : ℚ) • ω = picQ ⟨L, hL.isInvertible⟩ := by
  obtain ⟨L, a, m, hm, rfl⟩ := exists_actual_line_presentation ω
  have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  have hc : (m : ℚ) • ((1 / (m : ℚ)) • rationalPicardClass a) = rationalPicardClass a := by
    rw [smul_smul, mul_one_div_cancel hmQ, one_smul]
  have hcls : NativeRealNumericalClasses.lineClass p L (isInvertible_of_atlas a) =
      (m : ℝ) • numericalClass p ((1 / (m : ℚ)) • rationalPicardClass a) := by
    rw [← numericalClass_line p a, Nat.cast_smul_eq_nsmul ℝ, ← map_nsmul,
      ← Nat.cast_smul_eq_nsmul ℚ, hc]
  have hamp : NativeRealNumericalClasses.lineClass p L (isInvertible_of_atlas a) ∈
      NativeRealNumericalClasses.ampleCone p := by
    rw [hcls]
    exact (NativeRealNumericalClasses.ampleCone p).smul_mem (by exact_mod_cast hm) hω
  have hL := SGPT.NAPotential.BJ.SourceNumericalAmpleness.isAmple_of_lineClass_mem_ampleCone p L (isInvertible_of_atlas a) hamp
  exact ⟨m, L, hL, hm, by rw [hc, rationalPicardClass_eq_picQ a]⟩

end representative

/-! ### Segre ampleness on `X × ℙ¹` -/

section segre

variable {k : Type} [Field k] {X : Scheme.{0}} (p : X ⟶ Spec (.of k))

/-- **Segre ampleness**: for a closed immersion `i : X ⟶ ℙ^N` over `k`, the invertible sheaf
`pr₁^* i^*𝒪(1) ⊗ pr₂^*𝒪(1)` is (very) ample on `X × ℙ¹`: it is the pull-back of `𝒪(1)` along the
closed immersion `X × ℙ¹ ⟶ ℙ^N × ℙ¹ ⟶ ℙ^{2N+1}` (product with `ℙ¹`, then the Segre embedding). -/
theorem isAmple_segre {N : ℕ} (i : X ⟶ projectiveSpace k N) [IsClosedImmersion i]
    (hi : i ≫ projectiveSpaceStructure k N = p) :
    SchemeLineAmpleness.IsAmple (productStructure p)
      (ProjectiveSegrePullbackSections.line (productFst p ≫ i) ⊗
        ProjectiveSegrePullbackSections.line (productSnd p)) := by
  have hfg : (productFst p ≫ i) ≫ projectiveSpaceStructure k N =
      productSnd p ≫ projectiveSpaceStructure k 1 := by
    rw [Category.assoc, hi]
    exact pullback.condition
  have hmap := MorphismProperty.pullbackMap (P := @IsClosedImmersion)
    (f := p) (g := projectiveSpaceStructure k 1) (f' := projectiveSpaceStructure k N)
    (g' := projectiveSpaceStructure k 1) (i₁ := i) (i₂ := 𝟙 _)
    (inferInstance : IsClosedImmersion i)
    (inferInstance : IsClosedImmersion (𝟙 (projectiveSpace k 1))) hi.symm
    (Category.id_comp _).symm
  have hpair : ProjectiveSegrePullbackSections.pair (productFst p ≫ i) (productSnd p) hfg =
      pullback.map p (projectiveSpaceStructure k 1) (projectiveSpaceStructure k N)
        (projectiveSpaceStructure k 1) i (𝟙 _) (𝟙 _)
        ((Category.comp_id _).trans hi.symm)
        ((Category.comp_id _).trans (Category.id_comp _).symm) := by
    apply pullback.hom_ext
    · simp [ProjectiveSegrePullbackSections.pair, pullback.map]
    · simp [ProjectiveSegrePullbackSections.pair, pullback.map]
  have : IsClosedImmersion
      (ProjectiveSegrePullbackSections.pair (productFst p ≫ i) (productSnd p) hfg) := by
    rw [hpair]
    exact hmap
  have hV : SchemeLineAmpleness.IsVeryAmple (productStructure p)
      (ProjectiveSegrePullbackSections.line
        (ProjectiveSegrePullbackSections.morphism (productFst p ≫ i) (productSnd p) hfg)) := by
    refine ⟨_, ProjectiveSegrePullbackSections.morphism (productFst p ≫ i) (productSnd p) hfg,
      ?_, ?_, ⟨Iso.refl _⟩⟩
    · unfold ProjectiveSegrePullbackSections.morphism
      infer_instance
    · rw [ProjectiveSegrePullbackSections.morphism_structure, Category.assoc, hi]
  exact AmpleLineTwistGeneration.isAmple_of_isVeryAmple
    (SchemeAmpleClosedRestriction.veryAmple_of_iso hV
      (ProjectiveSegrePullbackSections.lineIso (productFst p ≫ i) (productSnd p) hfg))

end segre

/-! ### `𝒪(1)` is trivial near `0 ∈ ℙ¹` -/

section chart

variable (k : Type) [Field k]

/-- The invertible sheaf `𝒪(1)` on `ℙ¹_k` (twist by the hyperplane `x₀ = 0`). -/
abbrev twistOne : (projectiveSpace k 1).Modules :=
  coordinateHyperplaneTwist (R := k) (0 : Fin (1 + 1)) 1

theorem twistOne_isInvertible : Scheme.Modules.IsInvertible (twistOne k) :=
  coordinateHyperplaneTwist_isInvertible (R := k) (0 : Fin (1 + 1)) 1

/-- The chart `D₊(x₀)` of `ℙ¹_k`. -/
abbrev zeroChart : (projectiveSpace k 1).Opens := coordinateOpen (R := k) (σ := Fin (1 + 1)) 0

/-- The point `0 = [1 : 0]` lies in the chart `D₊(x₀)`. -/
theorem range_zeroPoint_subset :
    Set.range (zeroPoint k) ⊆ (zeroChart k : Set (projectiveSpace k 1)) := by
  rintro _ ⟨x, rfl⟩
  have h : Segre.coordinateChartInclusion (R := k) (0 : Fin (1 + 1))
      (Spec.map (CommRingCat.ofHom (evalZero k)) x) ∈
        (Segre.coordinateChartInclusion (R := k) (0 : Fin (1 + 1))).opensRange := ⟨_, rfl⟩
  rw [Segre.coordinateChartInclusion_opensRange] at h
  rw [zeroPoint, Scheme.Hom.comp_apply]
  exact h

/-- **`𝒪_{ℙ¹}(1)` is trivial on every scheme mapping into `{0}`**: such a map factors through the
chart `D₊(x₀)`, on which `𝒪(1)` has the standard frame. -/
theorem nonempty_pullback_twistOne_iso {T : Scheme.{0}} (h : T ⟶ projectiveSpace k 1)
    (hh : Set.range h ⊆ Set.range (zeroPoint k)) :
    Nonempty ((Scheme.Modules.pullback h).obj (twistOne k) ≅ Scheme.Modules.unitObj T) := by
  let U := zeroChart k
  have hrange : Set.range h ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    exact hh.trans (range_zeroPoint_subset k)
  let h' := IsOpenImmersion.lift U.ι h hrange
  have hfac : h' ≫ U.ι = h := IsOpenImmersion.lift_fac _ _ _
  exact ⟨(Scheme.Modules.pullbackCongr hfac.symm).app _ ≪≫
    ((Scheme.Modules.pullbackComp h' U.ι).app _).symm ≪≫
    (Scheme.Modules.pullback h').mapIso
      (((Scheme.Modules.restrictFunctorIsoPullback U.ι).app _).symm ≪≫
        coordinateHyperplaneTwistTrivialization (R := k) (0 : Fin (1 + 1)) 0 1) ≪≫
    Scheme.Modules.pullbackUnitIso h'⟩

end chart

/-! ### Classes of invertible sheaves -/

section classes

/-- The `ℚ`-class of a tensor power is the multiple of the class. -/
theorem picQ_tensorPower {Y : Scheme.{0}} {N : Y.Modules} (hN : Scheme.Modules.IsInvertible N)
    (s : ℕ) (h : Scheme.Modules.IsInvertible (CanonicalGeometry.bundleTensorPower N s)) :
    picQ ⟨CanonicalGeometry.bundleTensorPower N s, h⟩ = (s : ℚ) • picQ ⟨N, hN⟩ := by
  simp only [picQ]
  rw [lineCls_tensorPower hN s, TensorProduct.tmul_smul, Nat.cast_smul_eq_nsmul]

/-- The `ℚ`-class of the trivial sheaf is `0`. -/
theorem picQ_unit {Y : Scheme.{0}} :
    picQ ⟨Scheme.Modules.unitObj Y, Scheme.Modules.isInvertible_unit⟩ = 0 := by
  simp only [picQ]
  rw [lineCls_unit, TensorProduct.tmul_zero]

/-- **Ample invertible sheaves are nef on every set.** -/
theorem isNefOn_of_isAmple {k : Type} [Field k] {Y : Scheme.{0}} [CompactSpace Y]
    (q : Y ⟶ Spec (.of k)) [IsProjective q] {A : Y.Modules}
    (hA : SchemeLineAmpleness.IsAmple q A) (W : Set Y) : IsNefOn q A W :=
  fun C _ => (CurveAmpleLineDegrees.degree_pos_on_closedIntegralCurve q A hA C).le

end classes

/-! ### The pull-back of `𝒪_{ℙ¹}(1)` to the models -/

section model

variable {X : Scheme.{0}} (p : X ⟶ Spec (.of ℂ)) [IsProjective p]

omit [IsProjective p] in
/-- Maps into the central fibre of a model map into `{0}` under `𝒳 ⟶ ℙ¹`. -/
theorem range_comp_modelLine_subset {T : Scheme.{0}} {𝔠 : FlagIdeal X} {c : ℤ}
    (g : T ⟶ flagModel p 𝔠 c) (hg : Set.range g ⊆ centralFibre p 𝔠 c) :
    Set.range (g ≫ modelLine p 𝔠 c) ⊆ Set.range (zeroPoint ℂ) := by
  rintro _ ⟨x, rfl⟩
  have hx : flagModelπ p 𝔠 c (g x) ∈ ((centralIdeal p).support : Set (productLine p)) :=
    hg ⟨x, rfl⟩
  rw [support_centralIdeal] at hx
  rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
  exact hx

/-- The class `μ = [ρ^*𝒪_{ℙ¹}(1)]` on the model `(𝔠, c)`, `ρ : 𝒳 ⟶ ℙ¹`. -/
def lineTwistClass (𝔠 : FlagIdeal X) (c : ℤ) : PicQ (flagModel p 𝔠 c) :=
  picQ ⟨ProjectiveSegrePullbackSections.line (modelLine p 𝔠 c),
    ProjectiveSegrePullbackSections.line_isInvertible _⟩

omit [IsProjective p] in
theorem lineTwistClass_eq (𝔠 : FlagIdeal X) (c : ℤ) :
    lineTwistClass p 𝔠 c = picPullbackQ (flagModelπ p 𝔠 c)
      (picPullbackQ (productSnd p) (picQ ⟨twistOne ℂ, twistOne_isInvertible ℂ⟩)) := by
  rw [← picPullbackQ_comp, picPullbackQ_picQ]
  rfl

omit [IsProjective p] in
/-- **`μ` vanishes on everything inside the central fibre.** -/
theorem picPullbackQ_lineTwistClass_eq_zero {T : Scheme.{0}} {𝔠 : FlagIdeal X} {c : ℤ}
    (g : T ⟶ flagModel p 𝔠 c) (hg : Set.range g ⊆ centralFibre p 𝔠 c) :
    picPullbackQ g (lineTwistClass p 𝔠 c) = 0 := by
  rw [lineTwistClass, picPullbackQ_picQ]
  obtain ⟨e⟩ := nonempty_pullback_twistOne_iso ℂ (g ≫ modelLine p 𝔠 c)
    (range_comp_modelLine_subset p g hg)
  exact (picQ_eq_of_iso _ Scheme.Modules.isInvertible_unit
    (((Scheme.Modules.pullbackComp g (modelLine p 𝔠 c)).app _) ≪≫ e)).trans picQ_unit

/-- `ρ^*𝒪(1)` has degree `0` on every closed integral curve inside the central fibre. -/
theorem degree_lineTwist_eq_zero {𝔠 : FlagIdeal X} {c : ℤ}
    (C : NativeClosedCurveDegrees.ClosedIntegralCurve (flagModel p 𝔠 c))
    (hC : Set.range C.inclusion ⊆ centralFibre p 𝔠 c) :
    letI : IsClosedImmersion C.inclusion := C.closed
    letI : CompactSpace C.carrier := QuasiCompact.compactSpace_of_compactSpace C.inclusion
    CurveLineDegrees.degree (C.inclusion ≫ flagModelStructure p 𝔠 c)
      ((Scheme.Modules.pullback C.inclusion).obj
        (ProjectiveSegrePullbackSections.line (modelLine p 𝔠 c))) = 0 := by
  let : IsClosedImmersion C.inclusion := C.closed
  let : CompactSpace C.carrier := QuasiCompact.compactSpace_of_compactSpace C.inclusion
  obtain ⟨e⟩ := nonempty_pullback_twistOne_iso ℂ (C.inclusion ≫ modelLine p 𝔠 c)
    (range_comp_modelLine_subset p _ hC)
  exact (CurveLineDegrees.degree_eq_of_iso _
    (((Scheme.Modules.pullbackComp C.inclusion (modelLine p 𝔠 c)).app _) ≪≫ e)).trans
    (CurveLineDegrees.degree_unit _)

/-- The dual of `ρ^*𝒪(1)` is nef on the central fibre. -/
theorem isNefOn_dual_lineTwist (𝔠 : FlagIdeal X) (c : ℤ) :
    IsNefOn (flagModelStructure p 𝔠 c)
      (Scheme.Modules.dualObj (ProjectiveSegrePullbackSections.line (modelLine p 𝔠 c)))
      (centralFibre p 𝔠 c) := by
  intro C hC
  let : IsClosedImmersion C.inclusion := C.closed
  let : IsIntegral C.carrier := C.integral
  let : CompactSpace C.carrier := QuasiCompact.compactSpace_of_compactSpace C.inclusion
  have hp : IsProjectiveFactorization (C.inclusion ≫ flagModelStructure p 𝔠 c) :=
    (SGPT.Foundations.Envelope.ProjectiveFactorizationRingIso.of_isProjective
      (flagModelStructure p 𝔠 c)).comp_isClosedImmersion C.inclusion C.closed
  have hL := ProjectiveSegrePullbackSections.line_isInvertible (modelLine p 𝔠 c)
  have h0 := degree_lineTwist_eq_zero p C hC
  have h1 := CurvePicardDegrees.curveDegreeHom_lineClass _ hp C.dimension.le C.inclusion
    (ProjectiveSegrePullbackSections.line (modelLine p 𝔠 c)) hL
  have h2 := CurvePicardDegrees.curveDegreeHom_lineClass _ hp C.dimension.le C.inclusion
    (Scheme.Modules.dualObj (ProjectiveSegrePullbackSections.line (modelLine p 𝔠 c))) hL.dual
  rw [SGPT.Foundations.Envelope.ProjectiveGeneratedLineClasses.lineClass_dual _ hL, map_inv,
    toAdd_inv] at h2
  have : CurveLineDegrees.degree (C.inclusion ≫ flagModelStructure p 𝔠 c)
      ((Scheme.Modules.pullback C.inclusion).obj
        (Scheme.Modules.dualObj (ProjectiveSegrePullbackSections.line (modelLine p 𝔠 c)))) = 0 := by
    rw [← h2, h1, h0, neg_zero]
  exact this.ge

/-- **`-μ` is nef on the central fibre.** -/
theorem neg_lineTwistClass_mem_relNefCone (𝔠 : FlagIdeal X) (c : ℤ) :
    -lineTwistClass p 𝔠 c ∈ relNefCone (flagModelStructure p 𝔠 c) (centralFibre p 𝔠 c) := by
  have hL := ProjectiveSegrePullbackSections.line_isInvertible (modelLine p 𝔠 c)
  have h := picQ_mem_relNefCone (flagModelStructure p 𝔠 c)
    ⟨Scheme.Modules.dualObj (ProjectiveSegrePullbackSections.line (modelLine p 𝔠 c)), hL.dual⟩
    (isNefOn_dual_lineTwist p 𝔠 c)
  convert h using 1
  simp only [lineTwistClass, picQ, lineCls]
  rw [SGPT.Foundations.Envelope.ProjectiveGeneratedLineClasses.lineClass_dual _ hL, ofMul_inv,
    TensorProduct.tmul_neg]

omit [IsProjective p] in
/-- **The exceptional divisor of the model `(𝔠, c)` as a flag datum**: `(t^c 𝔠) · 𝒪` is invertible
on the blow-up of `t^c 𝔠`. -/
def exceptionalDatum {𝔠 : FlagIdeal X} {c : ℤ} (hc : IsWeightBound 𝔠 c) : FlagDatum p 𝔠 c where
  ideal := 𝔠
  bound := c
  isWeightBound := hc
  isInvertible := isInvertible_comap_flagSheaf p 𝔠 c

end model

/-! ### The ample sheaf on a model -/

section ampleLine

variable {X : Scheme.{0}} (p : X ⟶ Spec (.of ℂ)) {N₀ : ℕ} (i : X ⟶ projectiveSpace ℂ N₀)

/-- The Segre sheaf `H = pr₁^* i^*𝒪(1) ⊗ pr₂^*𝒪(1)` on `X × ℙ¹`. -/
def segreLine : (productLine p).Modules :=
  ProjectiveSegrePullbackSections.line (productFst p ≫ i) ⊗
    ProjectiveSegrePullbackSections.line (productSnd p)

theorem segreLine_isInvertible : Scheme.Modules.IsInvertible (segreLine p i) :=
  ((ProjectiveSegrePullbackSections.line_isInvertible _).tensorObj
    (ProjectiveSegrePullbackSections.line_isInvertible _)).of_iso
    (SGPT.Support.ModularCurves.monoidalTensorObjIso _ _)

/-- **The class of the Segre sheaf**: if `i^*𝒪(1) ≅ L^r`, then
`[H] = r pr₁^*[L] + pr₂^*[𝒪(1)]`. -/
theorem picQ_segreLine {L : X.Modules} (hL : Scheme.Modules.IsInvertible L) {r : ℕ}
    (eL : (Scheme.Modules.pullback i).obj
        (coordinateHyperplaneTwist (R := ℂ) (0 : Fin (N₀ + 1)) 1) ≅
      CanonicalGeometry.bundleTensorPower L r) :
    picQ ⟨segreLine p i, segreLine_isInvertible p i⟩ =
      (r : ℚ) • picPullbackQ (productFst p) (picQ ⟨L, hL⟩) +
        picPullbackQ (productSnd p) (picQ ⟨twistOne ℂ, twistOne_isInvertible ℂ⟩) := by
  have hF : picQ ⟨ProjectiveSegrePullbackSections.line (productFst p ≫ i),
      ProjectiveSegrePullbackSections.line_isInvertible _⟩ =
      (r : ℚ) • picPullbackQ (productFst p) (picQ ⟨L, hL⟩) := by
    have h1 := picPullbackQ_comp (productFst p) i
      (picQ ⟨coordinateHyperplaneTwist (R := ℂ) (0 : Fin (N₀ + 1)) 1,
        coordinateHyperplaneTwist_isInvertible (R := ℂ) (0 : Fin (N₀ + 1)) 1⟩)
    rw [picPullbackQ_picQ, picPullbackQ_picQ] at h1
    refine h1.trans ?_
    rw [picQ_eq_of_iso _ (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL r) eL,
      picQ_tensorPower hL r, map_smul]
  refine (picQ_tensor (ProjectiveSegrePullbackSections.line_isInvertible _)
    (ProjectiveSegrePullbackSections.line_isInvertible _) (segreLine_isInvertible p i)).trans ?_
  rw [hF]
  congr 1
  exact (picPullbackQ_picQ (productSnd p) ⟨twistOne ℂ, twistOne_isInvertible ℂ⟩).symm

/-- The ample sheaf `A = 𝒪(-E) ⊗ π^*H^s` on the model `(𝔠, c)`. -/
def modelAmpleLine (𝔠 : FlagIdeal X) (c : ℤ) (s : ℕ) : (flagModel p 𝔠 c).Modules :=
  (flagSheaf p 𝔠 c).exceptionalDivisor.toModules ⊗
    (Scheme.Modules.pullback (flagModelπ p 𝔠 c)).obj
      (CanonicalGeometry.bundleTensorPower (segreLine p i) s)

/-- **The class of `A`**: `[A] = [𝒪(-E)] + s π^*[H]`. -/
theorem picQ_modelAmpleLine {𝔠 : FlagIdeal X} {c : ℤ}
    (hc : IsWeightBound 𝔠 c) (s : ℕ)
    (h : Scheme.Modules.IsInvertible (modelAmpleLine p i 𝔠 c s)) :
    picQ ⟨modelAmpleLine p i 𝔠 c s, h⟩ = picQ (exceptionalDatum p hc).vert.line +
      (s : ℚ) • picPullbackQ (flagModelπ p 𝔠 c)
        (picQ ⟨segreLine p i, segreLine_isInvertible p i⟩) := by
  have hE := (exceptionalDatum p hc).vert.line.2
  have hHs := TensorPowerBaseIdealGrading.tensorPower_isInvertible (segreLine_isInvertible p i) s
  refine (picQ_tensor hE (hHs.pullback (flagModelπ p 𝔠 c)) h).trans ?_
  congr 1
  refine (picPullbackQ_picQ (flagModelπ p 𝔠 c) ⟨_, hHs⟩).symm.trans ?_
  rw [picQ_tensorPower (segreLine_isInvertible p i) s, map_smul]

end ampleLine

end SGPT.NAPotential.ThinApprox.BJ
