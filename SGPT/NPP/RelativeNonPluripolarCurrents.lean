import SGPT.NPP.RelativeNonPluripolarPotentials
import SGPT.NPP.NonPluripolarCurrent5Relative
import SGPT.NPP.NonPluripolarCurrentBiholomorphic
import SGPT.NPP.NonPluripolarCurrentManifold
import SGPT.NPP.NonPluripolarCurrent3Currents
import SGPT.NPP.NonPluripolarClosedManifold

/-! Body-preserving consolidation PLAN ONLY. Fresh proper-name checking is
required; private flat objects are provenance, never providers for this file. -/

-- Exact frozen body: RelativePullbackDraft
section OriginalFragment_01

/-! Genuine relative NPP pullback comparison. The intrinsic chart producer
will manufacture pullback-closedness from the SAME original global T. -/
set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff ENNReal

namespace SGPT.NPP.RelativeNonPluripolar
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere SGPT.Foundations.Analysis.Pending
open LocalProductCurrents LocalBedfordTaylorProducts LocalBedfordTaylorLocality
open LocalBedfordTaylorCalculus LocalCurrentPullback LocalCurrentPullbackDdc BedfordTaylor
open SGPT.NPP.NonPluripolarCurrent

variable {n p r : ℕ} {A B : Opens (ComplexModel n)}
  {τ σ : ComplexModel n → ComplexModel n}

/-- Actual arbitrary-base relative bounded truncations commute with the
same genuine biholomorphic pullback, in every original degree. -/
theorem relativeTruncatedBT_pullback (h : IsBiholomorphicPair A B τ σ)
    (T : LocalProductCurrent n B (r + p)) (hT : IsPositive T)
    (hTc : IsClosedAny (r + p) T) (hTpc : IsClosedAny (r + p) (pullback h hT))
    (φ : Fin p → ComplexModel n → EReal) (hφ : ∀ i, PlurisubharmonicOn (φ i) B) (k : ℕ) :
    pullback h ((isTruncationFamily_relative T hT hTc φ hφ).isPositive k) =
      relativeTruncatedBT A (fun i x => φ i (τ x)) (pullback h hT) k :=
  RelativeBT.pullback_btProduct_rel h p r (fun i => truncationReal (φ i) k) T hT hTc hTpc
    (fun i => truncationReal_isLocallyBoundedPshOn (hφ i) k)

/-- The ACTUAL Borel strict-locus relative truncations commute with pullback. -/
theorem relativeTruncAt_pullback (h : IsBiholomorphicPair A B τ σ)
    (T : LocalProductCurrent n B (r + p)) (hT : IsPositive T)
    (hTc : IsClosedAny (r + p) T) (hTpc : IsClosedAny (r + p) (pullback h hT))
    (φ : Fin p → ComplexModel n → EReal) (hφ : ∀ i, PlurisubharmonicOn (φ i) B) (k : ℕ) :
    pullback h ((isTruncationFamily_relative T hT hTc φ hφ).isPositive_trunc k) =
      truncAt (relativeTruncatedBT A (fun i x => φ i (τ x)) (pullback h hT))
        (BedfordTaylorTopDegree.strictLocus A (fun i x => φ i (τ x))) k := by
  have hB := (isTruncationFamily_relative T hT hTc φ hφ).isPositive k
  have hO := BedfordTaylorTopDegree.measurableSet_strictLocus hφ k
  have e := pullback_mulBorel h hB (measurable_const.indicator hO)
    (isLocallyBoundedOn_indicator_one _) (fun x => by
      by_cases hx : x ∈ BedfordTaylorTopDegree.strictLocus B φ k <;> simp [hx])
  refine e.trans ?_
  rw [← indicator_strictLocus_comp h k, relativeTruncatedBT_pullback h T hT hTc hTpc φ hφ k]
  rfl

/-- Original actual finite mass produces the actual transported mass and
current. Closedness of the base pullback is explicit here; intrinsic manifold
producers derive it from the original base-current compatibility. -/
theorem exists_relative_product_of_pullback (h : IsBiholomorphicPair A B τ σ)
    (T : LocalProductCurrent n B (r + p)) (hT : IsPositive T)
    (hTc : IsClosedAny (r + p) T) (hTpc : IsClosedAny (r + p) (pullback h hT))
    (φ : Fin p → ComplexModel n → EReal) (hφ : ∀ i, PlurisubharmonicOn (φ i) B)
    (hm : HasFiniteRelativeMass T hT hTc φ hφ) :
    ∃ hmA : HasFiniteRelativeMass (pullback h hT) (isPositive_pullback h hT) hTpc
        (fun i x => φ i (τ x)) (plurisubharmonicOn_comp h hφ),
      pullback h (relativeNonPluripolarProduct T hT hTc φ hφ hm).property =
        (relativeNonPluripolarProduct (pullback h hT) (isPositive_pullback h hT) hTpc
          (fun i x => φ i (τ x)) (plurisubharmonicOn_comp h hφ) hmA).val := by
  have hconv := weakTendsto_pullback h
    (fun k => (isTruncationFamily_relative T hT hTc φ hφ).isPositive_trunc k)
    (relativeNonPluripolarProduct T hT hTc φ hφ hm).property
    (weakTendsto_relativeTruncations T hT hTc φ hφ hm)
  have e : (fun k => pullback h ((isTruncationFamily_relative T hT hTc φ hφ).isPositive_trunc k)) =
      truncAt (relativeTruncatedBT A (fun i x => φ i (τ x)) (pullback h hT))
        (BedfordTaylorTopDegree.strictLocus A (fun i x => φ i (τ x))) := by
    funext k
    exact relativeTruncAt_pullback h T hT hTc hTpc φ hφ k
  rw [e] at hconv
  have hmA := (hasFiniteRelativeMass_iff_exists_weak_limit (pullback h hT)
    (isPositive_pullback h hT) hTpc (fun i x => φ i (τ x))
    (plurisubharmonicOn_comp h hφ)).mpr ⟨_, hconv⟩
  refine ⟨hmA, ?_⟩
  ext γ ψ
  exact tendsto_nhds_unique (hconv γ ψ) (weakTendsto_relativeTruncations
    (pullback h hT) (isPositive_pullback h hT) hTpc (fun i x => φ i (τ x))
    (plurisubharmonicOn_comp h hφ) hmA γ ψ)

end SGPT.NPP.RelativeNonPluripolar

#check @SGPT.NPP.RelativeNonPluripolar.relativeTruncatedBT_pullback
#check @SGPT.NPP.RelativeNonPluripolar.relativeTruncAt_pullback
#check @SGPT.NPP.RelativeNonPluripolar.exists_relative_product_of_pullback
#print axioms SGPT.NPP.RelativeNonPluripolar.relativeTruncatedBT_pullback
#print axioms SGPT.NPP.RelativeNonPluripolar.relativeTruncAt_pullback
#print axioms SGPT.NPP.RelativeNonPluripolar.exists_relative_product_of_pullback

-- Close original EOF sections, then restore this fragment scope.
end
end OriginalFragment_01

-- Exact frozen body: RelativeGlobalTruncationDraft
section OriginalFragment_02

/-! Actual globally compatible relative strict truncations, manufactured from
original global T and PSH functions. Pullback closedness is proved internally. -/
set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff ENNReal Manifold

namespace SGPT.NPP.RelativeNonPluripolar
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere SGPT.Foundations.Analysis.Pending
open LocalProductCurrents LocalBedfordTaylorProducts LocalBedfordTaylorLocality
open LocalBedfordTaylorCalculus LocalBedfordTaylorDecreasing LocalCurrentPullback
open LocalCurrentPullbackDdc BedfordTaylor
open SGPT.NPP.NonPluripolarCurrent

/-- Pointwise equality of ORIGINAL potentials on the original domain preserves
actual strict truncation currents; no current equality certificate is supplied. -/
theorem relativeTruncAt_congr {n p r : ℕ} {U : Opens (ComplexModel n)}
    (T : LocalProductCurrent n U (r + p))
    (φ ψ : Fin p → ComplexModel n → EReal)
    (he : ∀ i, ∀ x ∈ U, φ i x = ψ i x) (k : ℕ) :
    truncAt (relativeTruncatedBT U φ T) (BedfordTaylorTopDegree.strictLocus U φ) k =
      truncAt (relativeTruncatedBT U ψ T) (BedfordTaylorTopDegree.strictLocus U ψ) k := by
  have hO : BedfordTaylorTopDegree.strictLocus U φ k =
      BedfordTaylorTopDegree.strictLocus U ψ k := by
    ext x
    constructor
    · rintro ⟨hx, hv⟩
      exact ⟨hx, fun i => by rw [← he i x hx]; exact hv i⟩
    · rintro ⟨hx, hv⟩
      exact ⟨hx, fun i => by rw [he i x hx]; exact hv i⟩
  have hBT : relativeTruncatedBT U φ T k = relativeTruncatedBT U ψ T k := by
    apply btProduct_congr p r _ _ T
    intro i x hx
    unfold truncationReal truncation
    rw [he i x hx]
  unfold truncAt
  rw [hO, hBT]

variable {n p r : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsManifold (𝓘(ℂ, ComplexModel n)) ∞ M]

/-- Every actual strict truncation is a globally compatible positive current.
The only base data is the ORIGINAL global positive closed T; its other-chart
closedness manufactures actual pullback-closedness on every overlap. -/
def relativeGlobalTruncations (T : PositiveCurrent n M (r + p)) (hTc : T.IsClosed)
    (φ : Fin p → M → EReal) (hφ : ∀ i, SGPT.PSH.ManifoldPSH (n := n) (φ i))
    (k : ℕ) : PositiveCurrent n M r where
  inChart e := truncAt (relativeTruncatedBT (chartTarget e)
    (fun i z => φ i (e.val.symm z)) (T.inChart e))
    (BedfordTaylorTopDegree.strictLocus (chartTarget e) (fun i z => φ i (e.val.symm z))) k
  isPositive e := (isTruncationFamily_relative (T.inChart e) (T.isPositive e) (hTc e)
    (fun i z => φ i (e.val.symm z)) (chartPlurisubharmonicOn hφ e)).isPositive_trunc k
  compatible e f := by
    have hh := chartTransition_isBiholomorphicPair e f
    have hAe := overlapSource_le e f
    have hBf := overlapTarget_le e f
    let TB := restrict hBf (T.inChart f)
    have hTB : IsPositive TB := isPositive_restrict (T.isPositive f) hBf
    have hTBc : IsClosedAny (r + p) TB := isClosedAny_restrict (hTc f) hBf
    have hcomp : restrict hAe (T.inChart e) = pullback hh hTB := T.compatible e f
    have hTBpc : IsClosedAny (r + p) (pullback hh hTB) := by
      rw [← hcomp]
      exact isClosedAny_restrict (hTc e) hAe
    have hφB : ∀ i, PlurisubharmonicOn (fun z => φ i (f.val.symm z)) (overlapTarget e f) :=
      fun i => (chartPlurisubharmonicOn hφ f i).mono hBf
    have eB := relativeTruncAt_restrict (T.inChart f) (T.isPositive f) (hTc f)
      (fun i z => φ i (f.val.symm z)) (chartPlurisubharmonicOn hφ f) hBf k
    rw [← relativeTruncAt_restrict (T.inChart e) (T.isPositive e) (hTc e)
      (fun i z => φ i (e.val.symm z)) (chartPlurisubharmonicOn hφ e) hAe k,
      pullback_congr_current hh _
        ((isTruncationFamily_relative TB hTB hTBc
          (fun i z => φ i (f.val.symm z)) hφB).isPositive_trunc k) eB.symm,
      relativeTruncAt_pullback hh TB hTB hTBc hTBpc
        (fun i z => φ i (f.val.symm z)) hφB k, ← hcomp]
    apply relativeTruncAt_congr
    intro i x hx
    have hx' : x ∈ (chartTransition e f).source := hx
    have hxf : e.val.symm x ∈ f.val.source := by
      simp only [chartTransition, OpenPartialHomeomorph.trans_source,
        OpenPartialHomeomorph.symm_source, mem_inter_iff, mem_preimage] at hx'
      exact hx'.2
    simp only [chartTransition, OpenPartialHomeomorph.coe_trans, Function.comp_apply,
      f.val.left_inv hxf]

/-- Exact original-coordinate readback of the manufactured global truncation. -/
theorem relativeGlobalTruncations_inChart (T : PositiveCurrent n M (r + p)) (hTc : T.IsClosed)
    (φ : Fin p → M → EReal) (hφ : ∀ i, SGPT.PSH.ManifoldPSH (n := n) (φ i))
    (k : ℕ) (e : ComplexChart n M) :
    (relativeGlobalTruncations T hTc φ hφ k).inChart e =
      truncAt (relativeTruncatedBT (chartTarget e)
        (fun i z => φ i (e.val.symm z)) (T.inChart e))
        (BedfordTaylorTopDegree.strictLocus (chartTarget e) (fun i z => φ i (e.val.symm z))) k := rfl

end SGPT.NPP.RelativeNonPluripolar

#check @SGPT.NPP.RelativeNonPluripolar.relativeTruncAt_congr
#check @SGPT.NPP.RelativeNonPluripolar.relativeGlobalTruncations
#check @SGPT.NPP.RelativeNonPluripolar.relativeGlobalTruncations_inChart
#print axioms SGPT.NPP.RelativeNonPluripolar.relativeTruncAt_congr
#print axioms SGPT.NPP.RelativeNonPluripolar.relativeGlobalTruncations
#print axioms SGPT.NPP.RelativeNonPluripolar.relativeGlobalTruncations_inChart

-- Close original EOF sections, then restore this fragment scope.
end
end OriginalFragment_02

-- Exact frozen body: RelativeGlobalCurrentDraft
section OriginalFragment_03

/-! Genuine intrinsic global relative currents from original global T and
PSH functions. Output compatibility is proved by actual weak convergence. -/
set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff ENNReal Manifold

namespace SGPT.NPP.RelativeNonPluripolar
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere SGPT.Foundations.Analysis.Pending
open LocalProductCurrents LocalBedfordTaylorProducts LocalBedfordTaylorLocality
open LocalBedfordTaylorCalculus LocalCurrentPullback LocalCurrentPullbackDdc BedfordTaylor
open LocalBedfordTaylorContinuity
open SGPT.NPP.NonPluripolarCurrent

variable {n p r : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsManifold (𝓘(ℂ, ComplexModel n)) ∞ M]

/-- Literal actual compact uniform relative-truncation trace mass in the
original chart expressions. No output current/covariance is part of the domain. -/
def HasFiniteGlobalRelativeMass (T : PositiveCurrent n M (r + p)) (hTc : T.IsClosed)
    (φ : Fin p → M → EReal) (hφ : ∀ i, SGPT.PSH.ManifoldPSH (n := n) (φ i)) : Prop :=
  ∀ e : ComplexChart n M, HasFiniteRelativeMass (T.inChart e) (T.isPositive e) (hTc e)
    (fun i z => φ i (e.val.symm z)) (chartPlurisubharmonicOn hφ e)

/-- The actual intrinsic relative current. The original finite trace bounds
select the genuine local products; full chart compatibility is manufactured
from the SAME original global base current and its actual strict truncations. -/
def globalRelativeNonPluripolarProduct (T : PositiveCurrent n M (r + p)) (hTc : T.IsClosed)
    (φ : Fin p → M → EReal) (hφ : ∀ i, SGPT.PSH.ManifoldPSH (n := n) (φ i))
    (hm : HasFiniteGlobalRelativeMass T hTc φ hφ) : PositiveCurrent n M r where
  inChart e := (relativeNonPluripolarProduct (T.inChart e) (T.isPositive e) (hTc e)
    (fun i z => φ i (e.val.symm z)) (chartPlurisubharmonicOn hφ e) (hm e)).val
  isPositive e := (relativeNonPluripolarProduct (T.inChart e) (T.isPositive e) (hTc e)
    (fun i z => φ i (e.val.symm z)) (chartPlurisubharmonicOn hφ e) (hm e)).property
  compatible e f := by
    have hh := chartTransition_isBiholomorphicPair e f
    have hAe := overlapSource_le e f
    have hBf := overlapTarget_le e f
    let S (a : ComplexChart n M) := relativeNonPluripolarProduct (T.inChart a)
      (T.isPositive a) (hTc a) (fun i z => φ i (a.val.symm z))
      (chartPlurisubharmonicOn hφ a) (hm a)
    have hconvB : WeakTendsto
        (fun k => restrict hBf ((relativeGlobalTruncations T hTc φ hφ k).inChart f))
        (restrict hBf (S f).val) := by
      intro γ ψ
      exact weakTendsto_relativeTruncations (T.inChart f) (T.isPositive f) (hTc f)
        (fun i z => φ i (f.val.symm z)) (chartPlurisubharmonicOn hφ f) (hm f)
        γ (extTest hBf ψ)
    have hpb := weakTendsto_pullback hh
      (fun k => isPositive_restrict ((relativeGlobalTruncations T hTc φ hφ k).isPositive f) hBf)
      (isPositive_restrict (S f).property hBf) hconvB
    ext γ ψ
    have hright := hpb γ ψ
    have heq (k : ℕ) :
        pullback hh (isPositive_restrict
          ((relativeGlobalTruncations T hTc φ hφ k).isPositive f) hBf) =
        restrict hAe ((relativeGlobalTruncations T hTc φ hφ k).inChart e) :=
      ((relativeGlobalTruncations T hTc φ hφ k).compatible e f).symm
    simp_rw [heq] at hright
    exact tendsto_nhds_unique
      (weakTendsto_relativeTruncations (T.inChart e) (T.isPositive e) (hTc e)
        (fun i z => φ i (e.val.symm z)) (chartPlurisubharmonicOn hφ e) (hm e)
        γ (extTest hAe ψ)) hright

/-- The actual global current retains the SAME local current in every chart. -/
theorem globalRelativeNonPluripolarProduct_inChart
    (T : PositiveCurrent n M (r + p)) (hTc : T.IsClosed)
    (φ : Fin p → M → EReal) (hφ : ∀ i, SGPT.PSH.ManifoldPSH (n := n) (φ i))
    (hm : HasFiniteGlobalRelativeMass T hTc φ hφ) (e : ComplexChart n M) :
    (globalRelativeNonPluripolarProduct T hTc φ hφ hm).inChart e =
      (relativeNonPluripolarProduct (T.inChart e) (T.isPositive e) (hTc e)
        (fun i z => φ i (e.val.symm z)) (chartPlurisubharmonicOn hφ e) (hm e)).val := rfl

/-- Genuine original global closedness, in every degree including zero. -/
theorem isClosed_globalRelativeNonPluripolarProduct
    (T : PositiveCurrent n M (r + p)) (hTc : T.IsClosed)
    (φ : Fin p → M → EReal) (hφ : ∀ i, SGPT.PSH.ManifoldPSH (n := n) (φ i))
    (hm : HasFiniteGlobalRelativeMass T hTc φ hφ) :
    (globalRelativeNonPluripolarProduct T hTc φ hφ hm).IsClosed := fun e =>
  isClosedAny_relativeNonPluripolarProduct (T.inChart e) (T.isPositive e) (hTc e)
    (fun i z => φ i (e.val.symm z)) (chartPlurisubharmonicOn hφ e) (hm e)

/-- All original global strict-level defining identities, on every actual chart. -/
theorem globalRelativeNonPluripolarProduct_strictLocus
    (T : PositiveCurrent n M (r + p)) (hTc : T.IsClosed)
    (φ : Fin p → M → EReal) (hφ : ∀ i, SGPT.PSH.ManifoldPSH (n := n) (φ i))
    (hm : HasFiniteGlobalRelativeMass T hTc φ hφ) (e : ComplexChart n M) (k : ℕ) :
    mulBorel ((globalRelativeNonPluripolarProduct T hTc φ hφ hm).inChart e)
      ((BedfordTaylorTopDegree.strictLocus (chartTarget e)
        (fun i z => φ i (e.val.symm z)) k).indicator fun _ => (1 : ℝ)) =
      (relativeGlobalTruncations T hTc φ hφ k).inChart e :=
  mulBorel_relativeNonPluripolarProduct_strictLocus (T.inChart e) (T.isPositive e) (hTc e)
    (fun i z => φ i (e.val.symm z)) (chartPlurisubharmonicOn hφ e) (hm e) k

/-- Actual extension by zero off the union of all original strict loci. -/
theorem globalRelativeNonPluripolarProduct_compl
    (T : PositiveCurrent n M (r + p)) (hTc : T.IsClosed)
    (φ : Fin p → M → EReal) (hφ : ∀ i, SGPT.PSH.ManifoldPSH (n := n) (φ i))
    (hm : HasFiniteGlobalRelativeMass T hTc φ hφ) (e : ComplexChart n M) :
    mulBorel ((globalRelativeNonPluripolarProduct T hTc φ hφ hm).inChart e)
      ((⋃ k, BedfordTaylorTopDegree.strictLocus (chartTarget e)
        (fun i z => φ i (e.val.symm z)) k)ᶜ.indicator fun _ => (1 : ℝ)) = 0 :=
  mulBorel_relativeNonPluripolarProduct_compl (T.inChart e) (T.isPositive e) (hTc e)
    (fun i z => φ i (e.val.symm z)) (chartPlurisubharmonicOn hφ e) (hm e)

/-- The globally compatible actual strict truncations converge to the genuine
intrinsic relative current. No supplied global weak-limit interface is used. -/
theorem weakTendsto_relativeGlobalTruncations
    (T : PositiveCurrent n M (r + p)) (hTc : T.IsClosed)
    (φ : Fin p → M → EReal) (hφ : ∀ i, SGPT.PSH.ManifoldPSH (n := n) (φ i))
    (hm : HasFiniteGlobalRelativeMass T hTc φ hφ) :
    PositiveCurrent.WeakTendsto (relativeGlobalTruncations T hTc φ hφ)
      (globalRelativeNonPluripolarProduct T hTc φ hφ hm) := fun e =>
  weakTendsto_relativeTruncations (T.inChart e) (T.isPositive e) (hTc e)
    (fun i z => φ i (e.val.symm z)) (chartPlurisubharmonicOn hφ e) (hm e)

end SGPT.NPP.RelativeNonPluripolar

#check @SGPT.NPP.RelativeNonPluripolar.HasFiniteGlobalRelativeMass
#check @SGPT.NPP.RelativeNonPluripolar.globalRelativeNonPluripolarProduct
#check @SGPT.NPP.RelativeNonPluripolar.globalRelativeNonPluripolarProduct_inChart
#check @SGPT.NPP.RelativeNonPluripolar.isClosed_globalRelativeNonPluripolarProduct
#check @SGPT.NPP.RelativeNonPluripolar.globalRelativeNonPluripolarProduct_strictLocus
#check @SGPT.NPP.RelativeNonPluripolar.globalRelativeNonPluripolarProduct_compl
#check @SGPT.NPP.RelativeNonPluripolar.weakTendsto_relativeGlobalTruncations
#print axioms SGPT.NPP.RelativeNonPluripolar.HasFiniteGlobalRelativeMass
#print axioms SGPT.NPP.RelativeNonPluripolar.globalRelativeNonPluripolarProduct
#print axioms SGPT.NPP.RelativeNonPluripolar.globalRelativeNonPluripolarProduct_inChart
#print axioms SGPT.NPP.RelativeNonPluripolar.isClosed_globalRelativeNonPluripolarProduct
#print axioms SGPT.NPP.RelativeNonPluripolar.globalRelativeNonPluripolarProduct_strictLocus
#print axioms SGPT.NPP.RelativeNonPluripolar.globalRelativeNonPluripolarProduct_compl
#print axioms SGPT.NPP.RelativeNonPluripolar.weakTendsto_relativeGlobalTruncations

-- Close original EOF sections, then restore this fragment scope.
end
end OriginalFragment_03

-- Exact frozen body: RelativeCompatibleBaseDraft
section OriginalFragment_04

/-! Actual relative product transport from compatible ORIGINAL base currents.
Both base restrictions retain their original closedness; no closed-pullback
or relative-output compatibility premise is introduced. -/
set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff ENNReal

namespace SGPT.NPP.RelativeNonPluripolar
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere SGPT.Foundations.Analysis.Pending
open LocalProductCurrents LocalBedfordTaylorProducts LocalBedfordTaylorLocality
open LocalBedfordTaylorCalculus LocalCurrentPullback LocalCurrentPullbackDdc BedfordTaylor
open SGPT.NPP.NonPluripolarCurrent

/-- Two actual closed positive ORIGINAL base currents related by genuine
pullback give genuinely covariant relative outputs. The actual PSH coordinate
expressions and compact trace bounds are retained, and pullback-closedness is
manufactured from the other original base rather than supplied as a premise. -/
theorem relative_product_pullback_of_base_compatible
    {n p r : ℕ} {A B : Opens (ComplexModel n)} {τ σ : ComplexModel n → ComplexModel n}
    (h : IsBiholomorphicPair A B τ σ)
    (T : LocalProductCurrent n B (r + p)) (hT : IsPositive T) (hTc : IsClosedAny (r + p) T)
    (R : LocalProductCurrent n A (r + p)) (hR : IsPositive R) (hRc : IsClosedAny (r + p) R)
    (hbase : R = pullback h hT)
    (φ : Fin p → ComplexModel n → EReal) (hφ : ∀ i, PlurisubharmonicOn (φ i) B)
    (ψ : Fin p → ComplexModel n → EReal) (hψ : ∀ i, PlurisubharmonicOn (ψ i) A)
    (he : ∀ i, ∀ x ∈ A, φ i (τ x) = ψ i x)
    (hmφ : HasFiniteRelativeMass T hT hTc φ hφ)
    (hmψ : HasFiniteRelativeMass R hR hRc ψ hψ) :
    pullback h (relativeNonPluripolarProduct T hT hTc φ hφ hmφ).property =
      (relativeNonPluripolarProduct R hR hRc ψ hψ hmψ).val := by
  have hTpc : IsClosedAny (r + p) (pullback h hT) := by
    rw [← hbase]
    exact hRc
  have hseq (k : ℕ) :
      pullback h ((isTruncationFamily_relative T hT hTc φ hφ).isPositive_trunc k) =
        truncAt (relativeTruncatedBT A ψ R) (BedfordTaylorTopDegree.strictLocus A ψ) k := by
    rw [relativeTruncAt_pullback h T hT hTc hTpc φ hφ k, ← hbase]
    exact relativeTruncAt_congr R (fun i x => φ i (τ x)) ψ he k
  have hconv := weakTendsto_pullback h
    (fun k => (isTruncationFamily_relative T hT hTc φ hφ).isPositive_trunc k)
    (relativeNonPluripolarProduct T hT hTc φ hφ hmφ).property
    (weakTendsto_relativeTruncations T hT hTc φ hφ hmφ)
  simp_rw [hseq] at hconv
  ext γ χ
  exact tendsto_nhds_unique (hconv γ χ)
    (weakTendsto_relativeTruncations R hR hRc ψ hψ hmψ γ χ)

end SGPT.NPP.RelativeNonPluripolar
#check @SGPT.NPP.RelativeNonPluripolar.relative_product_pullback_of_base_compatible
#print axioms SGPT.NPP.RelativeNonPluripolar.relative_product_pullback_of_base_compatible

-- Close original EOF sections, then restore this fragment scope.
end
end OriginalFragment_04

-- Exact frozen body: RelativeCurrentFactorMassDraft
section OriginalFragment_05

/-! Original current-factor local potential comparisons with the SAME
arbitrary global base current and actual compact trace mass. -/
set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff ENNReal Manifold

namespace SGPT.NPP.RelativeNonPluripolar
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere SGPT.Foundations.Analysis.Pending
open LocalProductCurrents LocalBedfordTaylorProducts LocalBedfordTaylorLocality
open LocalBedfordTaylorCalculus LocalCurrentL1Ddc
open SGPT.NPP.NonPluripolarCurrent

variable {m p r : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel (m + 1)) M]
  [IsManifold (𝓘(ℂ, ComplexModel (m + 1))) ∞ M]

/-- The original actual compact uniform mass condition on an open set,
with the SAME original global base actually restricted in every chart. -/
def HasFiniteRelativeMassOn (B : PositiveCurrent (m + 1) M (r + p)) (hBc : B.IsClosed)
    (φ : Fin p → M → EReal) (O : Opens M)
    (hφ : ∀ i, (SGPT.PSH.VariableComplexAtlas.ofFixedModel (m + 1) M).IsPSHOn (φ i) O) : Prop :=
  ∀ e : ComplexChart (m + 1) M,
    HasFiniteRelativeMass (restrict (chartDomain_le e O) (B.inChart e))
      (isPositive_restrict (B.isPositive e) (chartDomain_le e O))
      (isClosedAny_restrict (hBc e) (chartDomain_le e O))
      (fun i z => φ i (e.val.symm z)) (fun i => (isL1PshOn_chartDomain (hφ i) e).psh)

/-- Actual local mass restricts to EVERY genuine coordinate subdomain,
retaining the SAME original global base current. -/
theorem relativeMassOn_chart_restrict
    (B : PositiveCurrent (m + 1) M (r + p)) (hBc : B.IsClosed)
    (φ : Fin p → M → EReal) (O : Opens M)
    (hφ : ∀ i, (SGPT.PSH.VariableComplexAtlas.ofFixedModel (m + 1) M).IsPSHOn (φ i) O)
    (hm : HasFiniteRelativeMassOn B hBc φ O hφ) (e : ComplexChart (m + 1) M)
    {W : Opens (ComplexModel (m + 1))} (hW : W ≤ chartDomain e O) :
    HasFiniteRelativeMass (restrict (hW.trans (chartDomain_le e O)) (B.inChart e))
      (isPositive_restrict (B.isPositive e) (hW.trans (chartDomain_le e O)))
      (isClosedAny_restrict (hBc e) (hW.trans (chartDomain_le e O)))
      (fun i z => φ i (e.val.symm z)) (fun i => ((isL1PshOn_chartDomain (hφ i) e).psh).mono hW) := by
  have h := hasFiniteRelativeMass_restrict (restrict (chartDomain_le e O) (B.inChart e))
    (isPositive_restrict (B.isPositive e) (chartDomain_le e O))
    (isClosedAny_restrict (hBc e) (chartDomain_le e O))
    (fun i z => φ i (e.val.symm z)) (fun i => (isL1PshOn_chartDomain (hφ i) e).psh) (hm e) hW
  simpa only [restrict_restrict] using h

/-- Full actual relative-current readback on coordinate subdomains,
with every nested restriction of the original base identified internally. -/
theorem relativeProductOn_chart_restrict
    (B : PositiveCurrent (m + 1) M (r + p)) (hBc : B.IsClosed)
    (φ : Fin p → M → EReal) (O : Opens M)
    (hφ : ∀ i, (SGPT.PSH.VariableComplexAtlas.ofFixedModel (m + 1) M).IsPSHOn (φ i) O)
    (hm : HasFiniteRelativeMassOn B hBc φ O hφ) (e : ComplexChart (m + 1) M)
    {W : Opens (ComplexModel (m + 1))} (hW : W ≤ chartDomain e O) :
    restrict hW (relativeNonPluripolarProduct (restrict (chartDomain_le e O) (B.inChart e))
      (isPositive_restrict (B.isPositive e) (chartDomain_le e O))
      (isClosedAny_restrict (hBc e) (chartDomain_le e O))
      (fun i z => φ i (e.val.symm z)) (fun i => (isL1PshOn_chartDomain (hφ i) e).psh) (hm e)).val =
    (relativeNonPluripolarProduct (restrict (hW.trans (chartDomain_le e O)) (B.inChart e))
      (isPositive_restrict (B.isPositive e) (hW.trans (chartDomain_le e O)))
      (isClosedAny_restrict (hBc e) (hW.trans (chartDomain_le e O)))
      (fun i z => φ i (e.val.symm z)) (fun i => ((isL1PshOn_chartDomain (hφ i) e).psh).mono hW)
      (relativeMassOn_chart_restrict B hBc φ O hφ hm e hW)).val := by
  have h := restrict_relativeNonPluripolarProduct (restrict (chartDomain_le e O) (B.inChart e))
    (isPositive_restrict (B.isPositive e) (chartDomain_le e O))
    (isClosedAny_restrict (hBc e) (chartDomain_le e O))
    (fun i z => φ i (e.val.symm z)) (fun i => (isL1PshOn_chartDomain (hφ i) e).psh) (hm e) hW
  simpa only [restrict_restrict] using h

/-- SAME original current factors manufacture actual potential independence
on every overlap; the original arbitrary global base B is never replaced.
Native Weyl produces all pluriharmonic differences from actual ddcL1 equality. -/
theorem relativeMassOn_compare_potentials
    (B : PositiveCurrent (m + 1) M (r + p)) (hBc : B.IsClosed)
    {T : Fin p → PositiveCurrent (m + 1) M m} {O O' : Opens M}
    {φ ψ : Fin p → M → EReal} (hφ : IsLocalPotential T O φ) (hψ : IsLocalPotential T O' ψ)
    (e : ComplexChart (m + 1) M) {W : Opens (ComplexModel (m + 1))}
    (hW : W ≤ chartDomain e O) (hW' : W ≤ chartDomain e O') :
    let R := restrict (hW.trans (chartDomain_le e O)) (B.inChart e)
    let hR := isPositive_restrict (B.isPositive e) (hW.trans (chartDomain_le e O))
    let hRc := isClosedAny_restrict (hBc e) (hW.trans (chartDomain_le e O))
    (HasFiniteRelativeMass R hR hRc (fun i z => φ i (e.val.symm z))
        (fun i => ((hφ.isL1PshOn e i).mono hW).psh) ↔
      HasFiniteRelativeMass R hR hRc (fun i z => ψ i (e.val.symm z))
        (fun i => ((hψ.isL1PshOn e i).mono hW').psh)) ∧
    ∀ (hmφ : HasFiniteRelativeMass R hR hRc (fun i z => φ i (e.val.symm z))
        (fun i => ((hφ.isL1PshOn e i).mono hW).psh))
      (hmψ : HasFiniteRelativeMass R hR hRc (fun i z => ψ i (e.val.symm z))
        (fun i => ((hψ.isL1PshOn e i).mono hW').psh)),
      (relativeNonPluripolarProduct R hR hRc (fun i z => φ i (e.val.symm z))
        (fun i => ((hφ.isL1PshOn e i).mono hW).psh) hmφ).val =
      (relativeNonPluripolarProduct R hR hRc (fun i z => ψ i (e.val.symm z))
        (fun i => ((hψ.isL1PshOn e i).mono hW').psh) hmψ).val := by
  apply relative_product_independent_of_ddcL1
    (restrict (hW.trans (chartDomain_le e O)) (B.inChart e))
    (isPositive_restrict (B.isPositive e) (hW.trans (chartDomain_le e O)))
    (isClosedAny_restrict (hBc e) (hW.trans (chartDomain_le e O)))
    (fun i z => φ i (e.val.symm z)) (fun i z => ψ i (e.val.symm z))
    (fun i => (hφ.isL1PshOn e i).mono hW) (fun i => (hψ.isL1PshOn e i).mono hW')
  intro i
  rw [hφ.ddcL1_eq e hW, hψ.ddcL1_eq e hW']

end SGPT.NPP.RelativeNonPluripolar
#check @SGPT.NPP.RelativeNonPluripolar.HasFiniteRelativeMassOn
#check @SGPT.NPP.RelativeNonPluripolar.relativeMassOn_chart_restrict
#check @SGPT.NPP.RelativeNonPluripolar.relativeProductOn_chart_restrict
#check @SGPT.NPP.RelativeNonPluripolar.relativeMassOn_compare_potentials
#print axioms SGPT.NPP.RelativeNonPluripolar.HasFiniteRelativeMassOn
#print axioms SGPT.NPP.RelativeNonPluripolar.relativeMassOn_chart_restrict
#print axioms SGPT.NPP.RelativeNonPluripolar.relativeProductOn_chart_restrict
#print axioms SGPT.NPP.RelativeNonPluripolar.relativeMassOn_compare_potentials

-- Close original EOF sections, then restore this fragment scope.
end
end OriginalFragment_05

-- Exact frozen body: RelativeCurrentFactorGlueDraft
section OriginalFragment_06

/-! Actual chart gluing from the ORIGINAL local-current-factor potential
cover and compact trace mass. Every overlap comparison is manufactured. -/
set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff ENNReal Manifold

namespace SGPT.NPP.RelativeNonPluripolar
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere SGPT.Foundations.Analysis.Pending
open LocalProductCurrents LocalBedfordTaylorProducts LocalBedfordTaylorLocality
open LocalBedfordTaylorCalculus LocalCurrentL1Ddc
open SGPT.NPP.NonPluripolarCurrent

variable {m p r : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel (m + 1)) M]
  [IsManifold (𝓘(ℂ, ComplexModel (m + 1))) ∞ M]

/-- The ORIGINAL local-potential-cover definition for relative products:
actual PSH potentials of the same current factors and actual finite relative
mass against the original arbitrary closed positive base. No output is input. -/
def IsRelativeCurrentProductWellDefined
    (B : PositiveCurrent (m + 1) M (r + p)) (hBc : B.IsClosed)
    (T : Fin p → PositiveCurrent (m + 1) M m) : Prop :=
  ∃ C : Set (Opens M), (∀ x : M, ∃ O ∈ C, x ∈ O) ∧
    ∀ O ∈ C, ∃ φ : Fin p → M → EReal, ∃ hφ : IsLocalPotential T O φ,
      HasFiniteRelativeMassOn B hBc φ O hφ.psh

namespace IsRelativeCurrentProductWellDefined
variable {B : PositiveCurrent (m + 1) M (r + p)} {hBc : B.IsClosed}
  {T : Fin p → PositiveCurrent (m + 1) M m} (hW : IsRelativeCurrentProductWellDefined B hBc T)

/-- The original cover, selected from the original source existence. -/
def cover : Set (Opens M) := hW.choose

theorem cover_spec (x : M) : ∃ O ∈ hW.cover, x ∈ O := hW.choose_spec.1 x

/-- Original local potentials, selected from the ORIGINAL source data. -/
def pot (O : hW.cover) : Fin p → M → EReal := (hW.choose_spec.2 O.1 O.2).choose

/-- The selected potentials satisfy the actual original current equations. -/
theorem potential (O : hW.cover) : IsLocalPotential T O.1 (hW.pot O) :=
  (hW.choose_spec.2 O.1 O.2).choose_spec.choose

/-- Actual mass of the selected original potential tuple. -/
theorem potMass (O : hW.cover) : HasFiniteRelativeMassOn B hBc (hW.pot O) O.1 (hW.potential O).psh :=
  (hW.choose_spec.2 O.1 O.2).choose_spec.choose_spec

/-- Actual relative product on one original potential domain in one chart. -/
def localProduct (e : ComplexChart (m + 1) M) (O : hW.cover) :
    LocalProductCurrent (m + 1) (chartDomain e O.1) r :=
  (relativeNonPluripolarProduct (restrict (chartDomain_le e O.1) (B.inChart e))
    (isPositive_restrict (B.isPositive e) (chartDomain_le e O.1))
    (isClosedAny_restrict (hBc e) (chartDomain_le e O.1))
    (fun i z => hW.pot O i (e.val.symm z)) ((hW.potential O).chartPsh e) (hW.potMass O e)).val

theorem isPositive_localProduct (e : ComplexChart (m + 1) M) (O : hW.cover) :
    IsPositive (hW.localProduct e O) :=
  (relativeNonPluripolarProduct (restrict (chartDomain_le e O.1) (B.inChart e))
    (isPositive_restrict (B.isPositive e) (chartDomain_le e O.1))
    (isClosedAny_restrict (hBc e) (chartDomain_le e O.1))
    (fun i z => hW.pot O i (e.val.symm z)) ((hW.potential O).chartPsh e) (hW.potMass O e)).property

/-- Compatibility is PROVED from the actual original current-factor equations
by native Weyl and actual relative restriction, rather than supplied. -/
theorem isCompatibleFamily (e : ComplexChart (m + 1) M) :
    SGPT.Currents.IsCompatibleFamily (fun O : hW.cover => chartDomain e O.1) (hW.localProduct e) where
  isPositive := hW.isPositive_localProduct e
  agree O V := by
    rw [localProduct, localProduct,
      relativeProductOn_chart_restrict B hBc (hW.pot O) O.1 (hW.potential O).psh
        (hW.potMass O) e inf_le_left,
      relativeProductOn_chart_restrict B hBc (hW.pot V) V.1 (hW.potential V).psh
        (hW.potMass V) e inf_le_right]
    exact (relativeMassOn_compare_potentials B hBc (hW.potential O) (hW.potential V)
      e inf_le_left inf_le_right).2 _ _

theorem chartDomain_cover (e : ComplexChart (m + 1) M) :
    ∀ z ∈ chartTarget e, ∃ O : hW.cover, z ∈ chartDomain e O.1 := by
  intro z hz
  obtain ⟨O,hO,hzO⟩ := hW.cover_spec (e.val.symm z)
  exact ⟨⟨O,hO⟩,hz,hzO⟩

/-- Actual positive-current sheaf gluing of the internally compatible outputs. -/
theorem exists_glue (e : ComplexChart (m + 1) M) :
    ∃ S : LocalProductCurrent (m + 1) (chartTarget e) r, IsPositive S ∧
      ∀ O : hW.cover, restrict (chartDomain_le e O.1) S = hW.localProduct e O :=
  (hW.isCompatibleFamily e).exists_glue (fun O => chartDomain_le e O.1) (hW.chartDomain_cover e)

/-- Manufactured actual chart current; no output chart-current field is input. -/
def productInChart (e : ComplexChart (m + 1) M) : LocalProductCurrent (m + 1) (chartTarget e) r :=
  (hW.exists_glue e).choose

theorem isPositive_productInChart (e : ComplexChart (m + 1) M) : IsPositive (hW.productInChart e) :=
  (hW.exists_glue e).choose_spec.1

theorem restrict_productInChart (e : ComplexChart (m + 1) M) (O : hW.cover) :
    restrict (chartDomain_le e O.1) (hW.productInChart e) = hW.localProduct e O :=
  (hW.exists_glue e).choose_spec.2 O

/-- ANY original local potential tuple has actual finite relative mass and
reads back the SAME manufactured chart current. The initial cover/tuple may
differ; all actual mass/equality on its intersections is manufactured. -/
theorem productInChart_restrict {O : Opens M} {ψ : Fin p → M → EReal}
    (hψ : IsLocalPotential T O ψ) (e : ComplexChart (m + 1) M) :
    ∃ hmψ : HasFiniteRelativeMass (restrict (chartDomain_le e O) (B.inChart e))
        (isPositive_restrict (B.isPositive e) (chartDomain_le e O))
        (isClosedAny_restrict (hBc e) (chartDomain_le e O))
        (fun i z => ψ i (e.val.symm z)) (hψ.chartPsh e),
      restrict (chartDomain_le e O) (hW.productInChart e) =
        (relativeNonPluripolarProduct (restrict (chartDomain_le e O) (B.inChart e))
          (isPositive_restrict (B.isPositive e) (chartDomain_le e O))
          (isClosedAny_restrict (hBc e) (chartDomain_le e O))
          (fun i z => ψ i (e.val.symm z)) (hψ.chartPsh e) hmψ).val := by
  have hloc (V : hW.cover) :
      HasFiniteRelativeMass (restrict
        ((inf_le_left : chartDomain e O ⊓ chartDomain e V.1 ≤ _).trans (chartDomain_le e O))
          (B.inChart e))
        (isPositive_restrict (B.isPositive e) ((inf_le_left : chartDomain e O ⊓ chartDomain e V.1 ≤ _).trans (chartDomain_le e O)))
        (isClosedAny_restrict (hBc e) ((inf_le_left : chartDomain e O ⊓ chartDomain e V.1 ≤ _).trans (chartDomain_le e O)))
        (fun i z => ψ i (e.val.symm z)) (fun i => (hψ.chartPsh e i).mono inf_le_left) :=
    (relativeMassOn_compare_potentials B hBc (hW.potential V) hψ
      e inf_le_right inf_le_left).1.mp
      (relativeMassOn_chart_restrict B hBc (hW.pot V) V.1 (hW.potential V).psh
        (hW.potMass V) e inf_le_right)
  have hmψ : HasFiniteRelativeMass (restrict (chartDomain_le e O) (B.inChart e))
      (isPositive_restrict (B.isPositive e) (chartDomain_le e O))
      (isClosedAny_restrict (hBc e) (chartDomain_le e O))
      (fun i z => ψ i (e.val.symm z)) (hψ.chartPsh e) := by
    apply hasFiniteRelativeMass_of_cover (restrict (chartDomain_le e O) (B.inChart e))
      (isPositive_restrict (B.isPositive e) (chartDomain_le e O))
      (isClosedAny_restrict (hBc e) (chartDomain_le e O))
      (fun i z => ψ i (e.val.symm z)) (hψ.chartPsh e)
      (fun V : hW.cover => chartDomain e O ⊓ chartDomain e V.1) (fun _ => inf_le_left)
    · intro z hz
      obtain ⟨V,hzV⟩ := hW.chartDomain_cover e z hz.1
      exact mem_iUnion.mpr ⟨V,hz,hzV⟩
    · intro V
      simpa only [restrict_restrict] using hloc V
  refine ⟨hmψ, ?_⟩
  apply eq_of_local
  intro z hz
  obtain ⟨V,hzV⟩ := hW.chartDomain_cover e z hz.1
  refine ⟨chartDomain e O ⊓ chartDomain e V.1,inf_le_left,⟨hz,hzV⟩,?_⟩
  rw [restrict_restrict, ← restrict_restrict (inf_le_right : chartDomain e O ⊓ chartDomain e V.1 ≤ _)
    (chartDomain_le e V.1), hW.restrict_productInChart e V, localProduct,
    relativeProductOn_chart_restrict B hBc (hW.pot V) V.1 (hW.potential V).psh
      (hW.potMass V) e inf_le_right,
    restrict_relativeNonPluripolarProduct (restrict (chartDomain_le e O) (B.inChart e))
      (isPositive_restrict (B.isPositive e) (chartDomain_le e O))
      (isClosedAny_restrict (hBc e) (chartDomain_le e O))
      (fun i z => ψ i (e.val.symm z)) (hψ.chartPsh e) hmψ inf_le_left]
  simpa only [restrict_restrict] using
    (relativeMassOn_compare_potentials B hBc (hW.potential V) hψ
      e inf_le_right inf_le_left).2
      (relativeMassOn_chart_restrict B hBc (hW.pot V) V.1 (hW.potential V).psh
        (hW.potMass V) e inf_le_right) (hloc V)

end IsRelativeCurrentProductWellDefined
end SGPT.NPP.RelativeNonPluripolar

#check @SGPT.NPP.RelativeNonPluripolar.IsRelativeCurrentProductWellDefined
#check @SGPT.NPP.RelativeNonPluripolar.IsRelativeCurrentProductWellDefined.cover
#check @SGPT.NPP.RelativeNonPluripolar.IsRelativeCurrentProductWellDefined.cover_spec
#check @SGPT.NPP.RelativeNonPluripolar.IsRelativeCurrentProductWellDefined.pot
#check @SGPT.NPP.RelativeNonPluripolar.IsRelativeCurrentProductWellDefined.potential
#check @SGPT.NPP.RelativeNonPluripolar.IsRelativeCurrentProductWellDefined.potMass
#check @SGPT.NPP.RelativeNonPluripolar.IsRelativeCurrentProductWellDefined.localProduct
#check @SGPT.NPP.RelativeNonPluripolar.IsRelativeCurrentProductWellDefined.isPositive_localProduct
#check @SGPT.NPP.RelativeNonPluripolar.IsRelativeCurrentProductWellDefined.isCompatibleFamily
#check @SGPT.NPP.RelativeNonPluripolar.IsRelativeCurrentProductWellDefined.chartDomain_cover
#check @SGPT.NPP.RelativeNonPluripolar.IsRelativeCurrentProductWellDefined.exists_glue
#check @SGPT.NPP.RelativeNonPluripolar.IsRelativeCurrentProductWellDefined.productInChart
#check @SGPT.NPP.RelativeNonPluripolar.IsRelativeCurrentProductWellDefined.isPositive_productInChart
#check @SGPT.NPP.RelativeNonPluripolar.IsRelativeCurrentProductWellDefined.restrict_productInChart
#check @SGPT.NPP.RelativeNonPluripolar.IsRelativeCurrentProductWellDefined.productInChart_restrict
#print axioms SGPT.NPP.RelativeNonPluripolar.IsRelativeCurrentProductWellDefined
#print axioms SGPT.NPP.RelativeNonPluripolar.IsRelativeCurrentProductWellDefined.cover
#print axioms SGPT.NPP.RelativeNonPluripolar.IsRelativeCurrentProductWellDefined.cover_spec
#print axioms SGPT.NPP.RelativeNonPluripolar.IsRelativeCurrentProductWellDefined.pot
#print axioms SGPT.NPP.RelativeNonPluripolar.IsRelativeCurrentProductWellDefined.potential
#print axioms SGPT.NPP.RelativeNonPluripolar.IsRelativeCurrentProductWellDefined.potMass
#print axioms SGPT.NPP.RelativeNonPluripolar.IsRelativeCurrentProductWellDefined.localProduct
#print axioms SGPT.NPP.RelativeNonPluripolar.IsRelativeCurrentProductWellDefined.isPositive_localProduct
#print axioms SGPT.NPP.RelativeNonPluripolar.IsRelativeCurrentProductWellDefined.isCompatibleFamily
#print axioms SGPT.NPP.RelativeNonPluripolar.IsRelativeCurrentProductWellDefined.chartDomain_cover
#print axioms SGPT.NPP.RelativeNonPluripolar.IsRelativeCurrentProductWellDefined.exists_glue
#print axioms SGPT.NPP.RelativeNonPluripolar.IsRelativeCurrentProductWellDefined.productInChart
#print axioms SGPT.NPP.RelativeNonPluripolar.IsRelativeCurrentProductWellDefined.isPositive_productInChart
#print axioms SGPT.NPP.RelativeNonPluripolar.IsRelativeCurrentProductWellDefined.restrict_productInChart
#print axioms SGPT.NPP.RelativeNonPluripolar.IsRelativeCurrentProductWellDefined.productInChart_restrict

-- Close original EOF sections, then restore this fragment scope.
end
end OriginalFragment_06

-- Exact frozen body: RelativeCurrentFactorGlobalDraft
section OriginalFragment_07

/-! Genuine intrinsic relative products of ORIGINAL local current factors.
Every overlap, local mass, closedness and local-potential readback is proved. -/
set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff ENNReal Manifold

namespace SGPT.NPP.RelativeNonPluripolar
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere SGPT.Foundations.Analysis.Pending
open LocalProductCurrents LocalBedfordTaylorProducts LocalBedfordTaylorLocality
open LocalBedfordTaylorCalculus LocalCurrentL1Ddc LocalCurrentPullback LocalCurrentPullbackDdc
open SGPT.NPP.NonPluripolarCurrent

variable {m p r : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel (m + 1)) M]
  [IsManifold (𝓘(ℂ, ComplexModel (m + 1))) ∞ M]

namespace IsRelativeCurrentProductWellDefined
variable {B : PositiveCurrent (m + 1) M (r + p)} {hBc : B.IsClosed}
  {T : Fin p → PositiveCurrent (m + 1) M m} (hW : IsRelativeCurrentProductWellDefined B hBc T)

/-- Full genuine chart covariance of the MANUFACTURED local-current-factor
outputs. Original base compatibility and original closedness supply every
condition; no relative-output or closed-pullback certificate is supplied. -/
theorem productInChart_compatible (e f : ComplexChart (m + 1) M) :
    restrict (overlapSource_le e f) (hW.productInChart e) =
      pullback (chartTransition_isBiholomorphicPair e f)
        (isPositive_restrict (hW.isPositive_productInChart f) (overlapTarget_le e f)) := by
  have hh := chartTransition_isBiholomorphicPair e f
  apply eq_of_local
  intro z hz
  obtain ⟨U,hU,hzU⟩ := hW.cover_spec (e.val.symm z)
  let O : hW.cover := ⟨U,hU⟩
  let V : Opens (ComplexModel (m + 1)) := overlapTarget e f ⊓ chartDomain f U
  have hVB : V ≤ overlapTarget e f := inf_le_left
  have hτ : ∀ x ∈ overlapSource e f, f.val.symm (chartTransition e f x) = e.val.symm x := by
    intro x hx
    have hx' : x ∈ (chartTransition e f).source := hx
    have hxf : e.val.symm x ∈ f.val.source := by
      simp only [chartTransition, OpenPartialHomeomorph.trans_source,
        OpenPartialHomeomorph.symm_source, mem_inter_iff, mem_preimage] at hx'
      exact hx'.2
    simp only [chartTransition, OpenPartialHomeomorph.coe_trans, Function.comp_apply,
      f.val.left_inv hxf]
  have hpre : preOpen hh V ≤ chartDomain e U := by
    intro x hx
    refine ⟨overlapSource_le e f hx.1,?_⟩
    have h2 : f.val.symm (chartTransition e f x) ∈ U := hx.2.2.2
    rw [hτ x hx.1] at h2
    exact h2
  have hzpre : z ∈ preOpen hh V :=
    ⟨hz,hh.mapsTo hz,overlapTarget_le e f (hh.mapsTo hz),
      show f.val.symm (chartTransition e f z) ∈ U by rw [hτ z hz]; exact hzU⟩
  refine ⟨preOpen hh V,preOpen_le hh V,hzpre,?_⟩
  let RA := restrict (hpre.trans (chartDomain_le e U)) (B.inChart e)
  let RB := restrict ((inf_le_right : V ≤ chartDomain f U).trans (chartDomain_le f U)) (B.inChart f)
  have hRA : IsPositive RA := isPositive_restrict (B.isPositive e) _
  have hRB : IsPositive RB := isPositive_restrict (B.isPositive f) _
  have hRAc : IsClosedAny (r + p) RA := isClosedAny_restrict (hBc e) _
  have hRBc : IsClosedAny (r + p) RB := isClosedAny_restrict (hBc f) _
  let h' := isBiholomorphicPair_preOpen hh hVB
  have hbase : RA = pullback h' hRB := by
    calc
      RA = restrict (preOpen_le hh V) (restrict (overlapSource_le e f) (B.inChart e)) := by
        rw [restrict_restrict]
      _ = restrict (preOpen_le hh V) (pullback hh
          (isPositive_restrict (B.isPositive f) (overlapTarget_le e f))) :=
        congrArg (restrict (preOpen_le hh V)) (B.compatible e f)
      _ = pullback h' (isPositive_restrict
          (isPositive_restrict (B.isPositive f) (overlapTarget_le e f)) hVB) :=
        (pullback_restrict hh (isPositive_restrict (B.isPositive f) (overlapTarget_le e f)) hVB).symm
      _ = pullback h' hRB := pullback_congr_current h' _ _
        (restrict_restrict hVB (overlapTarget_le e f) (B.inChart f))
  have hmA := relativeMassOn_chart_restrict B hBc (hW.pot O) U (hW.potential O).psh
    (hW.potMass O) e hpre
  have hmB := relativeMassOn_chart_restrict B hBc (hW.pot O) U (hW.potential O).psh
    (hW.potMass O) f (inf_le_right : V ≤ chartDomain f U)
  let SA := relativeNonPluripolarProduct RA hRA hRAc (fun i x => hW.pot O i (e.val.symm x))
    (fun i => ((hW.potential O).chartPsh e i).mono hpre) hmA
  let SB := relativeNonPluripolarProduct RB hRB hRBc (fun i y => hW.pot O i (f.val.symm y))
    (fun i => ((hW.potential O).chartPsh f i).mono inf_le_right) hmB
  have hL : restrict (preOpen_le hh V) (restrict (overlapSource_le e f) (hW.productInChart e)) = SA.val := by
    rw [restrict_restrict, ← restrict_restrict hpre (chartDomain_le e U),
      hW.restrict_productInChart e O, localProduct,
      relativeProductOn_chart_restrict B hBc (hW.pot O) U (hW.potential O).psh
        (hW.potMass O) e hpre]
  have hRV : restrict hVB (restrict (overlapTarget_le e f) (hW.productInChart f)) = SB.val := by
    rw [restrict_restrict, ← restrict_restrict (inf_le_right : V ≤ chartDomain f U) (chartDomain_le f U),
      hW.restrict_productInChart f O, localProduct,
      relativeProductOn_chart_restrict B hBc (hW.pot O) U (hW.potential O).psh
        (hW.potMass O) f inf_le_right]
  have hpb : pullback h' SB.property = SA.val :=
    relative_product_pullback_of_base_compatible h' RB hRB hRBc RA hRA hRAc hbase
      (fun i y => hW.pot O i (f.val.symm y))
      (fun i => ((hW.potential O).chartPsh f i).mono inf_le_right)
      (fun i x => hW.pot O i (e.val.symm x))
      (fun i => ((hW.potential O).chartPsh e i).mono hpre)
      (fun i x hx => by rw [hτ x hx.1]) hmB hmA
  rw [hL, ← pullback_restrict hh _ hVB,
    pullback_congr_current h' _ SB.property hRV, hpb]

/-- Closedness of the actual glued chart current follows from its actual
closed local products and native locality of coefficient distribution derivatives. -/
theorem isClosed_productInChart (e : ComplexChart (m + 1) M) : IsClosedAny r (hW.productInChart e) := by
  apply isClosedAny_of_local
  intro z hz
  obtain ⟨O,hzO⟩ := hW.chartDomain_cover e z hz
  refine ⟨chartDomain e O.1,chartDomain_le e O.1,hzO,?_⟩
  rw [hW.restrict_productInChart e O, localProduct]
  exact isClosedAny_relativeNonPluripolarProduct (restrict (chartDomain_le e O.1) (B.inChart e))
    (isPositive_restrict (B.isPositive e) (chartDomain_le e O.1))
    (isClosedAny_restrict (hBc e) (chartDomain_le e O.1))
    (fun i z => hW.pot O i (e.val.symm z)) ((hW.potential O).chartPsh e) (hW.potMass O e)

end IsRelativeCurrentProductWellDefined

/-- The genuine intrinsic relative product of ORIGINAL current factors and
arbitrary closed positive base B, built from the actual original potential
cover and actual mass. Its output compatibility is entirely manufactured. -/
def relativeCurrentProduct (B : PositiveCurrent (m + 1) M (r + p)) (hBc : B.IsClosed)
    (T : Fin p → PositiveCurrent (m + 1) M m) (hW : IsRelativeCurrentProductWellDefined B hBc T) :
    PositiveCurrent (m + 1) M r where
  inChart := hW.productInChart
  isPositive := hW.isPositive_productInChart
  compatible := hW.productInChart_compatible

/-- Genuine closedness in EVERY base/output degree, not only top degree. -/
theorem isClosed_relativeCurrentProduct (B : PositiveCurrent (m + 1) M (r + p)) (hBc : B.IsClosed)
    (T : Fin p → PositiveCurrent (m + 1) M m) (hW : IsRelativeCurrentProductWellDefined B hBc T) :
    (relativeCurrentProduct B hBc T hW).IsClosed := hW.isClosed_productInChart

/-- EVERY original local potential tuple, independent of the chosen cover,
produces the actual local mass and reads back the SAME intrinsic relative
current. No output/current/equality/limit certificate is input. -/
theorem relativeCurrentProduct_restrict
    (B : PositiveCurrent (m + 1) M (r + p)) (hBc : B.IsClosed)
    (T : Fin p → PositiveCurrent (m + 1) M m) (hW : IsRelativeCurrentProductWellDefined B hBc T)
    {O : Opens M} {ψ : Fin p → M → EReal} (hψ : IsLocalPotential T O ψ) :
    ∃ hmψ : HasFiniteRelativeMassOn B hBc ψ O hψ.psh,
      ∀ e : ComplexChart (m + 1) M,
        restrict (chartDomain_le e O) ((relativeCurrentProduct B hBc T hW).inChart e) =
        (relativeNonPluripolarProduct (restrict (chartDomain_le e O) (B.inChart e))
          (isPositive_restrict (B.isPositive e) (chartDomain_le e O))
          (isClosedAny_restrict (hBc e) (chartDomain_le e O))
          (fun i z => ψ i (e.val.symm z)) (hψ.chartPsh e) (hmψ e)).val := by
  choose hm he using hW.productInChart_restrict hψ
  exact ⟨hm,he⟩

/-- Actual local defining products on ANY original potential cover determine
the intrinsic relative current uniquely; hence all cover/choice constructions agree. -/
theorem eq_relativeCurrentProduct
    (B : PositiveCurrent (m + 1) M (r + p)) (hBc : B.IsClosed)
    (T : Fin p → PositiveCurrent (m + 1) M m) (hW : IsRelativeCurrentProductWellDefined B hBc T)
    {S : PositiveCurrent (m + 1) M r} {C : Set (Opens M)}
    (hC : ∀ x : M, ∃ O ∈ C, x ∈ O) (ψ : (O : C) → Fin p → M → EReal)
    (hψ : ∀ O : C, IsLocalPotential T O.1 (ψ O))
    (hm : ∀ O : C, HasFiniteRelativeMassOn B hBc (ψ O) O.1 (hψ O).psh)
    (he : ∀ (O : C) (e : ComplexChart (m + 1) M),
      restrict (chartDomain_le e O.1) (S.inChart e) =
        (relativeNonPluripolarProduct (restrict (chartDomain_le e O.1) (B.inChart e))
          (isPositive_restrict (B.isPositive e) (chartDomain_le e O.1))
          (isClosedAny_restrict (hBc e) (chartDomain_le e O.1))
          (fun i z => ψ O i (e.val.symm z)) ((hψ O).chartPsh e) (hm O e)).val) :
    S = relativeCurrentProduct B hBc T hW := by
  ext1 e
  apply eq_of_local
  intro z hz
  obtain ⟨O,hO,hzO⟩ := hC (e.val.symm z)
  let V : C := ⟨O,hO⟩
  obtain ⟨_,hread⟩ := relativeCurrentProduct_restrict B hBc T hW (hψ V)
  exact ⟨chartDomain e O,chartDomain_le e O,⟨hz,hzO⟩,(he V e).trans (hread e).symm⟩

end SGPT.NPP.RelativeNonPluripolar

#check @SGPT.NPP.RelativeNonPluripolar.IsRelativeCurrentProductWellDefined.productInChart_compatible
#check @SGPT.NPP.RelativeNonPluripolar.IsRelativeCurrentProductWellDefined.isClosed_productInChart
#check @SGPT.NPP.RelativeNonPluripolar.relativeCurrentProduct
#check @SGPT.NPP.RelativeNonPluripolar.isClosed_relativeCurrentProduct
#check @SGPT.NPP.RelativeNonPluripolar.relativeCurrentProduct_restrict
#check @SGPT.NPP.RelativeNonPluripolar.eq_relativeCurrentProduct
#print axioms SGPT.NPP.RelativeNonPluripolar.IsRelativeCurrentProductWellDefined.productInChart_compatible
#print axioms SGPT.NPP.RelativeNonPluripolar.IsRelativeCurrentProductWellDefined.isClosed_productInChart
#print axioms SGPT.NPP.RelativeNonPluripolar.relativeCurrentProduct
#print axioms SGPT.NPP.RelativeNonPluripolar.isClosed_relativeCurrentProduct
#print axioms SGPT.NPP.RelativeNonPluripolar.relativeCurrentProduct_restrict
#print axioms SGPT.NPP.RelativeNonPluripolar.eq_relativeCurrentProduct

-- Close original EOF sections, then restore this fragment scope.
end
end OriginalFragment_07
