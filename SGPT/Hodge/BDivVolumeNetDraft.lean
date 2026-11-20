import SGPT.Hodge.BDivChainZeroSourceVolumeDraft
import SGPT.Hodge.BDivChainZeroNefDraft
import SGPT.Hodge.BDivCone

/-!
# `lma:volbdivnet` in the dimension-uniform actual model-family API

The source uses actual model classes and modelwise Euclidean
convergence. `WeilFamilyAny` is the existing dimension-uniform compatible
family of such classes. In dimension zero every model class volume is one;
in positive dimension the proofs are transported to the existing results.
The model system follows the compact `def:modif` finite-blowup convention.
No cofinality assertion for arbitrary analytic modifications is made here.
-/

set_option autoImplicit false
noncomputable section
universe u

namespace SGPT.Hodge.BDivChain.NativeDraft.VolumeNetDraft

open Filter SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending
  SGPT.BDivisor
open scoped Topology ENNReal

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [CompactSpace X] [ConnectedSpace X]

/-- The source modelwise order, with the actual pseudo-effective cone. -/
def LEAny {S : ModelSystem n X} (D E : WeilFamilyAny S) : Prop :=
  ∀ π : S.Model, ClassPseudoeffectiveViaPotentials (E.val π - D.val π)

omit [ConnectedSpace X] in
/-- Compatibility with the previously defined positive-dimensional modelwise
convergence, on exactly the same family and the same models. -/
theorem convergesAny_iff_existing {S : ModelSystem n X} (hn : 0 < n)
    {ι : Type*} (l : Filter ι) (D : ι → WeilFamilyAny S) (D₀ : WeilFamilyAny S) :
    ConvergesAny l D D₀ ↔
      WeilBDivisorOn.Converges l (fun i => toExisting S hn (D i)) (toExisting S hn D₀) := by
  simp only [ConvergesAny, WeilBDivisorOn.Converges, toExisting_onModel]

omit [ConnectedSpace X] in
/-- Compatibility with the previously defined positive-dimensional order. -/
theorem leAny_iff_existing {S : ModelSystem n X} (hn : 0 < n)
    (D E : WeilFamilyAny S) :
    LEAny D E ↔ (toExisting S hn D).LE (toExisting S hn E) := by
  simp only [LEAny, WeilBDivisorOn.LE, toExisting_onModel]

/-- Dimension zero: every actual model-family volume equals one, hence every
family of volumes converges, independently of monotonicity. -/
theorem tendsto_volumeAny_zero {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel 0) X] [IsComplexManifold 0 X]
    [CompactSpace X] [ConnectedSpace X] {S : ModelSystem 0 X}
    {ι : Type*} (l : Filter ι) (D : ι → WeilFamilyAny S) (D₀ : WeilFamilyAny S) :
    Tendsto (fun i => volumeAny (D i)) l (𝓝 (volumeAny D₀)) := by
  simp only [volumeAny_eq_one_of_dim_zero]
  exact tendsto_const_nhds

/-- In particular, the book's limsup bound holds in dimension zero, for any
nontrivial filter, without adding surrogate models or a volume assumption. -/
theorem limsup_volumeAny_le_zero {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel 0) X] [IsComplexManifold 0 X]
    [CompactSpace X] [ConnectedSpace X] {S : ModelSystem 0 X}
    {ι : Type*} (l : Filter ι) [l.NeBot] (D : ι → WeilFamilyAny S) (D₀ : WeilFamilyAny S) :
    limsup (fun i => volumeAny (D i)) l ≤ volumeAny D₀ :=
  (tendsto_volumeAny_zero l D D₀).limsup_eq.le

/-- `lma:volbdivnet`, first observation: an arbitrary nontrivially
convergent family of pseudo-effective b-divisors has pseudo-effective limit. -/
theorem isPseudoeffectiveAny_of_converges_blowup
    (hK : Nonempty (KahlerBackground n X))
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {D : ι → WeilFamilyAny (ModelSystem.blowup n X)}
    {D₀ : WeilFamilyAny (ModelSystem.blowup n X)}
    (hD : ∀ i, IsPseudoeffectiveAny (D i)) (h : ConvergesAny l D D₀) :
    IsPseudoeffectiveAny D₀ := by
  cases n with
  | zero => exact isPseudoeffectiveAny_of_dim_zero D₀
  | succ m =>
    have hp : ∀ i, (toExisting _ (Nat.succ_pos m) (D i)).IsPseudoeffective :=
      fun i => (isPseudoeffectiveAny_iff_existing (Nat.succ_pos m) (D i)).mp (hD i)
    have hc := (convergesAny_iff_existing (Nat.succ_pos m) l D D₀).mp h
    exact (isPseudoeffectiveAny_iff_existing (Nat.succ_pos m) D₀).mpr
      (WeilBDivisorOn.isPseudoeffective_of_converges_blowup hK hp hc)

/-- `lma:volbdivnet` limsup bound, over the existing finite-composite blowup
system, in every dimension. -/
theorem limsup_volumeAny_le_blowup (hK : Nonempty (KahlerBackground n X))
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {D : ι → WeilFamilyAny (ModelSystem.blowup n X)}
    {D₀ : WeilFamilyAny (ModelSystem.blowup n X)}
    (hD : ∀ i, IsPseudoeffectiveAny (D i)) (h : ConvergesAny l D D₀) :
    limsup (fun i => volumeAny (D i)) l ≤ volumeAny D₀ := by
  cases n with
  | zero => exact limsup_volumeAny_le_zero l D D₀
  | succ m =>
    have hp : ∀ i, (toExisting _ (Nat.succ_pos m) (D i)).IsPseudoeffective :=
      fun i => (isPseudoeffectiveAny_iff_existing (Nat.succ_pos m) (D i)).mp (hD i)
    have hc := (convergesAny_iff_existing (Nat.succ_pos m) l D D₀).mp h
    simpa only [volumeAny_eq_existing (Nat.succ_pos m)] using
      (WeilBDivisorOn.limsup_vol_le_blowup hK hp hc)

/-- `lma:volbdivnet` decreasing-net conclusion, over the same actual
finite-composite blowup system and in every dimension. -/
theorem tendsto_volumeAny_of_antitone_blowup (hK : Nonempty (KahlerBackground n X))
    {ι : Type*} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    {D : ι → WeilFamilyAny (ModelSystem.blowup n X)}
    {D₀ : WeilFamilyAny (ModelSystem.blowup n X)}
    (hD : ∀ i, IsPseudoeffectiveAny (D i))
    (hanti : ∀ i j, i ≤ j → LEAny (D j) (D i))
    (h : ConvergesAny atTop D D₀) :
    Tendsto (fun i => volumeAny (D i)) atTop (𝓝 (volumeAny D₀)) := by
  cases n with
  | zero => exact tendsto_volumeAny_zero atTop D D₀
  | succ m =>
    have hp : ∀ i, (toExisting _ (Nat.succ_pos m) (D i)).IsPseudoeffective :=
      fun i => (isPseudoeffectiveAny_iff_existing (Nat.succ_pos m) (D i)).mp (hD i)
    have ha : ∀ i j, i ≤ j → (toExisting _ (Nat.succ_pos m) (D j)).LE
        (toExisting _ (Nat.succ_pos m) (D i)) := by
      intro i j hij
      exact (leAny_iff_existing (Nat.succ_pos m) _ _).mp (hanti i j hij)
    have hc := (convergesAny_iff_existing (Nat.succ_pos m) atTop D D₀).mp h
    simpa only [volumeAny_eq_existing (Nat.succ_pos m)] using
      (WeilBDivisorOn.tendsto_vol_of_antitone_blowup hK hp ha hc)

end SGPT.Hodge.BDivChain.NativeDraft.VolumeNetDraft
