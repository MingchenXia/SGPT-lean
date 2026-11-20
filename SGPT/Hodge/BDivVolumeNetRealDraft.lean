import SGPT.Hodge.BDivVolumeNetDraft
import SGPT.Hodge.BDivChainReal

/-!
# Real-valued corollaries of `lma:volbdivnet`

This uses the dimension-uniform ENNReal net theorem. The conversion requires
genuine finiteness; it does not discard a
possible infinity using the totalized `ENNReal.toReal` convention. No extra
finite-volume premise is imposed on the source families.
-/

set_option autoImplicit false
noncomputable section
universe u

namespace SGPT.Hodge.BDivChain.NativeDraft.VolumeNetRealDraft

open Filter SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending
  SGPT.BDivisor SGPT.Hodge.BDivChain.NativeDraft.VolumeNetDraft
open scoped Topology ENNReal

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [CompactSpace X] [ConnectedSpace X]

/-- The real value of the already constructed actual b-divisor volume. -/
def volumeRealAny {S : ModelSystem n X} (D : WeilFamilyAny S) : ℝ :=
  (volumeAny D).toReal

/-- The real volume is nonnegative. -/
theorem volumeRealAny_nonneg {S : ModelSystem n X} (D : WeilFamilyAny S) :
    0 ≤ volumeRealAny D := ENNReal.toReal_nonneg

/-- The actual b-divisor volume is finite: in dimension zero it is one; in
positive dimension it is bounded by the finite volume on the root model. -/
theorem volumeAny_lt_top_blowup (hK : Nonempty (KahlerBackground n X))
    (D : WeilFamilyAny (ModelSystem.blowup n X)) : volumeAny D < ⊤ := by
  cases n with
  | zero =>
    rw [volumeAny_eq_one_of_dim_zero D]
    exact ENNReal.one_lt_top
  | succ m =>
    rw [volumeAny_eq_existing (Nat.succ_pos m) D]
    let π : (ModelSystem.blowup (m + 1) X).Model := ModelSystem.Model.root
    have : ConnectedSpace π.1.carrier := Modification.IsBlowupModel.connectedSpace π.2
    obtain ⟨κ⟩ := ModelSystem.blowup_nonempty_kahlerBackground hK π
    exact ((toExisting _ (Nat.succ_pos m) D).vol_le_classVolume π).trans_lt
      (SGPT.Hodge.BDivChain.classVolume_lt_top π.1 κ _)

/-- The real value recovers the original ENNReal volume; `toReal` is not
silently turning a possible infinity into zero. -/
theorem ofReal_volumeRealAny (hK : Nonempty (KahlerBackground n X))
    (D : WeilFamilyAny (ModelSystem.blowup n X)) :
    ENNReal.ofReal (volumeRealAny D) = volumeAny D :=
  ENNReal.ofReal_toReal (volumeAny_lt_top_blowup hK D).ne

/-- Every actual model class-volume in the book's blowup system is finite. -/
theorem modelClassVolume_lt_top_blowup (hK : Nonempty (KahlerBackground n X))
    (D : WeilFamilyAny (ModelSystem.blowup n X))
    (π : (ModelSystem.blowup n X).Model) :
    Modification.classVolume π.1 (D.val π) < ⊤ := by
  cases n with
  | zero =>
    rw [SGPT.Hodge.BDivChain.modelClassVolume_eq_one_of_dim_zero]
    exact ENNReal.one_lt_top
  | succ m =>
    have : ConnectedSpace π.1.carrier := Modification.IsBlowupModel.connectedSpace π.2
    obtain ⟨κ⟩ := ModelSystem.blowup_nonempty_kahlerBackground hK π
    exact SGPT.Hodge.BDivChain.classVolume_lt_top π.1 κ _

/-- The source model class-volume net converges to the b-divisor volume in
the real topology, uniformly in dimension. The given family is pseudo-effective. -/
theorem tendsto_realModelVolume_blowup (hK : Nonempty (KahlerBackground n X))
    (D : WeilFamilyAny (ModelSystem.blowup n X)) (hD : IsPseudoeffectiveAny D) :
    Tendsto (fun π : (ModelSystem.blowup n X).Model =>
      (Modification.classVolume π.1 (D.val π)).toReal) atTop (𝓝 (volumeRealAny D)) := by
  have hnet : Tendsto (fun π : (ModelSystem.blowup n X).Model =>
      Modification.classVolume π.1 (D.val π)) atTop (𝓝 (volumeAny D)) := by
    cases n with
    | zero => exact tendsto_bookModelVolume_zero D
    | succ m => exact tendsto_bookModelVolume_pos hK D hD
  exact (ENNReal.tendsto_toReal (volumeAny_lt_top_blowup hK D).ne).comp hnet

/-- A finite ENNReal limsup bound gives a genuine eventual finite bound, so
the real and ENNReal limsups agree. This is an arbitrary-filter statement. -/
theorem limsup_toReal_le_of_limsup_le {ι : Type*} (l : Filter ι) [l.NeBot]
    (u : ι → ℝ≥0∞) (a : ℝ≥0∞) (ha : a < ⊤)
    (hlim : limsup u l ≤ a) : limsup (fun i => (u i).toReal) l ≤ a.toReal := by
  obtain ⟨b, hab, hb⟩ := exists_between ha
  have hbound : ∀ᶠ i in l, u i ≤ b :=
    (eventually_lt_of_limsup_lt (hlim.trans_lt hab)).mono fun _ h => h.le
  have hlimtop : limsup u l ≠ ⊤ := (hlim.trans_lt ha).ne
  rw [ENNReal.limsup_toReal_eq hb.ne hbound]
  exact (ENNReal.toReal_le_toReal hlimtop ha.ne).mpr hlim

/-- The source limsup inequality as a genuine inequality in the real numbers. -/
theorem limsup_volumeRealAny_le_blowup (hK : Nonempty (KahlerBackground n X))
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {D : ι → WeilFamilyAny (ModelSystem.blowup n X)}
    {D₀ : WeilFamilyAny (ModelSystem.blowup n X)}
    (hD : ∀ i, IsPseudoeffectiveAny (D i)) (h : ConvergesAny l D D₀) :
    limsup (fun i => volumeRealAny (D i)) l ≤ volumeRealAny D₀ :=
  limsup_toReal_le_of_limsup_le l (fun i => volumeAny (D i)) (volumeAny D₀)
    (volumeAny_lt_top_blowup hK D₀) (limsup_volumeAny_le_blowup hK hD h)

/-- The source decreasing-net convergence in the real topology. -/
theorem tendsto_volumeRealAny_of_antitone_blowup (hK : Nonempty (KahlerBackground n X))
    {ι : Type*} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    {D : ι → WeilFamilyAny (ModelSystem.blowup n X)}
    {D₀ : WeilFamilyAny (ModelSystem.blowup n X)}
    (hD : ∀ i, IsPseudoeffectiveAny (D i))
    (hanti : ∀ i j, i ≤ j → LEAny (D j) (D i))
    (h : ConvergesAny atTop D D₀) :
    Tendsto (fun i => volumeRealAny (D i)) atTop (𝓝 (volumeRealAny D₀)) :=
  (ENNReal.tendsto_toReal (volumeAny_lt_top_blowup hK D₀).ne).comp
    (tendsto_volumeAny_of_antitone_blowup hK hD hanti h)

end SGPT.Hodge.BDivChain.NativeDraft.VolumeNetRealDraft
