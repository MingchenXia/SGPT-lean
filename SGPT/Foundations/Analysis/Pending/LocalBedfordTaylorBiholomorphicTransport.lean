import SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorBiholomorphicProducts
import SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorCanonicalTraceMeasure

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff

namespace SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorBiholomorphicTransport

open FirstPass FirstPass.MongeAmpere FirstPass.MixedMongeAmpere
  LocalProductCurrents LocalBedfordTaylorProducts LocalBedfordTaylorSmooth
  LocalBedfordTaylorLocality LocalBedfordTaylorDecreasing LocalBedfordTaylorSmoothTraceMeasure
  LocalCurrentPullback LocalCurrentPullbackDdc BedfordTaylor
  LocalBedfordTaylorCanonicalTraceMeasure

variable {n q r : ℕ} {A B : Opens (ComplexModel n)}
  {τ σ : ComplexModel n → ComplexModel n}

private theorem reverse_biholomorphic (h : IsBiholomorphicPair A B τ σ) :
    IsBiholomorphicPair B A σ τ where
  holo := h.holo_inv
  holo_inv := h.holo
  mapsTo := h.mapsTo_inv
  mapsTo_inv := h.mapsTo
  left_inv := h.right_inv
  right_inv := h.left_inv

private theorem locallyBounded_comp (h : IsBiholomorphicPair A B τ σ)
    {w : ComplexModel n → ℝ} (hw : IsLocallyBoundedPshOn B w) :
    IsLocallyBoundedPshOn A (fun x => w (τ x)) := by
  refine ⟨HolomorphicPullback.plurisubharmonicOn_comp_holomorphic
    (u := fun z => (w z : EReal)) A.isOpen
    (h.holo.differentiableOn (by simp)) h.mapsTo hw.1, fun z hz => ?_⟩
  obtain ⟨V, hzV, hVB, C, hC⟩ := hw.2 (τ z) (h.mapsTo hz)
  exact ⟨preOpen h V, ⟨hz, hzV⟩, preOpen_le h V, C, fun x hx => hC (τ x) hx.2⟩

/-- The actual inverse-map pullback is the pushforward of the original
bounded recursive product, in every degree. All geometric/PSH witnesses are produced. -/
theorem inverse_pullback_btProduct (hdegree : r + q = n)
    (h : IsBiholomorphicPair A B τ σ) {u : Fin q → ComplexModel n → ℝ}
    (hu : ∀ i, IsLocallyBoundedPshOn B (u i)) :
    ∃ (hrev : IsBiholomorphicPair B A σ τ)
      (huA : ∀ i, IsLocallyBoundedPshOn A (fun x => u i (τ x))),
      pullback hrev (isPositive_btProduct q r (fun i x => u i (τ x))
        (oneCurrentOf (U := A) hdegree) (isPositive_oneCurrentOf hdegree)
        (isClosedAny_oneCurrentOf hdegree) huA).1 =
      btProduct q r u (oneCurrentOf (U := B) hdegree) := by
  let hrev := reverse_biholomorphic h
  let huA : ∀ i, IsLocallyBoundedPshOn A (fun x => u i (τ x)) :=
    fun i => locallyBounded_comp h (hu i)
  refine ⟨hrev, huA, ?_⟩
  rw [LocalBedfordTaylorBiholomorphicProducts.pullback_btProduct hdegree hrev huA]
  exact btProduct_congr q r _ u (oneCurrentOf hdegree)
    fun i y hy => by rw [h.right_inv y hy]

/-- Top-degree actual recursive traces are the canonical mixed measures,
and the restricted-domain pushforward is literally the target canonical measure. -/
theorem canonicalMixedMeasure_pushforward (h : IsBiholomorphicPair A B τ σ)
    {u : Fin n → ComplexModel n → ℝ} (hu : IsLocallyBoundedMixedPshOn B u) :
    ∃ huA : IsLocallyBoundedMixedPshOn A (fun i x => u i (τ x)),
      MixedMongeAmpere.canonicalMixedBedfordTaylorMeasure A (fun i x => u i (τ x)) huA =
        recursiveMixedTraceMeasure A (fun i x => u i (τ x)) huA ∧
      MixedMongeAmpere.canonicalMixedBedfordTaylorMeasure B u hu =
        recursiveMixedTraceMeasure B u hu ∧
      ((MixedMongeAmpere.canonicalMixedBedfordTaylorMeasure A
        (fun i x => u i (τ x)) huA).restrict (A : Set (ComplexModel n))).map τ =
        MixedMongeAmpere.canonicalMixedBedfordTaylorMeasure B u hu := by
  let huA : IsLocallyBoundedMixedPshOn A (fun i x => u i (τ x)) :=
    fun i => locallyBounded_comp h (hu i)
  refine ⟨huA, canonicalMixedBedfordTaylorMeasure_eq_recursiveMixedTraceMeasure huA,
    canonicalMixedBedfordTaylorMeasure_eq_recursiveMixedTraceMeasure hu, ?_⟩
  have hlimA := BedfordTaylor.IsLocalMixedBedfordTaylorMeasure.isBTLimit
    (MixedMongeAmpere.canonicalMixedBedfordTaylorMeasure_spec A
      (fun i x => u i (τ x)) huA)
  have hpush := hlimA.comp_biholomorphic (reverse_biholomorphic h)
  have hpush' : IsBTLimit B u
      (((MixedMongeAmpere.canonicalMixedBedfordTaylorMeasure A
        (fun i x => u i (τ x)) huA).restrict (A : Set (ComplexModel n))).map τ) :=
    hpush.congr fun i y hy => by
      change u i (τ (σ y)) = u i y
      rw [h.right_inv y hy]
  exact hpush'.unique (BedfordTaylor.IsLocalMixedBedfordTaylorMeasure.isBTLimit
    (MixedMongeAmpere.canonicalMixedBedfordTaylorMeasure_spec B u hu))

end SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorBiholomorphicTransport
