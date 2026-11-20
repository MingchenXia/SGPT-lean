import SGPT.Foundations.Analysis.Pending.SingularModelEnergyConcavity

set_option autoImplicit false

/-!
# Genuine singular same-type diamond paths

Xia SGPT PDF0137, Corollary 3.1.7. The affine path uses actual extended
potentials, retaining common negative-infinity poles. Its upper maximum
and lower actual rooftop are genuine same-type potentials. The upper
increments and bounded integrable positive canonical gap feed the actual
path estimates, without bounded potentials or a target diamond premise.
-/

open Set Filter MeasureTheory

namespace SGPT.Foundations.Analysis.Pending.SingularModelEnergyDiamondPaths

open FirstPass FirstPass.PositiveClasses RelativeEnergy RelativeEnergyIntegrability
  SingularModelEnergyConcavity GlobalNonPluripolar ThetaPshConvexCombination

noncomputable section

/-- The genuine extended affine path, with common poles retained. -/
def path {X : Type*} (u v : X → EReal) (t : ℝ) : X → EReal := convexComb (1 - t) u v

/-- The upper diamond path. -/
def upperPath {X : Type*} (u v : X → EReal) (t : ℝ) : X → EReal :=
  fun x => max (u x) (path u v t x)

/-- The actual lower rooftop path. -/
def lowerPath {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    (θ : ClosedRealOneOneForm n M) (u v : M → EReal) (t : ℝ) : M → EReal :=
  rooftopEnvelope θ.val (fun x => min (path u v t x) (v x))

/-- The affine path starts at the genuine extended first endpoint. -/
theorem path_zero {X : Type*} (u v : X → EReal) : path u v 0 = u := by
  funext x
  simp [path, convexComb]

/-- The affine path ends at the genuine extended second endpoint. -/
theorem path_one {X : Type*} (u v : X → EReal) : path u v 1 = v := by
  funext x
  simp [path, convexComb]

/-- Away from poles, the upper extended path has its ordinary real affine form. -/
theorem upperPath_coe {X : Type*} {u v : X → EReal} {x : X} {a b : ℝ}
    (hua : u x = (a : EReal)) (hvb : v x = (b : EReal)) {t : ℝ} (ht : 0 ≤ t) :
    upperPath u v t x = ((a + t * max (b - a) 0 : ℝ) : EReal) := by
  simp only [upperPath, path, convexComb, hua, hvb]
  rw [← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add,
    ← EReal.coe_strictMono.monotone.map_max]
  congr 1
  rcases le_total a b with hab | hab
  · rw [max_eq_left (sub_nonneg.mpr hab), max_eq_right (by nlinarith)]
    ring
  · rw [max_eq_right (sub_nonpos.mpr hab), max_eq_left (by nlinarith)]
    ring

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Genuine same-type endpoints produce a genuine same-type affine path. -/
theorem relativeEInfinity_path {θ : ClosedRealOneOneForm n M} {φ u v : M → EReal}
    (hu : RelativeEInfinity θ φ u) (hv : RelativeEInfinity θ φ v)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : RelativeEInfinity θ φ (path u v t) := by
  rcases eq_or_lt_of_le ht.1 with hzero | hpos
  · rw [← hzero, path_zero]
    exact hu
  · rcases eq_or_lt_of_le ht.2 with hone | hless
    · rw [hone, path_one]
      exact hv
    · exact ⟨isThetaPshPotential_convexComb hu.1 hv.1 (by linarith) (by linarith),
        sameSingularityTypeOn_convexComb hu.2 hv.2 (by linarith) (by linarith)⟩

/-- The actual maximum path is genuine and retains the common reference type. -/
theorem relativeEInfinity_upperPath {θ : ClosedRealOneOneForm n M} {φ u v : M → EReal}
    (hu : RelativeEInfinity θ φ u) (hv : RelativeEInfinity θ φ v)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : RelativeEInfinity θ φ (upperPath u v t) := by
  have hf := relativeEInfinity_path hu hv ht
  refine ⟨IsThetaPshPotential.max hu.1 hf.1, ?_⟩
  exact ⟨DominationPrincipleReduction.moreSingularOn_max hu.2.1 hf.2.1,
    hu.2.2.trans (MoreSingularOn.of_le fun x _ => le_max_left _ _)⟩

/-- The actual upper-path canonical increment keeps the real affine identity
at common poles as well as at finite endpoints. -/
theorem canonicalDiff_upperPath {θ : ClosedRealOneOneForm n M} {φ u v : M → EReal}
    (hu : RelativeEInfinity θ φ u) (hv : RelativeEInfinity θ φ v)
    {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) (x : M) :
    canonicalERealDiffToReal (upperPath u v t x) (upperPath u v s x) =
      (t - s) * max (canonicalERealDiffToReal (v x) (u x)) 0 := by
  have hAt := relativeEInfinity_upperPath hu hv ht
  have hAs := relativeEInfinity_upperPath hu hv hs
  have huv := hu.2.trans hv.2.symm
  by_cases hux : u x = ⊥
  · have hφx : φ x = ⊥ := (sameSingularityTypeOn_eq_bot_iff hu.2 (mem_univ x)).mp hux
    have hvx : v x = ⊥ := (sameSingularityTypeOn_eq_bot_iff huv (mem_univ x)).mp hux
    have hAtx : upperPath u v t x = ⊥ :=
      (sameSingularityTypeOn_eq_bot_iff hAt.2 (mem_univ x)).mpr hφx
    have hAsx : upperPath u v s x = ⊥ :=
      (sameSingularityTypeOn_eq_bot_iff hAs.2 (mem_univ x)).mpr hφx
    simp [hAtx, hAsx, hvx, hux]
  · have hvx : v x ≠ ⊥ := fun h =>
      hux ((sameSingularityTypeOn_eq_bot_iff huv (mem_univ x)).mpr h)
    have eu := (EReal.coe_toReal (hu.1.1.quasiPlurisubharmonic.ne_top x) hux).symm
    have ev := (EReal.coe_toReal (hv.1.1.quasiPlurisubharmonic.ne_top x) hvx).symm
    rw [upperPath_coe eu ev ht.1, upperPath_coe eu ev hs.1, ev, eu,
      canonicalERealDiffToReal_coe_coe, canonicalERealDiffToReal_coe_coe]
    simp only [EReal.toReal_coe]
    ring

variable [CompactSpace M]

/-- Actual same-type rooftop regularity produces the genuine lower path;
its regularity and type are conclusions, rather than extra path premises. -/
theorem relativeEInfinity_lowerPath [Nonempty M] {θ : ClosedRealOneOneForm n M}
    {φ u v : M → EReal} (hφ : IsThetaPshPotential θ.val φ)
    (hu : RelativeEInfinity θ φ u) (hv : RelativeEInfinity θ φ v)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : RelativeEInfinity θ φ (lowerPath θ u v t) := by
  have hf := relativeEInfinity_path hu hv ht
  simpa only [lowerPath, EReal.coe_zero, add_zero] using
    relativeEInfinity_rooftop_add_const_of_sameSingularityType
      θ φ (path u v t) v hφ hf.1 hv.1 hf.2 hv.2 0

variable [MeasurableSpace M] [BorelSpace M]

/-- The actual positive canonical endpoint gap is integrable against every
actual mixed measure, even for singular same-type endpoints and slots. -/
theorem integrable_positivePart_canonicalDiff (omega : KahlerBackground n M)
    {θ : ClosedRealOneOneForm n M} {φ u v : M → EReal}
    (hu : RelativeEInfinity θ φ u) (hv : RelativeEInfinity θ φ v)
    {η : Fin n → ClosedRealOneOneForm n M} {ψ : Fin n → M → EReal}
    (hψ : ∀ i, ThetaPlurisubharmonic (η i).val (ψ i)) :
    Integrable (fun x => max (canonicalERealDiffToReal (v x) (u x)) 0)
      (globalMixedMeasure η ψ hψ) :=
  (integrable_canonicalDiff_globalMixedMeasure omega hv.1.1 hu.1.1
    (hv.2.trans hu.2.symm) hψ).pos_part

end

end SGPT.Foundations.Analysis.Pending.SingularModelEnergyDiamondPaths
