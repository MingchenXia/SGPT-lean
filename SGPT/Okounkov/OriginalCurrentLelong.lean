import SGPT.Foundations.Analysis.Pending.FullPositiveCurrentLocalPshPotential
import SGPT.Foundations.Analysis.Pending.ActualOriginalPotentialOverlapSmoothDifference
import SGPT.Foundations.Analysis.Pending.LelongChartReaderInvariance
import SGPT.Foundations.Analysis.Pending.SquaredLogLelongSourceNormalization

set_option autoImplicit false

noncomputable section
open Set Filter Metric MeasureTheory TopologicalSpace
open scoped Topology ContDiff Distributions Manifold ENNReal

namespace SGPT.Okounkov

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending CanonicalCurrentFrame GlobalPositiveCurrentACRestriction
open ActualQuasiPshPotentialSmoothCompatibility ActualOriginalPotentialOverlapSmoothDifference
open _root_.SGPT.Foundations.Analysis.LocalCurrents

/-- True AE finiteness supplies a non-bottom value in every genuine open
neighborhood, including zero-dimensional Euclidean space. -/
private theorem localQuasiPsh_of_psh_ae_finite {n : ℕ}
    {U : Opens (ComplexModel n)} {u : ComplexModel n → EReal}
    (hu : PlurisubharmonicOn u U)
    (hfin : ∀ᵐ z ∂volume.restrict U, u z ≠ ⊤ ∧ u z ≠ ⊥) :
    LocalQuasiPshPotentialOn u U := by
  refine ⟨U.isOpen, fun x hx => (hu x hx).quasiPlurisubharmonicAt, ?_⟩
  intro x hx V hV hxV
  have hpos : volume ((U : Set (ComplexModel n)) ∩ V) ≠ 0 :=
    ((U.isOpen.inter hV).measure_pos volume ⟨x, hx, hxV⟩).ne'
  obtain ⟨y, hy, hfy⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hpos
    (ae_restrict_of_ae_restrict_of_subset inter_subset_left hfin)
  exact ⟨y, hy, hfy.2⟩

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

private theorem coordinate_lelong_reader_eq
    (e : ComplexChart (m + 1) M) (u : ComplexModel (m + 1) → EReal)
    {p : M} (hp : p ∈ e.val.source) :
    lelongNumber (n := m + 1) u (e.val p) =
      lelongNumber (n := m + 1) (fun y => u (e.val y)) p := by
  have hgerm : chartFunction (fun y => u (e.val y)) e =ᶠ[𝓝 (e.val p)] u := by
    filter_upwards [e.val.open_target.mem_nhds (e.val.map_source hp)] with z hz
    change u (e.val (e.val.symm z)) = u z
    rw [e.val.right_inv hz]
  exact (LelongNumberComparison.lelongNumber_congr hgerm).symm.trans
    (LelongChartReaderInvariance.lelongNumber_chartFunction_eq e hp)

/-- Main's complete smooth compatibility applies to genuine original
potentials, without its later analytic-current atlas hypothesis. -/
private theorem original_current_local_readers_eq
    (T : GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m)))
    (e f : ComplexChart (m + 1) M) {U V : Opens (ComplexModel (m + 1))}
    (hU : U ≤ chartTarget e) (hV : V ≤ chartTarget f)
    {u v : ComplexModel (m + 1) → EReal}
    (hu : LocalQuasiPshPotentialOn u U) (hv : LocalQuasiPshPotentialOn v V)
    (hreadu : ∀ (w : Fin 2 → ComplexModel (m + 1)) (φ : 𝓓(U, ℝ)),
      T.coefficients (canonicalBasis (m + 1)) e w (TestFunction.monoCLM ℝ φ) =
        ddC (regularLocalQuasiPsh hu) w φ)
    (hreadv : ∀ (w : Fin 2 → ComplexModel (m + 1)) (φ : 𝓓(V, ℝ)),
      T.coefficients (canonicalBasis (m + 1)) f w (TestFunction.monoCLM ℝ φ) =
        ddC (regularLocalQuasiPsh hv) w φ)
    {p : M} (hpe : p ∈ e.val.source) (hpf : p ∈ f.val.source)
    (hpu : e.val p ∈ U) (hpv : f.val p ∈ V) :
    lelongNumber (n := m + 1) u (e.val p) =
      lelongNumber (n := m + 1) v (f.val p) := by
  let F := chartTransition e f
  have hcore : e.val p ∈ (U : Set _) ∩ (F.source ∩ F ⁻¹' V) := by
    refine ⟨hpu, ?_, ?_⟩
    · change e.val p ∈ e.val.target ∩ e.val.symm ⁻¹' f.val.source
      refine ⟨e.val.map_source hpe, ?_⟩
      change e.val.symm (e.val p) ∈ f.val.source
      rwa [e.val.left_inv hpe]
    · change f.val (e.val.symm (e.val p)) ∈ V
      simpa only [e.val.left_inv hpe] using hpv
  obtain ⟨_huU, _hvF, _heq, hdiff⟩ :=
    exists_original_chart_smooth_difference T e f hU hV hu hv hreadu hreadv
  obtain ⟨W, _hWU, h, hxW, hsm, _hh, heq, _hreg, _hlevi⟩ := hdiff (e.val p) hcore
  have hgerm : (fun y => u (e.val y)) =ᶠ[𝓝 p]
      (fun y => v (f.val y) + (h (e.val y) : EReal)) := by
    filter_upwards [(e.val.isOpen_inter_preimage W.isOpen).mem_nhds ⟨hpe, hxW⟩]
      with y hy
    have hz := heq hy.2
    change u (e.val y) = v (f.val (e.val.symm (e.val y))) + (h (e.val y) : EReal) at hz
    simpa only [e.val.left_inv hy.1] using hz
  have hc : ContinuousAt (fun y => h (e.val y)) p :=
    hsm.continuous.continuousAt.comp (e.val.continuousAt hpe)
  exact (coordinate_lelong_reader_eq e u hpe).trans
    ((LelongNumberComparison.lelongNumber_congr hgerm).trans
      ((LelongChartReaderInvariance.lelongNumber_add_continuous_eq hc).trans
        (coordinate_lelong_reader_eq f v hpf).symm))

/-- Every original closed fully positive current has a unique literal native
point reader. All genuine original local potentials are allowed; no analytic
singularity, chosen atlas, local-potential or reader certificate is assumed. -/
theorem exists_unique_original_full_positive_current_lelong_reader
    (T : GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m)))
    (hclosed : T.IsClosed (canonicalBasis (m + 1)))
    (h11 : T.IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m))
    (hT : IsFullPositive T) :
    ∃! ν : M → ℝ≥0∞,
      ∀ (e : ComplexChart (m + 1) M) (U : Opens (ComplexModel (m + 1)))
        (_hU : U ≤ chartTarget e) (u : ComplexModel (m + 1) → EReal)
        (hu : LocalQuasiPshPotentialOn u U),
        (∀ (w : Fin 2 → ComplexModel (m + 1)) (φ : 𝓓(U, ℝ)),
          T.coefficients (canonicalBasis (m + 1)) e w (TestFunction.monoCLM ℝ φ) =
            ddC (regularLocalQuasiPsh hu) w φ) →
        ∀ p ∈ e.val.source, e.val p ∈ U →
          ν p = lelongNumber (n := m + 1) u (e.val p) := by
  classical
  have hex (p : M) : ∃ (e : ComplexChart (m + 1) M)
      (U : Opens (ComplexModel (m + 1))) (_hU : U ≤ chartTarget e)
      (u : ComplexModel (m + 1) → EReal) (hu : LocalQuasiPshPotentialOn u U),
      p ∈ e.val.source ∧ e.val p ∈ U ∧
        ∀ (w : Fin 2 → ComplexModel (m + 1)) (φ : 𝓓(U, ℝ)),
          T.coefficients (canonicalBasis (m + 1)) e w (TestFunction.monoCLM ℝ φ) =
            ddC (regularLocalQuasiPsh hu) w φ := by
    let e := complexChartAt (n := m + 1) p
    have hp : p ∈ e.val.source := mem_complexChartAt_source p
    obtain ⟨U, hU, u, hpU, hpsh, hfin, hL, hcurrent⟩ :=
      FullPositiveCurrentLocalPshPotential.exists_local_psh_potential_of_full_positive
        volume T hclosed h11 hT e (e.val p) (e.val.map_source hp)
    let hu := localQuasiPsh_of_psh_ae_finite hpsh hfin
    refine ⟨e, U, hU, u, hu, hp, hpU, ?_⟩
    intro w φ
    have heq := congrArg (fun A => A w φ) hcurrent
    exact heq.symm
  choose e U hU u hu hsrc hmem hread using hex
  let ν : M → ℝ≥0∞ := fun p => lelongNumber (n := m + 1) (u p) ((e p).val p)
  refine ⟨ν, ?_, ?_⟩
  · intro f V hV v hv hr p hpf hpv
    exact original_current_local_readers_eq T (e p) f (hU p) hV (hu p) hv
      (hread p) hr (hsrc p) hpf (hmem p) hpv
  · intro μ hμ
    funext p
    exact hμ (e p) (U p) (hU p) (u p) (hu p) (hread p) p (hsrc p) (hmem p)

/-- The actual source squared-log normalization gives a unique current
reader for every original full positive current. Infinite point values and
arbitrary genuine native local potentials are retained. -/
theorem exists_unique_original_full_positive_current_source_reader
    (T : GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m)))
    (hclosed : T.IsClosed (canonicalBasis (m + 1)))
    (h11 : T.IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m))
    (hT : IsFullPositive T) :
    ∃! μ : M → ℝ≥0∞,
      ∀ (e : ComplexChart (m + 1) M) (U : Opens (ComplexModel (m + 1)))
        (_hU : U ≤ chartTarget e) (u : ComplexModel (m + 1) → EReal)
        (hu : LocalQuasiPshPotentialOn u U),
        (∀ (w : Fin 2 → ComplexModel (m + 1)) (φ : 𝓓(U, ℝ)),
          T.coefficients (canonicalBasis (m + 1)) e w (TestFunction.monoCLM ℝ φ) =
            ddC (regularLocalQuasiPsh hu) w φ) →
        ∀ p ∈ e.val.source, e.val p ∈ U →
          μ p = SquaredLogLelongSourceNormalization.squaredLogLelongNumber
            (n := m + 1) u (e.val p) := by
  obtain ⟨ν, hν, huniq⟩ :=
    exists_unique_original_full_positive_current_lelong_reader T hclosed h11 hT
  let μ : M → ℝ≥0∞ := fun p => (2 : ℝ≥0∞)⁻¹ * ν p
  have htwo : (2 : ℝ≥0∞)⁻¹ * 2 = 1 :=
    ENNReal.inv_mul_cancel (by norm_num) (by norm_num)
  have hμ : ∀ (e : ComplexChart (m + 1) M) (U : Opens (ComplexModel (m + 1)))
      (hU : U ≤ chartTarget e) (u : ComplexModel (m + 1) → EReal)
      (hu : LocalQuasiPshPotentialOn u U),
      (∀ (w : Fin 2 → ComplexModel (m + 1)) (φ : 𝓓(U, ℝ)),
        T.coefficients (canonicalBasis (m + 1)) e w (TestFunction.monoCLM ℝ φ) =
          ddC (regularLocalQuasiPsh hu) w φ) →
      ∀ p ∈ e.val.source, e.val p ∈ U →
        μ p = SquaredLogLelongSourceNormalization.squaredLogLelongNumber
          (n := m + 1) u (e.val p) := by
    intro e U hU u hu hread p hp hpU
    dsimp only [μ]
    rw [hν e U hU u hu hread p hp hpU,
      SquaredLogLelongSourceNormalization.lelongNumber_eq_two_mul_squaredLog
        (Nat.succ_ne_zero m), ← mul_assoc]
    rw [htwo, one_mul]
  refine ⟨μ, hμ, ?_⟩
  intro μ' hμ'
  have heq : (fun p => (2 : ℝ≥0∞) * μ' p) = ν := by
    apply huniq
    intro e U hU u hu hread p hp hpU
    rw [hμ' e U hU u hu hread p hp hpU,
      SquaredLogLelongSourceNormalization.lelongNumber_eq_two_mul_squaredLog
        (Nat.succ_ne_zero m)]
  funext p
  change μ' p = (2 : ℝ≥0∞)⁻¹ * ν p
  rw [← congrFun heq p, ← mul_assoc]
  rw [htwo, one_mul]

end SGPT.Okounkov
