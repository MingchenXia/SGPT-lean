import SGPT.Foundations.Analysis.Pending.DemaillyCommonGeometryDiagonalFullQea
import SGPT.Foundations.Analysis.Pending.QuasiEquisingularUniformTraceReaders
import SGPT.Foundations.Analysis.Pending.NativeRowDiagonalSelection
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false

/-! # Actual full trace readers and their native sequence limit -/

open Set Filter Metric MeasureTheory
open scoped Topology Manifold ENNReal ContDiff

namespace SGPT.Foundations.Analysis.Pending.TraceCompatibleDiagonalSequence
open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
  FirstPass.QuasiEquisingularApproximation FirstPass.TraceBackground
  ThetaPshL1Topology TraceRepresentativeConstruction SingularCanonicalSingularityDistance
  DemaillyCommonGeometryDiagonalFullQea QuasiEquisingularUniformTraceReaders
  NativeRowDiagonalSelection
  PluripolarCapacityDichotomy

noncomputable section

variable {n k : ℕ} {M V : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M] [TopologicalSpace V] [MeasurableSpace V]
  [BorelSpace V] [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V]
  [CompactSpace V] [ConnectedSpace V]

/-- Full rows, a common actual target and the compatible full diagonal
internally produce trace readers converging in one genuine native topology. -/
theorem exists_native_trace_readers_of_antitone_literal_inf
    (omega : KahlerBackground n M) (omegaV : KahlerBackground k V)
    (θ : ClosedRealOneOneForm n M) (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    (ui : ℕ → ThetaPshL1 θ.val) (u : ThetaPshL1 θ.val)
    (hanti : ∀ x, Antitone fun j => (ui j).val x)
    (hinf : ∀ x, (⨅ j, (ui j).val x) = u.val x)
    (hlim : Tendsto ui atTop (@nhds (ThetaPshL1 θ.val)
      (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace u))
    {ι : V → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (hgeneric : (⨅ y : V, lelongNumber (n := n) u.val (ι y)) = 0) :
    ∃ β : KahlerBackground k V, ∃ Tj : ℕ → ThetaPshL1 β.form.val,
      ∃ T : ThetaPshL1 β.form.val,
        (∀ j, IsTraceRepresentativeAlong omega omegaV hι (ui j).val (Tj j).val) ∧
        IsTraceRepresentativeAlong omega omegaV hι u.val T.val ∧
        Tendsto Tj atTop (@nhds (ThetaPshL1 β.form.val)
          (singularityPseudoMetricSpace omegaV β.form
            (isBigClass_kahler β)).toUniformSpace.toTopologicalSpace T) := by
  classical
  have hn : 0 < n := by
    by_contra hn
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    have htop (y : V) : lelongNumber (n := n) u.val (ι y) = ⊤ :=
      LelongNumberChartTransport.lelongNumber_eq_top_of_eventually_bot
        (by rw [LelongNumberChartTransport.nhdsWithin_ne_eq_bot_of_dim_eq_zero hn0]
            exact Filter.eventually_bot)
    simp only [htop, iInf_const] at hgeneric
    exact ENNReal.top_ne_zero hgeneric
  obtain ⟨F, ρ, D, K, _hD, _hρ, hrows, hdiagonal⟩ :=
    exists_common_geometry_full_diagonal hn omega θ hbig ui u hanti hinf hlim
  let R : ℕ → ℕ → M → EReal := fun j l =>
    DemaillyApproximationSequence.seq F ρ (ui j).val (2 * (D + 1 / 4)) (l + K)
  have hR (j : ℕ) : IsQuasiEquisingularApproximation omega (θ + omega.form)
      (ui j).val (fun _ => 0) (R j) := hrows (ui j).val (ui j).property
  have hg (j : ℕ) : (⨅ y : V, lelongNumber (n := n) (ui j).val (ι y)) = 0 := by
    have hpoint (x : M) : u.val x ≤ (ui j).val x := by
      rw [← hinf x]
      exact iInf_le _ j
    have hle : (⨅ y : V, lelongNumber (n := n) (ui j).val (ι y)) ≤
        ⨅ y : V, lelongNumber (n := n) u.val (ι y) :=
      iInf_mono fun _ => KahlerCurrentMax.lelongNumber_le_of_eventually_le
        (Eventually.of_forall hpoint)
    exact le_antisymm (by simpa only [hgeneric] using hle) zero_le
  obtain ⟨C, hC, _hadm, hall⟩ := exists_uniform_target_full_trace_readers
    hι omega omegaV (θ + omega.form) (ε := fun _ => 0) antitone_const
  let β := KahlerBackground.smul hC omegaV
  have hrow (j : ℕ) := hall (ui j).val (R j) (hR j) (hg j)
  choose hv hmodel hreader hnative using hrow
  let Tj : ℕ → ThetaPshL1 β.form.val := fun j =>
    ⟨⨅ l, singularityEnvelope β.form.val (fun y => R j l (ι y)),
      (hmodel j).plurisubharmonic⟩
  let W : ℕ → ℕ → ThetaPshL1 β.form.val := fun j l =>
    ⟨fun y => R j l (ι y), hv j l⟩
  let := singularityPseudoMetricSpace omegaV β.form (isBigClass_kahler β)
  let : TopologicalSpace (ThetaPshL1 β.form.val) :=
    (singularityPseudoMetricSpace omegaV β.form
      (isBigClass_kahler β)).toUniformSpace.toTopologicalSpace
  have hW (j : ℕ) : Tendsto (W j) atTop (𝓝 (Tj j)) := hnative j
  obtain ⟨κ, hκ, hκtop, _hclose, herror⟩ :=
    exists_strictMono_diagonal_of_tendsto_rows W Tj hW
      (ε := fun j => (1 / 2 : ℝ) ^ j) (fun j => pow_pos (by norm_num) j)
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
  let η : ℕ → M → EReal := fun j => R j (κ j)
  have hη : IsQuasiEquisingularApproximation omega (θ + omega.form)
      u.val (fun _ => 0) η := (hdiagonal κ hκ.monotone hκtop).1
  obtain ⟨hηV, hηmodel, hηreader, hηnative⟩ := hall u.val η hη hgeneric
  let T : ThetaPshL1 β.form.val :=
    ⟨⨅ j, singularityEnvelope β.form.val (fun y => η j (ι y)), hηmodel.plurisubharmonic⟩
  have hdiag : Tendsto (fun j => W j (κ j)) atTop (𝓝 T) := hηnative
  have hdiagdist := tendsto_iff_dist_tendsto_zero.mp hdiag
  have hsum := herror.add hdiagdist
  rw [add_zero] at hsum
  refine ⟨β, Tj, T, hreader, hηreader, ?_⟩
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero (fun _ => dist_nonneg) (fun j => ?_) hsum
  simpa only [dist_comm (Tj j) (W j (κ j))] using
    dist_triangle (Tj j) (W j (κ j)) T

end
end SGPT.Foundations.Analysis.Pending.TraceCompatibleDiagonalSequence
