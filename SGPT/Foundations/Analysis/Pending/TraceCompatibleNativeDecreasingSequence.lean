import SGPT.Foundations.Analysis.Pending.TraceCompatibleDiagonalSequence
import SGPT.Foundations.Analysis.Pending.IdealOrderGenericLelongZero
import SGPT.Foundations.Analysis.Pending.SingularDecreasingPEnvelopeNets
import SGPT.Foundations.Analysis.Pending.SingularNativeBackgroundIndependence
import SGPT.Foundations.Analysis.Pending.SingularPositiveCommonBackgroundExistence
import SGPT.Foundations.Analysis.Pending.GlobalPMultiplierOrder
import SGPT.Foundations.Analysis.Pending.GlobalQuasiPshTraceExistence
import SGPT.Foundations.Analysis.Pending.TraceIdealOrderMonotonicity
import SGPT.Foundations.Analysis.Pending.TraceRepresentativeGlobalPClass

set_option autoImplicit false

/-! # Actual full trace readers for original decreasing native sequences -/

open Set Filter Metric
open scoped Topology Manifold ENNReal ContDiff

namespace SGPT.Foundations.Analysis.Pending.TraceCompatibleNativeDecreasingSequence

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
  FirstPass.IEnvelope FirstPass.QuasiEquisingularApproximation FirstPass.TraceBackground
  ThetaPshL1Topology TraceRepresentativeConstruction SingularCanonicalSingularityDistance
  SingularCanonicalDistanceZeroPEquivalence SingularGlobalPEnvelopeBridge
  SingularNativeBackgroundIndependence SingularDecreasingPEnvelopeNets
  GlobalPMultiplierOrder IdealOrderGenericLelongZero TraceCompatibleDiagonalSequence
  SingularGlobalPOrder

noncomputable section

variable {n k : ℕ} {M V : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M] [TopologicalSpace V] [MeasurableSpace V]
  [BorelSpace V] [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V]
  [CompactSpace V] [ConnectedSpace V]

omit [MeasurableSpace M] [BorelSpace M] [ConnectedSpace M] in
private theorem reader_of_ideal_equivalence
    (omega : KahlerBackground n M) (omegaV : KahlerBackground k V)
    {θ : ClosedRealOneOneForm n M} {u p : M → EReal} {T : V → EReal}
    (hu : IsThetaPshPotential θ.val u) {ι : V → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (hg : (⨅ y : V, lelongNumber (n := n) u (ι y)) = 0)
    (hP : IsTraceRepresentativeAlong omega omegaV hι p T)
    (heq : IEquivalentOnManifold (n := n) u p) :
    IsTraceRepresentativeAlong omega omegaV hι u T := by
  obtain ⟨S, hS, _⟩ :=
    GlobalQuasiPshTraceExistence.exists_of_isThetaPshPotential omega omegaV hu hι hg
  have hST := TraceIdealOrderMonotonicity.sourcePEquivalent_of_iEquivalent_of_isTraceRepresentativeAlong
    omegaV omegaV hι hS hP heq
  exact TraceRepresentativeGlobalPClass.isTraceRepresentativeAlong_of_sourcePEquivalent
    omegaV hι hS hST

/-- Actual positive-background envelope infima and full ideal-order domain
transport remove the literal-infimum premise from the original sequence. -/
theorem exists_native_trace_readers_of_antitone
    (omega : KahlerBackground n M) (omegaV : KahlerBackground k V)
    (θ : ClosedRealOneOneForm n M) (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    (ui : ℕ → ThetaPshL1 θ.val) (u : ThetaPshL1 θ.val)
    (hanti : ∀ x, Antitone fun j => (ui j).val x)
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
            (PluripolarCapacityDichotomy.isBigClass_kahler β)).toUniformSpace.toTopologicalSpace T) := by
  classical
  let γ : ClosedRealOneOneForm n M := θ + omega.form
  have hγ : IsBigClass (RealBottChern.ofRepresentative γ) := by
    simpa only [one_smul] using
      PositiveCurrentAssembly.isBigClass_add_smul_of_isThetaPshPotential
        omega θ u.property zero_lt_one
  let U : ℕ → ThetaPshL1 γ.val := fun j =>
    ⟨(ui j).val, LocalPotentials.isThetaPshPotential_add_of_semipositive
      (ui j).property omega.isSemipositive⟩
  let v : ThetaPshL1 γ.val :=
    ⟨u.val, LocalPotentials.isThetaPshPotential_add_of_semipositive
      u.property omega.isSemipositive⟩
  have hU : Tendsto U atTop (@nhds (ThetaPshL1 γ.val)
      (singularityPseudoMetricSpace omega γ hγ).toUniformSpace.toTopologicalSpace v) :=
    (tendsto_native_iff_add_kahler omega θ hbig atTop ui u).mp hlim
  have hpos : 0 < DiagonalMass.diagonalPotentialMass γ v.val v.property := by
    simpa only [DiagonalMass.HasPositivePotentialMass, one_smul] using
      SingularPositiveCommonBackgroundExistence.hasPositivePotentialMass_add_smul
        omega u.property zero_lt_one
  have hP (q : ThetaPshL1 γ.val) :
      IsThetaPshPotential γ.val (singularityEnvelope γ.val q.val) :=
    singularityEnvelope_isThetaPshPotential γ.val γ.property.1 γ.property.2
      q.property.1.hasSmoothLocalPotentials q.val q.property
  let Pj : ℕ → ThetaPshL1 γ.val := fun j =>
    ⟨singularityEnvelope γ.val (U j).val, hP (U j)⟩
  let p : ThetaPshL1 γ.val := ⟨singularityEnvelope γ.val v.val, hP v⟩
  have hEP (q : ThetaPshL1 γ.val) :
      IEquivalentOnManifold (n := n) q.val (singularityEnvelope γ.val q.val) :=
    iEquivalentOnManifold_of_sourcePEquivalent
      (sourcePEquivalent_singularityEnvelope omega γ q.property)
  have hgP : (⨅ y : V, lelongNumber (n := n) p.val (ι y)) = 0 :=
    generic_lelong_inf_eq_zero_of_iOrder v.property.1 (hEP v).1 ι hgeneric
  have hPanti : ∀ x, Antitone fun j => (Pj j).val x := by
    intro x a b hab
    exact singularityEnvelope_mono
      (MoreSingularOn.of_le fun y _ => hanti y hab) x
  have horder : ∀ i j, i ≤ j → SourcePOrder (n := n) (U j).val (U i).val := by
    intro i j hij
    exact sourcePOrder_of_moreSingularOn omega γ γ (U j).property (U i).property
      (MoreSingularOn.of_le fun x _ => hanti x hij)
  have hInf : ∀ x, (⨅ j, (Pj j).val x) = p.val x := by
    have hf := iInf_singularityEnvelope_eq_of_sourcePOrder_tendsto_native
      omega γ hγ U v horder hU hpos
    exact fun x => by simpa only [iInf_apply] using congrFun hf x
  let := singularityPseudoMetricSpace omega γ hγ
  let : TopologicalSpace (ThetaPshL1 γ.val) :=
    (singularityPseudoMetricSpace omega γ hγ).toUniformSpace.toTopologicalSpace
  have hz (q : ThetaPshL1 γ.val) :
      dist q (⟨singularityEnvelope γ.val q.val, hP q⟩ : ThetaPshL1 γ.val) = 0 := by
    have he := (singularityDistance_eq_zero_iff_sourcePEquivalent omega γ hγ
      q.property (hP q)).mpr (sourcePEquivalent_singularityEnvelope omega γ q.property)
    calc
      dist q (⟨singularityEnvelope γ.val q.val, hP q⟩ : ThetaPshL1 γ.val) =
          (singularityDistance omega γ hγ q.val (singularityEnvelope γ.val q.val)).toReal :=
        dist_eq_singularityDistance_toReal omega γ hγ q
          ⟨singularityEnvelope γ.val q.val, hP q⟩
      _ = 0 := by rw [he, EReal.toReal_zero]
  have hPlim : Tendsto Pj atTop (𝓝 p) := by
    have hzeroVP : dist v p = 0 := hz v
    apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero (fun _ => dist_nonneg) (fun j => ?_)
      (tendsto_iff_dist_tendsto_zero.mp hU)
    have h1 := dist_triangle (Pj j) (U j) p
    have h2 := dist_triangle (U j) v p
    have hzero : dist (Pj j) (U j) = 0 := by simpa only [dist_comm] using hz (U j)
    have h1' : dist (Pj j) p ≤ dist (U j) p := by
      simpa only [hzero, zero_add] using h1
    have h2' : dist (U j) p ≤ dist (U j) v := by
      simpa only [hzeroVP, add_zero] using h2
    exact h1'.trans h2'
  obtain ⟨β, Tj, T, hTj, hT, hTlim⟩ :=
    exists_native_trace_readers_of_antitone_literal_inf omega omegaV γ hγ
      Pj p hPanti hInf hPlim hι hgP
  have hgPj (j : ℕ) : (⨅ y : V, lelongNumber (n := n) (Pj j).val (ι y)) = 0 := by
    have hpoint (x : M) : p.val x ≤ (Pj j).val x := by
      rw [← hInf x]
      exact iInf_le _ j
    have hle : (⨅ y : V, lelongNumber (n := n) (Pj j).val (ι y)) ≤
        ⨅ y : V, lelongNumber (n := n) p.val (ι y) :=
      iInf_mono fun _ => KahlerCurrentMax.lelongNumber_le_of_eventually_le
        (Eventually.of_forall hpoint)
    exact le_antisymm (by simpa only [hgP] using hle) zero_le
  refine ⟨β, Tj, T, ?_, ?_, hTlim⟩
  · intro j
    have hgUj := generic_lelong_inf_eq_zero_of_iOrder (Pj j).property.1
      (hEP (U j)).2 ι (hgPj j)
    exact reader_of_ideal_equivalence omega omegaV (U j).property hι hgUj
      (hTj j) (hEP (U j))
  · exact reader_of_ideal_equivalence omega omegaV v.property hι hgeneric hT (hEP v)

end
end SGPT.Foundations.Analysis.Pending.TraceCompatibleNativeDecreasingSequence
