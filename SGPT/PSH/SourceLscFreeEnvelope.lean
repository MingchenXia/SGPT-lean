import SGPT.Envelopes.SourceObstacleConcentration
import SGPT.Envelopes.SourceMinimalEnvelopeLocalBounds
import SGPT.Foundations.Analysis.Pending.PatchLocalBoundedMeasure
import SGPT.Foundations.Analysis.Pending.RooftopDimZero

/-! Original `lma:BT_freeenvelope`, author/chapter_npp.tex:658--693.

The original real lower-semicontinuous obstacle is unchanged. Its finite
lower bound and the envelope's genuine domain/finite upper bound are produced.
The obstacle is not assumed bounded above or quasicontinuous, and the envelope
is compared to it only quasi-everywhere. Local boundedness is outside the
actual source analytic-current non-Kähler locus. Bounded-patch agreement keeps
the ordinary Bedford–Taylor meaning of the measure on the original free set.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set Filter MeasureTheory
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.FirstPass.GlobalPotentialPatches
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere FirstPass.MixedMongeAmpere
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.MixedMongeAmpere
open SGPT.Foundations.Analysis.Pending.BoundedGlobalProduct
open PatchLocalBoundedMeasure GlobalNonPluripolar

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]

/-- A real LSC obstacle on the compact source has a finite lower bound.
The shifted actual minimal potential produces noncollapse; the sole printed
non-top hypothesis then produces the genuine envelope and its upper bound. -/
theorem sourceLscObstacleEnvelope_data (omega : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (f : M → ℝ) (hf : LowerSemicontinuous f)
    (hnt : sourceRelativeEnvelope θ (fun _ => ⊤) (fun x => (f x : EReal)) ≠ fun _ => ⊤) :
    let P := sourceRelativeEnvelope θ (fun _ => ⊤) (fun x => (f x : EReal))
    ∃ _hP : IsThetaPSH θ P, ∃ c C : ℝ,
      (fun x => sourceMinimalEnvelope θ x + (c : EReal)) ≤ P ∧
      ∀ x, P x ≤ (C : EReal) := by
  classical
  let P := sourceRelativeEnvelope θ (fun _ => ⊤) (fun x => (f x : EReal))
  obtain ⟨c, hc⟩ := LowerSemicontinuousOn.bddBelow_of_isCompact
    (f := f) (s := (univ : Set M)) isCompact_univ (hf.lowerSemicontinuousOn univ)
  have hcf (x : M) : c ≤ f x := hc ⟨x, mem_univ x, rfl⟩
  have hV := (isThetaPSH_iff_nativeThetaPotential θ _).mp
    (sourceMinimalEnvelope_thetaPSH omega θ hbig)
  have hcand := hV.add_const c
  have hle (x : M) : sourceMinimalEnvelope θ x + (c : EReal) ≤ (f x : EReal) := by
    calc
      sourceMinimalEnvelope θ x + (c : EReal) ≤ 0 + (c : EReal) :=
        add_le_add (sourceMinimalEnvelope_le_zero θ x) le_rfl
      _ = (c : EReal) := zero_add _
      _ ≤ (f x : EReal) := EReal.coe_le_coe_iff.mpr (hcf x)
  have hminor : (fun x => sourceMinimalEnvelope θ x + (c : EReal)) ≤ P := by
    dsimp only [P]
    rw [sourceObstacleEnvelope_eq_native]
    exact le_rooftopEnvelope hcand (quasiEverywhere_of_forall hle)
  have hnb : P ≠ fun _ => ⊥ := by
    intro hbot
    obtain ⟨y, _, hny⟩ := hcand.2 (Classical.arbitrary M) univ isOpen_univ (mem_univ _)
    have hy := hminor y
    rw [hbot] at hy
    exact hny (le_bot_iff.mp hy)
  have hP : IsThetaPSH θ P := sourceObstacleEnvelope_genuine omega hnb hnt
  obtain ⟨C, hC⟩ := ((isThetaPSH_iff_nativeThetaPotential θ _).mp hP).exists_global_upper_bound
  exact ⟨hP, c, C, hminor, hC⟩

/-- Both finite local bounds are manufactured off the original analytic-current
polar intersection. The source locus is never replaced by a native alias. -/
theorem sourceLscObstacleEnvelope_locallyBounded (omega : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (f : M → ℝ) (hf : LowerSemicontinuous f)
    (hnt : sourceRelativeEnvelope θ (fun _ => ⊤) (fun x => (f x : EReal)) ≠ fun _ => ⊤) :
    let P := sourceRelativeEnvelope θ (fun _ => ⊤) (fun x => (f x : EReal))
    ∀ x, x ∉ sourceNonKahlerLocus
      (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)) →
      ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ ∃ a b : ℝ,
        ∀ y ∈ U, (a : EReal) ≤ P y ∧ P y ≤ (b : EReal) := by
  dsimp only
  obtain ⟨_, c, C, hminor, hupper⟩ := sourceLscObstacleEnvelope_data omega θ hbig f hf hnt
  intro x hx
  obtain ⟨U, hU, hxU, a, _, hab⟩ := sourceMinimalEnvelope_locallyBounded omega θ hbig hx
  refine ⟨U, hU, hxU, a + c, C, fun y hy => ⟨?_, hupper y⟩⟩
  rw [EReal.coe_add]
  exact (add_le_add (hab y hy).1 le_rfl).trans (hminor y)

omit [ConnectedSpace M] in
/-- The actual source diagonal measure on a locally bounded patch is the
ordinary bounded Bedford–Taylor product, with no global bound on the potential. -/
theorem sourceBoundedPatch_diagonal_measure_eq_BedfordTaylor
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (u : M → EReal)
    (hu : IsThetaPSH θ u)
    (P : Patch (fun _ : Fin n => atlasClosedFormToNative θ) (fun _ => u))
    (hb : IsBoundedPotentialOn u P.source) :
    (sourcePotentialNonPluripolarMeasure θ u hu).restrict (P.source : Set M) =
      P.pushMeasure (canonicalMixedBedfordTaylorMeasure P.domain (correctedReal P)
        (correctedReal_isLocallyBoundedMixedPshOn_of_boundedOn P (fun _ => hb))) := by
  exact globalMixedMeasure_restrict_patch_eq_canonical_of_boundedOn
    (fun _ : Fin n => ((isThetaPSH_iff_nativeThetaPotential θ u).mp hu).1) P (fun _ => hb)

/-- Whole original `lma:BT_freeenvelope`: genuine envelope, both finite local
bounds outside the actual source non-Kähler locus and literal zero restriction
of its measure on the original free region. All natural dimensions are kept. -/
theorem sourceLscObstacleEnvelope_free_BedfordTaylor (omega : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (f : M → ℝ) (hf : LowerSemicontinuous f)
    (hnt : sourceRelativeEnvelope θ (fun _ => ⊤) (fun x => (f x : EReal)) ≠ fun _ => ⊤) :
    let P := sourceRelativeEnvelope θ (fun _ => ⊤) (fun x => (f x : EReal))
    let N := sourceNonKahlerLocus (RealBottChern.ofRepresentative (atlasClosedFormToNative θ))
    ∃ hP : IsThetaPSH θ P,
      (∀ x, x ∉ N → ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ ∃ a b : ℝ,
        ∀ y ∈ U, (a : EReal) ≤ P y ∧ P y ≤ (b : EReal)) ∧
      (sourcePotentialNonPluripolarMeasure θ P hP).restrict ({x | P x < (f x : EReal)} \ N) = 0 := by
  classical
  let P := sourceRelativeEnvelope θ (fun _ => ⊤) (fun x => (f x : EReal))
  let Θ := atlasClosedFormToNative θ
  let N := sourceNonKahlerLocus (RealBottChern.ofRepresentative Θ)
  let S := {x | P x < (f x : EReal)} \ N
  obtain ⟨hP, _, _, _, _⟩ := sourceLscObstacleEnvelope_data omega θ hbig f hf hnt
  have hloc := sourceLscObstacleEnvelope_locallyBounded omega θ hbig f hf hnt
  have hPn : IsThetaPshPotential Θ.val P := (isThetaPSH_iff_nativeThetaPotential θ _).mp hP
  have hread : P = rooftopEnvelope Θ.val (fun x => (f x : EReal)) :=
    sourceObstacleEnvelope_eq_native θ _
  refine ⟨hP, hloc, ?_⟩
  have hnull : sourcePotentialNonPluripolarMeasure θ P hP S = 0 := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · have hF : IsThetaPshPotential Θ.val (fun x => (f x : EReal)) :=
        RooftopDimZero.isThetaPshPotential_of_dim_zero hn hPn.1.hasSmoothLocalPotentials
          (fun x => EReal.coe_ne_top (f x)) (fun x => EReal.coe_ne_bot (f x))
      have hFP : (fun x => (f x : EReal)) ≤ P := by
        rw [hread]
        exact self_le_rooftopEnvelope hF
      have hempty : S = ∅ := Set.eq_empty_iff_forall_notMem.mpr fun x hx =>
        (not_lt_of_ge (hFP x)) hx.1
      simp only [hempty, measure_empty]
    · have hflsc : LowerSemicontinuous (fun x => (f x : EReal)) := by
        intro x r hr
        obtain ⟨q, hrq, hqf⟩ := EReal.lt_iff_exists_real_btwn.mp hr
        filter_upwards [hf x q (EReal.coe_lt_coe_iff.mp hqf)] with y hy
        exact hrq.trans (EReal.coe_lt_coe_iff.mpr hy)
      have hqe : QuasiEverywhere (n := n) (fun x => P x ≤ (f x : EReal)) := by
        rw [hread]
        exact PolydiskPatchBalayageContactQE.rooftopEnvelope_le_quasiEverywhere_of_kahler
          omega Θ (by simpa only [hread] using hPn)
      have hmax (v : M → EReal) (hv : IsThetaPshPotential Θ.val v)
          (hvf : QuasiEverywhere (n := n) (fun x => v x ≤ (f x : EReal))) : v ≤ P := by
        rw [hread]
        exact le_rooftopEnvelope hv hvf
      have hlocal (x : M) (hx : x ∈ S) : ∃ U ∈ 𝓝 x, IsBoundedPotentialOn P U := by
        obtain ⟨U, hU, hxU, a, b, hab⟩ := hloc x hx.2
        exact ⟨U, hU.mem_nhds hxU, a, b, hab⟩
      exact PolydiskPatchBalayageContactQE.diagonalPotentialMeasure_lt_eq_zero_of_locallyBounded_qe
        hn hflsc hqe hmax hPn (fun _ hx => hx.1) hlocal
  exact Measure.restrict_eq_zero.mpr hnull

end SGPT.PSH.VariableComplexAtlas
