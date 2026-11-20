import SGPT.Foundations.Analysis.Pending.ActualLocalPotentialSmoothDifference
import SGPT.Foundations.Analysis.Pending.ActualLocalQuasiPshQuadraticCorrection
import SGPT.Foundations.Analysis.PlurisubharmonicAE

set_option autoImplicit false

/-! # Smooth compatibility of the original extended-valued local potentials

Local integrability and finite representatives are produced from the genuine
local quasi-PSH predicate. Complete native current equality then determines a
smooth difference at every original point, including poles.
-/

noncomputable section
open Set Filter Metric MeasureTheory TopologicalSpace
open scoped Topology ContDiff Distributions

namespace SGPT.Foundations.Analysis.Pending.ActualQuasiPshPotentialSmoothCompatibility
open FirstPass LocalBedfordTaylorCollar
open _root_.SGPT.Foundations.Analysis.LocalCurrents

variable {n : ℕ} {Ω : Opens (ComplexModel n)} {u v : ComplexModel n → EReal}

private theorem local_ball_data (hu : LocalQuasiPshPotentialOn u Ω)
    {x : ComplexModel n} (hx : x ∈ Ω) :
    ∃ r : ℝ, 0 < r ∧ ball x r ⊆ Ω ∧
      LocallyIntegrableOn (fun z ↦ (u z).toReal) (ball x r) volume ∧
      ∀ᵐ z ∂volume.restrict (ball x r), u z ≠ ⊤ ∧ u z ≠ ⊥ := by
  obtain ⟨A, r, _hA, hr, hsub, hp, _hQ, hne⟩ :=
    ActualLocalQuasiPshQuadraticCorrection.exists_noncollapsed_positive_quadratic_correction hu hx
  let Q := ballPot A x 0
  have hfin := hp.ae_finite volume (convex_ball x r).isPreconnected hne
  have hufin : ∀ᵐ z ∂volume.restrict (ball x r), u z ≠ ⊤ ∧ u z ≠ ⊥ := by
    filter_upwards [hfin] with z hz
    exact ⟨(EReal.add_ne_top_iff_ne_top_left (EReal.coe_ne_bot _)
      (EReal.coe_ne_top _)).mp hz.1, (EReal.add_ne_bot_iff.mp hz.2).1⟩
  have hLP := hp.locallyIntegrableOn_toReal volume (convex_ball x r).isPreconnected hne
  have hLQ : LocallyIntegrableOn Q (ball x r) volume :=
    (contDiff_ballPot A x 0).continuous.continuousOn.locallyIntegrableOn isOpen_ball.measurableSet
  have hreal : (fun z ↦ (u z + (Q z : EReal)).toReal - Q z) =ᵐ[
      volume.restrict (ball x r)] (fun z ↦ (u z).toReal) := by
    filter_upwards [hufin] with z hz
    rw [EReal.toReal_add hz.1 hz.2 (EReal.coe_ne_top _) (EReal.coe_ne_bot _),
      EReal.toReal_coe, add_sub_cancel_right]
  exact ⟨r, hr, hsub, (hLP.sub hLQ).congr hreal, hufin⟩

private theorem local_real_data (hu : LocalQuasiPshPotentialOn u Ω) :
    LocallyIntegrableOn (fun z ↦ (u z).toReal) Ω volume ∧
      ∀ᵐ z ∂volume.restrict Ω, u z ≠ ⊤ ∧ u z ≠ ⊥ := by
  refine ⟨?_, ?_⟩
  · intro x hx
    obtain ⟨r, hr, _hsub, hL, _hfin⟩ := local_ball_data hu hx
    simpa only [nhdsWithin_eq_nhds.mpr (isOpen_ball.mem_nhds (mem_ball_self hr)),
      nhdsWithin_eq_nhds.mpr (Ω.isOpen.mem_nhds hx)] using hL x (mem_ball_self hr)
  · apply ae_restrict_of_open_neighborhood_ae
    intro x hx
    obtain ⟨r, hr, _hsub, _hL, hfin⟩ := local_ball_data hu hx
    exact ⟨ball x r, isOpen_ball, mem_ball_self hr, hfin⟩

/-- The scalar regular distribution of the actual genuine local quasi-PSH
reader. Its realification is internally proved locally integrable. -/
def regularLocalQuasiPsh (hu : LocalQuasiPshPotentialOn u Ω) : 𝓓'(Ω, ℝ) :=
  regularDistribution volume (fun z ↦ (u z).toReal) (local_real_data hu).1

private theorem eqOn_of_ae_eq_localQuasiPsh
    (hu : LocalQuasiPshPotentialOn u Ω) (hv : LocalQuasiPshPotentialOn v Ω)
    (hae : u =ᵐ[volume.restrict Ω] v) : EqOn u v Ω := by
  intro x hx
  obtain ⟨A, r, _hA, hr, hsub, hp, hQ, _hne⟩ :=
    ActualLocalQuasiPshQuadraticCorrection.exists_noncollapsed_positive_quadratic_correction hu hx
  obtain ⟨B, s, _hB, hs, hsub', hp', hQ', _hne'⟩ :=
    ActualLocalQuasiPshQuadraticCorrection.exists_noncollapsed_positive_quadratic_correction hv hx
  let t := min r s
  have ht : 0 < t := lt_min hr hs
  have htr : ball x t ⊆ ball x r := ball_subset_ball (min_le_left _ _)
  have hts : ball x t ⊆ ball x s := ball_subset_ball (min_le_right _ _)
  have hAE : u =ᵐ[volume.restrict (ball x t)] v :=
    ae_restrict_of_ae_restrict_of_subset (htr.trans hsub) hae
  have hsum := (hp.mono htr).add (hQ'.mono hts)
  have hsum' := (hp'.mono hts).add (hQ.mono htr)
  have hcorrected :
      (fun z ↦ (u z + (ballPot A x 0 z : EReal)) + (ballPot B x 0 z : EReal)) =ᵐ[
        volume.restrict (ball x t)]
      (fun z ↦ (v z + (ballPot B x 0 z : EReal)) + (ballPot A x 0 z : EReal)) := by
    filter_upwards [hAE] with z hz
    rw [hz, add_right_comm]
  have heq := hsum.eqOn_of_ae_eq hsum' isOpen_ball volume hcorrected (mem_ball_self ht)
  have hc : u x + ((ballPot A x 0 x + ballPot B x 0 x : ℝ) : EReal) =
      v x + ((ballPot A x 0 x + ballPot B x 0 x : ℝ) : EReal) := by
    simpa only [EReal.coe_add, ← add_assoc, add_right_comm] using heq
  exact le_antisymm
    ((EReal.addLECancellable_coe _).add_le_add_iff_right.mp hc.le)
    ((EReal.addLECancellable_coe _).add_le_add_iff_right.mp hc.ge)

/-- Original genuine extended-valued quasi-PSH potentials of the same full
native current have an internally produced smooth pluriharmonic difference
at every original point, retaining the complete scalar distribution. -/
theorem exists_smooth_original_difference_of_equal_native_ddc
    (hu : LocalQuasiPshPotentialOn u Ω) (hv : LocalQuasiPshPotentialOn v Ω)
    (heq : ddC (regularLocalQuasiPsh hu) = ddC (regularLocalQuasiPsh hv))
    (x : ComplexModel n) (hx : x ∈ Ω) :
    ∃ (U : Opens (ComplexModel n)) (hU : U ≤ Ω) (h : ComplexModel n → ℝ),
      x ∈ U ∧ ContDiff ℝ (⊤ : ℕ∞) h ∧
      ∃ hh : LocallyIntegrableOn h U volume,
        EqOn u (fun z ↦ v z + (h z : EReal)) U ∧
        restrictDistribution (regularLocalQuasiPsh hu - regularLocalQuasiPsh hv) hU =
          regularDistribution volume h hh ∧
        ∀ z ∈ U, ∀ w : ComplexModel n, leviForm h z w = 0 := by
  obtain ⟨U, hU, h, hxU, hsm, hh, hAEreal, hcurrent, hlevi⟩ :=
    ActualLocalPotentialSmoothDifference.exists_smooth_difference_of_equal_native_ddc
      volume (local_real_data hu).1 (local_real_data hv).1 heq x hx
  have hufin : ∀ᵐ z ∂volume.restrict U, u z ≠ ⊤ ∧ u z ≠ ⊥ :=
    ae_restrict_of_ae_restrict_of_subset hU (local_real_data hu).2
  have hvfin : ∀ᵐ z ∂volume.restrict U, v z ≠ ⊤ ∧ v z ≠ ⊥ :=
    ae_restrict_of_ae_restrict_of_subset hU (local_real_data hv).2
  have hAE : u =ᵐ[volume.restrict U] (fun z ↦ v z + (h z : EReal)) := by
    filter_upwards [hAEreal, hufin, hvfin] with z hz huz hvz
    have hreal : (u z).toReal = (v z).toReal + h z := by linarith
    calc
      u z = ((u z).toReal : EReal) := (EReal.coe_toReal huz.1 huz.2).symm
      _ = (((v z).toReal + h z : ℝ) : EReal) := congrArg (fun a : ℝ ↦ (a : EReal)) hreal
      _ = v z + (h z : EReal) := by rw [EReal.coe_add, EReal.coe_toReal hvz.1 hvz.2]
  have huU : LocalQuasiPshPotentialOn u U := hu.mono U.isOpen hU
  have hvU : LocalQuasiPshPotentialOn v U := hv.mono U.isOpen hU
  have hvh : LocalQuasiPshPotentialOn (fun z ↦ v z + (h z : EReal)) U := by
    refine ⟨U.isOpen, hvU.2.1.add_smooth (fun _ _ ↦
      Eventually.of_forall fun _ ↦ hsm.contDiffAt), ?_⟩
    intro z hz W hW hzW
    obtain ⟨y, hy, hne⟩ := hvU.2.2 z hz W hW hzW
    exact ⟨y, hy, EReal.add_ne_bot_iff.mpr ⟨hne, EReal.coe_ne_bot _⟩⟩
  exact ⟨U, hU, h, hxU, hsm, hh, eqOn_of_ae_eq_localQuasiPsh huU hvh hAE,
    hcurrent, hlevi⟩

end SGPT.Foundations.Analysis.Pending.ActualQuasiPshPotentialSmoothCompatibility
