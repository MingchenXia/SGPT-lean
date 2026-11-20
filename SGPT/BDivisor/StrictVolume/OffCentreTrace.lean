import SGPT.BDivisor.StrictVolume.ExceptionalPhysicalCurrent

/-! Genuine onModel equality for the original Cartier constructor. The
common refinement is chosen internally from the existing modification system.
Checks and provider-boundary receipts are preserved separately. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace SGPT.BDivisor.TraceOffCentreNext

open Set
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.CanonicalCurrentFrame

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel 2) X]
  [IsComplexManifold 2 X] [CompactSpace X] [ConnectedSpace X]

/-- Exact source trace identity for a genuine fibre-supported effective divisor.
The actual common refinement and ZERO exceptional push-pull are produced internally.
No trace equality, class comparison, pushforward-zero or common-model data is input. -/
theorem cartier_fibre_divisor_trace_eq_pullback
    (pi rho : Modification 2 X) (H : RealBottChern 2 X)
    (F : MeteredEffectiveQDivisor 2 pi.carrier)
    (hF : IsThetaPshPotential F.curvature.val F.weight)
    {p : X} (hsupp : F.support ⊆ pi.map ⁻¹' {p})
    {U : Set X} (hiso : IsIsomorphismOver 2 rho.map U) (hp : p ∈ U) :
    (WeilBDivisor.cartierOf (by decide) pi
      (classPullback pi.contMDiff_map H - RealBottChern.ofRepresentative F.curvature)).onModel rho =
        classPullback rho.contMDiff_map H := by
  obtain ⟨sigma, hpi, hrho⟩ := Modification.exists_le_le pi rho
  have hcomm : pi.map ∘ Modification.homOfLE hpi =
      rho.map ∘ Modification.homOfLE hrho :=
    (Modification.map_comp_homOfLE hpi).trans (Modification.map_comp_homOfLE hrho).symm
  have hZero := pushforward_pullback_metered_fibre_class_eq_zero
    (Modification.Dominates.isAnalyticModification hpi)
    (Modification.Dominates.isAnalyticModification hrho) hcomm hiso hp F hF hsupp
  have hZeroLE : Modification.classPushforwardOfLE (by decide) hrho
      (Modification.classPullbackOfLE hpi (RealBottChern.ofRepresentative F.curvature)) = 0 :=
    hZero
  have hH : Modification.classPullbackOfLE hpi (classPullback pi.contMDiff_map H) =
      Modification.classPullbackOfLE hrho (classPullback rho.contMDiff_map H) := by
    rw [← Modification.classPullbackOfLE_root pi H,
      ← Modification.classPullbackOfLE_root rho H,
      ← Modification.classPullbackOfLE_trans (Modification.root_le pi) hpi,
      ← Modification.classPullbackOfLE_trans (Modification.root_le rho) hrho]
  rw [WeilBDivisor.cartierOf_onModel _ hpi hrho, map_sub, map_sub, hZeroLE, sub_zero,
    hH, Modification.classPushforwardOfLE_classPullbackOfLE]

open SGPT.Toric SGPT.Toric.BlowdownDraft SGPT.Toric.F1IntersectionDraft
open SGPT.Projective
open SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy

/-- SAME physical exceptional metric and actual re-centred point blowdown,
with common refinement, support, Chern readback and onModel equality ALL
manufactured. Root's actual moving blowup constructor is definitionally this
modification; its nef/volume constructions remain separately owned. -/
theorem original_recentered_exceptional_cartier_trace_eq_pullback
    (hs : latticePolytopeEdgeSmooth blowupGenerator)
    (a : ComplexProjectiveSpace 2 → ComplexProjectiveSpace 2)
    (ha : IsAnalyticModification (n := 2) (a ∘ originalBlowdown hs))
    (rho : Modification 2 (ComplexProjectiveSpace 2)) (H : RealBottChern 2 (ComplexProjectiveSpace 2))
    {U : Set (ComplexProjectiveSpace 2)} (hiso : IsIsomorphismOver 2 rho.map U)
    (hp : a blowdownOrigin ∈ U) :
    let pi : Modification 2 (ComplexProjectiveSpace 2) :=
      { carrier := PolytopeToricVariety blowupGenerator hs
        map := a ∘ originalBlowdown hs
        isAnalyticModification := ha }
    (WeilBDivisor.cartierOf (by decide) pi
      (classPullback ha.1 H - RealBottChern.ofRepresentative (originalExceptionalMetric hs).form)).onModel rho =
        classPullback rho.contMDiff_map H := by
  let pi : Modification 2 (ComplexProjectiveSpace 2) :=
    { carrier := PolytopeToricVariety blowupGenerator hs
      map := a ∘ originalBlowdown hs
      isAnalyticModification := ha }
  have hsupp : (originalExceptionalPhysicalDivisor hs).support ⊆
      pi.map ⁻¹' {a blowdownOrigin} := by
    intro z hz
    rw [originalExceptionalPhysicalDivisor_support_fibre] at hz
    change a (originalBlowdown hs z) = a blowdownOrigin
    exact congrArg a hz
  have h := cartier_fibre_divisor_trace_eq_pullback pi rho H
    (originalExceptionalPhysicalDivisor hs) (originalExceptionalPhysicalDivisor_weight_psh hs)
    hsupp hiso hp
  rw [originalExceptionalPhysicalDivisor_class hs] at h
  exact h

end SGPT.BDivisor.TraceOffCentreNext
