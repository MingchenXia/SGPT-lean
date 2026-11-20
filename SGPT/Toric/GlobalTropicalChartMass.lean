import SGPT.Toric.TropicalLocalMass
import SGPT.Foundations.Analysis.Pending.GlobalDiagonalScaling
import SGPT.Foundations.Analysis.Pending.PatchLocalBoundedMeasure

set_option autoImplicit false
noncomputable section

namespace SGPT.Toric

open Set MeasureTheory TopologicalSpace SGPT.Convex
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.GlobalPotentialPatches
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.MixedMongeAmpere
open scoped Topology ENNReal RealInnerProductSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {θ : ClosedRealOneOneForm n M} {u : M → EReal}
  {ρ : ComplexModel n → ℝ} {f : EuclideanSpace ℝ (Fin n) → ℝ}

local notation "D" => tropicalSmoothDomain n

/-- Genuine chart, original local potential and literal source values manufacture
every field of this tropical patch, including the actual empty-tuple domain. -/
def tropicalPotentialPatch (e : ComplexChart n M)
    (hρ : IsSmoothLocalPotential θ.val e D ρ) (hc : ConvexOn ℝ univ f)
    (heq : EqOn (fun z => chartFunction u e z + (ρ z : EReal))
      (fun z => (f (tropicalization z) : EReal)) D) :
    Patch (fun _ : Fin n => θ) (fun _ => u) where
  chart := e
  domain := D
  domain_le_target := hρ.2.1
  potential := fun _ => ρ
  localPotential := fun _ => hρ
  plurisubharmonic := fun _ => plurisubharmonicOn_congr (tropicalSmoothDomain n).isOpen
    (isLocallyBoundedPshOn_tropicalConvexProfile hc).1
    (fun _z hz => (heq hz).symm)

/-- The actual corrected tuple reads back the SAME original finite convex profile. -/
theorem tropicalPotentialPatch_corrected (e : ComplexChart n M)
    (hρ : IsSmoothLocalPotential θ.val e D ρ) (hc : ConvexOn ℝ univ f)
    (heq : EqOn (fun z => chartFunction u e z + (ρ z : EReal))
      (fun z => (f (tropicalization z) : EReal)) D)
    (i : Fin n) {z : ComplexModel n} (hz : z ∈ D) :
    (tropicalPotentialPatch e hρ hc heq).corrected i z =
      (f (tropicalization z) : EReal) := heq hz

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- Existing global finite-cover restriction and real locally-bounded BT comparison
give the actual NP restriction; no canonical measure equality is an input. -/
theorem globalMixedMeasure_restrict_tropical_chart
    (hu : IsThetaPshPotential θ.val u) (e : ComplexChart n M)
    (hρ : IsSmoothLocalPotential θ.val e D ρ) (hc : ConvexOn ℝ univ f)
    (heq : EqOn (fun z => chartFunction u e z + (ρ z : EReal))
      (fun z => (f (tropicalization z) : EReal)) D) :
    (GlobalNonPluripolar.globalMixedMeasure (fun _ : Fin n => θ) (fun _ => u)
      (fun _ => hu.1)).restrict (tropicalPotentialPatch e hρ hc heq).source =
      (tropicalPotentialPatch e hρ hc heq).pushMeasure (tropicalCanonicalBTMeasure hc) := by
  rw [GlobalNonPluripolar.globalMixedMeasure_restrict_patch]
  unfold GlobalNonPluripolar.patchMeasure
  apply congrArg (tropicalPotentialPatch e hρ hc heq).pushMeasure
  exact MixedNonPluripolar.mixedTruncationLimitMeasure_eq_canonical_of_eqOn
    (fun _ => isLocallyBoundedPshOn_tropicalConvexProfile hc)
    (tropicalPotentialPatch e hρ hc heq).plurisubharmonic
    (fun i z hz => tropicalPotentialPatch_corrected e hρ hc heq i hz)

/-- OTHER actual quasi-PSH pole geometry internally gives boundary nullity and
the whole measure, without finite total mass or a desired NP identity premise. -/
theorem globalMixedMeasure_eq_tropical_chart_pushMeasure
    (hu : IsThetaPshPotential θ.val u) (e : ComplexChart n M)
    (hρ : IsSmoothLocalPotential θ.val e D ρ) (hc : ConvexOn ℝ univ f)
    (heq : EqOn (fun z => chartFunction u e z + (ρ z : EReal))
      (fun z => (f (tropicalization z) : EReal)) D)
    {v : M → EReal} (hv : IsGlobalQuasiPshPotential (n := n) v)
    (hpole : ((tropicalPotentialPatch e hρ hc heq).source : Set M)ᶜ ⊆
      {x | v x = ⊥}) :
    GlobalNonPluripolar.globalMixedMeasure (fun _ : Fin n => θ) (fun _ => u)
      (fun _ => hu.1) =
      (tropicalPotentialPatch e hρ hc heq).pushMeasure (tropicalCanonicalBTMeasure hc) := by
  have hnull : GlobalNonPluripolar.globalMixedMeasure
      (fun _ : Fin n => θ) (fun _ => u) (fun _ => hu.1)
      ((tropicalPotentialPatch e hρ hc heq).source : Set M)ᶜ = 0 :=
    le_antisymm ((measure_mono hpole).trans_eq
      (GlobalDiagonalScaling.globalMixedMeasure_pole_null_of_quasiPsh
        (fun _ => hu.1) hv)) bot_le
  have hself := Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr hnull)
  exact hself.symm.trans (globalMixedMeasure_restrict_tropical_chart hu e hρ hc heq)

/-- The actual restricted inverse-chart transport and genuine canonical support
read the whole original NP total as the SAME lattice-normalized Newton volume. -/
theorem globalMixedMeasure_univ_eq_tropicalNewtonBody
    (hu : IsThetaPshPotential θ.val u) (e : ComplexChart n M)
    (hρ : IsSmoothLocalPotential θ.val e D ρ) (hc : ConvexOn ℝ univ f)
    (heq : EqOn (fun z => chartFunction u e z + (ρ z : EReal))
      (fun z => (f (tropicalization z) : EReal)) D)
    {v : M → EReal} (hv : IsGlobalQuasiPshPotential (n := n) v)
    (hpole : ((tropicalPotentialPatch e hρ hc heq).source : Set M)ᶜ ⊆
      {x | v x = ⊥}) :
    GlobalNonPluripolar.globalMixedMeasure (fun _ : Fin n => θ) (fun _ => u)
      (fun _ => hu.1) univ = (n.factorial : ENNReal) * volume
      (convexNewtonBody (conjugate (innerₗ (EuclideanSpace ℝ (Fin n)))
        (fun a => (f a : EReal)))) := by
  have hsupport : tropicalCanonicalBTMeasure hc (D : Set (ComplexModel n))ᶜ = 0 :=
    canonicalMixedBedfordTaylorMeasure_compl D
      (fun _ : Fin n => fun z => f (tropicalization z))
      (fun _ => isLocallyBoundedPshOn_tropicalConvexProfile hc)
  have hrestrict : (tropicalCanonicalBTMeasure hc).restrict D = tropicalCanonicalBTMeasure hc :=
    Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr hsupport)
  have htotal : tropicalCanonicalBTMeasure hc D = tropicalCanonicalBTMeasure hc univ := by
    have h := congrArg (fun μ : Measure (ComplexModel n) => μ univ) hrestrict
    simpa only [Measure.restrict_apply_univ] using h
  rw [globalMixedMeasure_eq_tropical_chart_pushMeasure hu e hρ hc heq hv hpole,
    Patch.pushMeasure_apply]
  simpa only [tropicalPotentialPatch, preimage_univ, inter_univ] using
    htotal.trans (tropicalCanonicalBTMeasure_univ_eq_convexNewtonBody hc)

end SGPT.Toric
