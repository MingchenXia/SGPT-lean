import SGPT.Hodge.ExceptionalBlowup
import SGPT.Siu.SiuDecompositionPrimeDivisors
import SGPT.Foundations.Analysis.Pending.BlowupSNCTransform
import SGPT.Foundations.Analysis.Pending.SNCGlobalPrimeComponents
import SGPT.Foundations.Analysis.Pending.BlowupCodimOne
import SGPT.Foundations.Analysis.Pending.BlowupIsomorphismOff
import SGPT.Foundations.Analysis.Pending.BlowupKahler
import SGPT.Foundations.Analysis.Pending.AnalyticModificationConnectedFibres
import SGPT.Foundations.Analysis.Pending.SourceGenericSubmanifoldMinimum
import SGPT.Foundations.Analysis.Pending.PrescribedBlowupDomination
import SGPT.Foundations.Analysis.Pending.BlowupExistence

/-!
# The exceptional divisor of the blow-up along a connected submanifold

Let `π : Y → X` be the blow-up (`IsBlowupAlong`) of a complex manifold `X` of dimension `m + 1`
along a closed connected complex submanifold `C` of dimension `k`, and `E = π⁻¹(C)`.

* `isConnected_preimage_of_isAnalyticModification`: the preimage of a closed connected set under
  an analytic modification is connected (the fibres are connected, Zariski).
* `isClosedConnectedSubmanifold_exceptional`: `E` is a closed connected smooth hypersurface.
* `exceptionalLocus_eq_preimage`: if `k + 2 ≤ m + 1` (codimension at least two), then
  `Exc(π) = E`.
* `exceptionalPrime`: `E` as a prime divisor of `Y`;
  `excPrimes_eq_singleton`: `E` is the only `π`-exceptional prime divisor.
* `blowupCone_bijective`, `blowupConeEquiv` (**source `prop:blowup_cone`**): for `X` compact
  Kähler, `(β, t) ↦ π^*β + t{E}` is a linear isomorphism
  `H^{1,1}(X, ℝ) × ℝ ≃ H^{1,1}(Y, ℝ)`, i.e. `H^{1,1}(Y,ℝ) = H^{1,1}(X,ℝ) ⊕ ℝ{E}`.
* `exists_kahler_isBlowupAlong`: the blow-up of a compact Kähler manifold along a nowhere dense
  closed submanifold exists, is an analytic modification and is compact Kähler.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

universe u

open Set Filter
open scoped Topology Manifold ContDiff

namespace SGPT.Blowup

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.BlowupSequences
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses
  SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
  SGPT.Foundations.Analysis.Pending.CurrentBottChernClass
  SGPT.Hodge.Exceptional SGPT.BDivisor

section Connected

variable {n : ℕ} {X Y : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y]

/-- **The preimage of a closed connected set under an analytic modification is connected**:
the modification is a closed surjection with connected fibres. -/
theorem isConnected_preimage_of_isAnalyticModification {π : Y → X}
    (hπ : IsAnalyticModification (n := n) π) {S : Set X} (hSc : IsClosed S)
    (hS : IsConnected S) : IsConnected (π ⁻¹' S) := by
  have hfib := fun x : X => (AnalyticModificationConnectedFibres.isConnected_fibre hπ x).1
  have hsurj : Function.Surjective π := fun x => (hfib x).nonempty
  have hq : Topology.IsQuotientMap π :=
    hπ.2.1.isClosedMap.isQuotientMap hπ.1.continuous hsurj
  exact hq.isCoinducing.isConnected_preimage_of_isClosed hfib hSc hS

end Connected

section Exceptional

variable {m : ℕ} {X Y : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X]
  [IsComplexManifold (m + 1) X] [TopologicalSpace Y] [ChartedSpace (ComplexModel (m + 1)) Y]
  [IsComplexManifold (m + 1) Y] {C : Set X} {π : Y → X}

/-- **The exceptional divisor of the blow-up along a connected centre is a closed connected smooth
hypersurface.** -/
theorem isClosedConnectedSubmanifold_exceptional (hπ : IsBlowupAlong (m + 1) C π)
    (hC : IsConnected C) : IsClosedConnectedSubmanifold (m + 1) (π ⁻¹' C) m := by
  have hsnc := BlowupSNCTransform.isSNCDivisor_preimage_centre hπ
  refine ⟨hπ.1.1.preimage hπ.contMDiff.continuous,
    isConnected_preimage_of_isAnalyticModification
      (PrescribedBlowupDomination.isAnalyticModification_of_isBlowupAlong hπ) hπ.1.1 hC,
    fun y hy => ?_⟩
  exact SNCGlobalPrimeComponents.regularAtDim_member hsnc ⟨0, by simp⟩ (x := y) hy

/-- **Over a centre of codimension at least two the exceptional locus is the whole preimage of
the centre.** -/
theorem exceptionalLocus_eq_preimage (hπ : IsBlowupAlong (m + 1) C π) {k : ℕ}
    (hCk : ∀ x ∈ C, RegularAtDim (n := m + 1) C x k) (hk : k + 2 ≤ m + 1) :
    exceptionalLocus (m + 1) π = π ⁻¹' C := by
  refine Subset.antisymm (BlowupIsomorphismOff.exceptionalLocus_subset_preimage hπ)
    fun z hz => ?_
  obtain ⟨-, -, Φ, hΦsrc, -, hflat⟩ := hCk (π z) hz
  exact BlowupCodimOne.mem_exceptionalLocus_of_codim_ge_two hπ hΦsrc
    (fun hy hyΦ => hflat hy hyΦ) hk (BlowupFlatCoordinates.mem_flatDomain_self Φ) hz

/-- The exceptional divisor `E = π⁻¹(C)` of the blow-up along a connected centre, as a prime
divisor of `Y`. -/
def exceptionalPrime (hπ : IsBlowupAlong (m + 1) C π) (hC : IsConnected C) :
    SGPT.PSH.GeometricPrimeCarrier (m + 1) Y :=
  ⟨π ⁻¹' C, by
    obtain ⟨V, hV, hdim⟩ := SourceGenericSubmanifoldMinimum.exists_subvariety_carrier_eq_of_submanifold
      (isClosedConnectedSubmanifold_exceptional hπ hC)
    exact ⟨V, hV, by rw [hdim]⟩⟩

@[simp] theorem exceptionalPrime_val (hπ : IsBlowupAlong (m + 1) C π) (hC : IsConnected C) :
    (exceptionalPrime hπ hC).val = π ⁻¹' C := rfl

variable [CompactSpace X] [CompactSpace Y]

/-- **The exceptional divisor is the only `π`-exceptional prime divisor** of the blow-up along
a connected centre of codimension at least two. -/
theorem excPrimes_eq_singleton (hπ : IsBlowupAlong (m + 1) C π) {k : ℕ}
    (hC : IsClosedConnectedSubmanifold (m + 1) C k) (hk : k + 2 ≤ m + 1) :
    excPrimes (PrescribedBlowupDomination.isAnalyticModification_of_isBlowupAlong hπ) =
      {exceptionalPrime hπ hC.2.1} := by
  ext D
  rw [mem_excPrimes, Finset.mem_singleton, exceptionalLocus_eq_preimage hπ hC.2.2 hk]
  constructor
  · intro hD
    exact SGPT.Siu.eq_of_subset (P := D) (Q := exceptionalPrime hπ hC.2.1) hD
  · rintro rfl
    exact Subset.rfl

/-- **Source `prop:blowup_cone`.** Let `X` be a compact Kähler manifold and `π : Y → X` the
blow-up along a connected closed complex submanifold `C` of codimension at least two, with
exceptional divisor `E = π⁻¹(C)`.  Then `(β, t) ↦ π^*β + t{E}` is a bijection
`H^{1,1}(X, ℝ) × ℝ → H^{1,1}(Y, ℝ)`. -/
theorem blowupCone_bijective (ωX : KahlerBackground (m + 1) X)
    (hπ : IsBlowupAlong (m + 1) C π) {k : ℕ} (hC : IsClosedConnectedSubmanifold (m + 1) C k)
    (hk : k + 2 ≤ m + 1) :
    Function.Bijective (fun p : RealBottChern (m + 1) X × ℝ =>
      classPullback hπ.contMDiff p.1 + p.2 • primeDivisorClass (exceptionalPrime hπ hC.2.1)) := by
  obtain ⟨ωY⟩ := (BlowupKahler.compactSpace_and_kahler_of_isBlowupAlong ⟨ωX⟩ hπ).2
  exact blowupClassMap_single_bijective
    (PrescribedBlowupDomination.isAnalyticModification_of_isBlowupAlong hπ) ωY _
    (excPrimes_eq_singleton hπ hC hk)

/-- **Source `eq:H11blowup`**: the natural identification
`H^{1,1}(X, ℝ) ⊕ ℝ{E} ≃ H^{1,1}(Y, ℝ)`, `(β, t) ↦ π^*β + t{E}`. -/
def blowupConeEquiv (ωX : KahlerBackground (m + 1) X) (hπ : IsBlowupAlong (m + 1) C π) {k : ℕ}
    (hC : IsClosedConnectedSubmanifold (m + 1) C k) (hk : k + 2 ≤ m + 1) :
    (RealBottChern (m + 1) X × ℝ) ≃ₗ[ℝ] RealBottChern (m + 1) Y :=
  LinearEquiv.ofBijective
    ((classPullback hπ.contMDiff).comp (LinearMap.fst ℝ _ _) +
      (LinearMap.smulRight (LinearMap.id : ℝ →ₗ[ℝ] ℝ)
        (primeDivisorClass (exceptionalPrime hπ hC.2.1))).comp (LinearMap.snd ℝ _ _))
    (blowupCone_bijective ωX hπ hC hk)

theorem blowupConeEquiv_apply (ωX : KahlerBackground (m + 1) X) (hπ : IsBlowupAlong (m + 1) C π)
    {k : ℕ} (hC : IsClosedConnectedSubmanifold (m + 1) C k) (hk : k + 2 ≤ m + 1)
    (β : RealBottChern (m + 1) X) (t : ℝ) :
    blowupConeEquiv ωX hπ hC hk (β, t) =
      classPullback hπ.contMDiff β + t • primeDivisorClass (exceptionalPrime hπ hC.2.1) :=
  rfl

end Exceptional

section Existence

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

/-- **The blow-up of a compact Kähler manifold along a nowhere dense closed submanifold exists
and is compact Kähler** (Demailly's construction; Blanchard). -/
theorem exists_kahler_isBlowupAlong [CompactSpace X] (omega : KahlerBackground n X) {C : Set X}
    (hC : IsClosedSubmanifold n C) (hCint : interior C = ∅) :
    ∃ (Y : Type u) (_ : TopologicalSpace Y) (_ : ChartedSpace (ComplexModel n) Y)
      (_ : IsComplexManifold n Y) (π : Y → X), IsBlowupAlong n C π ∧
        IsAnalyticModification (n := n) π ∧ CompactSpace Y ∧ Nonempty (KahlerBackground n Y) := by
  obtain ⟨Y, _, _, _, π, hπ⟩ := BlowupExistence.exists_isBlowupAlong C hC hCint
  exact ⟨Y, inferInstance, inferInstance, inferInstance, π, hπ,
    PrescribedBlowupDomination.isAnalyticModification_of_isBlowupAlong hπ,
    BlowupKahler.compactSpace_and_kahler_of_isBlowupAlong ⟨omega⟩ hπ⟩

end Existence

end SGPT.Blowup
