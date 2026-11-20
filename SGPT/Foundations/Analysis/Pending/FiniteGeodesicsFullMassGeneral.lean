import SGPT.Foundations.Analysis.Pending.FiniteGeodesics
import SGPT.Foundations.Analysis.Pending.RooftopEnvelopeLatticeMass
import SGPT.Foundations.Analysis.Pending.BoucksomMassBigness
import SGPT.Foundations.Analysis.Pending.KahlerDomination

set_option autoImplicit false

/-!
# Full-mass Perron geodesics and shifted rooftops without bigness or envelope hypotheses

Xia, *Singularities in global pluripotential theory* (SGPT), §4.2 (`xia-sgpt:page-0154`--`page-0156`),
works on a connected compact Kähler manifold `X` of dimension `n`, with `θ` representing a BIG class and a
model potential `φ` of positive mass. The full-mass theorems of `Pending.FiniteGeodesics` and
`Pending.RelativeFullMass` carry two extra hypotheses:
* `BigWithRespectToViaPotentials omega theta` (Xia's bigness);
* `RooftopMassDiamondReduction.EnvelopeLatticeMassReduction omega theta` (the mass identities of Step 1
  of Xia's Theorem 3.1.3).

Here both are discharged, so every statement below assumes only:
* a connected compact Kähler manifold of positive dimension;
* a model potential (`IsModelPotential`, which includes positive mass);
* endpoints in the relevant relative class.

* **Bigness is implied by the model potential.** A `θ`-psh potential of positive non-pluripolar mass
  makes `{θ}` big: `BoucksomMassBigness.isBigClass_of_diagonalPotentialMass_pos`, which is Boucksom's
  criterion. `bigWithRespectToViaPotentials_of_isBigClass` turns a Kähler current in `{θ}` into the
  potential form of bigness relative to any Kähler background, by comparing two Kähler forms on a compact
  manifold (`KahlerDomination.exists_pos_isSemipositive_add_smul`). So Xia's bigness assumption is
  redundant once a model potential of positive mass is fixed.
* **The envelope identities are proved.** `RooftopEnvelopeLatticeMass.envelopeLatticeMassReduction`
  discharges them.

## Main results

* `bigWithRespectToViaPotentials_of_isBigClass`, `bigWithRespectToViaPotentials_of_isModelPotential`.
* Shifted rooftops: `reference_mass_le_rooftop_add_const` and `relativeFullMass_rooftop_add_const_tendsto`
  (rooftop exhaustion).
* Full-mass Perron geodesics:
  - `finiteGeodesic_isSubgeodesicInterior_of_relativeFullMass`;
  - endpoint recovery `finiteGeodesic_tendsto_left_of_relativeFullMass` / `_right_`;
  - `finiteGeodesic_isSubgeodesicFrom_of_relativeFullMass`;
  - `relativeFullMass_finiteGeodesic` (slices).
* The same for finite-energy endpoints (`..._of_relativeFiniteEnergy`, `relativeFiniteEnergy_finiteGeodesic`)
  and for endpoints of bounded singularity type (`..._of_relativeEInfinity`, `relativeEInfinity_finiteGeodesic`).

Each geodesic theorem is the corresponding theorem of `Pending.FiniteGeodesics` with the two hypotheses
supplied. No statement of that module is changed.
-/

namespace SGPT.Foundations.Analysis.Pending.FiniteGeodesicsFullMassGeneral

open Filter Set
open scoped Topology
open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus Pending.DiagonalMass

noncomputable section

section Bridge

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] [CompactSpace M]

/-- **A big class is big relative to every Kähler background.**  A Kähler current in `{θ}` dominates some
Kähler form `ω_L`; on a compact manifold `ω_L ≥ ε ω` for some `ε > 0`, and the potential of the current
is then `(θ - ε ω)`-psh after transport along the Bott--Chern relation. -/
theorem bigWithRespectToViaPotentials_of_isBigClass (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) (hθ : IsBigClass (RealBottChern.ofRepresentative θ)) :
    BigWithRespectToViaPotentials omega θ := by
  obtain ⟨T⟩ := hθ
  obtain ⟨A, hA, hsemi⟩ :=
    KahlerDomination.exists_pos_isSemipositive_add_smul T.lowerBound (-omega.form)
  have hε : 0 < A⁻¹ := inv_pos.mpr hA
  have hdiff : (T.lowerBound.form - A⁻¹ • omega.form).val.IsSemipositive := by
    have heq : T.lowerBound.form - A⁻¹ • omega.form =
        A⁻¹ • (-omega.form + A • T.lowerBound.form) := by
      rw [smul_add, smul_smul, inv_mul_cancel₀ hA.ne', one_smul, smul_neg]
      abel
    rw [heq]
    intro e z hz
    exact coefficientSemipositive_smul hε.le (hsemi e z hz)
  have hpsh := Pending.LocalPotentials.isThetaPshPotential_add_of_semipositive T.strictlyPsh hdiff
  have hform : T.representative - T.lowerBound.form + (T.lowerBound.form - A⁻¹ • omega.form) =
      T.representative - A⁻¹ • omega.form := by abel
  rw [hform] at hpsh
  have hbig' : BigWithRespectToViaPotentials omega T.representative :=
    ⟨A⁻¹, hε, T.potential, hpsh⟩
  exact bigWithRespectToViaPotentials_of_bottChernRel omega
    ((RealBottChern.ofRepresentative_eq_iff _ _).mp T.represents) hbig'

end Bridge

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M] [Nonempty M]

/-- **A model potential forces bigness.**  On a connected compact Kähler manifold of positive dimension, a
model potential has positive non-pluripolar mass, so `{θ}` is big (Boucksom's criterion). -/
theorem bigWithRespectToViaPotentials_of_isModelPotential (hn : 0 < n)
    (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M) {phi : M → EReal}
    (hphi : IsModelPotential theta phi) : BigWithRespectToViaPotentials omega theta :=
  bigWithRespectToViaPotentials_of_isBigClass omega theta
    (BoucksomMassBigness.isBigClass_of_diagonalPotentialMass_pos hn omega theta
      hphi.plurisubharmonic hphi.positive_mass)

/-- **Rooftop mass lower bound** (Xia SGPT, `xia-sgpt:page-0108`, `page-0132`).
For `u, v ∈ E(X, θ; φ)` and `C ∈ ℝ`, the rooftop `P_θ(min(u, v + C))` is `θ`-psh and its mass is at least
that of `φ`. -/
theorem reference_mass_le_rooftop_add_const (hn : 0 < n) (omega : KahlerBackground n M)
    (theta : ClosedRealOneOneForm n M) (phi u v : M → EReal) (hphi : IsModelPotential theta phi)
    (hu : RelativeFullMass theta phi u hphi) (hv : RelativeFullMass theta phi v hphi) (C : ℝ) :
    ∃ hw : IsThetaPshPotential theta.val
        (rooftopEnvelope theta.val (fun x => min (u x) (v x + (C : EReal)))),
      diagonalPotentialMass theta phi hphi.plurisubharmonic ≤
        diagonalPotentialMass theta
          (rooftopEnvelope theta.val (fun x => min (u x) (v x + (C : EReal)))) hw :=
  ⟨isThetaPshPotential_rooftop_add_const hn omega theta phi u v hphi hu hv C,
    Pending.reference_mass_le_rooftop_add_const hn omega theta phi u v hphi hu hv C _
      (RooftopEnvelopeLatticeMass.envelopeLatticeMassReduction omega theta)⟩

/-- **Rooftop exhaustion** (Xia SGPT, `xia-sgpt:page-0134`--`page-0135`): for `u, v ∈ E(X, θ; φ)` the
shifted rooftops `P_θ(min(u, v + C))` converge to `u` in chart-local `L¹` as `C → +∞`. -/
theorem relativeFullMass_rooftop_add_const_tendsto (hn : 0 < n) (omega : KahlerBackground n M)
    (theta : ClosedRealOneOneForm n M) (phi u v : M → EReal) (hphi : IsModelPotential theta phi)
    (hu : RelativeFullMass theta phi u hphi) (hv : RelativeFullMass theta phi v hphi) :
    ManifoldL1LocallyTendsto (n := n)
      (fun C : ℝ => rooftopEnvelope theta.val (fun x => min (u x) (v x + (C : EReal))))
      atTop u :=
  Pending.relativeFullMass_rooftop_add_const_tendsto hn omega theta phi u v hphi hu hv
    (RooftopEnvelopeLatticeMass.envelopeLatticeMassReduction omega theta)

/-- **Perron interior for full-mass endpoints** (Xia SGPT, Proposition 4.1.3 / 4.2.1). -/
theorem finiteGeodesic_isSubgeodesicInterior_of_relativeFullMass (hn : 0 < n)
    (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M)
    (phi u₀ u₁ : M → EReal) (hphi : IsModelPotential theta phi)
    (hu₀ : RelativeFullMass theta phi u₀ hphi) (hu₁ : RelativeFullMass theta phi u₁ hphi) :
    IsSubgeodesicInterior theta.val (finiteGeodesic theta.val u₀ u₁) :=
  Pending.finiteGeodesic_isSubgeodesicInterior_of_relativeFullMass hn omega theta
    (bigWithRespectToViaPotentials_of_isModelPotential hn omega theta hphi) phi u₀ u₁ hphi hu₀ hu₁

/-- **Left endpoint recovery** for full-mass endpoints: `G_t(u₀, u₁) → u₀` in chart-local `L¹` as `t → 0+`. -/
theorem finiteGeodesic_tendsto_left_of_relativeFullMass (hn : 0 < n)
    (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M)
    (phi u₀ u₁ : M → EReal) (hphi : IsModelPotential theta phi)
    (hu₀ : RelativeFullMass theta phi u₀ hphi) (hu₁ : RelativeFullMass theta phi u₁ hphi) :
    ManifoldL1LocallyTendsto (n := n) (finiteGeodesic theta.val u₀ u₁) (𝓝[>] (0 : ℝ)) u₀ :=
  Pending.finiteGeodesic_tendsto_left_of_relativeFullMass hn omega theta
    (bigWithRespectToViaPotentials_of_isModelPotential hn omega theta hphi) phi u₀ u₁ hphi hu₀ hu₁
    (RooftopEnvelopeLatticeMass.envelopeLatticeMassReduction omega theta)

/-- **Right endpoint recovery** for full-mass endpoints: `G_t(u₀, u₁) → u₁` in chart-local `L¹` as `t → 1-`. -/
theorem finiteGeodesic_tendsto_right_of_relativeFullMass (hn : 0 < n)
    (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M)
    (phi u₀ u₁ : M → EReal) (hphi : IsModelPotential theta phi)
    (hu₀ : RelativeFullMass theta phi u₀ hphi) (hu₁ : RelativeFullMass theta phi u₁ hphi) :
    ManifoldL1LocallyTendsto (n := n) (finiteGeodesic theta.val u₀ u₁) (𝓝[<] (1 : ℝ)) u₁ :=
  Pending.finiteGeodesic_tendsto_right_of_relativeFullMass hn omega theta
    (bigWithRespectToViaPotentials_of_isModelPotential hn omega theta hphi) phi u₀ u₁ hphi hu₀ hu₁
    (RooftopEnvelopeLatticeMass.envelopeLatticeMassReduction omega theta)

/-- **Xia SGPT, Proposition 4.2.1, full-mass case**: the Perron envelope is a subgeodesic from `u₀` to `u₁`. -/
theorem finiteGeodesic_isSubgeodesicFrom_of_relativeFullMass (hn : 0 < n)
    (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M)
    (phi u₀ u₁ : M → EReal) (hphi : IsModelPotential theta phi)
    (hu₀ : RelativeFullMass theta phi u₀ hphi) (hu₁ : RelativeFullMass theta phi u₁ hphi) :
    IsSubgeodesicFrom theta.val (finiteGeodesic theta.val u₀ u₁) u₀ u₁ :=
  Pending.finiteGeodesic_isSubgeodesicFrom_of_relativeFullMass hn omega theta
    (bigWithRespectToViaPotentials_of_isModelPotential hn omega theta hphi) phi u₀ u₁ hphi hu₀ hu₁
    (RooftopEnvelopeLatticeMass.envelopeLatticeMassReduction omega theta)

/-- Every interior Perron slice between full-mass endpoints has relative full mass. -/
theorem relativeFullMass_finiteGeodesic (hn : 0 < n)
    (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M)
    (phi u₀ u₁ : M → EReal) (hphi : IsModelPotential theta phi)
    (hu₀ : RelativeFullMass theta phi u₀ hphi) (hu₁ : RelativeFullMass theta phi u₁ hphi)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    RelativeFullMass theta phi (finiteGeodesic theta.val u₀ u₁ t) hphi :=
  Pending.relativeFullMass_finiteGeodesic hn omega theta
    (bigWithRespectToViaPotentials_of_isModelPotential hn omega theta hphi) phi u₀ u₁ hphi hu₀ hu₁
    (RooftopEnvelopeLatticeMass.envelopeLatticeMassReduction omega theta) t ht

/-- Finite-energy endpoints give a subgeodesic from `u₀` to `u₁`. -/
theorem finiteGeodesic_isSubgeodesicFrom_of_relativeFiniteEnergy (hn : 0 < n)
    (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M)
    (phi u₀ u₁ : M → EReal) (hphi : IsModelPotential theta phi)
    (hu₀ : RelativeFiniteEnergy theta phi u₀ hphi) (hu₁ : RelativeFiniteEnergy theta phi u₁ hphi) :
    IsSubgeodesicFrom theta.val (finiteGeodesic theta.val u₀ u₁) u₀ u₁ :=
  Pending.finiteGeodesic_isSubgeodesicFrom_of_relativeFiniteEnergy hn omega theta
    (bigWithRespectToViaPotentials_of_isModelPotential hn omega theta hphi) phi u₀ u₁ hphi hu₀ hu₁
    (RooftopEnvelopeLatticeMass.envelopeLatticeMassReduction omega theta)

/-- **Xia SGPT, Proposition 4.2.1, finite-energy case**: every interior slice has finite relative energy. -/
theorem relativeFiniteEnergy_finiteGeodesic (hn : 0 < n)
    (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M)
    (phi u₀ u₁ : M → EReal) (hphi : IsModelPotential theta phi)
    (hu₀ : RelativeFiniteEnergy theta phi u₀ hphi) (hu₁ : RelativeFiniteEnergy theta phi u₁ hphi)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    RelativeFiniteEnergy theta phi (finiteGeodesic theta.val u₀ u₁ t) hphi :=
  Pending.relativeFiniteEnergy_finiteGeodesic hn omega theta
    (bigWithRespectToViaPotentials_of_isModelPotential hn omega theta hphi) phi u₀ u₁ hphi hu₀ hu₁
    (RooftopEnvelopeLatticeMass.envelopeLatticeMassReduction omega theta) t ht

/-- Endpoints of bounded singularity type give a subgeodesic from `u₀` to `u₁`. -/
theorem finiteGeodesic_isSubgeodesicFrom_of_relativeEInfinity (hn : 0 < n)
    (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M)
    (phi u₀ u₁ : M → EReal) (hphi : IsModelPotential theta phi)
    (hu₀ : RelativeEInfinity theta phi u₀) (hu₁ : RelativeEInfinity theta phi u₁) :
    IsSubgeodesicFrom theta.val (finiteGeodesic theta.val u₀ u₁) u₀ u₁ :=
  Pending.finiteGeodesic_isSubgeodesicFrom_of_relativeEInfinity hn omega theta
    (bigWithRespectToViaPotentials_of_isModelPotential hn omega theta hphi) phi u₀ u₁ hphi hu₀ hu₁

/-- Every interior slice between endpoints of bounded singularity type has that singularity type. -/
theorem relativeEInfinity_finiteGeodesic (hn : 0 < n)
    (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M)
    (phi u₀ u₁ : M → EReal) (hphi : IsModelPotential theta phi)
    (hu₀ : RelativeEInfinity theta phi u₀) (hu₁ : RelativeEInfinity theta phi u₁)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    RelativeEInfinity theta phi (finiteGeodesic theta.val u₀ u₁ t) :=
  Pending.relativeEInfinity_finiteGeodesic hn omega theta
    (bigWithRespectToViaPotentials_of_isModelPotential hn omega theta hphi) phi u₀ u₁ hphi hu₀ hu₁ t ht

end

end SGPT.Foundations.Analysis.Pending.FiniteGeodesicsFullMassGeneral
