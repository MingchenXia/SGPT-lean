import SGPT.Foundations.Analysis.Pending.AnalyticTypeRestriction
import SGPT.Foundations.Analysis.Pending.SubmanifoldKahlerRestriction
import SGPT.Foundations.Analysis.Pending.GlobalPotentialPullback
import SGPT.Foundations.Analysis.Pending.ThetaPshIdentityPrinciple
import SGPT.Foundations.Analysis.Pending.StepFourNoComponentContainsW
import SGPT.Foundations.Analysis.Pending.ModificationInputs
import SGPT.Foundations.Analysis.Pending.QuasiEquisingularApproximationDemailly

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Potentials on a closed connected submanifold: restriction, backgrounds, restricted approximants

Source: Copy-4, `sec:setup` ("We write `ω_V := ω|_V` and `γ := θ|_V`") and `sec:trace-approx`
(`references/transcendental-nakamaye-copy4-20260911/source/main-Nulllocus.tex:1388-1460`):

> Since `𝔅_q ⊄ 𝓘_V`, the restriction `φ_q := Φ^D_q|_V` is not identically `-∞`, and it has
> analytic singularities of type `(q⁻¹, 𝔅̄_q)`. Set `β_q := γ + η_q ω_V`, so that
> `φ_q ∈ PSH(V, β_q)`.

`V` is a closed connected complex submanifold `W` of dimension `k`, with the complex structure of
`Pending.SubmanifoldChartedSpace` (the one `Copy4FixedDataFromInputs.IsLevelPotential` uses) and
the Kähler background `ω_V` of `Pending.SubmanifoldKahlerRestriction`.  The non-pluripolar mass
calculus Copy-4 uses on `V` — monotonicity in the background
(`AmbientMassBackgroundMonotone.diagonalPotentialMass_le_add_smul`), the convex-combination bound
`tᵏ θ_a^k ≤ θ_{ta+(1-t)b}^k` (`GlobalDiagonalConvexScaling`), multilinearity
(`GlobalMultilinearExpansion`), finiteness (`GlobalNonPluripolarKahler`) and monotonicity in the
singularity order (`SingularityEnvelopeMassProof.diagonalPotentialMass_mono_of_kahler`) — is
proved in the tree for an arbitrary compact Kähler manifold; this module supplies what is needed
to apply it on `V`:

* `compactSpace_of_isClosed`, `connectedSpace_of_isClosedConnectedSubmanifold` — `V` is compact
  and connected;
* `thetaPlurisubharmonic_pullback_add_smul_iff`, `isThetaPshPotential_pullback_add_smul_iff` —
  `(θ + c ω)|_V`-psh is `θ|_V + c ω_V`-psh (pullback is linear up to geometric equality);
* `isThetaPshPotential_comp_val` — **the restriction of a potential with analytic singularities of
  type `(c, 𝔞)` with `V ⊄ Z(𝔞)` is a genuine potential on `V`**, of type `(c, Res_V 𝔞)`: it is
  finite at a point of `V \ Z(𝔞)` (`StepFourNoComponentContainsW.poleSet_eq_zeroLocus`), hence
  locally nondegenerate on the connected `V` (identity principle,
  `ThetaPshIdentityPrinciple.locallyNondegenerate_of_exists_ne_bot`);
* `exists_restrictedApproximants` — **Copy-4 `sec:trace-approx` for any `θ`-psh `ψ` satisfying the
  Skoda clause** (for `ψ = V_θ` this clause is `TraceInputSkoda`): Demailly's quasi-equisingular
  approximation `Φ_j` of `ψ` (type `(2^{-j}, 𝓘(2^jψ))`, `QuasiEquisingularApproximationDemailly`)
  restricts to `φ_j = Φ_j|_V ∈ PSH(V, γ + ε_j ω_V)` of type `(2^{-j}, Res_V 𝓘(2^jψ))`.

Programme `TN.2.3.PCI`, piece C4 of `scratch/tn23-envelopes-qea-plan-0117.md` §5.3.  Sorry-free.
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace SGPT.Foundations.Analysis.Pending.SubmanifoldMassCalculus

noncomputable section

open FirstPass FirstPass.PositiveClasses FirstPass.HolomorphicIdealSheaves
  FirstPass.GlobalAnalyticSingularities FirstPass.BlowupSequences
  FirstPass.QuasiEquisingularApproximation SubmanifoldChartedSpace
  SubmanifoldIdealRestriction AnalyticTypeRestriction

variable {n k : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {W : Set X}

/-! ### `V` is compact and connected -/

/-- A closed subset of a compact space is compact as a subtype. -/
theorem compactSpace_of_isClosed [CompactSpace X] (hWc : IsClosed W) : CompactSpace W :=
  isCompact_iff_compactSpace.mp hWc.isCompact

/-- A closed connected submanifold is connected as a subtype. -/
theorem connectedSpace_of_isClosedConnectedSubmanifold
    (hV : IsClosedConnectedSubmanifold n W k) : ConnectedSpace W :=
  isConnected_iff_connectedSpace.mp hV.2.1

/-! ### Restricted backgrounds -/

section Backgrounds

variable (hk : k ≤ n) (hW : ∀ x ∈ W, RegularAtDim (n := n) W x k)

include hk hW in
/-- **`(θ + c ω)|_V = θ|_V + c ω|_V`** at the level of `θ`-plurisubharmonicity. -/
theorem thetaPlurisubharmonic_pullback_add_smul_iff (θ β : ClosedRealOneOneForm n X) (c : ℝ) :
    letI := chartedSpace hk hW
    haveI := isComplexManifold_chartedSpace hk hW
    ∀ v : W → EReal,
      ThetaPlurisubharmonic
          (ClosedRealOneOneForm.pullback (contMDiff_val hk hW) (θ + c • β)).val v ↔
        ThetaPlurisubharmonic
          (ClosedRealOneOneForm.pullback (contMDiff_val hk hW) θ +
            c • ClosedRealOneOneForm.pullback (contMDiff_val hk hW) β).val v := by
  let := chartedSpace hk hW
  have := isComplexManifold_chartedSpace hk hW
  intro v
  exact (ModificationInputs.pullback_add_smul_geometricallyEq (contMDiff_val hk hW) θ β c
    ).thetaPlurisubharmonic_iff v

include hk hW in
/-- `isThetaPshPotential` form of `thetaPlurisubharmonic_pullback_add_smul_iff`. -/
theorem isThetaPshPotential_pullback_add_smul_iff (θ β : ClosedRealOneOneForm n X) (c : ℝ) :
    letI := chartedSpace hk hW
    haveI := isComplexManifold_chartedSpace hk hW
    ∀ v : W → EReal,
      IsThetaPshPotential
          (ClosedRealOneOneForm.pullback (contMDiff_val hk hW) (θ + c • β)).val v ↔
        IsThetaPshPotential
          (ClosedRealOneOneForm.pullback (contMDiff_val hk hW) θ +
            c • ClosedRealOneOneForm.pullback (contMDiff_val hk hW) β).val v := by
  let := chartedSpace hk hW
  have := isComplexManifold_chartedSpace hk hW
  intro v
  exact and_congr_left' (thetaPlurisubharmonic_pullback_add_smul_iff hk hW θ β c v)

end Backgrounds

/-! ### Restricting a potential with analytic singularities -/

section Restriction

variable (hV : IsClosedConnectedSubmanifold n W k)

include hV in
/-- **The restriction to `V` of a `θ`-psh function with analytic singularities of type `(c, 𝔞)`,
`V ⊄ Z(𝔞)`, is a genuine `θ|_V`-psh potential of type `(c, Res_V 𝔞)`.**  Nondegeneracy is the
only point: the restriction is finite at any point of `V \ Z(𝔞)` (the pole set of a function of
type `(c, 𝔞)` is `Z(𝔞)`), and a `θ|_V`-psh function finite at one point of the connected manifold
`V` is locally nondegenerate. -/
theorem isThetaPshPotential_comp_val {θ : ClosedRealOneOneForm n X} {Φ : X → EReal}
    (hΦ : ThetaPlurisubharmonic θ.val Φ) {c : ℚ} {𝔞 : GermIdeal n X}
    (htype : HasAnalyticSingularitiesOfType (n := n) Φ c 𝔞) (hnz : ¬ W ⊆ 𝔞.zeroLocus) :
    letI := chartedSpace (le_of_isClosedConnectedSubmanifold hV) hV.2.2
    haveI := isComplexManifold_chartedSpace (le_of_isClosedConnectedSubmanifold hV) hV.2.2
    IsThetaPshPotential
        (ClosedRealOneOneForm.pullback
          (contMDiff_val (le_of_isClosedConnectedSubmanifold hV) hV.2.2) θ).val
        (fun q : W => Φ q.1) ∧
      HasAnalyticSingularitiesOfType (n := k) (fun q : W => Φ q.1) c
        (restrictIdeal (k := k) (W := W) 𝔞) := by
  set hk := le_of_isClosedConnectedSubmanifold hV
  let := chartedSpace hk hV.2.2
  have := isComplexManifold_chartedSpace hk hV.2.2
  have := connectedSpace_of_isClosedConnectedSubmanifold hV
  have hval := contMDiff_val hk hV.2.2
  have hpsh := GlobalPotentialPullback.thetaPlurisubharmonic_comp hval hΦ
  obtain ⟨x, hxW, hxZ⟩ := not_subset.mp hnz
  have hfin : Φ x ≠ ⊥ := by
    intro hbot
    apply hxZ
    rw [← StepFourNoComponentContainsW.poleSet_eq_zeroLocus htype]
    exact hbot
  refine ⟨⟨hpsh, ThetaPshIdentityPrinciple.locallyNondegenerate_of_exists_ne_bot hpsh
    ⟨⟨x, hxW⟩, hfin⟩⟩, ?_⟩
  exact hasAnalyticSingularitiesOfType_comp hval htype

end Restriction

/-! ### Copy-4 `sec:trace-approx`: the restricted approximants -/

section Approximants

variable [CompactSpace X] (hV : IsClosedConnectedSubmanifold n W k)

include hV in
/-- **Copy-4 `sec:trace-approx`.**  Let `ψ` be `θ`-psh on the compact Kähler `X` with
`V ⊄ Z(𝓘(qψ))` for every `q ≥ 1` (for `ψ = V_θ` this is the Skoda clause, proved in
`TraceInputSkoda`).  Demailly's quasi-equisingular approximation `Φ_j` of `ψ` (errors `ε_j`) has
global type `(2^{-j}, 𝓘(2^jψ))`, and its restrictions `φ_j = Φ_j|_V` are genuine potentials on
`V` for `β_j = γ + ε_j ω_V` (`γ = θ|_V`, `ω_V = ω|_V`), of type `(2^{-j}, Res_V 𝓘(2^jψ))`. -/
theorem exists_restrictedApproximants (hn : 0 < n) (omega : KahlerBackground n X)
    (θ : ClosedRealOneOneForm n X) {ψ : X → EReal} (hψ : IsThetaPshPotential θ.val ψ)
    (hskoda : ∀ q : ℕ, 1 ≤ q → ¬ W ⊆ (multiplierIdeal (n := n) (q : ℝ) ψ).zeroLocus) :
    letI := chartedSpace (le_of_isClosedConnectedSubmanifold hV) hV.2.2
    haveI := isComplexManifold_chartedSpace (le_of_isClosedConnectedSubmanifold hV) hV.2.2
    ∃ ε : ℕ → ℝ, ∃ Φ : ℕ → X → EReal,
      IsQuasiEquisingularApproximation omega θ ψ ε Φ ∧
      (∀ j, HasAnalyticSingularitiesOfType (n := n) (Φ j) (((2 ^ j : ℕ) : ℚ)⁻¹)
        (multiplierIdeal (n := n) ((2 ^ j : ℕ) : ℝ) ψ)) ∧
      (∀ j, IsThetaPshPotential
        (ClosedRealOneOneForm.pullback
            (contMDiff_val (le_of_isClosedConnectedSubmanifold hV) hV.2.2) θ +
          ε j • (SubmanifoldKahlerRestriction.kahlerBackground
            (le_of_isClosedConnectedSubmanifold hV) hV.2.2 omega).form).val
        (fun q : W => Φ j q.1)) ∧
      (∀ j, HasAnalyticSingularitiesOfType (n := k) (fun q : W => Φ j q.1)
        (((2 ^ j : ℕ) : ℚ)⁻¹)
        (restrictIdeal (k := k) (W := W) (multiplierIdeal (n := n) ((2 ^ j : ℕ) : ℝ) ψ))) := by
  set hk := le_of_isClosedConnectedSubmanifold hV
  let := chartedSpace hk hV.2.2
  have := isComplexManifold_chartedSpace hk hV.2.2
  obtain ⟨ε, Φ, hqea, htype⟩ :=
    QuasiEquisingularApproximationDemailly.exists_quasiEquisingularApproximation_ofType hn omega
      θ hψ
  have hnz : ∀ j : ℕ, ¬ W ⊆ (multiplierIdeal (n := n) ((2 ^ j : ℕ) : ℝ) ψ).zeroLocus :=
    fun j => hskoda (2 ^ j) (Nat.one_le_two_pow)
  have hres := fun j => isThetaPshPotential_comp_val hV (hqea.term j).1 (htype j) (hnz j)
  refine ⟨ε, Φ, hqea, htype, fun j => ?_, fun j => (hres j).2⟩
  exact (isThetaPshPotential_pullback_add_smul_iff hk hV.2.2 θ omega.form (ε j) _).mp
    (hres j).1

end Approximants

end

end SGPT.Foundations.Analysis.Pending.SubmanifoldMassCalculus
