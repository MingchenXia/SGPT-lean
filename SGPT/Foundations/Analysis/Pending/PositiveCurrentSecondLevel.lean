import SGPT.Foundations.Analysis.Pending.SubmanifoldMassCalculus
import SGPT.Foundations.Analysis.Pending.Copy4FixedDataFromInputs
import SGPT.Foundations.Analysis.Pending.MultiplierIdealBergmanNadelManifold
import SGPT.Foundations.Analysis.Pending.KahlerDomination
import SGPT.Foundations.Analysis.Pending.LocalPotentials

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Copy-4 `sec:positive-current`: the second level `K_ℓ` and the encoding of `PositiveCurrentInput`

Source: Copy-4, `sec:positive-current`, "The second level and the current `K_ℓ`" and
`lem:ideal-comparison` (`references/transcendental-nakamaye-copy4-20260911/source/main-Nulllocus.tex:1638-1712`):

> By `eq:def-K`, `φ_K ∈ PSH(V, γ - (δ_*/2)ω_V)`.  By [Xia, Thm 1.6.2], `φ_K` admits a
> quasi-equisingular approximation consisting of potentials with analytic singularities of type
> `(2^{-j}, 𝓘(2^jφ_K))` [...] `γ + ddᶜφ_{K,q} ≥ (δ_*/2 - η'_q) ω_V` [...] Now choose a dyadic
> integer `ℓ ≥ m` so large that `η'_ℓ ≤ δ₀` [...] `K_ℓ := γ + ddᶜφ_{K,ℓ} ≥ δ₀ ω_V`.  The potential
> `φ_{K,ℓ}` has analytic singularities of type `(ℓ⁻¹, 𝔅)`, where `𝔅 := 𝓘(ℓφ_K) ⊆ 𝒪_V`.

`secondLevel_of_kahlerCurrent` is this paragraph, together with the passage from the ideal
`𝔅 ⊆ 𝒪_V` to the ambient data that `Copy4TraceInputReduction.PositiveCurrentInput` asks for
(`Pending.AnalyticTypeRestriction`: the lift `𝔅̂` of `𝔅`, a weight `ψ_𝔅` of type `(1, 𝔅̂)`).
Its inputs are exactly what the rest of `sec:positive-current` produces at a fixed level
`m = 2^a`:

* `hK`: the Kähler current `K = γ + ddᶜφ_K ≥ 2δ₀ ω_V` (`eq:def-K`, `δ₀ = δ_*/4`), i.e. `φ_K` is a
  potential on `V` for `(θ - 2δ₀ ω)|_V`;
* `hideal`: the inclusion `𝔅 · 𝔅̄_m^{(C-1)r} ⊆ 𝔅̄_{Cmr}` of ideals on `V`, for every dyadic
  `r = 2^i` (`lem:ideal-comparison`, `ℓ = mr`, `M = Cℓ`, `p = (C-1)ℓ/m`), with
  `𝔅̄_q = Res_V 𝓘(qψ)`.

Its conclusion is the clause of `PositiveCurrentInput` following the choice of `C`, `m`, `δ₀`
(with `ψ = V_θ` there): for every `N` there are `r ≥ N`, a coherent `𝔅̂` with `V ⊄ Z(𝔅̂)`, its
weight `ψ_𝔅`, `RestrictLe V (𝔅̂ · 𝓘(mψ)^{(C-1)r}) 𝓘(Cmrψ)`, and the level potential
`φ_{K,ℓ}` (`K_ℓ ≥ δ₀ ω_V`) with the singularities of `(mr)⁻¹ ψ_𝔅` on `V`.  It uses no property of
the trace `u` and no `lem:domination`: those enter only through `hK` and `hideal`.

Programme `TN.2.3.PCI`, piece C7 (route-independent part) of
`scratch/tn23-envelopes-qea-plan-0117.md` §5.3.  Sorry-free.
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace SGPT.Foundations.Analysis.Pending.PositiveCurrentSecondLevel

noncomputable section

open FirstPass FirstPass.PositiveClasses FirstPass.HolomorphicIdealSheaves
  FirstPass.GlobalAnalyticSingularities FirstPass.BlowupSequences
  FirstPass.QuasiEquisingularApproximation FirstPass.NumericalRestrictedVolumeScaffold
  SubmanifoldChartedSpace SubmanifoldIdealRestriction AnalyticTypeRestriction
  SubmanifoldMassCalculus IdealWeightPowers RestrictedIdealWeight Copy4FixedDataFromInputs

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

/-- `(θ - 2δ ω)|_V + ε ω_V`-psh with `ε ≤ δ` implies `(θ - δ ω)|_V`-psh: the Kähler
correction `(δ - ε) ω_V` is semipositive, and pullback is linear up to geometric equality. -/
theorem isThetaPshPotential_pullback_sub_of_le {k : ℕ} {W : Set X} (hk : k ≤ n)
    (hW : ∀ x ∈ W, RegularAtDim (n := n) W x k) (omega : KahlerBackground n X)
    (θ : ClosedRealOneOneForm n X) {δ ε : ℝ} (hε : ε ≤ δ) :
    letI := chartedSpace hk hW
    haveI := isComplexManifold_chartedSpace hk hW
    ∀ v : W → EReal,
      IsThetaPshPotential
          (ClosedRealOneOneForm.pullback (contMDiff_val hk hW) (θ - (2 * δ) • omega.form) +
            ε • (SubmanifoldKahlerRestriction.kahlerBackground hk hW omega).form).val v →
        IsThetaPshPotential
          (ClosedRealOneOneForm.pullback (contMDiff_val hk hW) (θ - δ • omega.form)).val v := by
  let := chartedSpace hk hW
  have := isComplexManifold_chartedSpace hk hW
  intro v hv
  set ωV := SubmanifoldKahlerRestriction.kahlerBackground hk hW omega
  set A := ClosedRealOneOneForm.pullback (contMDiff_val hk hW) (θ - (2 * δ) • omega.form)
  have hsemi : ((δ - ε) • ωV.form).val.IsSemipositive :=
    KahlerDomination.isSemipositive_smul ωV.isSemipositive (by linarith)
  have h1 := LocalPotentials.isThetaPshPotential_add_of_semipositive hv hsemi
  have hform : A + ε • ωV.form + (δ - ε) • ωV.form = A + δ • ωV.form := by module
  rw [hform] at h1
  have hθ : θ - δ • omega.form = (θ - (2 * δ) • omega.form) + δ • omega.form := by module
  rw [hθ]
  exact (isThetaPshPotential_pullback_add_smul_iff hk hW _ omega.form δ v).mpr h1

/-- **Copy-4: the second level `K_ℓ` and the encoding of `PositiveCurrentInput`.**  Let `V` be a
closed connected submanifold of positive dimension of the compact Kähler `X`, `ψ` a `θ`-psh
function (Copy-4: `V_θ`), `m = 2^a`, `C ≥ 1`, `δ₀ > 0`, and `φ_K` a potential on `V` of
`(θ - 2δ₀ω)|_V` (the Kähler current `K ≥ 2δ₀ ω_V`).  If `𝓘_V(mrφ_K) · (Res_V 𝓘(mψ))^{(C-1)r} ⊆
Res_V 𝓘(Cmrψ)` on `V` for every dyadic `r`, then for every `N` there are `r ≥ N`, a coherent ideal
`𝔅` on `X` with `V ⊄ Z(𝔅)` and a weight `ψ_𝔅` of type `(1, 𝔅)` such that
`Res_V (𝔅 · 𝓘(mψ)^{(C-1)r}) ⊆ Res_V 𝓘(Cmrψ)`, and a potential `φ` on `V` of `(θ - δ₀ω)|_V` with
the singularities of `(mr)⁻¹ ψ_𝔅` on `V`: `φ = φ_{K,ℓ}`, `ℓ = mr`, the `ℓ`-th Demailly approximant
of `φ_K`, and `𝔅` the lift of `𝓘_V(ℓφ_K)`. -/
theorem secondLevel_of_kahlerCurrent [CompactSpace X] (hn : 0 < n)
    (omega : KahlerBackground n X) (θ : ClosedRealOneOneForm n X)
    (V : ClosedIrreducibleAnalyticSubvariety n X)
    (hV : IsClosedConnectedSubmanifold n V.carrier V.dim) (hdim : 0 < V.dim)
    {ψ : X → EReal} (hψ : ThetaPlurisubharmonic θ.val ψ)
    {C m a : ℕ} (hm : m = 2 ^ a) {δ₀ : ℝ} (hδ₀ : 0 < δ₀) {φK : V.carrier → EReal}
    (hK :
      letI := chartedSpace (le_of_isClosedConnectedSubmanifold hV) hV.2.2
      haveI := isComplexManifold_chartedSpace (le_of_isClosedConnectedSubmanifold hV) hV.2.2
      IsThetaPshPotential
        (ClosedRealOneOneForm.pullback
          (contMDiff_val (le_of_isClosedConnectedSubmanifold hV) hV.2.2)
          (θ - (2 * δ₀) • omega.form)).val φK)
    (hideal :
      letI := chartedSpace (le_of_isClosedConnectedSubmanifold hV) hV.2.2
      haveI := isComplexManifold_chartedSpace (le_of_isClosedConnectedSubmanifold hV) hV.2.2
      ∀ i : ℕ,
        ((multiplierIdeal (n := V.dim) ((m * 2 ^ i : ℕ) : ℝ) φK).mul
            (idealPow (restrictIdeal (k := V.dim) (W := V.carrier)
              (multiplierIdeal (n := n) (m : ℝ) ψ)) ((C - 1) * 2 ^ i))).Le
          (restrictIdeal (k := V.dim) (W := V.carrier)
            (multiplierIdeal (n := n) ((C * m * 2 ^ i : ℕ) : ℝ) ψ))) :
    ∀ N : ℕ, ∃ r : ℕ, N ≤ r ∧ 1 ≤ r ∧
      ∃ (idealB : GermIdeal n X) (ψB : X → EReal) (φ : V.carrier → EReal),
        idealB.IsCoherent ∧ ¬ V.carrier ⊆ idealB.zeroLocus ∧
        HasAnalyticSingularitiesOfType (n := n) ψB 1 idealB ∧
        RestrictLe V.carrier
          (idealB.mul (idealPow (multiplierIdeal (n := n) (m : ℝ) ψ) ((C - 1) * r)))
          (multiplierIdeal (n := n) ((C * m * r : ℕ) : ℝ) ψ) ∧
        IsLevelPotential omega θ V hV δ₀ φ ∧
        SameSingularityTypeOn φ
          (fun v => ((1 / ((m * r : ℕ) : ℝ) : ℝ) : EReal) * ψB v.1) univ := by
  intro N
  set hk := le_of_isClosedConnectedSubmanifold hV
  let := chartedSpace hk hV.2.2
  have := isComplexManifold_chartedSpace hk hV.2.2
  have hcpt : CompactSpace V.carrier := compactSpace_of_isClosed hV.1
  set ωV := SubmanifoldKahlerRestriction.kahlerBackground hk hV.2.2 omega
  -- Demailly's approximation of `φ_K` on `V`, with its global type
  obtain ⟨ε, Φ, hqea, htype⟩ :=
    QuasiEquisingularApproximationDemailly.exists_quasiEquisingularApproximation_ofType hdim ωV
      (ClosedRealOneOneForm.pullback (contMDiff_val hk hV.2.2) (θ - (2 * δ₀) • omega.form)) hK
  -- the level: `2^i ≥ N` and `ε_{a+i} ≤ δ₀`
  obtain ⟨J, hJ⟩ := eventually_atTop.mp (hqea.error_tendsto.eventually (ge_mem_nhds hδ₀))
  set i := max J N with hi
  set r : ℕ := 2 ^ i with hr
  set j := a + i with hj
  have hℓ : 2 ^ j = m * r := by rw [hj, hm, hr, pow_add]
  have hr1 : 1 ≤ r := Nat.one_le_two_pow
  have hNr : N ≤ r := (le_max_right J N).trans (Nat.lt_two_pow_self).le
  have hεj : ε j ≤ δ₀ := hJ j (by omega)
  -- the ideal `𝔅 = 𝓘_V(ℓφ_K)` and the type of `φ_{K,ℓ}`
  set 𝔟 : GermIdeal V.dim V.carrier := multiplierIdeal (n := V.dim) ((m * r : ℕ) : ℝ) φK
  have htypej : HasAnalyticSingularitiesOfType (n := V.dim) (Φ j) (((m * r : ℕ) : ℚ)⁻¹) 𝔟 := by
    have := htype j
    rwa [hℓ] at this
  have h𝔟 : 𝔟.IsCoherent := htypej.2.1
  have hψcoh : (multiplierIdeal (n := n) (m : ℝ) ψ).IsCoherent :=
    MultiplierIdealBergmanNadelManifold.isCoherent_multiplierIdeal_of_pos hn hψ
      (by rw [hm]; positivity)
  obtain ⟨ψB, hψB, -⟩ := exists_liftIdeal_weight hk hV.2.2 hV.1 𝔟 h𝔟
  refine ⟨r, hNr, hr1, liftIdeal n V.carrier 𝔟, ψB, Φ j,
    isCoherent_liftIdeal hk hV.2.2 hV.1 𝔟 h𝔟, ?_, hψB, ?_, ?_, ?_⟩
  · -- `V ⊄ Z(𝔅̂)`: `φ_{K,ℓ}` is finite somewhere, and its pole set is `Z(𝔅)`
    obtain ⟨y, hyV⟩ := hV.2.1.nonempty
    obtain ⟨p, -, hp⟩ := (hqea.term j).2 ⟨y, hyV⟩ univ isOpen_univ (mem_univ _)
    have hpZ : p ∉ 𝔟.zeroLocus := by
      rw [← StepFourNoComponentContainsW.poleSet_eq_zeroLocus htypej]
      exact hp
    intro hsub
    exact hpZ ((mem_zeroLocus_liftIdeal_iff hk hV.2.2 𝔟 h𝔟 p).mp (hsub p.2))
  · -- the ideal clause, from the inclusion on `V`
    have h := hideal i
    exact restrictLe_liftIdeal_mul_idealPow hk hV.2.2 hV.1 𝔟 h𝔟 hψcoh _ _ h
  · -- `K_ℓ ≥ δ₀ ω_V`
    exact isThetaPshPotential_pullback_sub_of_le hk hV.2.2 omega θ hεj (Φ j) (hqea.term j)
  · -- `φ_{K,ℓ} ~ ℓ⁻¹ ψ_𝔅` on `V`
    exact sameSingularityTypeOn_inv_mul_liftWeight hk hV.2.2 hV.1 𝔟 h𝔟 ψB (Φ j) (m * r)
      (by rw [← hℓ]; positivity) hψB htypej

end

end SGPT.Foundations.Analysis.Pending.PositiveCurrentSecondLevel
