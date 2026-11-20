import SGPT.Foundations.Analysis.Pending.SmoothComponentReduction
import SGPT.Foundations.Analysis.Pending.PrincipalizationData
import SGPT.Foundations.Analysis.Pending.LocalGluingData
import SGPT.Foundations.Analysis.Pending.AnalyticGluing
import SGPT.Foundations.Analysis.Pending.LocusProperties
import SGPT.Foundations.Analysis.Pending.AnalyticIrreducibleComponents

set_option autoImplicit false

/-!
# Vanishing on components of the non-Kähler locus

Source: Copy-4, `thm:main` (first assertion) and `sec:gluing`
(`transcendental-nakamaye-copy4-20260911`); blueprint `ana:component-vanishing`.

Let `X` be a nonempty connected compact Kähler manifold of positive complex
dimension and `α ∈ H^{1,1}(X, ℝ)` pseudoeffective.  If `V` is a positive-dimensional
irreducible component of `E_nK(α)`, then `⟨α^{dim V}⟩_{X|V} = 0`.

Pseudoeffectivity is `ClassPseudoeffectiveViaPotentials` (a closed positive current
in the class, presented by a global theta-psh potential).  The restricted volume is
taken with respect to an arbitrary Kähler form `omega` on `X`.

The hypothesis `0 < n` is essential in this encoding: in dimension zero every
punctured neighbourhood filter is trivial, Lelong numbers take the value `⊤`, and
`E_nK` would be the whole (point) manifold while no subvariety has positive
dimension.

The proof is the manuscript's composition, with no local `sorry`: its open
obligations are those of the imported chain statements.  If `α` is not big, `V = X`
(`AnalyticIrreducibleComponents`) and `⟨α^n⟩_{X|X} = 0` (`LocusProperties`).  If `α`
is big and `V ⊄ E_nn(α)` with positive restricted volume, `SmoothComponentReduction`
replaces `(X, α, V)` by a smooth triple; the component is proper since `E_nK` of a
big class is, so `0 < dim V < n`; `PrincipalizationData`, `LocalGluingData` and
`AnalyticGluing` produce `y ∈ W` outside `E_nK(π^* α)`, while the transformation
rule puts `W ⊆ π⁻¹ V` inside it.
-/

open Set

universe u

namespace SGPT.Foundations.Analysis.Pending.ComponentVanishing

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
  FirstPass.NumericalRestrictedVolume FirstPass.BlowupSequences
  SmoothComponentReduction PrincipalizationData LocalGluingData AnalyticGluing
  LocusProperties AnalyticIrreducibleComponents

noncomputable section

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-- **Vanishing on components of the non-Kähler locus**
(Copy-4, `thm:main`, first assertion). -/
theorem numericalRestrictedVolume_eq_zero_of_isIrreducibleComponent
    [Nonempty X] [CompactSpace X] [ConnectedSpace X] (hn : 0 < n)
    (omega : KahlerBackground n X) (alpha : RealBottChern n X)
    (hpsef : ClassPseudoeffectiveViaPotentials alpha)
    (V : ClosedIrreducibleAnalyticSubvariety n X) (hdim_pos : 0 < V.dim)
    (hcomponent : IsIrreducibleComponent V (nonKahlerLocus alpha)) :
    numericalRestrictedVolume omega alpha V = 0 := by
  obtain ⟨θ, rfl⟩ : ∃ θ, RealBottChern.ofRepresentative θ = alpha := Quotient.exists_rep alpha
  by_cases hbig : IsBigClass (RealBottChern.ofRepresentative θ)
  swap
  · have hEuniv := nonKahlerLocus_eq_univ_of_not_isBigClass hbig
    obtain ⟨Z, hZ, -⟩ := exists_subvariety_univ (n := n) (M := X)
    have hVZ : Z.carrier = V.carrier :=
      hcomponent.2 Z (by rw [hZ]; exact subset_univ _) (by rw [hZ, hEuniv])
    exact (numericalRestrictedVolume_eq_zero_iff_not_isBigClass hn omega _ hpsef V
      (hVZ ▸ hZ)).mpr hbig
  by_cases hnn : V.carrier ⊆ nonNefLocus omega (RealBottChern.ofRepresentative θ)
  · exact numericalRestrictedVolume_eq_zero_of_subset_nonNefLocus _ _ _ hnn
  by_contra hne
  have hpos := pos_iff_ne_zero.mpr hne
  obtain ⟨Xt, _, _, _, μ, hμ, -, _, _, hXtK, hbigT, Vt, -, hVtsmooth, hVtdim, hVtcomp,
    hVtRV⟩ := exists_modification_smooth_component omega θ hbig V hdim_pos hcomponent hnn
  obtain ⟨omegaT⟩ := hXtK
  obtain ⟨hnnT, hRVT⟩ := hVtRV omegaT
  have hposT := hRVT ▸ hpos
  have hdim_lt : Vt.dim < n := by
    refine lt_of_le_of_ne Vt.dim_le fun h => ?_
    have huniv : Vt.carrier = univ :=
      eq_univ_of_isClosedConnectedSubmanifold_self (h ▸ hVtsmooth)
    exact nonKahlerLocus_ne_univ hn ⟨omegaT⟩ _ hbigT
      (eq_univ_of_univ_subset (huniv ▸ hVtcomp.1))
  obtain ⟨Y, _, _, _, π, hπ, _, _, hYK, hW, y, hy, U, hU, hWU, φG, φU, hdata⟩ :=
    exists_principalizationGluingData omegaT _ hbigT Vt hVtsmooth (hVtdim ▸ hdim_pos)
      hdim_lt hVtcomp hnnT hposT
  obtain ⟨U₁, U₂, hU₁, hU₂, hyU₁, -, hU₁₂, -, hglue⟩ :=
    exists_collars_gluingHypotheses_of_principalizationGluingConclusions omegaT _ hbigT Vt
      hVtsmooth (hVtdim ▸ hdim_pos) hdim_lt hVtcomp hnnT hposT hYK π hπ hW y hy U hU hWU
      φG φU hdata
  apply (exists_kahlerCurrent_isSmoothNear_of_gluingHypotheses hYK _ U₁ U₂ hU₁ hU₂ hU₁₂ y
    hyU₁ φG φU hglue).2
  have hrule := nonKahlerLocus_pullback ⟨omegaT⟩ _ hbigT π hπ.isBlowupSequence
  have hsub : strictTransform n π Vt.carrier ⊆ π ⁻¹' Vt.carrier :=
    closure_minimal sdiff_subset (Vt.isClosed_carrier.preimage hπ.contMDiff.continuous)
  exact hrule ▸ Or.inl (hVtcomp.1 (hsub hy))

end

end SGPT.Foundations.Analysis.Pending.ComponentVanishing
