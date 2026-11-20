import SGPT.TestCurve.TCLinGraph

/-!
# Uniqueness of the linearization

The weight spaces of a `𝔾_m`-linearization of `𝓛` (`SectionLinearization`) are
forced: on an integral projective `X`, the weight-`λ` subspace of `H⁰(𝓧, 𝓛^m)` is exactly
`weightSpace T m λ`, the space of sections restricting to some `t^{-λ} q^* s`
(`SectionLinearization.weight_eq`). Hence a linearization of `𝓛` compatible with the
identification over `𝔾_m` is unique when it exists (`SectionLinearization.weight_eq'`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.TestCurve.TCLin

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes SGPT.LineBundle Opposite
open SGPT.TestCurve.TestConfig SGPT.TestCurve.TestConfig.LaurentSecRing SGPT.TestCurve.TCEnc
open SGPT.TestCurve.FGRel

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} {L : X.Modules} {a : LineBundleAtlas L}
  {T : TestConfiguration f a}

/-- A section extending `t^{-λ} q^* 0` vanishes (`𝓧` integral). -/
theorem eq_zero_of_extends_zero [IsIntegral T.space] [Nonempty X] {lam : ℤ} {m : ℕ}
    {σ : SectionSpace T.structureMap T.line m} (h : T.Extends lam m 0 σ) : σ = 0 := by
  apply T.eq_of_epsCoeff_eq
  intro j
  rw [h j, (TestConfiguration'.extends_zero T lam m) j]

namespace SectionLinearization

/-- **The weight spaces of a linearization are forced**: the weight-`λ` part of `H⁰(𝓧, 𝓛^m)` is
the space of sections restricting to some `t^{-λ} q^* s`. -/
theorem weight_eq [IsIntegral X] (E : ClosedProjectiveEmbedding f) (P : SectionLinearization T)
    (m : ℕ) (lam : ℤ) : P.weight m lam = weightSpace T m lam := by
  classical
  refine le_antisymm (P.compat m lam) ?_
  rintro σ ⟨s, hs⟩
  have : IsIntegral T.space := T.isIntegral_space_of_embedding E
  have hmem : σ ∈ ⨆ μ, P.weight m μ := by
    rw [(P.isInternal m).submodule_iSup_eq_top]
    trivial
  obtain ⟨c, hc, hsum⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).mp hmem
  choose y hy using fun μ => P.compat m μ (hc μ)
  have h1 : (σ, mono (-lam) m s) ∈ graph T m := mem_graph_of_extends hs
  have h2 : (σ, ∑ μ ∈ c.support, (mono (-μ) m (y μ) : LaurentSecRing f a)) ∈ graph T m := by
    have e : (σ, ∑ μ ∈ c.support, (mono (-μ) m (y μ) : LaurentSecRing f a)) =
        ∑ μ ∈ c.support, (c μ, (mono (-μ) m (y μ) : LaurentSecRing f a)) := by
      refine Prod.ext ?_ ?_
      · rw [Prod.fst_sum, ← hsum, Finsupp.sum]
      · rw [Prod.snd_sum]
    rw [e]
    exact Submodule.sum_mem _ fun μ _ => mem_graph_of_extends (hy μ)
  have heq := graph_unique h1 h2
  -- the components of weight `μ ≠ λ` vanish
  have hc0 : ∀ μ, μ ≠ lam → c μ = 0 := by
    intro μ hne
    by_cases hμ : μ ∈ c.support
    · have hco := congrArg (coeffAt (-μ) m) heq
      rw [coeffAt_mono, dif_neg (fun h => hne (neg_inj.mp h.1).symm), map_sum,
        Finset.sum_eq_single μ] at hco
      · rw [coeffAt_mono_same] at hco
        have hyμ := hy μ
        rw [← hco] at hyμ
        exact eq_zero_of_extends_zero hyμ
      · intro μ' _ hμ'
        rw [coeffAt_mono, dif_neg (fun h => hμ' (neg_inj.mp h.1))]
      · intro h
        exact absurd hμ h
    · exact Finsupp.notMem_support_iff.mp hμ
  have hσ : σ = c lam := by
    rw [← hsum, Finsupp.sum]
    by_cases hl : lam ∈ c.support
    · rw [Finset.sum_eq_single lam (fun μ _ hμ => hc0 μ hμ) (fun h => absurd hl h)]
    · rw [Finset.sum_eq_zero (fun μ hμ => hc0 μ (fun h => hl (h ▸ hμ))),
        Finsupp.notMem_support_iff.mp hl]
  rw [hσ]
  exact hc lam

/-- **Uniqueness of the linearization**: two linearizations of `𝓛` compatible with the
identification over `𝔾_m` have the same weight spaces. -/
theorem weight_eq' [IsIntegral X] (E : ClosedProjectiveEmbedding f) (P P' : SectionLinearization T)
    (m : ℕ) (lam : ℤ) : P.weight m lam = P'.weight m lam := by
  rw [P.weight_eq E, P'.weight_eq E]

end SectionLinearization

end SGPT.TestCurve.TCLin
