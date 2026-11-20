import SGPT.Okounkov.OF13LogResolution
import SGPT.Okounkov.OF4AbhyankarCentre
import SGPT.NAPotential.GAGAMult2Faithful

/-!
# [CFKLRS17, Thm 2.9] on a smooth projective analytic log resolution

Source: chapter *The theory of Okounkov bodies*, Section *Flags and valuations*, `rmk:Abhyankar`:
*if a valuation has value group identified with `ℤⁿ_lex` and maximal rational rank `n`, then
[CFKLRS17, Theorem 2.9] shows that it is equivalent to, but not necessarily equal to, a valuation
induced by an admissible flag on a modification of `X`.*

`IsAnalyticLogResolutionAt g e u p`: at the complex point `p` of a smooth complex scheme `V` (a
model of `ℂ(X)` through `e : ℂ(X) ≃ ℂ(V)`), the rational functions `u₁, …, uₙ ∈ ℂ(X)` are, on
`V(ℂ)`, analytically Laurent monomials in normal crossings coordinates: there are holomorphic
coordinates `ℓ₁, …, ℓₙ` at `p` (their germs generate the maximal ideal of `𝒪^{an}_{V,p}`), a set
`M` of indices such that `ℓⱼ` (`j ∈ M`) generates at `p` the ideal of an analytic hypersurface
`Hⱼ ⊆ V(ℂ)` (the members of the normal crossings divisor through `p`), and the meromorphic germ of
each `u_k` is an analytic unit times `∏_{j ∈ M} ℓⱼ^{a_{kj}}`, the germ of `u_k` or of `u_k⁻¹`
being holomorphic. A resolution of singularities (principalization of the ideals of the numerators,
denominators and indeterminacies of the `u_k`) produces such `V(ℂ)` at every point.

**Main theorem** (`exists_admissibleFlag_lexEquivalent_of_isAnalyticLogResolution`): let `X` be
integral, `ν : ℂ(X)^× → ℤⁿ_lex` a surjective valuation (value group `ℤⁿ_lex`), and `u_k` with
`ν(u_k) = e_k`. If `V` is an integral smooth projective complex scheme of dimension `n` with
`e : ℂ(X) ≃ ℂ(V)` which is an analytic log resolution of `u₁, …, uₙ` at every point, then `ν` is
equivalent to `ν_{Y•} ∘ e` for an admissible flag `Y•` on `V` (with point the centre of `ν` on `V`).
The centre exists (`V` is proper), is a closed point, hence the image of a complex point
(`exists_schemeComplexPoint_eq_of_isClosed`, Hilbert's Nullstellensatz).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.Okounkov.OF13

open CategoryTheory AlgebraicGeometry Filter Set IsLocalRing SGPT.Foundations.Schemes
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Okounkov SGPT.NAPotential.FSPos SGPT.Okounkov.OF5 SGPT.Okounkov.OF6 SGPT.Okounkov.ValCurr
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open scoped Topology Manifold

/-- Closed points of a scheme locally of finite type over `ℂ` are complex points. -/
theorem exists_schemeComplexPoint_eq_of_isClosed {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ))
    [LocallyOfFiniteType f] {c : X} (hc : IsClosed ({c} : Set X)) :
    ∃ p : SchemeComplexPoint f, schemeComplexPointImage f p = c := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hcU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ c) isOpen_univ
  let x : U := ⟨c, hcU⟩
  let P := hU.primeIdealOf x
  have hPc : hU.fromSpec P = c := hU.fromSpec_primeIdealOf x
  have hclosed : IsClosed ({P} : Set (PrimeSpectrum Γ(X, U))) := by
    have h : ({P} : Set (PrimeSpectrum Γ(X, U))) = hU.fromSpec ⁻¹' {c} := by
      ext Q
      constructor
      · rintro rfl
        exact hPc
      · intro hQ
        exact hU.fromSpec.isOpenEmbedding.injective ((hQ : hU.fromSpec Q = c).trans hPc.symm)
    rw [h]
    exact hc.preimage hU.fromSpec.continuous
  have hmax := (PrimeSpectrum.isClosed_singleton_iff_isMaximal P).mp hclosed
  obtain ⟨p, hp⟩ :=
    SGPT.NAPotential.Berkovich.exists_schemeComplexPoint_fromSpec f hU P.asIdeal hmax
  exact ⟨p, hp.trans hPc⟩

section Scheme

variable {V : Scheme.{0}} (g : V ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n g] [IsSeparated g] [QuasiCompact g]

local instance of13pmTopology : TopologicalSpace (SchemeComplexPoint g) :=
  schemeAnalyticPointTopology g
local instance of13pmCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint g) :=
  schemeAnalyticTNChartedSpace g n
local instance of13pmManifold : IsComplexManifold n (SchemeComplexPoint g) :=
  schemeAnalyticTN_isComplexManifold g n

/-- **Analytic log resolution at a point.** At the complex point `p` of `V`, the functions
`u₁, …, uₙ ∈ ℂ(X)` (read on `V` through `e`) are analytic units times Laurent monomials in the
local equations of the members through `p` of a normal crossings divisor of `V(ℂ)`, and `u_k` or
`u_k⁻¹` is holomorphic at `p`. -/
def IsAnalyticLogResolutionAt [IsIntegral V] {X : Scheme.{0}} [IsIntegral X]
    (e : X.functionField ≃+* V.functionField) (u : Fin n → X.functionField)
    (p : SchemeComplexPoint g) : Prop :=
  ∃ (ℓ : Fin n → SchemeComplexPoint g → ℂ) (hℓ : ∀ j, HolomorphicAt n (ℓ j) p),
    Ideal.span (Set.range fun j => NativeHolGerm.mk (ℓ j) (hℓ j)) =
      maximalIdeal (NativeHolGerm n (SchemeComplexPoint g) p) ∧
    ∃ (M : Finset (Fin n)) (H : Fin n → Set (SchemeComplexPoint g)),
      (∀ j ∈ M, IsComplexAnalyticSubset (n := n) (H j)) ∧
      (∀ j ∈ M, (vanishingIdeal (n := n) (H j)).mem p (ℓ j)) ∧
      (∀ j ∈ M, ∀ (h : SchemeComplexPoint g → ℂ) (hh : HolomorphicAt n h p),
        (vanishingIdeal (n := n) (H j)).mem p h →
          NativeHolGerm.mk h hh ∈ Ideal.span {NativeHolGerm.mk (ℓ j) (hℓ j)}) ∧
      ∃ (η : Fin n → (NativeHolGerm n (SchemeComplexPoint g) p)ˣ) (a : Fin n → Fin n → ℤ),
        (∀ k, ∀ j ∉ M, a k j = 0) ∧
        (∀ k, schemeNativeFunctionFieldGerm g n p (e (u k)) =
          algebraMap _ (FractionRing (NativeHolGerm n (SchemeComplexPoint g) p))
              (η k : NativeHolGerm n (SchemeComplexPoint g) p) *
            ∏ j, (algebraMap _ (FractionRing (NativeHolGerm n (SchemeComplexPoint g) p))
              (NativeHolGerm.mk (ℓ j) (hℓ j))) ^ (a k j)) ∧
        ∀ k, (∃ h : NativeHolGerm n (SchemeComplexPoint g) p,
            schemeNativeFunctionFieldGerm g n p (e (u k)) =
              algebraMap _ (FractionRing (NativeHolGerm n (SchemeComplexPoint g) p)) h) ∨
          ∃ h : NativeHolGerm n (SchemeComplexPoint g) p,
            schemeNativeFunctionFieldGerm g n p (e (u k))⁻¹ =
              algebraMap _ (FractionRing (NativeHolGerm n (SchemeComplexPoint g) p)) h

variable {g n}

/-- **[CFKLRS17, Thm 2.9] on a smooth projective analytic log resolution.** Let `X` be integral,
`ν : ℂ(X)^× → ℤⁿ_lex` a surjective valuation, `u₁, …, uₙ ∈ ℂ(X)` with `ν(u_k) = e_k`, and `V` an
integral smooth projective complex scheme of dimension `n` with `e : ℂ(X) ≃ ℂ(V)` which is an
analytic log resolution of the `u_k` at every complex point. Then `ν` is equivalent to the valuation
`ν_{Y•} ∘ e` of an admissible flag `Y•` on `V`, whose point is the centre of `ν` on `V`. -/
theorem exists_admissibleFlag_lexEquivalent_of_isAnalyticLogResolution {X : Scheme.{0}}
    [IsIntegral X] [IsIntegral V] (EV : ClosedProjectiveEmbedding g)
    (e : X.functionField ≃+* V.functionField)
    (ν : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ)))) (hν : Function.Surjective ν)
    (u : Fin n → X.functionField) (hνu : ∀ k, ν (u k) = basisValue k)
    (hres : ∀ p : SchemeComplexPoint g, IsAnalyticLogResolutionAt g n e u p) :
    letI := EV.isProper
    ∃ (Y : Fin (n + 1) → Set V) (hY : IsAdmissibleFlag g n Y),
      hY.point = AlgebraicValuation.valuationCenter g (ν.comap e.symm.toRingHom) ∧
      ValuationsLexEquivalent ((admissibleFlagValuation hY).comap e.toRingHom) ν := by
  let := EV.isProper
  let ν' := ν.comap e.symm.toRingHom
  have hν' : Function.Surjective ν' := fun w => by
    obtain ⟨q, hq⟩ := hν w
    exact ⟨e q, by change ν (e.symm (e q)) = w; rw [e.symm_apply_apply, hq]⟩
  have hclosed := OF4.isClosed_valuationCenter g n ν' hν'
  obtain ⟨p, hp⟩ := exists_schemeComplexPoint_eq_of_isClosed g hclosed
  have hcent : AlgebraicValuation.IsValuationCenter ν' (schemeComplexPointImage g p) := by
    rw [hp]
    exact AlgebraicValuation.isValuationCenter_valuationCenter g ν'
  obtain ⟨ℓ, hℓ, hcoord, M, H, hH, hℓmem, hℓgen, η, a, haM, hu, hreg⟩ := hres p
  have hcoord' : Ideal.span (Set.range fun j =>
      NativeHolGerm.chartEquiv p (NativeHolGerm.mk (ℓ j) (hℓ j))) =
      maximalIdeal (HolGerm (ComplexModel n)) := by
    have h := congrArg (Ideal.map (NativeHolGerm.chartEquiv (n := n) p)) hcoord
    rw [Ideal.map_span, IsLocalRing.map_ringEquiv_maximalIdeal, ← Set.range_comp] at h
    exact h
  obtain ⟨Y, hY, hpt, hlex⟩ := exists_admissibleFlag_lexEquivalent_of_analyticLogResolution EV e
    ν p hcent ℓ hℓ hcoord' M H hH hℓmem hℓgen u η a haM hu hreg hνu
  exact ⟨Y, hY, hpt.trans hp, hlex⟩

end Scheme

end SGPT.Okounkov.OF13
