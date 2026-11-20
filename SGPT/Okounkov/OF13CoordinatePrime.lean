import SGPT.Okounkov.OF13AnalyticSnc
import SGPT.Foundations.Analysis.Pending.HironakaActualInheritedNextBlockGraph
import SGPT.Foundations.Analysis.Pending.HironakaHolomorphicJetChartInvariance
import SGPT.Foundations.Analysis.FirstPass.LocalHolomorphicInverse
import SGPT.Foundations.Analysis.Pending.HolomorphicZeroSetThin

/-!
# Analytic coordinates generate prime coordinate ideals

Source: chapter *The theory of Okounkov bodies*, `rmk:Abhyankar` (existence part of
[CFKLRS17, Thm 2.9]); continuation of `SGPT.Okounkov.OF13AnalyticSnc`.

If germs `t₁, …, tₙ ∈ 𝒪_{ℂⁿ,0}` generate the maximal ideal, then for every set `s` of indices the
ideal `(t_s)` is prime (`isPrime_span_image_of_span_eq_maximalIdeal`): by the holomorphic inverse
function theorem (`SGPT.Foundations.Analysis.FirstPass.exists_localHolomorphicEquivAt`) the map
`t = (t₁, …, tₙ)` is a local biholomorphism at `0` (its differential is invertible, by the dual
vectors of `OF13.dualVectors_of_span_eq`), so composition with `t` is an automorphism of
`𝒪_{ℂⁿ,0}` (`localGermAlgEquiv`) sending the coordinate `wⱼ` to `tⱼ`; and the coordinate ideal
`(w_s)` is the kernel of the restriction to the coordinate subspace `{w_s = 0}` (TN's
`mem_actualAnalyticCoordinateBlockIdeal_iff_projection_zero`), a prime since `𝒪_{ℂⁿ,0}` is a
domain.

Consequently the primality hypothesis of `OF13.exists_admissibleFlag_lexEquivalent_of_analytic`
is automatic: **`exists_admissibleFlag_lexEquivalent_of_analyticCoordinates`** derives the
conclusion of [CFKLRS17, Thm 2.9] on a smooth model `V` from algebraic elements `zⱼ ∈ 𝒪_{V,x}`
whose analytic germs generate the maximal ideal of `𝒪^{an}` (holomorphic coordinates at the
centre) and in which the `u_k` are, analytically, units times Laurent monomials.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.Okounkov.OF13

open CategoryTheory AlgebraicGeometry Filter IsLocalRing SGPT.Foundations.Schemes
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open HironakaHolomorphicJetMonomialSpan HolomorphicGermCoordinateDerivation
open HironakaActualAnalyticBlockGraphTranslation HironakaActualInheritedNextBlockGraph
open HironakaHolomorphicJetChartInvariance
open SGPT.Okounkov SGPT.NAPotential.FSPos SGPT.Okounkov.OF5 SGPT.Okounkov.OF6 SGPT.Okounkov.ValCurr
open scoped Topology Manifold

section Prime

variable {n : ℕ}

/-- The coordinate ideal `(w_s)` of `𝒪_{ℂⁿ,0}` is prime. -/
theorem isPrime_actualAnalyticCoordinateBlockIdeal (s : Set (Fin n)) :
    (actualAnalyticCoordinateBlockIdeal s).IsPrime := by
  have h : actualAnalyticCoordinateBlockIdeal s =
      RingHom.ker (actualBlockProjectionGermHom sᶜ).toRingHom := by
    ext F
    rw [mem_actualAnalyticCoordinateBlockIdeal_iff_projection_zero, RingHom.mem_ker]
    rfl
  rw [h]
  exact RingHom.ker_isPrime _

/-- **Coordinate ideals of a holomorphic coordinate system are prime.** If `t₁, …, tₙ` generate
the maximal ideal of `𝒪_{ℂⁿ,0}`, then every ideal `(t_s)` is prime. -/
theorem isPrime_span_image_of_span_eq_maximalIdeal (t : Fin n → HolGerm (ComplexModel n))
    (ht : Ideal.span (Set.range t) = maximalIdeal (HolGerm (ComplexModel n))) (s : Set (Fin n)) :
    (Ideal.span (t '' s)).IsPrime := by
  classical
  obtain ⟨v, hv⟩ := dualVectors_of_span_eq t ht
  have ht0 : ∀ j, HolGerm.eval (t j) = 0 := fun j => by
    rw [← HolGerm.mem_maximalIdeal_iff, ← ht]
    exact Ideal.subset_span ⟨j, rfl⟩
  choose T hT hTt using fun j => HolGerm.exists_eq_mk (t j)
  let F : ComplexModel n → ComplexModel n := fun z => WithLp.toLp 2 (fun j => T j z)
  have hFj : ∀ z j, F z j = T j z := fun _ _ => rfl
  obtain ⟨N, hNsub, hN, h0N⟩ := eventually_nhds_iff.mp (eventually_all.mpr hT)
  have hFd : ∀ z ∈ N, DifferentiableAt ℂ F z := fun z hz =>
    differentiableAt_euclidean.mpr fun j => hNsub z hz j
  have hT0 : ∀ j, T j 0 = 0 := fun j => by
    have h := ht0 j
    rw [hTt j, HolGerm.eval_mk] at h
    exact h
  have hF0 : F 0 = 0 := by
    ext j
    rw [hFj, hT0]
    rfl
  -- the differential of `F` at `0`
  have hcomp : ∀ j (w : ComplexModel n), fderiv ℂ F 0 w j = germDeriv w (t j) := by
    intro j w
    have h1 := ((PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin n => ℂ) j).hasFDerivAt (x := F 0)).comp
      (0 : ComplexModel n) (hFd 0 h0N).hasFDerivAt
    rw [hTt j, germDeriv_mk]
    have h2 : fderiv ℂ (T j) 0 =
        (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin n => ℂ) j).comp (fderiv ℂ F 0) := by
      have hTF : T j = (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin n => ℂ) j) ∘ F := rfl
      rw [hTF]
      exact h1.fderiv
    rw [h2]
    rfl
  have hsurj : Function.Surjective (fderiv ℂ F 0) := by
    intro y
    refine ⟨∑ i, y i • v i, ?_⟩
    ext j
    rw [hcomp]
    have hlin : ∀ (c : ℂ) (w : ComplexModel n) (h : HolGerm (ComplexModel n)),
        germDeriv (c • w) h = c * germDeriv w h := fun c w h => by
      simp only [germDeriv, PiLp.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
    have hadd : ∀ (w w' : ComplexModel n) (h : HolGerm (ComplexModel n)),
        germDeriv (w + w') h = germDeriv w h + germDeriv w' h := fun w w' h => by
      simp only [germDeriv, PiLp.add_apply, add_mul, Finset.sum_add_distrib]
    have hsum : ∀ (S : Finset (Fin n)) (h : HolGerm (ComplexModel n)),
        germDeriv (∑ i ∈ S, y i • v i) h = ∑ i ∈ S, y i * germDeriv (v i) h := by
      intro S h
      induction S using Finset.induction_on with
      | empty => simp [germDeriv]
      | insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hadd, hlin, ih]
    rw [hsum]
    simp only [hv, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    simp
  have hinj : Function.Injective (fderiv ℂ F 0) := by
    have hfin : Module.finrank ℂ (ComplexModel n) = Module.finrank ℂ (ComplexModel n) := rfl
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin
      (f := (fderiv ℂ F 0 : ComplexModel n →ₗ[ℂ] ComplexModel n))).mpr hsurj
  have hFdOn : DifferentiableOn ℂ F N := fun z hz => (hFd z hz).differentiableWithinAt
  obtain ⟨Φ, -, hΦF, -⟩ := exists_localHolomorphicEquivAt hN h0N hFdOn hinj
  have hΦ0 : Φ.toFun 0 = 0 := by rw [hΦF, hF0]
  let ψ := localGermAlgEquiv Φ hΦ0
  have hψ : ∀ j, ψ (coordinateGerm j) = t j := fun j => by
    unfold coordinateGerm
    rw [localGermAlgEquiv_mk, hTt j]
    apply HolGerm.mk_eq_mk_iff.mpr
    refine Eventually.of_forall fun z => ?_
    change Φ.toFun z j = T j z
    rw [hΦF]
  have hmap : Ideal.span (t '' s) =
      (actualAnalyticCoordinateBlockIdeal s).map ψ.toRingEquiv.toRingHom := by
    rw [actualAnalyticCoordinateBlockIdeal, Ideal.map_span, Set.image_image]
    congr 1
    exact Set.image_congr fun j _ => (hψ j).symm
  rw [hmap]
  have := isPrime_actualAnalyticCoordinateBlockIdeal s
  exact Ideal.map_isPrime_of_equiv ψ.toRingEquiv

end Prime

section Scheme

variable {V : Scheme.{0}} {f : V ⟶ Spec (.of ℂ)} {n : ℕ}
  [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f]

local instance of13cpTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance of13cpCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance of13cpManifold : IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n

variable {p : SchemeComplexPoint f}

/-- **Algebraic local equations of holomorphic coordinates are strict normal crossings
coordinates.** If the analytic germs of `z₁, …, zₙ ∈ 𝒪_{V,x}` generate the maximal ideal of
`𝒪_{ℂⁿ,0}`, then `z` are strict normal crossings coordinates at `x` (lane OF11's
`IsSNCCoordinates`). -/
theorem isSNCCoordinates_of_analyticCoordinates [IsIntegral V]
    (z : Fin n → V.presheaf.stalk (schemeComplexPointImage f p))
    (hm : Ideal.span (Set.range (stalkToModel f n p ∘ z)) =
      maximalIdeal (HolGerm (ComplexModel n))) :
    OF11.IsSNCCoordinates f (schemeComplexPointImage f p) z :=
  isSNCCoordinates_of_analytic z hm fun _ => isPrime_span_image_of_span_eq_maximalIdeal _ hm _

/-- **[CFKLRS17, Thm 2.9] from analytic log resolution data with algebraic coordinates.** Let `X`
be integral, `ν : ℂ(X)^× → ℤⁿ_lex` a valuation, and `V` an integral scheme, smooth of relative
dimension `n` over `ℂ` (separated, quasi-compact), with `e : ℂ(X) ≃ ℂ(V)`, on which `ν` is
centred at the image `x` of a complex point `p`. Suppose that `z₁, …, zₙ ∈ 𝒪_{V,x}` are
holomorphic coordinates at `p` (their germs generate the maximal ideal of `𝒪_{ℂⁿ,0}`), and that
`u₁, …, uₙ ∈ ℂ(X)` with `ν(u_k) = e_k` have meromorphic germs at `p` equal to analytic units times
Laurent monomials `∏ⱼ zⱼ^{a_{kj}}`, the germ of `u_k` or of `u_k⁻¹` being holomorphic. Then `ν` is
equivalent to the valuation `ν_{Y•} ∘ e` of an admissible flag `Y•` on `V` with point `x`. -/
theorem exists_admissibleFlag_lexEquivalent_of_analyticCoordinates {X : Scheme.{0}}
    [IsIntegral X] [IsIntegral V] (e : X.functionField ≃+* V.functionField)
    (ν : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ))))
    (hcent : AlgebraicValuation.IsValuationCenter (ν.comap e.symm.toRingHom)
      (schemeComplexPointImage f p))
    (z : Fin n → V.presheaf.stalk (schemeComplexPointImage f p))
    (hm : Ideal.span (Set.range (stalkToModel f n p ∘ z)) =
      maximalIdeal (HolGerm (ComplexModel n)))
    (u : Fin n → X.functionField) (η : Fin n → (HolGerm (ComplexModel n))ˣ)
    (a : Fin n → Fin n → ℤ)
    (hu : ∀ k, modelFractionGerm f n p (e (u k)) =
      algebraMap _ (FractionRing (HolGerm (ComplexModel n))) (η k : HolGerm (ComplexModel n)) *
        ∏ j, (algebraMap _ (FractionRing (HolGerm (ComplexModel n)))
          (stalkToModel f n p (z j))) ^ (a k j))
    (hreg : ∀ k, (∃ h : HolGerm (ComplexModel n), modelFractionGerm f n p (e (u k)) =
        algebraMap _ (FractionRing (HolGerm (ComplexModel n))) h) ∨
      ∃ h : HolGerm (ComplexModel n), modelFractionGerm f n p (e (u k))⁻¹ =
        algebraMap _ (FractionRing (HolGerm (ComplexModel n))) h)
    (hνu : ∀ k, ν (u k) = basisValue k) :
    ∃ (Y : Fin (n + 1) → Set V) (hY : IsAdmissibleFlag f n Y),
      hY.point = schemeComplexPointImage f p ∧
      ValuationsLexEquivalent ((admissibleFlagValuation hY).comap e.toRingHom) ν :=
  exists_admissibleFlag_lexEquivalent_of_analytic e ν hcent z hm
    (fun _ => isPrime_span_image_of_span_eq_maximalIdeal _ hm _) u η a hu hreg hνu

end Scheme

end SGPT.Okounkov.OF13
