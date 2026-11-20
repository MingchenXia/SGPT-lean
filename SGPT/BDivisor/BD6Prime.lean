import SGPT.BDivisor.BD6Divisor
import SGPT.BDivisor.DFAlgNeronSeveri
import SGPT.Projective.BDivNov16PrimeSpan
import SGPT.Okounkov.DivisorMetricAddition

/-!
# Chow equations of a prime divisor give local factorizations

Source: `rmk:bdiv:L749` (GAGA for divisors on the algebraized models).

Let `P` be a prime divisor of `V(ℂ)` (`SGPT.PSH.GeometricPrimeCarrier`), `V` smooth projective with
its projective embedding `ι = projectivePoint`.  Chow's theorem (`SGPT.GAGA.ChowBl.chow_image`)
gives homogeneous `F_k` generating the ideal of the cone over `ι(P)`; Theorem A
(`vanishingIdeal_mem_iff_isInSpanAt_genFun`) says that the `F_k(x/xᵢ)` generate the ideal sheaf
`𝓘_P` of `P`.  As `𝓘_P = (h)` is invertible, `F_k(x/xᵢ) = h · u_k` and `h = ∑ b_l F_{κ l}(x/xᵢ)`
forces `∑ b_l u_{κ l} = 1`: the `u_k` have no common zero
(`exists_localFactorization_prime`).  These are the data of `BD6Morphism`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.BDivisor.BD6

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set Filter
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves SGPT.Foundations.Analysis.Pending
open SGPT.Okounkov SGPT.GAGA.H0S SGPT.GAGA.ChowBl SGPT.NAPotential.FSPos SGPT.Projective
open SGPT.Projective.ComplexProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

variable {V : Scheme.{0}} (g : V ⟶ Spec (.of ℂ)) (EV : ClosedProjectiveEmbedding g) (m : ℕ)
  [SmoothOfRelativeDimension (m + 1) g] [IsSeparated g] [QuasiCompact g]

local instance bd6PrimeTopology : TopologicalSpace (SchemeComplexPoint g) :=
  schemeAnalyticPointTopology g
local instance bd6PrimeCharts : ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint g) :=
  schemeAnalyticTNChartedSpace g (m + 1)
local instance bd6PrimeManifold : IsComplexManifold (m + 1) (SchemeComplexPoint g) :=
  schemeAnalyticTN_isComplexManifold g (m + 1)

/-- The restriction `F(x/xᵢ)` of Chow's theorem is the polynomial in the homogeneous coordinates. -/
theorem genFun_eq_eval (i : Fin (EV.ambientDimension + 1)) {p : SchemeComplexPoint g}
    (hp : schemeComplexPointImage g p ∈ coordOpen EV i)
    (Q : MvPolynomial (Fin (EV.ambientDimension + 1)) ℂ) :
    genFun (projectivePoint g EV (m + 1)) i Q p = MvPolynomial.eval (homCoords g EV (m + 1) i p) Q := by
  change MvPolynomial.eval (fun j => (WithLp.toLp 2 (affineLift i (affineChart i
    (projectivePoint g EV (m + 1) p))) : SGPT.GAGA.PN.ConeSpace _) j) Q = _
  rw [affineChart_projectivePoint g EV (m + 1) i hp, ← homCoords_eq_affineLift g EV (m + 1) i hp]

/-- **Local factorizations of the Chow equations of a prime divisor.** -/
theorem exists_localFactorization_prime (P : SGPT.PSH.GeometricPrimeCarrier (m + 1) (SchemeComplexPoint g))
    {r : ℕ} (F : Fin (r + 1) → MvPolynomial (Fin (EV.ambientDimension + 1)) ℂ)
    (hgen : (coneIdeal (projectivePoint g EV (m + 1) '' P.val)).GeneratedOn
      (SGPT.GAGA.PN.puncture (SGPT.GAGA.PN.ConeSpace EV.ambientDimension))
      (fun k => SGPT.GAGA.PN.polyTuple (F k)))
    (z : SchemeComplexPoint g) :
    ∃ i, ∃ D : LocalFactorization g EV (m + 1) F i, z ∈ D.Nb ∧
      (∀ y ∈ D.Nb, HolomorphicAt (m + 1) D.h y) ∧
      ∀ y ∈ D.Nb, ∀ f, (SGPT.Siu.primeEffectiveDivisor P).ideal.mem y f ↔
        IsInSpanAt (n := m + 1) (· = D.h) y f := by
  classical
  have : CompactSpace (SchemeComplexPoint g) := EV.analyticCompact
  set ι := projectivePoint g EV (m + 1)
  have hι : IsHolomorphicEmbedding (n := m + 1) ι := isHolomorphicEmbedding_projectivePoint g EV (m + 1)
  set i := frameIndex g EV z
  have hzi : schemeComplexPointImage g z ∈ coordOpen EV i := mem_coordOpen_frameIndex g EV z
  have hsrc : ∀ y, schemeComplexPointImage g y ∈ coordOpen EV i → ι y ∈ (affineChart i).source :=
    fun y hy => (projectivePoint_mem_source_iff g EV (m + 1) i y).mpr hy
  have hideal : (SGPT.Siu.primeEffectiveDivisor P).ideal = vanishingIdeal (n := m + 1) P.val :=
    SGPT.PSH.geometricPrimeCarrierEffectiveDivisor_ideal P
  have hA := fun (y : SchemeComplexPoint g) (hy : schemeComplexPointImage g y ∈ coordOpen EV i) f =>
    vanishingIdeal_mem_iff_isInSpanAt_genFun hι hgen (hsrc y hy) f
  obtain ⟨U, hU, hzU, h, hhol, hdense, hgenh⟩ := (SGPT.Siu.primeEffectiveDivisor P).isInvertible z
  have hhz : HolomorphicAt (m + 1) h z :=
    CoherentIdealColon.holomorphicAt_of_mdifferentiableOn hU hhol hzU
  -- the generators lie in the ideal `(h)`
  have hfac : ∀ k, ∃ a : SchemeComplexPoint g → ℂ, HolomorphicAt (m + 1) a z ∧
      genFun ι i (F k) =ᶠ[𝓝 z] fun y => a y * h y := by
    intro k
    have hmem : (SGPT.Siu.primeEffectiveDivisor P).ideal.mem z (genFun ι i (F k)) := by
      rw [hideal]
      exact (hA z hzi _).mpr (InvertibleIdealQuotient.isInSpanAt_self ⟨k, rfl⟩ (holomorphicAt_genFun hι (hsrc z hzi) (F k)))
    exact ((isInSpanAt_eq_iff).mp ((hgenh z hzU _).mp hmem)).2
  choose a ha hfa using hfac
  -- `h` lies in the ideal generated by the `F_k`
  have hhmem : (vanishingIdeal (n := m + 1) P.val).mem z h := by
    rw [← hideal]
    exact (hgenh z hzU h).mpr (InvertibleIdealQuotient.isInSpanAt_self rfl hhz)
  obtain ⟨-, L, s, b, hs, hb, hhs⟩ := (hA z hzi h).mp hhmem
  choose κ hκ using hs
  set S : SchemeComplexPoint g → ℂ := fun y => ∑ l, b l y * a (κ l) y with hSdef
  -- an open neighbourhood on which everything holds
  have hev : ∀ᶠ y in 𝓝 z, y ∈ U ∧ schemeComplexPointImage g y ∈ coordOpen EV i ∧
      (∀ k, genFun ι i (F k) y = a k y * h y) ∧ h y = h y * S y ∧
      (∀ k, MDifferentiableAt 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ℂ) (a k) y) ∧
      (∀ l, MDifferentiableAt 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ℂ) (b l) y) := by
    have e1 : ∀ᶠ y in 𝓝 z, y ∈ U := hU.mem_nhds hzU
    have e2 : ∀ᶠ y in 𝓝 z, schemeComplexPointImage g y ∈ coordOpen EV i :=
      (isOpen_coordOpen_points g EV i).mem_nhds hzi
    have e3 : ∀ᶠ y in 𝓝 z, ∀ k, genFun ι i (F k) y = a k y * h y :=
      Filter.eventually_all.mpr hfa
    have e5 : ∀ᶠ y in 𝓝 z, ∀ k, MDifferentiableAt 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ℂ) (a k) y :=
      Filter.eventually_all.mpr ha
    have e6 : ∀ᶠ y in 𝓝 z, ∀ l, MDifferentiableAt 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ℂ) (b l) y :=
      Filter.eventually_all.mpr hb
    filter_upwards [e1, e2, e3, hhs, e5, e6] with y h1 h2 h3 h4 h5 h6
    refine ⟨h1, h2, h3, ?_, h5, h6⟩
    refine h4.trans ?_
    simp only [hSdef, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← hκ l]
    beta_reduce
    rw [h3]
    ring
  obtain ⟨Nb, hsub, hNbo, hzNb⟩ := mem_nhds_iff.mp hev
  have hdenseNb : ∀ W : Set (SchemeComplexPoint g), IsOpen W → W ⊆ Nb → W.Nonempty →
      ∃ y ∈ W, h y ≠ 0 := fun W hW hWsub hWne => hdense W hW (fun x hx => (hsub (hWsub hx)).1) hWne
  have hS1 : ∀ y ∈ Nb, S y = 1 := by
    intro y hy
    have hcont : ContinuousAt (fun y => 1 - S y) y := by
      refine continuousAt_const.sub ?_
      exact tendsto_finsetSum Finset.univ fun l _ =>
        ((hsub hy).2.2.2.2.2 l).continuousAt.mul ((hsub hy).2.2.2.2.1 (κ l)).continuousAt
    have := eq_zero_of_mul_eq_zero g hNbo (h := h) hy hcont
      (fun y' hy' => by
        have := (hsub hy').2.2.2.1
        linear_combination this) hdenseNb
    exact (sub_eq_zero.mp this).symm
  refine ⟨i, ⟨Nb, h, a, hNbo, fun y hy => (hsub hy).2.1, fun y hy k => ?_, fun y hy k => ?_,
    fun y hy => ?_, hdenseNb⟩, hzNb, fun y hy => ?_, fun y hy f => ?_⟩
  · rw [← genFun_eq_eval g EV m i (hsub hy).2.1, (hsub hy).2.2.1 k, mul_comm]
  · filter_upwards [hNbo.mem_nhds hy] with y' hy'
    exact (hsub hy').2.2.2.2.1 k
  · intro h0
    have h1 := hS1 y hy
    simp only [hSdef] at h1
    have : ∑ l, b l y * a (κ l) y = 0 :=
      Finset.sum_eq_zero fun l _ => by rw [show a (κ l) y = 0 from congrFun h0 (κ l), mul_zero]
    rw [this] at h1
    exact zero_ne_one h1
  · exact CoherentIdealColon.holomorphicAt_of_mdifferentiableOn hU hhol (hsub hy).1
  · exact hgenh y (hsub hy).1 f

end SGPT.BDivisor.BD6
