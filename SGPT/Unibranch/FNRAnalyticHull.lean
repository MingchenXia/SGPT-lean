import SGPT.Unibranch.FNRHullBasics
import SGPT.GAGA.CoreCTheoremB
import SGPT.Foundations.Analysis.Pending.CartanIrreducible
import SGPT.Foundations.Analysis.Pending.CartanIrreducibleReduction
import SGPT.Foundations.Analysis.FirstPass.ComplexAnalyticSubvarieties
import SGPT.Foundations.Analysis.Pending.AnalyticSubsetOpens

/-!
# Hulls of compact subsets of analytic sets

Source: Fornæss–Narasimhan, *The Levi problem on complex spaces with singularities*,
Math. Ann. 248 (1980), Lemma 5.2 and Theorem 5.3.1: for a closed complex subvariety `X` of a
polydisc and a compact `K ⊆ X`, "`K̂` is the polynomially convex hull of `K` (`=` hull in `X`)".
The point is that `K̂ ⊆ X`. Ingredient of `thm:FN` (2) ⇒ (1) (`appendix_unibranch.tex`).

`X` is only assumed to be cut out locally by finitely many holomorphic functions
(`HasLocalEquationsOn X Ω`; `hasLocalEquationsOn_of_isComplexAnalyticSubset` translates the
workspace's `IsComplexAnalyticSubset` on an open subset `Ω ⊆ ℂⁿ`, e.g. the carrier of a local
embedding of a complex space). Global equations near a compact convex box `Q ⊆ Ω`
(`exists_equations_near_box`) come from Cartan's coherence theorem (SGPT.Foundations.Analysis
`LocalCartan`, the vanishing ideal of a locally cut out set is finitely generated near each point)
and Cartan's Theorem A on boxes (`SGPT.GAGA.Core.TheoremB.theoremA_box`): finitely many sections
of the vanishing ideal over a neighbourhood `V` of `Q` generate it at every point of `V`; their
common zero set in `V` is `X ∩ V`, because the germ `1` lies in the vanishing ideal at points off
the (relatively closed) set `X`. Then Oka–Weil (`polyHull_subset_zeroLocus`) gives `K̂ ⊆ X`
whenever `K ⊆ X` and `K̂ ⊆ Q` (`polyHull_subset_of_localEquations_box`), in particular for every
compact `K ⊆ X ∩ Δ` when `X` is analytic in a polydisc `Δ`
(`polyHull_subset_of_localEquations_polydisc`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric
open scoped Topology
open SGPT.Foundations.Analysis.FirstPass

namespace SGPT.Unibranch.FNR

open E2Nov16FNPolynomialPolyhedron E2Nov16FNHolomorphicHullMaximum
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.OkaRelationSheaf
  SGPT.Foundations.Analysis.Pending.OkaIdealOperations
open SGPT.GAGA.Core SGPT.GAGA.Core.Box SGPT.GAGA.Core.TheoremB

variable {n : ℕ}

/-- `X` is cut out near every point of `Ω` by finitely many holomorphic functions. -/
def HasLocalEquationsOn (X Ω : Set (ComplexModel n)) : Prop :=
  ∀ x ∈ Ω, ∃ W : Set (ComplexModel n), IsOpen W ∧ x ∈ W ∧
    ∃ (N : ℕ) (g : Fin N → ComplexModel n → ℂ), (∀ i, DifferentiableOn ℂ (g i) W) ∧
      ∀ y ∈ W, (y ∈ X ↔ ∀ i, g i y = 0)

theorem HasLocalEquationsOn.mono {X Ω Ω' : Set (ComplexModel n)} (h : HasLocalEquationsOn X Ω)
    (hΩ : Ω' ⊆ Ω) : HasLocalEquationsOn X Ω' :=
  fun x hx => h x (hΩ hx)

/-- The workspace notion of an analytic subset of an open set `Ω ⊆ ℂⁿ` (an analytic subset of
the complex manifold `Ω`, as in `LocalEmbedding.analytic`) has local equations. -/
theorem hasLocalEquationsOn_of_isComplexAnalyticSubset {Ω : TopologicalSpace.Opens (ComplexModel n)}
    {C : Set Ω} (hC : IsComplexAnalyticSubset (n := n) C) :
    HasLocalEquationsOn (Subtype.val '' C) Ω := by
  intro x hx
  obtain ⟨p⟩ := hC ⟨x, hx⟩
  have happly : ∀ y : Ω, (complexChartAt (n := n) (⟨x, hx⟩ : Ω)).val y = y.val := fun y => rfl
  have hsource : ∀ y : Ω, y ∈ (complexChartAt (n := n) (⟨x, hx⟩ : Ω)).val.source := by
    intro y
    show y ∈ ((chartAt (ComplexModel n) x).subtypeRestr ⟨(⟨x, hx⟩ : Ω)⟩).source
    rw [OpenPartialHomeomorph.subtypeRestr_source]
    simp [chartAt_self_eq]
  refine ⟨p.coordinateNeighborhood ∩ Ω, p.isOpen_coordinateNeighborhood.inter Ω.isOpen,
    ⟨by simpa [happly] using p.center_mem_coordinateNeighborhood, hx⟩, p.generatorCount,
    p.generator, fun i => (p.generator_holomorphic i).mono inter_subset_left, ?_⟩
  rintro y ⟨hyV, hyΩ⟩
  have hz := p.zeroLocus (y := (⟨y, hyΩ⟩ : Ω)) (hsource _) (by rw [happly]; exact hyV)
  rw [happly] at hz
  rw [← hz]
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact hc
  · intro h
    exact ⟨_, h, rfl⟩

/-- The rank-one germ module of holomorphic germs vanishing on `X`. -/
def vanishingModule (X : Set (ComplexModel n)) : GermModule (ComplexModel n) Unit where
  mem y a := vanishingIdealF X y (a ())

/-- **Cartan's coherence theorem** in the germ-module language of `SGPT.GAGA.Core`. -/
theorem vanishingModule_isCoherentOn {X Ω : Set (ComplexModel n)}
    (hX : HasLocalEquationsOn X Ω) : (vanishingModule X).IsCoherentOn Ω := by
  intro x hx
  obtain ⟨W, hW, hxW, N, g, hg, hXW⟩ := hX x hx
  have hLC : CartanLocalReduction.LocalCartan n :=
    CartanIrreducibleReduction.localCartan_of_irreducibleLocalCartan
      (CartanIrreducible.irreducibleLocalCartan n)
  obtain ⟨U, hU, hxU, μ, hμ, s, hs, hgen⟩ := hLC W hW N g hg x hxW
  refine ⟨U ∩ W, hU.inter hW, ⟨hxU, hxW⟩, μ, hμ, fun k _ => s k,
    ⟨fun k _ => (hs k).mono inter_subset_left, ?_⟩⟩
  intro y hy a
  have hev : ∀ᶠ z in 𝓝 y, (z ∈ X ↔ z ∈ {w | ∀ i, g i w = 0}) := by
    filter_upwards [hW.mem_nhds hy.2] with z hz using hXW z hz
  have hXZ : vanishingIdealF X y (a ()) ↔ vanishingIdealF {w | ∀ i, g i w = 0} y (a ()) := by
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by filter_upwards [h2, hev] with z hz hze hzZ using hz (hze.mpr hzZ)⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by filter_upwards [h2, hev] with z hz hze hzX using hz (hze.mp hzX)⟩
  show vanishingIdealF X y (a ()) ↔ _
  rw [hXZ, hgen y hy.1]
  have hsy : ∀ k, HolAt (s k) y := fun k => holAt_of_differentiableOn hU (hs k) hy.1
  constructor
  · rintro ⟨-, c, hc, hca⟩
    exact ⟨c, hc, fun j => by cases j; exact hca⟩
  · rintro ⟨c, hc, hca⟩
    exact ⟨(HolAt.fintype_sum fun k => (hc k).mul (hsy k)).congr (hca ()).symm, c, hc, hca ()⟩

/-- **Global equations near a box**: if `X` has local equations on an open `Ω` containing the
compact convex box `Q = ∏ C_l`, then on an open `V` with `Q ⊆ V ⊆ Ω`, `X ∩ V` is the common zero
set of finitely many functions holomorphic on `V`. -/
theorem exists_equations_near_box {X Ω : Set (ComplexModel n)} {C : Fin n → Set ℂ}
    (hC : IsBox C) (hΩ : IsOpen Ω) (hCΩ : boxSet C ⊆ Ω) (hX : HasLocalEquationsOn X Ω) :
    ∃ V : Set (ComplexModel n), IsOpen V ∧ boxSet C ⊆ V ∧ V ⊆ Ω ∧
      ∃ (μ : Type) (_ : Fintype μ) (f : μ → ComplexModel n → ℂ),
        (∀ k, DifferentiableOn ℂ (f k) V) ∧ ∀ z ∈ V, (z ∈ X ↔ ∀ k, f k z = 0) := by
  obtain ⟨U, hU, hCU, μ, hμ, σ, hσ⟩ := theoremA_box hC hΩ hCΩ (vanishingModule_isCoherentOn hX)
  refine ⟨U ∩ Ω, hU.inter hΩ, subset_inter hCU hCΩ, inter_subset_right, μ, hμ,
    fun k => σ k (), fun k => (hσ.1 k ()).mono inter_subset_left, ?_⟩
  intro z hz
  constructor
  · intro hzX k
    exact (hσ.gen_mem hz.1 k).2.self_of_nhds hzX
  · intro h0
    by_contra hzX
    obtain ⟨W, hW, hzW, N, g, hg, hXW⟩ := hX z hz.2
    obtain ⟨i, hi⟩ : ∃ i, g i z ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hzX ((hXW z hzW).mpr hcon)
    have hcont : ContinuousAt (g i) z := (hg i).continuousOn.continuousAt (hW.mem_nhds hzW)
    have hev : ∀ᶠ x in 𝓝 z, x ∉ X := by
      filter_upwards [hcont.eventually_ne hi, hW.mem_nhds hzW] with x hx1 hx2 hxX
      exact hx1 ((hXW x hx2).mp hxX i)
    have h1 : (vanishingModule X).mem z (fun _ _ => (1 : ℂ)) :=
      ⟨holAt_const 1 z, by filter_upwards [hev] with x hx hxX using absurd hxX hx⟩
    obtain ⟨c, -, hca⟩ := (hσ.2 z hz.1 _).mp h1
    have := (hca ()).self_of_nhds
    simp only [h0, mul_zero, Finset.sum_const_zero] at this
    exact one_ne_zero this

/-- **The hull of a compact subset of an analytic set stays in it** (FN80's "`K̂` (`=` hull in
`X`)"): `X` with local equations on an open `Ω` containing a compact convex box `Q`, `K ⊆ X`
compact with `K̂ ⊆ Q`. Then `K̂ ⊆ X`. -/
theorem polyHull_subset_of_localEquations_box {X Ω K : Set (ComplexModel n)} {C : Fin n → Set ℂ}
    (hC : IsBox C) (hΩ : IsOpen Ω) (hCΩ : boxSet C ⊆ Ω) (hX : HasLocalEquationsOn X Ω)
    (hK : IsCompact K) (hKX : K ⊆ X) (hKC : polyHull K ⊆ boxSet C) : polyHull K ⊆ X := by
  obtain ⟨V, hV, hCV, -, μ, hμ, f, hf, hXV⟩ := exists_equations_near_box hC hΩ hCΩ hX
  have h := polyHull_subset_zeroLocus hK hV (hKC.trans hCV) hf fun x hx =>
    (hXV x (hCV (hKC (subset_polyHull K hx)))).mp (hKX hx)
  intro z hz
  obtain ⟨hzV, h0⟩ := h hz
  exact (hXV z hzV).mpr h0

/-- **Polydisc form**: if `X` has local equations on the open polydisc
`Δ = {z : |zᵢ - aᵢ| < rᵢ}` and `K ⊆ X ∩ Δ` is compact, then `K̂ ⊆ X ∩ Δ`. -/
theorem polyHull_subset_of_localEquations_polydisc {X K : Set (ComplexModel n)}
    {a : ComplexModel n} {r : Fin n → ℝ}
    (hX : HasLocalEquationsOn X {z | ∀ i, ‖z i - a i‖ < r i}) (hK : IsCompact K)
    (hKX : K ⊆ X) (hKΔ : ∀ x ∈ K, ∀ i, ‖x i - a i‖ < r i) :
    polyHull K ⊆ X ∩ {z | ∀ i, ‖z i - a i‖ < r i} := by
  rcases K.eq_empty_or_nonempty with hKe | hne
  · rw [hKe, polyHull_empty]; exact empty_subset _
  have hmax (i : Fin n) : ∃ s : ℝ, s < r i ∧ ∀ x ∈ K, ‖x i - a i‖ ≤ s := by
    have hc : ContinuousOn (fun x : ComplexModel n => ‖x i - a i‖) K :=
      (((EuclideanSpace.proj i : ComplexModel n →L[ℂ] ℂ).continuous.sub
        continuous_const).norm).continuousOn
    obtain ⟨x₀, hx₀, hx₀max⟩ := hK.exists_isMaxOn hne hc
    exact ⟨_, hKΔ x₀ hx₀ i, fun x hx => hx₀max hx⟩
  choose s hs hsK using hmax
  let C : Fin n → Set ℂ := fun i => closedBall (a i) (s i)
  have hC : IsBox C := ⟨fun i => isCompact_closedBall _ _, fun i => convex_closedBall _ _⟩
  have hboxEq : boxSet C = {z : ComplexModel n | ∀ i, ‖z i - a i‖ ≤ s i} := by
    ext z
    simp [C, mem_boxSet, dist_eq_norm]
  have hCΔ : boxSet C ⊆ {z : ComplexModel n | ∀ i, ‖z i - a i‖ < r i} := by
    rw [hboxEq]
    exact fun z hz i => (hz i).trans_lt (hs i)
  have hKC : polyHull K ⊆ boxSet C := by
    rw [hboxEq]
    exact polyHull_subset_closedPolydisc fun x hx i => hsK i x hx
  exact subset_inter
    (polyHull_subset_of_localEquations_box hC (isOpen_polydisc a r) hCΔ hX hK hKX hKC)
    (hKC.trans hCΔ)

end SGPT.Unibranch.FNR
