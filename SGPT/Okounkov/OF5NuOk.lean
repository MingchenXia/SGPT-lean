import SGPT.Okounkov.OF5PrimeDivisorPresentation
import SGPT.Okounkov.OF3NuOk
import SGPT.Okounkov.OF3SectionOrderConstancy

/-!
# `thm:nuOk` for admissible flags

Source: chapter *The theory of Okounkov bodies*, subsection *Recover Lelong numbers from partial
Okounkov bodies*, `thm:nuOk`:

*Let `E` be a prime divisor on `X`. Let `Y•` be an admissible flag with `E = Y₁`. Then
`ν(φ, E) = min_{x ∈ Δ_{Y•}(θ, φ)} x₁`.*

Setting of `sec:PoB`: `X` a connected smooth complex projective variety of dimension `n = m + 1`
(an integral scheme, smooth of relative dimension `n` over `ℂ`, with a closed projective
embedding), `(L, h)` a Hermitian big line bundle, `θ = c₁(L, h₀)`, `φ ∈ PSH(X, θ)` with
`vol θ_φ > 0`.

## Ingredients

* `SGPT.Okounkov.OF5.admissibleFlagValuation`: the valuation `ν_{Y•}` of the admissible flag, as in
  the book (successive orders along local defining equations near `Yₙ`); it is a surjective rank
  `n` valuation of `ℂ(X)`, centred at `Yₙ`, whose first coordinate is `ord_{Y₁}`.
* `SGPT.Okounkov.OF5.exists_primePresentation_ord`: the prime divisor `E = Y₁` of `X` (possibly
  singular) as a prime divisor `Ẽ` over `X(ℂ)` (strict transform of the irreducible component `W`
  of `E(ℂ)` through a smooth point of `E`), whose analytic order of vanishing is `ord_E`.
* **`isFirstCoordinateOrder_admissibleFlag`**: `ν_{Y•}` satisfies the hypothesis
  `SGPT.Okounkov.OF3.IsFirstCoordinateOrder` of the general theorem: on sections of line
  bundles its first coordinate is `ord_{Ẽ}`.
* **`isLeast_firstCoordinate_admissibleFlag`** (`thm:nuOk`): `ν(φ, E) = min_{x ∈ Δ_{Y•}(θ, φ)} x₁`,
  with `ν(φ, E) = ν(π^*φ, Ẽ) = min_{x ∈ W} ν(φ, x)` the generic Lelong number.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.Okounkov.OF5

open Set Filter CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open scoped Topology Manifold ContDiff ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending.FixedGermNormalOrder
open SGPT.Foundations.Analysis.Pending.DemaillyApproximantDivisorialLelong
open SGPT.PSH.CompactPrimeOver SGPT.Okounkov.AlgebraicValuation SGPT.Okounkov.OF3
open SGPT.NAPotential.TowerAlg
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus SquaredLogLelongSourceNormalization

variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ)) {m : ℕ}
  [SmoothOfRelativeDimension (m + 1) f] (E : ClosedProjectiveEmbedding f)
  [IsSeparated f] [QuasiCompact f]

local instance of5NuOkTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance of5NuOkCharts : ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (m + 1)
local instance of5NuOkManifold : IsComplexManifold (m + 1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (m + 1)
local instance of5NuOkMeasurable : MeasurableSpace (SchemeComplexPoint f) := borel _
local instance of5NuOkBorel : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩

/-- `p` **realizes the prime divisor `{z}‾` of `X`**: at some point `y₀ ∈ Ẽ` lying over `{z}‾`,
the analytic order along `Ẽ` of every nonzero germ of `𝒪_{X,π(y₀)}` is its algebraic order
`ord_{z}` (Mathlib's `Scheme.ord`). -/
def RealizesOrder [IsLocallyNoetherian X] (p : PrimePresentation (m + 1) (SchemeComplexPoint f))
    (z : X) : Prop :=
  letI := E.isProper
  ∃ (y₀ : p.model) (_ : y₀ ∈ p.divisor) (Φ₀ : DivisorFlattening (m := m) p.divisor y₀),
    z ⤳ schemeComplexPointImage f (p.projection y₀) ∧
    ∀ g : X.presheaf.stalk (schemeComplexPointImage f (p.projection y₀)), g ≠ 0 →
      stalkOrd p Φ₀ g = ((Scheme.ord (algebraMap _ X.functionField g) z).toNat : ℕ∞)

/-- The frame coefficients of a section in two frames differ by a unit on the overlap. -/
theorem globalSectionToFunctionField_frame {M : X.Modules} {U V : X.Opens} [Nonempty U]
    [Nonempty V] (e : LocalBundleFrame M U) (e' : LocalBundleFrame M V) (x : X) (hx : x ∈ U)
    (hy : x ∈ V) (s : bundleSections M ⊤) :
    letI : Nonempty (U ⊓ V : X.Opens) := ⟨⟨x, hx, hy⟩⟩
    globalSectionToFunctionField e' s =
      X.germToFunctionField (U ⊓ V)
        (localBundleFrameTransition e e' (homOfLE inf_le_left) (homOfLE inf_le_right) :
          X.sheaf.obj.obj (Opposite.op (U ⊓ V))) * globalSectionToFunctionField e s := by
  let : Nonempty (U ⊓ V : X.Opens) := ⟨⟨x, hx, hy⟩⟩
  change X.germToFunctionField V (e'.coefficients (𝟙 _) (M.val.map (homOfLE le_top).op s)) = _ *
    X.germToFunctionField U (e.coefficients (𝟙 _) (M.val.map (homOfLE le_top).op s))
  rw [← germToFunctionField_restrict (homOfLE inf_le_right : U ⊓ V ⟶ V),
    ← germToFunctionField_restrict (homOfLE inf_le_left : U ⊓ V ⟶ U), ← map_mul]
  congr 1
  rw [← frame_global_coefficients_restrict e' (homOfLE inf_le_right) s,
    ← frame_global_coefficients_restrict e (homOfLE inf_le_left) s]
  exact localBundleFrameTransition_coefficients e e' _ _ _

/-- `ord_Z` of the frame coefficient of a section does not depend on the frame, for frames whose
domains contain the generic point `z` of `Z`. -/
theorem ord_globalSectionToFunctionField_frame [IsLocallyNoetherian X] {M : X.Modules}
    (b : LineBundleAtlas M) {U V : X.Opens} [Nonempty U] [Nonempty V] (e : LocalBundleFrame M U)
    (e' : LocalBundleFrame M V) {z : X} (hzU : z ∈ U) (hzV : z ∈ V) {s : bundleSections M ⊤}
    (hs : s ≠ 0) :
    Scheme.ord (globalSectionToFunctionField e' s) z =
      Scheme.ord (globalSectionToFunctionField e s) z := by
  let : Nonempty (U ⊓ V : X.Opens) := ⟨⟨z, hzU, hzV⟩⟩
  rw [globalSectionToFunctionField_frame e e' z hzU hzV s]
  have hunit := (localBundleFrameTransition e e' (homOfLE inf_le_left) (homOfLE inf_le_right)).isUnit
  have hne : X.germToFunctionField (U ⊓ V)
      (localBundleFrameTransition e e' (homOfLE inf_le_left) (homOfLE inf_le_right) :
        X.sheaf.obj.obj (Opposite.op (U ⊓ V))) ≠ 0 := by
    exact (hunit.map (X.germToFunctionField (U ⊓ V)).hom).ne_zero
  have hs' : globalSectionToFunctionField e s ≠ 0 := by
    intro h
    apply hs
    apply globalSectionToFunctionField_injective b e
    rw [h, map_zero]
  rw [Scheme.ord_mul hne hs', Scheme.ord_of_isUnit hunit ⟨hzU, hzV⟩, zero_add]

variable {f} in
/-- **`ν_{Y•}` has first coordinate `ord_{Y₁}` on sections**: the hypothesis
`IsFirstCoordinateOrder` of the theorem holds for `ν_{Y•}` and every presentation `p` of
`Y₁` as a prime divisor over `X(ℂ)` realizing its order of vanishing (source: *"`ν₁ =
ord_{Y₁}(s⁽⁰⁾)` … the same construction applies to a non-zero section `s ∈ H⁰(X, L)` after
choosing a local trivialization of `L` near `Yₙ`"*). -/
theorem isFirstCoordinateOrder_admissibleFlag [IsLocallyNoetherian X]
    {Y : Fin (m + 1 + 1) → Set X} (hY : IsAdmissibleFlag f (m + 1) Y)
    (p : PrimePresentation (m + 1) (SchemeComplexPoint f))
    (hp : RealizesOrder f E p (memberPoint hY 1)) :
    IsFirstCoordinateOrder f E (admissibleFlagValuation hY) p := by
  intro M b s hs
  let := E.isProper
  set ν := admissibleFlagValuation hY with hν
  set z := memberPoint hY 1 with hz
  obtain ⟨y₀, hy₀, Φ₀, hzP, hord⟩ := hp
  -- the centre is `Yₙ`, which lies on `Y₁`
  have hcen : valuationCenter f ν = hY.point := valuationCenter_admissibleFlagValuation hY
  have hzc : z ⤳ hY.point := memberPoint_specializes hY 1
  -- the frame at the centre
  set c := valuationCenter f ν with hcdef
  set e := b.frame (b.centerIndex c) with hedef
  have hcU : c ∈ b.opens (b.centerIndex c) := b.centerIndex_mem c
  have hzc' : z ⤳ c := by rw [hcen]; exact hzc
  have hzU : z ∈ b.opens (b.centerIndex c) := hzc'.mem_open (b.opens _).isOpen hcU
  -- the frame at the point over `Y₁`
  set P₀ := schemeComplexPointImage f (p.projection y₀) with hP₀
  set i₀ := b.centerIndex P₀ with hi₀
  have hP₀U : P₀ ∈ b.opens i₀ := b.centerIndex_mem P₀
  have hzU₀ : z ∈ b.opens i₀ := hzP.mem_open (b.opens _).isOpen hP₀U
  have : Nonempty (b.opens i₀) := ⟨⟨P₀, hP₀U⟩⟩
  have : Nonempty (b.opens (b.centerIndex c)) := ⟨⟨c, hcU⟩⟩
  -- the first coordinate is `ord_{Y₁}` of the coefficient in `e`
  have hq0 : globalSectionToFunctionField e s ≠ 0 := by
    intro h
    apply hs
    apply globalSectionToFunctionField_injective b e
    rw [h, map_zero]
  obtain ⟨w, hw, hw0⟩ := admissibleFlagValuation_firstCoord hY (Nat.succ_pos m) hq0
  have hvec : plainSectionVector ν c b s hs = w := by
    have h1 := plainSectionValue_eq_vector (v := ν) c b s hs
    have h2 : plainSectionValue ν c b s = ν (globalSectionToFunctionField e s) := rfl
    rw [h2, hw] at h1
    exact (toLex.injective (WithTop.coe_injective h1)).symm
  -- the order of the coefficient in the frame at `P₀`
  set r := (b.frame i₀).coefficients (𝟙 _) (M.val.map (homOfLE le_top).op s) with hr
  have hgerm : algebraMap (X.presheaf.stalk P₀) X.functionField
      (X.presheaf.germ (b.opens i₀) P₀ hP₀U r) = globalSectionToFunctionField (b.frame i₀) s :=
    X.algebraMap_germ_eq_germToFunctionField hP₀U r
  have hg0 : X.presheaf.germ (b.opens i₀) P₀ hP₀U r ≠ 0 := by
    intro h
    have h' := hgerm
    rw [h, map_zero] at h'
    apply hs
    apply globalSectionToFunctionField_injective b (b.frame i₀)
    rw [← h', map_zero]
  have hordP := hord _ hg0
  rw [hgerm] at hordP
  have hsame := ord_globalSectionToFunctionField_frame b e (b.frame i₀) hzU hzU₀ hs
  rw [hsame] at hordP
  -- the section order at `y₀`
  obtain ⟨hsec, -⟩ := sectionDivisorOrder_eq_pullbackNormalOrder f E b p hs hy₀ (b.frame i₀) hP₀U Φ₀
  have hst : stalkOrd p Φ₀ (X.presheaf.germ (b.opens i₀) P₀ hP₀U r) =
      pullbackNormalOrder p.modification Φ₀ (frameCoefficient f m E (b.frame i₀) s)
        (frameCoefficient_holomorphicAt (m := m) f E (b.frame i₀) s hP₀U) :=
    stalkOrd_eq p Φ₀ _ _ (schemeOpenRegularFunction_germ f (m + 1) E (b.opens i₀) r _ hP₀U).symm
  -- nonnegativity: the coefficient is regular at `P₀`, a specialization of `z`
  have hnonneg : 0 ≤ Scheme.ord (globalSectionToFunctionField e s) z := by
    rw [← hsame, ← hgerm, ← algebraMap_stalkSpecializes hzP]
    exact ord_nonneg_of_stalk (coheight_memberPoint hY 1 |>.trans (by simp)) _
  have hw0' : w 0 = Scheme.ord (globalSectionToFunctionField e s) z := hw0
  refine ⟨?_, ?_⟩
  · rw [hvec, hw0']
    exact hnonneg
  · rw [hvec, hw0', hsec, ← hst, hordP]

omit [IsIntegral X] in
/-- `ν(φ, Ẽ) = min_{x ∈ W} ν(φ, x)` when `Ẽ` maps onto `W` with the same generic Lelong numbers
(the book's `def:pshfunctions:L1112` and `def:pshfunctions:L1101`, Lelong numbers in the source
normalization `squaredLogLelongNumber`). -/
theorem presentationReader_eq_iInf_of_lelong (p : PrimePresentation (m + 1) (SchemeComplexPoint f))
    (W : Set (SchemeComplexPoint f)) (φ : SchemeComplexPoint f → EReal)
    (h : (⨅ y ∈ p.divisor, lelongNumber (n := m + 1) (fun y => φ (p.projection y)) y) =
      ⨅ x ∈ W, lelongNumber (n := m + 1) φ x) :
    presentationReader φ p = ⨅ x ∈ W, squaredLogLelongNumber (n := m + 1) φ x := by
  simp only [presentationReader, SGPT.PSH.VariableComplexAtlas.sourceGenericLelong,
    SGPT.PSH.VariableComplexAtlas.sourceLelong_ofFixedModel_eq]
  apply (ENNReal.mul_right_inj (a := 2) (by norm_num) (by norm_num)).mp
  rw [← SquaredLogLelongSourceNormalization.iInf_lelongNumber_eq_two_mul_squaredLog
      (Nat.succ_ne_zero m),
    ← SquaredLogLelongSourceNormalization.iInf_lelongNumber_eq_two_mul_squaredLog
      (Nat.succ_ne_zero m)]
  exact h

/-- **Source `thm:nuOk`, admissible flags.** Let `Y•` be an admissible flag of `X` (`def:admfl`)
and `E = Y₁` (a prime divisor of `X`, possibly singular). Regard `E` as a prime divisor over
`X(ℂ)`: the strict transform `Ẽ` (by an embedded resolution `π`) of the irreducible component
`W ⊆ E(ℂ)` through a smooth point of `E`, so that `ν(φ, E) = ν(π^* φ, Ẽ) = min_{x ∈ W} ν(φ, x)`
(`def:pshfunctions:L1112`, `def:pshfunctions:L1101`; `W = E(ℂ)` when `E(ℂ)` is analytically
irreducible, and in any case `min_{x ∈ E(ℂ)} ν(φ, x) ≤ ν(φ, E)`) and the order of vanishing along
`Ẽ` is `ord_E`. Then for every `φ ∈ PSH(X, θ)` with `vol θ_φ > 0`,
`ν(φ, E) = min_{x ∈ Δ_{Y•}(θ, φ)} x₁`, where `Δ_{Y•}(θ, φ)` is the partial Okounkov body
(`def:Okounkov:L687`) of the valuation `ν_{Y•}` of the flag. -/
theorem isLeast_firstCoordinate_admissibleFlag [Nonempty (SchemeComplexPoint f)]
    {Y : Fin (m + 1 + 1) → Set X} (hY : IsAdmissibleFlag f (m + 1) Y)
    {L : X.Modules} (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f (m + 1) E L)
    {φ : SchemeComplexPoint f → EReal} (hφ : IsThetaPshPotential (H.curvature a).val φ)
    (hpos : haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact;
      0 < iVolume (H.curvature a) (LocalPotentials.closedRealOneOne_hasLocalPotentials _) φ hφ) :
    letI := E.isProper
    ∃ (p : PrimePresentation (m + 1) (SchemeComplexPoint f))
      (W : ClosedIrreducibleAnalyticSubvariety (m + 1) (SchemeComplexPoint f)),
      W.carrier ⊆ schemeNativeAlgebraicTrace f (Y 1) ∧ W.dim = m ∧
      p.projection '' p.divisor = W.carrier ∧
      presentationReader φ p = (⨅ x ∈ W.carrier, squaredLogLelongNumber (n := m + 1) φ x) ∧
      (⨅ x ∈ schemeNativeAlgebraicTrace f (Y 1), squaredLogLelongNumber (n := m + 1) φ x) ≤
        presentationReader φ p ∧
      ∃ (hKc : IsCompact (centreOkounkovBody f (admissibleFlagValuation hY) a))
        (hKv : Convex ℝ (centreOkounkovBody f (admissibleFlagValuation hY) a)),
        IsLeast ((fun x : EuclideanSpace ℝ (Fin (m + 1)) => x 0) ''
            ValGen.partialBody f (m + 1) E (admissibleFlagValuation hY)
              (valuationCenter f (admissibleFlagValuation hY)) a
              (SGPT.GAGA.OkoClose.coneOver _ hKc hKv) φ)
          (presentationReader φ p).toReal := by
  let := E.isProper
  have : Smooth f := SmoothOfRelativeDimension.smooth (m + 1) f
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hz1 : Order.coheight (memberPoint hY 1) = 1 := by
    rw [coheight_memberPoint]
    simp
  obtain ⟨p, W, hWsub, hWdim, himage, hreader, y₀, hy₀, Φ₀, hzP, hord⟩ :=
    exists_primePresentation_ord (m := m) E hz1
  have hY1 : closure {memberPoint hY 1} = Y 1 := by
    rw [hY.closure_genericPoint]
    rfl
  have hq : ManifoldQuasiPlurisubharmonic (n := m + 1) φ := hφ.1.quasiPlurisubharmonic
  have hR := presentationReader_eq_iInf_of_lelong f p W.carrier φ (hreader φ hq)
  have hWY : W.carrier ⊆ schemeNativeAlgebraicTrace f (Y 1) := by rw [← hY1]; exact hWsub
  refine ⟨p, W, hWY, hWdim, himage, hR, by rw [hR]; exact biInf_mono hWY, ?_⟩
  have hfirst := isFirstCoordinateOrder_admissibleFlag E hY p ⟨y₀, hy₀, Φ₀, hzP, hord⟩
  exact isLeast_firstCoordinate_partialBody f E p a H (admissibleFlagValuation hY)
    (admissibleFlagValuation_surjective hY) hfirst hφ hpos

end SGPT.Okounkov.OF5
