import SGPT.Projective.OkounkovOriginalBookKahlerHCP
import SGPT.Projective.OkounkovOriginalAnalyticHCPAllDimensions
import SGPT.Projective.OkounkovOriginalBookDeltapert
import SGPT.Projective.OkounkovOriginalPerturbGeometry
import SGPT.Projective.OkounkovOriginalRightScalarAllDimensions
import SGPT.NAPotential.FSPosAlgebraic
import SGPT.Projective.OkounkovOriginalBookPartial
import SGPT.Projective.OkounkovSetBodyGeometry
import SGPT.Okounkov.ValGen2Res
import SGPT.GAGA.OkoCloseBig
import SGPT.GAGA.H0LOkounkov
import SGPT.Okounkov.FlagValuationEndpointCenter
import SGPT.Okounkov.FlagValuationGenericCenters
import SGPT.AlmostSemigroup.BodyExtrema

/-!
# `thm:nuOk` for every valuation whose first coordinate is `ord_E`

Source: chapter *The theory of Okounkov bodies*, Section *Algebraic partial Okounkov bodies*,
`thm:nuOk`: *let `E` be a prime divisor on `X` and `Y•` an admissible flag with `E = Y₁`; then
`ν(φ, E) = min_{x ∈ Δ_{Y•}(θ, φ)} x₁`.*

The proof in the book only uses one property of the flag valuation `ν_{Y•}`: its first
coordinate is the order of vanishing `ord_E` along `E = Y₁` ("By definition,
`min_{x ∈ Δ_k(θ, φ)} x₁ = k⁻¹ ord_E H⁰(X, L^k ⊗ 𝓘(kφ))`"). We formalize the statement for
**every** surjective rank `n` valuation `ν : ℂ(X)^× → ℤⁿ` (the standing valuation of `sec:PoB`)
whose first coordinate is `ord_E`, for a smooth prime divisor `E`, i.e. whose first-coordinate
coarsening coincides with that of the flag valuation `ν_{Y•}` of some smooth flag with `Y₁ = E`
(`ValCurr.prefixValuation`). Every admissible flag `Y•` with smooth first member `Y₁ = E` gives
such a valuation (its first coordinate is `ord_{Y₁}` by definition), as does every smooth flag;
the case `E` singular is not covered.

## Main results

* `surjective_of_generatedGroup_eq_top`: an additive valuation `v` of `ℂ(X)` with values in
  `ℤⁿ_lex` is surjective as soon as the value semigroup `Γ_v(L)` of some line bundle generates
  `ℤⁿ⁺¹`; in particular flag valuations are surjective (`surjective_flagValuation`).
* `plainSectionVector_zero_eq_of_prefixValuation_eq`: two valuations with the same first
  coordinate give the same first coordinate `ν(s)₁` on every section of every line bundle (each
  read at its own centre): the frames at the two centres differ by a unit at the centre of the
  common coarsening.
* `image_coordinate_poly_eq`, `tendsto_sInf_image_coordinate`: hence the first-coordinate
  projections of the (twisted) polytopes `Δ_{k,T}(θ, φ)` coincide, and coordinate minima pass to
  Hausdorff limits.
* `sInf_firstCoordinate_partialBody_eq_of_kahler`, `sInf_firstCoordinate_partialBody_eq`: two
  surjective valuations with the same first coordinate have partial Okounkov bodies with the same
  first-coordinate minimum (Kähler currents; every `φ` with `vol θ_φ > 0`).
* **`isLeast_firstCoordinate_partialBody_of_prefix_eq`** (source `thm:nuOk`): for such `ν` and
  every `φ ∈ PSH(X, θ)` with `vol θ_φ > 0`, `ν(φ, E) = min_{x ∈ Δ_ν(θ, φ)} x₁`, where
  `Δ_ν(θ, φ) = Δ(Γ_ν(θ, φ))` is the partial Okounkov body of `def:Okounkov:L687` in the cone
  over `Δ_ν(L)` and `ν(φ, E)` is the generic Lelong number along `E`.

The proof follows the book: for Kähler currents, `thm:HCP` for `ν` and for `ν_{Y•}`
(`Δ_{k,T}(θ, φ) → Δ_ν(θ, φ)`, `SGPT.Okounkov.OriginalBook.tendsto_twistedMultiplierPolytope_kahler_positiveDimension`),
the equality of the first coordinates of their polytopes and the continuity of coordinate minima in
the Hausdorff metric (`lma:Hausdorffconvcoordbounds`); the general case `vol θ_φ > 0` by perturbing
`L` by an ample line bundle (`prop:Deltapert`, as in the book); finally the smooth-flag case
(`SGPT.GAGA.OkoClose.isLeast_firstCoordinate_partialOkounkovBody`).
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.Okounkov.OF

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set Filter MeasureTheory Metric
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Okounkov SGPT.Okounkov.AlgebraicValuation SGPT.AlmostSemigroup
open SGPT.AlmostSemigroup.Class SGPT.Okounkov.ValGen2 SGPT.NAPotential.FSPos
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open scoped Topology ENNReal Pointwise

/-! ### Surjectivity from generation -/

section Surjective

variable {X : Scheme.{0}} [IsIntegral X] {n : ℕ}

/-- An additive valuation of `ℂ(X)` with values in `ℤⁿ_lex` whose section semigroup `Γ(L)` (at a
point `c`) generates `ℤⁿ⁺¹` is surjective. -/
theorem surjective_of_generatedGroup_eq_top
    (v : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ)))) (c : X)
    {L : X.Modules} (a : LineBundleAtlas L)
    (hG : LatticeSlices.generatedGroup (sectionSemigroup v c a) = ⊤) :
    Function.Surjective v := by
  classical
  have key : ∀ z ∈ LatticeSlices.generatedGroup (sectionSemigroup v c a),
      ∃ q : X.functionField, q ≠ 0 ∧
        v q = ((toLex z.1 : Lex (Fin n → ℤ)) : WithTop (Lex (Fin n → ℤ))) := by
    intro z hz
    change z ∈ AddSubgroup.closure (sectionSemigroup v c a : Set ((Fin n → ℤ) × ℤ)) at hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨k, s, hs, rfl⟩ := hz
      refine ⟨globalSectionToFunctionField ((a.frame (a.centerIndex c)).tensorPower k) s, ?_, ?_⟩
      · intro h0
        apply hs
        apply (sectionValue_eq_top_iff (v := v) c a k s).mp
        change v (globalSectionToFunctionField ((a.frame (a.centerIndex c)).tensorPower k) s) = ⊤
        rw [h0, v.map_zero]
      · exact sectionValue_eq_vector (v := v) c a k s hs
    | zero => exact ⟨1, one_ne_zero, by rw [v.map_one]; rfl⟩
    | add x y _ _ hx hy =>
      obtain ⟨p, hp0, hp⟩ := hx
      obtain ⟨q, hq0, hq⟩ := hy
      refine ⟨p * q, mul_ne_zero hp0 hq0, ?_⟩
      rw [v.map_mul, hp, hq, ← WithTop.coe_add, ← toLex_add, Prod.fst_add]
    | neg x _ hx =>
      obtain ⟨p, hp0, hp⟩ := hx
      refine ⟨p⁻¹, inv_ne_zero hp0, ?_⟩
      have h1 : v p + v p⁻¹ = 0 := by
        rw [← v.map_mul, mul_inv_cancel₀ hp0, v.map_one]
      have hne : v p⁻¹ ≠ ⊤ := by
        rw [Ne, AddValuation.top_iff]
        exact inv_ne_zero hp0
      obtain ⟨y, hy⟩ := WithTop.ne_top_iff_exists.mp hne
      rw [← hy, hp, ← WithTop.coe_add, ← WithTop.coe_zero, WithTop.coe_inj] at h1
      rw [← hy]
      congr 1
      rw [← neg_eq_of_add_eq_zero_right h1]
      rfl
  intro t
  induction t using WithTop.recTopCoe with
  | top => exact ⟨0, v.map_zero⟩
  | coe x =>
    obtain ⟨q, -, hq⟩ := key (ofLex x, 0) (by rw [hG]; trivial)
    exact ⟨q, hq⟩

end Surjective

/-! ### First coordinates of section values -/

section Prefix

variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ)) [IsProper f] {m : ℕ}

/-- The first-coordinate coarsening of a valuation is nonnegative wherever the valuation is. -/
theorem prefixValuation_isNonnegAt {n k : ℕ} (hk : k ≤ n)
    {v : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ)))} {c : X}
    (hc : IsNonnegAt v c) : IsNonnegAt (ValCurr.prefixValuation hk v) c := by
  intro g
  have h := ValCurr.monotone_prefixWithTopHom hk (hc g)
  rw [map_zero] at h
  exact h

include f in
/-- **Two valuations with the same first coordinate read the same first coordinate on every
section**, each at a point where it is nonnegative (e.g. its centre): the two frames of the
line bundle differ by a function which is a unit at the centre of the common first-coordinate
coarsening (which generizes both points). -/
theorem plainSectionVector_zero_eq_of_prefixValuation_eq
    (v w : AddValuation X.functionField (WithTop (Lex (Fin (m + 1) → ℤ))))
    (hvw : ValCurr.prefixValuation (Nat.le_add_left 1 m) v =
      ValCurr.prefixValuation (Nat.le_add_left 1 m) w)
    {c d : X} (hc : IsNonnegAt v c) (hd : IsNonnegAt w d)
    {M : X.Modules} (b : LineBundleAtlas M) (s : bundleSections M ⊤) (hs : s ≠ 0) :
    plainSectionVector v c b s hs 0 = plainSectionVector w d b s hs 0 := by
  set h1 : 1 ≤ m + 1 := Nat.le_add_left 1 m with hh1
  have hpc : IsNonnegAt (ValCurr.prefixValuation h1 v) c := prefixValuation_isNonnegAt h1 hc
  have hpd : IsNonnegAt (ValCurr.prefixValuation h1 v) d := by
    rw [hvw]
    exact prefixValuation_isNonnegAt h1 hd
  have hz : IsNonnegAt (ValCurr.prefixValuation h1 v)
      (valuationCenter f (ValCurr.prefixValuation h1 v)) :=
    (isValuationCenter_valuationCenter f _).1
  have hzc := valuationCenter_specializes_of_stalk_nonneg f (ValCurr.prefixValuation h1 v) c hpc
  have hzd := valuationCenter_specializes_of_stalk_nonneg f (ValCurr.prefixValuation h1 v) d hpd
  have hzU := hzc.mem_open (b.opens (b.centerIndex c)).isOpen (b.centerIndex_mem c)
  have hzV := hzd.mem_open (b.opens (b.centerIndex d)).isOpen (b.centerIndex_mem d)
  have : Nonempty (b.opens (b.centerIndex c)) := ⟨⟨_, hzU⟩⟩
  have : Nonempty (b.opens (b.centerIndex d)) := ⟨⟨_, hzV⟩⟩
  have hfr := frame_value_eq hz (b.frame (b.centerIndex c)) (b.frame (b.centerIndex d)) hzU hzV s
  have hv := plainSectionValue_eq_vector (v := v) c b s hs
  have hw := plainSectionValue_eq_vector (v := w) d b s hs
  have key : ((ValCurr.prefixHom h1 (toLex (plainSectionVector v c b s hs)) :
        Lex (Fin 1 → ℤ)) : WithTop (Lex (Fin 1 → ℤ))) =
      ((ValCurr.prefixHom h1 (toLex (plainSectionVector w d b s hs)) :
        Lex (Fin 1 → ℤ)) : WithTop (Lex (Fin 1 → ℤ))) := by
    calc ((ValCurr.prefixHom h1 (toLex (plainSectionVector v c b s hs)) :
          Lex (Fin 1 → ℤ)) : WithTop (Lex (Fin 1 → ℤ)))
        = ValCurr.prefixWithTopHom h1 (plainSectionValue v c b s) := by rw [hv]; rfl
      _ = ValCurr.prefixValuation h1 v
            (globalSectionToFunctionField (b.frame (b.centerIndex c)) s) := rfl
      _ = ValCurr.prefixValuation h1 v
            (globalSectionToFunctionField (b.frame (b.centerIndex d)) s) := hfr.symm
      _ = ValCurr.prefixValuation h1 w
            (globalSectionToFunctionField (b.frame (b.centerIndex d)) s) := by rw [hvw]
      _ = ValCurr.prefixWithTopHom h1 (plainSectionValue w d b s) := rfl
      _ = _ := by rw [hw]; rfl
  have h0 := congrArg (fun x : Lex (Fin 1 → ℤ) => ofLex x 0) (WithTop.coe_injective key)
  simpa only [ValCurr.prefixHom_apply, ofLex_toLex, Fin.castLE_zero] using h0

end Prefix

/-! ### First-coordinate projections of polytopes -/

section Poly

variable {n : ℕ}

/-- The coordinate projection `x ↦ x i` as a linear map on Euclidean space. -/
def coordinateLinearMap (i : Fin n) : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] ℝ where
  toFun x := x i
  map_add' x y := by simp
  map_smul' t x := by simp

/-- The coordinate projection of `poly Q k = Conv {k⁻¹ x : x ∈ Q k}` only depends on the
coordinate projection of `Q k`. -/
theorem image_coordinate_poly_eq (i : Fin n) {Q Q' : ℕ → Set (Fin n → ℤ)} (k : ℕ)
    (hQ : (fun x : Fin n → ℤ => x i) '' Q k = (fun x : Fin n → ℤ => x i) '' Q' k) :
    (fun x : EuclideanSpace ℝ (Fin n) => x i) '' poly Q k =
      (fun x : EuclideanSpace ℝ (Fin n) => x i) '' poly Q' k := by
  have hlin : ∀ S : Set (EuclideanSpace ℝ (Fin n)),
      (fun x : EuclideanSpace ℝ (Fin n) => x i) '' convexHull ℝ S =
        convexHull ℝ ((fun x : EuclideanSpace ℝ (Fin n) => x i) '' S) :=
    fun S => (coordinateLinearMap i).image_convexHull S
  have hcomp : (fun x : EuclideanSpace ℝ (Fin n) => x i) ∘
      (fun x : Fin n → ℤ => ((k : ℝ)⁻¹) • euclideanCast n x) =
      (fun t : ℤ => (k : ℝ)⁻¹ * (t : ℝ)) ∘ (fun x : Fin n → ℤ => x i) := by
    funext x
    simp [euclideanCast]
  unfold poly
  rw [hlin, hlin, ← Set.image_comp, ← Set.image_comp, hcomp, Set.image_comp, Set.image_comp, hQ]

/-- Coordinate minima are `1`-Lipschitz for the Hausdorff distance of compact convex sets. -/
theorem abs_sInf_image_coordinate_sub_le (i : Fin n) {A B : Set (EuclideanSpace ℝ (Fin n))}
    (hAc : IsCompact A) (hAv : Convex ℝ A) (hAn : A.Nonempty)
    (hBc : IsCompact B) (hBv : Convex ℝ B) (hBn : B.Nonempty) :
    |sInf ((fun x : EuclideanSpace ℝ (Fin n) => x i) '' A) -
      sInf ((fun x : EuclideanSpace ℝ (Fin n) => x i) '' B)| ≤ hausdorffDist A B := by
  let KA : ConvexBody (EuclideanSpace ℝ (Fin n)) := ⟨A, hAv, hAc, hAn⟩
  let KB : ConvexBody (EuclideanSpace ℝ (Fin n)) := ⟨B, hBv, hBc, hBn⟩
  have hf : LipschitzWith 1 (fun x : EuclideanSpace ℝ (Fin n) => -x i) :=
    (BodyExtrema.lipschitzWith_coordinate i).neg
  have h1 := BodyExtrema.upperValue_sub_le hf KA KB
  have h2 := BodyExtrema.upperValue_sub_le hf KB KA
  have hA := BodyExtrema.lowerValue_eq_neg_upperValue_neg (fun x : EuclideanSpace ℝ (Fin n) => x i) KA
  have hB := BodyExtrema.lowerValue_eq_neg_upperValue_neg (fun x : EuclideanSpace ℝ (Fin n) => x i) KB
  have hdist : dist KA KB = hausdorffDist A B := rfl
  have hdist' : dist KB KA = hausdorffDist A B := by rw [dist_comm]; rfl
  change |BodyExtrema.lowerValue (fun x : EuclideanSpace ℝ (Fin n) => x i) KA -
    BodyExtrema.lowerValue (fun x : EuclideanSpace ℝ (Fin n) => x i) KB| ≤ _
  rw [hA, hB, abs_le]
  simp only [NNReal.coe_one, one_mul] at h1 h2
  rw [hdist] at h1
  rw [hdist'] at h2
  constructor <;> linarith

/-- If compact convex sets `P k → K` in the Hausdorff metric, the coordinate minima converge. -/
theorem tendsto_sInf_image_coordinate (i : Fin n) {P : ℕ → Set (EuclideanSpace ℝ (Fin n))}
    {K : Set (EuclideanSpace ℝ (Fin n))}
    (hP : ∀ᶠ k in atTop, IsCompact (P k) ∧ (P k).Nonempty) (hPv : ∀ k, Convex ℝ (P k))
    (hKc : IsCompact K) (hKv : Convex ℝ K) (hKn : K.Nonempty)
    (hlim : Tendsto (fun k => hausdorffDist (P k) K) atTop (𝓝 0)) :
    Tendsto (fun k => sInf ((fun x : EuclideanSpace ℝ (Fin n) => x i) '' P k)) atTop
      (𝓝 (sInf ((fun x : EuclideanSpace ℝ (Fin n) => x i) '' K))) := by
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) ?_ hlim
  filter_upwards [hP] with k hk
  rw [Real.dist_eq]
  exact abs_sInf_image_coordinate_sub_le i hk.1 (hPv k) hk.2 hKc hKv hKn

end Poly

/-! ### `thm:nuOk` -/

section NuOk

variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ)) {m : ℕ}
  [SmoothOfRelativeDimension (m + 1) f] (E : ClosedProjectiveEmbedding f)
  [Nonempty (SchemeComplexPoint f)]

local instance ofNuOkTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance ofNuOkCharts : ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (m + 1)
local instance ofNuOkManifold [IsSeparated f] [QuasiCompact f] :
    IsComplexManifold (m + 1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (m + 1)

/-- The coordinate projection of a rescaled set. -/
theorem image_coordinate_smul {n : ℕ} (i : Fin n) (t : ℝ) (S : Set (EuclideanSpace ℝ (Fin n))) :
    (fun x : EuclideanSpace ℝ (Fin n) => x i) '' (t • S) =
      t • ((fun x : EuclideanSpace ℝ (Fin n) => x i) '' S) := by
  rw [← Set.image_smul, ← Set.image_smul, Set.image_image, Set.image_image]
  refine Set.image_congr fun x _ => ?_
  simp

/-- **Kähler currents**: two surjective valuations with the same first coordinate have partial
Okounkov bodies with the same first-coordinate minimum. -/
theorem sInf_firstCoordinate_partialBody_eq_of_kahler
    {L : X.Modules} (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f (m + 1) E L)
    (hbig : SGPT.LineBundle.IsBig f L (m + 1))
    (v w : AddValuation X.functionField (WithTop (Lex (Fin (m + 1) → ℤ))))
    (hv : Function.Surjective v) (hw : Function.Surjective w)
    (hpre : ValCurr.prefixValuation (Nat.le_add_left 1 m) v =
      ValCurr.prefixValuation (Nat.le_add_left 1 m) w)
    {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsKahlerCurrentPotential (H.curvature a) φ) :
    letI := E.isProper
    letI := E.isSeparated
    letI := E.quasiCompact
    ∀ (hKc : IsCompact (centreOkounkovBody f v a)) (hKv : Convex ℝ (centreOkounkovBody f v a))
      (hKc' : IsCompact (centreOkounkovBody f w a)) (hKv' : Convex ℝ (centreOkounkovBody f w a)),
      sInf ((fun x : EuclideanSpace ℝ (Fin (m + 1)) => x 0) ''
          ValGen.partialBody f (m + 1) E v (valuationCenter f v) a
            (SGPT.GAGA.OkoClose.coneOver _ hKc hKv) φ) =
        sInf ((fun x : EuclideanSpace ℝ (Fin (m + 1)) => x 0) ''
          ValGen.partialBody f (m + 1) E w (valuationCenter f w) a
            (SGPT.GAGA.OkoClose.coneOver _ hKc' hKv') φ) := by
  let := E.isProper
  let := E.isSeparated
  let := E.quasiCompact
  let : MeasurableSpace (SchemeComplexPoint f) := borel _
  have : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  intro hKc hKv hKc' hKv'
  have hφθ := PartialBody.isThetaPshPotential_of_isKahlerCurrentPotential hφ
  have hpos := OriginalBook.original_iVolume_pos_of_kahler_allDimensions f (m + 1) E a H hφ
  let r : ∀ k, LineBundleAtlas (bundleTensor L (bundleTensorPower L k)) :=
    fun k => SGPT.IGood.DXMain.twistAtlas a a k
  set Kv := ValGen.partialBody f (m + 1) E v (valuationCenter f v) a
    (SGPT.GAGA.OkoClose.coneOver _ hKc hKv) φ with hKvdef
  set Kw := ValGen.partialBody f (m + 1) E w (valuationCenter f w) a
    (SGPT.GAGA.OkoClose.coneOver _ hKc' hKv') φ with hKwdef
  -- `thm:HCP` for Kähler currents, for `v` and for `w`
  obtain ⟨_, _, hlim⟩ :=
    OriginalBook.tendsto_twistedMultiplierPolytope_kahler_positiveDimension f E a a H hbig v hv r hφ
  obtain ⟨_, _, hlim'⟩ :=
    OriginalBook.tendsto_twistedMultiplierPolytope_kahler_positiveDimension f E a a H hbig w hw r hφ
  have hlimv : Tendsto (fun k : ℕ => hausdorffDist
      (poly (fun k => AlgebraicValuation.twistedMultiplierValues f (m + 1) E v
        (valuationCenter f v) k (r k) φ) k) Kv) atTop (𝓝 0) := hlim
  have hlimw : Tendsto (fun k : ℕ => hausdorffDist
      (poly (fun k => AlgebraicValuation.twistedMultiplierValues f (m + 1) E w
        (valuationCenter f w) k (r k) φ) k) Kw) atTop (𝓝 0) := hlim'
  have hev := OriginalBook.eventually_twistedMultiplierPolytope_compact_nonempty_positiveDimension
    f E a a H hbig v hv (valuationCenter f v) r hφθ hpos
  have hev' := OriginalBook.eventually_twistedMultiplierPolytope_compact_nonempty_positiveDimension
    f E a a H hbig w hw (valuationCenter f w) r hφθ hpos
  -- the two bodies are compact, convex and nonempty (`thm:Gammaasg`, `cor:POBvolume`)
  obtain ⟨_hKc₁, _hKv₁, _hsubv, _hΓv, -, -, hvolv⟩ :=
    OriginalBook.centreMultiplierSectionSet_mem_ownBody_almostSemigroupLocus_allDimensions
      f (m + 1) E a H hbig v hv hφθ hpos
  obtain ⟨_hKc₂, _hKv₂, _hsubw, _hΓw, -, -, hvolw⟩ :=
    OriginalBook.centreMultiplierSectionSet_mem_ownBody_almostSemigroupLocus_allDimensions
      f (m + 1) E a H hbig w hw hφθ hpos
  have hIpos : (0 : ℝ≥0∞) <
      iVolume (H.curvature a) (LocalPotentials.closedRealOneOne_hasLocalPotentials _) φ hφθ /
        ((m + 1).factorial : ℝ≥0∞) :=
    ENNReal.div_pos hpos.ne' (ENNReal.natCast_ne_top _)
  have hKvn : Kv.Nonempty := by
    apply MeasureTheory.nonempty_of_measure_ne_zero (μ := volume)
    have h : volume Kv = _ := hvolv
    rw [h]
    exact hIpos.ne'
  have hKwn : Kw.Nonempty := by
    apply MeasureTheory.nonempty_of_measure_ne_zero (μ := volume)
    have h : volume Kw = _ := hvolw
    rw [h]
    exact hIpos.ne'
  -- the first coordinates of the polytopes of `v` and `w` coincide
  have hcv : IsNonnegAt v (valuationCenter f v) := (isValuationCenter_valuationCenter f v).1
  have hcw : IsNonnegAt w (valuationCenter f w) := (isValuationCenter_valuationCenter f w).1
  have hpoly : ∀ k : ℕ,
      (fun x : EuclideanSpace ℝ (Fin (m + 1)) => x 0) ''
          poly (fun k => AlgebraicValuation.twistedMultiplierValues f (m + 1) E v
            (valuationCenter f v) k (r k) φ) k =
        (fun x : EuclideanSpace ℝ (Fin (m + 1)) => x 0) ''
          poly (fun k => AlgebraicValuation.twistedMultiplierValues f (m + 1) E w
            (valuationCenter f w) k (r k) φ) k := by
    intro k
    apply image_coordinate_poly_eq
    ext t
    constructor
    · rintro ⟨x, ⟨s, hs, hcond, rfl⟩, rfl⟩
      exact ⟨_, ⟨s, hs, hcond, rfl⟩,
        (plainSectionVector_zero_eq_of_prefixValuation_eq f v w hpre hcv hcw (r k) s hs).symm⟩
    · rintro ⟨x, ⟨s, hs, hcond, rfl⟩, rfl⟩
      exact ⟨_, ⟨s, hs, hcond, rfl⟩,
        plainSectionVector_zero_eq_of_prefixValuation_eq f v w hpre hcv hcw (r k) s hs⟩
  -- pass to the limit
  have hmv := tendsto_sInf_image_coordinate 0
    (hev.mono fun k hk => ⟨hk.2, poly_nonempty hk.1⟩) (fun _ => convex_convexHull ℝ _)
    (ValGen.isCompact_setBody _ _) (ValGen.convex_setBody _ _) hKvn hlimv
  have hmw := tendsto_sInf_image_coordinate 0
    (hev'.mono fun k hk => ⟨hk.2, poly_nonempty hk.1⟩) (fun _ => convex_convexHull ℝ _)
    (ValGen.isCompact_setBody _ _) (ValGen.convex_setBody _ _) hKwn hlimw
  refine tendsto_nhds_unique hmv ?_
  refine hmw.congr fun k => ?_
  rw [hpoly k]

/-- **Every `φ` with `vol θ_φ > 0`**: two surjective valuations with the same first coordinate
have partial Okounkov bodies with the same first-coordinate minimum. As in the book (proof of
`thm:nuOk`), `L` is perturbed by the ample `𝒪_X(1)` (`prop:Deltapert`), which makes `θ_φ` a
Kähler current. -/
theorem sInf_firstCoordinate_partialBody_eq
    {L : X.Modules} (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f (m + 1) E L)
    (v w : AddValuation X.functionField (WithTop (Lex (Fin (m + 1) → ℤ))))
    (hv : Function.Surjective v) (hw : Function.Surjective w)
    (hpre : ValCurr.prefixValuation (Nat.le_add_left 1 m) v =
      ValCurr.prefixValuation (Nat.le_add_left 1 m) w)
    {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val φ)
    (hpos : letI := E.isSeparated; letI := E.quasiCompact;
      letI : MeasurableSpace (SchemeComplexPoint f) := borel _;
      haveI : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩;
      haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact;
      0 < iVolume (H.curvature a) (LocalPotentials.closedRealOneOne_hasLocalPotentials _) φ hφ) :
    letI := E.isProper
    letI := E.isSeparated
    letI := E.quasiCompact
    ∀ (hKc : IsCompact (centreOkounkovBody f v a)) (hKv : Convex ℝ (centreOkounkovBody f v a))
      (hKc' : IsCompact (centreOkounkovBody f w a)) (hKv' : Convex ℝ (centreOkounkovBody f w a)),
      sInf ((fun x : EuclideanSpace ℝ (Fin (m + 1)) => x 0) ''
          ValGen.partialBody f (m + 1) E v (valuationCenter f v) a
            (SGPT.GAGA.OkoClose.coneOver _ hKc hKv) φ) =
        sInf ((fun x : EuclideanSpace ℝ (Fin (m + 1)) => x 0) ''
          ValGen.partialBody f (m + 1) E w (valuationCenter f w) a
            (SGPT.GAGA.OkoClose.coneOver _ hKc' hKv') φ) := by
  let := E.isProper
  let := E.isSeparated
  let := E.quasiCompact
  let : MeasurableSpace (SchemeComplexPoint f) := borel _
  have : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  intro hKc hKv hKc' hKv'
  have hbig := OriginalBook.original_isBig_of_positive_iVolume_allDimensions f (m + 1) E a H hφ hpos
  set Kv := ValGen.partialBody f (m + 1) E v (valuationCenter f v) a
    (SGPT.GAGA.OkoClose.coneOver _ hKc hKv) φ with hKvdef
  set Kw := ValGen.partialBody f (m + 1) E w (valuationCenter f w) a
    (SGPT.GAGA.OkoClose.coneOver _ hKc' hKv') φ with hKwdef
  -- the ample perturbation `𝒪_X(1)` with its Fubini–Study metric
  let aA := hyperplaneAtlas E
  let K := fubiniStudyMetric f E (m + 1)
  have hK := fubiniStudy_curvature_isKahler f (m + 1) E
  let P : SGPT.LineBundle.AmplePolarization f (hyperplaneBundle E) :=
    { power := 1
      power_pos := one_pos
      ambientDimension := E.ambientDimension
      map := E.map
      isClosedImmersion := E.closedImmersion
      over_base := E.over_base
      iso := bundleTensorLeftUnitIso (hyperplaneBundle E) }
  obtain ⟨_, _, hpertv⟩ := OriginalBook.tendsto_normalized_positivePerturb_partialBody_allDimensions
    f (m + 1) E a H aA P K hK hφ hpos v hv
  obtain ⟨_, _, hpertw⟩ := OriginalBook.tendsto_normalized_positivePerturb_partialBody_allDimensions
    f (m + 1) E a H aA P K hK hφ hpos w hw
  let q : ℕ → ℕ := fun i => i + 1
  let p : ℕ → ℕ := fun _ => 1
  have hq : ∀ i, 0 < q i := fun i => Nat.succ_pos i
  have hp : ∀ i, 0 < p i := fun _ => one_pos
  have hqp : Tendsto (fun i => (p i : ℝ) / (q i : ℝ)) atTop (𝓝 0) := by
    have h := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    refine h.congr fun i => ?_
    simp [p, q]
  obtain ⟨hKic, hKiv, hcpt, hne, hlim⟩ := hpertv ℕ atTop q p hq hp hqp
  obtain ⟨hKic', hKiv', hcpt', hne', hlim'⟩ := hpertw ℕ atTop q p hq hp hqp
  -- the two bodies are compact, convex and nonempty
  obtain ⟨_hKc₁, _hKv₁, _hsubv, _hΓv, -, -, hvolv⟩ :=
    OriginalBook.centreMultiplierSectionSet_mem_ownBody_almostSemigroupLocus_allDimensions
      f (m + 1) E a H hbig v hv hφ hpos
  obtain ⟨_hKc₂, _hKv₂, _hsubw, _hΓw, -, -, hvolw⟩ :=
    OriginalBook.centreMultiplierSectionSet_mem_ownBody_almostSemigroupLocus_allDimensions
      f (m + 1) E a H hbig w hw hφ hpos
  have hIpos : (0 : ℝ≥0∞) <
      iVolume (H.curvature a) (LocalPotentials.closedRealOneOne_hasLocalPotentials _) φ hφ /
        ((m + 1).factorial : ℝ≥0∞) :=
    ENNReal.div_pos hpos.ne' (ENNReal.natCast_ne_top _)
  have hKvn : Kv.Nonempty := by
    apply MeasureTheory.nonempty_of_measure_ne_zero (μ := volume)
    have h : volume Kv = _ := hvolv
    rw [h]
    exact hIpos.ne'
  have hKwn : Kw.Nonempty := by
    apply MeasureTheory.nonempty_of_measure_ne_zero (μ := volume)
    have h : volume Kw = _ := hvolw
    rw [h]
    exact hIpos.ne'
  -- the perturbed weights are Kähler currents: the Kähler case applies
  have heq : ∀ i : ℕ,
      sInf ((fun x : EuclideanSpace ℝ (Fin (m + 1)) => x 0) ''
          ((q i : ℝ)⁻¹ • ValGen.partialBody f (m + 1) E v (valuationCenter f v)
            (OkoNS.perturbAtlas a aA (q i) (p i))
            (SGPT.GAGA.OkoClose.coneOver _ (hKic i) (hKiv i)) (fun x => (q i : EReal) * φ x))) =
        sInf ((fun x : EuclideanSpace ℝ (Fin (m + 1)) => x 0) ''
          ((q i : ℝ)⁻¹ • ValGen.partialBody f (m + 1) E w (valuationCenter f w)
            (OkoNS.perturbAtlas a aA (q i) (p i))
            (SGPT.GAGA.OkoClose.coneOver _ (hKic' i) (hKiv' i)) (fun x => (q i : EReal) * φ x))) := by
    intro i
    obtain ⟨hKφ, hbigi⟩ := OriginalBook.original_positivePerturbation_kahler_and_big f (m + 1) E
      a H aA K hK hφ (q i) (p i) (hq i) (hp i)
    have h := sInf_firstCoordinate_partialBody_eq_of_kahler f E (OkoNS.perturbAtlas a aA (q i) (p i))
      (OriginalBook.originalPerturbMetric f (m + 1) E a H aA K (q i) (p i)) hbigi v w hv hw hpre hKφ
      (hKic i) (hKiv i) (hKic' i) (hKiv' i)
    have hinv : (0 : ℝ) ≤ (q i : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
    rw [image_coordinate_smul, image_coordinate_smul, Real.sInf_smul_of_nonneg hinv,
      Real.sInf_smul_of_nonneg hinv]
    exact congrArg (fun t : ℝ => (q i : ℝ)⁻¹ • t) h
  -- pass to the limit
  have hmv := tendsto_sInf_image_coordinate 0
    (Eventually.of_forall fun i => ⟨hcpt i, hne i⟩)
    (fun i => (ValGen.convex_setBody _ _).smul _)
    (ValGen.isCompact_setBody _ _) (ValGen.convex_setBody _ _) hKvn hlim
  have hmw := tendsto_sInf_image_coordinate 0
    (Eventually.of_forall fun i => ⟨hcpt' i, hne' i⟩)
    (fun i => (ValGen.convex_setBody _ _).smul _)
    (ValGen.isCompact_setBody _ _) (ValGen.convex_setBody _ _) hKwn hlim'
  refine tendsto_nhds_unique hmv ?_
  exact hmw.congr fun i => (heq i).symm

variable (Y : Fin (m + 1 + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y)
  {L : X.Modules} (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f (m + 1) E L)

include a H in
/-- The flag valuation `ν_{Y•}` of a smooth flag is surjective (for `X` carrying a big line
bundle): `Γ_{Y•}(L)` generates `ℤⁿ⁺¹`. -/
theorem surjective_flagValuation (hbig : SGPT.LineBundle.IsBig f L (m + 1)) :
    Function.Surjective (schemeFubiniStudyFunctionFieldValuation f (m + 1) E Y hY) := by
  apply surjective_of_generatedGroup_eq_top _ (flagCentre (f := f) (n := m + 1) (E := E) Y hY) a
  rw [sectionSemigroup_flag]
  exact SGPT.GAGA.H0L.generatedGroup_sectionSemigroup_eq_top f E Y hY a H hbig

omit [Nonempty (SchemeComplexPoint f)] in
/-- The centre of the flag valuation is the image of the flag point. -/
theorem valuationCenter_flagValuation :
    letI := E.isProper
    valuationCenter f (schemeFubiniStudyFunctionFieldValuation f (m + 1) E Y hY) =
      flagCentre (f := f) (n := m + 1) (E := E) Y hY := by
  let := E.isProper
  let := E.isSeparated
  let := E.quasiCompact
  exact ((isValuationCenter_iff_eq f _ _).mp
    (schemeOriginalFlagFunctionFieldValuation_isCenter f (m + 1) E
      (schemeProjectiveTNKahlerBackground f (m + 1) E) Y hY)).symm

/-- **Source `thm:nuOk`, for every valuation whose first coordinate is `ord_E`, `E` smooth.** Let
`Y•` be a smooth flag and `ν` any surjective rank `n` valuation of `ℂ(X)` with the same first
coordinate as `ν_{Y•}` (i.e. `ν₁ = ord_{Y₁}`; e.g. `ν = ν_{Y'•}` for an admissible flag `Y'•`
with `Y'₁ = Y₁`). Then for every `φ ∈ PSH(X, θ)` with `vol θ_φ > 0`,
`ν(φ, Y₁) = min_{x ∈ Δ_ν(θ, φ)} x₁`, where `Δ_ν(θ, φ)` is the partial Okounkov body of
`def:Okounkov:L687` (in the cone over `Δ_ν(L)`, section values at the centre of `ν`). -/
theorem isLeast_firstCoordinate_partialBody_of_prefix_eq
    (v : AddValuation X.functionField (WithTop (Lex (Fin (m + 1) → ℤ))))
    (hv : Function.Surjective v)
    (hpre : ValCurr.prefixValuation (Nat.le_add_left 1 m) v =
      ValCurr.prefixValuation (Nat.le_add_left 1 m)
        (schemeFubiniStudyFunctionFieldValuation f (m + 1) E Y hY))
    {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val φ)
    (hpos : letI := E.isSeparated; letI := E.quasiCompact;
      letI : MeasurableSpace (SchemeComplexPoint f) := borel _;
      haveI : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩;
      haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact;
      0 < iVolume (H.curvature a) (LocalPotentials.closedRealOneOne_hasLocalPotentials _) φ hφ) :
    letI := E.isProper
    letI := E.isSeparated
    letI := E.quasiCompact
    ∃ (hKc : IsCompact (centreOkounkovBody f v a)) (hKv : Convex ℝ (centreOkounkovBody f v a)),
      IsLeast ((fun x : EuclideanSpace ℝ (Fin (m + 1)) => x 0) ''
          ValGen.partialBody f (m + 1) E v (valuationCenter f v) a
            (SGPT.GAGA.OkoClose.coneOver _ hKc hKv) φ)
        (SGPT.Okounkov.OkoLelong.firstFlagLelong f Y φ) := by
  let := E.isProper
  let := E.isSeparated
  let := E.quasiCompact
  let : MeasurableSpace (SchemeComplexPoint f) := borel _
  have : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  have hbig := OriginalBook.original_isBig_of_positive_iVolume_allDimensions f (m + 1) E a H hφ hpos
  set w := schemeFubiniStudyFunctionFieldValuation f (m + 1) E Y hY with hw
  have hwsurj : Function.Surjective w := surjective_flagValuation f E Y hY a H hbig
  have hcw : valuationCenter f w = flagCentre (f := f) (n := m + 1) (E := E) Y hY :=
    valuationCenter_flagValuation f E Y hY
  -- geometry of the two bodies (`thm:Gammaasg`, `cor:POBvolume`)
  obtain ⟨hKc, hKv, _hsubv, _hΓv, -, -, hvolv⟩ :=
    OriginalBook.centreMultiplierSectionSet_mem_ownBody_almostSemigroupLocus_allDimensions
      f (m + 1) E a H hbig v hv hφ hpos
  obtain ⟨hKc', hKv', hsubw, hΓw, -, -, _hvolw⟩ :=
    OriginalBook.centreMultiplierSectionSet_mem_ownBody_almostSemigroupLocus_allDimensions
      f (m + 1) E a H hbig w hwsurj hφ hpos
  refine ⟨hKc, hKv, ?_⟩
  set Kv := ValGen.partialBody f (m + 1) E v (valuationCenter f v) a
    (SGPT.GAGA.OkoClose.coneOver _ hKc hKv) φ with hKvdef
  set Kw := ValGen.partialBody f (m + 1) E w (valuationCenter f w) a
    (SGPT.GAGA.OkoClose.coneOver _ hKc' hKv') φ with hKwdef
  have hIpos : (0 : ℝ≥0∞) <
      iVolume (H.curvature a) (LocalPotentials.closedRealOneOne_hasLocalPotentials _) φ hφ /
        ((m + 1).factorial : ℝ≥0∞) :=
    ENNReal.div_pos hpos.ne' (ENNReal.natCast_ne_top _)
  have hKvn : Kv.Nonempty := by
    apply MeasureTheory.nonempty_of_measure_ne_zero (μ := volume)
    have h : volume Kv = _ := hvolv
    rw [h]
    exact hIpos.ne'
  have hKvc : IsCompact Kv := ValGen.isCompact_setBody _ _
  -- the first-coordinate minima of the bodies of `v` and of `ν_{Y•}` coincide
  have hmin : sInf ((fun x : EuclideanSpace ℝ (Fin (m + 1)) => x 0) '' Kv) =
      sInf ((fun x : EuclideanSpace ℝ (Fin (m + 1)) => x 0) '' Kw) :=
    sInf_firstCoordinate_partialBody_eq f E a H v w hv hwsurj hpre hφ hpos hKc hKv hKc' hKv'
  -- the body of the flag valuation is the existing algebraic partial body of the flag
  obtain ⟨C₀, _hC₀, hC⟩ :=
    SGPT.GAGA.OkoClose.isLeast_firstCoordinate_partialOkounkovBody f E Y hY a H
  obtain ⟨C₁, _hC₁, hcube⟩ := exists_lineBundleOkounkovBody_subset_cube f (m + 1) E Y hY a
  set C' := max C₀ C₁
  have hposY := AlgPOB.volume_real_generalPartialBody_pos f E Y hY a H hφ hpos
  have hLeast := hC C' (le_max_left _ _) φ hφ hposY
  have hCD : ((SGPT.GAGA.OkoClose.coneOver _ hKc' hKv').cone :
      Set ((Fin (m + 1) → ℝ) × ℝ)) ⊆ (cubeCone (n := m + 1) C').cone := by
    rintro z ⟨hz2, y, hy, hz1⟩
    have hy' : y ∈ lineBundleOkounkovBody f (m + 1) E Y hY a := by
      rw [← okounkovBody_flag, ← hcw]
      exact hy
    have hyc := hcube hy'
    refine ⟨hz2, fun i => ?_⟩
    have hyi0 : 0 ≤ y i := hyc.1 i
    have hyi1 : y i ≤ C₁ := hyc.2 i
    have hz1i : z.1 i = z.2 * y i := by rw [hz1]; rfl
    rw [hz1i]
    refine ⟨mul_nonneg hz2 hyi0, ?_⟩
    calc z.2 * y i ≤ z.2 * C₁ := mul_le_mul_of_nonneg_left hyi1 hz2
      _ ≤ z.2 * C' := mul_le_mul_of_nonneg_left (le_max_right _ _) hz2
      _ = C' * z.2 := mul_comm _ _
  have hKweq : Kw = partialOkounkovBody f (m + 1) E Y hY (cubeCone C') a φ := by
    have h1 := setBody_of_cone_le hCD hsubw hΓw
    have h2 : partialOkounkovBody f (m + 1) E Y hY (cubeCone C') a φ =
        ValGen.setBody (cubeCone (n := m + 1) C') (centreMultiplierSectionSet f (m + 1) E w a φ) := by
      change ValGen.setBody (cubeCone (n := m + 1) C')
          (SGPT.Okounkov.multiplierSectionSet f (m + 1) E Y hY a φ) = _
      rw [← multiplierSectionSet_flag (f := f) (n := m + 1) (E := E) Y hY a φ]
      change _ = ValGen.setBody (cubeCone (n := m + 1) C')
        (AlgebraicValuation.multiplierSectionSet f (m + 1) E w (valuationCenter f w) a φ)
      rw [hcw]
    rw [h2, h1]
    try rfl
  have hwmin : sInf ((fun x : EuclideanSpace ℝ (Fin (m + 1)) => x 0) '' Kw) =
      SGPT.Okounkov.OkoLelong.firstFlagLelong f Y φ := by
    rw [hKweq]
    exact hLeast.csInf_eq
  have hcompact : IsCompact ((fun x : EuclideanSpace ℝ (Fin (m + 1)) => x 0) '' Kv) :=
    hKvc.image (BodyExtrema.lipschitzWith_coordinate (0 : Fin (m + 1))).continuous
  have hleast := hcompact.isLeast_sInf (hKvn.image _)
  rw [hmin, hwmin] at hleast
  exact hleast

end NuOk

end SGPT.Okounkov.OF
