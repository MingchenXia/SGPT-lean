import SGPT.NAPotential.DivDictComparison
import SGPT.NAPotential.AnTransPLCurve
import SGPT.PSH.LelongArithmetic

/-! # `A^An = Ã^An` on `X^Div` for piecewise linear curves

Source `lma:psieqpsiprimeondiv` (`chapter_NApotential.tex`), equation `eq:psieqsiprime`: for a
piecewise linear curve `A` in `PSH(X, θ)` (`def:piecewiselincurv`) and the `𝓘`-projected
regularized concave envelope `Ã` of `rmk:pwlinhull`, `A^An = Ã^An` on `X^Div`.
Blueprint `claude-div-dict:lelong-hull`, `claude-div-dict:psieqpsiprime`.

The book's proof: *fix `v ∈ X^Div` and put `a_i = A_i^An(v)`.  Analytification commutes with
finite maxima and positive linear combinations on divisorial valuations.  Since `𝓘`-projection
preserves these valuations, `eq:pwlinhull-simplex` gives
`(Ã_τ)^An(v) + τ = max_{λ ∈ Λ_τ} Σ λ_i a_i + τ ≤ max_i (a_i + τ_i)`.  Conversely
`A'_τ ≥ A_i` whenever `τ < τ_i`.*

## Main results

* `presentationReader_finset_sup'_ge`: the generic Lelong number along a prime divisor of a
  finite maximum is at least the minimum of the generic Lelong numbers.
* `presentationReader_weighted_ge`: for weights `w_i ≥ 0`,
  `ν(Σ_i w_i u_i, E) ≥ Σ_i w_i ν(u_i, E)` (quasi-psh `u_i`).
* `curveAn_le_naPotentialAnAt_hull`: `A^An ≤ Ã^An` on all of `X^An` (conditional on
  `MultiplierIdealAlgebraic`).
* `curveAn_eq_naPotentialAnAt_hull`: **`eq:psieqsiprime`**, `A^An = Ã^An` on `X^Div` (the
  divisorial valuations and the trivial valuation), conditional on `MultiplierIdealAlgebraic` and
  on the algebraic half of the dictionary of prime divisors (`AlgebraicPrimesRealized`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.NAPotential.Berkovich

open Set Filter
open scoped Topology ENNReal
open AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes SGPT.Okounkov
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending.SquaredLogLelongSourceNormalization
open SGPT.PSH.VariableComplexAtlas SGPT.PSH.CompactPrimeOver SGPT.NAPotential.BJPrep
open PiecewiseLinearData SimplexRevision SimplexRevision.WholeHull SGPT.Convex.CutSimplex

/-! ### Generic Lelong numbers of maxima and of positive combinations -/

section Lelong

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- Sums of quasi-psh functions on a complex manifold are quasi-psh. -/
theorem manifoldQuasiPlurisubharmonic_add {u v : M → EReal}
    (hu : ManifoldQuasiPlurisubharmonic (n := n) u)
    (hv : ManifoldQuasiPlurisubharmonic (n := n) v) :
    ManifoldQuasiPlurisubharmonic (n := n) (fun y => u y + v y) := by
  intro e z hz
  obtain ⟨p, h, hp, hh, hpu⟩ := hu e z hz
  obtain ⟨q, k, hq, hk, hqv⟩ := hv e z hz
  refine ⟨fun y => p y + q y, fun y => h y + k y, hp.add hq, ?_, ?_⟩
  · filter_upwards [hh, hk] with y hy ky
    exact hy.add ky
  · filter_upwards [hpu, hqv] with y uy vy
    change chartFunction u e y + chartFunction v e y = _
    rw [uy, vy, EReal.coe_add]
    ac_rfl

/-- Pointwise Lelong numbers of a nonnegative combination of quasi-psh functions:
`Σ_i w_i ν(u_i, y) ≤ ν(Σ_i w_i u_i, y)`, together with the quasi-plurisubharmonicity of the
combination. -/
theorem squaredLogLelongNumber_weighted_ge {ι : Type*} (S : Finset ι) (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (u : ι → M → EReal)
    (hu : ∀ i, ManifoldQuasiPlurisubharmonic (n := n) (u i)) :
    ManifoldQuasiPlurisubharmonic (n := n) (fun y => ∑ i ∈ S, (w i : EReal) * u i y) ∧
      ∀ y, ∑ i ∈ S, ENNReal.ofReal (w i) * squaredLogLelongNumber (n := n) (u i) y ≤
        squaredLogLelongNumber (n := n) (fun y => ∑ i ∈ S, (w i : EReal) * u i y) y := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨?_, fun y => by simp⟩
    simpa only [Finset.sum_empty, EReal.coe_zero] using
      (manifoldQuasiPlurisubharmonic_const (n := n) (M := M) 0)
  | @insert a S ha ih =>
    obtain ⟨hS, hSy⟩ := ih
    have hterm : ManifoldQuasiPlurisubharmonic (n := n) (fun y => (w a : EReal) * u a y) := by
      rcases (hw a).lt_or_eq with hpos | hzero
      · exact manifoldQuasiPlurisubharmonic_const_mul (hu a) hpos
      · have he : (fun y => (w a : EReal) * u a y) = fun _ => ((0 : ℝ) : EReal) := by
          funext y
          rw [← hzero, EReal.coe_zero, zero_mul]
        rw [he]
        exact manifoldQuasiPlurisubharmonic_const 0
    have hsum : (fun y => ∑ i ∈ insert a S, (w i : EReal) * u i y) =
        fun y => (w a : EReal) * u a y + ∑ i ∈ S, (w i : EReal) * u i y := by
      funext y
      rw [Finset.sum_insert ha]
    rw [hsum]
    refine ⟨manifoldQuasiPlurisubharmonic_add hterm hS, fun y => ?_⟩
    rw [SGPT.Okounkov.squaredLogLelongNumber_add_eq hterm hS y, Finset.sum_insert ha]
    refine add_le_add ?_ (hSy y)
    rcases (hw a).lt_or_eq with hpos | hzero
    · rw [SGPT.Okounkov.squaredLogLelongNumber_smul_eq (u a) y hpos]
    · rw [← hzero, ENNReal.ofReal_zero, zero_mul]
      exact zero_le

variable {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

/-- The generic Lelong number along `E` as an infimum of pointwise Lelong numbers on `E`. -/
theorem presentationReader_eq_iInf (φ : X → EReal) (p : PrimePresentation n X) :
    presentationReader φ p =
      ⨅ q ∈ p.divisor, squaredLogLelongNumber (n := n) (fun y => φ (p.projection y)) q := by
  unfold presentationReader sourceGenericLelong
  simp_rw [sourceLelong_ofFixedModel_eq]
  rfl

/-- **Positive combinations** (generic Lelong numbers along a prime divisor over `X`):
`Σ_i w_i ν(u_i, E) ≤ ν(Σ_i w_i u_i, E)` for `w_i ≥ 0` and `θ`-psh `u_i`. -/
theorem presentationReader_weighted_ge {ι : Type*} (S : Finset ι)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n X)} (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (u : ι → X → EReal) (hu : ∀ i, (ofFixedModel n X).IsThetaPSH θ (u i))
    (p : PrimePresentation n X) :
    ∑ i ∈ S, ENNReal.ofReal (w i) * presentationReader (u i) p ≤
      presentationReader (fun x => ∑ i ∈ S, (w i : EReal) * u i x) p := by
  have hq : ∀ i, ManifoldQuasiPlurisubharmonic (n := n)
      (fun y => u i (p.projection y)) := fun i =>
    manifoldQuasiPlurisubharmonic_comp_projection (hu i) p
  have hpt := (squaredLogLelongNumber_weighted_ge S w hw
    (fun i y => u i (p.projection y)) hq).2
  rw [presentationReader_eq_iInf]
  refine le_iInf₂ fun q hqE => ?_
  refine le_trans (Finset.sum_le_sum fun i _ => ?_) (hpt q)
  rw [presentationReader_eq_iInf]
  gcongr
  exact iInf₂_le q hqE

/-- **Finite maxima** (generic Lelong numbers along a prime divisor over `X`): the generic
Lelong number of a finite maximum is at least the minimum of the generic Lelong numbers. -/
theorem presentationReader_finset_sup'_ge {ι : Type*} (S : Finset ι) (hS : S.Nonempty)
    (u : ι → X → EReal) (p : PrimePresentation n X) :
    S.inf' hS (fun i => presentationReader (u i) p) ≤
      presentationReader (fun x => S.sup' hS (fun i => u i x)) p := by
  -- pointwise: the Lelong number of a finite maximum is the minimum
  have hpt : ∀ y : p.model, (ofFixedModel n p.model).sourceLelong
      (fun z => S.sup' hS (fun i => u i (p.projection z))) y =
        S.inf' hS (fun i => (ofFixedModel n p.model).sourceLelong
          (fun z => u i (p.projection z)) y) := by
    intro y
    induction hS using Finset.Nonempty.cons_induction with
    | singleton a => simp
    | cons a S ha hS ih =>
      simp_rw [Finset.sup'_cons hS, Finset.inf'_cons hS]
      rw [sourceLelong_max_eq]
      congr 1
  unfold presentationReader sourceGenericLelong
  refine le_iInf₂ fun q hqE => ?_
  change S.inf' hS (fun i => presentationReader (u i) p) ≤
    (ofFixedModel n p.model).sourceLelong
      (fun z => S.sup' hS (fun i => u i (p.projection z))) q
  rw [hpt q]
  refine Finset.le_inf' _ _ fun i hi => (Finset.inf'_le _ hi).trans ?_
  unfold presentationReader sourceGenericLelong
  exact iInf₂_le q hqE

end Lelong

/-! ### The comparison `A^An = Ã^An` -/

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} (m : ℕ) [SmoothOfRelativeDimension (m + 1) f]
  (E : ClosedProjectiveEmbedding f) [IsProper f]

local instance divDictPLPointTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance divDictPLPointCharts : ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (m + 1)
local instance divDictPLPointManifold : IsComplexManifold (m + 1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (m + 1)

variable [MeasurableSpace (SchemeComplexPoint f)] [BorelSpace (SchemeComplexPoint f)]
  [CompactSpace (SchemeComplexPoint f)] [ConnectedSpace (SchemeComplexPoint f)]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel (m + 1) (SchemeComplexPoint f))}

variable {m E}

/-- `Ã^An(v) = sup_{τ < τ_0} ((A'_τ)^An(v) + τ)` with `A'_τ` the simplex hull `simplexValue`. -/
theorem naPotentialAnAt_hull_eq (D : PiecewiseLinearData θ)
    (ω : SourceKahlerForm (m + 1) (SchemeComplexPoint f)) (v : BerkovichPoint f) :
    naPotentialAnAt (m + 1) E (hullNAPotential D) ω v =
      ⨆ τ : Iio (D.τ 0), potentialAn (m + 1) E (simplexValue D τ) v + ((τ : ℝ) : EReal) := by
  rw [naPotentialAnAt_hullNAPotential]
  simp_rw [uscRegularization_pointwiseUpperConcaveEnvelope_eq_simplexValue]

omit [MeasurableSpace (SchemeComplexPoint f)] [BorelSpace (SchemeComplexPoint f)]
  [CompactSpace (SchemeComplexPoint f)] [ConnectedSpace (SchemeComplexPoint f)] in
/-- `(ofFixedModel).IsThetaPSH` gives the `SGPT.Foundations.Analysis` notion. -/
private theorem native_of_isThetaPSH {φ : SchemeComplexPoint f → EReal}
    (hφ : (ofFixedModel (m + 1) (SchemeComplexPoint f)).IsThetaPSH θ φ) :
    IsThetaPshPotential (atlasClosedFormToNative θ).val φ :=
  (isThetaPSH_iff_nativeThetaPotential θ φ).mp hφ

/-- **`A^An ≤ Ã^An` on `X^An`** (the inequality `A'_τ ≥ A_τ` of the proof of
`lma:psieqpsiprimeondiv`), conditional on `MultiplierIdealAlgebraic`. -/
theorem curveAn_le_naPotentialAnAt_hull (hA : MultiplierIdealAlgebraic f (m + 1) E)
    (D : PiecewiseLinearData θ) (ω : SourceKahlerForm (m + 1) (SchemeComplexPoint f))
    (v : BerkovichPoint f) :
    D.curveAn (m + 1) E v ≤ naPotentialAnAt (m + 1) E (hullNAPotential D) ω v := by
  rw [naPotentialAnAt_hull_eq]
  set S := ⨆ τ : Iio (D.τ 0), potentialAn (m + 1) E (simplexValue D τ) v + ((τ : ℝ) : EReal)
  have hterm : ∀ (r : ℝ) (hr : r < D.τ 0),
      potentialAn (m + 1) E (simplexValue D r) v + (r : EReal) ≤ S := fun r hr =>
    le_iSup (fun τ : Iio (D.τ 0) =>
      potentialAn (m + 1) E (simplexValue D τ) v + ((τ : ℝ) : EReal)) ⟨r, hr⟩
  refine iSup₂_le fun s hs => ?_
  rcases hs.lt_or_eq with hlt | heq
  · refine le_trans (add_le_add ?_ le_rfl) (hterm s hlt)
    exact BerkovichPoint.potentialAn_mono_of_multiplierIdealAlgebraic (m + 1) E hA
      (native_of_isThetaPSH (D.isThetaPSH_curve hs))
      (native_of_isThetaPSH (isThetaPSH_simplexValue D s hs))
      (fun x => curve_le_simplexValue D s x) v
  · subst heq
    rw [D.curve_tau 0]
    have hx : potentialAn (m + 1) E (D.A 0) v ≠ ⊤ :=
      ne_top_of_le_ne_top EReal.zero_ne_top (potentialAn_nonpos (m + 1) E _ v)
    refine add_coe_le_of_forall_lt hx fun r hr => le_trans (add_le_add ?_ le_rfl) (hterm r hr)
    refine BerkovichPoint.potentialAn_mono_of_multiplierIdealAlgebraic (m + 1) E hA
      (native_of_isThetaPSH (D.isThetaPSH 0))
      (native_of_isThetaPSH (isThetaPSH_simplexValue D r hr.le)) (fun x => ?_) v
    rw [← simplexValue_first D x]
    exact simplexValue_antitone D x hr.le

omit [MeasurableSpace (SchemeComplexPoint f)] [BorelSpace (SchemeComplexPoint f)]
  [CompactSpace (SchemeComplexPoint f)] [ConnectedSpace (SchemeComplexPoint f)] in
/-- The Lelong-number estimate of the proof of `lma:psieqpsiprimeondiv`: for `s ≤ τ_0` there are
feasible weights `w` (`w_i ≥ 0`, `Σ w_i = 1`, `Σ w_i τ_i ≥ s`) with
`ν(A'_s, E) ≥ Σ_i w_i ν(A_i, E)`. -/
theorem exists_weights_presentationReader_simplexValue_ge (D : PiecewiseLinearData θ)
    {s : ℝ} (hs : s ≤ D.τ 0) (p : PrimePresentation (m + 1) (SchemeComplexPoint f)) :
    ∃ w ∈ feasibleWeights D s,
      ∑ i, ENNReal.ofReal (w i) * presentationReader (D.A i) p ≤
        presentationReader (simplexValue D s) p := by
  classical
  let : Fintype (VertexIndex D.τ s) := Fintype.ofFinite _
  have hne : (Finset.univ : Finset (VertexIndex D.τ s)).Nonempty :=
    ⟨Sum.inl ⟨0, hs⟩, Finset.mem_univ _⟩
  have he : simplexValue D s = fun x => Finset.univ.sup' hne
      (fun v : VertexIndex D.τ s => weightedValue D (vertexVector D.τ s v) x) := by
    funext x
    rw [simplexValue_eq_vertex_iSup]
    apply le_antisymm
    · exact iSup_le (fun v => Finset.le_sup'
        (fun v : VertexIndex D.τ s => weightedValue D (vertexVector D.τ s v) x)
        (Finset.mem_univ v))
    · exact Finset.sup'_le _ _ (fun v _ => le_iSup
        (fun v : VertexIndex D.τ s => weightedValue D (vertexVector D.τ s v) x) v)
  obtain ⟨v, -, hv⟩ := Finset.exists_mem_eq_inf' hne
    (fun v : VertexIndex D.τ s => presentationReader (weightedValue D (vertexVector D.τ s v)) p)
  have hfeas := vertexVector_feasible D s v
  refine ⟨vertexVector D.τ s v, hfeas, ?_⟩
  have h1 := presentationReader_weighted_ge (Finset.univ : Finset (Fin (D.N + 1)))
    (vertexVector D.τ s v) (fun i => (hfeas.1 i).1) D.A D.isThetaPSH p
  have h2 := presentationReader_finset_sup'_ge Finset.univ hne
    (fun v : VertexIndex D.τ s => weightedValue D (vertexVector D.τ s v)) p
  rw [hv] at h2
  rw [he]
  exact h1.trans h2

variable [IsIntegral X]

/-- **Source `lma:psieqpsiprimeondiv`, `eq:psieqsiprime`: `A^An = Ã^An` on `X^Div`** (the
divisorial valuations `t ord_E` and the trivial valuation), conditional on
`MultiplierIdealAlgebraic` and on the algebraic half `AlgebraicPrimesRealized` of the dictionary
of prime divisors. -/
theorem curveAn_eq_naPotentialAnAt_hull (hA : MultiplierIdealAlgebraic f (m + 1) E)
    (halg : AlgebraicPrimesRealized (f := f) m E) (D : PiecewiseLinearData θ)
    (ω : SourceKahlerForm (m + 1) (SchemeComplexPoint f)) (v : sourceDivisorialSet f) :
    D.curveAn (m + 1) E v = naPotentialAnAt (m + 1) E (hullNAPotential D) ω v := by
  refine le_antisymm (curveAn_le_naPotentialAnAt_hull hA D ω v) ?_
  rw [naPotentialAnAt_hull_eq]
  obtain ⟨v, hv⟩ := v
  rcases hv with rfl | ⟨Dv, t, ht, rfl⟩
  · -- the trivial valuation: both sides are `τ_0`
    have hcurve : ((D.τ 0 : ℝ) : EReal) ≤ D.curveAn (m + 1) E (BerkovichPoint.trivial f) := by
      have h := D.le_curveAn (m + 1) E (BerkovichPoint.trivial f) 0
      rwa [potentialAn_trivial hA (native_of_isThetaPSH (D.isThetaPSH 0)), zero_add] at h
    refine iSup_le fun τ => le_trans ?_ hcurve
    calc potentialAn (m + 1) E (simplexValue D τ) (BerkovichPoint.trivial f) + ((τ : ℝ) : EReal)
        ≤ 0 + ((τ : ℝ) : EReal) := add_le_add (potentialAn_nonpos (m + 1) E _ _) le_rfl
      _ ≤ ((D.τ 0 : ℝ) : EReal) := by
          rw [zero_add]
          exact EReal.coe_le_coe_iff.mpr (le_of_lt τ.2)
  · -- a divisorial valuation `t ord_E`, with an analytic realization `p` of `E`
    obtain ⟨p, hDp⟩ := halg Dv
    refine iSup_le fun τ => ?_
    have hτ : (τ : ℝ) ≤ D.τ 0 := le_of_lt τ.2
    obtain ⟨w, hw, hwν⟩ := exists_weights_presentationReader_simplexValue_ge D hτ p
    -- finite Lelong numbers
    set a : Fin (D.N + 1) → ℝ := fun i => (presentationReader (D.A i) p).toReal with ha
    have hAfin : ∀ i, presentationReader (D.A i) p ≠ ⊤ := fun i =>
      presentationReader_ne_top (D.isThetaPSH i) p
    have hBfin : presentationReader (simplexValue D τ) p ≠ ⊤ :=
      presentationReader_ne_top (isThetaPSH_simplexValue D τ hτ) p
    have hsumle : ∑ i, w i * a i ≤ (presentationReader (simplexValue D τ) p).toReal := by
      have hsum : ∑ i, ENNReal.ofReal (w i) * presentationReader (D.A i) p =
          ENNReal.ofReal (∑ i, w i * a i) := by
        rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (hw.1 i).1 ENNReal.toReal_nonneg)]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [ENNReal.ofReal_mul (hw.1 i).1, ENNReal.ofReal_toReal (hAfin i)]
      rw [hsum] at hwν
      have := ENNReal.toReal_mono hBfin hwν
      rwa [ENNReal.toReal_ofReal (Finset.sum_nonneg fun i _ =>
        mul_nonneg (hw.1 i).1 ENNReal.toReal_nonneg)] at this
    have ht' : (0 : ℝ) < (t : ℝ) := ht
    -- the index maximizing `τ_i - t ν(A_i, E)`
    obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ
      (fun i : Fin (D.N + 1) => D.τ i - (t : ℝ) * a i) Finset.univ_nonempty
    have hreal : (τ : ℝ) - (t : ℝ) * (presentationReader (simplexValue D τ) p).toReal ≤
        D.τ j - (t : ℝ) * a j := by
      have hw1 : ∑ i, w i = 1 := hw.2.1
      have hwτ : (τ : ℝ) ≤ ∑ i, w i * D.τ i := hw.2.2
      have hconv : ∑ i, w i * (D.τ i - (t : ℝ) * a i) ≤ D.τ j - (t : ℝ) * a j := by
        calc ∑ i, w i * (D.τ i - (t : ℝ) * a i)
            ≤ ∑ i, w i * (D.τ j - (t : ℝ) * a j) :=
              Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hj i hi) (hw.1 i).1
          _ = D.τ j - (t : ℝ) * a j := by rw [← Finset.sum_mul, hw1, one_mul]
      have hexp : ∑ i, w i * (D.τ i - (t : ℝ) * a i) =
          ∑ i, w i * D.τ i - (t : ℝ) * ∑ i, w i * a i := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring
      nlinarith [mul_le_mul_of_nonneg_left hsumle ht'.le]
    have hB := potentialAn_ordVal_eq_coe hA hDp
      (native_of_isThetaPSH (isThetaPSH_simplexValue D τ hτ)) hBfin t ht'
    have hAj := potentialAn_ordVal_eq_coe hA hDp (native_of_isThetaPSH (D.isThetaPSH j))
      (hAfin j) t ht'
    have hle := D.le_curveAn (m + 1) E (Dv.ordVal f t ht') j
    rw [hAj] at hle
    rw [hB]
    refine le_trans ?_ hle
    rw [← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff]
    linarith

end SGPT.NAPotential.Berkovich

end
