import SGPT.Okounkov.OkoNSInfty
import SGPT.Okounkov.SourceCurrentValuationWhole
import SGPT.Okounkov.ValuativeTestCurve

/-!
# Rescaling and real concavity of partial Okounkov bodies

Lane QW-OKO, blueprint `claude-qw-oko.tex`. Source: chapter *The theory of Okounkov bodies*,
subsection *Basic properties of partial Okounkov bodies*: `thm:concOko` and `prop:res`.

## Transcendental bodies

For a smooth flag `Y•` on a connected compact Kähler manifold, `θ` a closed real `(1,1)`-form and
`φ ∈ PSH(X, θ)`, `Δ(θ, φ)` denotes the partial Okounkov body `Δ_{Y•}(θ + dd^c φ)` of
`def:generalPOB` (`PartialBody.generalPartialBody`).

* `real_smul_mem_generalPartialBody` (**real homogeneity**): `s Δ(θ, φ) ⊆ Δ(sθ, sφ)` for every
  real `s > 0`. For rational `q ∈ (0, s)`, `q Δ(θ, φ) ⊆ Δ(qθ, qφ)`
  (`Valuative.smul_generalPartialBody_subset`), the valuation `ν((s - q)φ) = (s - q) ν(φ)` lies in
  `Δ((s - q)θ, (s - q)φ)` (`cor:valuationcurrentinPOB`,
  `SourceCurrentValuation.flagValuation_mem_generalPartialBody`), and superadditivity
  (`thm:pobmain` (6), `PartialBody.generalPartialBody_add_subset`) gives
  `q x + (s - q) ν(φ) ∈ Δ(sθ, sφ)` for `x ∈ Δ(θ, φ)`; let `q → s` and use that the body is closed.
* `convexComb_mem_generalPartialBody_real` (**real concavity**): for real `t ∈ (0, 1)`,
  `t Δ(θ, φ) + (1 - t) Δ(θ, ψ) ⊆ Δ(θ, tφ + (1 - t)ψ)` (homogeneity and superadditivity).

## Algebraic bodies

Setting of lanes OKO-A / DXMAIN / H0-GAGA3 / OKO-NS: `X` an integral smooth projective complex
scheme of dimension `n = m + 1` carrying a smooth flag `Y•` (`ν = ν_{Y•}`), `L` a line bundle with
atlas `a` and smooth metric `H`, `θ = c₁(L, H)`; a plurisubharmonic metric `h = H e^{-φ}` is its
weight `φ ∈ PSH(X, θ)`. The algebraic partial Okounkov body `Δ_ν(θ, φ) = Δ(Γ(θ, φ))` is
`partialOkounkovBody` relative to a cube cone `C([0, C]ⁿ)`; it is the book's body for all large
`C` (`SGPT.GAGA.H0L.exists_partialOkounkovBody_eq`).

* **`thm:concOko`** (`convexComb_partialOkounkovBody_subset`): for `φ, ψ ∈ PSH(X, θ)_{>0}` and
  every real `t ∈ (0, 1)`, `tφ + (1 - t)ψ ∈ PSH(X, θ)_{>0}` and
  `t Δ_ν(θ, φ) + (1 - t) Δ_ν(θ, ψ) ⊆ Δ_ν(θ, tφ + (1 - t)ψ)`.
* **`prop:res`** (`partialOkounkovBody_tensorPower_eq_smul`): for every integer `p > 0`,
  `Δ_ν(pθ, pφ) = p Δ_ν(θ, φ)`, where `Δ_ν(pθ, pφ)` is the body of `(L^p, h^p)`: the tensor power
  `L^p` with the power atlas, the metric `H^p` (curvature `c₁(L^p, H^p) = pθ`) and the weight `pφ`
  of `h^p`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

noncomputable section

universe u

namespace SGPT.Okounkov.QwOko

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set Filter MeasureTheory Metric
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending.ThetaPshConvexCombination
open SGPT.Okounkov SGPT.Okounkov.AlgPOB SGPT.LineBundle SGPT.PSH SGPT.AlmostSemigroup
open SGPT.Okounkov.TranscendentalCore SGPT.Okounkov.PartialBody
open scoped Topology ENNReal NNReal Pointwise

/-! ### Real homogeneity and real concavity of the transcendental bodies -/

section Transcendental

variable {m : ℕ} {F : OriginalFlagGeometry.{u} (m + 1)}

/-- `q x + (s - q) x = s x` in `EReal` for real `0 ≤ q ≤ s`. -/
theorem ereal_coe_mul_add_coe_sub_mul {q s : ℝ} (hq : 0 ≤ q) (hqs : q ≤ s) (x : EReal) :
    (q : EReal) * x + ((s - q : ℝ) : EReal) * x = (s : EReal) * x := by
  rw [← EReal.right_distrib_of_nonneg (EReal.coe_nonneg.mpr hq)
    (EReal.coe_nonneg.mpr (sub_nonneg.mpr hqs)), ← EReal.coe_add, add_sub_cancel]

/-- **Real homogeneity** `s Δ(θ, φ) ⊆ Δ(sθ, sφ)` for every real `s > 0` (`def:generalPOB`):
rational homogeneity, the valuation point `ν((s - q)φ) ∈ Δ((s - q)θ, (s - q)φ)`,
superadditivity and closedness. -/
theorem real_smul_mem_generalPartialBody {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    {φ : F.carrier → EReal} (hφ : IsThetaPshPotential θ.val φ) {s : ℝ} (hs : 0 < s)
    {x : Fin (m + 1) → ℝ} (hx : x ∈ generalPartialBody F θ φ) :
    s • x ∈ generalPartialBody F (s • θ) (fun y => (s : EReal) * φ y) := by
  set ν : Fin (m + 1) → ℝ := flagValuation F φ with hνdef
  -- the points `q x + (s - q) ν(φ)`, `q ∈ ℚ ∩ (0, s)`
  have hmem : ∀ q : ℚ, 0 < q → (q : ℝ) < s →
      (q : ℝ) • x + (s - q) • ν ∈ generalPartialBody F (s • θ) (fun y => (s : EReal) * φ y) := by
    intro q hq0 hqs
    have hq0R : (0 : ℝ) < q := by exact_mod_cast hq0
    have hr : (0 : ℝ) ≤ s - q := sub_nonneg.mpr hqs.le
    have h1 := Valuative.smul_generalPartialBody_subset hφ hq0 ⟨x, hx, rfl⟩
    have hψ := isThetaPshPotential_nonneg_smul hφ hr
    have h2 := SourceCurrentValuation.flagValuation_mem_generalPartialBody F hψ
    rw [flagValuation_smul hφ hr] at h2
    have h3 := generalPartialBody_add_subset (isThetaPshPotential_nonneg_smul hφ hq0R.le) hψ
      ⟨_, h1, _, h2, rfl⟩
    have hform : (q : ℝ) • θ + (s - q) • θ = s • θ := by
      rw [← add_smul, add_sub_cancel]
    have hfun : (fun y => ((q : ℝ) : EReal) * φ y + ((s - q : ℝ) : EReal) * φ y) =
        fun y => (s : EReal) * φ y := by
      funext y
      exact ereal_coe_mul_add_coe_sub_mul hq0R.le hqs.le (φ y)
    rw [hform, hfun] at h3
    exact h3
  rw [← (isClosed_generalPartialBody (s • θ) _).closure_eq, Metric.mem_closure_iff]
  intro ε hε
  set D : ℝ := dist x ν + 1 with hD
  have hDpos : 0 < D := by positivity
  have hδ : 0 < min (ε / D) s := lt_min (div_pos hε hDpos) hs
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (sub_lt_self s hδ)
  have hq0 : (0 : ℝ) < q := by
    have := min_le_right (ε / D) s
    linarith
  refine ⟨_, hmem q (by exact_mod_cast hq0) hq2, ?_⟩
  have heq : s • x - ((q : ℝ) • x + (s - q) • ν) = (s - q) • (x - ν) := by module
  rw [dist_eq_norm, heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith),
    ← dist_eq_norm]
  have hsq : s - q < ε / D := by
    have := min_le_left (ε / D) s
    linarith
  calc (s - q) * dist x ν ≤ (s - q) * D := by
        apply mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    _ < ε / D * D := by apply mul_lt_mul_of_pos_right hsq hDpos
    _ = ε := div_mul_cancel₀ ε hDpos.ne'

/-- **Real concavity of partial Okounkov bodies** (`thm:concOko` for transcendental bodies): for
`φ, ψ ∈ PSH(X, θ)` and real `t ∈ (0, 1)`, `t Δ(θ, φ) + (1 - t) Δ(θ, ψ) ⊆ Δ(θ, tφ + (1 - t)ψ)`. -/
theorem convexComb_mem_generalPartialBody_real {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    {φ ψ : F.carrier → EReal} (hφ : IsThetaPshPotential θ.val φ)
    (hψ : IsThetaPshPotential θ.val ψ) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    {x y : Fin (m + 1) → ℝ} (hx : x ∈ generalPartialBody F θ φ)
    (hy : y ∈ generalPartialBody F θ ψ) :
    t • x + (1 - t) • y ∈ generalPartialBody F θ (convexComb t φ ψ) := by
  have hb : 0 < 1 - t := sub_pos.mpr ht1
  have h1 := real_smul_mem_generalPartialBody hφ ht0 hx
  have h2 := real_smul_mem_generalPartialBody hψ hb hy
  have h3 := generalPartialBody_add_subset (isThetaPshPotential_nonneg_smul hφ ht0.le)
    (isThetaPshPotential_nonneg_smul hψ hb.le) ⟨_, h1, _, h2, rfl⟩
  have hform : t • θ + (1 - t) • θ = θ := by rw [← add_smul, add_sub_cancel, one_smul]
  rw [hform] at h3
  exact h3

/-- Set form of `convexComb_mem_generalPartialBody_real`. -/
theorem convexComb_generalPartialBody_subset_real {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    {φ ψ : F.carrier → EReal} (hφ : IsThetaPshPotential θ.val φ)
    (hψ : IsThetaPshPotential θ.val ψ) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    t • generalPartialBody F θ φ + (1 - t) • generalPartialBody F θ ψ ⊆
      generalPartialBody F θ (convexComb t φ ψ) := by
  rintro _ ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩
  exact convexComb_mem_generalPartialBody_real hφ hψ ht0 ht1 hx hy

end Transcendental

/-! ### The algebraic setting -/

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (E : ClosedProjectiveEmbedding f)
  [IsIntegral X] {m : ℕ} [SmoothOfRelativeDimension (m + 1) f]

local instance qwOkoTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance qwOkoCharts : ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (m + 1)
local instance qwOkoManifold [IsSeparated f] [QuasiCompact f] :
    IsComplexManifold (m + 1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (m + 1)

variable (Y : Fin (m + 1 + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y)
  {L : X.Modules} (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f (m + 1) E L)

/-! ### `thm:concOko` -/

/-- **Source `thm:concOko`** (flag valuations): for `φ, ψ ∈ PSH(X, θ)_{>0}` and every real
`t ∈ (0, 1)`, the potential `tφ + (1 - t)ψ` lies in `PSH(X, θ)_{>0}` and
`t Δ_ν(θ, φ) + (1 - t) Δ_ν(θ, ψ) ⊆ Δ_ν(θ, tφ + (1 - t)ψ)` (for all large cube cones). -/
theorem convexComb_partialOkounkovBody_subset [Nonempty (SchemeComplexPoint f)] :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ C : ℝ, C₀ ≤ C → ∀ φ ψ : SchemeComplexPoint f → EReal,
      (letI := E.isSeparated; letI := E.quasiCompact;
        IsThetaPshPotential (H.curvature a).val φ) →
      (letI := E.isSeparated; letI := E.quasiCompact;
        IsThetaPshPotential (H.curvature a).val ψ) →
      0 < volume.real (PartialBody.generalPartialBody
        (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) (H.curvature a) φ) →
      0 < volume.real (PartialBody.generalPartialBody
        (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) (H.curvature a) ψ) →
      ∀ t : ℝ, 0 < t → t < 1 →
      (letI := E.isSeparated; letI := E.quasiCompact;
        IsThetaPshPotential (H.curvature a).val (convexComb t φ ψ)) ∧
      0 < volume.real (PartialBody.generalPartialBody
        (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) (H.curvature a)
          (convexComb t φ ψ)) ∧
      t • partialOkounkovBody f (m + 1) E Y hY (cubeCone C) a φ +
          (1 - t) • partialOkounkovBody f (m + 1) E Y hY (cubeCone C) a ψ ⊆
        partialOkounkovBody f (m + 1) E Y hY (cubeCone C) a (convexComb t φ ψ) := by
  let := E.isSeparated
  let := E.quasiCompact
  obtain ⟨C₀, hC₀, hC⟩ := SGPT.GAGA.H0L.exists_partialOkounkovBody_eq f E Y hY a H
  refine ⟨C₀, hC₀, fun C hC' φ ψ hφ hψ hpφ hpψ t ht0 ht1 => ?_⟩
  set Fg := schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY
  have hχ : IsThetaPshPotential (H.curvature a).val (convexComb t φ ψ) :=
    isThetaPshPotential_convexComb hφ hψ ht0 ht1
  have hsub := convexComb_generalPartialBody_subset_real (F := Fg) hφ hψ ht0 ht1
  have htφ : 0 < volume.real (t • PartialBody.generalPartialBody Fg (H.curvature a) φ) := by
    rw [OkoNS.volume_real_smul_set]
    exact mul_pos (abs_pos.mpr (pow_ne_zero _ ht0.ne')) hpφ
  have hpχ : 0 < volume.real (PartialBody.generalPartialBody Fg (H.curvature a)
      (convexComb t φ ψ)) :=
    OkoNS.volume_real_pos_of_add_subset
      (convex_isCompact_generalPartialBody (F := Fg) hχ).2 htφ
      ((nonempty_generalPartialBody (F := Fg) hψ).smul_set) hsub
  refine ⟨hχ, hpχ, ?_⟩
  rw [hC C hC' φ hφ hpφ, hC C hC' ψ hψ hpψ, hC C hC' _ hχ hpχ,
    Valuative.euclideanImage_convexComb]
  exact image_mono hsub

/-! ### `prop:res` -/

/-- **Source `prop:res`** (flag valuations): for every integer `p > 0`,
`Δ_ν(pθ, pφ) = p Δ_ν(θ, φ)` for `φ ∈ PSH(X, θ)_{>0}`: `Δ_ν(pθ, pφ)` is the partial Okounkov body
of `(L^p, h^p)`, i.e. of the tensor power `L^p` with its power atlas and the metric `H^p`
(curvature `c₁(L^p, H^p) = pθ`), and the weight `pφ` of `h^p` (which is `c₁(L^p, H^p)`-psh, with
positive volume); the equality holds for all large cube cones. -/
theorem partialOkounkovBody_tensorPower_eq_smul [Nonempty (SchemeComplexPoint f)]
    (p : ℕ) (hp : 0 < p) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ C : ℝ, C₀ ≤ C → ∀ φ : SchemeComplexPoint f → EReal,
      (letI := E.isSeparated; letI := E.quasiCompact;
        IsThetaPshPotential (H.curvature a).val φ) →
      0 < volume.real (PartialBody.generalPartialBody
        (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) (H.curvature a) φ) →
      (letI := E.isSeparated; letI := E.quasiCompact;
        IsThetaPshPotential ((H.tensorPower a p).curvature (a.tensorPower p)).val
          (fun x => ((p : ℝ) : EReal) * φ x)) ∧
      0 < volume.real (PartialBody.generalPartialBody
        (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY)
        ((H.tensorPower a p).curvature (a.tensorPower p)) (fun x => ((p : ℝ) : EReal) * φ x)) ∧
      partialOkounkovBody f (m + 1) E Y hY (cubeCone C) (a.tensorPower p)
          (fun x => ((p : ℝ) : EReal) * φ x) =
        (p : ℝ) • partialOkounkovBody f (m + 1) E Y hY (cubeCone C) a φ := by
  let := E.isSeparated
  let := E.quasiCompact
  obtain ⟨C₁, hC₁, h₁⟩ := SGPT.GAGA.H0L.exists_partialOkounkovBody_eq f E Y hY a H
  obtain ⟨C₂, -, h₂⟩ := OkoNS.inv_smul_partialOkounkovBody_eq_of_geometricallyEq f E Y hY
    (a.tensorPower p) (H.tensorPower a p)
  refine ⟨max C₁ C₂, le_max_of_le_left hC₁, fun C hC φ hφ hpos => ?_⟩
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hpQ : (0 : ℚ) < p := by exact_mod_cast hp
  have hgeo := H.curvature_tensorPower a p
  obtain ⟨hpφ, hbody⟩ := h₂ C (le_of_max_le_right hC) p hp (H.curvature a) φ hgeo hφ hpos
  -- `Δ(pθ, pφ) = p Δ(θ, φ)` for the transcendental bodies, hence positivity of the volume
  have hqφ : IsThetaPshPotential ((p : ℝ) • H.curvature a).val
      (fun x => ((p : ℝ) : EReal) * φ x) := isThetaPshPotential_nonneg_smul hφ hpR.le
  have hhom : PartialBody.generalPartialBody
      (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY)
      ((H.tensorPower a p).curvature (a.tensorPower p)) (fun x => ((p : ℝ) : EReal) * φ x) =
      (p : ℝ) • PartialBody.generalPartialBody
        (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) (H.curvature a) φ := by
    rw [SourceSlice.generalPartialBody_eq_of_geometricallyEq _ hgeo hqφ]
    have h := SGPT.GAGA.OkoClose.generalPartialBody_rat_smul
      (F := schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) hφ hpQ
    rw [Rat.cast_natCast] at h
    exact h
  have hposp : 0 < volume.real (PartialBody.generalPartialBody
        (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY)
      ((H.tensorPower a p).curvature (a.tensorPower p)) (fun x => ((p : ℝ) : EReal) * φ x)) := by
    rw [hhom, OkoNS.volume_real_smul_set]
    exact mul_pos (abs_pos.mpr (pow_ne_zero _ hpR.ne')) hpos
  refine ⟨hpφ, hposp, ?_⟩
  rw [h₁ C (le_of_max_le_left hC) φ hφ hpos, ← hbody, smul_inv_smul₀ hpR.ne']

end SGPT.Okounkov.QwOko
