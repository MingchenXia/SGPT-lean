import SGPT.Okounkov.OkoNSTranscendental

/-!
# Superadditivity, perturbation and shrinking of algebraic partial Okounkov bodies

Lane OKO-NS, blueprint `claude-oko-ns.tex`. Source: chapter *The theory of Okounkov bodies*,
Section *Algebraic partial Okounkov bodies*.

Setting of lanes OKO-A / DXMAIN / H0-GAGA3 / OKO-CLOSE: `X` an integral smooth projective complex
scheme of dimension `n = m + 1` carrying a smooth flag `Y•` (the valuation is the flag valuation
`ν = ν_{Y•}`), `L` a line bundle with atlas `a` and smooth metric `H`, `θ = c₁(L, H)`; a
plurisubharmonic metric `h = H e^{-φ}` is its weight `φ ∈ PSH(X, θ)`. The algebraic partial
Okounkov body `Δ_ν(L, h) = Δ_ν(θ, φ) = Δ(Γ(θ, φ))` is `partialOkounkovBody` relative to a cube
cone `C([0, C]ⁿ)`; it is the book's body for all large `C`
(`SGPT.GAGA.H0L.exists_partialOkounkovBody_eq`).

* **`prop:suba`** (`partialOkounkovBody_add_subset_tensor`):
  `Δ_ν(L, h) + Δ_ν(L', h') ⊆ Δ_ν(L ⊗ L', h ⊗ h')`, for the tensor product `L ⊗ L'` with its
  pairwise tensor atlas, the product metric `H ⊗ H'` (curvature `θ + θ'`) and the weight
  `φ + φ'` of `h ⊗ h'`.
* `inv_smul_partialOkounkovBody_eq_of_geometricallyEq`: the definition `eq:DeltanuTalgebraic1`
  (`Δ_ν(S) = a⁻¹ Δ_ν(aS)` for a current `S` whose class is in `NS¹(X)_ℚ`) agrees with the partial
  body of the current `S` (`def:generalPOB`), for any line bundle `M` with
  `c₁(M, H_M) = a θ_S` (the version of `cor:transalgPOB` with chartwise equality of forms).
* **`prop:Deltapert`** (`partialOkounkovBody_perturb`): for an ample `A` with a metric `h_A` of
  Kähler curvature `ω` and rational `δ = p/q > 0`, the bodies
  `Δ_ν(θ + δω + dd^c φ) = q⁻¹ Δ_ν(L^q ⊗ A^p, h^q ⊗ h_A^p e^{-qφ})` are decreasing as `δ ↘ 0`
  and converge to `Δ_ν(θ_φ)` in the Hausdorff metric.
* **`lma:Hausconvbetato0`** (`tendsto_hausdorffDist_one_sub`): if `θ_φ` is a Kähler current, then
  `Δ_ν((1-β)θ, φ) = q⁻¹ Δ_ν(L^{q-p}, h^{q-p} e^{-qφ})` (`β = p/q`) converges to `Δ_ν(θ, φ)` as
  `ℚ ∋ β → 0+`.
* **`prop:Okounonlydepnum`**, first part (`lineBundleOkounkovBody_eq_of_chernClass_eq`): for big
  line bundles, `Δ_ν(L)` only depends on the real first Chern class `c₁(L) ∈ H^{1,1}(X, ℝ)`
  (it is the transcendental Okounkov body `Δ_{Y•}(c₁(L))`, `lineBundleOkounkovBody_eq_tradOkounkovBody`).
  That numerically equivalent line bundles have the same real Chern class is not formalized.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.Okounkov.OkoNS

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set Filter MeasureTheory Metric
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Okounkov SGPT.Okounkov.AlgPOB SGPT.LineBundle SGPT.PSH SGPT.AlmostSemigroup
open SGPT.Okounkov.TranscendentalCore
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open scoped Topology ENNReal NNReal Pointwise

/-! ### Euclidean copies -/

/-- Minkowski sums commute with the Euclidean copy. -/
theorem euclideanImage_add {k : ℕ} (A B : Set (Fin k → ℝ)) :
    TranscendentalMain.euclideanImage A + TranscendentalMain.euclideanImage B =
      TranscendentalMain.euclideanImage (A + B) := by
  simp only [euclideanImage_def]
  exact (Set.image_add (EuclideanSpace.equiv (Fin k) ℝ).symm).symm

/-- `q⁻¹ (q K) = K` for Euclidean copies (`q ≠ 0`). -/
theorem inv_smul_euclideanImage_smul {k : ℕ} {q : ℝ} (hq : q ≠ 0) (A : Set (Fin k → ℝ)) :
    q⁻¹ • TranscendentalMain.euclideanImage (q • A) = TranscendentalMain.euclideanImage A := by
  rw [TranscendentalMain.euclideanImage, TranscendentalMain.euclideanImage, ← Set.image_smul,
    Set.image_image, ← Set.image_smul, Set.image_image]
  congr 1
  funext x
  rw [map_smul, smul_smul, inv_mul_cancel₀ hq, one_smul]

/-- If `A + B ⊆ K` with `K` compact, `vol A > 0` and `B ≠ ∅`, then `vol K > 0`. -/
theorem volume_real_pos_of_add_subset {k : ℕ} {A B K : Set (Fin k → ℝ)} (hK : IsCompact K)
    (hA : 0 < volume.real A) (hB : B.Nonempty) (hsub : A + B ⊆ K) : 0 < volume.real K := by
  obtain ⟨b, hb⟩ := hB
  have h1 : (fun x => x + b) '' A ⊆ K := by
    rintro _ ⟨x, hx, rfl⟩
    exact hsub (add_mem_add hx hb)
  have h2 : volume ((fun x => x + b) '' A) = volume A := by
    rw [image_add_right, measure_preimage_add_right]
  have hA0 : volume A ≠ 0 := by
    intro h
    rw [measureReal_def, h, ENNReal.toReal_zero] at hA
    exact lt_irrefl _ hA
  have hAK : volume A ≤ volume K := by
    rw [← h2]
    exact measure_mono h1
  rw [measureReal_def]
  exact ENNReal.toReal_pos (lt_of_lt_of_le (pos_iff_ne_zero.mpr hA0) hAK).ne'
    hK.measure_lt_top.ne

/-- A Kähler current has a partial Okounkov body of positive volume. -/
theorem volume_real_generalPartialBody_pos_of_kahler {m : ℕ} (F : OriginalFlagGeometry (m + 1))
    {θ : ClosedRealOneOneForm (m + 1) F.carrier} {φ : F.carrier → EReal}
    (hφ : IsKahlerCurrentPotential θ φ) :
    0 < volume.real (PartialBody.generalPartialBody F θ φ) := by
  have hφθ := PartialBody.isThetaPshPotential_of_isKahlerCurrentPotential hφ
  have hcpt := (PartialBody.convex_isCompact_generalPartialBody (F := F) hφθ).2
  have hint := SourceLexmin.interior_generalPartialBody_nonempty_of_kahler F hφ
  have hne := MeasureTheory.Measure.measure_pos_of_nonempty_interior volume hint
  rw [measureReal_def]
  exact ENNReal.toReal_pos hne.ne' hcpt.measure_lt_top.ne

/-- A squeeze criterion for limits along `ℚ ∋ x → 0+`. -/
theorem tendsto_nhdsGT_of_forall_le {g : ℚ → ℝ} (hg0 : ∀ x, 0 ≤ g x)
    (h : ∀ ε : ℝ, 0 < ε → ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ x : ℚ, 0 < x → (x : ℝ) ≤ t₀ → g x ≤ ε) :
    Tendsto g (𝓝[>] 0) (𝓝 0) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨t₀, ht₀, ht⟩ := h (ε / 2) (by positivity)
  refine ⟨t₀, ht₀, fun {x} hx hdist => ?_⟩
  have hx0 : (0 : ℚ) < x := hx
  have hx0R : (0 : ℝ) < x := by exact_mod_cast hx0
  rw [Rat.dist_eq, Rat.cast_zero, sub_zero, abs_of_pos hx0R] at hdist
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hg0 x)]
  exact (ht x hx0 hdist.le).trans_lt (by linarith)

/-! ### The algebraic setting -/

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (E : ClosedProjectiveEmbedding f)
  [IsIntegral X] {m : ℕ} [SmoothOfRelativeDimension (m + 1) f]

local instance okoNSTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance okoNSCharts : ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (m + 1)
local instance okoNSManifold [IsSeparated f] [QuasiCompact f] :
    IsComplexManifold (m + 1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (m + 1)

variable (Y : Fin (m + 1 + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y)

/-! ### `prop:suba` -/

/-- **Source `prop:suba`** (flag valuations): for Hermitian line bundles `(L, h)`, `(L', h')`
with `h = H e^{-φ}`, `h' = H' e^{-φ'}` (`φ ∈ PSH(X, θ)`, `φ' ∈ PSH(X, θ')`, `θ = c₁(L, H)`,
`θ' = c₁(L', H')`) of positive volume, the weight `φ + φ'` of `h ⊗ h'` is psh for the curvature
`c₁(L ⊗ L', H ⊗ H') = θ + θ'` of the product metric, and
`Δ_ν(L, h) + Δ_ν(L', h') ⊆ Δ_ν(L ⊗ L', h ⊗ h')` (for all large cube cones). -/
theorem partialOkounkovBody_add_subset_tensor [Nonempty (SchemeComplexPoint f)]
    {L L' : X.Modules} (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f (m + 1) E L)
    (a' : LineBundleAtlas L') (H' : SchemeLineBundleMetric f (m + 1) E L') :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ C : ℝ, C₀ ≤ C → ∀ φ φ' : SchemeComplexPoint f → EReal,
      (letI := E.isSeparated; letI := E.quasiCompact;
        IsThetaPshPotential (H.curvature a).val φ) →
      (letI := E.isSeparated; letI := E.quasiCompact;
        IsThetaPshPotential (H'.curvature a').val φ') →
      0 < volume.real (PartialBody.generalPartialBody
        (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) (H.curvature a) φ) →
      0 < volume.real (PartialBody.generalPartialBody
        (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) (H'.curvature a') φ') →
      (letI := E.isSeparated; letI := E.quasiCompact;
        IsThetaPshPotential ((H.tensorProduct H' a a').curvature (pairwiseTensorAtlas a a')).val
          (fun x => φ x + φ' x)) ∧
      partialOkounkovBody f (m + 1) E Y hY (cubeCone C) a φ +
          partialOkounkovBody f (m + 1) E Y hY (cubeCone C) a' φ' ⊆
        partialOkounkovBody f (m + 1) E Y hY (cubeCone C) (pairwiseTensorAtlas a a')
          (fun x => φ x + φ' x) := by
  let := E.isSeparated
  let := E.quasiCompact
  obtain ⟨C₁, hC₁, h₁⟩ := SGPT.GAGA.H0L.exists_partialOkounkovBody_eq f E Y hY a H
  obtain ⟨C₂, -, h₂⟩ := SGPT.GAGA.H0L.exists_partialOkounkovBody_eq f E Y hY a' H'
  obtain ⟨C₃, -, h₃⟩ := SGPT.GAGA.H0L.exists_partialOkounkovBody_eq f E Y hY
    (pairwiseTensorAtlas a a') (H.tensorProduct H' a a')
  refine ⟨max C₁ (max C₂ C₃), le_max_of_le_left hC₁, fun C hC φ φ' hφ hφ' hp hp' => ?_⟩
  have hgeo := H.curvature_tensorProduct H' a a' (pairwiseTensorAtlas a a')
  have hsum := isThetaPshPotential_add_from_positive_sum hφ hφ'
  have hsum' := (hgeo.thetaPshPotential_iff (fun x => φ x + φ' x)).mpr hsum
  have hbody := SourceSlice.generalPartialBody_eq_of_geometricallyEq
    (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) hgeo hsum
  have hadd := PartialBody.generalPartialBody_add_subset
    (F := schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) hφ hφ'
  have hp3 : 0 < volume.real (PartialBody.generalPartialBody
      (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY)
      ((H.tensorProduct H' a a').curvature (pairwiseTensorAtlas a a')) (fun x => φ x + φ' x)) := by
    erw [hbody]
    exact volume_real_pos_of_add_subset
      (PartialBody.convex_isCompact_generalPartialBody
        (F := schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) hsum).2 hp
      (PartialBody.nonempty_generalPartialBody
        (F := schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) hφ') hadd
  refine ⟨hsum', ?_⟩
  have hC1 : C₁ ≤ C := le_of_max_le_left hC
  have hC2 : C₂ ≤ C := (le_max_left _ _).trans ((le_max_right _ _).trans hC)
  have hC3 : C₃ ≤ C := (le_max_right _ _).trans ((le_max_right _ _).trans hC)
  rw [h₁ C hC1 φ hφ hp, h₂ C hC2 φ' hφ' hp', h₃ C hC3 _ hsum' hp3, hbody, euclideanImage_add]
  exact image_mono hadd

/-! ### `eq:DeltanuTalgebraic1` with chartwise equality of forms -/

/-- **The definition `eq:DeltanuTalgebraic1` (`cor:transalgPOB`, `ℚ`-classes)**: let `M` be a
line bundle with atlas `b` and smooth metric `H_M`, `q > 0` an integer and `S = θ' + dd^c φ` a
current (`φ ∈ PSH(X, θ')`, `vol > 0`) with `c₁(M, H_M) = q θ'` (chartwise). Then `qφ` is
`c₁(M, H_M)`-psh and `q⁻¹ Δ_ν(M, H_M e^{-qφ}) = Δ_{Y•}(S)` (for all large cube cones), i.e.
`q⁻¹ Δ_ν(qS)` is the partial Okounkov body of the current `S` (`def:generalPOB`); in particular it
does not depend on the choice of `(M, q)`. -/
theorem inv_smul_partialOkounkovBody_eq_of_geometricallyEq [Nonempty (SchemeComplexPoint f)]
    {M : X.Modules} (b : LineBundleAtlas M) (HM : SchemeLineBundleMetric f (m + 1) E M) :
    letI := E.isSeparated
    letI := E.quasiCompact
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ C : ℝ, C₀ ≤ C → ∀ q : ℕ, 0 < q →
      ∀ (θ : ClosedRealOneOneForm (m + 1) (SchemeComplexPoint f))
        (φ : SchemeComplexPoint f → EReal),
      (HM.curvature b).val.GeometricallyEq ((q : ℝ) • θ).val → IsThetaPshPotential θ.val φ →
      0 < volume.real (PartialBody.generalPartialBody
        (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) θ φ) →
      IsThetaPshPotential (HM.curvature b).val (fun x => ((q : ℝ) : EReal) * φ x) ∧
      ((q : ℝ))⁻¹ • partialOkounkovBody f (m + 1) E Y hY (cubeCone C) b
          (fun x => ((q : ℝ) : EReal) * φ x) =
        TranscendentalMain.euclideanImage (PartialBody.generalPartialBody
          (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) θ φ) := by
  let := E.isSeparated
  let := E.quasiCompact
  obtain ⟨C₀, hC₀, hC⟩ := SGPT.GAGA.H0L.exists_partialOkounkovBody_eq f E Y hY b HM
  refine ⟨C₀, hC₀, fun C hC' q hq θ φ hgeo hφ hpos => ?_⟩
  have hqQ : (0 : ℚ) < q := by exact_mod_cast hq
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hcast : (((q : ℚ)) : ℝ) = (q : ℝ) := Rat.cast_natCast q
  have hqφ : IsThetaPshPotential ((q : ℝ) • θ).val (fun x => ((q : ℝ) : EReal) * φ x) :=
    isThetaPshPotential_nonneg_smul hφ hqR.le
  have hqφ' := (hgeo.thetaPshPotential_iff _).mpr hqφ
  have hhom : PartialBody.generalPartialBody
      (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) (HM.curvature b)
      (fun x => ((q : ℝ) : EReal) * φ x) =
      (q : ℝ) • PartialBody.generalPartialBody
        (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) θ φ := by
    rw [SourceSlice.generalPartialBody_eq_of_geometricallyEq _ hgeo hqφ]
    have h := SGPT.GAGA.OkoClose.generalPartialBody_rat_smul
      (F := schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) hφ hqQ
    rw [hcast] at h
    exact h
  have hposq : 0 < volume.real (PartialBody.generalPartialBody
      (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) (HM.curvature b)
      (fun x => ((q : ℝ) : EReal) * φ x)) := by
    rw [hhom, Measure.real, MeasureTheory.Measure.addHaar_smul, Module.finrank_fin_fun,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _)]
    exact mul_pos (abs_pos.mpr (pow_ne_zero _ hqR.ne')) hpos
  refine ⟨hqφ', ?_⟩
  rw [hC C hC' _ hqφ' hposq]
  erw [hhom]
  exact inv_smul_euclideanImage_smul hqR.ne' _

/-! ### `prop:Deltapert` -/

/-- The atlas of `L^q ⊗ A^p` by tensor frames. -/
def perturbAtlas {L A : X.Modules} (a : LineBundleAtlas L) (aA : LineBundleAtlas A) (q p : ℕ) :
    LineBundleAtlas (bundleTensor (bundleTensorPower L q) (bundleTensorPower A p)) :=
  pairwiseTensorAtlas (a.tensorPower q) (aA.tensorPower p)

/-- The product metric `h^q ⊗ h_A^p` on `L^q ⊗ A^p`. -/
def perturbMetric {L A : X.Modules} (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f (m + 1) E L)
    (aA : LineBundleAtlas A) (HA : SchemeLineBundleMetric f (m + 1) E A) (q p : ℕ) :
    SchemeLineBundleMetric f (m + 1) E (bundleTensor (bundleTensorPower L q) (bundleTensorPower A p)) :=
  (H.tensorPower a q).tensorProduct (HA.tensorPower aA p) (a.tensorPower q) (aA.tensorPower p)

omit [IsIntegral X] in
/-- `c₁(L^q ⊗ A^p, h^q ⊗ h_A^p) = q c₁(L, h) + p c₁(A, h_A)`. -/
theorem curvature_perturbMetric {L A : X.Modules} (a : LineBundleAtlas L)
    (H : SchemeLineBundleMetric f (m + 1) E L) (aA : LineBundleAtlas A)
    (HA : SchemeLineBundleMetric f (m + 1) E A) (q p : ℕ) :
    letI := E.isSeparated
    letI := E.quasiCompact
    ((perturbMetric f E a H aA HA q p).curvature (perturbAtlas a aA q p)).val.GeometricallyEq
      ((q : ℝ) • H.curvature a + (p : ℝ) • HA.curvature aA).val := by
  let := E.isSeparated
  let := E.quasiCompact
  have h1 := (H.tensorPower a q).curvature_tensorProduct (HA.tensorPower aA p) (a.tensorPower q)
    (aA.tensorPower p) (perturbAtlas a aA q p)
  have h2 := H.curvature_tensorPower a q
  have h3 := HA.curvature_tensorPower aA p
  intro e u hu
  have e1 := h1 e hu
  have e2 := h2 e hu
  have e3 := h3 e hu
  change ((perturbMetric f E a H aA HA q p).curvature (perturbAtlas a aA q p)).val.coeff e u =
    ((q : ℝ) • H.curvature a + (p : ℝ) • HA.curvature aA).val.coeff e u
  refine e1.trans ?_
  rw [ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.coeff_add, e2, e3]

/-- **Source `prop:Deltapert`** (flag valuations). Let `A` be a line bundle with a smooth metric
`h_A` whose curvature `ω = c₁(A, h_A)` is a Kähler form, and `φ ∈ PSH(X, θ)` with
`vol θ_φ > 0`. For rational `δ = p/q > 0`, the body `Δ_ν(θ + δω + dd^c φ)` of
`eq:DeltanuTalgebraic1` is `q⁻¹ Δ_ν(L^q ⊗ A^p, h^q ⊗ h_A^p e^{-qφ})` (for all large cube cones);
it is the Euclidean copy of `Δ_{Y•}(θ + δω + dd^c φ)` for every representative `(q, p)` of `δ`
(first conjunct). These bodies are decreasing as `δ ↘ 0` (second conjunct) and
`Δ_ν(θ + δω + dd^c φ) → Δ_ν(θ_φ)` in the Hausdorff metric as `ℚ ∋ δ → 0+` (third conjunct). -/
theorem partialOkounkovBody_perturb [Nonempty (SchemeComplexPoint f)]
    {L A : X.Modules} (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f (m + 1) E L)
    (aA : LineBundleAtlas A) (HA : SchemeLineBundleMetric f (m + 1) E A)
    (hA : letI := E.isSeparated; letI := E.quasiCompact; (HA.curvature aA).val.IsKahler)
    {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val φ)
    (hpos : 0 < volume.real (PartialBody.generalPartialBody
      (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) (H.curvature a) φ)) :
    (∀ (δ : ℚ) (q p : ℕ), 0 < q → δ = (p : ℚ) / q →
      ∃ C₀ : ℝ, ∀ C : ℝ, C₀ ≤ C →
        ((q : ℝ))⁻¹ • partialOkounkovBody f (m + 1) E Y hY (cubeCone C) (perturbAtlas a aA q p)
            (fun x => ((q : ℝ) : EReal) * φ x) =
          TranscendentalMain.euclideanImage (PartialBody.generalPartialBody
            (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY)
            (H.curvature a + (δ : ℝ) • HA.curvature aA) φ)) ∧
    (∀ δ δ' : ℚ, 0 ≤ δ → δ ≤ δ' →
      TranscendentalMain.euclideanImage (PartialBody.generalPartialBody
          (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY)
          (H.curvature a + (δ : ℝ) • HA.curvature aA) φ) ⊆
        TranscendentalMain.euclideanImage (PartialBody.generalPartialBody
          (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY)
          (H.curvature a + (δ' : ℝ) • HA.curvature aA) φ)) ∧
    ∃ C₀ : ℝ, ∀ C : ℝ, C₀ ≤ C →
      Tendsto (fun δ : ℚ => hausdorffDist
          (TranscendentalMain.euclideanImage (PartialBody.generalPartialBody
            (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY)
            (H.curvature a + (δ : ℝ) • HA.curvature aA) φ))
          (partialOkounkovBody f (m + 1) E Y hY (cubeCone C) a φ))
        (𝓝[>] 0) (𝓝 0) := by
  let := E.isSeparated
  let := E.quasiCompact
  let κ : KahlerBackground (m + 1) (SchemeComplexPoint f) := ⟨HA.curvature aA, hA⟩
  have hω : (HA.curvature aA).val.IsSemipositive := κ.isSemipositive
  refine ⟨fun δ q p hq hδ => ?_, fun δ δ' hδ hδδ' => ?_, ?_⟩
  · -- the algebraic bodies of `eq:DeltanuTalgebraic1`
    obtain ⟨C₀, -, hC⟩ := inv_smul_partialOkounkovBody_eq_of_geometricallyEq f E Y hY
      (perturbAtlas a aA q p) (perturbMetric f E a H aA HA q p)
    refine ⟨C₀, fun C hC' => ?_⟩
    have hqR : (0 : ℝ) < q := by exact_mod_cast hq
    have hδR : (δ : ℝ) = (p : ℝ) / q := by rw [hδ]; push_cast; ring
    have hδ0 : (0 : ℝ) ≤ δ := by rw [hδR]; positivity
    have hφδ : IsThetaPshPotential (H.curvature a + (δ : ℝ) • HA.curvature aA).val φ := by
      refine TranscendentalBody.isThetaPshPotential_of_le hφ ?_
      rw [add_sub_cancel_left]
      exact KahlerDomination.isSemipositive_smul hω hδ0
    have hsub := generalPartialBody_subset_add_smul
      (F := schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) hφ hω le_rfl hδ0
    rw [zero_smul, add_zero] at hsub
    have hposδ : 0 < volume.real (PartialBody.generalPartialBody
        (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY)
        (H.curvature a + (δ : ℝ) • HA.curvature aA) φ) :=
      hpos.trans_le (measureReal_mono hsub
        ((PartialBody.convex_isCompact_generalPartialBody
          (F := schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) hφδ).2.measure_lt_top.ne))
    have hform : (q : ℝ) • H.curvature a + (p : ℝ) • HA.curvature aA =
        (q : ℝ) • (H.curvature a + (δ : ℝ) • HA.curvature aA) := by
      have hqp : (q : ℝ) * (δ : ℝ) = p := by rw [hδR]; field_simp
      rw [smul_add, smul_smul, hqp]
    have hgeo := curvature_perturbMetric f E a H aA HA q p
    rw [hform] at hgeo
    exact (hC C hC' q hq _ φ hgeo hφδ hposδ).2
  · -- decreasing
    exact image_mono (generalPartialBody_subset_add_smul hφ hω (by exact_mod_cast hδ)
      (by exact_mod_cast hδδ'))
  · -- Hausdorff convergence
    obtain ⟨C₀, -, hC⟩ := SGPT.GAGA.H0L.exists_partialOkounkovBody_eq f E Y hY a H
    refine ⟨C₀, fun C hC' => ?_⟩
    rw [hC C hC' φ hφ hpos]
    refine tendsto_nhdsGT_of_forall_le (fun _ => hausdorffDist_nonneg) fun ε hε => ?_
    obtain ⟨t₀, ht₀, ht⟩ := exists_hausdorffDist_add_kahler_le
      (F := schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) hφ κ hε
    exact ⟨t₀, ht₀, fun x hx hxt => ht x (by exact_mod_cast hx) hxt⟩

/-! ### `lma:Hausconvbetato0` -/

/-- **Source `lma:Hausconvbetato0`** (flag valuations): assume that `θ_φ` is a Kähler current.
There is `β₀ > 0` such that for rational `β = p/q ∈ (0, β₀)`, `φ ∈ PSH(X, (1 - β)θ)` and the body
`Δ_ν((1-β)θ, φ) = Δ_ν((1-β)θ + dd^c φ)` of `eq:DeltanuTalgebraic1`, namely
`q⁻¹ Δ_ν(L^{q-p}, h^{q-p} e^{-qφ})` (for all large cube cones), is the Euclidean copy of
`Δ_{Y•}((1-β)θ + dd^c φ)` for every representative `(q, p)` of `β`; and
`Δ_ν((1-β)θ, φ) → Δ_ν(θ, φ)` in the Hausdorff metric as `ℚ ∋ β → 0+`. -/
theorem tendsto_hausdorffDist_one_sub [Nonempty (SchemeComplexPoint f)]
    {L : X.Modules} (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f (m + 1) E L)
    {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsKahlerCurrentPotential (H.curvature a) φ) :
    ∃ β₀ : ℝ, 0 < β₀ ∧
    (∀ (β : ℚ) (q p : ℕ), 0 < q → β = (p : ℚ) / q → 0 < β → (β : ℝ) < β₀ →
      (letI := E.isSeparated; letI := E.quasiCompact;
        IsThetaPshPotential ((1 - (β : ℝ)) • H.curvature a).val φ) ∧
      ∃ C₀ : ℝ, ∀ C : ℝ, C₀ ≤ C →
        ((q : ℝ))⁻¹ • partialOkounkovBody f (m + 1) E Y hY (cubeCone C) (a.tensorPower (q - p))
            (fun x => ((q : ℝ) : EReal) * φ x) =
          TranscendentalMain.euclideanImage (PartialBody.generalPartialBody
            (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY)
            ((1 - (β : ℝ)) • H.curvature a) φ)) ∧
    ∃ C₀ : ℝ, ∀ C : ℝ, C₀ ≤ C →
      Tendsto (fun β : ℚ => hausdorffDist
          (TranscendentalMain.euclideanImage (PartialBody.generalPartialBody
            (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY)
            ((1 - (β : ℝ)) • H.curvature a) φ))
          (partialOkounkovBody f (m + 1) E Y hY (cubeCone C) a φ))
        (𝓝[>] 0) (𝓝 0) := by
  let := E.isSeparated
  let := E.quasiCompact
  obtain ⟨c, hcpos, K, hK, hbd⟩ := exists_hausdorffDist_one_sub_smul_le
    (F := schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) hφ
  have hcR : (0 : ℝ) < c := by exact_mod_cast hcpos
  have hcβ_of : ∀ β : ℚ, (β : ℝ) < 1 / c → (c : ℚ) * β < 1 := by
    intro β hβ
    have h : (c : ℝ) * β < 1 := by
      rw [lt_div_iff₀ hcR] at hβ
      linarith
    exact_mod_cast h
  refine ⟨1 / c, by positivity, fun β q p hq hβ hβ0 hββ₀ => ?_, ?_⟩
  · obtain ⟨hφβ, hposβ, -⟩ := hbd β hβ0 (hcβ_of β hββ₀)
    refine ⟨hφβ, ?_⟩
    obtain ⟨C₀, -, hC⟩ := inv_smul_partialOkounkovBody_eq_of_geometricallyEq f E Y hY
      (a.tensorPower (q - p)) (H.tensorPower a (q - p))
    refine ⟨C₀, fun C hC' => ?_⟩
    have hqR : (0 : ℝ) < q := by exact_mod_cast hq
    have hβR : (β : ℝ) = (p : ℝ) / q := by rw [hβ]; push_cast; ring
    have hβ1 : (β : ℝ) < 1 := by
      have : (1 : ℝ) / c ≤ 1 := by
        rw [div_le_one hcR]
        exact_mod_cast hcpos
      linarith
    have hpq : p ≤ q := by
      have : (p : ℝ) / q < 1 := hβR ▸ hβ1
      rw [div_lt_one hqR] at this
      exact_mod_cast this.le
    have hform : (((q - p : ℕ) : ℝ)) • H.curvature a = (q : ℝ) • ((1 - (β : ℝ)) • H.curvature a) := by
      rw [smul_smul, Nat.cast_sub hpq, hβR]
      congr 1
      field_simp
    have hgeo := H.curvature_tensorPower a (q - p)
    rw [hform] at hgeo
    exact (hC C hC' q hq _ φ hgeo hφβ hposβ).2
  · obtain ⟨C₀, -, hC⟩ := SGPT.GAGA.H0L.exists_partialOkounkovBody_eq f E Y hY a H
    have hφθ := PartialBody.isThetaPshPotential_of_isKahlerCurrentPotential hφ
    refine ⟨C₀, fun C hC' => ?_⟩
    rw [hC C hC' φ hφθ (volume_real_generalPartialBody_pos_of_kahler _ hφ)]
    refine tendsto_nhdsGT_of_forall_le (fun _ => hausdorffDist_nonneg) fun ε hε => ?_
    refine ⟨min (1 / (2 * c)) (ε / (K + 1)), lt_min (by positivity) (by positivity),
      fun x hx hxt => ?_⟩
    have hxR : (0 : ℝ) < x := by exact_mod_cast hx
    have hx1 : (x : ℝ) ≤ 1 / (2 * c) := hxt.trans (min_le_left _ _)
    have hx2 : (x : ℝ) ≤ ε / (K + 1) := hxt.trans (min_le_right _ _)
    have hcx : (x : ℝ) < 1 / c := by
      refine hx1.trans_lt ?_
      rw [div_lt_div_iff₀ (by positivity) hcR]
      linarith
    obtain ⟨-, -, hd⟩ := hbd x hx (hcβ_of x hcx)
    refine hd.trans ?_
    calc K * x ≤ (K + 1) * x := by nlinarith
      _ ≤ (K + 1) * (ε / (K + 1)) := by gcongr
      _ = ε := by field_simp

/-! ### `prop:Okounonlydepnum` -/

/-- For a big line bundle, the algebraic Okounkov body `Δ_ν(L)` is the transcendental Okounkov
body `Δ_{Y•}(c₁(L))` of its first Chern class (`def:tradOk`; `cor:transalgPOB` and
`thm:pobmain` (3)). -/
theorem lineBundleOkounkovBody_eq_tradOkounkovBody [Nonempty (SchemeComplexPoint f)]
    {L : X.Modules} (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f (m + 1) E L)
    (hbig : IsBig f L (m + 1)) :
    letI := E.isSeparated
    letI := E.quasiCompact
    lineBundleOkounkovBody f (m + 1) E Y hY a =
      tradOkounkovBody (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) (H.curvature a) := by
  let := E.isSeparated
  let := E.quasiCompact
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  set θ := H.curvature a with hθ
  have hV := isThetaPshPotential_thetaPshSupremum_of_isBig f E a H hbig
  have hbigC := SGPT.GAGA.OkoClose.isBigClass_of_isBig f E Y hY a H hbig
  have hbigB : SGPT.PSH.BookCurrent.IsBig (RealBottChern.ofRepresentative θ) :=
    (SGPT.PSH.BookCurrent.isBig_iff_isBigClass _).mpr hbigC
  have hmin : ∀ ψ : SchemeComplexPoint f → EReal, IsThetaPshPotential θ.val ψ →
      SingularityLE ψ (thetaPshSupremum θ.val) := fun ψ hψ =>
    FirstPass.thetaPshSupremum_minimalSingularities θ.val θ.2.1 θ.2.2
      (LocalPotentials.closedRealOneOne_hasLocalPotentials θ) ⟨_, hV⟩ ψ hψ
  rw [SGPT.GAGA.H0L.lineBundleOkounkovBody_eq_generalPartialBody f E Y hY a H hbig]
  exact PartialBody.generalPartialBody_eq_tradOkounkovBody_of_minimal hbigB hV hmin

/-- **Source `prop:Okounonlydepnum`, for the real first Chern class**: for big line bundles `L`,
`L'` (any smooth metrics `H`, `H'`) with the same real first Chern class
`{c₁(L, H)} = {c₁(L', H')}` in `H^{1,1}(X, ℝ)` (real Bott–Chern classes),
`Δ_ν(L) = Δ_ν(L')`. -/
theorem lineBundleOkounkovBody_eq_of_chernClass_eq [Nonempty (SchemeComplexPoint f)]
    {L L' : X.Modules} (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f (m + 1) E L)
    (a' : LineBundleAtlas L') (H' : SchemeLineBundleMetric f (m + 1) E L')
    (hbig : IsBig f L (m + 1)) (hbig' : IsBig f L' (m + 1))
    (hclass : letI := E.isSeparated; letI := E.quasiCompact;
      RealBottChern.ofRepresentative (H.curvature a) =
        RealBottChern.ofRepresentative (H'.curvature a')) :
    lineBundleOkounkovBody f (m + 1) E Y hY a = lineBundleOkounkovBody f (m + 1) E Y hY a' := by
  let := E.isSeparated
  let := E.quasiCompact
  rw [lineBundleOkounkovBody_eq_tradOkounkovBody f E Y hY a H hbig,
    lineBundleOkounkovBody_eq_tradOkounkovBody f E Y hY a' H' hbig',
    TranscendentalCore.tradOkounkovBody_eq_of_class_eq hclass]

end SGPT.Okounkov.OkoNS
