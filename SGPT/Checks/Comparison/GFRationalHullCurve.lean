import SGPT.Checks.Comparison.GFRationalHull

/-! # ORIGINAL rational hulls: actual section products and analytification at EVERY original point
Source: `lma:gfinimage`, closing paragraph and `eq:gf-rational-hull`.
Blueprint: `gf-rational-hull-curve.tex`. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.NAPotential.BJ.GfIm.RationalHull

open AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes
open SGPT.Okounkov SGPT.NAPotential.Berkovich SGPT.NAPotential.Berkovich.BJSections
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.PSH.VariableComplexAtlas SGPT.Convex.CutSimplex
open SGPT.NAPotential.Berkovich.PiecewiseLinearData.SimplexRevision
open SGPT.NAPotential.Berkovich.PiecewiseLinearData.SimplexRevision.WholeHull
open SGPT.Foundations.Envelope
open scoped BigOperators Classical ENNReal

variable {X : Scheme.{0}} {L : X.Modules} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] (E : ClosedProjectiveEmbedding f) [IsProjective f] [IsIntegral X]

local instance hullCurveProper : IsProper f :=
  (ProjectiveFactorizationRingIso.of_isProjective f).isProper
local instance hullCurvePointTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance hullCurvePointCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance hullCurvePointManifold : IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n

open SGPT.NAPotential.BJ.NativePicard SGPT.NAPotential.BJ.Printed
variable (b : LineBundleAtlas L) (HM : SchemeLineBundleMetric f n E L)

/-- `(c • a)` for `a ∈ [0, ∞]` and `c ∈ ℕ`. -/
theorem toENNReal_nsmul {a : WithTop ℝ} (ha : 0 ≤ a) (c : ℕ) :
    toENNReal (c • a) = c * toENNReal a := by
  induction c with
  | zero => simp
  | succ c ih =>
    rw [succ_nsmul, toENNReal_add (nsmul_nonneg ha c) ha, ih]
    push_cast
    ring

omit [IsIntegral X] in
/-- The rational GF formula, written as a supremum of translated values. -/
theorem packageEval_eq_iSup (D : RationalGFPackage X) (v : BerkovichPoint f) :
    D.eval f v = ⨆ i : D.data.I,
      (-(((toENNReal (powerSectionValue D.atlas D.n (D.data.sections i) v) / D.m : ℝ≥0∞)) :
        EReal) + (((D.data.weight i / D.m : ℚ) : ℝ) : EReal)) := by
  have hm := D.data.denominator_pos
  change rationalGFFunction D.atlas D.data v = _
  unfold rationalGFFunction SGPT.NAPotential.Berkovich.BJSections.finiteMaximum
  rw [Exist.coe_mul_iSup_of_finite (one_div_nonneg.mpr (Nat.cast_nonneg _))]
  refine iSup_congr fun i => ?_
  change (((1 / (D.m : ℝ)) : ℝ) : EReal) *
    (negativeValue (powerSectionValue D.atlas D.n (D.data.sections i) v) +
      (((D.data.weight i : ℚ) : ℝ) : EReal)) = _
  rw [Assembly.negativeValue_eq_neg_toENNReal (powerSectionValue_nonneg _ _ _ v)]
  have hmQ : (D.m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  have hw : D.data.weight i = (D.m : ℚ) * (D.data.weight i / D.m) := by field_simp
  conv_lhs => rw [hw]
  exact Exist.inv_mul_neg_add_mul hm _ _

/-- The actual original curve, genuine common-degree rational section hulls, and exact full-X^An identity. -/
def OriginalHullRealization {θ : AtlasClosedRealOneOneForm (ofFixedModel n (SchemeComplexPoint f))}
    (m : ℕ) (A : PiecewiseLinearData θ) (φ : BerkovichPoint f → EReal) : Prop :=
  (∀ l, ∃ q : ℚ, A.τ l = q) ∧
  (∀ v : BerkovichPoint f, A.curveAn n E v = φ v) ∧
  (∃ N : ℕ, 0 < N ∧ ∀ q : ℚ, (q : ℝ) ≤ A.τ 0 →
    ∃ Q : ℕ, 0 < Q ∧ ∃ F : ActualSectionFamily L (N * Q),
      (∀ j, F.sections j ≠ 0) ∧
      uscRegularization (A.pointwiseUpperConcaveEnvelope (q : ℝ)) =
        fun p => ((((m * N * Q : ℕ) : ℝ)⁻¹ : ℝ) : EReal) *
          finiteMaximum (fun j => HM.sectionLogNormSq b (N * Q) (F.sections j)) p) ∧
  ∀ v : BerkovichPoint f, φ v = ⨆ q : ℚ, ⨆ (_ : (q : ℝ) < A.τ 0),
    potentialAn n E (uscRegularization (A.pointwiseUpperConcaveEnvelope (q : ℝ))) v +
      ((q : ℝ) : EReal)

theorem exists_originalHullRealization_of_package {m : ℕ} (hm : 0 < m)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n (SchemeComplexPoint f))}
    (hθ : (atlasClosedFormToNative θ).val.GeometricallyEq (((m : ℝ)⁻¹) • HM.curvature b).val)
    (D : RationalGFPackage X) (hD : D.picardClass = (m : ℚ)⁻¹ • rationalPicardClass b) :
    ∃ A : PiecewiseLinearData θ, OriginalHullRealization f n E b HM m A (D.eval f) := by
  classical
  obtain ⟨k, hk, t, ht, hval⟩ := exists_sections_of_picardClass f D b hm hD
  have hmD := D.data.denominator_pos
  set K := m * (D.m * k) with hKdef
  have hKpos : 0 < K := Nat.mul_pos hm (Nat.mul_pos hmD hk)
  set w : D.data.I → ℚ := fun i => D.data.weight i / D.m with hw
  set W : Finset ℚ := Finset.univ.image w with hW
  have hWne : W.Nonempty := Finset.univ_nonempty.image w
  have hc : 0 < W.card := Finset.card_pos.mpr hWne
  set N' := W.card - 1 with hN'def
  have hN' : N' + 1 = W.card := Nat.sub_add_cancel hc
  set ord := W.orderEmbOfFin (rfl : W.card = W.card) with hord
  set τq : Fin (N' + 1) → ℚ := fun l => ord (Fin.rev (Fin.cast hN' l)) with hτq
  have hτmem : ∀ l, τq l ∈ W := fun l => W.orderEmbOfFin_mem rfl _
  have hτanti : StrictAnti τq := by
    intro l l' hll'
    apply ord.strictMono
    rw [Fin.rev_lt_rev, Fin.cast_lt_cast]
    exact hll'
  have hne : ∀ l, Nonempty {i : D.data.I // w i = τq l} := fun l => by
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp (hτmem l)
    exact ⟨⟨i, hi⟩⟩
  -- the node potentials `A_τ = K⁻¹ max_{λ_i/m_D = τ} log |t_i|²`
  set A : Fin (N' + 1) → SchemeComplexPoint f → EReal := fun l =>
    haveI := hne l
    fun p => (((K : ℝ)⁻¹ : ℝ) : EReal) *
      sectionsMaxLog f n E b (D.m * k) (fun i : {i // w i = τq l} => t i.1) HM p with hA
  have hApsh : ∀ l, (ofFixedModel n (SchemeComplexPoint f)).IsThetaPSH θ (A l) := by
    intro l
    have := hne l
    have h1 := isThetaPshPotential_sectionsMaxLog f n E b (D.m * k)
      (fun i : {i // w i = τq l} => t i.1) HM (fun i => ht i.1)
    have h2 := SGPT.Okounkov.TranscendentalCore.isThetaPshPotential_nonneg_smul h1
      (inv_nonneg.mpr (Nat.cast_nonneg (α := ℝ) K))
    have hform : ((K : ℝ)⁻¹ • (((D.m * k : ℕ) : ℝ) • HM.curvature b)) =
        ((m : ℝ)⁻¹ • HM.curvature b) := by
      rw [smul_smul]
      congr 1
      have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
      have hDR : (D.m : ℝ) ≠ 0 := by exact_mod_cast hmD.ne'
      have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
      simp only [hKdef]
      push_cast
      field_simp
    rw [hform] at h2
    exact (isThetaPSH_iff_nativeThetaPotential θ _).mpr ((hθ.thetaPshPotential_iff _).mpr h2)
  let P : PiecewiseLinearData θ :=
    ⟨N', A, hApsh, fun l => (τq l : ℝ), fun l l' h => by
      show ((τq l' : ℚ) : ℝ) < τq l
      exact_mod_cast hτanti h⟩
  let : ∀ l, Nonempty {i : D.data.I // w i = τq l} := hne
  have hrat : ∀ l, ∃ q : ℚ, P.τ l = q := fun l => ⟨τq l, rfl⟩
  have hApresent : ∀ l, P.A l = fun p => (((K : ℝ)⁻¹ : ℝ) : EReal) *
      finiteMaximum (fun i : {i : D.data.I // w i = τq l} => HM.sectionLogNormSq b (D.m * k) (t i.1)) p := by
    intro l
    rfl
  have hcurve : ∀ v : BerkovichPoint f, P.curveAn n E v = D.eval f v := by
    intro v
    -- the node terms
    have hKc : (K : ℝ≥0∞) = ((m * k : ℕ) : ℝ≥0∞) * (D.m : ℝ≥0∞) := by
      rw [hKdef]
      push_cast
      ring
    have hmk0 : ((m * k : ℕ) : ℝ≥0∞) ≠ 0 := by exact_mod_cast (Nat.mul_pos hm hk).ne'
    have hnode : ∀ l, potentialAn n E (A l) v + ((τq l : ℝ) : EReal) =
        ⨆ i : {i // w i = τq l},
          (-(((toENNReal (powerSectionValue D.atlas D.n (D.data.sections i.1) v) / D.m : ℝ≥0∞)) :
            EReal) + (((w i.1 : ℚ) : ℝ) : EReal)) := by
      intro l
      have := hne l
      have h := potentialAn_sectionsMaxLog_all_narrow f n E HM b (D.m * k) (fun i : {i // w i = τq l} => t i.1)
        (fun i => ht i.1) hKpos v
      simp only [hA]
      rw [h, idealVal_sectionsIdeal f b (D.m * k) _ v, ← Exist.iSup_neg_div_add]
      refine iSup_congr fun i => ?_
      rw [hval i.1 v, toENNReal_nsmul (powerSectionValue_nonneg _ _ _ v), hKc,
        ENNReal.mul_div_mul_left _ _ hmk0 (ENNReal.natCast_ne_top _), i.2]
    rw [PiecewiseLinearData.curveAn_eq_iSup, packageEval_eq_iSup]
    change (⨆ l, potentialAn n E (A l) v + ((τq l : ℝ) : EReal)) = _
    simp_rw [hnode]
    apply le_antisymm
    · exact iSup_le fun l => iSup_le fun i => le_iSup (fun i : D.data.I =>
        (-(((toENNReal (powerSectionValue D.atlas D.n (D.data.sections i) v) / D.m : ℝ≥0∞)) :
          EReal) + (((D.data.weight i / D.m : ℚ) : ℝ) : EReal))) i.1
    · refine iSup_le fun i => ?_
      have hiW : w i ∈ (W : Set ℚ) := Finset.mem_coe.mpr (Finset.mem_image_of_mem w (Finset.mem_univ i))
      rw [← Finset.range_orderEmbOfFin W rfl] at hiW
      obtain ⟨j, hj⟩ := hiW
      have hl : τq (Fin.cast hN'.symm (Fin.rev j)) = w i := by
        simp only [hτq, Fin.cast_cast, Fin.cast_eq_self, Fin.rev_rev]
        exact hj
      refine le_iSup_of_le (Fin.cast hN'.symm (Fin.rev j)) (le_iSup_of_le ⟨i, hl.symm⟩ ?_)
      exact le_rfl

  refine ⟨P, hrat, hcurve, ?_, ?_⟩
  · refine ⟨D.m * k, Nat.mul_pos hmD hk, ?_⟩
    intro q hq
    obtain ⟨Q, hQ, F, hF, heq⟩ := exists_originalHull_sectionMaximum n E HM b
      (D.m * k) K hKpos P hrat (fun l => {i : D.data.I // w i = τq l})
      (fun l i => t i.1) (fun l i => ht i.1) hApresent q hq
    exact ⟨Q, hQ, F, hF, by simpa only [hKdef] using heq⟩
  · intro v
    rw [← hcurve v]
    exact curveAn_eq_rational_originalHullSup f n E HM b (D.m * k) K hKpos P hrat
      (fun l => {i : D.data.I // w i = τq l}) (fun l i => t i.1)
      (fun l i => ht i.1) hApresent v

/-- EVERY actual original rational GF function has the full original rational-hull realization,
with genuine original common-degree section products and equality on ALL X^An. -/
theorem exists_originalHullRealization_of_isRationalGF {m : ℕ} (hm : 0 < m)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n (SchemeComplexPoint f))}
    (hθ : (atlasClosedFormToNative θ).val.GeometricallyEq (((m : ℝ)⁻¹) • HM.curvature b).val)
    {φ : BerkovichPoint f → EReal}
    (hφ : IsRationalGF f ((m : ℚ)⁻¹ • rationalPicardClass b) φ) :
    ∃ A : PiecewiseLinearData θ, OriginalHullRealization f n E b HM m A φ := by
  obtain ⟨D, hD, rfl⟩ := hφ
  exact exists_originalHullRealization_of_package f n E b HM hm hθ D hD

end SGPT.NAPotential.BJ.GfIm.RationalHull
