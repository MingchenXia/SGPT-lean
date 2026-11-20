import SGPT.Checks.Comparison.GfImTransport
import SGPT.Checks.Comparison.BJExistPackage
import SGPT.Checks.Comparison.BJAsmPLTest
import SGPT.Checks.Comparison.DimZeroDXZ
import SGPT.NAPotential.QwNANonTrivRestZero

/-!
# `lma:gfinimage`: rational GF functions are analytifications of piecewise linear curves

Source: `chapter_NApotential.tex`, `lma:gfinimage` (*The comparison theorem*):

> Let `φ ∈ H^gf_ℚ(L^An)`. Then there is a piecewise linear curve `A` in `PSH(X, θ)` with
> `φ = A^An`. In particular, `φ` is in the image of `eq:analymap`.

This file proves the first sentence on all of `X^An`, together with the remark of the proof that
the nodes `τ_0 > ⋯ > τ_N` are rational (`exists_piecewiseLinearData_curveAn_eq`,
`exists_piecewiseLinearData_of_isRationalGF`). The second sentence is `GfImImage`.

## Formal setting

As for `lma:varphian` and `lma:pltest` (`SGPT.Checks.Comparison.BJAsmVarphian`, `SGPT.Checks.Comparison.BJAsmPLTest`):
`X` integral, projective and smooth of relative dimension `n` over `ℂ` with a closed projective
embedding `E`; `L = m⁻¹ [M]` for an algebraic line bundle `M` with atlas `b` and smooth metric
`h_M`; `θ = c₁(L, h) = m⁻¹ c₁(M, h_M)` (equal coefficients in every chart);
`H^gf_ℚ(L^An)` is `IsRationalGF f L` (`def:BJpshmetric`'s rational GF functions, all of whose data
are actual sections of actual line bundles); `A^An` is `PiecewiseLinearData.curveAn`
(`eq:psianvlinear`).

## Proof

Write `φ = m_D⁻¹ max_i (log |s_i| + λ_i)` with `s_i ∈ H⁰(A^{n_D})`, `(n_D/m_D)[A] = m⁻¹[M]`. Some
power `A^{n_D m k}` is isomorphic to `M^{m_D k}`, carrying `s_i^{mk}` to `t_i ∈ H⁰(M^{m_D k})` with
`v(t_i) = mk v(s_i)` (`exists_sections_of_picardClass`). With `K = m m_D k`, group the indices by
the value `τ = λ_i / m_D` and put `A_τ = K⁻¹ max_{λ_i/m_D = τ} log |t_i|²_{h_M^{m_D k}}`, which lies
in `PSH(X, θ)`. At every `v ∈ X^An`, `A_τ^An(v) = -K⁻¹ min_i v(t_i) = -m_D⁻¹ min_i v(s_i)`
(`GfIm.potentialAn_sectionsMaxLog`, Skoda's theorem and GAGA; in dimension `0` both sides vanish),
so `A^An(v) = max_τ (A_τ^An(v) + τ) = m_D⁻¹ max_i (-v(s_i) + λ_i) = φ(v)`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.NAPotential.BJ.GfIm

open Set Filter
open scoped ENNReal
open AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes SGPT.Okounkov
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.NAPotential.Berkovich SGPT.NAPotential.Berkovich.BJSections SGPT.PSH.VariableComplexAtlas
open SGPT.NAPotential.BJ SGPT.NAPotential.BJ.NativePicard SGPT.NAPotential.BJ.Printed
open SGPT.Foundations.Envelope

/-- `(c • a)` for `a ∈ [0, ∞]` and `c ∈ ℕ`. -/
theorem toENNReal_nsmul {a : WithTop ℝ} (ha : 0 ≤ a) (c : ℕ) :
    toENNReal (c • a) = c * toENNReal a := by
  induction c with
  | zero => simp
  | succ c ih =>
    rw [succ_nsmul, toENNReal_add (nsmul_nonneg ha c) ha, ih]
    push_cast
    ring

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (n : ℕ) [SmoothOfRelativeDimension n f]
  (E : ClosedProjectiveEmbedding f) [IsProjective f] [IsIntegral X]

local instance gfImCurveProper : IsProper f :=
  (ProjectiveFactorizationRingIso.of_isProjective f).isProper

local instance gfImCurvePointTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance gfImCurvePointCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance gfImCurvePointManifold : IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n

/-- The rational GF formula, written as a supremum of translated values. -/
theorem eval_eq_iSup (D : RationalGFPackage X) (v : BerkovichPoint f) :
    D.eval f v = ⨆ i : D.data.I,
      (-(((toENNReal (powerSectionValue D.atlas D.n (D.data.sections i) v) / D.m : ℝ≥0∞)) :
        EReal) + (((D.data.weight i / D.m : ℚ) : ℝ) : EReal)) := by
  have hm := D.data.denominator_pos
  change rationalGFFunction D.atlas D.data v = _
  unfold rationalGFFunction finiteMaximum
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

variable {M : X.Modules} (b : LineBundleAtlas M) (HM : SchemeLineBundleMetric f n E M)

/-- `(K⁻¹ max_k log |t_k|²)^An = -K⁻¹ min_k v(t_k)` in every dimension (in dimension `0` both
sides vanish: `X^An` is the trivial point). -/
theorem potentialAn_sectionsMaxLog_all (N : ℕ) {ι : Type} [Fintype ι] [Nonempty ι]
    (t : ι → bundlePowerGlobalSections M N) (ht : ∀ k, t k ≠ 0) {K : ℕ} (hK : 0 < K)
    (v : BerkovichPoint f) :
    potentialAn n E (fun p => (((K : ℝ)⁻¹ : ℝ) : EReal) * sectionsMaxLog f n E b N t HM p) v =
      -(((v.idealVal (sectionsIdeal b N t) / K : ℝ≥0∞)) : EReal) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have hΦ := isThetaPshPotential_sectionsMaxLog f 0 E b N t HM ht
    have hψ := SGPT.Okounkov.TranscendentalCore.isThetaPshPotential_nonneg_smul hΦ
      (inv_nonneg.mpr (Nat.cast_nonneg (α := ℝ) K))
    have := SGPT.NAPotential.DimZero.berkovichPoint_subsingleton_of_dim_zero f
    have hv : v = BerkovichPoint.trivial f := Subsingleton.elim _ _
    rw [NANS.potentialAn_eq_zero_of_dim_zero (E := E) hψ.quasiPshPotential v,
      idealVal_sectionsIdeal f b N t v, hv]
    simp [powerSectionValue_trivial b N _ (ht _)]
  · exact potentialAn_sectionsMaxLog f n E b N t HM hn ht hK v

/-- **`lma:gfinimage`, first sentence, for a package**: if the rational GF package `D` has class
`L = m⁻¹ [M]`, there is a piecewise linear curve `A` in `PSH(X, θ)`, `θ = m⁻¹ c₁(M, h_M)`, with
rational nodes, such that `A^An = D` on all of `X^An`. -/
theorem exists_piecewiseLinearData_curveAn_eq {m : ℕ} (hm : 0 < m)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n (SchemeComplexPoint f))}
    (hθ : (atlasClosedFormToNative θ).val.GeometricallyEq (((m : ℝ)⁻¹) • HM.curvature b).val)
    (D : RationalGFPackage X) (hD : D.picardClass = (m : ℚ)⁻¹ • rationalPicardClass b) :
    ∃ A : PiecewiseLinearData θ, (∀ l, ∃ q : ℚ, A.τ l = q) ∧
      ∀ v : BerkovichPoint f, A.curveAn n E v = D.eval f v := by
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
  refine ⟨⟨N', A, hApsh, fun l => (τq l : ℝ), fun l l' h => by show ((τq l' : ℚ) : ℝ) < τq l; exact_mod_cast hτanti h⟩,
    fun l => ⟨τq l, rfl⟩, fun v => ?_⟩
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
    have h := potentialAn_sectionsMaxLog_all f n E b HM (D.m * k) (fun i : {i // w i = τq l} => t i.1)
      (fun i => ht i.1) hKpos v
    simp only [hA]
    rw [h, idealVal_sectionsIdeal f b (D.m * k) _ v, ← Exist.iSup_neg_div_add]
    refine iSup_congr fun i => ?_
    rw [hval i.1 v, toENNReal_nsmul (powerSectionValue_nonneg _ _ _ v), hKc,
      ENNReal.mul_div_mul_left _ _ hmk0 (ENNReal.natCast_ne_top _), i.2]
  rw [PiecewiseLinearData.curveAn_eq_iSup, eval_eq_iSup]
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

/-- **`lma:gfinimage`, first sentence**: every `φ ∈ H^gf_ℚ(L^An)`, `L = m⁻¹ [M]`, is the
analytification `A^An` (on all of `X^An`) of a piecewise linear curve `A` in `PSH(X, θ)`,
`θ = m⁻¹ c₁(M, h_M)`, whose nodes are rational. -/
theorem exists_piecewiseLinearData_of_isRationalGF {m : ℕ} (hm : 0 < m)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n (SchemeComplexPoint f))}
    (hθ : (atlasClosedFormToNative θ).val.GeometricallyEq (((m : ℝ)⁻¹) • HM.curvature b).val)
    {φ : BerkovichPoint f → EReal}
    (hφ : IsRationalGF f ((m : ℚ)⁻¹ • rationalPicardClass b) φ) :
    ∃ A : PiecewiseLinearData θ, (∀ l, ∃ q : ℚ, A.τ l = q) ∧ A.curveAn n E = φ := by
  obtain ⟨D, hD, rfl⟩ := hφ
  obtain ⟨A, hτ, hA⟩ := exists_piecewiseLinearData_curveAn_eq f n E b HM hm hθ D hD
  exact ⟨A, hτ, funext hA⟩

end SGPT.NAPotential.BJ.GfIm
