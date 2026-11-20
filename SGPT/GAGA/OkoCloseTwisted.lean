import SGPT.GAGA.OkoCloseFamily
import SGPT.GAGA.H0LDXMain
import SGPT.IGood.DXMainTwistedUpper

/-!
# GAGA for the twisted section spaces `H⁰(X, T ⊗ L^k)`


`X` is smooth projective over `ℂ`, `T` and `L` are algebraic line bundles with rank-one atlases
`aT` (frames `β_j` on `W_j`) and `a` (frames `αᵢ` on `Vᵢ`) and smooth metrics `HT`, `H`. The
analytic twisted bundle of lane DX-LOW2 is `twistedPower(L^an, T^an, k) = T^an ⊗ (L^an)^{⊗ k}`
(`L^an = (L, H)^an`, `T^an = (T, HT)^an`), with the frames `β_j ⊗ αᵢ^k`; the algebraic twisted
bundle of lane DXMAIN is `T ⊗ L^k = bundleTensor T (bundleTensorPower L k)` with the pairwise
tensor atlas `twistAtlas` (frames `β_j|_{W_j ∩ Vᵢ} ⊗ αᵢ^k|_{W_j ∩ Vᵢ}`).

* `schemeFrameTransition_restrict`: restricting frames does not change the analytic transitions;
* `tcoef`, `tcoef_transition`: the coefficients `c_{ji}` of a holomorphic section `s` of
  `twistedPower(L^an, T^an, k)` in the frames `β_j ⊗ αᵢ^k` satisfy `c_{j'i'} = g^T_{jj'} (g^L_{ii'})^k c_{ji}`,
  which is the transition law of the frames of `twistAtlas` (`schemeFrameTransition_twistAtlas`):
  they form a holomorphic coefficient family of degree one for `twistAtlas`
  (`isHolomorphicCoefficientFamily_tcoef`);
* **`exists_isTwistedAnalytificationOf`** (GAGA for `T ⊗ L^k`): every holomorphic section of
  `twistedPower(L^an, T^an, k)` is the analytification of a unique algebraic section of
  `T ⊗ L^k`, and `s ↦ s^alg` is `ℂ`-linear and injective (`twistedAlgSectionLinear`);
* `norm_sq_eq_sectionNormSq_twistMetric`: `|s|² = |s^alg|²_{h_T ⊗ h^k}`;
* `isIdealSection_of_lintegral_lt_top`: finite weighted `L²` norm implies membership in the
  multiplier ideal, in any degree and with any weight;
* **`finrank_literal_le_twistedMultiplierH0`**:
  `dim Γ(X, T ⊗ L^k ⊗ 𝓘(kφ))^{an} ≤ h⁰(X, T ⊗ L^k ⊗ 𝓘(kφ))` (the analytic section space of lane
  DX-LOW2 injects into the algebraic one of lane DXMAIN).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.GAGA.OkoClose

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Filter Set Bundle MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Okounkov SGPT.NAPotential.GAGAMult SGPT.GAGA.H0S SGPT.GAGA.H0L SGPT.LineBundle
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle
open SGPT.Bergman.MultiplierSectionsDraft SGPT.Bergman.PolynomialH0Growth
open SGPT.Bergman.NativeHermitianMetric
open Metric
open scoped Topology Manifold ENNReal

/-! ### Restricted frames -/

section Restrict

variable {X : Scheme} (f : X ⟶ Spec (.of ℂ)) (n : ℕ) [SmoothOfRelativeDimension n f]
  (E : ClosedProjectiveEmbedding f)

local instance okoTwRTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance okoTwRCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n

/-- **Restricting frames does not change the transitions**: if `r`, `r'` are frames on
`W ⊆ U`, `W' ⊆ U'` whose coefficients are those of `e`, `e'` (e.g. restrictions of `e`, `e'`),
then the analytic transition of `(r, r')` is that of `(e, e')` on `W ∩ W'`. -/
theorem schemeFrameTransition_congr_restrict {L : X.Modules} {U U' W W' : X.Opens}
    (e : LocalBundleFrame L U) (e' : LocalBundleFrame L U') (r : LocalBundleFrame L W)
    (r' : LocalBundleFrame L W') (hW : W ≤ U) (hW' : W' ≤ U')
    (hr : ∀ {Z : X.Opens} (j : Z ⟶ W) (s : bundleSections L Z),
      r.coefficients j s = e.coefficients (j ≫ homOfLE hW) s)
    (hr' : ∀ {Z : X.Opens} (j : Z ⟶ W') (s : bundleSections L Z),
      r'.coefficients j s = e'.coefficients (j ≫ homOfLE hW') s)
    (p : SchemeComplexPoint f) (hp : schemeComplexPointImage f p ∈ W)
    (hp' : schemeComplexPointImage f p ∈ W') :
    schemeFrameTransition f n E r r' p = schemeFrameTransition f n E e e' p := by
  have hU : W ⊓ W' ≤ U := inf_le_left.trans hW
  have hU' : W ⊓ W' ≤ U' := inf_le_right.trans hW'
  have htr : localBundleFrameTransition r r' (homOfLE inf_le_left) (homOfLE inf_le_right) =
      localBundleFrameTransition e e' (homOfLE hU) (homOfLE hU') := by
    unfold localBundleFrameTransition
    have h1 : r.coefficients (homOfLE (inf_le_left : W ⊓ W' ≤ W)) =
        e.coefficients (homOfLE hU) := LinearEquiv.ext fun s => by
      rw [hr]
      rfl
    have h2 : r'.coefficients (homOfLE (inf_le_right : W ⊓ W' ≤ W')) =
        e'.coefficients (homOfLE hU') := LinearEquiv.ext fun s => by
      rw [hr']
      rfl
    rw [h1, h2]
  unfold schemeFrameTransition
  rw [htr]
  exact schemeFrameTransition_on_subopen f n E e e' hU hU' ⟨hp, hp'⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- Restricted frames: the coefficients of `e|_W` are those of `e` (as in Bing–Wang's
`bundleHomRestrictionIso_coefficients`). -/
theorem coefficients_bundleHomRestrictionIso {L : X.Modules} {U W : X.Opens}
    (e : LocalBundleFrame L U) (h : W ≤ U) {Z : X.Opens} (j : Z ⟶ W) (s : bundleSections L Z) :
    (show LocalBundleFrame L W from
      bundleHomRestrictionIso L (SheafOfModules.unit X.ringCatSheaf) (homOfLE h) e).coefficients j s =
      e.coefficients (j ≫ homOfLE h) s :=
  bundleHomRestriction_app L (SheafOfModules.unit X.ringCatSheaf) (homOfLE h) e.hom
    (Opposite.op (Over.mk j)) s

/-- The coefficients of a frame are trivially "those of itself". -/
theorem coefficients_self {L : X.Modules} {U : X.Opens} (e : LocalBundleFrame L U) {Z : X.Opens}
    (j : Z ⟶ U) (s : bundleSections L Z) :
    e.coefficients j s = e.coefficients (j ≫ homOfLE (le_refl U)) s := by
  have : j ≫ homOfLE (le_refl U) = j := Subsingleton.elim _ _
  rw [this]

variable {T M : X.Modules}

/-- The transitions of the pairwise tensor atlas are the products of the transitions:
`g_{(j,i),(j',i')} = g^T_{jj'} g^M_{ii'}`. -/
theorem schemeFrameTransition_pairwiseTensorAtlas (aT : LineBundleAtlas T) (b : LineBundleAtlas M)
    (ji ji' : aT.I × b.I) (p : SchemeComplexPoint f)
    (hp : schemeComplexPointImage f p ∈ (pairwiseTensorAtlas aT b).opens ji)
    (hp' : schemeComplexPointImage f p ∈ (pairwiseTensorAtlas aT b).opens ji') :
    schemeFrameTransition f n E ((pairwiseTensorAtlas aT b).frame ji)
        ((pairwiseTensorAtlas aT b).frame ji') p =
      schemeFrameTransition f n E (aT.frame ji.1) (aT.frame ji'.1) p *
        schemeFrameTransition f n E (b.frame ji.2) (b.frame ji'.2) p := by
  change schemeFrameTransition f n E
      ((leftRestrictedFrame aT b ji).tensor (rightRestrictedFrame aT b ji))
      ((leftRestrictedFrame aT b ji').tensor (rightRestrictedFrame aT b ji')) p = _
  rw [SGPT.IGood.DXMain.schemeFrameTransition_tensor f n E _ _ _ _ p hp hp']
  congr 1
  · exact schemeFrameTransition_congr_restrict f n E _ _ _ _ inf_le_left inf_le_left
      (fun j s => coefficients_bundleHomRestrictionIso _ inf_le_left j s)
      (fun j s => coefficients_bundleHomRestrictionIso _ inf_le_left j s) p hp hp'
  · exact schemeFrameTransition_congr_restrict f n E _ _ _ _ inf_le_right inf_le_right
      (fun j s => coefficients_bundleHomRestrictionIso _ inf_le_right j s)
      (fun j s => coefficients_bundleHomRestrictionIso _ inf_le_right j s) p hp hp'

/-- The weight of a restricted frame is the weight of the frame. -/
theorem frameNormSq_bundleHomRestrictionIso {L : X.Modules} (K : SchemeLineBundleMetric f n E L)
    {U W : X.Opens} (e : LocalBundleFrame L U) (h : W ≤ U) (p : SchemeComplexPoint f)
    (hp : schemeComplexPointImage f p ∈ W) :
    K.frameNormSq (show LocalBundleFrame L W from
      bundleHomRestrictionIso L (SheafOfModules.unit X.ringCatSheaf) (homOfLE h) e) p =
      K.frameNormSq e p := by
  rw [K.transition _ e p hp (h hp),
    schemeFrameTransition_congr_restrict f n E e e _ e h le_rfl
      (fun j s => coefficients_bundleHomRestrictionIso e h j s) (fun j s => coefficients_self e j s)
      p hp (h hp),
    schemeFrameTransition_self f n E e p (h hp), Complex.normSq_one, one_mul]

end Restrict

/-! ### The coefficients of a holomorphic twisted section -/

section Coefficients

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} {E : ClosedProjectiveEmbedding f} {n : ℕ}
  [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f]

local instance okoTwTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance okoTwCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance okoTwManifold : IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n

variable {T L : X.Modules} (aT : LineBundleAtlas T) (HT : SchemeLineBundleMetric f n E T)
  (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f n E L)

/-- The analytic frame `β_j ⊗ αᵢ^k` of `twistedPower(L^an, T^an, k)`. -/
def twistAnFrame (ji : aT.I × a.I) (k : ℕ) :
    AtlasFrame (twistedPower (schemeHermitianLineBundle f n E a H)
      (schemeHermitianLineBundle f n E aT HT) k) :=
  twistedPowerAtlasFrame (schemeHermitianAtlasFrame f n E a H (a.frame ji.2))
    (schemeHermitianAtlasFrame f n E aT HT (aT.frame ji.1)) k

theorem mem_twistAnFrame_baseSet {ji : aT.I × a.I} (k : ℕ) {p : SchemeComplexPoint f}
    (hp : schemeComplexPointImage f p ∈ (pairwiseTensorAtlas aT (a.tensorPower k)).opens ji) :
    p ∈ (twistAnFrame aT HT a H ji k).val.baseSet :=
  twistedPowerAtlasFrame_mem _ _ hp.2 hp.1 k

variable {k : ℕ}

/-- The coefficient `c_{ji}` of a holomorphic section `s` of `twistedPower(L^an, T^an, k)` in the
frame `β_j ⊗ αᵢ^k`. -/
def tcoef (s : twistedSections (schemeHermitianLineBundle f n E a H)
    (schemeHermitianLineBundle f n E aT HT) k) (ji : aT.I × a.I) (p : SchemeComplexPoint f) : ℂ :=
  (twistAnFrame aT HT a H ji k).val.continuousLinearMapAt ℂ p (s p)

/-- **Transition of the twisted coefficients**: `c_{j'i'} = (g^L_{ii'})^k g^T_{jj'} c_{ji}`. -/
theorem tcoef_transition (s : twistedSections (schemeHermitianLineBundle f n E a H)
      (schemeHermitianLineBundle f n E aT HT) k) (ji ji' : aT.I × a.I) {p : SchemeComplexPoint f}
    (hp : schemeComplexPointImage f p ∈ (pairwiseTensorAtlas aT (a.tensorPower k)).opens ji)
    (hp' : schemeComplexPointImage f p ∈ (pairwiseTensorAtlas aT (a.tensorPower k)).opens ji') :
    tcoef aT HT a H s ji' p = schemeFrameTransition f n E (a.frame ji.2) (a.frame ji'.2) p ^ k *
      schemeFrameTransition f n E (aT.frame ji.1) (aT.frame ji'.1) p * tcoef aT HT a H s ji p := by
  set e := twistAnFrame aT HT a H ji k
  set e' := twistAnFrame aT HT a H ji' k
  have he : p ∈ e.val.baseSet := mem_twistAnFrame_baseSet aT HT a H k hp
  have he' : p ∈ e'.val.baseSet := mem_twistAnFrame_baseSet aT HT a H k hp'
  have htr := twistedPower_frame_transition
    (schemeHermitianAtlasFrame f n E a H (a.frame ji.2))
    (schemeHermitianAtlasFrame f n E a H (a.frame ji'.2))
    (schemeHermitianAtlasFrame f n E aT HT (aT.frame ji.1))
    (schemeHermitianAtlasFrame f n E aT HT (aT.frame ji'.1))
    (x := p) hp.2 hp'.2 hp.1 hp'.1 k
  rw [coordChangeL_schemeHermitianAtlasFrame' a H _ _ hp.2 hp'.2,
    coordChangeL_schemeHermitianAtlasFrame' aT HT _ _ hp.1 hp'.1] at htr
  unfold tcoef
  rw [Trivialization.continuousLinearMapAt_apply_of_mem (R := ℂ) e'.val he',
    Trivialization.continuousLinearMapAt_apply_of_mem (R := ℂ) e.val he]
  have hs : s p = e.val.symm p ((e.val ⟨p, s p⟩).2) := (e.val.symm_apply_apply_mk he (s p)).symm
  conv_lhs => rw [hs]
  rw [← Trivialization.coordChangeL_apply (R := ℂ) e.val e'.val ⟨he, he'⟩]
  have hlin : (e.val.coordChangeL ℂ e'.val p) ((e.val ⟨p, s p⟩).2) =
      (e.val ⟨p, s p⟩).2 * (e.val.coordChangeL ℂ e'.val p) 1 := by
    rw [← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one]
  rw [hlin]
  change _ * ((twistedPowerAtlasFrame _ _ k).val.coordChangeL ℂ
    (twistedPowerAtlasFrame _ _ k).val p) 1 = _
  rw [htr]
  ring

/-- **The twisted coefficients form a holomorphic coefficient family of degree one** for the
pairwise tensor atlas of `T ⊗ L^k`. -/
theorem isHolomorphicCoefficientFamily_tcoef
    (s : twistedSections (schemeHermitianLineBundle f n E a H)
      (schemeHermitianLineBundle f n E aT HT) k) :
    IsHolomorphicCoefficientFamily f E n (pairwiseTensorAtlas aT (a.tensorPower k)) 1
      (tcoef aT HT a H s) where
  holomorphicAt ji p hp :=
    holomorphicAt_coef_of_contMDiff (twistAnFrame aT HT a H ji k).val s.contMDiff
      (mem_twistAnFrame_baseSet aT HT a H k hp)
  transition ji ji' p hp hp' := by
    rw [tcoef_transition aT HT a H s ji ji' hp hp', pow_one,
      schemeFrameTransition_pairwiseTensorAtlas f n E aT (a.tensorPower k) ji ji' p hp hp']
    change _ = _ * schemeFrameTransition f n E ((a.frame ji.2).tensorPower k)
      ((a.frame ji'.2).tensorPower k) p * _
    rw [schemeFrameTransition_tensorPower f n E _ _ k p hp.2 hp'.2]
    ring

/-- `s = σ^an` for a holomorphic section `s` of `twistedPower(L^an, T^an, k)` and an algebraic
section `σ ∈ H⁰(X, T ⊗ L^k)`: in every frame `β_j ⊗ αᵢ^k`, the coefficient of `s` is the analytic
function of the algebraic coefficient of `σ`. -/
def IsTwistedAnalytificationOf
    (s : twistedSections (schemeHermitianLineBundle f n E a H)
      (schemeHermitianLineBundle f n E aT HT) k)
    (σ : bundlePowerGlobalSections (bundleTensor T (bundleTensorPower L k)) 1) : Prop :=
  ∀ (ji : aT.I × a.I) (p : SchemeComplexPoint f),
    schemeComplexPointImage f p ∈ (pairwiseTensorAtlas aT (a.tensorPower k)).opens ji →
      tcoef aT HT a H s ji p = schemeOpenRegularFunction f n E
        ((pairwiseTensorAtlas aT (a.tensorPower k)).opens ji)
        (algCoef ((pairwiseTensorAtlas aT (a.tensorPower k)).frame ji) 1 σ) p

/-- **GAGA for the twisted bundles `T ⊗ L^k`**: every holomorphic section of
`twistedPower(L^an, T^an, k)` is the analytification of an algebraic section of `T ⊗ L^k`. -/
theorem exists_isTwistedAnalytificationOf [CompactSpace (SchemeComplexPoint f)]
    (s : twistedSections (schemeHermitianLineBundle f n E a H)
      (schemeHermitianLineBundle f n E aT HT) k) :
    ∃ σ : bundlePowerGlobalSections (bundleTensor T (bundleTensorPower L k)) 1,
      IsTwistedAnalytificationOf aT HT a H s σ := by
  obtain ⟨σ, hσ⟩ := exists_section_of_isHolomorphicCoefficientFamily
    (isHolomorphicCoefficientFamily_tcoef aT HT a H s)
  exact ⟨σ, fun ji p hp => (hσ ji p hp).symm⟩

/-- The algebraic section of a holomorphic twisted section is unique. -/
theorem eq_of_isTwistedAnalytificationOf
    {s : twistedSections (schemeHermitianLineBundle f n E a H)
      (schemeHermitianLineBundle f n E aT HT) k}
    {σ σ' : bundlePowerGlobalSections (bundleTensor T (bundleTensorPower L k)) 1}
    (h : IsTwistedAnalytificationOf aT HT a H s σ)
    (h' : IsTwistedAnalytificationOf aT HT a H s σ') : σ = σ' :=
  eq_of_algCoef_eq (pairwiseTensorAtlas aT (a.tensorPower k)) fun ji p hp =>
    (h ji p hp).symm.trans (h' ji p hp)

end Coefficients

/-! ### Finite weighted `L²` norm and multiplier ideals, in any degree -/

section Ideal

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} {n : ℕ} [SmoothOfRelativeDimension n f]
  {E : ClosedProjectiveEmbedding f}

local instance okoIdTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance okoIdCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance okoIdManifold [IsSeparated f] [QuasiCompact f] :
    IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n
local instance okoIdMeasurable : MeasurableSpace (SchemeComplexPoint f) := borel _
local instance okoIdBorel : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩

/-- A section `σ` of `L^d` with finite weighted `L²` norm `∫_X |σ|²_{h^d} e^{-cψ} dμ` (`c > 0`, `ψ`
Borel, `μ` a smooth positive volume) lies in `H⁰(X, L^d ⊗ 𝓘(cψ))`. (Lane SKODA-RWN's
`SGPT.TestCurve.SkodaRWN.isMultiplierSection_of_lintegral_lt_top` is the case `c = d = k`; the
proof is the same.) -/
theorem isIdealSection_of_lintegral_lt_top {L : X.Modules} (a : LineBundleAtlas L)
    (H : SchemeLineBundleMetric f n E L)
    {μ : Measure (SchemeComplexPoint f)}
    (hμ : letI := E.isSeparated; letI := E.quasiCompact; IsSmoothPositiveVolume (n := n) μ)
    {ψ : SchemeComplexPoint f → EReal} (hψ : Measurable ψ) {c : ℝ} (hc : 0 < c) {d : ℕ}
    (σ : SectionSpace f L d)
    (hfin : ∫⁻ y, ENNReal.ofReal (H.sectionNormSq a d σ y) *
      multiplierWeight c (ψ y) ∂μ < ⊤) :
    IsIdealSection f n E (multiplierIdeal (n := n) c ψ) d σ := by
  let := E.isSeparated
  let := E.quasiCompact
  intro U α p hp
  set e := complexChartAt (n := n) p with he
  have hpe : p ∈ e.val.source := mem_complexChartAt_source p
  set G : ComplexModel n → ℂ := fun z => sectionFrameCoefficient f n E α d σ (e.val.symm z)
    with hG
  set w : ComplexModel n → ℝ := fun z => H.frameNormSq α (e.val.symm z) with hw
  set D : Set (ComplexModel n) :=
    e.val.target ∩ e.val.symm ⁻¹' (schemeComplexPointImage f ⁻¹' U) with hD
  have hDopen : IsOpen D :=
    e.val.isOpen_inter_preimage_symm (U.isOpen.preimage (schemeComplexPointImage_continuous f))
  have hz0D : e.val p ∈ D := by
    refine ⟨e.val.map_source hpe, ?_⟩
    change schemeComplexPointImage f (e.val.symm (e.val p)) ∈ U
    rw [e.val.left_inv hpe]
    exact hp
  obtain ⟨r₀, hr₀, hr₀D⟩ := Metric.isOpen_iff.mp hDopen _ hz0D
  set r := r₀ / 2 with hr
  have hrpos : 0 < r := half_pos hr₀
  have hcb : closedBall (e.val p) r ⊆ D := fun z hz =>
    hr₀D (lt_of_le_of_lt (mem_closedBall.mp hz) (half_lt_self hr₀))
  obtain ⟨ρ, hρsmooth, hρpos, hmap⟩ := hμ e
  -- lower bounds of the frame weight and of the density on the closed ball
  have hwcont : ContinuousOn w D := (H.smooth α e).continuousOn
  have hwpos : ∀ z ∈ D, 0 < w z := fun z hz => H.positive α _ hz.2
  obtain ⟨zw, hzw, hwmin⟩ := (isCompact_closedBall (e.val p) r).exists_isMinOn
    (nonempty_closedBall.mpr hrpos.le) (hwcont.mono hcb)
  obtain ⟨zρ, hzρ, hρmin⟩ := (isCompact_closedBall (e.val p) r).exists_isMinOn
    (nonempty_closedBall.mpr hrpos.le)
    (hρsmooth.continuousOn.mono fun z hz => (hcb hz).1)
  set cst : ℝ := ρ zρ * w zw ^ d with hcst
  have hcpos : 0 < cst := mul_pos (hρpos _ (hcb hzρ).1) (pow_pos (hwpos _ (hcb hzw)) d)
  -- the integrand on `X` and its density in the chart
  set fM : SchemeComplexPoint f → ℝ≥0∞ := fun y =>
    ENNReal.ofReal (H.sectionNormSq a d σ y) * multiplierWeight c (ψ y) with hfM
  have hWmeas : Measurable fun y => multiplierWeight c (ψ y) :=
    (multiplierWeight_antitone hc.le).measurable.comp hψ
  have hfMmeas : Measurable fM :=
    (ENNReal.continuous_ofReal.comp (SGPT.TestCurve.TestConfig.continuous_sectionNormSq H a d σ)).measurable.mul hWmeas
  set dens := multiplierDensity (chartFunction ψ e) c G with hdens
  have hbound : ∀ z ∈ closedBall (e.val p) r,
      dens z ≤ ENNReal.ofReal cst⁻¹ * (ENNReal.ofReal (ρ z) * fM (e.val.symm z)) := by
    intro z hz
    have hzD := hcb hz
    have hN : H.sectionNormSq a d σ (e.val.symm z) = ‖G z‖ ^ 2 * w z ^ d := by
      rw [H.sectionNormSq_frame a α d σ _ hzD.2, Complex.normSq_eq_norm_sq]
      rfl
    have hρw : cst ≤ ρ z * w z ^ d :=
      mul_le_mul (hρmin hz) (pow_le_pow_left₀ (hwpos _ (hcb hzw)).le (hwmin hz) d)
        (pow_pos (hwpos _ (hcb hzw)) d).le (hρpos _ hzD.1).le
    have hone : (1 : ℝ≥0∞) ≤ ENNReal.ofReal cst⁻¹ * ENNReal.ofReal (ρ z * w z ^ d) := by
      rw [← ENNReal.ofReal_mul (inv_pos.mpr hcpos).le, ← ENNReal.ofReal_one]
      apply ENNReal.ofReal_le_ofReal
      rw [inv_mul_eq_div, le_div_iff₀ hcpos, one_mul]
      exact hρw
    have heq : ENNReal.ofReal cst⁻¹ * (ENNReal.ofReal (ρ z) * fM (e.val.symm z)) =
        (ENNReal.ofReal cst⁻¹ * ENNReal.ofReal (ρ z * w z ^ d)) * dens z := by
      simp only [hfM, hdens, multiplierDensity, chartFunction]
      rw [hN, ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_mul (hρpos _ hzD.1).le]
      ring
    rw [heq]
    calc dens z = 1 * dens z := (one_mul _).symm
      _ ≤ _ := mul_le_mul' hone le_rfl
  refine ⟨schemeOpenRegularFunction_holomorphicAt f n E U _ p hp, hc, ball (e.val p) r,
    isOpen_ball, mem_ball_self hrpos, ?_, ?_, ?_⟩
  · intro z hz
    have hzD : z ∈ D := hcb (ball_subset_closedBall hz)
    exact (FactorizedWeightForm.differentiableAt_comp_chart_symm e hzD.1
      (schemeOpenRegularFunction_holomorphicAt f n E U _ _ hzD.2).self_of_nhds
      ).differentiableWithinAt
  · have hGc : ContinuousOn G (ball (e.val p) r) := by
      intro z hz
      have hzD : z ∈ D := hcb (ball_subset_closedBall hz)
      exact (FactorizedWeightForm.differentiableAt_comp_chart_symm e hzD.1
        (schemeOpenRegularFunction_holomorphicAt f n E U _ _ hzD.2).self_of_nhds
        ).continuousAt.continuousWithinAt
    have h1 : AEMeasurable (fun z => ENNReal.ofReal (‖G z‖ ^ 2))
        (volume.restrict (ball (e.val p) r)) :=
      ENNReal.measurable_ofReal.comp_aemeasurable
        (((continuous_pow 2).comp_continuousOn (continuous_norm.comp_continuousOn hGc)).aemeasurable
          measurableSet_ball)
    have h2 : AEMeasurable (fun z => multiplierWeight c (ψ (e.val.symm z)))
        (volume.restrict (ball (e.val p) r)) :=
      hWmeas.comp_aemeasurable ((e.val.continuousOn_symm.mono fun z hz =>
        (hcb (ball_subset_closedBall hz)).1).aemeasurable measurableSet_ball)
    exact h1.mul h2
  · calc (∫⁻ z in ball (e.val p) r, dens z)
        ≤ ∫⁻ z in closedBall (e.val p) r, dens z := lintegral_mono_set ball_subset_closedBall
      _ ≤ ∫⁻ z in closedBall (e.val p) r,
            ENNReal.ofReal cst⁻¹ * (ENNReal.ofReal (ρ z) * fM (e.val.symm z)) :=
          setLIntegral_mono' isClosed_closedBall.measurableSet hbound
      _ = ENNReal.ofReal cst⁻¹ *
            ∫⁻ z in closedBall (e.val p) r, ENNReal.ofReal (ρ z) * fM (e.val.symm z) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal cst⁻¹ *
            ∫⁻ y in e.val.source ∩ e.val ⁻¹' closedBall (e.val p) r, fM y ∂μ := by
          rw [setLIntegral_source_inter_preimage e hρsmooth.continuousOn hmap
            (isCompact_closedBall _ _) (fun z hz => (hcb hz).1) hfMmeas]
      _ ≤ ENNReal.ofReal cst⁻¹ * ∫⁻ y, fM y ∂μ :=
          mul_le_mul' le_rfl (setLIntegral_le_lintegral _ _)
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin

end Ideal

/-! ### The GAGA map for twisted sections and the multiplier sections -/

section Twisted

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} {E : ClosedProjectiveEmbedding f} {n : ℕ}
  [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f]

local instance okoTw2Topology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance okoTw2Charts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance okoTw2Manifold : IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n
local instance okoTw2Measurable : MeasurableSpace (SchemeComplexPoint f) := borel _
local instance okoTw2Borel : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩

variable {T L : X.Modules} (aT : LineBundleAtlas T) (HT : SchemeLineBundleMetric f n E T)
  (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f n E L) {k : ℕ}

theorem tcoef_add (s t : twistedSections (schemeHermitianLineBundle f n E a H)
      (schemeHermitianLineBundle f n E aT HT) k) (ji : aT.I × a.I) (p : SchemeComplexPoint f) :
    tcoef aT HT a H (s + t) ji p = tcoef aT HT a H s ji p + tcoef aT HT a H t ji p := by
  unfold tcoef
  rw [ContMDiffSection.coe_add, Pi.add_apply, map_add]

theorem tcoef_smul (c : ℂ) (s : twistedSections (schemeHermitianLineBundle f n E a H)
      (schemeHermitianLineBundle f n E aT HT) k) (ji : aT.I × a.I) (p : SchemeComplexPoint f) :
    tcoef aT HT a H (c • s) ji p = c * tcoef aT HT a H s ji p := by
  unfold tcoef
  rw [ContMDiffSection.coe_smul, Pi.smul_apply, map_smul, smul_eq_mul]

/-- `(s + t)^alg = s^alg + t^alg`. -/
theorem isTwistedAnalytificationOf_add
    {s t : twistedSections (schemeHermitianLineBundle f n E a H)
      (schemeHermitianLineBundle f n E aT HT) k}
    {σ τ : SectionSpace f (bundleTensor T (bundleTensorPower L k)) 1}
    (hs : IsTwistedAnalytificationOf aT HT a H s σ)
    (ht : IsTwistedAnalytificationOf aT HT a H t τ) :
    IsTwistedAnalytificationOf aT HT a H (s + t)
      (σ + τ : SectionSpace f (bundleTensor T (bundleTensorPower L k)) 1) := by
  intro ji p hp
  have hadd : algCoef ((pairwiseTensorAtlas aT (a.tensorPower k)).frame ji) 1
      (σ + τ : SectionSpace f (bundleTensor T (bundleTensorPower L k)) 1) =
      algCoef ((pairwiseTensorAtlas aT (a.tensorPower k)).frame ji) 1 σ +
        algCoef ((pairwiseTensorAtlas aT (a.tensorPower k)).frame ji) 1 τ := by
    simp only [algCoef, map_add]
  rw [hadd, schemeOpenRegularFunction_add f n E _ _ _ hp, tcoef_add, hs ji p hp, ht ji p hp]

/-- `(c • s)^alg = c • s^alg`. -/
theorem isTwistedAnalytificationOf_smul (c : ℂ)
    {s : twistedSections (schemeHermitianLineBundle f n E a H)
      (schemeHermitianLineBundle f n E aT HT) k}
    {σ : SectionSpace f (bundleTensor T (bundleTensorPower L k)) 1}
    (hs : IsTwistedAnalytificationOf aT HT a H s σ) :
    IsTwistedAnalytificationOf aT HT a H (c • s)
      (c • σ : SectionSpace f (bundleTensor T (bundleTensorPower L k)) 1) := by
  intro ji p hp
  have hsm : algCoef ((pairwiseTensorAtlas aT (a.tensorPower k)).frame ji) 1
      (c • σ : SectionSpace f (bundleTensor T (bundleTensorPower L k)) 1) =
      X.presheaf.map (homOfLE (le_top :
        (pairwiseTensorAtlas aT (a.tensorPower k)).opens ji ≤ ⊤)).op (schemeGlobalConstants f c) *
        algCoef ((pairwiseTensorAtlas aT (a.tensorPower k)).frame ji) 1 σ :=
    SectionSpace.atlasPowerGlobalCoefficients_smul_const f
      (pairwiseTensorAtlas aT (a.tensorPower k)) 1 ji c σ
  rw [hsm, schemeOpenRegularFunction_mul' f E n _ _ _ hp,
    schemeOpenRegularFunction_globalConstant _ c hp, tcoef_smul, hs ji p hp]

variable [CompactSpace (SchemeComplexPoint f)]

/-- **The algebraic section `s^alg ∈ H⁰(X, T ⊗ L^k)`** of a holomorphic section `s` of
`twistedPower(L^an, T^an, k)` (GAGA). -/
def twistedAlgSection (s : twistedSections (schemeHermitianLineBundle f n E a H)
    (schemeHermitianLineBundle f n E aT HT) k) :
    SectionSpace f (bundleTensor T (bundleTensorPower L k)) 1 :=
  Classical.choose (exists_isTwistedAnalytificationOf aT HT a H s)

theorem isTwistedAnalytificationOf_twistedAlgSection
    (s : twistedSections (schemeHermitianLineBundle f n E a H)
      (schemeHermitianLineBundle f n E aT HT) k) :
    IsTwistedAnalytificationOf aT HT a H s (twistedAlgSection aT HT a H s) :=
  Classical.choose_spec (exists_isTwistedAnalytificationOf aT HT a H s)

/-- The GAGA map `s ↦ s^alg` for the twisted bundles is `ℂ`-linear. -/
def twistedAlgSectionLinear :
    twistedSections (schemeHermitianLineBundle f n E a H) (schemeHermitianLineBundle f n E aT HT) k
      →ₗ[ℂ] SectionSpace f (bundleTensor T (bundleTensorPower L k)) 1 where
  toFun := twistedAlgSection aT HT a H
  map_add' s t := eq_of_isTwistedAnalytificationOf aT HT a H
    (isTwistedAnalytificationOf_twistedAlgSection aT HT a H (s + t))
    (isTwistedAnalytificationOf_add aT HT a H (isTwistedAnalytificationOf_twistedAlgSection aT HT a H s)
      (isTwistedAnalytificationOf_twistedAlgSection aT HT a H t))
  map_smul' c s := eq_of_isTwistedAnalytificationOf aT HT a H
    (isTwistedAnalytificationOf_twistedAlgSection aT HT a H (c • s))
    (isTwistedAnalytificationOf_smul aT HT a H c
      (isTwistedAnalytificationOf_twistedAlgSection aT HT a H s))

/-- The GAGA map `s ↦ s^alg` for the twisted bundles is injective. -/
theorem twistedAlgSectionLinear_injective :
    Function.Injective (twistedAlgSectionLinear aT HT a H (k := k)) := by
  rw [injective_iff_map_eq_zero]
  intro s hs
  have h0 : IsTwistedAnalytificationOf aT HT a H s
      (0 : SectionSpace f (bundleTensor T (bundleTensorPower L k)) 1) :=
    hs ▸ isTwistedAnalytificationOf_twistedAlgSection aT HT a H s
  apply ContMDiffSection.ext
  intro p
  obtain ⟨j, hj⟩ := aT.covers (schemeComplexPointImage f p)
  obtain ⟨i, hi⟩ := a.covers (schemeComplexPointImage f p)
  have hp : schemeComplexPointImage f p ∈ (pairwiseTensorAtlas aT (a.tensorPower k)).opens (j, i) :=
    ⟨hj, hi⟩
  set e := twistAnFrame aT HT a H (j, i) k
  have he : p ∈ e.val.baseSet := mem_twistAnFrame_baseSet aT HT a H k hp
  have hc := h0 (j, i) p hp
  have halg0 : algCoef ((pairwiseTensorAtlas aT (a.tensorPower k)).frame (j, i)) 1
      (0 : SectionSpace f (bundleTensor T (bundleTensorPower L k)) 1) = 0 := by
    simp only [algCoef, map_zero]
  rw [halg0, schemeOpenRegularFunction_zero' f E n _ p hp] at hc
  unfold tcoef at hc
  rw [← Trivialization.coe_continuousLinearEquivAt_eq e.val he] at hc
  rw [ContMDiffSection.coe_zero, Pi.zero_apply]
  exact (e.val.continuousLinearEquivAt ℂ p he).map_eq_zero_iff.mp hc

omit [CompactSpace (SchemeComplexPoint f)] in
/-- **`|s|² = |s^alg|²_{h_T ⊗ h^k}`**: the analytic norm of a holomorphic twisted section is the
norm of its algebraic section for the product metric `h_T ⊗ h^k` on `T ⊗ L^k`. -/
theorem norm_sq_eq_sectionNormSq_twist
    {s : twistedSections (schemeHermitianLineBundle f n E a H)
      (schemeHermitianLineBundle f n E aT HT) k}
    {σ : SectionSpace f (bundleTensor T (bundleTensorPower L k)) 1}
    (hσ : IsTwistedAnalytificationOf aT HT a H s σ) (p : SchemeComplexPoint f) :
    ‖s p‖ ^ 2 = (HT.tensorProduct (H.tensorPower a k) aT (a.tensorPower k)).sectionNormSq
      (pairwiseTensorAtlas aT (a.tensorPower k)) 1 σ p := by
  obtain ⟨j, hj⟩ := aT.covers (schemeComplexPointImage f p)
  obtain ⟨i, hi⟩ := a.covers (schemeComplexPointImage f p)
  have hp : schemeComplexPointImage f p ∈ (pairwiseTensorAtlas aT (a.tensorPower k)).opens (j, i) :=
    ⟨hj, hi⟩
  have hcoef := hσ (j, i) p hp
  have hmem := mem_twistAnFrame_baseSet aT HT a H k hp
  have hlin : tcoef aT HT a H s (j, i) p =
      ((twistAnFrame aT HT a H (j, i) k).val ⟨p, s p⟩).2 :=
    Trivialization.continuousLinearMapAt_apply_of_mem (R := ℂ) _ hmem (s p)
  rw [twistedSection_norm_sq_frame (schemeHermitianAtlasFrame f n E a H (a.frame i))
      (schemeHermitianAtlasFrame f n E aT HT (aT.frame j)) k s hi hj,
    schemeHermitianAtlasFrame_norm_sq f n E a H _ hi,
    schemeHermitianAtlasFrame_norm_sq f n E aT HT _ hj,
    SchemeLineBundleMetric.sectionNormSq_frame _ (pairwiseTensorAtlas aT (a.tensorPower k))
      ((pairwiseTensorAtlas aT (a.tensorPower k)).frame (j, i)) 1 σ p hp]
  change ‖((twistAnFrame aT HT a H (j, i) k).val ⟨p, s p⟩).2‖ ^ 2 * _ * _ =
    Complex.normSq (schemeOpenRegularFunction f n E
      ((pairwiseTensorAtlas aT (a.tensorPower k)).opens (j, i))
      (algCoef ((pairwiseTensorAtlas aT (a.tensorPower k)).frame (j, i)) 1 σ) p) *
      (HT.tensorProduct (H.tensorPower a k) aT (a.tensorPower k)).frameNormSq
        ((leftRestrictedFrame aT (a.tensorPower k) (j, i)).tensor
          (rightRestrictedFrame aT (a.tensorPower k) (j, i))) p ^ 1
  rw [← hcoef, ← hlin, SchemeLineBundleMetric.tensorProduct_frame _ _ _ _ _ _ p hp]
  have hl : HT.frameNormSq (leftRestrictedFrame aT (a.tensorPower k) (j, i)) p =
      HT.frameNormSq (aT.frame j) p :=
    frameNormSq_bundleHomRestrictionIso f n E HT (aT.frame j) inf_le_left p hp
  have hr : (H.tensorPower a k).frameNormSq (rightRestrictedFrame aT (a.tensorPower k) (j, i)) p =
      H.frameNormSq (a.frame i) p ^ k := by
    exact (frameNormSq_bundleHomRestrictionIso f n E (H.tensorPower a k)
      ((a.tensorPower k).frame i) inf_le_right p hp).trans (H.tensorPower_frame a (a.frame i) k p hi)
  rw [hl, hr, Complex.normSq_eq_norm_sq]
  ring

/-- **Finite-`L²` holomorphic twisted sections are algebraic multiplier sections**: if
`∫_X |s|² e^{-kφ} dμ < ∞` (`s` in the literal section space of `def:Bergman:L778` for
`T^an ⊗ (L^an)^k`), then `s^alg ∈ H⁰(X, T ⊗ L^k ⊗ 𝓘(kφ))`. -/
theorem mem_twistedMultiplierSubmodule_twistedAlgSection {φ : SchemeComplexPoint f → EReal}
    (hφ : IsThetaPshPotential (H.curvature a).val φ) {μ : Measure (SchemeComplexPoint f)}
    (hμ : IsSmoothPositiveVolume (n := n) μ)
    {s : twistedSections (schemeHermitianLineBundle f n E a H)
      (schemeHermitianLineBundle f n E aT HT) k}
    (hs : ∫⁻ x, originalSectionDensity (n := n)
      (twistedPower (schemeHermitianLineBundle f n E a H)
        (schemeHermitianLineBundle f n E aT HT) k).Fiber φ k s x ∂μ < ⊤) :
    twistedAlgSection aT HT a H s ∈
      SGPT.IGood.DXMain.twistedMultiplierSubmodule f n E hφ.1.quasiPlurisubharmonic T L k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact Or.inl rfl
  refine Or.inr (isIdealSection_of_lintegral_lt_top (pairwiseTensorAtlas aT (a.tensorPower k))
    (HT.tensorProduct (H.tensorPower a k) aT (a.tensorPower k)) hμ
    hφ.1.quasiPlurisubharmonic.upperSemicontinuous.measurable (by exact_mod_cast hk) _ ?_)
  have hn := norm_sq_eq_sectionNormSq_twist aT HT a H
    (isTwistedAnalytificationOf_twistedAlgSection aT HT a H s)
  simp only [originalSectionDensity, hn] at hs
  exact hs

/-- **`dim Γ(X, T ⊗ L^k ⊗ 𝓘(kφ))^{an} ≤ h⁰(X, T ⊗ L^k ⊗ 𝓘(kφ))`**: the literal analytic section
space of `def:Bergman:L778` for `T^an ⊗ (L^an)^k` (the `h⁰`) injects into the
algebraic twisted multiplier sections of lane DXMAIN. -/
theorem finrank_literal_le_twistedMultiplierH0 {φ : SchemeComplexPoint f → EReal}
    (hφ : IsThetaPshPotential (H.curvature a).val φ) (k : ℕ) :
    Module.finrank ℂ (LiteralTwistedMultiplierSections (schemeHermitianLineBundle f n E a H)
      (schemeHermitianLineBundle f n E aT HT) k φ) ≤
      SGPT.IGood.DXMain.twistedMultiplierH0 f n E hφ.1.quasiPlurisubharmonic T L k := by
  let ωb := schemeProjectiveTNKahlerBackground f n E
  let μ := IntegrationCurrent.kahlerVolume ωb
  have hμ : IsSmoothPositiveVolume (n := n) μ :=
    KahlerVolumeSmoothPositive.isSmoothPositiveVolume_kahlerVolume ωb
  have hq : IsGlobalQuasiPshPotential (n := n) φ := ⟨hφ.1.quasiPlurisubharmonic, hφ.2⟩
  rw [(literalTwistedMultiplierL2Equiv _ _ k hq μ hμ).finrank_eq]
  let W := twistedMultiplierL2Submodule (schemeHermitianLineBundle f n E a H)
    (schemeHermitianLineBundle f n E aT HT) k hq μ hμ
  let Φ : W →ₗ[ℂ] SGPT.IGood.DXMain.twistedMultiplierSubmodule f n E
      hφ.1.quasiPlurisubharmonic T L k :=
    ((twistedAlgSectionLinear aT HT a H).domRestrict W).codRestrict _
      (fun s => mem_twistedMultiplierSubmodule_twistedAlgSection aT HT a H hφ hμ s.2)
  have : FiniteDimensional ℂ (SectionSpace f (bundleTensor T (bundleTensorPower L k)) 1) :=
    SectionSpace.finiteDimensional f E (pairwiseTensorAtlas aT (a.tensorPower k)) 1
  refine LinearMap.finrank_le_finrank_of_injective (f := Φ) fun s t hst => ?_
  apply Subtype.ext
  apply twistedAlgSectionLinear_injective aT HT a H
  exact congrArg Subtype.val hst

end Twisted

end SGPT.GAGA.OkoClose
