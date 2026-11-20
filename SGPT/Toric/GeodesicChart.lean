import SGPT.Toric.BigToricCorrespondence
import SGPT.PSH.SourceSubgeodesic
import SGPT.Foundations.Analysis.Pending.FiniteGeodesicMaximality
import SGPT.Foundations.Analysis.Pending.PshAnalyticRemovable

/-!
# Tropical charts of complexified toric subgeodesics

Source `chapter_toric_big.tex`, proof of `prop:toricsubgeod`: the complexification of a
`T_c`-invariant family `(φ_t)_{t ∈ (0,1)}` is, on `T(ℂ) × S` in a vertex chart, a function of
`(Trop, Re τ)`, and it is plurisubharmonic exactly when the corresponding function on
`N_ℝ × (0,1)` is convex ("the same computation as in `lma:convextopsh`").  We use the strip
convention of `def:subgeod` (`S = {0 < Re τ < 1}`, `Φ(x, τ) = φ_{Re τ}(x)`), which is the one of the
formal subgeodesic definition; the annulus convention of the printed proof is equivalent
(`rmk:complexify1`).

## Main results

* `SGPT.Toric.plurisubharmonicOn_tropical_strip`: `K` convex on `ℝⁿ × (0,1)` gives
  `(z, τ) ↦ K(Trop z, Re τ)` plurisubharmonic on `T(ℂ) × S`;
* `SGPT.Toric.convexOn_of_plurisubharmonicOn_tropical_strip`: the converse;
* `SGPT.Toric.eq_of_plurisubharmonicOn_of_eqOn_complexTorus`: two psh functions on `ℂⁿ`
  agreeing on the torus coincide;
* `SGPT.Toric.BigToricMetric.convexOn_profile_of_jointThetaPSH`: the profiles of a
  `T_c`-invariant family with `p₁^*θ`-psh complexification are jointly convex;
* `SGPT.Toric.BigToricMetric.plurisubharmonicOn_vertexChart_strip`: conversely, a family of
  toric `θ`-psh functions with jointly convex profiles and a uniform upper bound has
  plurisubharmonic corrected complexification in every vertex chart (the boundary
  `(X ∖ T) × S` is removed by the bounded analytic extension theorem, `thm:GRexten`).
-/

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set Filter SGPT.PSH SGPT.PSH.VariableComplexAtlas SGPT.Convex
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology ContDiff BigOperators

/-! ### Flat lemmas -/

section Flat

variable {n : ℕ}

/-- `twiceRealCoordinates` as a real-linear map. -/
def twiceRealLinear : ComplexModel n →ₗ[ℝ] EuclideanSpace ℝ (Fin n) where
  toFun := twiceRealCoordinates
  map_add' x y := by
    simpa only [one_smul] using twiceRealCoordinates_combo x y 1 1
  map_smul' c x := by
    simpa only [zero_smul, add_zero, smul_zero, RingHom.id_apply] using
      twiceRealCoordinates_combo x 0 c 0

/-- The real-linear map `(ζ, τ) ↦ (2 Re ζ, Re τ)`. -/
def twiceRealTimeLinear : ComplexModel n × ℂ →ₗ[ℝ] EuclideanSpace ℝ (Fin n) × ℝ :=
  (twiceRealLinear.comp (LinearMap.fst ℝ (ComplexModel n) ℂ)).prod
    (Complex.reLm.comp (LinearMap.snd ℝ (ComplexModel n) ℂ))

theorem twiceRealTimeLinear_apply (p : ComplexModel n × ℂ) :
    twiceRealTimeLinear p = (twiceRealCoordinates p.1, p.2.re) := rfl

theorem twiceRealTimeLinear_preimage :
    (twiceRealTimeLinear (n := n)) ⁻¹' (univ ×ˢ Ioo (0 : ℝ) 1) =
      (univ : Set (ComplexModel n)) ×ˢ complexTimeStrip := by
  ext p
  simp only [mem_preimage, twiceRealTimeLinear_apply, mem_prod, mem_univ, true_and, mem_Ioo,
    mem_complexTimeStrip]

/-- A convex function of `(2 Re ζ, Re τ)` is plurisubharmonic on `ℂⁿ × S`. -/
theorem plurisubharmonicOn_twiceReal_strip {K : EuclideanSpace ℝ (Fin n) × ℝ → ℝ}
    (hK : ConvexOn ℝ (univ ×ˢ Ioo (0 : ℝ) 1) K) :
    PlurisubharmonicOn (fun p : ComplexModel n × ℂ => (K (twiceRealCoordinates p.1, p.2.re) : EReal))
      (univ ×ˢ complexTimeStrip) := by
  let L := Pending.FiniteGeodesicMaximality.stripModelEquiv n
  let A : ComplexModel (n + 1) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) × ℝ :=
    twiceRealTimeLinear.comp ((L : ComplexModel (n + 1) →L[ℂ] ComplexModel n × ℂ).toLinearMap.restrictScalars ℝ)
  have hpre : A ⁻¹' (univ ×ˢ Ioo (0 : ℝ) 1) = L ⁻¹' (univ ×ˢ complexTimeStrip) := by
    ext q
    change twiceRealTimeLinear (L q) ∈ (univ ×ˢ Ioo (0 : ℝ) 1 : Set (EuclideanSpace ℝ (Fin n) × ℝ)) ↔
      L q ∈ ((univ : Set (ComplexModel n)) ×ˢ complexTimeStrip)
    rw [← twiceRealTimeLinear_preimage]
    rfl
  have hconv : ConvexOn ℝ (L ⁻¹' (univ ×ˢ complexTimeStrip)) (K ∘ A) := by
    rw [← hpre]
    exact hK.comp_linearMap A
  have hopen : IsOpen (L ⁻¹' (univ ×ˢ complexTimeStrip)) :=
    (isOpen_univ.prod isOpen_complexTimeStrip).preimage L.continuous
  have hpsh := Pending.plurisubharmonicOn_of_convexOn hopen hconv (hconv.continuousOn hopen)
  have hback := Pending.FiniteGeodesicMaximality.plurisubharmonicOn_comp_stripModelEquiv_symm hpsh
  have hset : (L.symm : ComplexModel n × ℂ → ComplexModel (n + 1)) ⁻¹'
      (L ⁻¹' ((univ : Set (ComplexModel n)) ×ˢ complexTimeStrip)) =
        (univ : Set (ComplexModel n)) ×ˢ complexTimeStrip := by
    ext p; simp
  rw [hset] at hback
  intro p hp
  apply (hback p hp).congr
  filter_upwards with q
  change (K (A (L.symm q)) : EReal) = _
  congr 2
  change twiceRealTimeLinear (L (L.symm q)) = _
  rw [ContinuousLinearEquiv.apply_symm_apply]
  rfl

/-- Source `lma:convextopsh` with time: a convex function `K` on `ℝⁿ × (0,1)` gives the
plurisubharmonic function `(z, τ) ↦ K(Trop z, Re τ)` on `T(ℂ) × S`. -/
theorem plurisubharmonicOn_tropical_strip {K : EuclideanSpace ℝ (Fin n) × ℝ → ℝ}
    (hK : ConvexOn ℝ (univ ×ˢ Ioo (0 : ℝ) 1) K) :
    PlurisubharmonicOn (fun p : ComplexModel n × ℂ => (K (tropicalization p.1, p.2.re) : EReal))
      (complexTorus n ×ˢ complexTimeStrip) := by
  rintro ⟨z, τ⟩ ⟨hz, hτ⟩
  let F : ComplexModel n × ℂ → ComplexModel n × ℂ := fun p => (localToricLog z p.1, p.2)
  let U : Set (ComplexModel n × ℂ) := toricLogDomain z ×ˢ complexTimeStrip
  have hU : IsOpen U := (isOpen_toricLogDomain z).prod isOpen_complexTimeStrip
  have hF : DifferentiableOn ℂ F U := by
    apply DifferentiableOn.prodMk
    · exact (differentiableOn_localToricLog z).comp differentiableOn_fst (fun p hp => hp.1)
    · exact differentiableOn_snd
  have hmaps : MapsTo F U (univ ×ˢ complexTimeStrip) := fun p hp => ⟨mem_univ _, hp.2⟩
  have hraw := Pending.FiniteGeodesicMaximality.plurisubharmonicOn_comp_holomorphic_strip hU hF hmaps
    (plurisubharmonicOn_twiceReal_strip hK)
  have hzU : (z, τ) ∈ U := ⟨self_mem_toricLogDomain hz, hτ⟩
  apply (hraw (z, τ) hzU).congr
  filter_upwards [hU.mem_nhds hzU] with p hp
  change (K (twiceRealCoordinates (localToricLog z p.1), p.2.re) : EReal) = _
  rw [twiceRealCoordinates_localToricLog hz hp.1]

/-- The converse direction of `plurisubharmonicOn_tropical_strip`: if
`(z, τ) ↦ K(Trop z, Re τ)` is plurisubharmonic on `T(ℂ) × S`, then `K` is convex on
`ℝⁿ × (0,1)` (restrict to the holomorphic exponential lines and use the chord
inequality of subharmonic functions of `Re`). -/
theorem convexOn_of_plurisubharmonicOn_tropical_strip {K : EuclideanSpace ℝ (Fin n) × ℝ → ℝ}
    (hK : PlurisubharmonicOn
      (fun p : ComplexModel n × ℂ => (K (tropicalization p.1, p.2.re) : EReal))
      (complexTorus n ×ˢ complexTimeStrip)) :
    ConvexOn ℝ (univ ×ˢ Ioo (0 : ℝ) 1) K := by
  have hcvx : Convex ℝ (univ ×ˢ Ioo (0 : ℝ) 1 : Set (EuclideanSpace ℝ (Fin n) × ℝ)) :=
    convex_univ.prod (convex_Ioo 0 1)
  refine ⟨hcvx, ?_⟩
  rintro ⟨x₀, s₀⟩ ⟨-, hs₀⟩ ⟨x₁, s₁⟩ ⟨-, hs₁⟩ a b ha hb hab
  by_cases hb0 : b = 0
  · have ha1 : a = 1 := by linarith
    simp [hb0, ha1]
  by_cases ha0 : a = 0
  · have hb1 : b = 1 := by linarith
    simp [ha0, hb1]
  have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
  have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  have hb1 : b < 1 := by linarith
  -- the holomorphic line through the two points
  let ℓ : ℂ → ComplexModel n × ℂ := fun w =>
    (tropicalExponentialLine x₀ x₁ w, (s₀ : ℂ) + w * ((s₁ - s₀ : ℝ) : ℂ))
  let I : Set ℝ := (fun r : ℝ => s₀ + r * (s₁ - s₀)) ⁻¹' Ioo (0 : ℝ) 1
  have hIopen : IsOpen I := isOpen_Ioo.preimage (by fun_prop)
  have hIcc : Icc (0 : ℝ) 1 ⊆ I := by
    intro r hr
    change s₀ + r * (s₁ - s₀) ∈ Ioo (0 : ℝ) 1
    have he : s₀ + r * (s₁ - s₀) = (1 - r) * s₀ + r * s₁ := by ring
    rw [he]
    constructor
    · rcases hr.1.eq_or_lt with h0 | h0
      · rw [← h0]; simpa using hs₀.1
      · nlinarith [hs₀.1, hs₁.1, hr.2]
    · rcases hr.2.eq_or_lt with h1 | h1
      · rw [h1]; simpa using hs₁.2
      · nlinarith [hs₀.2, hs₁.2, hr.1]
  have hℓre (w : ℂ) : (ℓ w).2.re = s₀ + w.re * (s₁ - s₀) := by
    simp only [ℓ, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, mul_zero,
      sub_zero]
  have hℓmaps (w : ℂ) (hw : w.re ∈ I) : ℓ w ∈ complexTorus n ×ˢ complexTimeStrip := by
    refine ⟨tropicalExponentialLine_mem_complexTorus x₀ x₁ w, ?_⟩
    change 0 < (ℓ w).2.re ∧ (ℓ w).2.re < 1
    rw [hℓre]
    exact hw
  -- composition, through the models `ℂ¹` and `ℂⁿ⁺¹`
  let Lm := Pending.FiniteGeodesicMaximality.stripModelEquiv n
  let Ψ : ComplexModel n × ℂ → EReal :=
    fun p => (K (tropicalization p.1, p.2.re) : EReal)
  have hΨ := Pending.FiniteGeodesicMaximality.plurisubharmonicOn_comp_stripModelEquiv hK
  let G : ComplexModel 1 → ComplexModel (n + 1) := fun q => Lm.symm (ℓ (q 0))
  have hG : Differentiable ℂ G := by
    have h1 : Differentiable ℂ ℓ := by
      apply Differentiable.prodMk (differentiable_tropicalExponentialLine x₀ x₁)
      fun_prop
    exact Lm.symm.differentiable.comp (h1.comp (by fun_prop))
  let U : Set (ComplexModel 1) := {q | (q 0).re ∈ I}
  have hUo : IsOpen U := hIopen.preimage (by fun_prop)
  have hcomp := Pending.HolomorphicPullback.plurisubharmonicOn_comp_holomorphic hUo
    hG.differentiableOn
    (V := Lm ⁻¹' (complexTorus n ×ˢ complexTimeStrip))
    (fun q hq => by
      change Lm (Lm.symm (ℓ (q 0))) ∈ complexTorus n ×ˢ complexTimeStrip
      rw [ContinuousLinearEquiv.apply_symm_apply]
      exact hℓmaps (q 0) hq) hΨ
  let Lc : ℂ →L[ℂ] ComplexModel 1 :=
    (ContinuousLinearMap.id ℂ ℂ).smulRight (WithLp.toLp 2 (fun _ : Fin 1 ↦ (1 : ℂ)))
  have hLc (w : ℂ) : Lc w 0 = w := by simp [Lc]
  have hline := hcomp.comp_continuousLinearMap Lc
  let v : ℝ → EReal := fun r => (K (x₀ + r • (x₁ - x₀), s₀ + r * (s₁ - s₀)) : EReal)
  have hv : PlurisubharmonicOn (fun w : ℂ => v w.re) (Complex.re ⁻¹' I) := by
    have hset : (Lc : ℂ → ComplexModel 1) ⁻¹' U = Complex.re ⁻¹' I := by
      ext w; simp [U, hLc]
    rw [hset] at hline
    intro w hw
    apply (hline w hw).congr
    filter_upwards with w'
    change Ψ (Lm (Lm.symm (ℓ (Lc w' 0)))) = v w'.re
    rw [ContinuousLinearEquiv.apply_symm_apply, hLc]
    simp only [Ψ, v, hℓre]
    rw [show (ℓ w').1 = tropicalExponentialLine x₀ x₁ w' from rfl,
      tropicalization_tropicalExponentialLine]
  have hchord := hv.comp_re_toReal_le_affine_chord (a := 0) (t := b) (b := 1) hbpos hb1 hIcc
    (EReal.coe_ne_top _) (EReal.coe_ne_bot _) (EReal.coe_ne_top _) (EReal.coe_ne_bot _)
    (EReal.coe_ne_top _) (EReal.coe_ne_bot _)
  simp only [v, EReal.toReal_coe, zero_smul, add_zero, zero_mul, one_smul, one_mul, sub_zero,
    div_one, add_sub_cancel] at hchord
  have hpt : ((x₀ + b • (x₁ - x₀), s₀ + b * (s₁ - s₀)) : EuclideanSpace ℝ (Fin n) × ℝ) =
      a • (x₀, s₀) + b • (x₁, s₁) := by
    have haeq : a = 1 - b := by linarith
    rw [haeq]
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_add, Prod.smul_fst]
      module
    · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
      ring
  rw [hpt] at hchord
  simp only [smul_eq_mul]
  have haeq : a = 1 - b := by linarith
  rw [haeq] at hchord ⊢
  linarith

/-- The coordinate torus has full Lebesgue measure. -/
theorem ae_mem_complexTorus_volume : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure (ComplexModel n)),
    z ∈ complexTorus n := by
  have h := Pending.HolomorphicZeroSetNull.measure_inter_preimage_zero_eq_zero
    MeasureTheory.volume isOpen_univ (convex_univ : Convex ℝ (univ : Set (ComplexModel n)))
    (differentiable_originalPolytopeNativeBoundaryPolynomial n).differentiableOn
    (x₁ := (originalPolytopeNativeModelEquiv n).symm (fun _ => 1)) (mem_univ _)
    (by rw [originalPolytopeNativeBoundaryPolynomial_one]; exact one_ne_zero)
  rw [MeasureTheory.ae_iff]
  refine MeasureTheory.measure_mono_null ?_ h
  intro z hz
  refine ⟨mem_univ z, ?_⟩
  change originalPolytopeNativeBoundaryPolynomial n z = 0
  by_contra hne
  exact hz ((originalPolytopeNativeBoundaryPolynomial_ne_zero_iff z).mp hne)

/-- `prop:pshfuncdetdense` on `ℂⁿ`: two plurisubharmonic functions on `ℂⁿ` that agree on the
torus `(ℂ^*)ⁿ` (and are not identically `-∞`) coincide. -/
theorem eq_of_plurisubharmonicOn_of_eqOn_complexTorus {u w : ComplexModel n → EReal}
    (hu : PlurisubharmonicOn u univ) (hw : PlurisubharmonicOn w univ)
    (heq : EqOn u w (complexTorus n)) {z₀ : ComplexModel n} (hz₀ : z₀ ∈ complexTorus n)
    (hfin : u z₀ ≠ ⊥) : u = w := by
  have hconn : IsConnected (univ : Set (ComplexModel n)) := isConnected_univ
  have hpsh (f : ComplexModel n → EReal) (hf : PlurisubharmonicOn f univ) (hf0 : f z₀ ≠ ⊥) :
      (identityAtlas n).IsPSH f := by
    intro x
    refine ⟨(), mem_univ x, univ, isOpen_univ, hconn, subset_univ _, mem_univ _, ?_⟩
    exact ⟨hf.discPshOn, z₀, mem_univ _, hf0⟩
  apply IsPSH.eq_of_coordinateAEEq (hpsh u hu hfin) (hpsh w hw (by rwa [← heq hz₀]))
  intro i
  filter_upwards [MeasureTheory.ae_restrict_of_ae ae_mem_complexTorus_volume] with z hz
  exact heq hz

end Flat

/-! ### Vertex charts of a big toric metric -/

variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- The function on `N_ℝ × ℝ` read in the vertex chart at `v`:
`K_v(y, s) = F_s(L_v⁻¹ y) - ⟨m_v, L_v⁻¹ y⟩`, where `L_v` is the edge basis change. -/
def toricVertexStripFunction (D : ToricDivisor γ hs) (f : ℝ → EuclideanSpace ℝ (Fin n) → ℝ)
    (v : latticePolytopeVertices γ) (p : EuclideanSpace ℝ (Fin n) × ℝ) : ℝ :=
  f p.2 (latticeBasisLogInverse (originalPolytopeNativeBasis γ hs v) p.1) -
    latticeFunctional (toricCartierDatum D v)
      (latticeBasisLogInverse (originalPolytopeNativeBasis γ hs v) p.1)

/-- The base-chart function `K_w` recovers `F` by `F(x, s) = K_w(L_w x, s) + ⟨m_w, x⟩`. -/
theorem toricVertexStripFunction_logMap (D : ToricDivisor γ hs)
    (f : ℝ → EuclideanSpace ℝ (Fin n) → ℝ)
    (v : latticePolytopeVertices γ) (p : EuclideanSpace ℝ (Fin n) × ℝ) :
    f p.2 p.1 = toricVertexStripFunction D f v
        (latticeBasisLogMap (originalPolytopeNativeBasis γ hs v) p.1, p.2) +
      latticeFunctional (toricCartierDatum D v) p.1 := by
  simp only [toricVertexStripFunction, latticeBasisLogInverse_logMap, sub_add_cancel]

namespace BigToricMetric

variable {D : ToricDivisor γ hs} (h : BigToricMetric D)

/-- On `T(ℂ) × S`, the corrected complexification in the vertex chart at `v` of a
`T_c`-invariant family with real profiles `F_s` is `K_v(Trop z, Re τ)`. -/
theorem subgeodesicChartFunction_eq_vertexStrip {curve : ℝ → PolytopeToricVariety γ hs → EReal}
    {f : ℝ → EuclideanSpace ℝ (Fin n) → ℝ}
    (hinv : ∀ s ∈ Ioo (0 : ℝ) 1, PolytopeToricInvariant γ hs (curve s))
    (hprof : ∀ s ∈ Ioo (0 : ℝ) 1, h.profile (curve s) = fun x => (f s x : EReal))
    (v : latticePolytopeVertices γ) {p : ComplexModel n × ℂ}
    (hp : p ∈ complexTorus n ×ˢ complexTimeStrip) :
    subgeodesicChartFunction curve (polytopeToricVertexChart γ hs v) (h.weight v) p =
      (toricVertexStripFunction D f v (tropicalization p.1, p.2.re) : EReal) := by
  obtain ⟨hz, hτ⟩ := hp
  have hs' : p.2.re ∈ Ioo (0 : ℝ) 1 := hτ
  have hc := h.vertexChart_corrected_eq (u := curve p.2.re)
    (fun a => (hinv _ hs').embedding_eq γ hs a) v hz
  change curve p.2.re ((originalPolytopeNativeModelChart γ hs v).symm p.1) +
    (h.weight v p.1 : EReal) = _
  rw [hc, hprof _ hs']
  simp only [tropicalPullback, toricVertexStripFunction, sub_eq_add_neg, EReal.coe_add]

/-- The local potential `ψ_v` of `θ` on the whole vertex chart, in the native form. -/
theorem isSmoothLocalPotential_weight (v : latticePolytopeVertices γ) :
    IsSmoothLocalPotential (atlasClosedFormToNative h.atlasForm).val
      (polytopeToricVertexChart γ hs v) univ (h.weight v) :=
  ⟨isOpen_univ, (polytopeToric_chart_target γ hs (polytopeToricVertexChart γ hs v)).symm.subset,
    (h.smooth v).contDiffOn,
    fun z _ => (h.coeff v z).symm⟩

/-- Forward half of the chart computation in `prop:toricsubgeod`: if the complexification of
a `T_c`-invariant family with real profiles `F_s` is `p₁^*θ`-psh, then
`(x, s) ↦ F_s(x)` is convex on `N_ℝ × (0,1)`. -/
theorem convexOn_profile_of_jointThetaPSH {curve : ℝ → PolytopeToricVariety γ hs → EReal}
    {f : ℝ → EuclideanSpace ℝ (Fin n) → ℝ}
    (hjoint : SourceJointThetaPSH h.atlasForm curve)
    (hinv : ∀ s ∈ Ioo (0 : ℝ) 1, PolytopeToricInvariant γ hs (curve s))
    (hprof : ∀ s ∈ Ioo (0 : ℝ) 1, h.profile (curve s) = fun x => (f s x : EReal)) :
    ConvexOn ℝ (univ ×ˢ Ioo (0 : ℝ) 1) (fun p : EuclideanSpace ℝ (Fin n) × ℝ => f p.2 p.1) := by
  let w := polytopeToricBaseVertex γ
  have hpsh := sourceJointThetaPSH_corrected hjoint (polytopeToricVertexChart γ hs w)
    (h.isSmoothLocalPotential_weight w)
  have hK : ConvexOn ℝ (univ ×ˢ Ioo (0 : ℝ) 1) (toricVertexStripFunction D f w) := by
    apply convexOn_of_plurisubharmonicOn_tropical_strip
    intro p hp
    have hp' : p ∈ geodesicChartDomain (univ : Set (ComplexModel n)) := ⟨mem_univ _, hp.2⟩
    apply (hpsh p hp').congr
    filter_upwards [((isOpen_complexTorus n).prod isOpen_complexTimeStrip).mem_nhds hp] with q hq
    exact h.subgeodesicChartFunction_eq_vertexStrip hinv hprof w hq
  let A : EuclideanSpace ℝ (Fin n) × ℝ →ₗ[ℝ] EuclideanSpace ℝ (Fin n) × ℝ :=
    LinearMap.prodMap (latticeBasisLogMap (originalPolytopeNativeBasis γ hs w)) LinearMap.id
  have hA : A ⁻¹' (univ ×ˢ Ioo (0 : ℝ) 1) = univ ×ˢ Ioo (0 : ℝ) 1 := by
    ext p; simp [A]
  have h1 : ConvexOn ℝ (univ ×ˢ Ioo (0 : ℝ) 1) (toricVertexStripFunction D f w ∘ A) := by
    rw [← hA]; exact hK.comp_linearMap A
  have h2 : ConvexOn ℝ (univ ×ˢ Ioo (0 : ℝ) 1)
      (fun p : EuclideanSpace ℝ (Fin n) × ℝ => latticeFunctional (toricCartierDatum D w) p.1) :=
    ((latticeFunctional (toricCartierDatum D w)).comp (LinearMap.fst ℝ _ ℝ)).convexOn
      (convex_univ.prod (convex_Ioo 0 1))
  have h3 := h1.add h2
  refine ⟨h3.1, ?_⟩
  intro x hx y hy a b ha hb hab
  have := h3.2 hx hy ha hb hab
  simpa only [Pi.add_apply, Function.comp_apply, A, LinearMap.prodMap_apply, LinearMap.id_apply,
    ← toricVertexStripFunction_logMap D f w] using this

/-- Converse half of the chart computation in `prop:toricsubgeod`: let `(φ_s)_{s ∈ (0,1)}` be
toric `θ`-psh functions with real profiles `F_s`, uniformly bounded above, such that
`(x, s) ↦ F_s(x)` is convex on `N_ℝ × (0,1)`.  Then in every vertex chart the corrected
complexification `φ_{Re τ}(z) + ψ_v(z)` is plurisubharmonic on `ℂⁿ × S`.  On `T × S` this is
`plurisubharmonicOn_tropical_strip`; across `(X ∖ T) × S` the bounded analytic extension
(`thm:GRexten`) is plurisubharmonic and agrees with the complexification on every slice
(`eq_of_plurisubharmonicOn_of_eqOn_complexTorus`). -/
theorem plurisubharmonicOn_vertexChart_strip {curve : ℝ → PolytopeToricVariety γ hs → EReal}
    {f : ℝ → EuclideanSpace ℝ (Fin n) → ℝ}
    (hconv : ConvexOn ℝ (univ ×ˢ Ioo (0 : ℝ) 1)
      (fun p : EuclideanSpace ℝ (Fin n) × ℝ => f p.2 p.1))
    (hpsh : ∀ s ∈ Ioo (0 : ℝ) 1,
      (ofFixedModel n (PolytopeToricVariety γ hs)).IsThetaPSH h.atlasForm (curve s))
    (hinv : ∀ s ∈ Ioo (0 : ℝ) 1, PolytopeToricInvariant γ hs (curve s))
    (hprof : ∀ s ∈ Ioo (0 : ℝ) 1, h.profile (curve s) = fun x => (f s x : EReal))
    (C : ℝ) (hC : ∀ s ∈ Ioo (0 : ℝ) 1, ∀ p, curve s p ≤ (C : EReal))
    (v : latticePolytopeVertices γ) :
    PlurisubharmonicOn (subgeodesicChartFunction curve (polytopeToricVertexChart γ hs v)
      (h.weight v)) (univ ×ˢ complexTimeStrip) := by
  set Φ := subgeodesicChartFunction curve (polytopeToricVertexChart γ hs v) (h.weight v)
  -- convexity of the chart function
  have hKv : ConvexOn ℝ (univ ×ˢ Ioo (0 : ℝ) 1) (toricVertexStripFunction D f v) := by
    let A : EuclideanSpace ℝ (Fin n) × ℝ →ₗ[ℝ] EuclideanSpace ℝ (Fin n) × ℝ :=
      LinearMap.prodMap (latticeBasisLogInverse (originalPolytopeNativeBasis γ hs v)) LinearMap.id
    have hA : A ⁻¹' (univ ×ˢ Ioo (0 : ℝ) 1) = univ ×ˢ Ioo (0 : ℝ) 1 := by
      ext p; simp [A]
    have h1 : ConvexOn ℝ (univ ×ˢ Ioo (0 : ℝ) 1)
        ((fun p : EuclideanSpace ℝ (Fin n) × ℝ => f p.2 p.1) ∘ A) := by
      rw [← hA]; exact hconv.comp_linearMap A
    have h2 : ConvexOn ℝ (univ ×ˢ Ioo (0 : ℝ) 1)
        (fun p : EuclideanSpace ℝ (Fin n) × ℝ => -latticeFunctional (toricCartierDatum D v)
          (latticeBasisLogInverse (originalPolytopeNativeBasis γ hs v) p.1)) :=
      (-((latticeFunctional (toricCartierDatum D v)).comp
        ((latticeBasisLogInverse (originalPolytopeNativeBasis γ hs v)).comp
          (LinearMap.fst ℝ _ ℝ)))).convexOn (convex_univ.prod (convex_Ioo 0 1))
    have h3 := h1.add h2
    refine ⟨h3.1, ?_⟩
    intro x hx y hy a b ha hb hab
    have := h3.2 hx hy ha hb hab
    simpa only [toricVertexStripFunction, sub_eq_add_neg, Pi.add_apply, Function.comp_apply, A,
      LinearMap.prodMap_apply, LinearMap.id_apply] using this
  -- plurisubharmonic on the torus part
  have hTor : PlurisubharmonicOn Φ (complexTorus n ×ˢ complexTimeStrip) := by
    intro p hp
    apply (plurisubharmonicOn_tropical_strip hKv p hp).congr
    filter_upwards [((isOpen_complexTorus n).prod isOpen_complexTimeStrip).mem_nhds hp] with q hq
    exact (h.subgeodesicChartFunction_eq_vertexStrip hinv hprof v hq).symm
  -- the model `ℂⁿ⁺¹`
  let L := Pending.FiniteGeodesicMaximality.stripModelEquiv n
  let Ω : Set (ComplexModel (n + 1)) := L ⁻¹' (univ ×ˢ complexTimeStrip)
  let A : Set (ComplexModel (n + 1)) := L ⁻¹' ((complexTorus n)ᶜ ×ˢ univ)
  let ψ : ComplexModel (n + 1) → EReal := fun q => Φ (L q)
  have hΩ : IsOpen Ω := (isOpen_univ.prod isOpen_complexTimeStrip).preimage L.continuous
  have hΩA : Ω \ A = L ⁻¹' (complexTorus n ×ˢ complexTimeStrip) := by
    ext q
    constructor
    · rintro ⟨⟨-, h2⟩, h3⟩
      exact ⟨by_contra fun hc => h3 ⟨hc, mem_univ _⟩, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨mem_univ _, h2⟩, fun hA => hA.1 h1⟩
  have hψ : PlurisubharmonicOn ψ (Ω \ A) := by
    rw [hΩA]
    exact Pending.FiniteGeodesicMaximality.plurisubharmonicOn_comp_stripModelEquiv hTor
  have hopenΩA : IsOpen (Ω \ A) := by
    rw [hΩA]
    exact ((isOpen_complexTorus n).prod isOpen_complexTimeStrip).preimage L.continuous
  have hbound : Pending.PshHypersurfaceRemovable.LocallyBoundedAboveOff A Ω ψ := by
    intro q hq
    have hcomp : IsCompact (Metric.closedBall (L q).1 1) := isCompact_closedBall _ _
    obtain ⟨B, hB⟩ := hcomp.bddAbove_image (h.smooth v).continuous.continuousOn
    refine ⟨Ω ∩ L ⁻¹' (Metric.ball (L q).1 1 ×ˢ univ),
      inter_mem (hΩ.mem_nhds hq) ((((Metric.isOpen_ball).prod isOpen_univ).preimage
        L.continuous).mem_nhds ⟨Metric.mem_ball_self one_pos, mem_univ _⟩), C + B, ?_⟩
    rintro y ⟨hyΩ, hyb⟩ -
    have hyt : (L y).2.re ∈ Ioo (0 : ℝ) 1 := hyΩ.2
    have hρ : h.weight v (L y).1 ≤ B :=
      hB ⟨(L y).1, Metric.ball_subset_closedBall hyb.1, rfl⟩
    change curve (L y).2.re _ + (h.weight v (L y).1 : EReal) ≤ ((C + B : ℝ) : EReal)
    rw [EReal.coe_add]
    exact add_le_add (hC _ hyt _) (EReal.coe_le_coe_iff.mpr hρ)
  let g : Fin 1 → ComplexModel (n + 1) → ℂ :=
    fun _ q => originalPolytopeNativeBoundaryPolynomial n (L q).1
  have hg : ∀ i, DifferentiableOn ℂ (g i) Ω := fun _ =>
    ((differentiable_originalPolytopeNativeBoundaryPolynomial n).comp
      (differentiable_fst.comp L.differentiable)).differentiableOn
  have hgA : ∀ y ∈ Ω, y ∈ A ↔ ∀ i, g i y = 0 := by
    intro y _
    simp only [A, g, mem_preimage, mem_prod, mem_compl_iff, mem_univ, and_true, forall_const]
    rw [← not_iff_not, not_not, ← originalPolytopeNativeBoundaryPolynomial_ne_zero_iff]
  have hext := Pending.PshAnalyticRemovable.plurisubharmonicOn_extension_of_zeroLocus hΩ hψ
    hbound hg hgA
  -- back to `ℂⁿ × ℂ`
  let E : ComplexModel n × ℂ → EReal :=
    fun p => Pending.PshCodimTwoExtension.extension A ψ (L.symm p)
  have hE : PlurisubharmonicOn E (univ ×ˢ complexTimeStrip) := by
    have hb := Pending.FiniteGeodesicMaximality.plurisubharmonicOn_comp_stripModelEquiv_symm hext
    have hset : (L.symm : ComplexModel n × ℂ → ComplexModel (n + 1)) ⁻¹' Ω =
        univ ×ˢ complexTimeStrip := by
      ext p; simp [Ω]
    rwa [hset] at hb
  have hEoff : ∀ p ∈ complexTorus n ×ˢ complexTimeStrip, E p = Φ p := by
    intro p hp
    have hmem : L.symm p ∈ Ω \ A := by
      rw [hΩA]
      simpa only [mem_preimage, ContinuousLinearEquiv.apply_symm_apply] using hp
    change Pending.PshCodimTwoExtension.extension A ψ (L.symm p) = Φ p
    rw [Pending.PshCodimTwoExtension.extension_eq hψ hopenΩA hmem]
    change Φ (L (L.symm p)) = Φ p
    rw [ContinuousLinearEquiv.apply_symm_apply]
  -- equality on each slice
  have hEq : EqOn E Φ (univ ×ˢ complexTimeStrip) := by
    rintro ⟨z, τ⟩ ⟨-, hτ⟩
    let ι : ComplexModel n →L[ℂ] ComplexModel n × ℂ := ContinuousLinearMap.inl ℂ _ ℂ
    have hι (y : ComplexModel n) : ((0, τ) : ComplexModel n × ℂ) + ι y = (y, τ) := by
      simp [ι]
    have hpre : (fun y => ((0, τ) : ComplexModel n × ℂ) + ι y) ⁻¹' (univ ×ˢ complexTimeStrip) =
        univ := by
      ext y; simp only [hι, mem_preimage, mem_prod, mem_univ, true_and]; exact iff_of_true hτ trivial
    have hEs := hE.comp_affine ι (0, τ)
    rw [hpre] at hEs
    simp only [hι] at hEs
    have hτ' : τ.re ∈ Ioo (0 : ℝ) 1 := hτ
    have hΦs : PlurisubharmonicOn (fun y => Φ (y, τ)) univ := by
      have := h.plurisubharmonicOn_vertexChart (hpsh _ hτ') v
      exact this
    have hz₀ : expCoordinates (0 : EuclideanSpace ℝ (Fin n)) ∈ complexTorus n :=
      expCoordinates_mem_complexTorus 0
    have hτs : τ ∈ complexTimeStrip := hτ
    have hfin : E (expCoordinates 0, τ) ≠ ⊥ := by
      rw [hEoff (expCoordinates 0, τ) ⟨hz₀, hτs⟩]
      change subgeodesicChartFunction curve (polytopeToricVertexChart γ hs v) (h.weight v)
        (expCoordinates 0, τ) ≠ ⊥
      rw [h.subgeodesicChartFunction_eq_vertexStrip hinv hprof v ⟨hz₀, hτs⟩]
      exact EReal.coe_ne_bot _
    have := eq_of_plurisubharmonicOn_of_eqOn_complexTorus hEs hΦs
      (fun y hy => hEoff (y, τ) ⟨hy, hτs⟩) hz₀ hfin
    exact congrFun this z
  intro p hp
  apply (hE p hp).congr
  filter_upwards [(isOpen_univ.prod isOpen_complexTimeStrip).mem_nhds hp] with q hq
  exact hEq hq

end BigToricMetric

end SGPT.Toric
