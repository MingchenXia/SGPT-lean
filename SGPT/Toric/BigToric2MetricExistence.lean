import SGPT.Toric.BigToric2Orbits
import SGPT.Foundations.Analysis.Pending.LocalPotentialForm
import SGPT.Foundations.Analysis.Pending.PluriharmonicLogNorm

/-!
# Existence of torus-invariant metrics on `O(D)`

Source `chapter_toric_big.tex`, `sec:toricpob`: "We shall fix a `T_c`-invariant Hermitian metric
`h` on `L` so that `θ = c_1(L, h)`", and the proof of `lma:exist_Ftheta`, Step 1: write
`D = D_1 - D_2` with `D_1, D_2` ample and take `h = h_1 ⊗ h_2^{-1}`.

`BigToricMetric D` records such a metric by its local weights; its existence for an
arbitrary torus-invariant divisor `D` was left open there.  Here it is constructed:

* `ToricWeightFamily D`: smooth `T_c`-invariant local weights `ψ_v` on the vertex charts with the
  transition law on `T(ℂ)` and pluriharmonic differences on the overlaps; it glues
  (`LocalDDCData`) to a closed real `(1,1)`-form, and gives a `BigToricMetric D`
  (`ToricWeightFamily.toBigToricMetric`);
* `fsWeight E v z = log ∑_w ∏_i |z_i|^{2⟨m_w - m_v, u_i(v)⟩}`: the Fubini–Study weights of a
  divisor `E` whose Cartier data satisfy `⟨m_w - m_v, u_i(v)⟩ ≥ 0` (the metric induced by the
  sections `χ^{m_w}`); on `U_v ∩ U_w` their difference is `log |χ^{m_w - m_v}|²`, with
  `χ^{m_w - m_v}` a holomorphic unit there (orbit–cone correspondence);
* `D = (D + c D_P) - c D_P` for `c ≫ 0`, both of Fubini–Study type, which gives
  `exists_bigToricMetric : Nonempty (BigToricMetric D)` for every torus-invariant divisor `D`.
-/

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set Filter SGPT.PSH SGPT.PSH.VariableComplexAtlas
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.LocalPotentialForm
open scoped Topology ContDiff BigOperators Manifold

variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- Holomorphic chart transitions read a vertex chart in any chart of `X`. -/
theorem differentiableOn_vertexChart_comp_symm (v : latticePolytopeVertices γ)
    (e : ComplexChart n (PolytopeToricVariety γ hs)) :
    DifferentiableOn ℂ (fun u => originalPolytopeNativeModelChart γ hs v (e.val.symm u))
      (e.val.target ∩ e.val.symm ⁻¹' (originalPolytopeNativeModelChart γ hs v).source) := by
  exact (ofFixedModel n (PolytopeToricVariety γ hs)).holomorphic e
    (polytopeToricVertexChart γ hs v)

theorem isOpen_chartOverlap (v : latticePolytopeVertices γ)
    (e : ComplexChart n (PolytopeToricVariety γ hs)) :
    IsOpen (e.val.target ∩ e.val.symm ⁻¹' (originalPolytopeNativeModelChart γ hs v).source) :=
  e.val.isOpen_inter_preimage_symm (originalPolytopeNativeModelChart γ hs v).open_source

theorem contDiffOn_comp_vertexChart_comp_symm {f : ComplexModel n → ℝ} (hf : ContDiff ℝ ∞ f)
    (v : latticePolytopeVertices γ) (e : ComplexChart n (PolytopeToricVariety γ hs)) :
    ContDiffOn ℝ ∞ (fun u => f (originalPolytopeNativeModelChart γ hs v (e.val.symm u)))
      (e.val.target ∩ e.val.symm ⁻¹' (originalPolytopeNativeModelChart γ hs v).source) := by
  have hd := (contDiffOn_of_differentiableOn_complex
    (differentiableOn_vertexChart_comp_symm v e) (isOpen_chartOverlap v e)).restrict_scalars ℝ
  exact hf.contDiffOn.comp hd (mapsTo_univ _ _)

variable (D : ToricDivisor γ hs)

/-- Smooth `T_c`-invariant local weights `ψ_v` of a metric on `O(D)` (see `BigToricMetric`),
with pluriharmonic differences `ψ_v ∘ z_v - ψ_w ∘ z_w` on the overlaps `U_v ∩ U_w`. -/
structure ToricWeightFamily where
  weight : latticePolytopeVertices γ → ComplexModel n → ℝ
  smooth : ∀ v, ContDiff ℝ ∞ (weight v)
  invariant : ∀ v (a : Fin n → ℂˣ), IsCompactTorusElement a → ∀ z,
    weight v (originalPolytopeNativeModelActionLinear γ hs v a z) = weight v z
  transition : ∀ v w (a : Fin n → ℂˣ),
    weight v (originalPolytopeNativeModelChart γ hs v (polytopeToricEmbedding γ hs a)) +
        latticeFunctional (toricCartierDatum D v) (unitTorusLog a) =
      weight w (originalPolytopeNativeModelChart γ hs w (polytopeToricEmbedding γ hs a)) +
        latticeFunctional (toricCartierDatum D w) (unitTorusLog a)
  pluriharmonic : ∀ v w (e : ComplexChart n (PolytopeToricVariety γ hs)) (u : ComplexModel n),
    u ∈ e.val.target → e.val.symm u ∈ (originalPolytopeNativeModelChart γ hs v).source →
    e.val.symm u ∈ (originalPolytopeNativeModelChart γ hs w).source →
    smoothDDC (fun u' => weight v (originalPolytopeNativeModelChart γ hs v (e.val.symm u')) -
      weight w (originalPolytopeNativeModelChart γ hs w (e.val.symm u'))) u = 0

namespace ToricWeightFamily

variable {D} (F : ToricWeightFamily D)

/-- The local potentials `ψ_v ∘ z_v` on the vertex charts chosen by the cover. -/
def localDDCData : LocalDDCData n (PolytopeToricVariety γ hs) where
  domain p := (originalPolytopeNativeModelChart γ hs
    (originalPolytopeNativeModelChart_cover γ hs p).choose).source
  isOpen_domain _ := (originalPolytopeNativeModelChart γ hs _).open_source
  mem_domain p := (originalPolytopeNativeModelChart_cover γ hs p).choose_spec
  potential p q := F.weight (originalPolytopeNativeModelChart_cover γ hs p).choose
    (originalPolytopeNativeModelChart γ hs (originalPolytopeNativeModelChart_cover γ hs p).choose q)
  smooth _ e := contDiffOn_comp_vertexChart_comp_symm (F.smooth _) _ e
  pluriharmonic _ _ e u hu hp hq := F.pluriharmonic _ _ e u hu hp hq

/-- The metric on `O(D)` with the local weights `ψ_v` and curvature form the glued
`θ = ddᶜ ψ_v`. -/
def toBigToricMetric : BigToricMetric D where
  form := F.localDDCData.closedForm
  weight := F.weight
  smooth := F.smooth
  coeff v z := by
    have hz : z ∈ (originalPolytopeNativeModelChart γ hs v).target := by
      rw [originalPolytopeNativeModelChart_target]; exact mem_univ z
    set e := polytopeToricVertexChart γ hs v
    set p := (originalPolytopeNativeModelChart γ hs v).symm z
    set t := (originalPolytopeNativeModelChart_cover γ hs p).choose
    have ht : p ∈ (originalPolytopeNativeModelChart γ hs t).source :=
      (originalPolytopeNativeModelChart_cover γ hs p).choose_spec
    have hp : p ∈ (originalPolytopeNativeModelChart γ hs v).source :=
      (originalPolytopeNativeModelChart γ hs v).map_target hz
    have hcoeff := (F.localDDCData.form_coeff_eventuallyEq p e hz
      (F.localDDCData.mem_domain p)).self_of_nhds
    change F.localDDCData.form.coeff e z = _
    rw [hcoeff]
    have hsub := PositiveClasses.smoothDDC_sub
      ((isOpen_chartOverlap t e).inter (isOpen_chartOverlap v e))
      ((contDiffOn_comp_vertexChart_comp_symm (F.smooth t) t e).mono inter_subset_left)
      ((contDiffOn_comp_vertexChart_comp_symm (F.smooth v) v e).mono inter_subset_right)
      (z := z) ⟨⟨hz, ht⟩, hz, hp⟩
    have hzero := F.pluriharmonic t v e z hz ht hp
    rw [hsub] at hzero
    have h1 := sub_eq_zero.mp hzero
    change smoothDDC (fun u' => F.weight t (originalPolytopeNativeModelChart γ hs t
      ((originalPolytopeNativeModelChart γ hs v).symm u'))) z = _ at h1 ⊢
    rw [h1]
    apply smoothDDC_congr
    filter_upwards with u'
    exact congrArg (F.weight v) ((originalPolytopeNativeModelChart γ hs v).right_inv
      (by rw [originalPolytopeNativeModelChart_target]; exact mem_univ u'))
  invariant := F.invariant
  transition := F.transition

theorem toBigToricMetric_weight : F.toBigToricMetric.weight = F.weight := rfl

end ToricWeightFamily

/-! ### Fubini–Study weights -/

/-- The vertices of `P` form a finite type. -/
noncomputable local instance instFintypeVertices : Fintype (latticePolytopeVertices γ) :=
  (finite_latticePolytopeVertices γ).fintype

theorem toricCartierDatum_add (E E' : ToricDivisor γ hs) (v : latticePolytopeVertices γ) :
    toricCartierDatum (E + E') v = toricCartierDatum E v + toricCartierDatum E' v := by
  unfold toricCartierDatum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.add_apply, neg_add, add_smul]

theorem toricCartierDatum_sub (E E' : ToricDivisor γ hs) (v : latticePolytopeVertices γ) :
    toricCartierDatum (E - E') v = toricCartierDatum E v - toricCartierDatum E' v := by
  have h := toricCartierDatum_add (E - E') E' v
  rw [sub_add_cancel] at h
  rw [h, add_sub_cancel_right]

variable (E : ToricDivisor γ hs)

/-- The exponent `⟨m_w - m_v, u_i(v)⟩` of the section `χ^{m_w}` in the frame `e_v` of `O(E)`. -/
def fsExponent (v w : latticePolytopeVertices γ) (i : Fin n) : ℤ :=
  intPairing (toricCartierDatum E w - toricCartierDatum E v) (polytopeToricRayGenerator γ hs v i)

/-- The divisors for which the characters `χ^{m_w}` of the Cartier data are sections:
`⟨m_w - m_v, u_i(v)⟩ ≥ 0` for all vertices `v, w`. -/
def IsFubiniStudyDivisor : Prop := ∀ v w i, 0 ≤ fsExponent E v w i

/-- `∑_w |χ^{m_w - m_v}|²` in the vertex coordinates of `U_v`. -/
def fsSum (v : latticePolytopeVertices γ) (z : ComplexModel n) : ℝ :=
  ∑ w, ∏ i, (‖z i‖ ^ 2) ^ (fsExponent E v w i).toNat

/-- The Fubini–Study weight `ψ_v = log ∑_w |χ^{m_w - m_v}|²` of `O(E)` on `U_v`. -/
def fsWeight (v : latticePolytopeVertices γ) (z : ComplexModel n) : ℝ :=
  Real.log (fsSum E v z)

theorem one_le_fsSum (v : latticePolytopeVertices γ) (z : ComplexModel n) : 1 ≤ fsSum E v z := by
  have hv : ∏ i, (‖z i‖ ^ 2) ^ (fsExponent E v v i).toNat = 1 := by
    simp [fsExponent, sub_self, intPairing]
  calc (1 : ℝ) = ∏ i, (‖z i‖ ^ 2) ^ (fsExponent E v v i).toNat := hv.symm
    _ ≤ fsSum E v z := Finset.single_le_sum (f := fun w => ∏ i, (‖z i‖ ^ 2) ^ (fsExponent E v w i).toNat)
        (fun w _ => Finset.prod_nonneg fun i _ => pow_nonneg (sq_nonneg _) _) (Finset.mem_univ v)

theorem contDiff_fsSum (v : latticePolytopeVertices γ) : ContDiff ℝ ∞ (fsSum E v) := by
  unfold fsSum
  apply ContDiff.sum
  intro w _
  apply contDiff_prod
  intro i _
  apply ContDiff.pow
  exact (contDiff_norm_sq ℝ).comp
    ((EuclideanSpace.proj (𝕜 := ℂ) i).restrictScalars ℝ).contDiff

theorem contDiff_fsWeight (v : latticePolytopeVertices γ) : ContDiff ℝ ∞ (fsWeight E v) :=
  (contDiff_fsSum E v).log fun z => by linarith [one_le_fsSum E v z]

/-- `T_c`-invariance: the weight only depends on `|z_i|`. -/
theorem fsWeight_action (v : latticePolytopeVertices γ) (a : Fin n → ℂˣ)
    (ha : IsCompactTorusElement a) (z : ComplexModel n) :
    fsWeight E v (originalPolytopeNativeModelActionLinear γ hs v a z) = fsWeight E v z := by
  have hnorm : ∀ i, ‖(originalPolytopeNativeModelActionLinear γ hs v a z) i‖ = ‖z i‖ := by
    intro i
    change ‖(latticeCharacter (originalPolytopeNativeBasis γ hs v i) a : ℂ) * z i‖ = _
    rw [norm_mul]
    have h1 : ‖(latticeCharacter (originalPolytopeNativeBasis γ hs v i) a : ℂ)‖ = 1 := by
      simp only [latticeCharacter, MonoidHom.coe_mk, OneHom.coe_mk, Units.coe_prod,
        Units.val_zpow_eq_zpow_val, norm_prod, norm_zpow]
      exact Finset.prod_eq_one fun x _ => by rw [ha x, one_zpow]
    rw [h1, one_mul]
  simp only [fsWeight, fsSum, hnorm]

/-- On the torus, `ψ_v = log ∑_w e^{⟨m_w, Trop⟩} - ⟨m_v, Trop⟩`. -/
theorem fsWeight_chart_embedding (hE : IsFubiniStudyDivisor E) (v : latticePolytopeVertices γ)
    (a : Fin n → ℂˣ) :
    fsWeight E v (originalPolytopeNativeModelChart γ hs v (polytopeToricEmbedding γ hs a)) =
      Real.log (∑ w, Real.exp (latticeFunctional (toricCartierDatum E w) (unitTorusLog a))) -
        latticeFunctional (toricCartierDatum E v) (unitTorusLog a) := by
  have hcoord : ∀ i, ‖originalPolytopeNativeModelChart γ hs v (polytopeToricEmbedding γ hs a) i‖ ^ 2 =
      Real.exp (latticeFunctional (originalPolytopeNativeBasis γ hs v i) (unitTorusLog a)) := by
    intro i
    rw [vertexChart_embedding hs v, modelPoint_apply]
    have hpos : 0 < ‖(latticeCharacter (originalPolytopeNativeBasis γ hs v i) a : ℂ)‖ ^ 2 :=
      pow_pos (norm_pos_iff.mpr (Units.ne_zero _)) 2
    rw [← Real.exp_log hpos, latticeCharacter_log_norm_sq]
    congr 1
  have hterm : ∀ w, ∏ i, (‖originalPolytopeNativeModelChart γ hs v
      (polytopeToricEmbedding γ hs a) i‖ ^ 2) ^ (fsExponent E v w i).toNat =
      Real.exp (latticeFunctional (toricCartierDatum E w) (unitTorusLog a) -
        latticeFunctional (toricCartierDatum E v) (unitTorusLog a)) := by
    intro w
    simp only [hcoord]
    have hsub : latticeFunctional (toricCartierDatum E w) (unitTorusLog a) -
        latticeFunctional (toricCartierDatum E v) (unitTorusLog a) =
        latticeFunctional (toricCartierDatum E w - toricCartierDatum E v) (unitTorusLog a) := by
      simp only [latticeFunctional_apply, Pi.sub_apply, Int.cast_sub, sub_mul,
        Finset.sum_sub_distrib]
    rw [hsub, latticeFunctional_eq_sum_basis hs v _ (unitTorusLog a), Real.exp_sum]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← Real.exp_nat_mul]
    congr 1
    have : ((fsExponent E v w i).toNat : ℝ) = (fsExponent E v w i : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg (hE v w i)
    rw [this, fsExponent]
    ring
  have hne : Nonempty (latticePolytopeVertices γ) := by
    obtain ⟨w, hw⟩ := nonempty_latticePolytopeVertices γ
    exact ⟨⟨w, hw⟩⟩
  unfold fsWeight fsSum
  simp only [hterm, Real.exp_sub]
  rw [← Finset.sum_div, Real.log_div (Finset.sum_pos (fun w _ => Real.exp_pos _)
    Finset.univ_nonempty).ne' (Real.exp_pos _).ne', Real.log_exp]

theorem fsWeight_transition (hE : IsFubiniStudyDivisor E) (v w : latticePolytopeVertices γ)
    (a : Fin n → ℂˣ) :
    fsWeight E v (originalPolytopeNativeModelChart γ hs v (polytopeToricEmbedding γ hs a)) +
        latticeFunctional (toricCartierDatum E v) (unitTorusLog a) =
      fsWeight E w (originalPolytopeNativeModelChart γ hs w (polytopeToricEmbedding γ hs a)) +
        latticeFunctional (toricCartierDatum E w) (unitTorusLog a) := by
  rw [fsWeight_chart_embedding E hE, fsWeight_chart_embedding E hE]
  ring

/-- The character `χ^{m_w - m_v}` in the vertex coordinates of `U_v`. -/
def fsUnit (v w : latticePolytopeVertices γ) (z : ComplexModel n) : ℂ :=
  ∏ i, z i ^ fsExponent E v w i

/-- On `U_v ∩ U_w`, the coordinates `z_i` of `U_v` vanishing at a point have exponent zero in
`χ^{m_w - m_v}` (the ray `u_i(v)` is then a ray of `σ_w`). -/
theorem fsExponent_eq_zero_of_coord_eq_zero {v w : latticePolytopeVertices γ}
    {p : PolytopeToricVariety γ hs} (hv : p ∈ (originalPolytopeNativeModelChart γ hs v).source)
    (hw : p ∈ (originalPolytopeNativeModelChart γ hs w).source) {i : Fin n}
    (hi : originalPolytopeNativeModelChart γ hs v p i = 0) : fsExponent E v w i = 0 := by
  obtain ⟨i', hi', -⟩ := exists_chart_coord_eq_zero hs (v := w) (w := v) hw hv hi
  have hray : polytopeToricRay γ hs w i' = polytopeToricRay γ hs v i := Subtype.ext hi'
  have h1 := toricCartierDatum_pairing E w i'
  have h2 := toricCartierDatum_pairing E v i
  rw [hi', hray] at h1
  rw [fsExponent, intPairing_sub, h1, h2, sub_self]

theorem fsUnit_ne_zero {v w : latticePolytopeVertices γ} {p : PolytopeToricVariety γ hs}
    (hv : p ∈ (originalPolytopeNativeModelChart γ hs v).source)
    (hw : p ∈ (originalPolytopeNativeModelChart γ hs w).source) :
    fsUnit E v w (originalPolytopeNativeModelChart γ hs v p) ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  by_cases hz : originalPolytopeNativeModelChart γ hs v p i = 0
  · rw [fsExponent_eq_zero_of_coord_eq_zero E hv hw hz, zpow_zero]; exact one_ne_zero
  · exact zpow_ne_zero _ hz

/-- On `U_v ∩ U_w`: `ψ_v ∘ z_v - ψ_w ∘ z_w = log |χ^{m_w - m_v}|²`. -/
theorem fsWeight_sub_eq_log (hE : IsFubiniStudyDivisor E) {v w : latticePolytopeVertices γ}
    {p : PolytopeToricVariety γ hs} (hv : p ∈ (originalPolytopeNativeModelChart γ hs v).source)
    (hw : p ∈ (originalPolytopeNativeModelChart γ hs w).source) :
    fsWeight E v (originalPolytopeNativeModelChart γ hs v p) -
        fsWeight E w (originalPolytopeNativeModelChart γ hs w p) =
      Real.log (Complex.normSq (fsUnit E v w (originalPolytopeNativeModelChart γ hs v p))) := by
  set ev := originalPolytopeNativeModelChart γ hs v
  set ew := originalPolytopeNativeModelChart γ hs w
  set U := ev.source ∩ ew.source
  have hU : IsOpen U := ev.open_source.inter ew.open_source
  -- the identity on the torus
  have htorus : EqOn (fun q => fsWeight E v (ev q) - fsWeight E w (ew q))
      (fun q => Real.log (Complex.normSq (fsUnit E v w (ev q))))
      (U ∩ (polytopeToricBoundary γ hs)ᶜ) := by
    rintro q ⟨-, hq⟩
    obtain ⟨a, rfl⟩ := (mem_polytopeToricBoundary_compl_iff γ hs q).mp hq
    simp only
    rw [fsWeight_chart_embedding E hE, fsWeight_chart_embedding E hE]
    have hunit : fsUnit E v w (ev (polytopeToricEmbedding γ hs a)) =
        (latticeCharacter (toricCartierDatum E w - toricCartierDatum E v) a : ℂ) := by
      rw [fsUnit, vertexChart_embedding hs v, latticeCharacter_eq_prod_basis hs v]
      simp only [modelPoint_apply, Units.coe_prod, Units.val_zpow_eq_zpow_val]
      rfl
    rw [hunit, Complex.normSq_eq_norm_sq, latticeCharacter_log_norm_sq]
    have : ∑ j, ((toricCartierDatum E w - toricCartierDatum E v) j : ℝ) *
        SGPT.Convex.torusLogCoordinates (latticeTorusPoint a) j =
        latticeFunctional (toricCartierDatum E w) (unitTorusLog a) -
          latticeFunctional (toricCartierDatum E v) (unitTorusLog a) := by
      simp only [latticeFunctional_apply, Pi.sub_apply, Int.cast_sub, sub_mul,
        Finset.sum_sub_distrib]
      rfl
    rw [this]; ring
  have hcontL : ContinuousOn (fun q => fsWeight E v (ev q) - fsWeight E w (ew q)) U :=
    (((contDiff_fsWeight E v).continuous.comp_continuousOn ev.continuousOn).mono
      inter_subset_left).sub
    (((contDiff_fsWeight E w).continuous.comp_continuousOn ew.continuousOn).mono
      inter_subset_right)
  have hcontR : ContinuousOn (fun q => Real.log (Complex.normSq (fsUnit E v w (ev q)))) U := by
    intro q hq
    apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.log _ (by
      rw [Complex.normSq_eq_norm_sq]
      exact pow_ne_zero 2 (norm_ne_zero_iff.mpr (fsUnit_ne_zero E hq.1 hq.2)))
    apply Complex.continuous_normSq.continuousAt.comp
    unfold fsUnit
    apply tendsto_finsetProd
    intro i _
    apply ContinuousAt.zpow₀
    · exact (EuclideanSpace.proj (𝕜 := ℂ) i).continuous.continuousAt.comp
        (ev.continuousAt hq.1)
    · by_cases hz : ev q i = 0
      · right; rw [fsExponent_eq_zero_of_coord_eq_zero E hq.1 hq.2 hz]
      · left; exact hz
  have hdense : U ⊆ closure (U ∩ (polytopeToricBoundary γ hs)ᶜ) :=
    (dense_originalPolytopeNativeTorus γ).open_subset_closure_inter hU
  exact htorus.of_subset_closure hcontL hcontR inter_subset_left hdense ⟨hv, hw⟩

/-- The differences of the Fubini–Study weights are pluriharmonic on the overlaps, in every
chart of `X`. -/
theorem smoothDDC_fsWeight_sub (hE : IsFubiniStudyDivisor E) (v w : latticePolytopeVertices γ)
    (e : ComplexChart n (PolytopeToricVariety γ hs)) (u : ComplexModel n) (hu : u ∈ e.val.target)
    (hv : e.val.symm u ∈ (originalPolytopeNativeModelChart γ hs v).source)
    (hw : e.val.symm u ∈ (originalPolytopeNativeModelChart γ hs w).source) :
    smoothDDC (fun u' => fsWeight E v (originalPolytopeNativeModelChart γ hs v (e.val.symm u')) -
      fsWeight E w (originalPolytopeNativeModelChart γ hs w (e.val.symm u'))) u = 0 := by
  set O := e.val.target ∩ e.val.symm ⁻¹' ((originalPolytopeNativeModelChart γ hs v).source ∩
    (originalPolytopeNativeModelChart γ hs w).source)
  have hO : IsOpen O := e.val.isOpen_inter_preimage_symm
    ((originalPolytopeNativeModelChart γ hs v).open_source.inter
      (originalPolytopeNativeModelChart γ hs w).open_source)
  have huO : u ∈ O := ⟨hu, hv, hw⟩
  set f : ComplexModel n → ℂ := fun u' =>
    fsUnit E v w (originalPolytopeNativeModelChart γ hs v (e.val.symm u'))
  have hcongr : (fun u' => fsWeight E v (originalPolytopeNativeModelChart γ hs v (e.val.symm u')) -
      fsWeight E w (originalPolytopeNativeModelChart γ hs w (e.val.symm u'))) =ᶠ[𝓝 u]
      fun u' => Real.log (Complex.normSq (f u')) := by
    filter_upwards [hO.mem_nhds huO] with u' hu'
    exact fsWeight_sub_eq_log E hE hu'.2.1 hu'.2.2
  rw [smoothDDC_congr hcongr]
  apply PluriharmonicLogNorm.smoothDDC_log_normSq_eq_zero
  · filter_upwards [hO.mem_nhds huO] with u' hu'
    have hT := differentiableOn_vertexChart_comp_symm (hs := hs) v e
    have hTat : DifferentiableAt ℂ (fun u => originalPolytopeNativeModelChart γ hs v (e.val.symm u)) u' :=
      hT.differentiableAt ((isOpen_chartOverlap v e).mem_nhds ⟨hu'.1, hu'.2.1⟩)
    simp only [f, fsUnit]
    have hfac : ∀ i ∈ (Finset.univ : Finset (Fin n)), DifferentiableAt ℂ (fun u'' =>
        originalPolytopeNativeModelChart γ hs v (e.val.symm u'') i ^ fsExponent E v w i) u' := by
      intro i _
      apply DifferentiableAt.zpow ((EuclideanSpace.proj (𝕜 := ℂ) i).differentiableAt.comp u' hTat)
      by_cases hz : originalPolytopeNativeModelChart γ hs v (e.val.symm u') i = 0
      · right; rw [fsExponent_eq_zero_of_coord_eq_zero E hu'.2.1 hu'.2.2 hz]
      · left; exact hz
    classical
    exact (HasFDerivAt.finsetProd fun i hi => (hfac i hi).hasFDerivAt).differentiableAt
  · exact fsUnit_ne_zero E hv hw

/-! ### `D = (D + c D_P) - c D_P` -/

/-- `c D_P` is of Fubini–Study type (its Cartier data are `c v`). -/
theorem isFubiniStudyDivisor_smul_ampleDivisor (c : ℕ) :
    IsFubiniStudyDivisor ((c : ℤ) • polytopeToricAmpleDivisor γ hs) := by
  intro v w i
  rw [fsExponent, toricCartierDatum_smul, toricCartierDatum_smul, toricCartierDatum_ampleDivisor,
    toricCartierDatum_ampleDivisor, ← smul_sub, intPairing_smul]
  exact mul_nonneg (by positivity) (vertex_pairing_rayGenerator_nonneg γ hs v w i)

/-- The constant `c = ∑ |⟨m_w - m_v, u_i(v)⟩|`. -/
def fsShift (D : ToricDivisor γ hs) : ℕ :=
  ∑ v : latticePolytopeVertices γ, ∑ w : latticePolytopeVertices γ, ∑ i : Fin n,
    (intPairing (toricCartierDatum D w - toricCartierDatum D v)
      (polytopeToricRayGenerator γ hs v i)).natAbs

/-- `D + c D_P` is of Fubini–Study type for `c = fsShift D`. -/
theorem isFubiniStudyDivisor_add_smul_ampleDivisor (D : ToricDivisor γ hs) :
    IsFubiniStudyDivisor (D + ((fsShift D : ℕ) : ℤ) • polytopeToricAmpleDivisor γ hs) := by
  intro v w i
  set c := fsShift D
  set t := intPairing (toricCartierDatum D w - toricCartierDatum D v)
    (polytopeToricRayGenerator γ hs v i)
  set k := intPairing (w.val - v.val) (polytopeToricRayGenerator γ hs v i)
  have hk : 0 ≤ k := vertex_pairing_rayGenerator_nonneg γ hs v w i
  have hexp : fsExponent (D + ((c : ℕ) : ℤ) • polytopeToricAmpleDivisor γ hs) v w i =
      t + c * k := by
    rw [fsExponent, toricCartierDatum_add, toricCartierDatum_add, toricCartierDatum_smul,
      toricCartierDatum_smul, toricCartierDatum_ampleDivisor, toricCartierDatum_ampleDivisor]
    have : toricCartierDatum D w + (c : ℤ) • w.val - (toricCartierDatum D v + (c : ℤ) • v.val) =
        (toricCartierDatum D w - toricCartierDatum D v) + (c : ℤ) • (w.val - v.val) := by
      rw [smul_sub]; abel
    rw [this, intPairing_add, intPairing_smul]
  rw [hexp]
  rcases hk.eq_or_lt with h0 | hpos
  · -- `v` lies on the facet with normal `u_i(v)` through `w`
    obtain ⟨i', hi'⟩ := exists_rayGenerator_eq_of_pairing_eq_zero (hs := hs) (v := w) (w := v)
      (j := i) h0.symm
    have hray : polytopeToricRay γ hs w i' = polytopeToricRay γ hs v i := Subtype.ext hi'
    have h1 := toricCartierDatum_pairing D w i'
    have h2 := toricCartierDatum_pairing D v i
    rw [hi', hray] at h1
    have ht : t = 0 := by simp only [t]; rw [intPairing_sub, h1, h2, sub_self]
    rw [ht, ← h0]; simp
  · have hle : (t.natAbs : ℤ) ≤ c := by
      have h1 : t.natAbs ≤ c := by
        simp only [c, fsShift]
        calc t.natAbs ≤ ∑ i' : Fin n, (intPairing (toricCartierDatum D w - toricCartierDatum D v)
              (polytopeToricRayGenerator γ hs v i')).natAbs :=
              Finset.single_le_sum (f := fun i' => (intPairing (toricCartierDatum D w -
                toricCartierDatum D v) (polytopeToricRayGenerator γ hs v i')).natAbs)
                (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
          _ ≤ ∑ w' : latticePolytopeVertices γ, ∑ i' : Fin n, (intPairing
              (toricCartierDatum D w' - toricCartierDatum D v)
              (polytopeToricRayGenerator γ hs v i')).natAbs :=
              Finset.single_le_sum (f := fun w' : latticePolytopeVertices γ => ∑ i' : Fin n,
                (intPairing (toricCartierDatum D w' - toricCartierDatum D v)
                  (polytopeToricRayGenerator γ hs v i')).natAbs)
                (fun _ _ => Nat.zero_le _) (Finset.mem_univ w)
          _ ≤ _ := Finset.single_le_sum (f := fun v' : latticePolytopeVertices γ =>
                ∑ w' : latticePolytopeVertices γ, ∑ i' : Fin n,
                (intPairing (toricCartierDatum D w' - toricCartierDatum D v')
                  (polytopeToricRayGenerator γ hs v' i')).natAbs)
                (fun _ _ => Nat.zero_le _) (Finset.mem_univ v)
      exact_mod_cast h1
    have habs : -(t.natAbs : ℤ) ≤ t := by
      have := Int.natAbs_eq t
      rcases this with h | h <;> omega
    nlinarith

/-- Source `lma:exist_Ftheta`, Step 1 (`h = h_1 ⊗ h_2^{-1}`): the weights
`ψ_v = ψ_v(D + c D_P) - ψ_v(c D_P)` of Fubini–Study metrics. -/
def fsWeightFamily (D : ToricDivisor γ hs) : ToricWeightFamily D where
  weight v z := fsWeight (D + ((fsShift D : ℕ) : ℤ) • polytopeToricAmpleDivisor γ hs) v z -
    fsWeight (((fsShift D : ℕ) : ℤ) • polytopeToricAmpleDivisor γ hs) v z
  smooth v := (contDiff_fsWeight _ v).sub (contDiff_fsWeight _ v)
  invariant v a ha z := by
    simp only [fsWeight_action _ v a ha z]
  transition v w a := by
    have h1 := fsWeight_transition _ (isFubiniStudyDivisor_add_smul_ampleDivisor D) v w a
    have h2 := fsWeight_transition _ (isFubiniStudyDivisor_smul_ampleDivisor (hs := hs) (fsShift D)) v w a
    have hD : ∀ u : latticePolytopeVertices γ, toricCartierDatum D u =
        toricCartierDatum (D + ((fsShift D : ℕ) : ℤ) • polytopeToricAmpleDivisor γ hs) u -
          toricCartierDatum (((fsShift D : ℕ) : ℤ) • polytopeToricAmpleDivisor γ hs) u := by
      intro u
      rw [← toricCartierDatum_sub, add_sub_cancel_right]
    have hlf : ∀ (a b : Fin n → ℤ) (x : EuclideanSpace ℝ (Fin n)),
        latticeFunctional (a - b) x = latticeFunctional a x - latticeFunctional b x := by
      intro a b x
      simp only [latticeFunctional_apply, Pi.sub_apply, Int.cast_sub, sub_mul,
        Finset.sum_sub_distrib]
    rw [hD v, hD w, hlf, hlf]
    linarith
  pluriharmonic v w e u hu hv hw := by
    set E₁ := D + ((fsShift D : ℕ) : ℤ) • polytopeToricAmpleDivisor γ hs
    set E₂ := ((fsShift D : ℕ) : ℤ) • polytopeToricAmpleDivisor γ hs
    set O := (e.val.target ∩ e.val.symm ⁻¹' (originalPolytopeNativeModelChart γ hs v).source) ∩
      (e.val.target ∩ e.val.symm ⁻¹' (originalPolytopeNativeModelChart γ hs w).source)
    have hO : IsOpen O := (isOpen_chartOverlap v e).inter (isOpen_chartOverlap w e)
    have hsm : ∀ (E' : ToricDivisor γ hs), ContDiffOn ℝ ∞ (fun u' =>
        fsWeight E' v (originalPolytopeNativeModelChart γ hs v (e.val.symm u')) -
          fsWeight E' w (originalPolytopeNativeModelChart γ hs w (e.val.symm u'))) O := fun E' =>
      ((contDiffOn_comp_vertexChart_comp_symm (contDiff_fsWeight E' v) v e).mono
        inter_subset_left).sub
      ((contDiffOn_comp_vertexChart_comp_symm (contDiff_fsWeight E' w) w e).mono
        inter_subset_right)
    have hfun : (fun u' =>
        (fsWeight E₁ v (originalPolytopeNativeModelChart γ hs v (e.val.symm u')) -
          fsWeight E₂ v (originalPolytopeNativeModelChart γ hs v (e.val.symm u'))) -
        (fsWeight E₁ w (originalPolytopeNativeModelChart γ hs w (e.val.symm u')) -
          fsWeight E₂ w (originalPolytopeNativeModelChart γ hs w (e.val.symm u')))) =
        fun u' => (fsWeight E₁ v (originalPolytopeNativeModelChart γ hs v (e.val.symm u')) -
          fsWeight E₁ w (originalPolytopeNativeModelChart γ hs w (e.val.symm u'))) -
        (fsWeight E₂ v (originalPolytopeNativeModelChart γ hs v (e.val.symm u')) -
          fsWeight E₂ w (originalPolytopeNativeModelChart γ hs w (e.val.symm u'))) := by
      funext u'; ring
    change smoothDDC (fun u' =>
        (fsWeight E₁ v (originalPolytopeNativeModelChart γ hs v (e.val.symm u')) -
          fsWeight E₂ v (originalPolytopeNativeModelChart γ hs v (e.val.symm u'))) -
        (fsWeight E₁ w (originalPolytopeNativeModelChart γ hs w (e.val.symm u')) -
          fsWeight E₂ w (originalPolytopeNativeModelChart γ hs w (e.val.symm u')))) u = 0
    rw [hfun, PositiveClasses.smoothDDC_sub hO (hsm E₁) (hsm E₂) ⟨⟨hu, hv⟩, hu, hw⟩,
      smoothDDC_fsWeight_sub E₁ (isFubiniStudyDivisor_add_smul_ampleDivisor D) v w e u hu hv hw,
      smoothDDC_fsWeight_sub E₂ (isFubiniStudyDivisor_smul_ampleDivisor (hs := hs) _) v w e u hu hv hw,
      sub_zero]

/-- Source `sec:toricpob` / `lma:exist_Ftheta` (Step 1): every torus-invariant divisor `D` on
`X` carries a `T_c`-invariant smooth Hermitian metric on `O(D)`, i.e. `BigToricMetric D` is
nonempty. -/
theorem exists_bigToricMetric (D : ToricDivisor γ hs) : Nonempty (BigToricMetric D) :=
  ⟨(fsWeightFamily D).toBigToricMetric⟩

end SGPT.Toric
