import SGPT.BDivisor.BD6Glue
import SGPT.BDivisor.BD5Smooth
import SGPT.GAGA.H0LRegular
import SGPT.Projective.SmoothSchemeClopenComponents

/-!
# holomorphic maps `[F₀ : ⋯ : F_r]` with removable base locus are algebraic

Source: `rmk:bdiv:L749` (GAGA on the algebraized models of the book's blow-up system).

Let `V` be a smooth projective complex scheme (closed projective embedding `EV`, homogeneous
coordinates `homCoords i z = (x_k/x_i)(z)` on `Uᵢ = V ∩ D₊(xᵢ)`), and `F₀, …, F_r` homogeneous
polynomials of degree `e`.  Suppose that near every complex point the functions `F_k(x/xᵢ)` factor
as `h · u_k` with `h` vanishing on no open set and `u = (u_k)_k` holomorphic without common zero
(`LocalFactorization`; e.g. `h` a local equation of the base divisor).  Then the holomorphic map
`Φ(z) = [u₀(z) : ⋯ : u_r(z)]` is the analytification of a morphism `φ : V → ℙʳ` over `ℂ`
(`exists_morphism_of_localFactorization`).

Proof: `Φ` is well defined (`LocalFactorization.proportional`, the chart change
`LocalFactorization.toChart`).  At a complex point `c` with `u_j(c) ≠ 0` the regular function
`F_k/xᵢ^e` lies in the ideal of `F_j/xᵢ^e` in the algebraic stalk `𝒪_{V,c}`, since it does so in
the analytic stalk (the quotient `u_k/u_j` is holomorphic) and `𝒪_{V,c} → 𝒪^an_{V,c}` is faithfully
flat (`SGPT.Okounkov.mem_ideal_iff_schemeNativeStalkGerm`).  So `F_k/F_j` is regular on a Zariski
neighbourhood `O_c` of `c`, and the chart maps `O_c → D₊(y_j)` (`BD6Chart`) send every complex
point `p` to `Φ(p)`; they glue (`BD6Glue`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.BDivisor.BD6

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set Filter
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves SGPT.Foundations.Analysis.Pending
open SGPT.Okounkov SGPT.GAGA.H0S SGPT.NAPotential.FSPos SGPT.Projective
open SGPT.Projective.ComplexProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

variable {V : Scheme.{0}} (g : V ⟶ Spec (.of ℂ)) (EV : ClosedProjectiveEmbedding g) (n : ℕ)
  [SmoothOfRelativeDimension n g] [IsSeparated g] [QuasiCompact g]

local instance bd6MorTopology : TopologicalSpace (SchemeComplexPoint g) :=
  schemeAnalyticPointTopology g
local instance bd6MorCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint g) :=
  schemeAnalyticTNChartedSpace g n
local instance bd6MorManifold : IsComplexManifold n (SchemeComplexPoint g) :=
  schemeAnalyticTN_isComplexManifold g n

/-! ### Values -/

/-- The regular function `P(x/xᵢ)` on `Uᵢ`. -/
def chartFn (i : Fin (EV.ambientDimension + 1)) (P : MvPolynomial (Fin (EV.ambientDimension + 1)) ℂ) :
    Γ(V, coordOpen EV i) :=
  affinePresentation g EV i (polynomialProjDehomogenization ℂ EV.ambientDimension i P)

theorem chartFn_value (i : Fin (EV.ambientDimension + 1))
    (P : MvPolynomial (Fin (EV.ambientDimension + 1)) ℂ) (p : SchemeComplexPoint g)
    (hp : schemeComplexPointImage g p ∈ coordOpen EV i) :
    schemeOpenRegularFunction g n EV (coordOpen EV i) (chartFn g EV i P) p =
      MvPolynomial.eval (homCoords g EV n i p) P := by
  rw [chartFn, schemeOpenRegularFunction_affinePresentation g EV n i _ p hp,
    homCoords_eq_affineLift g EV n i hp, BD5.eval_affineLift_bd5]

theorem pointValue_eq (p : SchemeComplexPoint g) (U : V.Opens)
    (hp : schemeComplexPointImage g p ∈ U) (s : Γ(V, U)) :
    pointValue g p U hp s = schemeOpenRegularFunction g n EV U s p := by
  rw [schemeOpenRegularFunction_apply g n EV U s p hp, schemeNativeStalkGerm_eval]
  rfl

/-! ### Local factorizations -/

variable {r : ℕ} (F : Fin (r + 1) → MvPolynomial (Fin (EV.ambientDimension + 1)) ℂ)

/-- **A local factorization** of the family `F_k(x/xᵢ)` on an open set `Nb` of `Uᵢ(ℂ)`:
`F_k(x/xᵢ) = h · u_k` with `h` vanishing on no nonempty open subset and `u = (u_k)` holomorphic
without common zero. -/
structure LocalFactorization (i : Fin (EV.ambientDimension + 1)) where
  Nb : Set (SchemeComplexPoint g)
  h : SchemeComplexPoint g → ℂ
  u : Fin (r + 1) → SchemeComplexPoint g → ℂ
  isOpen : IsOpen Nb
  chart : ∀ z ∈ Nb, schemeComplexPointImage g z ∈ coordOpen EV i
  eq : ∀ z ∈ Nb, ∀ k, MvPolynomial.eval (homCoords g EV n i z) (F k) = h z * u k z
  hol : ∀ z ∈ Nb, ∀ k, HolomorphicAt n (u k) z
  ne : ∀ z ∈ Nb, (fun k => u k z) ≠ 0
  dense : ∀ W : Set (SchemeComplexPoint g), IsOpen W → W ⊆ Nb → W.Nonempty → ∃ z ∈ W, h z ≠ 0

omit [IsSeparated g] [QuasiCompact g] in
/-- Cancelling a factor that vanishes on no open set. -/
theorem eq_zero_of_mul_eq_zero {Nb : Set (SchemeComplexPoint g)} (hNb : IsOpen Nb)
    {h G : SchemeComplexPoint g → ℂ} {z : SchemeComplexPoint g} (hz : z ∈ Nb)
    (hG : ContinuousAt G z) (hmul : ∀ y ∈ Nb, h y * G y = 0)
    (hd : ∀ W : Set (SchemeComplexPoint g), IsOpen W → W ⊆ Nb → W.Nonempty → ∃ y ∈ W, h y ≠ 0) :
    G z = 0 := by
  by_contra hne
  have h1 : ∀ᶠ y in 𝓝 z, G y ≠ 0 := hG.eventually_ne hne
  obtain ⟨W, hWsub, hWo, hzW⟩ := mem_nhds_iff.mp (Filter.inter_mem h1 (hNb.mem_nhds hz))
  obtain ⟨y, hyW, hhy⟩ := hd W hWo (fun x hx => (hWsub hx).2) ⟨z, hzW⟩
  rcases mul_eq_zero.mp (hmul y (hWsub hyW).2) with h0 | h0
  · exact hhy h0
  · exact (hWsub hyW).1 h0

omit [IsSeparated g] [QuasiCompact g] in
theorem exists_ne_zero_of_ne_zero {v : Fin (r + 1) → ℂ} (hv : v ≠ 0) : ∃ l, v l ≠ 0 := by
  by_contra! h
  exact hv (funext h)

/-- **Two local factorizations in the same chart give proportional vectors.** -/
theorem LocalFactorization.proportional {i : Fin (EV.ambientDimension + 1)}
    (D D' : LocalFactorization g EV n F i) {z : SchemeComplexPoint g} (hz : z ∈ D.Nb)
    (hz' : z ∈ D'.Nb) : ∃ t : ℂ, t ≠ 0 ∧ (fun k => D'.u k z) = t • (fun k => D.u k z) := by
  obtain ⟨l, hl⟩ := exists_ne_zero_of_ne_zero (D.ne z hz)
  have hcross : ∀ k, D.u k z * D'.u l z - D.u l z * D'.u k z = 0 := by
    intro k
    have hcont : ∀ m, ContinuousAt (D.u m) z := fun m =>
      (D.hol z hz m).self_of_nhds.continuousAt
    have hcont' : ∀ m, ContinuousAt (D'.u m) z := fun m =>
      (D'.hol z hz' m).self_of_nhds.continuousAt
    refine eq_zero_of_mul_eq_zero g (D.isOpen.inter D'.isOpen) (h := D.h) ⟨hz, hz'⟩
      (((hcont k).mul (hcont' l)).sub ((hcont l).mul (hcont' k))) (fun y hy => ?_)
      (fun W hW hWsub hWne => D.dense W hW (fun x hx => (hWsub hx).1) hWne)
    have e1 := D.eq y hy.1 k
    have e2 := D'.eq y hy.2 k
    have e3 := D.eq y hy.1 l
    have e4 := D'.eq y hy.2 l
    show D.h y * (D.u k y * D'.u l y - D.u l y * D'.u k y) = 0
    have : D.h y * (D.u k y * D'.u l y - D.u l y * D'.u k y) =
        (D.h y * D.u k y) * D'.u l y - (D.h y * D.u l y) * D'.u k y := by ring
    rw [this, ← e1, ← e3, e2, e4]
    ring
  refine ⟨D'.u l z / D.u l z, ?_, funext fun k => ?_⟩
  · intro h0
    have hzero : ∀ k, D'.u k z = 0 := by
      intro k
      have := hcross k
      rw [div_eq_zero_iff, or_iff_left hl] at h0
      have h' : D.u l z * D'.u k z = 0 := by
        rw [h0, mul_zero, zero_sub, neg_eq_zero] at this; exact this
      exact (mul_eq_zero.mp h').resolve_left hl
    exact D'.ne z hz' (funext hzero)
  · simp only [Pi.smul_apply, smul_eq_mul]
    have := hcross k
    field_simp
    linear_combination -this

variable {F}

/-- The transition factor between the frames `xᵢ` and `x_l` at a complex point. -/
def frameFactor (i l : Fin (EV.ambientDimension + 1)) (y : SchemeComplexPoint g) : ℂ := by
  classical
  exact if hy : schemeComplexPointImage g y ∈ coordOpen EV i ∧ schemeComplexPointImage g y ∈ coordOpen EV l
  then Classical.choose (homCoords_transition g EV n i l hy.1 hy.2) else 1

theorem frameFactor_spec (i l : Fin (EV.ambientDimension + 1)) {y : SchemeComplexPoint g}
    (hi : schemeComplexPointImage g y ∈ coordOpen EV i)
    (hl : schemeComplexPointImage g y ∈ coordOpen EV l) :
    frameFactor g EV n i l y ≠ 0 ∧
      homCoords g EV n l y = frameFactor g EV n i l y • homCoords g EV n i y := by
  classical
  rw [frameFactor, dif_pos ⟨hi, hl⟩]
  exact Classical.choose_spec (homCoords_transition g EV n i l hi hl)

theorem eval_smul_of_isHomogeneous {N e : ℕ} {P : MvPolynomial (Fin (N + 1)) ℂ}
    (hP : P.IsHomogeneous e) (t : ℂ) (v : Fin (N + 1) → ℂ) :
    MvPolynomial.eval (t • v) P = t ^ e * MvPolynomial.eval v P := by
  have h := homogeneousPolynomial_eval₂_scaled hP (RingHom.id ℂ) v t
  have hv : t • v = fun i => t * v i := rfl
  change MvPolynomial.eval₂Hom (RingHom.id ℂ) (t • v) P =
    t ^ e * MvPolynomial.eval₂Hom (RingHom.id ℂ) v P
  rw [hv]
  exact h

/-- **Change of chart** of a local factorization (homogeneous `F`): the same `u`, and `h`
multiplied by the transition factor. -/
def LocalFactorization.toChart {e : ℕ} (hF : ∀ k, (F k).IsHomogeneous e)
    {i : Fin (EV.ambientDimension + 1)} (D : LocalFactorization g EV n F i)
    (l : Fin (EV.ambientDimension + 1)) : LocalFactorization g EV n F l where
  Nb := D.Nb ∩ schemeComplexPointImage g ⁻¹' (coordOpen EV l : Set V)
  h := fun y => frameFactor g EV n i l y ^ e * D.h y
  u := D.u
  isOpen := D.isOpen.inter (isOpen_coordOpen_points g EV l)
  chart := fun z hz => hz.2
  eq := fun z hz k => by
    obtain ⟨-, hc⟩ := frameFactor_spec g EV n i l (D.chart z hz.1) hz.2
    rw [hc, eval_smul_of_isHomogeneous (hF k), D.eq z hz.1 k]
    ring
  hol := fun z hz k => D.hol z hz.1 k
  ne := fun z hz => D.ne z hz.1
  dense := fun W hW hWsub hWne => by
    obtain ⟨y, hyW, hy⟩ := D.dense W hW (fun x hx => (hWsub hx).1) hWne
    refine ⟨y, hyW, mul_ne_zero (pow_ne_zero _ ?_) hy⟩
    exact (frameFactor_spec g EV n i l (D.chart y (hWsub hyW).1) (hWsub hyW).2).1

/-- **Local factorizations in any two charts give proportional vectors.** -/
theorem LocalFactorization.proportional' {e : ℕ} (hF : ∀ k, (F k).IsHomogeneous e)
    {i l : Fin (EV.ambientDimension + 1)} (D : LocalFactorization g EV n F i)
    (D' : LocalFactorization g EV n F l) {z : SchemeComplexPoint g} (hz : z ∈ D.Nb)
    (hz' : z ∈ D'.Nb) : ∃ t : ℂ, t ≠ 0 ∧ (fun k => D'.u k z) = t • (fun k => D.u k z) :=
  (D.toChart g EV n hF l).proportional g EV n F D' ⟨hz, D'.chart z hz'⟩ hz'

omit [IsSeparated g] [QuasiCompact g] in
theorem nonzeroVectorPoint_smul (v : Fin (r + 1) → ℂ) (hv : v ≠ 0) {t : ℂ} (ht : t ≠ 0)
    (htv : t • v ≠ 0) :
    polynomialProjNonzeroVectorPoint r ⟨t • v, htv⟩ = polynomialProjNonzeroVectorPoint r ⟨v, hv⟩ := by
  obtain ⟨k, hk⟩ := exists_ne_zero_of_ne_zero hv
  have hk' : (t • v) k ≠ 0 := by simpa only [Pi.smul_apply, smul_eq_mul] using mul_ne_zero ht hk
  rw [polynomialProjNonzeroVectorPoint_eq_chart r ⟨t • v, htv⟩ k hk',
    polynomialProjNonzeroVectorPoint_eq_chart r ⟨v, hv⟩ k hk]
  exact polynomialProjVectorChartPoint_smul r k v t ht

/-- **The holomorphic map `Φ = [u₀ : ⋯ : u_r]`**, read at a chosen local factorization. -/
def phiPoint (hloc : ∀ z : SchemeComplexPoint g, ∃ i, ∃ D : LocalFactorization g EV n F i, z ∈ D.Nb)
    (z : SchemeComplexPoint g) : SchemeComplexPoint (polynomialProjStructureMap ℂ r) :=
  polynomialProjNonzeroVectorPoint r
    ⟨fun k => (Classical.choose (Classical.choose_spec (hloc z))).u k z,
      (Classical.choose (Classical.choose_spec (hloc z))).ne z
        (Classical.choose_spec (Classical.choose_spec (hloc z)))⟩

/-- `Φ` is computed by every local factorization. -/
theorem phiPoint_eq {e : ℕ} (hF : ∀ k, (F k).IsHomogeneous e)
    (hloc : ∀ z : SchemeComplexPoint g, ∃ i, ∃ D : LocalFactorization g EV n F i, z ∈ D.Nb)
    {i : Fin (EV.ambientDimension + 1)} (D : LocalFactorization g EV n F i)
    {z : SchemeComplexPoint g} (hz : z ∈ D.Nb) :
    phiPoint g EV n hloc z = polynomialProjNonzeroVectorPoint r ⟨fun k => D.u k z, D.ne z hz⟩ := by
  set D₀ := Classical.choose (Classical.choose_spec (hloc z))
  have hz₀ : z ∈ D₀.Nb := Classical.choose_spec (Classical.choose_spec (hloc z))
  obtain ⟨t, ht, heq⟩ := D₀.proportional' g EV n hF D hz₀ hz
  unfold phiPoint
  change _ = polynomialProjNonzeroVectorPoint r ⟨fun k => D.u k z, _⟩
  have hv : (fun k => D.u k z) ≠ 0 := D.ne z hz
  have hsub : (⟨fun k => D.u k z, hv⟩ : {v : Fin (r + 1) → ℂ // v ≠ 0}) =
      ⟨t • (fun k => D₀.u k z), heq ▸ hv⟩ := Subtype.ext heq
  rw [hsub, nonzeroVectorPoint_smul _ (D₀.ne z hz₀) ht]

/-! ### Regularity of the ratios: faithful flatness -/

/-- **The ratio `F_k/F_j` is algebraic at `c`** when `u_j(c) ≠ 0`: the germ of `F_k(x/xᵢ)` lies in
the ideal generated by the germ of `F_j(x/xᵢ)` in the algebraic stalk `𝒪_{V,c}`. -/
theorem germ_mem_span_germ {i : Fin (EV.ambientDimension + 1)} (D : LocalFactorization g EV n F i)
    {c : SchemeComplexPoint g} (hc : c ∈ D.Nb) {j : Fin (r + 1)} (hj : D.u j c ≠ 0)
    (k : Fin (r + 1)) :
    V.presheaf.germ (coordOpen EV i) (schemeComplexPointImage g c) (D.chart c hc)
        (chartFn g EV i (F k)) ∈
      Ideal.span {V.presheaf.germ (coordOpen EV i) (schemeComplexPointImage g c) (D.chart c hc)
        (chartFn g EV i (F j))} := by
  rw [mem_ideal_iff_schemeNativeStalkGerm g n c, Ideal.map_span, Set.image_singleton,
    ← schemeOpenRegularFunction_germ g n EV _ _ c (D.chart c hc),
    ← schemeOpenRegularFunction_germ g n EV _ _ c (D.chart c hc), Ideal.mem_span_singleton']
  have hq : HolomorphicAt n (fun y => D.u k y * (D.u j y)⁻¹) c :=
    (D.hol c hc k).mul (RelativePrincipalizationSpan.holomorphicAt_inv (D.hol c hc j) hj)
  refine ⟨NativeHolGerm.mk _ hq, ?_⟩
  apply Subtype.ext
  change ((fun y => D.u k y * (D.u j y)⁻¹ *
      schemeOpenRegularFunction g n EV (coordOpen EV i) (chartFn g EV i (F j)) y :
        SchemeComplexPoint g → ℂ) : Germ (𝓝 c) ℂ) = _
  apply Germ.coe_eq.mpr
  have hne : ∀ᶠ y in 𝓝 c, D.u j y ≠ 0 :=
    (D.hol c hc j).self_of_nhds.continuousAt.eventually_ne hj
  filter_upwards [hne, D.isOpen.mem_nhds hc] with y hy hyN
  rw [chartFn_value g EV n i _ y (D.chart y hyN), chartFn_value g EV n i _ y (D.chart y hyN),
    D.eq y hyN j, D.eq y hyN k]
  field_simp

omit [IsSeparated g] [QuasiCompact g] in
theorem presheaf_map_map {U W O : V.Opens} (h₁ : O ≤ W) (h₂ : W ≤ U) (s : Γ(V, U)) :
    V.presheaf.map (homOfLE h₁).op (V.presheaf.map (homOfLE h₂).op s) =
      V.presheaf.map (homOfLE (h₁.trans h₂)).op s := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

/-- **The ratios on a Zariski neighbourhood.** At `c` with `u_j(c) ≠ 0` there are an open
`c ∈ O ⊆ Uᵢ` and regular functions `t_k` on `O` with `t_j = 1` and `t_k · F_j(x/xᵢ) = F_k(x/xᵢ)`
on `O`. -/
theorem exists_chart_ratio {i : Fin (EV.ambientDimension + 1)} (D : LocalFactorization g EV n F i)
    {c : SchemeComplexPoint g} (hc : c ∈ D.Nb) {j : Fin (r + 1)} (hj : D.u j c ≠ 0) :
    ∃ (O : V.Opens) (_ : schemeComplexPointImage g c ∈ O) (hOi : O ≤ coordOpen EV i)
      (t : Fin (r + 1) → Γ(V, O)), t j = 1 ∧ ∀ k,
        t k * V.presheaf.map (homOfLE hOi).op (chartFn g EV i (F j)) =
          V.presheaf.map (homOfLE hOi).op (chartFn g EV i (F k)) := by
  classical
  set x := schemeComplexPointImage g c
  have hxi : x ∈ coordOpen EV i := D.chart c hc
  have hW : ∀ k, ∃ (W : V.Opens) (_ : x ∈ W) (hWi : W ≤ coordOpen EV i) (s : Γ(V, W)),
      s * V.presheaf.map (homOfLE hWi).op (chartFn g EV i (F j)) =
        V.presheaf.map (homOfLE hWi).op (chartFn g EV i (F k)) := by
    intro k
    obtain ⟨σ, hσ⟩ := Ideal.mem_span_singleton'.mp (germ_mem_span_germ g EV n D hc hj k)
    obtain ⟨U, hUi, hxU, s, hs⟩ := V.presheaf.exists_le_germ_eq σ hxi
    have hgerm : V.presheaf.germ U x hxU (s * V.presheaf.map (homOfLE hUi).op
        (chartFn g EV i (F j))) =
          V.presheaf.germ U x hxU (V.presheaf.map (homOfLE hUi).op (chartFn g EV i (F k))) := by
      rw [map_mul, hs, TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply, hσ]
    obtain ⟨W, hxW, iU, iU', heq⟩ := V.presheaf.germ_eq x hxU hxU _ _ hgerm
    have hWU : W ≤ U := leOfHom iU
    refine ⟨W, hxW, hWU.trans hUi, V.presheaf.map (homOfLE hWU).op s, ?_⟩
    have e1 : iU = homOfLE hWU := Subsingleton.elim _ _
    have e2 : iU' = homOfLE hWU := Subsingleton.elim _ _
    rw [e1, e2, map_mul, presheaf_map_map, presheaf_map_map] at heq
    exact heq
  choose W hxW hWi s hs using hW
  have hO : x ∈ ⨅ k, W k := by
    rw [← SetLike.mem_coe, TopologicalSpace.Opens.coe_iInf, Set.mem_iInter]
    exact hxW
  have hOW : ∀ k, (⨅ k, W k) ≤ W k := fun k => iInf_le W k
  have hOi : (⨅ k, W k) ≤ coordOpen EV i := (hOW j).trans (hWi j)
  refine ⟨⨅ k, W k, hO, hOi, fun k => if k = j then 1 else
    V.presheaf.map (homOfLE (hOW k)).op (s k), if_pos rfl, fun k => ?_⟩
  dsimp only
  by_cases hk : k = j
  · subst hk; rw [if_pos rfl, one_mul]
  · rw [if_neg hk]
    have := congrArg (V.presheaf.map (homOfLE (hOW k)).op) (hs k)
    rw [map_mul, presheaf_map_map, presheaf_map_map] at this
    exact this

/-! ### The chart maps compute `Φ` -/

/-- On a Zariski open `O ⊆ Uᵢ` where `t_k · F_j(x/xᵢ) = F_k(x/xᵢ)` (`t_j = 1`), the chart map
`[t₀ : ⋯ : t_r]` sends every complex point `p` to `Φ(p)`. -/
theorem chartPoint_eq_phiPoint {e : ℕ} (hF : ∀ k, (F k).IsHomogeneous e)
    (hloc : ∀ z : SchemeComplexPoint g, ∃ i, ∃ D : LocalFactorization g EV n F i, z ∈ D.Nb)
    {i : Fin (EV.ambientDimension + 1)} {j : Fin (r + 1)} {O : V.Opens}
    (hOi : O ≤ coordOpen EV i) {t : Fin (r + 1) → Γ(V, O)} (htj : t j = 1)
    (ht : ∀ k, t k * V.presheaf.map (homOfLE hOi).op (chartFn g EV i (F j)) =
      V.presheaf.map (homOfLE hOi).op (chartFn g EV i (F k)))
    (p : SchemeComplexPoint g) (hp : schemeComplexPointImage g p ∈ O) :
    polynomialProjVectorChartPoint r j (fun k => pointValue g p O hp (t k)) =
      phiPoint g EV n hloc p := by
  obtain ⟨i', Dp, hpD⟩ := hloc p
  set D' := Dp.toChart g EV n hF i
  have hpD' : p ∈ D'.Nb := ⟨hpD, hOi hp⟩
  set T : Fin (r + 1) → SchemeComplexPoint g → ℂ :=
    fun k => schemeOpenRegularFunction g n EV O (t k) with hTdef
  have hT : ∀ k, pointValue g p O hp (t k) = T k p := fun k => pointValue_eq g EV n p O hp (t k)
  have hid : ∀ y ∈ D'.Nb ∩ schemeComplexPointImage g ⁻¹' (O : Set V), ∀ k,
      T k y * (D'.h y * D'.u j y) = D'.h y * D'.u k y := by
    intro y hy k
    have hyi : schemeComplexPointImage g y ∈ coordOpen EV i := D'.chart y hy.1
    have h1 := congrArg (fun s => schemeOpenRegularFunction g n EV O s y) (ht k)
    simp only at h1
    rw [schemeOpenRegularFunction_mul g n EV O _ _ hy.2] at h1
    beta_reduce at h1
    rw [schemeOpenRegularFunction_restrict g n EV O (coordOpen EV i) hOi _ hy.2,
      schemeOpenRegularFunction_restrict g n EV O (coordOpen EV i) hOi _ hy.2,
      chartFn_value g EV n i _ y hyi, chartFn_value g EV n i _ y hyi,
      D'.eq y hy.1 j, D'.eq y hy.1 k] at h1
    exact h1
  have hNb : IsOpen (D'.Nb ∩ schemeComplexPointImage g ⁻¹' (O : Set V)) :=
    D'.isOpen.inter (O.isOpen.preimage (schemeComplexPointImage_continuous g))
  have hcancel : ∀ k, T k p * D'.u j p - D'.u k p = 0 := by
    intro k
    have hTc : ContinuousAt (T k) p :=
      (schemeOpenRegularFunction_holomorphicAt g n EV O (t k) p hp).self_of_nhds.continuousAt
    refine eq_zero_of_mul_eq_zero g hNb (h := D'.h) ⟨hpD', hp⟩
      ((hTc.mul (D'.hol p hpD' j).self_of_nhds.continuousAt).sub
        (D'.hol p hpD' k).self_of_nhds.continuousAt) (fun y hy => ?_)
      (fun W hW hWsub hWne => D'.dense W hW (fun x hx => (hWsub hx).1) hWne)
    show D'.h y * (T k y * D'.u j y - D'.u k y) = 0
    linear_combination hid y hy k
  have huj : D'.u j p ≠ 0 := by
    intro h0
    apply D'.ne p hpD'
    funext k
    have := hcancel k
    rw [h0, mul_zero, zero_sub, neg_eq_zero] at this
    exact this
  have hTj : T j p = 1 := by
    simp only [hTdef, htj]
    exact schemeOpenRegularFunction_one g n EV O hp
  have hvec : (fun k => D'.u k p) = D'.u j p • (fun k => T k p) := by
    funext k
    simp only [Pi.smul_apply, smul_eq_mul]
    linear_combination -(hcancel k)
  have hTne : (fun k => T k p) ≠ 0 := by
    intro h0
    have := congrFun h0 j
    rw [hTj] at this
    exact one_ne_zero this
  rw [phiPoint_eq g EV n hF hloc D' hpD']
  have hsub : (⟨fun k => D'.u k p, D'.ne p hpD'⟩ : {v : Fin (r + 1) → ℂ // v ≠ 0}) =
      ⟨D'.u j p • (fun k => T k p), hvec ▸ D'.ne p hpD'⟩ := Subtype.ext hvec
  rw [hsub, nonzeroVectorPoint_smul _ hTne huj,
    polynomialProjNonzeroVectorPoint_eq_chart r _ j (by show T j p ≠ 0; rw [hTj]; exact one_ne_zero)]
  congr 1
  funext k
  exact hT k

/-! ### The algebraic morphism -/

/-- **Holomorphic maps `[F₀ : ⋯ : F_r]` with a removable base locus are algebraic.**  For a smooth
projective complex scheme `V` and homogeneous polynomials `F_k` of degree `e` admitting local
factorizations `F_k(x/xᵢ) = h · u_k` near every complex point (`h` vanishing on no open set, `u`
holomorphic without common zero), there is a morphism `φ : V → ℙʳ` over `ℂ` whose complex points
are `φ(z) = Φ(z) = [u₀(z) : ⋯ : u_r(z)]` for every local factorization. -/
theorem exists_morphism_of_localFactorization {e : ℕ} (hF : ∀ k, (F k).IsHomogeneous e)
    (hloc : ∀ z : SchemeComplexPoint g, ∃ i, ∃ D : LocalFactorization g EV n F i, z ∈ D.Nb) :
    ∃ (φ : V ⟶ polynomialProj ℂ r) (hφ : φ ≫ polynomialProjStructureMap ℂ r = g),
      ∀ z, schemeComplexPointMap g (polynomialProjStructureMap ℂ r) φ hφ z =
        phiPoint g EV n hloc z := by
  classical
  have hdata : ∀ c : SchemeComplexPoint g, ∃ (j : Fin (r + 1)) (O : V.Opens)
      (_ : schemeComplexPointImage g c ∈ O) (i : Fin (EV.ambientDimension + 1))
      (hOi : O ≤ coordOpen EV i) (t : Fin (r + 1) → Γ(V, O)), t j = 1 ∧ ∀ k,
        t k * V.presheaf.map (homOfLE hOi).op (chartFn g EV i (F j)) =
          V.presheaf.map (homOfLE hOi).op (chartFn g EV i (F k)) := by
    intro c
    obtain ⟨i, D, hc⟩ := hloc c
    obtain ⟨j, hj⟩ := exists_ne_zero_of_ne_zero (D.ne c hc)
    obtain ⟨O, hcO, hOi, t, htj, ht⟩ := exists_chart_ratio g EV n D hc hj
    exact ⟨j, O, hcO, i, hOi, t, htj, ht⟩
  choose j O hcO i hOi t htj ht using hdata
  have := EV.locallyOfFiniteType
  have hcover : TopologicalSpace.IsOpenCover O := by
    apply top_unique
    intro y _
    obtain ⟨p, -, hyp⟩ := SGPT.GAGA.H0L.exists_specializes_schemeComplexPoint g
      (W := ⊤) (y := y) trivial
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨p, hyp.mem_open (O p).isOpen (hcO p)⟩
  have hcompat : ∀ (a b : SchemeComplexPoint g) (p : SchemeComplexPoint g)
      (hU : schemeComplexPointImage g p ∈ O a) (hV : schemeComplexPointImage g p ∈ O b),
      polynomialProjVectorChartPoint r (j a) (fun k => pointValue g p (O a) hU (t a k)) =
        polynomialProjVectorChartPoint r (j b) (fun k => pointValue g p (O b) hV (t b k)) :=
    fun a b p hU hV => (chartPoint_eq_phiPoint g EV n hF hloc (hOi a) (htj a) (ht a) p hU).trans
      (chartPoint_eq_phiPoint g EV n hF hloc (hOi b) (htj b) (ht b) p hV).symm
  have : AlgebraicGeometry.IsReduced V :=
    SGPT.Projective.NumEq.AlgebraicCurveDegree.smoothScheme_isReduced g n
  refine ⟨glueChartMaps g O hcover j t htj hcompat,
    glueChartMaps_structure g O hcover j t htj hcompat, fun z => ?_⟩
  rw [glueChartMaps_point g O hcover j t htj hcompat z z (hcO z)]
  exact chartPoint_eq_phiPoint g EV n hF hloc (hOi z) (htj z) (ht z) z (hcO z)

end SGPT.BDivisor.BD6
