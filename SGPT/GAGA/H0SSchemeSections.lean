import SGPT.GAGA.H0SSchemeEmbedding

/-!
# Holomorphic sections of `𝒪_X(j)` as functions on the affine cone


Let `H` be any smooth metric on `𝒪_X(1) = E.map^*𝒪(1)` (e.g. FS-POS's Fubini–Study metric) and
`s` a holomorphic section of `((𝒪_X(1), H)^an)^{⊗ j}`, with coefficients `sᵢ = coef s i` in the
frames `xᵢ^j` (the twisted atlas frames of lane GAGAMULT2).

* `coef_transition`: `s_l = (x_i/x_l)^j sᵢ` on `Uᵢ ∩ U_l` (more precisely, the `j`-th power of
  the analytic transition of the frames).
* `coneFun s`: the function `F_s(Z) = Z_i^j sᵢ(p)` on the affine cone over `X(ℂ) ⊆ ℙᴺ`, for
  `[Z] = p` and any `i` with `p ∈ Uᵢ` (`coneFun_eq`); it is homogeneous of degree `j`
  (`coneFun_smul`) and holomorphic off the vertex (`isLocallyHolomorphicOn_coneFun`, through
  the local holomorphic inverse of `X(ℂ) → ℙᴺ` given by `exists_affine_graph`).
* **`eventually_sectionsPolynomial`**: if `X(ℂ) ⊆ ℙᴺ` has polynomial equations satisfying the
  Jacobian criterion (`IsJacobianPresentation`), then for `j ≫ 0` every holomorphic section of
  `𝒪_X(j)` is `P(x/xᵢ)·xᵢ^j` for a homogeneous polynomial `P` of degree `j`; for the
  Fubini–Study metric this is FS-POS's `HyperplaneSectionsPolynomial`
  (`eventually_hyperplaneSectionsPolynomial`), hence GAGA for the sections of `𝒪_X(j)`
  (`eventually_schemeSectionsAlgebraic`) and `MultiplierIdealAlgebraic`
  (`multiplierIdealAlgebraic_of_jacobianPresentation`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.GAGA.H0S

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Filter Set Metric Bundle
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Okounkov SGPT.NAPotential.FSPos SGPT.NAPotential.GAGAMult SGPT.Projective
  SGPT.Projective.ComplexProjectiveSpace SGPT.GAGA.H0
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle
open scoped Topology Manifold

attribute [local instance] MvPolynomial.gradedAlgebra

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (E : ClosedProjectiveEmbedding f) (n : ℕ)
  [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f]

local instance h0sSecTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance h0sSecCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance h0sSecManifold : IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n

/-- The homogeneous coordinates in the frames `xᵢ` and `x_l` differ by the analytic transition
of the frames. -/
theorem homCoords_transition_eq (i l : Fin (E.ambientDimension + 1)) {p : SchemeComplexPoint f}
    (hpi : schemeComplexPointImage f p ∈ coordOpen E i)
    (hpl : schemeComplexPointImage f p ∈ coordOpen E l) :
    homCoords f E n l p = schemeFrameTransition f n E ((hyperplaneAtlas E).frame i)
      ((hyperplaneAtlas E).frame l) p • homCoords f E n i p := by
  funext k
  have h := coordFun_transition f E n ((hyperplaneAtlas E).frame i) ((hyperplaneAtlas E).frame l) k
    p hpi hpl
  change schemeOpenRegularFunction f n E (coordOpen E l)
      (coordCoef E ((hyperplaneAtlas E).frame l) k) p = _ *
    schemeOpenRegularFunction f n E (coordOpen E i)
      (coordCoef E ((hyperplaneAtlas E).frame i) k) p at h
  rw [coordCoef_atlas, coordCoef_atlas] at h
  exact h

variable (H : SchemeLineBundleMetric f n E (hyperplaneBundle E)) {j : ℕ}

/-- The coefficient of a section `s` of `𝒪_X(j)` in the frame `xᵢ^j`. -/
def coef (s : twistedSections (schemeHermitianLineBundle f n E (hyperplaneAtlas E) H) unit j)
    (i : Fin (E.ambientDimension + 1)) (p : SchemeComplexPoint f) : ℂ :=
  (twistedFrame f n E (hyperplaneAtlas E) H ((hyperplaneAtlas E).frame i) j).val.continuousLinearMapAt
    ℂ p (s p)

/-- The analytic transition of `(𝒪_X(1), H)^an` between two algebraic frames. -/
theorem coordChangeL_schemeHermitianAtlasFrame {U V : X.Opens}
    (α : LocalBundleFrame (hyperplaneBundle E) U) (β : LocalBundleFrame (hyperplaneBundle E) V)
    {p : SchemeComplexPoint f} (hpU : schemeComplexPointImage f p ∈ U)
    (hpV : schemeComplexPointImage f p ∈ V) :
    ((schemeHermitianAtlasFrame f n E (hyperplaneAtlas E) H α).val.coordChangeL ℂ
      (schemeHermitianAtlasFrame f n E (hyperplaneAtlas E) H β).val p) 1 =
        schemeFrameTransition f n E α β p := by
  rw [Trivialization.coordChangeL_apply _ _ ⟨hpU, hpV⟩]
  change frameCoef f n E (hyperplaneAtlas E) H β p *
      (show ℂ from (schemeHermitianTrivialization f n E (hyperplaneAtlas E) H α).symm p 1) = _
  rw [schemeHermitianTrivialization_symm f n E (hyperplaneAtlas E) H α hpU,
    frameCoef_transition f n E (hyperplaneAtlas E) H α β hpU hpV, mul_one, mul_assoc,
    mul_inv_cancel₀ (frameCoef_ne_zero f n E (hyperplaneAtlas E) H α hpU), mul_one]

/-- **Transition of the coefficients**: `s_l = g_{il}^j sᵢ` on `Uᵢ ∩ U_l`. -/
theorem coef_transition
    (s : twistedSections (schemeHermitianLineBundle f n E (hyperplaneAtlas E) H) unit j)
    (i l : Fin (E.ambientDimension + 1)) {p : SchemeComplexPoint f}
    (hpi : schemeComplexPointImage f p ∈ coordOpen E i)
    (hpl : schemeComplexPointImage f p ∈ coordOpen E l) :
    coef f E n H s l p = schemeFrameTransition f n E ((hyperplaneAtlas E).frame i)
      ((hyperplaneAtlas E).frame l) p ^ j * coef f E n H s i p := by
  set e := twistedFrame f n E (hyperplaneAtlas E) H ((hyperplaneAtlas E).frame i) j
  set e' := twistedFrame f n E (hyperplaneAtlas E) H ((hyperplaneAtlas E).frame l) j
  have he : p ∈ e.val.baseSet := mem_twistedFrame_baseSet f n E (hyperplaneAtlas E) H _ j hpi
  have he' : p ∈ e'.val.baseSet := mem_twistedFrame_baseSet f n E (hyperplaneAtlas E) H _ j hpl
  have htr := twistedPower_frame_transition
    (schemeHermitianAtlasFrame f n E (hyperplaneAtlas E) H ((hyperplaneAtlas E).frame i))
    (schemeHermitianAtlasFrame f n E (hyperplaneAtlas E) H ((hyperplaneAtlas E).frame l))
    (unitAtlasFrame (n := n) (M := SchemeComplexPoint f)) unitAtlasFrame
    (x := p) hpi hpl (Set.mem_univ p) (Set.mem_univ p) j
  have hu : ((unitAtlasFrame (n := n) (M := SchemeComplexPoint f)).val.coordChangeL ℂ
      unitAtlasFrame.val p) 1 = 1 := by
    change ((Bundle.Trivial.trivialization (SchemeComplexPoint f) ℂ).coordChangeL ℂ
      (Bundle.Trivial.trivialization (SchemeComplexPoint f) ℂ) p) 1 = 1
    rw [Bundle.Trivial.trivialization.coordChangeL]
    rfl
  rw [hu, mul_one, coordChangeL_schemeHermitianAtlasFrame f E n H _ _ hpi hpl] at htr
  unfold coef
  rw [Trivialization.continuousLinearMapAt_apply_of_mem (R := ℂ) e'.val he',
    Trivialization.continuousLinearMapAt_apply_of_mem (R := ℂ) e.val he]
  have hs : s p = e.val.symm p ((e.val ⟨p, s p⟩).2) := (e.val.symm_apply_apply_mk he (s p)).symm
  conv_lhs => rw [hs]
  rw [← Trivialization.coordChangeL_apply (R := ℂ) e.val e'.val ⟨he, he'⟩]
  have hlin : (e.val.coordChangeL ℂ e'.val p) ((e.val ⟨p, s p⟩).2) =
      (e.val ⟨p, s p⟩).2 * (e.val.coordChangeL ℂ e'.val p) 1 := by
    rw [← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one]
  rw [hlin]
  change _ * ((twistedPowerAtlasFrame _ _ j).val.coordChangeL ℂ
    (twistedPowerAtlasFrame _ _ j).val p) 1 = _
  rw [htr, mul_comm]

/-- The coefficients are holomorphic on `Uᵢ(ℂ)`. -/
theorem holomorphicAt_coef
    (s : twistedSections (schemeHermitianLineBundle f n E (hyperplaneAtlas E) H) unit j)
    (i : Fin (E.ambientDimension + 1)) {p : SchemeComplexPoint f}
    (hp : schemeComplexPointImage f p ∈ coordOpen E i) :
    HolomorphicAt n (coef f E n H s i) p :=
  holomorphicAt_coef_of_contMDiff
    (twistedFrame f n E (hyperplaneAtlas E) H ((hyperplaneAtlas E).frame i) j).val
    s.contMDiff (mem_twistedFrame_baseSet f n E (hyperplaneAtlas E) H _ j hp)

/-! ### The cone function -/

/-- **The function `F_s` on the affine cone**: `F_s(Z) = Z_i^j sᵢ(p)` if `[Z] = p ∈ X(ℂ)`,
`i` the chosen frame index at `p`, and `0` otherwise. -/
def coneFun (s : twistedSections (schemeHermitianLineBundle f n E (hyperplaneAtlas E) H) unit j)
    (Z : ComplexModel (E.ambientDimension + 1)) : ℂ := by
  classical
  exact if h : ∃ (p : SchemeComplexPoint f) (hZ : WithLp.ofLp Z ≠ 0),
      projectivePoint f E n p = mk (WithLp.ofLp Z) hZ then
    Z (frameIndex f E h.choose) ^ j * coef f E n H s (frameIndex f E h.choose) h.choose
  else 0

/-- `F_s(Z) = Z_l^j s_l(p)` for `[Z] = p` and every `l` with `p ∈ U_l`. -/
theorem coneFun_eq
    (s : twistedSections (schemeHermitianLineBundle f n E (hyperplaneAtlas E) H) unit j)
    {Z : ComplexModel (E.ambientDimension + 1)} {p : SchemeComplexPoint f}
    (hZ : WithLp.ofLp Z ≠ 0) (hp : projectivePoint f E n p = mk (WithLp.ofLp Z) hZ)
    (l : Fin (E.ambientDimension + 1)) (hl : schemeComplexPointImage f p ∈ coordOpen E l) :
    coneFun f E n H s Z = Z l ^ j * coef f E n H s l p := by
  classical
  have hex : ∃ (p : SchemeComplexPoint f) (hZ : WithLp.ofLp Z ≠ 0),
      projectivePoint f E n p = mk (WithLp.ofLp Z) hZ := ⟨p, hZ, hp⟩
  unfold coneFun
  rw [dif_pos hex]
  have hpp : hex.choose = p := by
    apply injective_projectivePoint f E n
    obtain ⟨hZ', h'⟩ := hex.choose_spec
    rw [h', hp]
  rw [hpp]
  set i := frameIndex f E p
  have hi := mem_coordOpen_frameIndex f E p
  -- `Z = c • (homogeneous coordinates in the frame xᵢ)`
  have hZi : mk (homCoords f E n i p) (homCoords_ne_zero f E n i hi) = mk (WithLp.ofLp Z) hZ := by
    rw [← projectivePoint_eq f E n i hi, hp]
  obtain ⟨c, hc, hcZ⟩ := exists_eq_smul_of_mk_eq hZi
  have hZi' : Z i = c := by
    have := congrFun hcZ i
    rw [Pi.smul_apply, homCoords_self f E n i hi, smul_eq_mul, mul_one] at this
    exact this
  set g := schemeFrameTransition f n E ((hyperplaneAtlas E).frame i) ((hyperplaneAtlas E).frame l) p
  have hg := homCoords_transition_eq f E n i l hi hl
  have hgl : g * homCoords f E n i p l = 1 := by
    have := congrFun hg l
    rw [homCoords_self f E n l hl, Pi.smul_apply, smul_eq_mul] at this
    exact this.symm
  have hZl : Z l * g = c := by
    have := congrFun hcZ l
    rw [Pi.smul_apply, smul_eq_mul] at this
    change Z l = _ at this
    rw [this, mul_assoc, mul_comm (homCoords f E n i p l), hgl, mul_one]
  rw [coef_transition f E n H s i l hi hl, hZi', ← mul_assoc, ← mul_pow, hZl]

/-- `F_s` is homogeneous of degree `j ≥ 1` on the cone. -/
theorem coneFun_smul
    (s : twistedSections (schemeHermitianLineBundle f n E (hyperplaneAtlas E) H) unit j)
    (hj : 1 ≤ j) (c : ℂ) {Z : ComplexModel (E.ambientDimension + 1)}
    (hZ : Z ∈ affineCone (range (projectivePoint f E n))) :
    coneFun f E n H s (c • Z) = c ^ j * coneFun f E n H s Z := by
  classical
  have h0 : coneFun f E n H s 0 = 0 := by
    unfold coneFun
    rw [dif_neg]
    rintro ⟨p, hZ, -⟩
    exact hZ rfl
  by_cases hc : c = 0
  · subst hc
    rw [zero_smul, h0, zero_pow (by omega), zero_mul]
  by_cases hZ0 : WithLp.ofLp Z = 0
  · have : Z = 0 := by simpa using hZ0
    subst this
    rw [smul_zero, h0, mul_zero]
  obtain ⟨p, hp⟩ := hZ hZ0
  set l := frameIndex f E p
  have hl := mem_coordOpen_frameIndex f E p
  have hcZ : WithLp.ofLp (c • Z) ≠ 0 := by
    change c • WithLp.ofLp Z ≠ 0
    exact smul_ne_zero hc hZ0
  have hp' : projectivePoint f E n p = mk (WithLp.ofLp (c • Z)) hcZ := by
    rw [hp]
    exact (mk_smul hZ0 hc).symm
  rw [coneFun_eq f E n H s hcZ hp' l hl, coneFun_eq f E n H s hZ0 hp l hl]
  change (c * Z l) ^ j * _ = _
  ring

variable [CompactSpace (SchemeComplexPoint f)]

/-- `F_s` is holomorphic on the cone off the vertex. -/
theorem isLocallyHolomorphicOn_coneFun
    (s : twistedSections (schemeHermitianLineBundle f n E (hyperplaneAtlas E) H) unit j) :
    IsLocallyHolomorphicOn (affineCone (range (projectivePoint f E n))) (coneFun f E n H s) := by
  intro Z₀ hZ₀ h0
  obtain ⟨i, hZi⟩ : ∃ i, Z₀ i ≠ 0 := by
    by_contra h
    push Not at h
    exact h0 (by ext k; simpa using h k)
  have hv₀ : WithLp.ofLp Z₀ ≠ 0 := fun h => hZi (by simpa using congrFun h i)
  obtain ⟨p₀, hp₀⟩ := hZ₀ hv₀
  have hsrc : projectivePoint f E n p₀ ∈ (affineChart i).source := by
    rw [hp₀]; exact (mk_mem_affineChart_source_iff i hv₀).mpr hZi
  have hy₀ : affineChart i (projectivePoint f E n p₀) = (Z₀ i)⁻¹ • numer i Z₀ := by
    rw [hp₀, affineChart_mk i hv₀ hZi, affineRatio_eq_smul_numer]
  obtain ⟨-, L0, ε, O, g, ψ, hε, hOo, -, hψ, hψdom, -, hgraph⟩ :=
    exists_affine_graph (isHolomorphicEmbedding_projectivePoint f E n) p₀ i hsrc
  rw [hy₀] at hgraph
  set e := (complexChartAt (n := n) p₀).val
  set y : ComplexModel (E.ambientDimension + 1) → ComplexModel E.ambientDimension :=
    fun Z => (Z i)⁻¹ • numer i Z with hydef
  set U := {Z : ComplexModel (E.ambientDimension + 1) | Z i ≠ 0 ∧ y Z ∈ ball (y Z₀) ε}
  have hcont : ∀ Z, Z i ≠ 0 → DifferentiableAt ℂ y Z := fun Z hZ =>
    (((EuclideanSpace.proj (𝕜 := ℂ) i).differentiableAt).inv hZ).smul (numer i).differentiableAt
  have hUo : IsOpen U := by
    refine isOpen_iff_mem_nhds.mpr fun Z hZ => ?_
    have h1 : ∀ᶠ Z' in 𝓝 Z, Z' i ≠ 0 :=
      (EuclideanSpace.proj (𝕜 := ℂ) i).continuous.continuousAt.eventually_ne hZ.1
    have h2 : ∀ᶠ Z' in 𝓝 Z, y Z' ∈ ball (y Z₀) ε :=
      (hcont Z hZ.1).continuousAt.eventually (isOpen_ball.mem_nhds hZ.2)
    exact h1.and h2
  refine ⟨U, hUo.mem_nhds ⟨hZi, mem_ball_self hε⟩,
    fun Z => Z i ^ j * coef f E n H s i (e.symm (ψ (L0 (y Z)).1)), ?_, ?_⟩
  · -- holomorphy
    intro Z hZ
    have hyO : (L0 (y Z)).1 ∈ O := (hgraph _ hZ.2).1
    obtain ⟨hψt, hψs⟩ := hψdom _ hyO
    have hpU : schemeComplexPointImage f (e.symm (ψ (L0 (y Z)).1)) ∈ coordOpen E i :=
      (projectivePoint_mem_source_iff f E n i _).mp hψs
    have hc : DifferentiableAt ℂ (fun w => coef f E n H s i (e.symm w)) (ψ (L0 (y Z)).1) :=
      FactorizedWeightForm.differentiableAt_comp_chart_symm (complexChartAt (n := n) p₀) hψt
        (holomorphicAt_coef f E n H s i hpU).self_of_nhds
    have hψd : DifferentiableAt ℂ ψ (L0 (y Z)).1 := hψ.differentiableAt (hOo.mem_nhds hyO)
    have hL : DifferentiableAt ℂ (fun Z => (L0 (y Z)).1) Z :=
      ((ContinuousLinearMap.fst ℂ (ComplexModel n) (ComplexModel (E.ambientDimension - n))).comp
        (L0 : ComplexModel E.ambientDimension →L[ℂ]
          ComplexModel n × ComplexModel (E.ambientDimension - n))).differentiableAt.comp Z
        (hcont Z hZ.1)
    exact ((((EuclideanSpace.proj (𝕜 := ℂ) i).differentiableAt).pow j).mul
      (hc.comp Z (hψd.comp Z hL))).differentiableWithinAt
  · -- agreement on the cone
    intro Z hZU hZC
    have hZv : WithLp.ofLp Z ≠ 0 := fun h => hZU.1 (by simpa using congrFun h i)
    have hmem : affinePoint i (y Z) ∈ range (projectivePoint f E n) := by
      have := (mem_affineCone_iff hZU.1).mp hZC
      rwa [affineRatio_eq_smul_numer] at this
    have hg := (hgraph _ hZU.2).2.1.mp hmem
    obtain ⟨-, hq⟩ := (hgraph _ hZU.2).2.2 hg
    set q := e.symm (ψ (L0 (y Z)).1)
    have hqZ : projectivePoint f E n q = mk (WithLp.ofLp Z) hZv := by
      rw [hq, mk_eq_affinePoint i hZv hZU.1, affineRatio_eq_smul_numer]
    have hqi : schemeComplexPointImage f q ∈ coordOpen E i := by
      rw [← projectivePoint_mem_source_iff f E n i, hqZ]
      exact (mk_mem_affineChart_source_iff i hZv).mpr hZU.1
    exact (coneFun_eq f E n H s hZv hqZ i hqi).symm

/-! ### Conclusion -/

/-- **Holomorphic sections of `𝒪_X(j)` are polynomials, `j ≫ 0`**, given polynomial equations of
`X(ℂ) ⊆ ℙᴺ` satisfying the Jacobian criterion: for every smooth metric `H` on `𝒪_X(1)` and
`j ≫ 0`, every holomorphic section `s` of `((𝒪_X(1), H)^an)^{⊗ j}` is `P(x/xᵢ) xᵢ^j` for a
homogeneous polynomial `P` of degree `j`. -/
theorem eventually_sectionsPolynomial {q : ℕ}
    {g : Fin (E.ambientDimension + 1) → Fin q → MvPolynomial (Fin E.ambientDimension) ℂ}
    (hg : IsJacobianPresentation (n := n) (projectivePoint f E n) g) :
    ∀ᶠ j in atTop, ∀ s : twistedSections (schemeHermitianLineBundle f n E (hyperplaneAtlas E) H) unit j,
      ∃ P : MvPolynomial (Fin (E.ambientDimension + 1)) ℂ, P.IsHomogeneous j ∧
        ∀ (i : Fin (E.ambientDimension + 1)) (p : SchemeComplexPoint f),
          schemeComplexPointImage f p ∈ coordOpen E i →
            coef f E n H s i p = MvPolynomial.eval (fun k => schemeOpenRegularFunction f n E
              (coordOpen E i) (ratio E i k) p) P := by
  obtain ⟨k₀, hk₀⟩ := exists_isHomogeneous_eq_of_jacobianPresentation
    (isHolomorphicEmbedding_projectivePoint f E n) hg
  filter_upwards [eventually_ge_atTop (max k₀ 1)] with j hj s
  obtain ⟨P, hP, hPF⟩ := hk₀ j (le_of_max_le_left hj) (coneFun f E n H s)
    (fun c Z hZ => coneFun_smul f E n H s (le_of_max_le_right hj) c hZ)
    (isLocallyHolomorphicOn_coneFun f E n H s)
  refine ⟨P, hP, fun i p hp => ?_⟩
  set Z : ComplexModel (E.ambientDimension + 1) := WithLp.toLp 2 (homCoords f E n i p)
  have hZv : WithLp.ofLp Z ≠ 0 := homCoords_ne_zero f E n i hp
  have hZp : projectivePoint f E n p = mk (WithLp.ofLp Z) hZv := projectivePoint_eq f E n i hp
  have hZC : Z ∈ affineCone (range (projectivePoint f E n)) := fun h => ⟨p, hZp⟩
  have h1 := coneFun_eq f E n H s hZv hZp i hp
  have hZi : Z i = 1 := homCoords_self f E n i hp
  rw [hZi, one_pow, one_mul] at h1
  rw [← h1, ← hPF Z hZC]
  rfl

/-- **FS-POS's `HyperplaneSectionsPolynomial` for `j ≫ 0`**, given polynomial equations of
`X(ℂ) ⊆ ℙᴺ` satisfying the Jacobian criterion. -/
theorem eventually_hyperplaneSectionsPolynomial {q : ℕ}
    {g : Fin (E.ambientDimension + 1) → Fin q → MvPolynomial (Fin E.ambientDimension) ℂ}
    (hg : IsJacobianPresentation (n := n) (projectivePoint f E n) g) :
    ∀ᶠ j in atTop, HyperplaneSectionsPolynomial f n E j :=
  (eventually_sectionsPolynomial f E n (fubiniStudyMetric f E n) hg).mono fun _ hj s => hj s

/-- GAGA for the sections of `𝒪_X(j)`, `j ≫ 0` (`SchemeSectionsAlgebraic` of lane GAGAMULT2), given
polynomial equations of `X(ℂ) ⊆ ℙᴺ` satisfying the Jacobian criterion. -/
theorem eventually_schemeSectionsAlgebraic {q : ℕ}
    {g : Fin (E.ambientDimension + 1) → Fin q → MvPolynomial (Fin E.ambientDimension) ℂ}
    (hg : IsJacobianPresentation (n := n) (projectivePoint f E n) g) :
    ∀ᶠ j in atTop, SchemeSectionsAlgebraic f n E (hyperplaneAtlas E) (fubiniStudyMetric f E n) j :=
  (eventually_hyperplaneSectionsPolynomial f E n hg).mono fun _ hj =>
    schemeSectionsAlgebraic_of_polynomial f n E hj

omit [IsSeparated f] [QuasiCompact f] [CompactSpace (SchemeComplexPoint f)] in
/-- **`MultiplierIdealAlgebraic`** (the statement), given polynomial equations of
`X(ℂ) ⊆ ℙᴺ` satisfying the Jacobian criterion. -/
theorem multiplierIdealAlgebraic_of_jacobianPresentation {q : ℕ}
    {g : Fin (E.ambientDimension + 1) → Fin q → MvPolynomial (Fin E.ambientDimension) ℂ}
    (hg : IsJacobianPresentation (n := n) (projectivePoint f E n) g) :
    SGPT.NAPotential.Berkovich.MultiplierIdealAlgebraic f n E := by
  let := E.isSeparated
  let := E.quasiCompact
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  exact multiplierIdealAlgebraic_of_hyperplaneSectionsPolynomial f n E
    (eventually_hyperplaneSectionsPolynomial f E n hg)

end SGPT.GAGA.H0S
