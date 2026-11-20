import SGPT.GAGA.H0SProjective
import SGPT.NAPotential.FSPosSections
import SGPT.Foundations.Schemes.NativeProjectiveCoordinateUnitLocus

/-!
# The projective embedding of `X(ℂ)` as a holomorphic embedding into `ℙᴺ`


`X` is smooth of relative dimension `n` over `ℂ` with a closed projective embedding
`E.map : X ⟶ ℙᴺ`; `Uᵢ = E.map⁻¹ D₊(xᵢ)` and `ratio E i k = (x_k/x_i)|_X ∈ Γ(X, Uᵢ)`.

* `schemeOpenRegularFunction_ne_zero_iff`: the analytic function of a regular function `r` on `U`
  is nonzero at a complex point `p` iff `p ∈ D(r)` (the stalk is local and the evaluation at
  `p` is surjective onto `ℂ`).
* `mem_coordOpen_iff_ratio_ne_zero`: for `p ∈ U_l(ℂ)`, `p ∈ Uᵢ ⟺ (x_i/x_l)(p) ≠ 0`.
* `affinePresentation f E i : ℂ[t₁, …, t_N] → Γ(X, Uᵢ)`, `t_a ↦ x_{i.succAbove a}/x_i`, is
  surjective (`affinePresentation_surjective`; `E.map` is a closed immersion and `D₊(xᵢ)` is the
  affine space with coordinates `x_k/x_i`), and the analytic value of `affinePresentation f E i P`
  at `p` is `P` at the affine coordinates of `p` (`schemeOpenRegularFunction_affinePresentation`).
* `eq_of_ratio_eq`: two complex points of `Uᵢ` with the same affine coordinates are equal.
* `projectivePoint f n E : X(ℂ) → ℙᴺ`, `p ↦ [x₀(p) : … : x_N(p)]`, is a holomorphic embedding
  in the workspace charts (`isHolomorphicEmbedding_projectivePoint`), using FS-POS's immersion
  theorem `SGPT.NAPotential.FSPos.eq_zero_of_fderiv_ratio_eq_zero`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.GAGA.H0S

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Filter Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Okounkov SGPT.NAPotential.FSPos SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open scoped Topology Manifold

attribute [local instance] MvPolynomial.gradedAlgebra

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (E : ClosedProjectiveEmbedding f) (n : ℕ)
  [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f]

local instance h0sEmbTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance h0sEmbCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance h0sEmbManifold : IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n

/-! ### Values of regular functions and basic opens -/

/-- Evaluation of the algebraic stalk at a complex point (through the analytic germ). -/
def pointEval (p : SchemeComplexPoint f) :
    X.presheaf.stalk (schemeComplexPointImage f p) →+* ℂ :=
  NativeHolGerm.eval.comp (schemeNativeStalkGerm f n p)

theorem pointEval_germ_const (p : SchemeComplexPoint f) (b : ℂ) :
    pointEval f n p (X.presheaf.germ ⊤ (schemeComplexPointImage f p) trivial
      (schemeGlobalConstants f b)) = b := by
  change NativeHolGerm.eval (schemeNativeStalkGerm f n p _) = b
  rw [← NativeHolGerm.eval_chartEquiv]
  change HolGerm.eval (stalkToModel f n p _) = b
  rw [stalkToModel_constants]
  rfl

theorem pointEval_surjective (p : SchemeComplexPoint f) : Function.Surjective (pointEval f n p) :=
  fun b => ⟨_, pointEval_germ_const f n p b⟩

/-- The point evaluation kills exactly the maximal ideal of the stalk. -/
theorem pointEval_eq_zero_iff (p : SchemeComplexPoint f)
    (a : X.presheaf.stalk (schemeComplexPointImage f p)) : pointEval f n p a = 0 ↔ ¬ IsUnit a := by
  have hmax := RingHom.ker_isMaximal_of_surjective _ (pointEval_surjective f n p)
  have hker : RingHom.ker (pointEval f n p) = IsLocalRing.maximalIdeal _ :=
    IsLocalRing.eq_maximalIdeal hmax
  rw [← RingHom.mem_ker, hker, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]

/-- **The analytic function of `r` vanishes exactly off `D(r)`.** -/
theorem schemeOpenRegularFunction_ne_zero_iff (U : X.Opens) (r : Γ(X, U))
    (p : SchemeComplexPoint f) (hp : schemeComplexPointImage f p ∈ U) :
    schemeOpenRegularFunction f n E U r p ≠ 0 ↔ schemeComplexPointImage f p ∈ X.basicOpen r := by
  rw [schemeOpenRegularFunction_apply f n E U r p hp, Scheme.mem_basicOpen _ _ _ hp]
  change pointEval f n p _ ≠ 0 ↔ _
  rw [ne_eq, pointEval_eq_zero_iff, not_not]

omit [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f] in
/-- The basic open of `x_i/x_l` in `U_l` is `U_l ∩ U_i`. -/
theorem basicOpen_ratio (l i : Fin (E.ambientDimension + 1)) :
    X.basicOpen (ratio E l i) = coordOpen E l ⊓ coordOpen E i := by
  rw [ratio, ← Scheme.preimage_basicOpen, polynomialProjCoordinateRegularRatio_globalBasicOpen]
  rfl

/-- For `p ∈ U_l(ℂ)`: `p ∈ U_i ⟺ (x_i/x_l)(p) ≠ 0`. -/
theorem mem_coordOpen_iff_ratio_ne_zero (l i : Fin (E.ambientDimension + 1))
    (p : SchemeComplexPoint f) (hp : schemeComplexPointImage f p ∈ coordOpen E l) :
    schemeComplexPointImage f p ∈ coordOpen E i ↔
      schemeOpenRegularFunction f n E (coordOpen E l) (ratio E l i) p ≠ 0 := by
  rw [schemeOpenRegularFunction_ne_zero_iff f E n _ _ p hp, basicOpen_ratio f E]
  exact ⟨fun h => ⟨hp, h⟩, fun h => h.2⟩

/-! ### The affine coordinate ring of `Uᵢ` -/

/-- `ℂ[t₁, …, t_N] → Γ(X, Uᵢ)`, `t_a ↦ x_{i.succAbove a}/x_i`. -/
def affinePresentation (i : Fin (E.ambientDimension + 1)) :
    MvPolynomial (Fin E.ambientDimension) ℂ →+* Γ(X, coordOpen E i) :=
  (E.map.app (polynomialProjCoordinateOpen ℂ E.ambientDimension i)).hom.comp
    ((polynomialProjCoordinateSectionMap ℂ E.ambientDimension i).comp
      (polynomialProjRatioMap ℂ E.ambientDimension i).toRingHom)

omit [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f] in
theorem affinePresentation_surjective (i : Fin (E.ambientDimension + 1)) :
    Function.Surjective (affinePresentation f E i) := by
  intro s
  obtain ⟨t, rfl⟩ := Scheme.Hom.app_surjective E.map
    (polynomialProjCoordinateOpen ℂ E.ambientDimension i)
    (Proj.isAffineOpen_basicOpen _ _ (MvPolynomial.isHomogeneous_X ℂ i) (by decide)) s
  obtain ⟨z, rfl⟩ := (homogeneousPolynomialBasicOpenAwayEquiv (K := ℂ) i).surjective t
  refine ⟨polynomialProjCoordinateDehomogenization ℂ E.ambientDimension i z, ?_⟩
  simp only [affinePresentation, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    polynomialProjRatioMap_coordinateDehomogenization]
  rfl

omit [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f] in
theorem affinePresentation_X (i : Fin (E.ambientDimension + 1)) (a : Fin E.ambientDimension) :
    affinePresentation f E i (MvPolynomial.X a) = ratio E i (i.succAbove a) := by
  simp only [affinePresentation, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  rw [show polynomialProjRatioMap ℂ E.ambientDimension i (MvPolynomial.X a) =
    polynomialProjCoordinateRatio ℂ E.ambientDimension i (i.succAbove a) from MvPolynomial.aeval_X _ a]
  rfl

omit [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f] in
theorem affinePresentation_C (i : Fin (E.ambientDimension + 1)) (b : ℂ) :
    affinePresentation f E i (MvPolynomial.C b) = constMap E i b := by
  simp only [affinePresentation, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  rw [show polynomialProjRatioMap ℂ E.ambientDimension i (MvPolynomial.C b) =
    algebraMap ℂ _ b from (polynomialProjRatioMap ℂ E.ambientDimension i).commutes b]
  exact (constants_restrict E i b).symm

/-- The affine coordinates `((x_{i.succAbove a}/x_i)(p))_a` of a complex point. -/
def affineCoords (i : Fin (E.ambientDimension + 1)) (p : SchemeComplexPoint f) :
    ComplexModel E.ambientDimension :=
  WithLp.toLp 2 fun a => schemeOpenRegularFunction f n E (coordOpen E i) (ratio E i (i.succAbove a)) p

/-- The analytic value of `affinePresentation f E i P` is `P` at the affine coordinates. -/
theorem schemeOpenRegularFunction_affinePresentation (i : Fin (E.ambientDimension + 1))
    (P : MvPolynomial (Fin E.ambientDimension) ℂ) (p : SchemeComplexPoint f)
    (hp : schemeComplexPointImage f p ∈ coordOpen E i) :
    schemeOpenRegularFunction f n E (coordOpen E i) (affinePresentation f E i P) p =
      MvPolynomial.eval (fun a => affineCoords f E n i p a) P := by
  induction P using MvPolynomial.induction_on with
  | C b =>
    rw [affinePresentation_C, MvPolynomial.eval_C]
    exact schemeOpenRegularFunction_constMap f n E i b p hp
  | add P Q hP hQ =>
    rw [map_add, schemeOpenRegularFunction_add f n E _ _ _ hp, map_add]
    beta_reduce
    rw [hP, hQ]
  | mul_X P a hP =>
    rw [map_mul, schemeOpenRegularFunction_mul f n E _ _ _ hp, map_mul, MvPolynomial.eval_X]
    beta_reduce
    rw [hP, affinePresentation_X]
    rfl

/-! ### Complex points are determined by their affine coordinates -/

/-- Two complex points of an affine open with the same values of all regular functions are
equal. -/
theorem eq_of_forall_schemeOpenRegularFunction_eq {U : X.Opens} (hU : IsAffineOpen U)
    {p q : SchemeComplexPoint f} (hp : schemeComplexPointImage f p ∈ U)
    (hq : schemeComplexPointImage f q ∈ U)
    (h : ∀ r : Γ(X, U), schemeOpenRegularFunction f n E U r p =
      schemeOpenRegularFunction f n E U r q) : p = q := by
  apply schemeComplexPointImage_injective f
  have hb : ∀ r : Γ(X, U), schemeComplexPointImage f p ∈ X.basicOpen r ↔
      schemeComplexPointImage f q ∈ X.basicOpen r := fun r => by
    rw [← schemeOpenRegularFunction_ne_zero_iff f E n U r p hp,
      ← schemeOpenRegularFunction_ne_zero_iff f E n U r q hq, h r]
  have hP : hU.primeIdealOf ⟨_, hp⟩ = hU.primeIdealOf ⟨_, hq⟩ := by
    ext r
    have h1 : ∀ (x : X) (hx : x ∈ U), x ∈ X.basicOpen r ↔ r ∉ (hU.primeIdealOf ⟨x, hx⟩).asIdeal := by
      intro x hx
      have e1 : hU.primeIdealOf ⟨x, hx⟩ ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen r ↔
          x ∈ X.basicOpen r := by
        change hU.fromSpec (hU.primeIdealOf ⟨x, hx⟩) ∈ X.basicOpen r ↔ _
        rw [hU.fromSpec_primeIdealOf ⟨x, hx⟩]
      rw [← e1, hU.fromSpec_preimage_basicOpen r]
      exact PrimeSpectrum.mem_basicOpen _ _
    rw [← not_iff_not, ← h1 _ hp, ← h1 _ hq]
    exact hb r
  have := congrArg hU.fromSpec hP
  rwa [IsAffineOpen.fromSpec_primeIdealOf, IsAffineOpen.fromSpec_primeIdealOf] at this

/-- Two complex points of `Uᵢ` with the same affine coordinates are equal. -/
theorem eq_of_affineCoords_eq (i : Fin (E.ambientDimension + 1)) {p q : SchemeComplexPoint f}
    (hp : schemeComplexPointImage f p ∈ coordOpen E i)
    (hq : schemeComplexPointImage f q ∈ coordOpen E i)
    (h : affineCoords f E n i p = affineCoords f E n i q) : p = q := by
  refine eq_of_forall_schemeOpenRegularFunction_eq f E n (isAffineOpen_coordOpen E i) hp hq
    fun r => ?_
  obtain ⟨P, rfl⟩ := affinePresentation_surjective f E i r
  rw [schemeOpenRegularFunction_affinePresentation f E n i P p hp,
    schemeOpenRegularFunction_affinePresentation f E n i P q hq, h]

/-! ### The map `X(ℂ) → ℙᴺ` -/

/-- The homogeneous coordinates `((x_k/x_i)(p))_k` of `p` in the frame `xᵢ`. -/
def homCoords (i : Fin (E.ambientDimension + 1)) (p : SchemeComplexPoint f) :
    Fin (E.ambientDimension + 1) → ℂ :=
  fun k => schemeOpenRegularFunction f n E (coordOpen E i) (ratio E i k) p

omit [IsSeparated f] [QuasiCompact f] in
theorem homCoords_self (i : Fin (E.ambientDimension + 1)) {p : SchemeComplexPoint f}
    (hp : schemeComplexPointImage f p ∈ coordOpen E i) : homCoords f E n i p i = 1 := by
  rw [homCoords, ratio_self]
  exact schemeOpenRegularFunction_one f n E (coordOpen E i) hp

omit [IsSeparated f] [QuasiCompact f] in
theorem homCoords_eq_affineLift (i : Fin (E.ambientDimension + 1)) {p : SchemeComplexPoint f}
    (hp : schemeComplexPointImage f p ∈ coordOpen E i) :
    homCoords f E n i p = affineLift i (affineCoords f E n i p) := by
  funext k
  refine Fin.succAboveCases i ?_ (fun a => ?_) k
  · rw [homCoords_self f E n i hp, affineLift_same]
  · rw [affineLift_succAbove]
    rfl

omit [IsSeparated f] [QuasiCompact f] in
theorem homCoords_ne_zero (i : Fin (E.ambientDimension + 1)) {p : SchemeComplexPoint f}
    (hp : schemeComplexPointImage f p ∈ coordOpen E i) : homCoords f E n i p ≠ 0 := by
  rw [homCoords_eq_affineLift f E n i hp]
  exact affineLift_ne_zero i _

omit [IsSeparated f] [QuasiCompact f] in
/-- On `Uᵢ ∩ U_l` the homogeneous coordinates in the two frames are proportional. -/
theorem homCoords_transition (i l : Fin (E.ambientDimension + 1)) {p : SchemeComplexPoint f}
    (hpi : schemeComplexPointImage f p ∈ coordOpen E i)
    (hpl : schemeComplexPointImage f p ∈ coordOpen E l) :
    ∃ c : ℂ, c ≠ 0 ∧ homCoords f E n l p = c • homCoords f E n i p := by
  refine ⟨schemeFrameTransition f n E ((hyperplaneAtlas E).frame i) ((hyperplaneAtlas E).frame l) p,
    schemeFrameTransition_ne_zero f n E _ _ p hpi hpl, funext fun k => ?_⟩
  have h := coordFun_transition f E n ((hyperplaneAtlas E).frame i) ((hyperplaneAtlas E).frame l) k
    p hpi hpl
  change schemeOpenRegularFunction f n E (coordOpen E l)
      (coordCoef E ((hyperplaneAtlas E).frame l) k) p = _ *
    schemeOpenRegularFunction f n E (coordOpen E i)
      (coordCoef E ((hyperplaneAtlas E).frame i) k) p at h
  rw [coordCoef_atlas, coordCoef_atlas] at h
  exact h

omit [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f] in
/-- A chosen frame index at `p`. -/
def frameIndex (p : SchemeComplexPoint f) : Fin (E.ambientDimension + 1) :=
  Classical.choose ((hyperplaneAtlas E).covers (schemeComplexPointImage f p))

omit [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f] in
theorem mem_coordOpen_frameIndex (p : SchemeComplexPoint f) :
    schemeComplexPointImage f p ∈ coordOpen E (frameIndex f E p) :=
  Classical.choose_spec ((hyperplaneAtlas E).covers (schemeComplexPointImage f p))

/-- **The projective embedding on complex points**, `p ↦ [x₀(p) : … : x_N(p)] ∈ ℙᴺ`. -/
def projectivePoint (p : SchemeComplexPoint f) : ComplexProjectiveSpace E.ambientDimension :=
  mk (homCoords f E n (frameIndex f E p) p)
    (homCoords_ne_zero f E n _ (mem_coordOpen_frameIndex f E p))

theorem projectivePoint_eq (i : Fin (E.ambientDimension + 1)) {p : SchemeComplexPoint f}
    (hp : schemeComplexPointImage f p ∈ coordOpen E i) :
    projectivePoint f E n p = mk (homCoords f E n i p) (homCoords_ne_zero f E n i hp) := by
  obtain ⟨c, hc, h⟩ := homCoords_transition f E n (frameIndex f E p) i
    (mem_coordOpen_frameIndex f E p) hp
  unfold projectivePoint
  simp only [h]
  exact (mk_smul _ hc).symm

theorem projectivePoint_eq_affinePoint (i : Fin (E.ambientDimension + 1))
    {p : SchemeComplexPoint f} (hp : schemeComplexPointImage f p ∈ coordOpen E i) :
    projectivePoint f E n p = affinePoint i (affineCoords f E n i p) := by
  rw [projectivePoint_eq f E n i hp]
  unfold affinePoint
  simp only [homCoords_eq_affineLift f E n i hp]

/-- `[x(p)] ∈ {Zᵢ ≠ 0}` iff `p ∈ Uᵢ`. -/
theorem projectivePoint_mem_source_iff (i : Fin (E.ambientDimension + 1))
    (p : SchemeComplexPoint f) :
    projectivePoint f E n p ∈ (affineChart i).source ↔ schemeComplexPointImage f p ∈ coordOpen E i := by
  set l := frameIndex f E p
  have hl := mem_coordOpen_frameIndex f E p
  rw [projectivePoint_eq f E n l hl, mk_mem_affineChart_source_iff,
    mem_coordOpen_iff_ratio_ne_zero f E n l i p hl]
  rfl

theorem affineChart_projectivePoint (i : Fin (E.ambientDimension + 1)) {p : SchemeComplexPoint f}
    (hp : schemeComplexPointImage f p ∈ coordOpen E i) :
    affineChart i (projectivePoint f E n p) = affineCoords f E n i p := by
  rw [projectivePoint_eq_affinePoint f E n i hp, affineChart_affinePoint]

omit [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f] in
theorem isOpen_coordOpen_points (i : Fin (E.ambientDimension + 1)) :
    IsOpen (schemeComplexPointImage f ⁻¹' (coordOpen E i : Set X)) :=
  (coordOpen E i).isOpen.preimage (schemeComplexPointImage_continuous f)

omit [IsSeparated f] [QuasiCompact f] in
theorem continuousAt_affineCoords (i : Fin (E.ambientDimension + 1)) {p : SchemeComplexPoint f}
    (hp : schemeComplexPointImage f p ∈ coordOpen E i) :
    ContinuousAt (affineCoords f E n i) p := by
  have h : ∀ a, ContinuousAt (fun q => schemeOpenRegularFunction f n E (coordOpen E i)
      (ratio E i (i.succAbove a)) q) p := fun a =>
    (schemeOpenRegularFunction_holomorphicAt f n E _ _ p hp).self_of_nhds.continuousAt
  exact (PiLp.continuous_toLp 2 _).continuousAt.comp (continuousAt_pi.mpr h)

theorem continuous_projectivePoint : Continuous (projectivePoint f E n) := by
  rw [continuous_iff_continuousAt]
  intro p
  set i := frameIndex f E p
  have hp := mem_coordOpen_frameIndex f E p
  have hev : (fun q => affinePoint i (affineCoords f E n i q)) =ᶠ[𝓝 p] projectivePoint f E n := by
    filter_upwards [(isOpen_coordOpen_points f E i).mem_nhds hp] with q hq
    exact (projectivePoint_eq_affinePoint f E n i hq).symm
  exact ((continuous_affinePoint i).continuousAt.comp
    (continuousAt_affineCoords f E n i hp)).congr hev

theorem injective_projectivePoint : Function.Injective (projectivePoint f E n) := by
  intro p q hpq
  set i := frameIndex f E p
  have hp := mem_coordOpen_frameIndex f E p
  have hq : schemeComplexPointImage f q ∈ coordOpen E i := by
    rw [← projectivePoint_mem_source_iff f E n i, ← hpq, projectivePoint_mem_source_iff]
    exact hp
  refine eq_of_affineCoords_eq f E n i hp hq ?_
  rw [← affineChart_projectivePoint f E n i hp, ← affineChart_projectivePoint f E n i hq, hpq]

/-- In the chart `U_l` of `ℙᴺ` and a chart `e` of `X(ℂ)`, the embedding is FS-POS's
`affineCoordMap` on the chart image of `U_l(ℂ)`. -/
theorem chartMap_eq_affineCoordMap (p : SchemeComplexPoint f) (l : Fin (E.ambientDimension + 1))
    {z : ComplexModel n} (hz : z ∈ coordChartDomain f E n l (complexChartAt (n := n) p)) :
    chartMap (n := n) (projectivePoint f E n) p l z =
      affineCoordMap f E n l (complexChartAt (n := n) p) z := by
  unfold chartMap
  rw [affineChart_projectivePoint f E n l hz.2]
  rfl

/-- **`X(ℂ) → ℙᴺ` is a holomorphic embedding** in the workspace charts. -/
theorem isHolomorphicEmbedding_projectivePoint :
    IsHolomorphicEmbedding (n := n) (projectivePoint f E n) := by
  refine ⟨continuous_projectivePoint f E n, injective_projectivePoint f E n, ?_, ?_⟩
  · intro p l hl
    have hpl := (projectivePoint_mem_source_iff f E n l p).mp hl
    set e := complexChartAt (n := n) p
    have hp : p ∈ e.val.source := mem_complexChartAt_source p
    have hdom : e.val p ∈ coordChartDomain f E n l e :=
      ⟨e.val.map_source hp, by
        show schemeComplexPointImage f (e.val.symm (e.val p)) ∈ coordOpen E l
        rw [e.val.left_inv hp]; exact hpl⟩
    filter_upwards [(isOpen_coordChartDomain f E n l e).mem_nhds hdom] with z hz
    refine (differentiableAt_affineCoordMap f E n l e hz).congr_of_eventuallyEq ?_
    filter_upwards [(isOpen_coordChartDomain f E n l e).mem_nhds hz] with w hw
    exact chartMap_eq_affineCoordMap f E n p l hw
  · intro p l hl
    have hpl := (projectivePoint_mem_source_iff f E n l p).mp hl
    set e := complexChartAt (n := n) p
    have hp : p ∈ e.val.source := mem_complexChartAt_source p
    set u := e.val p
    have hdom : u ∈ coordChartDomain f E n l e :=
      ⟨e.val.map_source hp, by
        show schemeComplexPointImage f (e.val.symm (e.val p)) ∈ coordOpen E l
        rw [e.val.left_inv hp]; exact hpl⟩
    have hev : chartMap (n := n) (projectivePoint f E n) p l =ᶠ[𝓝 u] affineCoordMap f E n l e := by
      filter_upwards [(isOpen_coordChartDomain f E n l e).mem_nhds hdom] with w hw
      exact chartMap_eq_affineCoordMap f E n p l hw
    rw [hev.fderiv_eq]
    set T := affineCoordMap f E n l e
    have hT : DifferentiableAt ℂ T u := differentiableAt_affineCoordMap f E n l e hdom
    refine (injective_iff_map_eq_zero (fderiv ℂ T u)).mpr fun v h0 => ?_
    refine eq_zero_of_fderiv_ratio_eq_zero f E n p l hpl v fun a => ?_
    have hproj : (fun w => schemeOpenRegularFunction f n E (coordOpen E l)
        (ratio E l (l.succAbove a)) (e.val.symm w)) =
        (EuclideanSpace.proj a : ComplexModel E.ambientDimension →L[ℂ] ℂ) ∘ T := by
      funext w
      rfl
    change fderiv ℂ (fun w => schemeOpenRegularFunction f n E (coordOpen E l)
      (ratio E l (l.succAbove a)) (e.val.symm w)) u v = 0
    rw [hproj, fderiv_comp u (EuclideanSpace.proj a).differentiableAt hT,
      ContinuousLinearMap.fderiv, ContinuousLinearMap.comp_apply, h0, map_zero]

end SGPT.GAGA.H0S
