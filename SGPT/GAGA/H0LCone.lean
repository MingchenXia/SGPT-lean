import SGPT.GAGA.H0LRegular

/-!
# Families of local coefficients of degree `m` and the cone theorem


A *section family of degree `m`* (`IsSectionFamily`) is a family `h = (h_l)_l` of functions on
`X(ℂ)`, `h_l` holomorphic on `U_l(ℂ) = (X ∩ D₊(x_l))(ℂ)`, with the transition law of the
coefficients of a section of `𝒪_X(m)` in the frames `x_l^m`:
`h_l = (x_i/x_l)^m h_i` on `U_i ∩ U_l`.  This is the setting of the cone function
(`SGPT.GAGA.H0S.coneFun`), without a section of an analytic bundle: the function
`F(Z) = Z_l^m h_l([Z])` on the affine cone of `X(ℂ) ⊆ ℙᴺ` is homogeneous of degree `m` and
holomorphic off the vertex, so for `m ≫ 0` (`exists_polynomial_of_isSectionFamily`) every section
family is given by a homogeneous polynomial `P` of degree `m`: `h_l = P(x/x_l)` on `U_l(ℂ)`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.GAGA.H0L

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Filter Set Metric
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Okounkov SGPT.NAPotential.FSPos SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
  SGPT.GAGA.H0 SGPT.GAGA.H0S
open scoped Topology Manifold

attribute [local instance] MvPolynomial.gradedAlgebra

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (E : ClosedProjectiveEmbedding f) (n : ℕ)
  [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f]

local instance h0lConeTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance h0lConeCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance h0lConeManifold : IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n

/-! ### Homogeneous coordinates in two frames -/

/-- `(x_k/x_l) = (x_i/x_l)(x_k/x_i)` on `Uᵢ ∩ U_l`. -/
theorem homCoords_trans (i l k : Fin (E.ambientDimension + 1)) {p : SchemeComplexPoint f}
    (hpi : schemeComplexPointImage f p ∈ coordOpen E i)
    (hpl : schemeComplexPointImage f p ∈ coordOpen E l) :
    homCoords f E n l p k = homCoords f E n l p i * homCoords f E n i p k := by
  have hg := homCoords_transition_eq f E n i l hpi hpl
  have hk := congrFun hg k
  have hi := congrFun hg i
  rw [Pi.smul_apply, smul_eq_mul] at hk hi
  rw [homCoords_self f E n i hpi, mul_one] at hi
  rw [hk, hi]

/-- `(x_l/x_i)(x_i/x_l) = 1` on `Uᵢ ∩ U_l`. -/
theorem homCoords_mul_homCoords (i l : Fin (E.ambientDimension + 1)) {p : SchemeComplexPoint f}
    (hpi : schemeComplexPointImage f p ∈ coordOpen E i)
    (hpl : schemeComplexPointImage f p ∈ coordOpen E l) :
    homCoords f E n i p l * homCoords f E n l p i = 1 := by
  have h := homCoords_trans f E n i l l hpi hpl
  rw [homCoords_self f E n l hpl] at h
  rw [mul_comm, ← h]

/-! ### Section families -/

/-- **A section family of degree `m`**: functions `h_l`, holomorphic on `U_l(ℂ)`, with
`h_l = (x_i/x_l)^m h_i` on `Uᵢ ∩ U_l` (the coefficients of a holomorphic section of `𝒪_X(m)` in
the frames `x_l^m`). -/
structure IsSectionFamily (m : ℕ) (h : Fin (E.ambientDimension + 1) → SchemeComplexPoint f → ℂ) :
    Prop where
  holo : ∀ (i : Fin (E.ambientDimension + 1)) (p : SchemeComplexPoint f),
    schemeComplexPointImage f p ∈ coordOpen E i → HolomorphicAt n (h i) p
  trans : ∀ (i l : Fin (E.ambientDimension + 1)) (p : SchemeComplexPoint f),
    schemeComplexPointImage f p ∈ coordOpen E i → schemeComplexPointImage f p ∈ coordOpen E l →
      h l p = homCoords f E n l p i ^ m * h i p

/-- **The function on the affine cone of a section family**: `F(Z) = Z_i^m h_i(p)` if
`[Z] = p ∈ X(ℂ)`, `i` the chosen frame index at `p`, and `0` otherwise. -/
def familyConeFun (m : ℕ) (h : Fin (E.ambientDimension + 1) → SchemeComplexPoint f → ℂ)
    (Z : ComplexModel (E.ambientDimension + 1)) : ℂ := by
  classical
  exact if hZ : ∃ (p : SchemeComplexPoint f) (hZ : WithLp.ofLp Z ≠ 0),
      projectivePoint f E n p = mk (WithLp.ofLp Z) hZ then
    Z (frameIndex f E hZ.choose) ^ m * h (frameIndex f E hZ.choose) hZ.choose
  else 0

variable {f E n}

/-- `F(Z) = Z_l^m h_l(p)` for `[Z] = p` and every `l` with `p ∈ U_l`. -/
theorem familyConeFun_eq {m : ℕ} {h : Fin (E.ambientDimension + 1) → SchemeComplexPoint f → ℂ}
    (hh : IsSectionFamily f E n m h) {Z : ComplexModel (E.ambientDimension + 1)}
    {p : SchemeComplexPoint f} (hZ : WithLp.ofLp Z ≠ 0)
    (hp : projectivePoint f E n p = mk (WithLp.ofLp Z) hZ)
    (l : Fin (E.ambientDimension + 1)) (hl : schemeComplexPointImage f p ∈ coordOpen E l) :
    familyConeFun f E n m h Z = Z l ^ m * h l p := by
  classical
  have hex : ∃ (p : SchemeComplexPoint f) (hZ : WithLp.ofLp Z ≠ 0),
      projectivePoint f E n p = mk (WithLp.ofLp Z) hZ := ⟨p, hZ, hp⟩
  unfold familyConeFun
  rw [dif_pos hex]
  have hpp : hex.choose = p := by
    apply injective_projectivePoint f E n
    obtain ⟨hZ', h'⟩ := hex.choose_spec
    rw [h', hp]
  rw [hpp]
  set i := frameIndex f E p
  have hi := mem_coordOpen_frameIndex f E p
  have hZi : mk (homCoords f E n i p) (homCoords_ne_zero f E n i hi) = mk (WithLp.ofLp Z) hZ := by
    rw [← projectivePoint_eq f E n i hi, hp]
  obtain ⟨c, hc, hcZ⟩ := exists_eq_smul_of_mk_eq hZi
  have hZi' : Z i = c := by
    have := congrFun hcZ i
    rw [Pi.smul_apply, homCoords_self f E n i hi, smul_eq_mul, mul_one] at this
    exact this
  have hZl : Z l = c * homCoords f E n i p l := by
    have := congrFun hcZ l
    rw [Pi.smul_apply, smul_eq_mul] at this
    exact this
  rw [hh.trans i l p hi hl, hZi', hZl, ← mul_assoc, ← mul_pow, mul_assoc,
    homCoords_mul_homCoords f E n i l hi hl, mul_one]

/-- `F` is homogeneous of degree `m ≥ 1` on the cone. -/
theorem familyConeFun_smul {m : ℕ} {h : Fin (E.ambientDimension + 1) → SchemeComplexPoint f → ℂ}
    (hh : IsSectionFamily f E n m h) (hm : 1 ≤ m) (c : ℂ) {Z : ComplexModel (E.ambientDimension + 1)}
    (hZ : Z ∈ affineCone (range (projectivePoint f E n))) :
    familyConeFun f E n m h (c • Z) = c ^ m * familyConeFun f E n m h Z := by
  classical
  have h0 : familyConeFun f E n m h 0 = 0 := by
    unfold familyConeFun
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
  rw [familyConeFun_eq hh hcZ hp' l hl, familyConeFun_eq hh hZ0 hp l hl]
  change (c * Z l) ^ m * _ = _
  ring

variable [CompactSpace (SchemeComplexPoint f)]

/-- `F` is holomorphic on the cone off the vertex. -/
theorem isLocallyHolomorphicOn_familyConeFun {m : ℕ}
    {h : Fin (E.ambientDimension + 1) → SchemeComplexPoint f → ℂ}
    (hh : IsSectionFamily f E n m h) :
    IsLocallyHolomorphicOn (affineCone (range (projectivePoint f E n)))
      (familyConeFun f E n m h) := by
  intro Z₀ hZ₀ h0
  obtain ⟨i, hZi⟩ : ∃ i, Z₀ i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact h0 (by ext k; simpa using hcon k)
  have hv₀ : WithLp.ofLp Z₀ ≠ 0 := fun hz => hZi (by simpa using congrFun hz i)
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
    fun Z => Z i ^ m * h i (e.symm (ψ (L0 (y Z)).1)), ?_, ?_⟩
  · intro Z hZ
    have hyO : (L0 (y Z)).1 ∈ O := (hgraph _ hZ.2).1
    obtain ⟨hψt, hψs⟩ := hψdom _ hyO
    have hpU : schemeComplexPointImage f (e.symm (ψ (L0 (y Z)).1)) ∈ coordOpen E i :=
      (projectivePoint_mem_source_iff f E n i _).mp hψs
    have hc : DifferentiableAt ℂ (fun w => h i (e.symm w)) (ψ (L0 (y Z)).1) :=
      FactorizedWeightForm.differentiableAt_comp_chart_symm (complexChartAt (n := n) p₀) hψt
        (hh.holo i _ hpU).self_of_nhds
    have hψd : DifferentiableAt ℂ ψ (L0 (y Z)).1 := hψ.differentiableAt (hOo.mem_nhds hyO)
    have hL : DifferentiableAt ℂ (fun Z => (L0 (y Z)).1) Z :=
      ((ContinuousLinearMap.fst ℂ (ComplexModel n) (ComplexModel (E.ambientDimension - n))).comp
        (L0 : ComplexModel E.ambientDimension →L[ℂ]
          ComplexModel n × ComplexModel (E.ambientDimension - n))).differentiableAt.comp Z
        (hcont Z hZ.1)
    exact ((((EuclideanSpace.proj (𝕜 := ℂ) i).differentiableAt).pow m).mul
      (hc.comp Z (hψd.comp Z hL))).differentiableWithinAt
  · intro Z hZU hZC
    have hZv : WithLp.ofLp Z ≠ 0 := fun hz => hZU.1 (by simpa using congrFun hz i)
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
    exact (familyConeFun_eq hh hZv hqZ i hqi).symm

variable (f E n)

/-- **Section families of large degree are polynomial**: there is `k₀` such that for `m ≥ k₀`
every section family `h` of degree `m` is `h_l = P(x/x_l)` on `U_l(ℂ)` for a homogeneous
polynomial `P` of degree `m`. -/
theorem exists_polynomial_of_isSectionFamily :
    ∃ k₀ : ℕ, ∀ m ≥ k₀, ∀ h : Fin (E.ambientDimension + 1) → SchemeComplexPoint f → ℂ,
      IsSectionFamily f E n m h →
        ∃ P : MvPolynomial (Fin (E.ambientDimension + 1)) ℂ, P.IsHomogeneous m ∧
          ∀ (l : Fin (E.ambientDimension + 1)) (p : SchemeComplexPoint f),
            schemeComplexPointImage f p ∈ coordOpen E l →
              h l p = MvPolynomial.eval (homCoords f E n l p) P := by
  obtain ⟨k₀, hk₀⟩ := exists_isHomogeneous_eq_of_jacobianPresentation
    (isHolomorphicEmbedding_projectivePoint f E n) (isJacobianPresentation_chartEquations f E n)
  refine ⟨max k₀ 1, fun m hm h hh => ?_⟩
  obtain ⟨P, hP, hPF⟩ := hk₀ m (le_of_max_le_left hm) (familyConeFun f E n m h)
    (fun c Z hZ => familyConeFun_smul hh (le_of_max_le_right hm) c hZ)
    (isLocallyHolomorphicOn_familyConeFun hh)
  refine ⟨P, hP, fun l p hp => ?_⟩
  set Z : ComplexModel (E.ambientDimension + 1) := WithLp.toLp 2 (homCoords f E n l p)
  have hZv : WithLp.ofLp Z ≠ 0 := homCoords_ne_zero f E n l hp
  have hZp : projectivePoint f E n p = mk (WithLp.ofLp Z) hZv := projectivePoint_eq f E n l hp
  have hZC : Z ∈ affineCone (range (projectivePoint f E n)) := fun _ => ⟨p, hZp⟩
  have h1 := familyConeFun_eq hh hZv hZp l hp
  have hZl : Z l = 1 := homCoords_self f E n l hp
  rw [hZl, one_pow, one_mul] at h1
  rw [← h1, ← hPF Z hZC]

end SGPT.GAGA.H0L
