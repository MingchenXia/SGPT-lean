import SGPT.BDivisor.GMConeModule
import SGPT.BDivisor.BD6Morphism
import SGPT.NAPotential.ProjectiveGraphProjectiveHomeomorph
import SGPT.GAGA.SmoothFlagsScheme

/-!
# GAGA for morphisms — holomorphic maps `V(ℂ) → W(ℂ)` are algebraic

Source: the GAGA input "holomorphic maps between projective varieties are algebraic", used in
`rmk:bdiv:L749` (cofinality of the algebraized models), `rmk:valcurr` and `rmk:Abhyankar`
(resolutions of a normal projective variety).  Analytic half: `SGPT.BDivisor.GMConeModule`.

Let `V` be a smooth projective complex scheme (structure map `g`, closed projective embedding
`EV`, e.g. one of the algebraizations `exists_algebraization_of_chow_bd5`) and `W` any
complex scheme with a closed projective embedding `EW : W → ℙᴹ` (reduced, normal or smooth: no
condition is needed).  A complex point `w` of `W` has the point `ambientPoint EW w ∈ ℙᴹ`
(`EW ∘ w`, read through the homeomorphism `ℙᴹ(ℂ) ≅ ℙᴹ`); for smooth `W` it is `projectivePoint`
(`ambientPoint_eq_projectivePoint`).

* `exists_morphism_to_projectiveSpace`: a holomorphic map `Ψ : V(ℂ) → ℙᴹ` is the analytification
  of a morphism `V → ℙᴹ` over `ℂ`.  By `exists_polynomial_lifts` there are tuples `P_k` of
  homogeneous polynomials with `[P_k(x(p))] = Ψ(p)` wherever `P_k(x(p)) ≠ 0`, and these sets cover
  `V(ℂ)`; on the Zariski open `D(P_{k,j}(x/xᵢ)) ⊆ Uᵢ` the regular functions `P_{k,b}/P_{k,j}`
  define a chart map to `D₊(y_j)` (the `chartMap`) sending every complex point `p` to `Ψ(p)`,
  and these chart maps glue (`BD6.glueChartMaps`).
* **`exists_unique_morphism_of_mdifferentiable`** (GM): a holomorphic `Ψ : V(ℂ) → ℙᴹ` with values
  in `W(ℂ)` is `EW ∘ ρ` on complex points for a unique morphism `ρ : V → W` over `ℂ`: the morphism
  `V → ℙᴹ` lifts through the closed immersion `EW` (`IsClosedImmersion.lift`; `V` is reduced, so the
  kernel of `V → ℙᴹ` is the ideal of the closure of its image, which lies in `W` because the closed
  points of `V` are dense); uniqueness: `V` is reduced and its closed points are its complex points
  (`eq_of_schemeComplexPointMap_eq`, Mathlib's `ext_of_apply_eq`).
* **`exists_unique_morphism_of_holomorphic`** (GM): every map `Φ : V(ℂ) → W(ℂ)` with
  `ambientPoint EW ∘ Φ` holomorphic is the complex-point map of a unique morphism `V → W` over `ℂ`;
  `exists_unique_morphism_of_holomorphic_smooth`: for smooth `W`, every holomorphic
  `Φ : V(ℂ) → W(ℂ)` between the complex manifolds.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.BDivisor.GM

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set Filter
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Okounkov SGPT.GAGA.H0S SGPT.GAGA.ChowBl
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.BDivisor.BD6 SGPT.NAPotential.AlgPrimes3.ProjectiveGraphProjectiveHomeomorph
open SGPT.NAPotential.AlgPrimes3.ProjectiveGraphProjectivePoint
open SGPT.NAPotential.AlgPrimes3.ProjectiveGraphPointEvaluation SGPT.NAPotential.FSPos

attribute [local instance] MvPolynomial.gradedAlgebra SGPT.Toric.monomialProjectiveTopology

/-- The analytic topology on the complex points of a complex scheme. -/
local instance gmPointTopology {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) :
    TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f

/-! ### Complex points of a projectively embedded scheme as points of `ℙᴹ` -/

section Ambient

/-- The analytic point of `ℙᴹ` of the complex point of `ℙᴹ` given by a nonzero vector. -/
theorem originalProjectiveHomeomorph_vectorPoint {M : ℕ} (v : Fin (M + 1) → ℂ) (hv : v ≠ 0) :
    originalProjectiveHomeomorph M (polynomialProjNonzeroVectorPoint M ⟨v, hv⟩) = mk v hv := by
  rw [← SGPT.Toric.nativeProjectivePointHomeomorph_mk M ⟨v, hv⟩]
  exact (SGPT.Toric.nativeProjectivePointHomeomorph M).symm_apply_apply _

variable {W : Scheme.{0}} {f : W ⟶ Spec (.of ℂ)} (EW : ClosedProjectiveEmbedding f)

/-- **The point of `ℙᴹ` of a complex point** `w` of a complex scheme `W` with a closed projective
embedding `EW : W → ℙᴹ`: the complex point `EW ∘ w` of `ℙᴹ`, read in the analytic `ℙᴹ`.  No
smoothness of `W` is needed; for smooth `W` this is `projectivePoint`
(`ambientPoint_eq_projectivePoint`). -/
def ambientPoint (w : SchemeComplexPoint f) : ComplexProjectiveSpace EW.ambientDimension :=
  originalProjectiveHomeomorph EW.ambientDimension
    (schemeComplexPointMap f _ EW.map EW.over_base w)

/-- Distinct complex points of `W` have distinct points in `ℙᴹ`. -/
theorem ambientPoint_injective : Function.Injective (ambientPoint EW) := by
  intro w w' h
  have h1 := (originalProjectiveHomeomorph EW.ambientDimension).injective h
  have h2 : w.val ≫ EW.map = w'.val ≫ EW.map := congrArg Subtype.val h1
  exact Subtype.ext ((cancel_mono EW.map).mp h2)

/-- **For smooth `W`, `ambientPoint` is `projectivePoint`.** -/
theorem ambientPoint_eq_projectivePoint (m : ℕ) [SmoothOfRelativeDimension m f]
    (w : SchemeComplexPoint f) : ambientPoint EW w = projectivePoint f EW m w := by
  let := EW.isSeparated
  let := EW.quasiCompact
  let i := frameIndex f EW w
  have hp := mem_coordOpen_frameIndex f EW w
  let q := schemeComplexPointMap f _ EW.map EW.over_base w
  have hq : schemeComplexPointImage (polynomialProjStructureMap ℂ EW.ambientDimension) q ∈
      coordOpen (identityEmbedding EW.ambientDimension) i := hp
  have hvec : homCoords (polynomialProjStructureMap ℂ EW.ambientDimension)
      (identityEmbedding EW.ambientDimension) EW.ambientDimension i q = homCoords f EW m i w := by
    funext k
    change schemeOpenRegularFunction _ _ _ _ _ q = schemeOpenRegularFunction f m EW _ _ w
    rw [← canonical_value_original, ← canonical_value_original]
    rw [schemeComplexPointStalkEval_comp]
    change schemeComplexPointStalkEval f w
        ((EW.map.stalkMap (schemeComplexPointImage f w)).hom
          ((polynomialProj ℂ EW.ambientDimension).presheaf.germ _ _ hq _)) = _
    erw [EW.map.germ_stalkMap_apply]
    rfl
  have hm : ComplexProjectiveSpace.mk
      (homCoords (polynomialProjStructureMap ℂ EW.ambientDimension)
        (identityEmbedding EW.ambientDimension) EW.ambientDimension i q)
      (homCoords_ne_zero (polynomialProjStructureMap ℂ EW.ambientDimension)
        (identityEmbedding EW.ambientDimension) EW.ambientDimension i hq) =
      ComplexProjectiveSpace.mk (homCoords f EW m i w) (homCoords_ne_zero f EW m i hp) :=
    (pmk_eq_mk (homCoords_ne_zero (polynomialProjStructureMap ℂ EW.ambientDimension)
      (identityEmbedding EW.ambientDimension) EW.ambientDimension i hq)).symm.trans
      ((congrArg pmk hvec).trans (pmk_eq_mk (homCoords_ne_zero f EW m i hp)))
  exact (originalProjectiveHomeomorph_apply EW.ambientDimension q).trans
    ((projectivePoint_eq (polynomialProjStructureMap ℂ EW.ambientDimension)
      (identityEmbedding EW.ambientDimension) EW.ambientDimension i hq).trans
        (hm.trans (projectivePoint_eq f EW m i hp).symm))

end Ambient

/-! ### Uniqueness -/

/-- **A morphism from a reduced complex scheme of finite type is determined by its complex
points**: two morphisms `V → W` over `ℂ` (`W` separated, locally of finite type) with the same
complex-point maps are equal. -/
theorem eq_of_schemeComplexPointMap_eq {V W : Scheme.{0}} (g : V ⟶ Spec (.of ℂ))
    (f : W ⟶ Spec (.of ℂ)) [IsReduced V] [LocallyOfFiniteType g] [IsSeparated f]
    [LocallyOfFiniteType f] {ρ ρ' : V ⟶ W} (hρ : ρ ≫ f = g) (hρ' : ρ' ≫ f = g)
    (h : ∀ z, schemeComplexPointMap g f ρ hρ z = schemeComplexPointMap g f ρ' hρ' z) :
    ρ = ρ' := by
  have : LocallyOfFiniteType (ρ ≫ f) := by rw [hρ]; infer_instance
  refine ext_of_apply_eq f Set.univ isOpen_univ.isLocallyClosed dense_univ
    (fun x _ hx => ?_) (hρ.trans hρ'.symm)
  set q := pointOfClosedPoint g x hx
  have hq : q default = x := pointOfClosedPoint_apply g x hx default
  have hqc : q ≫ g = 𝟙 _ := pointOfClosedPoint_comp g x hx
  have h1 := congrArg (fun z => z.val default) (h ⟨q, hqc⟩)
  simp only [schemeComplexPointMap, Scheme.Hom.comp_apply, hq] at h1
  exact h1

/-! ### Holomorphic maps to `ℙᴹ` -/

section Morphism

variable {V : Scheme.{0}} (g : V ⟶ Spec (.of ℂ)) (EV : ClosedProjectiveEmbedding g) (n : ℕ)
  [SmoothOfRelativeDimension n g] [IsSeparated g] [QuasiCompact g]

local instance gmCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint g) :=
  schemeAnalyticTNChartedSpace g n
local instance gmManifold : IsComplexManifold n (SchemeComplexPoint g) :=
  schemeAnalyticTN_isComplexManifold g n

omit [SmoothOfRelativeDimension n g] [IsSeparated g] [QuasiCompact g] in
theorem pointValue_mul (p : SchemeComplexPoint g) (U : V.Opens)
    (hp : schemeComplexPointImage g p ∈ U) (a b : Γ(V, U)) :
    pointValue g p U hp (a * b) = pointValue g p U hp a * pointValue g p U hp b := by
  simp only [pointValue, map_mul]

omit [SmoothOfRelativeDimension n g] [IsSeparated g] [QuasiCompact g] in
theorem pointValue_one (p : SchemeComplexPoint g) (U : V.Opens)
    (hp : schemeComplexPointImage g p ∈ U) : pointValue g p U hp 1 = 1 := by
  simp only [pointValue, map_one]

omit [SmoothOfRelativeDimension n g] [IsSeparated g] [QuasiCompact g] in
theorem pointValue_res (p : SchemeComplexPoint g) {U O : V.Opens} (h : O ≤ U)
    (hpO : schemeComplexPointImage g p ∈ O) (hpU : schemeComplexPointImage g p ∈ U)
    (s : Γ(V, U)) :
    pointValue g p O hpO (V.presheaf.map (homOfLE h).op s) = pointValue g p U hpU s := by
  simp only [pointValue, TopCat.Presheaf.germ_res_apply]

include EV in
/-- **Holomorphic maps `V(ℂ) → ℙᴹ` are algebraic.** For a smooth projective complex scheme `V` and a
holomorphic map `Ψ : V(ℂ) → ℙᴹ` there is a morphism `φ : V → ℙᴹ` over `ℂ` whose complex points
are `Ψ`. -/
theorem exists_morphism_to_projectiveSpace {M : ℕ}
    (Ψ : SchemeComplexPoint g → ComplexProjectiveSpace M)
    (hΨ : MDifferentiable 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel M) Ψ) :
    ∃ (φ : V ⟶ polynomialProj ℂ M) (hφ : φ ≫ polynomialProjStructureMap ℂ M = g),
      ∀ z, originalProjectiveHomeomorph M (schemeComplexPointMap g _ φ hφ z) = Ψ z := by
  classical
  let : CompactSpace (SchemeComplexPoint g) := EV.analyticCompact
  have := EV.locallyOfFiniteType
  obtain ⟨m, μ, hμ, P, hPh, hcov, hprop⟩ :=
    exists_polynomial_lifts (isHolomorphicEmbedding_projectivePoint g EV n) hΨ
  -- the chosen data at each complex point `c`: a tuple `P_k` and a coordinate `j` with
  -- `P_{k,j}(x(c)) ≠ 0`, and a frame `xᵢ` at `c`
  have hdata : ∀ c : SchemeComplexPoint g, ∃ (k : μ) (j : Fin (M + 1))
      (i : Fin (EV.ambientDimension + 1)), schemeComplexPointImage g c ∈ coordOpen EV i ∧
        schemeComplexPointImage g c ∈ V.basicOpen (chartFn g EV i (P k j)) := by
    intro c
    obtain ⟨k, hk⟩ := hcov c
    obtain ⟨j, hj⟩ : ∃ j, MvPolynomial.eval (projectivePoint g EV n c).rep (P k j) ≠ 0 := by
      by_contra! h0
      exact hk (funext h0)
    have hi := mem_coordOpen_frameIndex g EV c
    refine ⟨k, j, frameIndex g EV c, hi, ?_⟩
    rw [← schemeOpenRegularFunction_ne_zero_iff g EV n _ _ c hi, chartFn_value g EV n _ _ c hi]
    obtain ⟨t, -, hrep⟩ := rep_smul (projectivePoint g EV n c)
      (homCoords_ne_zero g EV n _ hi) (projectivePoint_eq g EV n _ hi)
    rw [hrep, eval_smul_of_isHomogeneous (hPh k j)] at hj
    exact right_ne_zero_of_mul hj
  choose k j i hci hcb using hdata
  -- the chart maps
  let s : ∀ c : SchemeComplexPoint g, Γ(V, coordOpen EV (i c)) := fun c =>
    chartFn g EV (i c) (P (k c) (j c))
  let O : SchemeComplexPoint g → V.Opens := fun c => V.basicOpen (s c)
  have hOle : ∀ c, O c ≤ coordOpen EV (i c) := fun c => V.basicOpen_le (s c)
  have hunit : ∀ c, IsUnit (V.presheaf.map (homOfLE (hOle c)).op (s c)) := fun c =>
    V.toRingedSpace.isUnit_res_basicOpen (s c)
  let t : ∀ c, Fin (M + 1) → Γ(V, O c) := fun c b =>
    V.presheaf.map (homOfLE (hOle c)).op (chartFn g EV (i c) (P (k c) b)) * ↑(hunit c).unit⁻¹
  have ht : ∀ c, t c (j c) = 1 := fun c => (hunit c).mul_val_inv
  -- every chart map sends a complex point `p` to `Ψ p`
  have hval : ∀ c (p : SchemeComplexPoint g) (hp : schemeComplexPointImage g p ∈ O c),
      polynomialProjVectorChartPoint M (j c) (fun b => pointValue g p (O c) hp (t c b)) =
        (originalProjectiveHomeomorph M).symm (Ψ p) := by
    intro c p hp
    have hpi : schemeComplexPointImage g p ∈ coordOpen EV (i c) := hOle c hp
    set H : Fin (M + 1) → ℂ := fun b =>
      MvPolynomial.eval (homCoords g EV n (i c) p) (P (k c) b) with hHdef
    have hH : ∀ b, pointValue g p (coordOpen EV (i c)) hpi (chartFn g EV (i c) (P (k c) b)) =
        H b := fun b => by
      rw [pointValue_eq g EV n, chartFn_value g EV n _ _ p hpi]
    have hT : (fun b => pointValue g p (O c) hp (t c b)) =
        pointValue g p (O c) hp ↑(hunit c).unit⁻¹ • H := by
      funext b
      simp only [t, pointValue_mul, pointValue_res g p (hOle c) hp hpi, hH, Pi.smul_apply,
        smul_eq_mul]
      ring
    set w := pointValue g p (O c) hp ↑(hunit c).unit⁻¹ with hwdef
    have hHj : H (j c) ≠ 0 := by
      rw [← hH (j c), pointValue_eq g EV n]
      exact (schemeOpenRegularFunction_ne_zero_iff g EV n _ _ p hpi).mpr hp
    have hw : w ≠ 0 := by
      have h1 : pointValue g p (O c) hp (t c (j c)) = 1 := by
        rw [ht c]
        exact pointValue_one g p (O c) hp
      have h2 := congrFun hT (j c)
      simp only [Pi.smul_apply, smul_eq_mul] at h2
      rw [h1] at h2
      intro h0
      rw [h0, zero_mul] at h2
      exact one_ne_zero h2
    have hHne : H ≠ 0 := fun h0 => hHj (congrFun h0 (j c))
    have hmk : mk H hHne = Ψ p := by
      obtain ⟨τ, hτ, hrep⟩ := rep_smul (projectivePoint g EV n p)
        (homCoords_ne_zero g EV n _ hpi) (projectivePoint_eq g EV n _ hpi)
      have hE : (fun b => MvPolynomial.eval (projectivePoint g EV n p).rep (P (k c) b)) =
          (τ ^ m) • H := by
        funext b
        rw [hrep, eval_smul_of_isHomogeneous (hPh _ b)]
        rfl
      have hEne : (fun b => MvPolynomial.eval (projectivePoint g EV n p).rep (P (k c) b)) ≠ 0 := by
        rw [hE]
        exact smul_ne_zero (pow_ne_zero _ hτ) hHne
      rw [← hprop (k c) p hEne]
      refine (mk_eq_mk_iff hHne hEne).mpr ⟨(τ ^ m)⁻¹, ?_⟩
      rw [hE, smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hτ), one_smul]
    have hch := polynomialProjNonzeroVectorPoint_eq_chart M ⟨H, hHne⟩ (j c) hHj
    simp only at hch
    rw [hT, polynomialProjVectorChartPoint_smul M (j c) H w hw, ← hch, eq_comm,
      Homeomorph.symm_apply_eq, originalProjectiveHomeomorph_vectorPoint, hmk]
  -- gluing
  have hcover : TopologicalSpace.IsOpenCover O := by
    apply top_unique
    intro y _
    obtain ⟨p, -, hyp⟩ := SGPT.GAGA.H0L.exists_specializes_schemeComplexPoint g
      (W := ⊤) (y := y) trivial
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨p, hyp.mem_open (O p).isOpen (hcb p)⟩
  have hcompat : ∀ (a b : SchemeComplexPoint g) (p : SchemeComplexPoint g)
      (hU : schemeComplexPointImage g p ∈ O a) (hV : schemeComplexPointImage g p ∈ O b),
      polynomialProjVectorChartPoint M (j a) (fun l => pointValue g p (O a) hU (t a l)) =
        polynomialProjVectorChartPoint M (j b) (fun l => pointValue g p (O b) hV (t b l)) :=
    fun a b p hU hV => (hval a p hU).trans (hval b p hV).symm
  have : AlgebraicGeometry.IsReduced V :=
    SGPT.Projective.NumEq.AlgebraicCurveDegree.smoothScheme_isReduced g n
  refine ⟨glueChartMaps g O hcover j t ht hcompat, glueChartMaps_structure g O hcover j t ht hcompat,
    fun z => ?_⟩
  rw [glueChartMaps_point g O hcover j t ht hcompat z z (hcb z), hval z z (hcb z),
    Homeomorph.apply_symm_apply]

/-! ### GAGA for morphisms -/

variable {W : Scheme.{0}} (f : W ⟶ Spec (.of ℂ)) (EW : ClosedProjectiveEmbedding f)

include EV in
/-- **(GM) GAGA for morphisms, map-into-`ℙᴹ` form.** Let `V` be a smooth projective complex scheme
and `W` a complex scheme with a closed projective embedding `EW : W → ℙᴹ`.  Every holomorphic map
`Ψ : V(ℂ) → ℙᴹ` with values in `W(ℂ)` is, on complex points, `EW ∘ ρ` for a unique morphism
`ρ : V → W` over `ℂ`. -/
theorem exists_unique_morphism_of_mdifferentiable
    (Ψ : SchemeComplexPoint g → ComplexProjectiveSpace EW.ambientDimension)
    (hΨ : MDifferentiable 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel EW.ambientDimension) Ψ)
    (hrange : ∀ z, Ψ z ∈ Set.range (ambientPoint EW)) :
    ∃! ρ : V ⟶ W, ∃ hρ : ρ ≫ f = g,
      ∀ z, ambientPoint EW (schemeComplexPointMap g f ρ hρ z) = Ψ z := by
  classical
  have := EV.locallyOfFiniteType
  have := EW.isSeparated
  have := EW.locallyOfFiniteType
  have : AlgebraicGeometry.IsReduced V :=
    SGPT.Projective.NumEq.AlgebraicCurveDegree.smoothScheme_isReduced g n
  obtain ⟨φ, hφ, hpt⟩ := exists_morphism_to_projectiveSpace g EV n Ψ hΨ
  -- `φ` maps the complex points into `W`
  have hpts : ∀ z : SchemeComplexPoint g, φ (schemeComplexPointImage g z) ∈ Set.range EW.map := by
    intro z
    obtain ⟨w, hw⟩ := hrange z
    have h1 : schemeComplexPointMap g _ φ hφ z = schemeComplexPointMap f _ EW.map EW.over_base w :=
      (originalProjectiveHomeomorph _).injective ((hpt z).trans hw.symm)
    refine ⟨schemeComplexPointImage f w, ?_⟩
    have h2 := congrArg (fun q => q.val default) h1
    simp only [schemeComplexPointMap, Scheme.Hom.comp_apply] at h2
    exact h2.symm
  -- hence all of `V` (the complex points are dense in every closed set)
  have hsub : ∀ y : V, φ y ∈ Set.range EW.map := by
    intro y
    by_contra hy
    let Z : V.Opens := ⟨φ ⁻¹' (Set.range EW.map)ᶜ,
      (EW.map.isClosedEmbedding.isClosed_range.isOpen_compl).preimage φ.continuous⟩
    obtain ⟨p, hpZ, -⟩ := SGPT.GAGA.H0L.exists_specializes_schemeComplexPoint g
      (W := Z) (y := y) hy
    exact hpZ (hpts p)
  -- the kernel condition for the lift through the closed immersion `EW`
  have hker : EW.map.ker ≤ φ.ker := by
    have h1 : φ.ker = Scheme.IdealSheafData.vanishingIdeal
        (TopologicalSpace.Closeds.closure (φ '' ((⊤ : TopologicalSpace.Closeds V) : Set V))) := by
      rw [← Scheme.IdealSheafData.map_vanishingIdeal, Scheme.IdealSheafData.vanishingIdeal_top,
        Scheme.nilradical_eq_bot, Scheme.IdealSheafData.map_bot]
    rw [h1, ← Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal,
      TopologicalSpace.Closeds.closure_le]
    rintro _ ⟨y, -, rfl⟩
    exact EW.map.range_subset_ker_support (hsub y)
  let ρ := IsClosedImmersion.lift EW.map φ hker
  have hρφ : ρ ≫ EW.map = φ := IsClosedImmersion.lift_fac EW.map φ hker
  have hρ : ρ ≫ f = g := by rw [← EW.over_base, ← Category.assoc, hρφ, hφ]
  have hρpt : ∀ z, ambientPoint EW (schemeComplexPointMap g f ρ hρ z) = Ψ z := by
    intro z
    rw [ambientPoint, ← hpt z]
    congr 1
    apply Subtype.ext
    change (z.val ≫ ρ) ≫ EW.map = z.val ≫ φ
    rw [Category.assoc, hρφ]
  refine ⟨ρ, ⟨hρ, hρpt⟩, ?_⟩
  rintro ρ' ⟨hρ', hρ'pt⟩
  exact eq_of_schemeComplexPointMap_eq g f hρ' hρ fun z =>
    ambientPoint_injective EW ((hρ'pt z).trans (hρpt z).symm)

include EV in
/-- **(GM) GAGA for morphisms.** Let `V` be a smooth projective complex scheme and `W` a complex
scheme with a closed projective embedding `EW : W → ℙᴹ`.  Every map `Φ : V(ℂ) → W(ℂ)` which is
holomorphic into `ℙᴹ` (`ambientPoint EW ∘ Φ` holomorphic) is the complex-point map of a unique
morphism `ρ : V → W` over `ℂ`. -/
theorem exists_unique_morphism_of_holomorphic (Φ : SchemeComplexPoint g → SchemeComplexPoint f)
    (hΦ : MDifferentiable 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel EW.ambientDimension)
      (ambientPoint EW ∘ Φ)) :
    ∃! ρ : V ⟶ W, ∃ hρ : ρ ≫ f = g, ∀ z, schemeComplexPointMap g f ρ hρ z = Φ z := by
  obtain ⟨ρ, ⟨hρ, hρpt⟩, huniq⟩ := exists_unique_morphism_of_mdifferentiable g EV n f EW
    (ambientPoint EW ∘ Φ) hΦ fun z => ⟨Φ z, rfl⟩
  refine ⟨ρ, ⟨hρ, fun z => ambientPoint_injective EW (hρpt z)⟩, ?_⟩
  rintro ρ' ⟨hρ', hρ'pt⟩
  exact huniq ρ' ⟨hρ', fun z => by rw [hρ'pt z]; rfl⟩

include EV EW in
/-- **(GM) for smooth `W`**: every holomorphic map `Φ : V(ℂ) → W(ℂ)` between the complex manifolds of
two smooth projective complex schemes is the complex-point map of a unique morphism `V → W` over
`ℂ`. -/
theorem exists_unique_morphism_of_holomorphic_smooth (m : ℕ) [SmoothOfRelativeDimension m f]
    [IsSeparated f] [QuasiCompact f] (Φ : SchemeComplexPoint g → SchemeComplexPoint f)
    (hΦ : MDifferentiable 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m) Φ) :
    ∃! ρ : V ⟶ W, ∃ hρ : ρ ≫ f = g, ∀ z, schemeComplexPointMap g f ρ hρ z = Φ z := by
  have hW : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel EW.ambientDimension) ∞
      (projectivePoint f EW m) :=
    SGPT.GAGA.SmoothFlags.contMDiff_of_isHolomorphicEmbedding
      (isHolomorphicEmbedding_projectivePoint f EW m)
  have hcomp : ambientPoint EW ∘ Φ = projectivePoint f EW m ∘ Φ := by
    funext z
    exact ambientPoint_eq_projectivePoint EW m (Φ z)
  refine exists_unique_morphism_of_holomorphic g EV n f EW Φ ?_
  rw [hcomp]
  exact (hW.mdifferentiable (by simp)).comp hΦ

end Morphism

end SGPT.BDivisor.GM
