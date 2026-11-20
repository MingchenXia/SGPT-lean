import SGPT.Okounkov.OF2ModificationFlagValuation
import SGPT.Okounkov.FlagValuationSchemeChowFunctions
import SGPT.Okounkov.FlagValuationGlobalPolynomialZeros

/-!
# `rmk:valcurr`: projective embeddings of models by rational functions of `X`

Source: chapter *The theory of Okounkov bodies*, `rmk:valcurr`: *"This definition does not depend
on the choice of `π`, by passing to a common resolution and applying `prop:cormatrix` and
`prop:cormult`."*  On a common model the two presentations become presentations by flags on the
**same** model; to conclude, the flag must be determined by (the equivalence class of) the
valuation it induces on `ℂ(X)`.  On a model `π : Y → X(ℂ)` this needs `ℂ(X)` to see the geometry
of `Y`.  This file sets up the tool: a projective embedding `Ψ : Y → ℙᴺ` all of whose ratios of
homogeneous polynomials are pull-backs of rational functions of `X`.

* `fracComap`: pull-back of meromorphic germs along an analytic modification (well defined since
  modifications do not collapse holomorphic germs, `OF2.nativeHolGerm_comap_injective`), with its
  composition law `fracComap_comp`.
* `ratGerm f hρ y : ℂ(X) → Frac 𝒪_{Y,y}`: `q ↦ ρ^* q`, the germ at `y` of the pull-back of a
  rational function of `X` along a model `ρ : Y → X(ℂ)` (`ratGerm_comp`).
* `IsRationalEmbedding f hρ hΨ`: for all homogeneous `P, Q` of the same degree with `Q ∘ Ψ ≢ 0`
  there is ONE `q ∈ ℂ(X)` with `ρ^* q · Q(Ψ) = P(Ψ)` as germs at every point of `Y`, in every affine
  chart of `ℙᴺ` (`Q(Ψ)`, `P(Ψ)` read through the normalized lift `genFun`).
* `isRationalEmbedding_projectivePoint`: the closed projective embedding `X(ℂ) → ℙᴺ` of `X` is a
  rational embedding (`q = P(x/xᵢ)/Q(x/xᵢ)`, glued by the frame transitions `polyFF_transition`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

namespace SGPT.Okounkov.OF9

open CategoryTheory AlgebraicGeometry Set Filter SGPT.Foundations.Schemes Opposite
open SGPT.Okounkov
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.GAGA.H0S SGPT.GAGA.ChowBl SGPT.NAPotential.FSPos
open scoped Topology Manifold ContDiff

/-! ### Pull-back of meromorphic germs -/

section Fraction

variable {n : ℕ} {M Y Z : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y] [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z]
  [IsComplexManifold n Z]

/-- Pull-back of meromorphic germs along an analytic modification `g`, at `y` and `g y`. -/
def fracComap {g : Y → M} (hg : IsAnalyticModification (n := n) g) (y : Y) :
    FractionRing (NativeHolGerm n M (g y)) →+* FractionRing (NativeHolGerm n Y y) :=
  IsFractionRing.map (OF2.nativeHolGerm_comap_injective hg y)

theorem fracComap_algebraMap {g : Y → M} (hg : IsAnalyticModification (n := n) g) (y : Y)
    (a : NativeHolGerm n M (g y)) :
    fracComap hg y (algebraMap _ _ a) = algebraMap _ _ (NativeHolGerm.comap g hg.1 y a) := by
  unfold fracComap IsFractionRing.map
  exact IsLocalization.map_eq _ _

/-- Pull-back of holomorphic germs is functorial. -/
theorem nativeHolGerm_comap_comp {g : Y → M} {h : Z → Y}
    (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g)
    (hh : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ h)
    (hgh : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ (g ∘ h)) (z : Z)
    (a : NativeHolGerm n M (g (h z))) :
    NativeHolGerm.comap (g ∘ h) hgh z a =
      NativeHolGerm.comap h hh z (NativeHolGerm.comap g hg (h z) a) := by
  obtain ⟨G, hG, rfl⟩ := NativeHolGerm.exists_eq_mk a
  apply Subtype.ext
  rfl

/-- Pull-back of meromorphic germs is functorial. -/
theorem fracComap_comp {g : Y → M} {h : Z → Y} (hg : IsAnalyticModification (n := n) g)
    (hh : IsAnalyticModification (n := n) h) (hgh : IsAnalyticModification (n := n) (g ∘ h))
    (z : Z) (a : FractionRing (NativeHolGerm n M (g (h z)))) :
    fracComap hgh z a = fracComap hh z (fracComap hg (h z) a) := by
  have key : fracComap hgh z = ((fracComap hh z).comp (fracComap hg (h z)) :
      FractionRing (NativeHolGerm n M ((g ∘ h) z)) →+* FractionRing (NativeHolGerm n Z z)) := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors (NativeHolGerm n M ((g ∘ h) z)))
    apply RingHom.ext
    intro b
    simp only [RingHom.comp_apply]
    have e1 := fracComap_algebraMap hgh z b
    have e2 : fracComap hg (h z) (algebraMap (NativeHolGerm n M ((g ∘ h) z))
        (FractionRing (NativeHolGerm n M ((g ∘ h) z))) b) =
        algebraMap _ _ (NativeHolGerm.comap g hg.1 (h z) b) := fracComap_algebraMap hg (h z) b
    rw [e1]
    calc _ = algebraMap _ (FractionRing (NativeHolGerm n Z z))
          (NativeHolGerm.comap h hh.1 z (NativeHolGerm.comap g hg.1 (h z) b)) :=
            congrArg _ (nativeHolGerm_comap_comp hg.1 hh.1 hgh.1 z b)
      _ = fracComap hh z (algebraMap _ _ (NativeHolGerm.comap g hg.1 (h z) b)) :=
            (fracComap_algebraMap hh z _).symm
      _ = _ := congrArg (fracComap hh z) e2.symm
  exact RingHom.congr_fun key a

/-- Pull-back along the identity is the identity. -/
theorem fracComap_id (hid : IsAnalyticModification (n := n) (id : M → M)) (y : M)
    (a : FractionRing (NativeHolGerm n M y)) : fracComap hid y a = a := by
  have key : fracComap hid y = (RingHom.id (FractionRing (NativeHolGerm n M y)) :
      FractionRing (NativeHolGerm n M (id y)) →+* FractionRing (NativeHolGerm n M y)) := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors (NativeHolGerm n M (id y)))
    apply RingHom.ext
    intro b
    simp only [RingHom.comp_apply]
    rw [fracComap_algebraMap hid y b]
    have hb : NativeHolGerm.comap id hid.1 y b = b := by
      obtain ⟨G, hG, rfl⟩ := NativeHolGerm.exists_eq_mk b
      apply Subtype.ext
      rfl
    rw [hb]
    rfl
  exact RingHom.congr_fun key a

end Fraction

/-! ### Germs of chart restrictions of homogeneous polynomials -/

section PolyGerm

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] [CompactSpace M]

/-- The germ at `y` of `P(Ψ)` read in the affine chart `Uᵢ ∋ Ψ y`: `P(Λᵢ ∘ Ψ)`. -/
def polyGerm {N : ℕ} {Ψ : M → ComplexProjectiveSpace N} (hΨ : IsHolomorphicEmbedding (n := n) Ψ)
    {y : M} {i : Fin (N + 1)} (hi : Ψ y ∈ (affineChart i).source)
    (P : MvPolynomial (Fin (N + 1)) ℂ) : NativeHolGerm n M y :=
  NativeHolGerm.mk (genFun Ψ i P) (holomorphicAt_genFun hΨ hi P)

theorem eval_polyGerm {N : ℕ} {Ψ : M → ComplexProjectiveSpace N}
    (hΨ : IsHolomorphicEmbedding (n := n) Ψ) {y : M} {i : Fin (N + 1)}
    (hi : Ψ y ∈ (affineChart i).source) (P : MvPolynomial (Fin (N + 1)) ℂ) :
    NativeHolGerm.eval (polyGerm hΨ hi P) = genFun Ψ i P y :=
  rfl

/-- A homogeneous polynomial nonvanishing at `Ψ y` gives a unit germ. -/
theorem isUnit_polyGerm {N d : ℕ} {Ψ : M → ComplexProjectiveSpace N}
    (hΨ : IsHolomorphicEmbedding (n := n) Ψ) {y : M} {i : Fin (N + 1)}
    (hi : Ψ y ∈ (affineChart i).source) {P : MvPolynomial (Fin (N + 1)) ℂ}
    (hP : P.IsHomogeneous d) (hy : MvPolynomial.eval (Ψ y).rep P ≠ 0) :
    IsUnit (polyGerm hΨ hi P) := by
  rw [NativeHolGerm.isUnit_iff_eval_ne_zero, eval_polyGerm]
  exact fun h0 => hy ((eval_rep_eq_zero_iff_genFun Ψ i hi hP).mpr h0)

end PolyGerm

/-! ### Rational embeddings of models of `X` -/

section Scheme

variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ)) {n : ℕ}
  [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f]

local instance of9RatTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance of9RatCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance of9RatManifold : IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n

variable {M : Type} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- **The pull-back of rational functions of `X` to a model** `ρ : M → X(ℂ)`, read at `y`:
`q ↦ ρ^* q ∈ Frac 𝒪_{M,y}`. -/
def ratGerm {ρ : M → SchemeComplexPoint f} (hρ : IsAnalyticModification (n := n) ρ) (y : M) :
    X.functionField →+* FractionRing (NativeHolGerm n M y) :=
  (fracComap hρ y).comp (schemeNativeFunctionFieldGerm f n (ρ y))

theorem ratGerm_apply {ρ : M → SchemeComplexPoint f} (hρ : IsAnalyticModification (n := n) ρ)
    (y : M) (q : X.functionField) :
    ratGerm f hρ y q = fracComap hρ y (schemeNativeFunctionFieldGerm f n (ρ y) q) :=
  rfl

/-- Pull-back of rational functions along a composite model. -/
theorem ratGerm_comp {Z : Type} [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z]
    [IsComplexManifold n Z] {ρ : M → SchemeComplexPoint f} {g : Z → M}
    (hρ : IsAnalyticModification (n := n) ρ) (hg : IsAnalyticModification (n := n) g)
    (hρg : IsAnalyticModification (n := n) (ρ ∘ g)) (z : Z) (q : X.functionField) :
    ratGerm f hρg z q = fracComap hg z (ratGerm f hρ (g z) q) := by
  rw [ratGerm_apply, ratGerm_apply]
  exact fracComap_comp hρ hg hρg z _

/-- On `X(ℂ)` itself (the model `id`), `ratGerm` is the germ map of rational functions. -/
theorem ratGerm_id (hid : IsAnalyticModification (n := n) (id : SchemeComplexPoint f → _))
    (y : SchemeComplexPoint f) (q : X.functionField) :
    ratGerm f hid y q = schemeNativeFunctionFieldGerm f n y q := by
  rw [ratGerm_apply]
  exact fracComap_id hid y _

/-- **Rational embeddings.** A holomorphic embedding `Ψ : M → ℙᴺ` of a model `ρ : M → X(ℂ)` is
*rational* if every ratio `P(Ψ)/Q(Ψ)` of homogeneous polynomials of the same degree (`Q ∘ Ψ ≢ 0`)
is the pull-back `ρ^* q` of one rational function `q ∈ ℂ(X)`: `ρ^* q · Q(Ψ) = P(Ψ)` as meromorphic
germs at every point of `M`, in every affine chart. -/
def IsRationalEmbedding [CompactSpace M] {ρ : M → SchemeComplexPoint f}
    (hρ : IsAnalyticModification (n := n) ρ)
    {N : ℕ} {Ψ : M → ComplexProjectiveSpace N} (hΨ : IsHolomorphicEmbedding (n := n) Ψ) : Prop :=
  ∀ (d : ℕ) (P Q : MvPolynomial (Fin (N + 1)) ℂ), P.IsHomogeneous d → Q.IsHomogeneous d →
    (∃ y, MvPolynomial.eval (Ψ y).rep Q ≠ 0) →
    ∃ q : X.functionField, ∀ (y : M) (i : Fin (N + 1)) (hi : Ψ y ∈ (affineChart i).source),
      ratGerm f hρ y q * algebraMap _ (FractionRing (NativeHolGerm n M y)) (polyGerm hΨ hi Q) =
        algebraMap _ (FractionRing (NativeHolGerm n M y)) (polyGerm hΨ hi P)

/-! ### The base: `X(ℂ) ⊆ ℙᴺ` -/

variable (E : ClosedProjectiveEmbedding f)

omit [IsSeparated f] [QuasiCompact f] in
/-- The generic point lies in every affine coordinate open meeting a complex point. -/
theorem genericPoint_mem_coordOpen {i : Fin (E.ambientDimension + 1)} {p : SchemeComplexPoint f}
    (hp : schemeComplexPointImage f p ∈ coordOpen E i) : genericPoint X ∈ coordOpen E i :=
  ((genericPoint_spec X).mem_open_set_iff (coordOpen E i).isOpen).mpr
    ⟨schemeComplexPointImage f p, trivial, hp⟩

omit [IsSeparated f] [QuasiCompact f] in
/-- `P(x/xᵢ)` as a rational function of `X`. -/
def polyFF (i : Fin (E.ambientDimension + 1)) (hi : genericPoint X ∈ coordOpen E i)
    (P : MvPolynomial (Fin (E.ambientDimension + 1)) ℂ) : X.functionField :=
  (X.presheaf.germ (coordOpen E i) (genericPoint X) hi).hom (polyCoef E i P)

omit [IsSeparated f] [QuasiCompact f] in
/-- The rational function `P(x/xᵢ)` is the image of its germ at any point of `Uᵢ`. -/
theorem polyFF_eq_algebraMap (i : Fin (E.ambientDimension + 1))
    (hi : genericPoint X ∈ coordOpen E i) (P : MvPolynomial (Fin (E.ambientDimension + 1)) ℂ)
    {x : X} (hx : x ∈ coordOpen E i) :
    polyFF f E i hi P = algebraMap _ X.functionField
      ((X.presheaf.germ (coordOpen E i) x hx).hom (polyCoef E i P)) := by
  change _ = (X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes trivial)).hom
    ((X.presheaf.germ (coordOpen E i) x hx).hom (polyCoef E i P))
  rw [← CommRingCat.comp_apply, TopCat.Presheaf.germ_stalkSpecializes]
  rfl

/-- The analytic germ of `P(x/xᵢ)` at a complex point of `Uᵢ` is `P(Ψ)` read in `Uᵢ`. -/
theorem schemeNativeFunctionFieldGerm_polyFF (i : Fin (E.ambientDimension + 1))
    (hi : genericPoint X ∈ coordOpen E i) (P : MvPolynomial (Fin (E.ambientDimension + 1)) ℂ)
    (p : SchemeComplexPoint f) (hp : projectivePoint f E n p ∈ (affineChart i).source) :
    letI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    schemeNativeFunctionFieldGerm f n p (polyFF f E i hi P) =
      algebraMap _ _ (polyGerm (isHolomorphicEmbedding_projectivePoint f E n) hp P) := by
  let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  have hx : schemeComplexPointImage f p ∈ coordOpen E i :=
    (projectivePoint_mem_source_iff f E n i p).mp hp
  rw [polyFF_eq_algebraMap f E i hi P hx]
  have h1 := schemeNativeFunctionFieldGerm_stalk f n p
    ((X.presheaf.germ (coordOpen E i) (schemeComplexPointImage f p) hx).hom (polyCoef E i P))
  have h2 := schemeNativeStalkGerm_polyCoef f E n i P p hx
  refine h1.trans ?_
  congr 1

omit [IsSeparated f] [QuasiCompact f] in
/-- **Frame transitions in `ℂ(X)`**: `P(x/x_l) = (xᵢ/x_l)^d P(x/xᵢ)` for `P` homogeneous of
degree `d`. -/
theorem polyFF_transition (i l : Fin (E.ambientDimension + 1))
    (hi : genericPoint X ∈ coordOpen E i) (hl : genericPoint X ∈ coordOpen E l)
    {P : MvPolynomial (Fin (E.ambientDimension + 1)) ℂ} {d : ℕ} (hP : P.IsHomogeneous d) :
    polyFF f E l hl P =
      (X.presheaf.germ (coordOpen E i ⊓ coordOpen E l) (genericPoint X) ⟨hi, hl⟩).hom
          (frameTr E i l) ^ d * polyFF f E i hi P := by
  have h := congrArg
    (X.presheaf.germ (coordOpen E i ⊓ coordOpen E l) (genericPoint X) ⟨hi, hl⟩).hom
    (polyCoef_transition E i l hP)
  rw [map_mul, map_pow] at h
  have hres : ∀ (U : X.Opens) (hU : coordOpen E i ⊓ coordOpen E l ≤ U)
      (s : X.presheaf.obj (op U)) (hgU : genericPoint X ∈ U),
      (X.presheaf.germ (coordOpen E i ⊓ coordOpen E l) (genericPoint X) ⟨hi, hl⟩).hom
          (X.presheaf.map (homOfLE hU).op s) =
        (X.presheaf.germ U (genericPoint X) hgU).hom s := by
    intro U hU s hgU
    exact TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE hU) (genericPoint X) ⟨hi, hl⟩ s
  have h1 := hres (coordOpen E l) inf_le_right (polyCoef E l P) hl
  have h2 := hres (coordOpen E i) inf_le_left (polyCoef E i P) hi
  change (X.presheaf.germ (coordOpen E i ⊓ coordOpen E l) (genericPoint X) ⟨hi, hl⟩).hom
      (X.presheaf.map (homOfLE (inf_le_right : coordOpen E i ⊓ coordOpen E l ≤ coordOpen E l)).op
        (polyCoef E l P)) = _ * (X.presheaf.germ (coordOpen E i ⊓ coordOpen E l) (genericPoint X)
          ⟨hi, hl⟩).hom (X.presheaf.map (homOfLE (inf_le_left :
            coordOpen E i ⊓ coordOpen E l ≤ coordOpen E i)).op (polyCoef E i P)) at h
  rw [h1, h2] at h
  exact h

/-- **The base model is rational**: the closed projective embedding `X(ℂ) → ℙᴺ` of `X` is a
rational embedding of the model `id : X(ℂ) → X(ℂ)`, with `q = P(x/xᵢ) / Q(x/xᵢ)`. -/
theorem isRationalEmbedding_projectivePoint
    (hid : IsAnalyticModification (n := n) (id : SchemeComplexPoint f → SchemeComplexPoint f)) :
    letI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    IsRationalEmbedding f hid (isHolomorphicEmbedding_projectivePoint f E n) := by
  let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  intro d P Q hP hQ hy
  obtain ⟨y₀, hy₀⟩ := hy
  set i₀ := chartIndex (projectivePoint f E n y₀)
  have hi₀ : projectivePoint f E n y₀ ∈ (affineChart i₀).source := mem_affineChart_chartIndex _
  have hx₀ : schemeComplexPointImage f y₀ ∈ coordOpen E i₀ :=
    (projectivePoint_mem_source_iff f E n i₀ y₀).mp hi₀
  have hg₀ : genericPoint X ∈ coordOpen E i₀ := genericPoint_mem_coordOpen f E hx₀
  have hQ0 : polyFF f E i₀ hg₀ Q ≠ 0 := by
    intro h0
    have h1 := congrArg (schemeNativeFunctionFieldGerm f n y₀) h0
    rw [map_zero, schemeNativeFunctionFieldGerm_polyFF f E i₀ hg₀ Q y₀ hi₀] at h1
    have h2 := IsFractionRing.injective (NativeHolGerm n (SchemeComplexPoint f) y₀)
      (FractionRing (NativeHolGerm n (SchemeComplexPoint f) y₀))
      (h1.trans (map_zero _).symm)
    exact (isUnit_polyGerm (isHolomorphicEmbedding_projectivePoint f E n) hi₀ hQ hy₀).ne_zero h2
  refine ⟨polyFF f E i₀ hg₀ P / polyFF f E i₀ hg₀ Q, ?_⟩
  intro y i hi
  have hx : schemeComplexPointImage f y ∈ coordOpen E i :=
    (projectivePoint_mem_source_iff f E n i y).mp hi
  have hg : genericPoint X ∈ coordOpen E i := genericPoint_mem_coordOpen f E hx
  rw [ratGerm_id, ← schemeNativeFunctionFieldGerm_polyFF f E i hg Q y hi,
    ← schemeNativeFunctionFieldGerm_polyFF f E i hg P y hi, ← map_mul]
  congr 1
  rw [div_mul_eq_mul_div, div_eq_iff hQ0, polyFF_transition f E i₀ i hg₀ hg hP,
    polyFF_transition f E i₀ i hg₀ hg hQ]
  ring

end Scheme

end SGPT.Okounkov.OF9
