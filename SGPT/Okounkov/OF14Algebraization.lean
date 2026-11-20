import SGPT.Okounkov.OF14Integral
import SGPT.Okounkov.OF14TowerRatios
import SGPT.Okounkov.OF13Final
import SGPT.GAGA.OkoCloseDXMain
import SGPT.Foundations.Analysis.Pending.BlowupConnected

/-!
# `rmk:Abhyankar` for smooth `X`: rational algebraizations of blow-up towers

Source: chapter *The theory of Okounkov bodies*, Section *Flags and valuations*, `rmk:Abhyankar`:
*if a valuation has value group identified with `ℤⁿ_lex` and maximal rational rank `n`, then
[CFKLRS17, Theorem 2.9] shows that it is equivalent to, but not necessarily equal to, a valuation
induced by an admissible flag on a modification of `X`.*  Appendix `def:modif`: a modification of a
compact complex space is a finite composition of blow-ups with smooth centres.

Lane OF13 reduced the existence statement, for `X` integral smooth projective, to rational
algebraizations of blow-up towers (`OF13.HasRationalAlgebraization`).  We prove them:

* `exists_ringEquiv_of_germs`: two families of field embeddings `α_v : K → F_v`, `β_v : L → F_v`
  (`β_v` injective) with the same images, *uniformly in `v`*, come from one isomorphism
  `e : K ≃ L` with `β_v ∘ e = α_v` for all `v`;
* `comap_polyGerm_of_comp_eq`: if `Ψ ∘ φ` is the projective embedding of `V`, the pull-back along
  `φ` of the germ of `P(Ψ)` is the germ of `P` on `V(ℂ)`;
* `polyGerm_ne_zero_of_eval_ne_zero`: on an integral `V ⊆ ℙᴺ`, a homogeneous `B` not vanishing at
  one complex point has a nonzero germ in every chart at every point (`B(x/xᵢ) ≠ 0` in `ℂ(V)`);
* `exists_ringEquiv_germ_of_comp_eq`: if the embedding `Ψ : Y → ℙᴺ` of a model `π : Y → X(ℂ)` is
  rational and generating (lanes OF9/OF14: `ℂ(X)` is exactly the field of ratios of `Ψ`) and
  `φ : V(ℂ) ≃ Y` identifies `Ψ` with the embedding of `V`, then `ℂ(X) ≃ ℂ(V)` compatibly with
  meromorphic germs;
* **`hasRationalAlgebraization_of_isBlowupSequence`**: every blow-up tower `π : Y → X(ℂ)` of an
  integral smooth projective complex scheme has a rational algebraization: `Y` is connected, its
  rational and generating embedding is cut out by equations (Chow), the model `V` is
  integral (`exists_integral_algebraization_of_chow`), and `ℂ(X) ≃ ℂ(V)`;
* **`exists_admissibleFlag_lexEquivalent`**: `rmk:Abhyankar` (existence, [CFKLRS17, Thm 2.9]) for
  `X` integral smooth projective, unconditionally: every valuation `ν : ℂ(X)^× → ℤⁿ_lex` with
  value group `ℤⁿ_lex` is `ν_{Y•} G` (`G = I + N`) for an admissible flag `Y•` on the algebraic
  model `V` of a blow-up tower `π : Y → X(ℂ)` (a modification of `X`, `def:modif`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.Okounkov.OF14

open CategoryTheory AlgebraicGeometry Set Filter SGPT.Foundations.Schemes
open SGPT.Okounkov SGPT.Okounkov.OF9 SGPT.Okounkov.OF5 SGPT.Okounkov.OF6 SGPT.Okounkov.ValCurr
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.GAGA.H0S SGPT.GAGA.ChowBl SGPT.NAPotential.FSPos
open scoped Topology Manifold ContDiff

/-! ### Isomorphisms of fields from germ embeddings -/

/-- **Fields with the same germs are isomorphic.** Let `α_v : K → F_v` and `β_v : L → F_v` be
ring maps from fields, indexed by a nonempty `v`, with every `β_v` injective. If every `q ∈ K` has
an `r ∈ L` with `β_v r = α_v q` for all `v`, and conversely, then there is a ring isomorphism
`e : K ≃ L` with `β_v ∘ e = α_v` for all `v`. -/
theorem exists_ringEquiv_of_germs {K L : Type*} [Field K] [Field L] {ι : Type*} [Nonempty ι]
    {F : ι → Type*} [∀ i, CommRing (F i)] (α : ∀ i, K →+* F i) (β : ∀ i, L →+* F i)
    (hβ : ∀ i, Function.Injective (β i)) (h₁ : ∀ q, ∃ r, ∀ i, β i r = α i q)
    (h₂ : ∀ r, ∃ q, ∀ i, β i r = α i q) :
    ∃ e : K ≃+* L, ∀ q i, β i (e q) = α i q := by
  classical
  choose F₁ hF₁ using h₁
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  let e₀ : K →+* L :=
    { toFun := F₁
      map_one' := hβ i₀ (by simp only [hF₁, map_one])
      map_mul' := fun a b => hβ i₀ (by simp only [hF₁, map_mul])
      map_zero' := hβ i₀ (by simp only [hF₁, map_zero])
      map_add' := fun a b => hβ i₀ (by simp only [hF₁, map_add]) }
  have hsurj : Function.Surjective e₀ := fun r => by
    obtain ⟨q, hq⟩ := h₂ r
    exact ⟨q, hβ i₀ ((hF₁ q i₀).trans (hq i₀).symm)⟩
  exact ⟨RingEquiv.ofBijective e₀ ⟨e₀.injective, hsurj⟩, fun q i => hF₁ q i⟩

local instance of14AlTopology {A : Scheme.{0}} (g : A ⟶ Spec (.of ℂ)) :
    TopologicalSpace (SchemeComplexPoint g) :=
  schemeAnalyticPointTopology g
local instance of14AlCharts {A : Scheme.{0}} (g : A ⟶ Spec (.of ℂ)) (n : ℕ)
    [SmoothOfRelativeDimension n g] : ChartedSpace (ComplexModel n) (SchemeComplexPoint g) :=
  schemeAnalyticTNChartedSpace g n
local instance of14AlManifold {A : Scheme.{0}} (g : A ⟶ Spec (.of ℂ)) (n : ℕ)
    [SmoothOfRelativeDimension n g] [IsSeparated g] [QuasiCompact g] :
    IsComplexManifold n (SchemeComplexPoint g) :=
  schemeAnalyticTN_isComplexManifold g n

/-! ### Polynomial germs on the algebraic model -/

section Model

variable {V : Scheme.{0}} [IsIntegral V] (g : V ⟶ Spec (.of ℂ)) {n : ℕ}
  [SmoothOfRelativeDimension n g] [IsSeparated g] [QuasiCompact g]
  (EV : ClosedProjectiveEmbedding g)

omit [IsIntegral V] in
/-- If `Ψ ∘ φ` is the projective embedding of `V`, then pulling back the germ of `P(Ψ)` along `φ`
gives the germ of `P` on `V(ℂ)` (in the same affine chart). -/
theorem comap_polyGerm_of_comp_eq [CompactSpace (SchemeComplexPoint g)] {Y : Type}
    [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
    [CompactSpace Y] (φ : SchemeComplexPoint g ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y)
    {Ψ : Y → ComplexProjectiveSpace EV.ambientDimension} (hΨ : IsHolomorphicEmbedding (n := n) Ψ)
    (hΨφ : ∀ v, Ψ (φ v) = projectivePoint g EV n v) (v : SchemeComplexPoint g)
    {i : Fin (EV.ambientDimension + 1)} (hi : Ψ (φ v) ∈ (affineChart i).source)
    (hi' : projectivePoint g EV n v ∈ (affineChart i).source)
    (P : MvPolynomial (Fin (EV.ambientDimension + 1)) ℂ) :
    NativeHolGerm.comap φ (OF13.isAnalyticModification_of_diffeomorph φ).1 v (polyGerm hΨ hi P) =
      polyGerm (isHolomorphicEmbedding_projectivePoint g EV n) hi' P := by
  apply Subtype.ext
  change ((genFun Ψ i P ∘ φ : SchemeComplexPoint g → ℂ) : Germ (𝓝 v) ℂ) =
    ((genFun (projectivePoint g EV n) i P : SchemeComplexPoint g → ℂ) : Germ (𝓝 v) ℂ)
  congr 1
  funext w
  simp only [Function.comp_apply, genFun, coneLift, hΨφ]

omit [IsIntegral V] in
/-- **Transport of a ratio relation along `φ`.** If `ρ^* q · B(Ψ) = A(Ψ)` at every point of `Y`
and `Ψ ∘ φ` is the embedding of `V`, then `(ρ ∘ φ)^* q · B = A` at every point of `V(ℂ)`. -/
theorem ratio_relation_transport [CompactSpace (SchemeComplexPoint g)] {X : Scheme.{0}}
    [IsIntegral X] (f : X ⟶ Spec (.of ℂ)) [SmoothOfRelativeDimension n f] [IsSeparated f]
    [QuasiCompact f] {Y : Type} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
    [IsComplexManifold n Y] [CompactSpace Y] {π : Y → SchemeComplexPoint f}
    (hπ : IsAnalyticModification (n := n) π)
    (φ : SchemeComplexPoint g ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y)
    {Ψ : Y → ComplexProjectiveSpace EV.ambientDimension} (hΨ : IsHolomorphicEmbedding (n := n) Ψ)
    (hΨφ : ∀ v, Ψ (φ v) = projectivePoint g EV n v) (q : X.functionField)
    {A B : MvPolynomial (Fin (EV.ambientDimension + 1)) ℂ}
    (hrel : ∀ (y : Y) (i : Fin (EV.ambientDimension + 1)) (hi : Ψ y ∈ (affineChart i).source),
      ratGerm f hπ y q * algebraMap _ (FractionRing (NativeHolGerm n Y y)) (polyGerm hΨ hi B) =
        algebraMap _ (FractionRing (NativeHolGerm n Y y)) (polyGerm hΨ hi A))
    (v : SchemeComplexPoint g) (i : Fin (EV.ambientDimension + 1))
    (hi' : projectivePoint g EV n v ∈ (affineChart i).source) :
    fracComap (OF13.isAnalyticModification_of_diffeomorph φ) v (ratGerm f hπ (φ v) q) *
        algebraMap _ (FractionRing (NativeHolGerm n (SchemeComplexPoint g) v))
          (polyGerm (isHolomorphicEmbedding_projectivePoint g EV n) hi' B) =
      algebraMap _ (FractionRing (NativeHolGerm n (SchemeComplexPoint g) v))
        (polyGerm (isHolomorphicEmbedding_projectivePoint g EV n) hi' A) := by
  have hi : Ψ (φ v) ∈ (affineChart i).source := by rw [hΨφ]; exact hi'
  have key := congrArg (fracComap (OF13.isAnalyticModification_of_diffeomorph φ) v)
    (hrel (φ v) i hi)
  rw [map_mul, fracComap_algebraMap, fracComap_algebraMap,
    comap_polyGerm_of_comp_eq g EV φ hΨ hΨφ v hi hi',
    comap_polyGerm_of_comp_eq g EV φ hΨ hΨφ v hi hi'] at key
  exact key

/-- **Nonvanishing germs.** On an integral `V ⊆ ℙᴺ`, a homogeneous polynomial `B` which does not
vanish at one complex point has a nonzero germ at every point of `V(ℂ)`, in every chart:
`B(x/xᵢ) ≠ 0` in `ℂ(V)` and the germ map of `ℂ(V)` is injective. -/
theorem polyGerm_ne_zero_of_eval_ne_zero [CompactSpace (SchemeComplexPoint g)] {d : ℕ}
    {B : MvPolynomial (Fin (EV.ambientDimension + 1)) ℂ} (hB : B.IsHomogeneous d)
    {v₁ : SchemeComplexPoint g} (hv₁ : MvPolynomial.eval (projectivePoint g EV n v₁).rep B ≠ 0)
    (v : SchemeComplexPoint g) {i : Fin (EV.ambientDimension + 1)}
    (hi : projectivePoint g EV n v ∈ (affineChart i).source) :
    algebraMap _ (FractionRing (NativeHolGerm n (SchemeComplexPoint g) v))
      (polyGerm (isHolomorphicEmbedding_projectivePoint g EV n) hi B) ≠ 0 := by
  set i₀ := chartIndex (projectivePoint g EV n v₁)
  have hi₀ : projectivePoint g EV n v₁ ∈ (affineChart i₀).source := mem_affineChart_chartIndex _
  have hg₀ : genericPoint V ∈ coordOpen EV i₀ :=
    genericPoint_mem_coordOpen g EV ((projectivePoint_mem_source_iff g EV n i₀ v₁).mp hi₀)
  have hg : genericPoint V ∈ coordOpen EV i :=
    genericPoint_mem_coordOpen g EV ((projectivePoint_mem_source_iff g EV n i v).mp hi)
  have hQ0 : polyFF g EV i₀ hg₀ B ≠ 0 := by
    intro h0
    have h1 := congrArg (schemeNativeFunctionFieldGerm g n v₁) h0
    rw [map_zero, schemeNativeFunctionFieldGerm_polyFF g EV i₀ hg₀ B v₁ hi₀] at h1
    have h2 := IsFractionRing.injective (NativeHolGerm n (SchemeComplexPoint g) v₁)
      (FractionRing (NativeHolGerm n (SchemeComplexPoint g) v₁))
      (h1.trans (map_zero _).symm)
    exact (isUnit_polyGerm (isHolomorphicEmbedding_projectivePoint g EV n) hi₀ hB hv₁).ne_zero h2
  have hQi : polyFF g EV i hg B ≠ 0 := by
    intro h0
    have hback := polyFF_transition g EV i i₀ hg hg₀ hB
    rw [h0, mul_zero] at hback
    exact hQ0 hback
  rw [← schemeNativeFunctionFieldGerm_polyFF g EV i hg B v hi]
  exact (map_ne_zero_iff _ (schemeNativeFunctionFieldGerm_injective g n v)).mpr hQi

/-- A rational function `r = A(x/x_l)/B(x/x_l)` of `V` has germ `A/B` at every point of `V(ℂ)`. -/
theorem schemeNativeFunctionFieldGerm_mul_polyGerm [CompactSpace (SchemeComplexPoint g)]
    {r : V.functionField} {A B : MvPolynomial (Fin (EV.ambientDimension + 1)) ℂ}
    (hr : ∀ (l : Fin (EV.ambientDimension + 1)) (hl : genericPoint V ∈ coordOpen EV l),
      r * polyFF g EV l hl B = polyFF g EV l hl A)
    (v : SchemeComplexPoint g) (i : Fin (EV.ambientDimension + 1))
    (hi : projectivePoint g EV n v ∈ (affineChart i).source) :
    schemeNativeFunctionFieldGerm g n v r *
        algebraMap _ (FractionRing (NativeHolGerm n (SchemeComplexPoint g) v))
          (polyGerm (isHolomorphicEmbedding_projectivePoint g EV n) hi B) =
      algebraMap _ (FractionRing (NativeHolGerm n (SchemeComplexPoint g) v))
        (polyGerm (isHolomorphicEmbedding_projectivePoint g EV n) hi A) := by
  have hg : genericPoint V ∈ coordOpen EV i :=
    genericPoint_mem_coordOpen g EV ((projectivePoint_mem_source_iff g EV n i v).mp hi)
  rw [← schemeNativeFunctionFieldGerm_polyFF g EV i hg B v hi,
    ← schemeNativeFunctionFieldGerm_polyFF g EV i hg A v hi, ← map_mul, hr i hg]

/-- **The function field of the model.** Let `π : Y → X(ℂ)` be a model of an integral smooth
projective `X` with a holomorphic embedding `Ψ : Y → ℙᴺ` which is rational (every ratio of `Ψ` is
the pull-back of a rational function of `X`) and generating (every rational function of `X` is a
ratio of `Ψ`), and let `φ : V(ℂ) ≃ Y` be a biholomorphism from an integral smooth projective
`V ⊆ ℙᴺ` with `Ψ ∘ φ` the embedding of `V`. Then `ℂ(X) ≃ ℂ(V)`, compatibly with meromorphic
germs: `e q` at `v` is the pull-back of `q` along `π ∘ φ`. -/
theorem exists_ringEquiv_germ_of_comp_eq {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ))
    [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f] {Y : Type}
    [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
    [CompactSpace Y] {π : Y → SchemeComplexPoint f} (hπ : IsAnalyticModification (n := n) π)
    (φ : SchemeComplexPoint g ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y)
    {Ψ : Y → ComplexProjectiveSpace EV.ambientDimension} (hΨ : IsHolomorphicEmbedding (n := n) Ψ)
    (hΨφ : ∀ v, Ψ (φ v) = projectivePoint g EV n v) (hR : IsRationalEmbedding f hπ hΨ)
    (hG : IsGeneratingEmbedding f hπ hΨ) :
    ∃ e : X.functionField ≃+* V.functionField, ∀ (q : X.functionField) (v : SchemeComplexPoint g),
      schemeNativeFunctionFieldGerm g n v (e q) =
        fracComap (OF13.isAnalyticModification_of_diffeomorph φ) v (ratGerm f hπ (φ v) q) := by
  let : CompactSpace (SchemeComplexPoint g) := EV.analyticCompact
  have hV := isHolomorphicEmbedding_projectivePoint g EV n
  have : Nonempty (SchemeComplexPoint g) := OF2.nonempty_schemeComplexPoint g EV
  set hφ := OF13.isAnalyticModification_of_diffeomorph φ
  -- two ratio relations with the same `A/B` force equality of germs
  have hcancel : ∀ (r : V.functionField) (q : X.functionField) (d : ℕ)
      (A B : MvPolynomial (Fin (EV.ambientDimension + 1)) ℂ), B.IsHomogeneous d →
      (∃ v₁, MvPolynomial.eval (projectivePoint g EV n v₁).rep B ≠ 0) →
      (∀ v i (hi : projectivePoint g EV n v ∈ (affineChart i).source),
        schemeNativeFunctionFieldGerm g n v r *
            algebraMap _ (FractionRing (NativeHolGerm n (SchemeComplexPoint g) v))
              (polyGerm hV hi B) =
          algebraMap _ (FractionRing (NativeHolGerm n (SchemeComplexPoint g) v))
            (polyGerm hV hi A)) →
      (∀ v i (hi : projectivePoint g EV n v ∈ (affineChart i).source),
        fracComap hφ v (ratGerm f hπ (φ v) q) *
            algebraMap _ (FractionRing (NativeHolGerm n (SchemeComplexPoint g) v))
              (polyGerm hV hi B) =
          algebraMap _ (FractionRing (NativeHolGerm n (SchemeComplexPoint g) v))
            (polyGerm hV hi A)) →
      ∀ v, schemeNativeFunctionFieldGerm g n v r = fracComap hφ v (ratGerm f hπ (φ v) q) := by
    rintro r q d A B hB ⟨v₁, hv₁⟩ h1 h2 v
    have hi : projectivePoint g EV n v ∈
        (affineChart (chartIndex (projectivePoint g EV n v))).source :=
      mem_affineChart_chartIndex _
    exact mul_right_cancel₀ (polyGerm_ne_zero_of_eval_ne_zero g EV hB hv₁ v hi)
      ((h1 v _ hi).trans (h2 v _ hi).symm)
  have hX : ∀ q : X.functionField, ∃ r : V.functionField, ∀ v,
      schemeNativeFunctionFieldGerm g n v r = fracComap hφ v (ratGerm f hπ (φ v) q) := by
    intro q
    obtain ⟨d, A, B, hA, hB, ⟨y₁, hy₁⟩, hrel⟩ := hG q
    have hv₁ : MvPolynomial.eval (projectivePoint g EV n (φ.symm y₁)).rep B ≠ 0 := by
      rw [← hΨφ, φ.apply_symm_apply]
      exact hy₁
    obtain ⟨r, hr⟩ := isRationalEmbedding_projectivePoint g EV isAnalyticModification_identity
      d A B hA hB ⟨_, hv₁⟩
    refine ⟨r, hcancel r q d A B hB ⟨_, hv₁⟩ (fun v i hi => ?_)
      (ratio_relation_transport g EV f hπ φ hΨ hΨφ q hrel)⟩
    rw [← ratGerm_id g isAnalyticModification_identity v r]
    exact hr v i hi
  have hVfield : ∀ r : V.functionField, ∃ q : X.functionField, ∀ v,
      schemeNativeFunctionFieldGerm g n v r = fracComap hφ v (ratGerm f hπ (φ v) q) := by
    intro r
    obtain ⟨d, A, B, hA, hB, hrel⟩ := OF13.exists_homogeneous_ratio g EV r
    obtain ⟨v₀⟩ := ‹Nonempty (SchemeComplexPoint g)›
    have hi₀ := mem_affineChart_chartIndex (projectivePoint g EV n v₀)
    have hg₀ := genericPoint_mem_coordOpen g EV
      ((projectivePoint_mem_source_iff g EV n _ v₀).mp hi₀)
    obtain ⟨v₁, hv₁⟩ : ∃ v₁, MvPolynomial.eval (projectivePoint g EV n v₁).rep B ≠ 0 := by
      refine exists_eval_ne_zero_of_polyGerm_ne_zero hV hi₀ hB fun h0 => (hrel _ hg₀).1 ?_
      apply schemeNativeFunctionFieldGerm_injective g n v₀
      rw [schemeNativeFunctionFieldGerm_polyFF g EV _ hg₀ B v₀ hi₀, h0, map_zero, map_zero]
    obtain ⟨q, hq⟩ := hR d A B hA hB ⟨φ v₁, by rw [hΨφ]; exact hv₁⟩
    exact ⟨q, hcancel r q d A B hB ⟨v₁, hv₁⟩
      (schemeNativeFunctionFieldGerm_mul_polyGerm g EV (fun l hl => (hrel l hl).2))
      (ratio_relation_transport g EV f hπ φ hΨ hΨφ q hq)⟩
  obtain ⟨e, he⟩ := exists_ringEquiv_of_germs
    (F := fun v : SchemeComplexPoint g => FractionRing (NativeHolGerm n (SchemeComplexPoint g) v))
    (fun v => (fracComap hφ v).comp (ratGerm f hπ (φ v)))
    (fun v => schemeNativeFunctionFieldGerm g n v)
    (fun v => schemeNativeFunctionFieldGerm_injective g n v) hX hVfield
  exact ⟨e, fun q v => he q v⟩

end Model

/-! ### Rational algebraizations of blow-up towers and the main theorem -/

section Tower

variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ)) {n : ℕ}
  [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f]

/-- **Blow-up towers are rationally algebraic.** Every finite sequence of blow-ups with smooth
centres `π : Y → X(ℂ)` of an integral smooth projective complex scheme `X` has a rational
algebraization: an integral smooth projective complex scheme `V`, a biholomorphism
`φ : V(ℂ) ≃ Y` and an isomorphism `e : ℂ(X) ≃ ℂ(V)` with `e q = (π ∘ φ)^* q` as meromorphic germs
at every point of `V(ℂ)`. -/
theorem hasRationalAlgebraization_of_isBlowupSequence (E : ClosedProjectiveEmbedding f)
    {Y : Type} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
    {π : Y → SchemeComplexPoint f} (hseq : IsBlowupSequence n (SchemeComplexPoint f) Y π) :
    OF13.HasRationalAlgebraization f n
      (HironakaChowLemma.isAnalyticModification_of_isBlowupSequence hseq) := by
  obtain ⟨hc, N, Ψ, hΨ, hRG⟩ := exists_isRationalEmbedding_and_isGeneratingEmbedding f E hseq
  have := hc
  obtain ⟨hR, hG⟩ := @hRG hc
  -- `Y` is connected
  have : Nonempty (SchemeComplexPoint f) := OF2.nonempty_schemeComplexPoint f E
  have : ConnectedSpace (SchemeComplexPoint f) :=
    SGPT.GAGA.OkoClose.connectedSpace_of_isIntegral f E n
  have : ConnectedSpace Y := BlowupConnected.connectedSpace_of_isBlowupSequence π hseq
  -- Chow's theorem and the integral algebraic model
  obtain ⟨m₀, hm⟩ := chow_image hΨ (isComplexAnalyticSubset_univ (n := n) (M := Y))
  obtain ⟨μ, hμ, P, hP, hgen, hzero⟩ := hm m₀ le_rfl
  rw [Set.image_univ] at hgen hzero
  obtain ⟨V, g, hsm, EV, hVint, hrest⟩ := exists_integral_algebraization_of_chow hΨ P hP hgen hzero
  let := hsm
  let := EV.isSeparated
  let := EV.quasiCompact
  obtain ⟨φ, hN, hcomp⟩ := hrest
  subst hN
  have hΨφ : ∀ v, Ψ (φ v) = projectivePoint g EV n v := fun v => eq_of_heq (hcomp v)
  obtain ⟨e, he⟩ := exists_ringEquiv_germ_of_comp_eq g EV f
    (HironakaChowLemma.isAnalyticModification_of_isBlowupSequence hseq) φ hΨ hΨφ hR hG
  exact ⟨V, hVint, g, hsm, EV, φ, e, he⟩

/-- **`rmk:Abhyankar`, existence ([CFKLRS17, Thm 2.9]) for smooth `X`.** Let `X` be an integral
smooth projective complex scheme of dimension `n`. Every valuation `ν : ℂ(X)^× → ℤⁿ_lex` with value
group `ℤⁿ_lex` is equivalent to the valuation of an admissible flag on a modification of `X`: there
are a finite sequence of blow-ups with smooth centres `π : Y → X(ℂ)` (a modification, `def:modif`),
its algebraic model `V` (an integral smooth projective complex scheme, `φ : V(ℂ) ≃ Y`, and
`e : ℂ(X) ≃ ℂ(V)` with `e q = (π ∘ φ)^* q`) and an admissible flag `Y•` on `V` with
`ν = ν_{Y•} G`, `G = I + N` unit upper triangular. -/
theorem exists_admissibleFlag_lexEquivalent (E : ClosedProjectiveEmbedding f)
    (ν : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ)))) (hν : Function.Surjective ν) :
    ∃ (Y : Type) (_ : TopologicalSpace Y) (_ : ChartedSpace (ComplexModel n) Y)
      (_ : IsComplexManifold n Y) (π : Y → SchemeComplexPoint f)
      (hseq : IsBlowupSequence n (SchemeComplexPoint f) Y π)
      (V : Scheme.{0}) (_ : IsIntegral V) (g : V ⟶ Spec (.of ℂ))
      (hsm : SmoothOfRelativeDimension n g) (EV : ClosedProjectiveEmbedding g),
      letI := hsm
      letI := EV.isSeparated
      letI := EV.quasiCompact
      ∃ (φ : SchemeComplexPoint g ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y)
        (e : X.functionField ≃+* V.functionField),
        (∀ (q : X.functionField) (v : SchemeComplexPoint g),
          schemeNativeFunctionFieldGerm g n v (e q) =
            fracComap (OF13.isAnalyticModification_of_diffeomorph φ) v
              (ratGerm f (HironakaChowLemma.isAnalyticModification_of_isBlowupSequence hseq)
                (φ v) q)) ∧
        ∃ (Yf : Fin (n + 1) → Set V) (hY : IsAdmissibleFlag g n Yf),
          ValuationsLexEquivalent ((admissibleFlagValuation hY).comap e.toRingHom) ν :=
  OF13.exists_admissibleFlag_lexEquivalent_of_hasRationalAlgebraization f n E
    (by
      intro Y _ _ _ π hseq
      exact hasRationalAlgebraization_of_isBlowupSequence f E hseq) ν hν

end Tower

end SGPT.Okounkov.OF14
