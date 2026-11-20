import SGPT.Checks.Comparison.BJCycleCore
import SGPT.Foundations.Envelope.Local.PLGaussVerticalCurveSurfaceSelectionComponent

/-!
# The cycle lower bound

Source: Kleiman's intersection theory (`[K] = Σ_E ord_E(K) [E]` for an effective Cartier divisor
on an integral scheme, nonnegativity against nef classes, the projection formula), used in
[BJ22, `equ:mixedMAPL`] for `thm:BJappseq` of `chapter_NApotential.tex` ([BJ22, Cor. 12.18]).
Blueprint: `claude-bj-cycle.tex`.

`cycleLowerBound n : CycleLowerBound n` proves the first hypothesis of
`bjAppSeq_of_cycleLowerBound`: on an integral projective `Y` of dimension
`≤ n + 1` over `ℂ`, for an effective Cartier divisor `E = V(K)`, a class `θ` on `Y₀` with `ρ^*θ`
nef on `E`, a codimension-one point `z` with a discrete valuation ring as local ring and an integral
closed subscheme `Z ⊆ Y₀` with generic point `ρ(z)`,

  `ord_z(K) · (θ|_Z)^n ≤ (𝒪(E) ⋅ (ρ^*θ)^n)_Y`.

Proof: the cut by the canonical section of `𝒪(E)` (`interFormQ_cut`) turns the right side into
`((ρ^*θ|_E)^n)_E`. If `z ∉ E`, then `ord_z(K) = 0` and the right side is `≥ 0` (nef positivity).
Otherwise `z` lifts to a maximal point `z'` of `E` (codimension one),
`ℓ(𝒪_{E,z'}) = ℓ(𝒪_{Y,z}/K_z) = ord_z(K)` (`length_stalk_subscheme`, `Ring.ord_eq_addVal`), and
the multiplicity bound `interFormQ_ge_length_mul` gives
`ord_z(K) · ((ρ^*θ)|_V)^n ≤ ((ρ^*θ|_E)^n)_E` for the reduced closure `V` of `z'`. Finally
`V → Y₀` factors through a surjection `g : V ⟶ Z` (closed immersions of reduced schemes), and
the projection formula `exists_interFormQ_pullback_eq_of_surjective` gives
`((ρ^*θ)|_V)^n = e · (θ|_Z)^n` with `e ≥ 1`, where `(θ|_Z)^n ≥ 0` since the left side is.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Order IsLocalRing
open Scheme.Modules
open scoped ENNReal

universe u

namespace SGPT.NAPotential.BJCycle

open SGPT.Foundations.Envelope SGPT.Foundations.Envelope.SeshadriAmplenessCriterion
open SGPT.NAPotential.BJIntersect SGPT.NAPotential.BJ SGPT.NAPotential.BJProj
open SGPT.NAPotential.BJHodge

attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory

/-! ### Auxiliary facts -/

/-- On an integral scheme, the generic point is not in the support of an invertible ideal
sheaf. -/
theorem genericPoint_not_mem_support_of_isInvertible {Y : Scheme.{u}} [IsIntegral Y]
    {K : Y.IdealSheafData} (hK : K.IsInvertible) : genericPoint Y ∉ K.support := by
  intro hmem
  obtain ⟨g, hg, hKg⟩ := hK.exists_mem_nonZeroDivisors_stalkIdeal_eq_span (genericPoint Y)
  have h := (Scheme.IdealSheafData.mem_support_iff_stalkIdeal_le_maximalIdeal (I := K)
    (x := genericPoint Y)).mp hmem
  rw [hKg] at h
  have hgm : g ∈ maximalIdeal (Y.presheaf.stalk (genericPoint Y)) :=
    h (Ideal.mem_span_singleton_self g)
  have hg0 : g ≠ 0 := nonZeroDivisors.ne_zero hg
  rw [mem_maximalIdeal, mem_nonunits_iff] at hgm
  exact hgm ((isUnit_iff_ne_zero (G₀ := Y.functionField)).mpr hg0)

/-- The order of an ideal of a discrete valuation ring is the length of the quotient. -/
theorem ordIdeal_eq_length {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (I : Ideal R) : ordIdeal I = ((Module.length R (R ⧸ I) : ℕ∞) : ℝ≥0∞) := by
  rw [ordIdeal_eq, ← Ring.ord_eq_addVal, Ring.ord, Ideal.span_singleton_generator]

/-- Intersection numbers along equal structure morphisms agree. -/
theorem interFormQ_congr {k : Type u} [Field k] {X : Scheme.{u}} [CompactSpace X] [X.IsSeparated]
    {p p' : X ⟶ Spec (.of k)} [IsProjective p] [IsProjective p'] (h : p = p') (d : ℕ)
    (hdim : topologicalKrullDim X ≤ d) (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    interFormQ p d hdim F = interFormQ p' d hdim F := by
  subst h
  rfl

private theorem isFiniteType_unit (Y : Scheme.{u}) : (unitObj Y).IsFiniteType :=
  let : (unitObj Y).IsFinitePresentation := isInvertible_unit.isFinitePresentation
  SheafOfModules.instIsFiniteTypeOfIsFinitePresentation (R := Y.ringCatSheaf) (unitObj Y)

end SGPT.NAPotential.BJCycle

namespace SGPT.NAPotential.BJ

open SGPT.Foundations.Envelope SGPT.Foundations.Envelope.SeshadriAmplenessCriterion
open SGPT.NAPotential.BJIntersect SGPT.NAPotential.BJProj SGPT.NAPotential.BJHodge
open SGPT.NAPotential.BJCycle

attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory

/-- **The cycle lower bound** (the hypothesis `CycleLowerBound n` of `bjAppSeq_of_cycleLowerBound`):
on an integral projective `Y` of dimension `≤ n + 1` over `ℂ` with `ρ : Y ⟶ Y₀`, an invertible ideal
sheaf `K`, a class `θ` of `Y₀` with `ρ^*θ` nef on `V(K)`, a point `z` of codimension one with a
discrete valuation ring as local ring and an integral closed subscheme `Z ⊆ Y₀` of dimension `≤ n`
with generic point `ρ(z)`: `ord_z(K) · (θ|_Z)^n ≤ (𝒪(K) ⋅ (ρ^*θ)^n)_Y`. -/
theorem cycleLowerBound (n : ℕ) : CycleLowerBound n := by
  intro Y Y₀ _ _ _ _ _ q _ q₀ _ ρ hρ hdim K hK θ hnef z _ hz Z _ _ _ ι _ _ hrange hdimZ
  have hE := cartierLine_isInvertible hK
  have hzero := zeroIdeal_cartierSection K hK
  have hgen : genericPoint Y ∉ K.support := genericPoint_not_mem_support_of_isInvertible hK
  have hσ : cartierSection K hK ≠ 0 :=
    ne_zero_of_not_mem_support _ hE _ (genericPoint Y) (by rw [hzero]; exact hgen)
  rw [interFormQ_cut n q hdim (cartierLine K) hE (cartierSection K hK) hσ, Multiset.map_replicate]
  set D := LineSectionZeroIdeal.zeroIdeal (cartierLine K) hE (cartierSection K hK) with hD
  let : CompactSpace D.subscheme := QuasiCompact.compactSpace_of_compactSpace D.subschemeι
  let : D.subscheme.IsSeparated := isSeparated_of_closed D.subschemeι
  let : IsProjective (D.subschemeι ≫ q) := isProjective_closed_comp D.subschemeι q
  have hdimD : topologicalKrullDim D.subscheme ≤ n :=
    sectionZero_dimension_drop n hdim (cartierLine K) hE (cartierSection K hK) hσ
  let : (unitObj D.subscheme).IsQuasicoherent := isInvertible_unit.isQuasicoherent
  let : (unitObj D.subscheme).IsFiniteType := isFiniteType_unit _
  have hst : ∀ x : Y, D.stalkIdeal x = K.stalkIdeal x := fun x => by rw [hzero]
  -- the pulled-back class is nef on `D`
  have hrangeD : Set.range D.subschemeι = (K.support : Set Y) := by
    rw [Scheme.IdealSheafData.range_subschemeι, hzero]
  have hnefD : picPullbackQ D.subschemeι (picPullbackQ ρ θ) ∈
      relNefCone (D.subschemeι ≫ q) Set.univ := by
    refine relNefCone_mono (D.subschemeι ≫ q) (fun x _ => ?_)
      (picPullbackQ_mem_relNefCone q D.subschemeι hnef)
    change D.subschemeι x ∈ (K.support : Set Y)
    rw [← hrangeD]
    exact ⟨x, rfl⟩
  by_cases hzK : z ∈ K.support
  · -- `z` lies on `D`
    obtain ⟨z', rfl⟩ : ∃ z' : D.subscheme, D.subschemeι z' = z := by
      rw [← Set.mem_range, hrangeD]
      exact hzK
    -- `z'` is a maximal point of `D`
    have hmax : ∀ y : D.subscheme, y ⤳ z' → y = z' := by
      intro y hy
      have hyK : D.subschemeι y ∈ K.support := by
        change D.subschemeι y ∈ (K.support : Set Y)
        rw [← hrangeD]
        exact ⟨y, rfl⟩
      exact D.subschemeι.isClosedEmbedding.injective
        (eq_of_specializes_of_coheight_eq_one hgen hz hyK (hy.map D.subschemeι.continuous))
    -- the multiplicity of `D` at `z'` is `ord_z(K)`
    have hKz : K.stalkIdeal (D.subschemeι z') ≠ ⊥ := by
      obtain ⟨g, hg, hKg⟩ := hK.exists_mem_nonZeroDivisors_stalkIdeal_eq_span (D.subschemeι z')
      rw [hKg, Ne, Ideal.span_singleton_eq_bot]
      exact nonZeroDivisors.ne_zero hg
    have hlen : stalkLength (unitObj D.subscheme) z' =
        Module.length (Y.presheaf.stalk (D.subschemeι z'))
          (Y.presheaf.stalk (D.subschemeι z') ⧸ K.stalkIdeal (D.subschemeι z')) := by
      rw [stalkLength_unit, length_stalk_subscheme D z', hst]
    have hord := ordIdeal_eq_length (K.stalkIdeal (D.subschemeι z'))
    have hfin : Module.length (Y.presheaf.stalk (D.subschemeι z'))
        (Y.presheaf.stalk (D.subschemeι z') ⧸ K.stalkIdeal (D.subschemeι z')) ≠ ⊤ := by
      intro htop
      apply ordIdeal_ne_top hKz
      rw [hord, htop]
      exact ENat.toENNReal_top
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hfin
    have hordm : (ordIdeal (K.stalkIdeal (D.subschemeι z'))).toReal = m := by
      rw [hord, ← hm]
      simp
    rw [hordm]
    -- the reduced closure `V` of `z'` and the factorization `g : V ⟶ Z`
    let g' : pointClosure z' ⟶ Y₀ := pointClosureι z' ≫ D.subschemeι ≫ ρ
    have hrg : Set.range g' ⊆ Set.range ι := by
      rintro _ ⟨v, rfl⟩
      rw [hrange]
      have hv : z' ⤳ pointClosureι z' v := by
        rw [specializes_iff_mem_closure, ← range_pointClosureι]
        exact ⟨v, rfl⟩
      exact specializes_iff_mem_closure.mp (hv.map (D.subschemeι ≫ ρ).continuous)
    have hker : ι.ker ≤ g'.ker := by
      rw [PLGaussVerticalCurveSurfaceSelectionComponent.reduced_source_kernel_eq_vanishingIdeal g']
      exact Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal.mp
        (Closeds.closure_le.mpr (hrg.trans ι.range_subset_ker_support))
    let g : pointClosure z' ⟶ Z := IsClosedImmersion.lift ι g' hker
    have hgfac : g ≫ ι = g' := IsClosedImmersion.lift_fac _ _ _
    have hmor : g ≫ ι ≫ q₀ = pointClosureι z' ≫ D.subschemeι ≫ q := by
      rw [← Category.assoc, hgfac, ← hρ]
      show (pointClosureι z' ≫ D.subschemeι ≫ ρ) ≫ q₀ = _
      simp only [Category.assoc]
    let : IsProjective (g ≫ ι ≫ q₀) := by rw [hmor]; infer_instance
    let : IsProper (ι ≫ q₀) :=
      (SGPT.Foundations.Envelope.ProjectiveFactorizationRingIso.of_isProjective (ι ≫ q₀)).isProper
    let : IsProper (g ≫ ι ≫ q₀) :=
      (SGPT.Foundations.Envelope.ProjectiveFactorizationRingIso.of_isProjective (g ≫ ι ≫ q₀)).isProper
    let : IsProper g := IsProper.of_comp g (ι ≫ q₀)
    have hgsurj : Function.Surjective g := by
      let v₀ : pointClosure z' := SGPT.Foundations.Envelope.SchemePointClosureIntegral.pointClosureLift z'
      have hv₀ : ι (g v₀) = ρ (D.subschemeι z') := by
        change (g ≫ ι) v₀ = ρ (D.subschemeι z')
        rw [hgfac]
        rfl
      have hclosed : IsClosed (Set.range g) := by
        rw [← Set.image_univ]
        exact g.isClosedMap _ isClosed_univ
      intro w
      have hw : ι w ∈ closure {ι (g v₀)} := by
        rw [hv₀, ← hrange]
        exact ⟨w, rfl⟩
      have hw' : w ∈ closure {g v₀} := by
        rw [ι.isClosedEmbedding.isInducing.closure_eq_preimage_closure_image, Set.image_singleton]
        exact hw
      exact closure_minimal (Set.singleton_subset_iff.mpr (Set.mem_range_self v₀)) hclosed hw'
    have hdimV : topologicalKrullDim (pointClosure z') ≤ n :=
      topologicalKrullDim_pointClosure_le_of_le hdimD z'
    obtain ⟨e, he, hproj⟩ := exists_interFormQ_pullback_eq_of_surjective (ι ≫ q₀) g n hdimZ hdimV
      hgsurj
    -- the multiplicity bound on `D`
    have hcore := interFormQ_ge_length_mul (D.subschemeι ≫ q) n hdimD z' hmax m
      (by rw [hlen, ← hm])
      (Multiset.replicate n (picPullbackQ D.subschemeι (picPullbackQ ρ θ)))
      (fun θ' hθ' => (Multiset.eq_of_mem_replicate hθ') ▸ hnefD) (Multiset.card_replicate _ _)
    rw [Multiset.map_replicate] at hcore
    -- the classes on `V`
    have hclass : picPullbackQ (pointClosureι z') (picPullbackQ D.subschemeι (picPullbackQ ρ θ)) =
        picPullbackQ g (picPullbackQ ι θ) := by
      rw [← picPullbackQ_comp, ← picPullbackQ_comp, ← picPullbackQ_comp, hgfac, Category.assoc]
    have hVZ := hproj (Multiset.replicate n (picPullbackQ ι θ))
    rw [Multiset.map_replicate, ← hclass,
      interFormQ_congr hmor n hdimV (unitObj (pointClosure z'))] at hVZ
    -- nonnegativity on `V`
    have hVnef : picPullbackQ (pointClosureι z') (picPullbackQ D.subschemeι (picPullbackQ ρ θ)) ∈
        relNefCone (pointClosureι z' ≫ D.subschemeι ≫ q) Set.univ := by
      have h := picPullbackQ_mem_relNefCone (D.subschemeι ≫ q) (pointClosureι z') hnefD
      rwa [Set.preimage_univ] at h
    let : (unitObj (pointClosure z')).IsQuasicoherent := isInvertible_unit.isQuasicoherent
    let : (unitObj (pointClosure z')).IsFiniteType := isFiniteType_unit _
    have hVnn := interFormQ_nonneg_of_mem_relNefCone (pointClosureι z' ≫ D.subschemeι ≫ q) n
      hdimV (unitObj (pointClosure z'))
      (Multiset.replicate n
        (picPullbackQ (pointClosureι z') (picPullbackQ D.subschemeι (picPullbackQ ρ θ))))
      (fun θ' hθ' => (Multiset.eq_of_mem_replicate hθ') ▸ hVnef)
    rw [hVZ] at hcore hVnn
    set cZ := interFormQ (ι ≫ q₀) n hdimZ (unitObj Z) (Multiset.replicate n (picPullbackQ ι θ))
    set cD := interFormQ (D.subschemeι ≫ q) n hdimD (unitObj D.subscheme)
      (Multiset.replicate n (picPullbackQ D.subschemeι (picPullbackQ ρ θ)))
    have he0 : (0 : ℚ) < e := by exact_mod_cast he
    have he1 : (1 : ℚ) ≤ e := by exact_mod_cast he
    have hcZ : 0 ≤ cZ := by
      by_contra hneg
      have : (e : ℚ) * cZ < 0 := mul_neg_of_pos_of_neg he0 (not_le.mp hneg)
      linarith
    have hm0 : (0 : ℚ) ≤ m := Nat.cast_nonneg m
    have hfinal : (m : ℚ) * cZ ≤ cD := by
      calc (m : ℚ) * cZ ≤ (m : ℚ) * ((e : ℚ) * cZ) := by
            apply mul_le_mul_of_nonneg_left _ hm0
            nlinarith
        _ ≤ cD := hcore
    exact_mod_cast hfinal
  · -- `z ∉ D`: the order vanishes
    have hKz : K.stalkIdeal z = ⊤ := by
      by_contra hne
      apply hzK
      rw [Scheme.IdealSheafData.mem_support_iff_stalkIdeal_le_maximalIdeal]
      exact le_maximalIdeal hne
    rw [hKz, ordIdeal_top, ENNReal.toReal_zero, zero_mul]
    have h := interFormQ_nonneg_of_mem_relNefCone (D.subschemeι ≫ q) n hdimD
      (unitObj D.subscheme)
      (Multiset.replicate n (picPullbackQ D.subschemeι (picPullbackQ ρ θ)))
      (fun θ' hθ' => (Multiset.eq_of_mem_replicate hθ') ▸ hnefD)
    exact_mod_cast h

end SGPT.NAPotential.BJ

namespace SGPT.NAPotential.BJCycle

open SGPT.NAPotential.BJ

/-- **`thm:BJappseq` modulo relatively ample vertical divisors** ([BJ22, Corollary 12.18]): with
the cycle lower bound proved (`cycleLowerBound`), `bjAppSeq_of_cycleLowerBound` gives the book's
statement for an integral projective `X` of dimension `n ≥ 1` as soon as `RelAmplePositive p n ω`
holds for every ample rational class `ω`. -/
theorem bjAppSeq_of_relAmplePositive {X : Scheme.{0}} {p : X ⟶ Spec (.of ℂ)} [IsProjective p]
    [IsIntegral X] (n : ℕ) (hXn : topologicalKrullDim X = n) (hn : 0 < n)
    (hamp : ∀ ω : NativePicard.RationalPicardSpace X,
      NativePicard.numericalClass p ω ∈ SGPT.Foundations.Envelope.NativeRealNumericalClasses.ampleCone p →
        RelAmplePositive p n ω) :
    AppSeq.BJAppSeqStatement.{u} p :=
  bjAppSeq_of_cycleLowerBound n hXn hn (cycleLowerBound n) hamp

end SGPT.NAPotential.BJCycle
