import SGPT.Okounkov.ValGenLeaves
import SGPT.Okounkov.AlgebraicValuationBodies
import SGPT.Okounkov.AlgebraicBodyBound
import SGPT.IGood.DXMainSections
import SGPT.AlmostSemigroup.BodyGeometry
import SGPT.AlmostSemigroup.OkounkovComparison

/-!
# One-dimensional leaves and section counts for an arbitrary valuation

Lane VAL-GEN, blueprint `claude-val-gen.tex`. Source: chapter *The theory of Okounkov bodies*,
Section *Algebraic partial Okounkov bodies* (`sec:PoB`), which fixes an **arbitrary** rank `n`
valuation `ν : ℂ(X)^× → ℤⁿ` and uses that it has one-dimensional leaves,
`#ν(V^×) = dim V` [LM09, Lemma 1.3].

## Setting

`X` an integral smooth projective complex scheme of dimension `n` (closed projective embedding
`E`), `v : ℂ(X) → ℤⁿ_lex ∪ {∞}` an arbitrary additive valuation, `c ∈ X` a point (in the source,
the centre of `v`), `L` a line bundle with atlas `a`. The value of `s ∈ H⁰(X, L^k)` is
`ν(s) = v(s / e^k)` (`SGPT.Okounkov.AlgebraicValuation.sectionValue`, `e` the frame of `a` at `c`).

## Main results

* `sectionToField`: the injective `ℂ`-linear map `H⁰(X, L^m) → ℂ(X)`, `s ↦ s/e^m`; it is
  multiplicative and sends `1 ∈ H⁰(X, L⁰)` to `1`, so the images `R_m` form a graded family of
  subspaces of `ℂ(X)` with `dim R_m = h⁰(X, L^m)` and value sets `Γ(L)_m`.
* **`card_vectorSet_eq_finrank`** (one-dimensional leaves, `[LM09, Lemma 1.3]`): if
  `Γ(L) ∈ 𝒮'(C)` for the valuation `v` (`Γ(L)` lies in an admissible cone `C` and generates
  `ℤⁿ⁺¹`; the conclusion of `prop:Okounbiglbdl` for `v`) and `X` carries a smooth flag (only used
  for the growth bound `h⁰(X, L^m) = O(mⁿ)`), then for every `k` and every subspace
  `V ⊆ H⁰(X, L^k)`, `#{ν(s) : s ∈ V \ {0}} = dim V`. No hypothesis on `v` beyond being a
  valuation: the rank of the value group is recovered from the generation of `ℤⁿ⁺¹` by `Γ(L)`
  (`SGPT.Okounkov.ValGen.exists_leaf_cancel`).
* `card_slice_multiplierSectionSet`: hence `#Γ_k(θ, φ) = h⁰(X, L^k ⊗ 𝓘(kφ))` for the valuation
  `v`, and `#Γ(L)_k = h⁰(X, L^k)`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.Okounkov.ValGen

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set Filter Opposite TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Okounkov.AlgebraicValuation SGPT.LineBundle SGPT.AlmostSemigroup
open scoped Topology

/-! ### Sections as elements of the function field -/

section Field

variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ)) (c : X)
  {L : X.Modules} (a : LineBundleAtlas L)

/-- `s ↦ s / e^m ∈ ℂ(X)`, `e` the frame of the atlas `a` at `c`, as a `ℂ`-linear map. -/
def sectionToField (m : ℕ) :
    letI := schemeFunctionFieldAlgebra f
    SectionSpace f L m →ₗ[ℂ] X.functionField :=
  globalSectionToFunctionFieldOverBase f ((a.frame (a.centerIndex c)).tensorPower m)

theorem sectionToField_apply (m : ℕ) (s : SectionSpace f L m) :
    sectionToField f c a m s =
      globalSectionToFunctionField ((a.frame (a.centerIndex c)).tensorPower m) s := rfl

theorem sectionToField_injective (m : ℕ) : Function.Injective (sectionToField f c a m) :=
  globalSectionToFunctionField_injective (a.tensorPower m) _

/-- The values of sections are the valuations of their images. -/
theorem valuation_sectionToField {n : ℕ}
    (v : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ)))) (m : ℕ)
    (s : SectionSpace f L m) : v (sectionToField f c a m s) = sectionValue v c a m s := rfl

/-- Products of sections multiply their images. -/
theorem sectionToField_mul (m k : ℕ) (s : SectionSpace f L m) (t : SectionSpace f L k) :
    sectionToField f c a (m + k) (atlasPowerGlobalMul a m k s t) =
      sectionToField f c a m s * sectionToField f c a k t := by
  change X.germToFunctionField (a.opens (a.centerIndex c))
      (atlasPowerGlobalCoefficients a (m + k) (a.centerIndex c) (atlasPowerGlobalMul a m k s t)) =
    X.germToFunctionField (a.opens (a.centerIndex c))
      (atlasPowerGlobalCoefficients a m (a.centerIndex c) s) *
    X.germToFunctionField (a.opens (a.centerIndex c))
      (atlasPowerGlobalCoefficients a k (a.centerIndex c) t)
  rw [atlasPowerGlobalMul_coefficients, map_mul]

/-- The unit section is sent to `1`. -/
theorem sectionToField_one :
    sectionToField f c a 0 (bundlePowerGlobalOne L) = 1 := by
  change X.germToFunctionField (a.opens (a.centerIndex c))
      (atlasPowerGlobalCoefficients a 0 (a.centerIndex c) (bundlePowerGlobalOne L)) = 1
  rw [atlasPowerGlobalCoefficients_one, map_one]

/-- The graded family `R_m = {s / e^m : s ∈ H⁰(X, L^m)} ⊆ ℂ(X)`. -/
def sectionRange (m : ℕ) :
    letI := schemeFunctionFieldAlgebra f
    Submodule ℂ X.functionField :=
  letI := schemeFunctionFieldAlgebra f
  LinearMap.range (sectionToField f c a m)

theorem one_mem_sectionRange :
    letI := schemeFunctionFieldAlgebra f
    (1 : X.functionField) ∈ sectionRange f c a 0 :=
  ⟨bundlePowerGlobalOne L, sectionToField_one f c a⟩

theorem mul_mem_sectionRange {m k : ℕ} {x y : X.functionField}
    (hx : letI := schemeFunctionFieldAlgebra f; x ∈ sectionRange f c a m)
    (hy : letI := schemeFunctionFieldAlgebra f; y ∈ sectionRange f c a k) :
    letI := schemeFunctionFieldAlgebra f
    x * y ∈ sectionRange f c a (m + k) := by
  obtain ⟨s, rfl⟩ := hx
  obtain ⟨t, rfl⟩ := hy
  exact ⟨atlasPowerGlobalMul a m k s t, sectionToField_mul f c a m k s t⟩

variable {n : ℕ} (v : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ))))

/-- The vectors `ν(s) ∈ ℤⁿ` of the nonzero sections of a subspace `V ⊆ H⁰(X, L^k)`. -/
def vectorSet (k : ℕ) (V : Submodule ℂ (SectionSpace f L k)) : Set (Fin n → ℤ) :=
  {x | ∃ (s : SectionSpace f L k) (hs : s ≠ 0), s ∈ V ∧ sectionVector v c a k s hs = x}

/-- The value set of the image of `V` is the set of vectors of `V`. -/
theorem card_valueSet_map_eq (k : ℕ) (V : Submodule ℂ (SectionSpace f L k)) :
    letI := schemeFunctionFieldAlgebra f
    Nat.card (valueSet v (V.map (sectionToField f c a k)).subtype) =
      Nat.card (vectorSet f c a v k V) := by
  let := schemeFunctionFieldAlgebra f
  let ι : (Fin n → ℤ) → WithTop (Lex (Fin n → ℤ)) := fun x => ((toLex x : Lex (Fin n → ℤ)) :
    WithTop (Lex (Fin n → ℤ)))
  have hι : Function.Injective ι := fun x y h => toLex.injective (WithTop.coe_injective h)
  have himage : ι '' vectorSet f c a v k V =
      valueSet v (V.map (sectionToField f c a k)).subtype := by
    ext w
    constructor
    · rintro ⟨x, ⟨s, hs, hsV, rfl⟩, rfl⟩
      refine ⟨⟨sectionToField f c a k s, s, hsV, rfl⟩, ?_, ?_⟩
      · intro h
        apply hs
        apply sectionToField_injective f c a k
        rw [map_zero]
        exact congrArg Subtype.val h
      · change v (sectionToField f c a k s) = _
        rw [valuation_sectionToField, sectionValue_eq_vector c a k s hs]
    · rintro ⟨⟨y, s, hsV, rfl⟩, hy, rfl⟩
      have hs : s ≠ 0 := by
        rintro rfl
        apply hy
        apply Subtype.ext
        simp
      refine ⟨sectionVector v c a k s hs, ⟨s, hs, hsV, rfl⟩, ?_⟩
      change _ = v (sectionToField f c a k s)
      rw [valuation_sectionToField, sectionValue_eq_vector c a k s hs]
  rw [← himage, Nat.card_image_of_injective hι]

/-- The degree-`k` slice of `Γ(L)` is the vector set of `H⁰(X, L^k)`. -/
theorem slice_sectionSemigroup_eq (k : ℕ) :
    slice (sectionSemigroup v c a : Set ((Fin n → ℤ) × ℤ)) (k : ℤ) = vectorSet f c a v k ⊤ := by
  ext x
  constructor
  · rintro ⟨k', s, hs, hz⟩
    have hk : k' = k := by
      have h2 := congrArg Prod.snd hz
      simp only at h2
      exact_mod_cast h2.symm
    subst hk
    exact ⟨s, hs, Submodule.mem_top, (congrArg Prod.fst hz).symm⟩
  · rintro ⟨s, hs, -, rfl⟩
    exact ⟨k, s, hs, rfl⟩

end Field

/-! ### Growth bounds and one-dimensional leaves -/

section Leaves

variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] (E : ClosedProjectiveEmbedding f)

local instance valGenTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance valGenCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance valGenManifold [IsSeparated f] [QuasiCompact f] :
    IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n

variable (Y : Fin (n + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y)
  {L : X.Modules} (a : LineBundleAtlas L)

include E Y hY a in
/-- **`h⁰(X, L^m) = O(mⁿ)`** on `X` carrying a smooth flag `Y•`: the flag valuation has
one-dimensional leaves and its values on `H⁰(X, L^m)` lie in `[0, C m]ⁿ`. -/
theorem exists_h0_le_pow : ∃ B : ℝ, ∀ m : ℕ, 1 ≤ m → (h0 f L m : ℝ) ≤ B * (m : ℝ) ^ n := by
  obtain ⟨C, hC0, hC⟩ := exists_schemeFubiniStudySectionVector_le f n E Y hY a
  refine ⟨(C + 1) ^ n, fun m hm => ?_⟩
  have hcard := SGPT.IGood.DXMain.card_sectionValues_eq_finrank f n E Y hY a m ⊤
  rw [finrank_top] at hcard
  set N : ℕ := ⌊C * m⌋₊ with hN
  have hle : Nat.card (SGPT.IGood.DXMain.sectionValues f n E Y hY a m ⊤) ≤ (N + 1) ^ n := by
    let g : SGPT.IGood.DXMain.sectionValues f n E Y hY a m ⊤ → (Fin n → Fin (N + 1)) :=
      fun w i => ⟨w.1 i, by
        obtain ⟨s, hs, -, hw⟩ := w.2
        have h := hC m s hs i
        rw [← hw]
        have : (schemeFubiniStudySectionVector f n E Y hY a m s hs i : ℝ) ≤ C * m := h
        have h2 : schemeFubiniStudySectionVector f n E Y hY a m s hs i ≤ N :=
          Nat.le_floor this
        omega⟩
    have hg : Function.Injective g := by
      intro w w' h
      apply Subtype.ext
      funext i
      have := congrFun h i
      simp only [g, Fin.mk.injEq] at this
      exact this
    have := Nat.card_le_card_of_injective g hg
    simpa [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin] using this
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hNR : (N : ℝ) ≤ C * m := Nat.floor_le (by positivity)
  have h1 : ((N + 1 : ℕ) : ℝ) ≤ (C + 1) * m := by push_cast; nlinarith
  calc (h0 f L m : ℝ) = (Nat.card (SGPT.IGood.DXMain.sectionValues f n E Y hY a m ⊤) : ℝ) := by
        rw [hcard]; rfl
    _ ≤ (((N + 1) ^ n : ℕ) : ℝ) := by exact_mod_cast hle
    _ = ((N + 1 : ℕ) : ℝ) ^ n := by push_cast; ring
    _ ≤ ((C + 1) * m) ^ n := by gcongr
    _ = (C + 1) ^ n * (m : ℝ) ^ n := mul_pow _ _ _

variable {n} (c : X) (v : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ))))

omit [SmoothOfRelativeDimension n f] in
/-- The hypothesis `Γ(L) ∈ 𝒮'(C)` for the valuation `v` gives `#Γ(L)_M ≥ c₀ Mⁿ` for large `M`. -/
theorem exists_card_slice_ge {C : AdmissibleCone n}
    (hS : sectionSemigroup v c a ≤ latticePoints C.cone)
    (hG : LatticeSlices.generatedGroup (sectionSemigroup v c a) = ⊤) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ᶠ M : ℕ in atTop,
      c₀ * (M : ℝ) ^ n ≤ Nat.card (vectorSet f c a v M ⊤) := by
  have ht := Okounkov.tendsto_source_of_generatedGroup_eq_top C _ hS hG
  have hpos := BodyGeometry.volume_source_pos C _ hS hG
  rw [BodyGeometry.volume_source_eq_body C _ hS hG] at hpos
  refine ⟨MeasureTheory.volume.real (Okounkov.body (sectionSemigroup v c a)) / 2,
    half_pos hpos, ?_⟩
  filter_upwards [(tendsto_order.mp ht).1 _ (half_lt_self hpos), eventually_ge_atTop 1]
    with M hM hM1
  rw [ConeSubset.normalizedCardinality, Okounkov.card_sourceSubset_slices,
    slice_sectionSemigroup_eq] at hM
  have hMpos : (0 : ℝ) < (M : ℝ) ^ n := by
    have : (0 : ℝ) < M := by exact_mod_cast hM1
    positivity
  rw [inv_pow] at hM
  rw [← div_eq_inv_mul, lt_div_iff₀ hMpos] at hM
  exact hM.le

include E Y hY in
/-- **One-dimensional leaves for an arbitrary valuation** (`[LM09, Lemma 1.3]`): if `Γ(L)` lies
in an admissible cone and generates `ℤⁿ⁺¹` for the valuation `v` (source `prop:Okounbiglbdl`) and
`X` carries a smooth flag, then for every subspace `V ⊆ H⁰(X, L^k)`,
`#{ν(s) : s ∈ V \ {0}} = dim V`. -/
theorem card_vectorSet_eq_finrank {C : AdmissibleCone n}
    (hS : sectionSemigroup v c a ≤ latticePoints C.cone)
    (hG : LatticeSlices.generatedGroup (sectionSemigroup v c a) = ⊤)
    (k : ℕ) (V : Submodule ℂ (SectionSpace f L k)) :
    Nat.card (vectorSet f c a v k V) = Module.finrank ℂ V := by
  let := schemeFunctionFieldAlgebra f
  obtain ⟨B, hB⟩ := exists_h0_le_pow f n E Y hY a
  obtain ⟨c₀, hc₀, hlow⟩ := exists_card_slice_ge f a c v hS hG
  have hfinS : ∀ m, FiniteDimensional ℂ (SectionSpace f L m) :=
    fun m => SectionSpace.finiteDimensional f E a m
  have hfin : ∀ m, FiniteDimensional ℂ (sectionRange f c a m) := by
    intro m
    have := hfinS m
    exact LinearMap.finiteDimensional_range _
  have hrank : ∀ m, Module.finrank ℂ (sectionRange f c a m) = h0 f L m := by
    intro m
    have := hfinS m
    exact LinearMap.finrank_range_of_inj (sectionToField_injective f c a m)
  have hlow' : ∀ᶠ M : ℕ in atTop,
      c₀ * (M : ℝ) ^ n ≤ Nat.card (valueSet v (sectionRange f c a M).subtype) := by
    filter_upwards [hlow] with M hM
    have h := card_valueSet_map_eq f c a v M ⊤
    rw [Submodule.map_top] at h
    change c₀ * (M : ℝ) ^ n ≤ (Nat.card (valueSet v (sectionRange f c a M).subtype) : ℝ)
    rw [show sectionRange f c a M = LinearMap.range (sectionToField f c a M) from rfl, h]
    exact hM
  have hup : ∀ᶠ m : ℕ in atTop,
      (Module.finrank ℂ (sectionRange f c a m) : ℝ) ≤ B * (m : ℝ) ^ n := by
    filter_upwards [eventually_ge_atTop 1] with m hm
    rw [hrank]
    exact hB m hm
  have hV : V.map (sectionToField f c a k) ≤ sectionRange f c a k :=
    LinearMap.map_le_range
  have h := card_valueSet_eq_finrank_of_growth hfin (one_mem_sectionRange f c a)
    (fun hx hy => mul_mem_sectionRange f c a hx hy) hc₀ hlow' hup _ hV
  rw [card_valueSet_map_eq] at h
  rw [h]
  have := hfinS k
  exact LinearEquiv.finrank_eq
    (Submodule.equivMapOfInjective _ (sectionToField_injective f c a k) V).symm

end Leaves

/-! ### The partial Okounkov body of an arbitrary valuation -/

section PartialBody

open SGPT.AlmostSemigroup.Class SGPT.AlmostSemigroup.OkounkovExtension
open SGPT.AlmostSemigroup.Okounkov SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves

variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] (E : ClosedProjectiveEmbedding f)

local instance valGenPBTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance valGenPBCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n

variable (v : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ)))) (c : X)
  {L : X.Modules} (a : LineBundleAtlas L)

open Classical in
/-- The Okounkov body `Δ(S)` of a lattice subset `S` of the admissible cone `C` which is an
almost semigroup there (value of the continuous extension of source `thm:Okocont`), and the junk
value `∅` otherwise. -/
def setBody {n : ℕ} (C : AdmissibleCone n) (S : Set ((Fin n → ℤ) × ℤ)) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  if h : ∃ hsub : S ⊆ (latticePoints C.cone : Set _), (⟨S, hsub⟩ : ConeSubset C) ∈
      almostSemigroupLocus C then
    (bodyExtension (⟨⟨S, h.1⟩, h.2⟩ : AlmostSpace C) : Set (EuclideanSpace ℝ (Fin n)))
  else ∅

theorem setBody_eq {n : ℕ} {C : AdmissibleCone n} {S : Set ((Fin n → ℤ) × ℤ)}
    (hsub : S ⊆ (latticePoints C.cone : Set _))
    (hΓ : (⟨S, hsub⟩ : ConeSubset C) ∈ almostSemigroupLocus C) :
    setBody C S = (bodyExtension (⟨⟨S, hsub⟩, hΓ⟩ : AlmostSpace C) :
      Set (EuclideanSpace ℝ (Fin n))) := by
  unfold setBody
  rw [dif_pos ⟨hsub, hΓ⟩]

/-- **Source `def:Okounkov:L687` for an arbitrary valuation `ν = v`**, relative to an admissible
ambient cone `C` (the source takes `C = C(Δ_ν(L))`): when `Γ(θ, φ)` lies in `C` and is an almost
semigroup there (source `thm:Gammaasg`), `Δ_ν(θ, φ) = Δ(Γ(θ, φ))` is the value of the continuous
extension of the Okounkov body map (source `thm:Okocont`); otherwise the junk value `∅`. -/
def partialBody (C : AdmissibleCone n) (φ : SchemeComplexPoint f → EReal) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  setBody C (AlgebraicValuation.multiplierSectionSet f n E v c a φ)

variable {f n E v c}

/-- The value of the partial body on an almost semigroup. -/
theorem partialBody_eq {C : AdmissibleCone n} (φ : SchemeComplexPoint f → EReal)
    (hsub : AlgebraicValuation.multiplierSectionSet f n E v c a φ ⊆ (latticePoints C.cone : Set _))
    (hΓ : (⟨_, hsub⟩ : ConeSubset C) ∈ almostSemigroupLocus C) :
    partialBody f n E v c a C φ =
      (bodyExtension (⟨⟨_, hsub⟩, hΓ⟩ : AlmostSpace C) : Set (EuclideanSpace ℝ (Fin n))) :=
  setBody_eq hsub hΓ

/-- `vol Δ_ν(θ, φ) = vol Γ(θ, φ)` on almost semigroups (source `eq:volWfinal`). -/
theorem volume_partialBody {C : AdmissibleCone n} (φ : SchemeComplexPoint f → EReal)
    (hsub : AlgebraicValuation.multiplierSectionSet f n E v c a φ ⊆ (latticePoints C.cone : Set _))
    (hΓ : (⟨_, hsub⟩ : ConeSubset C) ∈ almostSemigroupLocus C) :
    MeasureTheory.volume.real (partialBody f n E v c a C φ) =
      ConeSubset.volume (⟨_, hsub⟩ : ConeSubset C) := by
  rw [partialBody_eq a φ hsub hΓ, volume_bodyExtension]

/-- **Source `prop:IcompimplyDeltacomp` for an arbitrary valuation, on almost semigroups**: if
`𝓘(kφ) ⊆ 𝓘(kψ)` for all `k ≥ 1` (e.g. `φ ⪯_𝓘 ψ`) and both `Γ(θ, φ)`, `Γ(θ, ψ)` are almost
semigroups in `C`, then `Δ_ν(θ, φ) ⊆ Δ_ν(θ, ψ)` (via source `cor:Okocomp`). -/
theorem partialBody_mono {C : AdmissibleCone n} {φ ψ : SchemeComplexPoint f → EReal}
    (hI : ∀ k : ℕ, 0 < k → (multiplierIdeal (n := n) (k : ℝ) φ).Le
      (multiplierIdeal (n := n) (k : ℝ) ψ))
    (hφ : ∃ hsub : AlgebraicValuation.multiplierSectionSet f n E v c a φ ⊆
      (latticePoints C.cone : Set _), (⟨_, hsub⟩ : ConeSubset C) ∈ almostSemigroupLocus C)
    (hψ : ∃ hsub : AlgebraicValuation.multiplierSectionSet f n E v c a ψ ⊆
      (latticePoints C.cone : Set _), (⟨_, hsub⟩ : ConeSubset C) ∈ almostSemigroupLocus C) :
    partialBody f n E v c a C φ ⊆ partialBody f n E v c a C ψ := by
  obtain ⟨hsφ, hφ⟩ := hφ
  obtain ⟨hsψ, hψ⟩ := hψ
  rw [partialBody_eq a φ hsφ hφ, partialBody_eq a ψ hsψ hψ]
  apply SGPT.AlmostSemigroup.OkounkovComparison.bodyExtension_mono
  apply AlgebraicValuation.sectionValueSet_mono c a
  rintro k s (hk | hs)
  · exact Or.inl hk
  · rcases Nat.eq_zero_or_pos k with hk | hk
    · exact Or.inl hk
    · exact Or.inr fun U α p hp => hI k hk p _ (hs U α p hp)

/-- **`Δ_ν(θ, φ) ⊆ Δ_ν(L)`** (after source `prop:IcompimplyDeltacomp`) for an arbitrary valuation:
if `Γ(L) ∈ 𝒮'(C)` and `Γ(θ, φ)` is an almost semigroup in `C`, then `Δ_ν(θ, φ)` lies in the
Euclidean copy of `Δ_ν(L) = Δ(Γ(L))`. -/
theorem partialBody_subset_okounkovBody {C : AdmissibleCone n} {φ : SchemeComplexPoint f → EReal}
    (hS : sectionSemigroup v c a ≤ latticePoints C.cone)
    (hG : LatticeSlices.generatedGroup (sectionSemigroup v c a) = ⊤)
    (hφ : ∃ hsub : AlgebraicValuation.multiplierSectionSet f n E v c a φ ⊆
      (latticePoints C.cone : Set _), (⟨_, hsub⟩ : ConeSubset C) ∈ almostSemigroupLocus C) :
    partialBody f n E v c a C φ ⊆
      (EuclideanSpace.equiv (Fin n) ℝ).symm '' okounkovBody v c a := by
  obtain ⟨hsφ, hφ⟩ := hφ
  rw [partialBody_eq a φ hsφ hφ]
  have hfull : sourceSubset C _ hS ∈ fullSemigroupLocus C :=
    sourceSubset_mem_fullSemigroupLocus C _ hS hG
  let T : FullSemigroup C := ⟨_, hfull⟩
  have h := SGPT.AlmostSemigroup.OkounkovComparison.bodyExtension_mono
    (⟨⟨_, hsφ⟩, hφ⟩ : AlmostSpace C) (fullToAlmost T)
    (fun z hz => AlgebraicValuation.multiplierSectionSet_subset (f := f) (n := n) (E := E) a φ hz)
  rw [bodyExtension_source] at h
  exact h

end PartialBody

end SGPT.Okounkov.ValGen
