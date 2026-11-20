import SGPT.GAGA.H0LOkounkov
import SGPT.GAGA.OkoCloseBig
import SGPT.Okounkov.ValGenBook
import SGPT.AlmostSemigroup.BrunnMinkowski
import SGPT.NPP.DimensionZero
import SGPT.NAPotential.NANSNonTrivRest
import SGPT.Trace.RestVolPoint
import SGPT.Foundations.Analysis.Pending.ZeroDimensionalQuasiPshMultiplierIdeals

/-!
# Algebraic partial Okounkov bodies in dimension zero: the basic computations


Section *Algebraic partial Okounkov bodies* (`sec:PoB`) of the chapter *The theory of Okounkov
bodies* works on a connected smooth complex projective variety `X` of dimension `n`; the case
`n = 0` is not excluded. The existing Lean statements of the section are written for `X` of
relative dimension `m + 1`. The section-level objects themselves (`sectionValueSet`,
`multiplierSectionSet`, `inftySectionSet`, `schemeProjectiveSectionSemigroup`,
`lineBundleOkounkovBody`, `multiplierDegreePolytope`, `twistedDegreePolytope`,
`partialOkounkovBody`, the almost-semigroup library) are defined for every relative dimension
`n`. This file computes all of them for `n = 0`.

In dimension `0` (with the smooth flag `Y₀ = X` of the setting, which makes `X(ℂ)` connected):

* `X(ℂ)` is one point (`subsingleton_complexPoint`, `nonempty_complexPoint`) and so is the
  scheme `X` (`subsingleton_scheme`: every point of `X` specializes to the image of the complex
  point and is a specialization of it, by the Nullstellensatz);
* every line bundle has a nowhere vanishing global frame, so `H⁰(X, Lᵏ) ≠ 0` for every `k`
  (`exists_section_ne_zero`) and `h⁰(X, Lᵏ) = 1` (`h0_eq_one`), `vol L = 1` (`volume_eq_one`);
* for every quasi-psh `φ`, `𝓘(kφ) = 𝓘_∞(kφ) = 𝒪_X` (`isMultiplierSection_of_dim_zero`,
  `isInftySection_of_dim_zero`), so `Γ(θ, φ) = Γ^∞(θ, φ) = Γ(L) = {(0, k) : k ∈ ℕ}`
  (`multiplierSectionSet_eq`, `inftySectionSet_eq`, `coe_schemeProjectiveSectionSemigroup`);
* this semigroup (`nonnegHeight`) is a full semigroup of volume `1` in every admissible cone
  containing `(0, 1)` (`sourceSubset_nonnegHeight_mem_fullSemigroupLocus`,
  `volume_sourceSubset_nonnegHeight`), and every Okounkov-type body is the whole space
  `ℝ⁰ = {0}` (`partialOkounkovBody_eq_univ`, `lineBundleOkounkovBody_eq_univ`,
  `multiplierDegreePolytope_eq_univ`, `twistedDegreePolytope_eq_univ`, ...), of volume `1`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.Okounkov.PobDimZero

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set Filter MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.AlmostSemigroup SGPT.AlmostSemigroup.Class SGPT.AlmostSemigroup.Okounkov
open scoped Topology

/-! ### The lattice semigroup `{(0, k) : k ∈ ℕ}` of `ℤ⁰ × ℤ` -/

section Lattice

/-- The lattice points `(0, k)`, `k ∈ ℕ`, of `ℤ⁰ × ℤ`. In dimension `0` every section semigroup
of the chapter (`Γ(L)`, `Γ(θ, φ)`, `Γ^∞(θ, φ)`) is this semigroup. -/
def nonnegHeight : AddSubsemigroup ((Fin 0 → ℤ) × ℤ) where
  carrier := {z | 0 ≤ z.2}
  add_mem' {a b} ha hb := by
    change 0 ≤ (a + b).2
    exact add_nonneg ha hb

@[simp] theorem mem_nonnegHeight {z : (Fin 0 → ℤ) × ℤ} : z ∈ nonnegHeight ↔ 0 ≤ z.2 :=
  Iff.rfl

/-- `{(0, k) : k ∈ ℕ}` generates `ℤ⁰⁺¹`. -/
theorem generatedGroup_nonnegHeight : LatticeSlices.generatedGroup nonnegHeight = ⊤ := by
  rw [eq_top_iff]
  intro z _
  have h1 : ((0 : Fin 0 → ℤ), (1 : ℤ)) ∈ LatticeSlices.generatedGroup nonnegHeight :=
    AddSubgroup.subset_closure (show (0 : ℤ) ≤ 1 from zero_le_one)
  have hz : z = z.2 • ((0 : Fin 0 → ℤ), (1 : ℤ)) := by
    ext i
    · exact i.elim0
    · simp
  rw [hz]
  exact AddSubgroup.zsmul_mem _ h1 _

/-- A closed convex cone containing a point contains the origin. -/
theorem zero_mem_cone_of_mem {n : ℕ} (C : AdmissibleCone n) {x : (Fin n → ℝ) × ℝ}
    (hx : x ∈ C.cone) : (0 : (Fin n → ℝ) × ℝ) ∈ C.cone := by
  have hlim : Tendsto (fun k : ℕ => ((k : ℝ) + 1)⁻¹ • x) atTop (𝓝 0) := by
    have h : Tendsto (fun k : ℕ => ((k : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
    simpa using h.smul_const x
  exact C.closed.mem_of_tendsto hlim (Eventually.of_forall fun k =>
    C.cone.smul_mem (inv_pos.mpr (by positivity)) hx)

/-- `{(0, k) : k ∈ ℕ}` lies in every admissible cone containing `(0, 1)`. -/
theorem nonnegHeight_le_latticePoints (C : AdmissibleCone 0)
    (h1 : ((0 : Fin 0 → ℝ), (1 : ℝ)) ∈ C.cone) : nonnegHeight ≤ latticePoints C.cone := by
  intro z hz
  change latticeCast 0 z ∈ C.cone
  have hcast : latticeCast 0 z = (z.2 : ℝ) • ((0 : Fin 0 → ℝ), (1 : ℝ)) := by
    ext i
    · exact i.elim0
    · simp [latticeCast]
  rw [hcast]
  rcases (show (0 : ℤ) ≤ z.2 from hz).lt_or_eq with hpos | hzero
  · exact C.cone.smul_mem (by exact_mod_cast hpos) h1
  · rw [← hzero, Int.cast_zero, zero_smul]
    exact zero_mem_cone_of_mem C h1

/-- In dimension `0` the cube cone `C([0, c]⁰)` is the half-line `{(0, t) : t ≥ 0}`. -/
theorem mem_cubeCone_zero_one (c : ℝ) :
    ((0 : Fin 0 → ℝ), (1 : ℝ)) ∈ (cubeCone (n := 0) c).cone :=
  ⟨zero_le_one, fun i => i.elim0⟩

/-- The cone over a nonempty compact convex `K ⊆ ℝ⁰` contains `(0, 1)`. -/
theorem mem_coneOver_zero_one {K : Set (Fin 0 → ℝ)} (hKc : IsCompact K) (hKv : Convex ℝ K)
    (hK : K.Nonempty) :
    ((0 : Fin 0 → ℝ), (1 : ℝ)) ∈ (SGPT.GAGA.OkoClose.coneOver K hKc hKv).cone := by
  obtain ⟨x, hx⟩ := hK
  exact ⟨zero_le_one, x, hx, Subsingleton.elim _ _⟩

variable (C : AdmissibleCone 0) (hS : nonnegHeight ≤ latticePoints C.cone)

/-- `{(0, k) : k ∈ ℕ}` is a full semigroup (`𝒮'(C)`) of every admissible cone containing it. -/
theorem sourceSubset_nonnegHeight_mem_fullSemigroupLocus :
    sourceSubset C nonnegHeight hS ∈ fullSemigroupLocus C :=
  sourceSubset_mem_fullSemigroupLocus C nonnegHeight hS generatedGroup_nonnegHeight

/-- Each degree slice of `{(0, k) : k ∈ ℕ}` has exactly one point. -/
theorem card_slices_nonnegHeight (k : ℕ) :
    ((sourceSubset C nonnegHeight hS).slices k).card = 1 := by
  rw [card_sourceSubset_slices]
  have huniv : slice (nonnegHeight : Set ((Fin 0 → ℤ) × ℤ)) (k : ℤ) = univ :=
    eq_univ_of_forall fun x => (mem_nonnegHeight (z := (x, (k : ℤ)))).mpr (Nat.cast_nonneg k)
  rw [huniv, Nat.card_univ, Nat.card_unique]

/-- `k⁻⁰ #Γ_k = 1` for every `k`. -/
theorem normalizedCardinality_nonnegHeight (k : ℕ) :
    (sourceSubset C nonnegHeight hS).normalizedCardinality k = 1 := by
  rw [ConeSubset.normalizedCardinality, card_slices_nonnegHeight, pow_zero, one_mul,
    Nat.cast_one]

theorem tendsto_normalizedCardinality_nonnegHeight :
    Tendsto (sourceSubset C nonnegHeight hS).normalizedCardinality atTop (𝓝 1) := by
  simp_rw [show (sourceSubset C nonnegHeight hS).normalizedCardinality = fun _ => 1 from
    funext (normalizedCardinality_nonnegHeight C hS)]
  exact tendsto_const_nhds

/-- `vol {(0, k) : k ∈ ℕ} = 1`. -/
theorem volume_sourceSubset_nonnegHeight : (sourceSubset C nonnegHeight hS).volume = 1 :=
  (tendsto_normalizedCardinality_nonnegHeight C hS).limsup_eq

/-- `{(0, k) : k ∈ ℕ}` lies in the almost-semigroup locus `𝒮'(C)‾_{>0}`. -/
theorem sourceSubset_nonnegHeight_mem_almostSemigroupLocus :
    sourceSubset C nonnegHeight hS ∈ almostSemigroupLocus C :=
  (fullToAlmost ⟨_, sourceSubset_nonnegHeight_mem_fullSemigroupLocus C hS⟩).property

end Lattice

/-! ### Subsets of `ℝ⁰` -/

section Point

/-- A nonempty subset of `ℝ⁰` is the whole space `{0}`. -/
theorem eq_univ_of_nonempty_euclidean {s : Set (EuclideanSpace ℝ (Fin 0))} (hs : s.Nonempty) :
    s = univ := by
  obtain ⟨y, hy⟩ := hs
  exact eq_univ_of_forall fun x => Subsingleton.elim y x ▸ hy

/-- A nonempty subset of `ℝ⁰` (coordinates) is the whole space `{0}`. -/
theorem eq_univ_of_nonempty_fun {s : Set (Fin 0 → ℝ)} (hs : s.Nonempty) : s = univ := by
  obtain ⟨y, hy⟩ := hs
  exact eq_univ_of_forall fun x => Subsingleton.elim y x ▸ hy

/-- `ℝ⁰` has volume `1`. -/
theorem volume_univ_euclidean : volume (univ : Set (EuclideanSpace ℝ (Fin 0))) = 1 := by
  have h := SGPT.AlmostSemigroup.BrunnMinkowski.volume_zero_dimensional
    (⟨univ, convex_univ, isCompact_univ, univ_nonempty⟩ :
      ConvexBody (EuclideanSpace ℝ (Fin 0)))
  have hfin : volume (univ : Set (EuclideanSpace ℝ (Fin 0))) ≠ ⊤ := measure_ne_top _ _
  rw [← ENNReal.ofReal_toReal hfin]
  change ENNReal.ofReal (volume.real (univ : Set (EuclideanSpace ℝ (Fin 0)))) = 1
  rw [show volume.real (univ : Set (EuclideanSpace ℝ (Fin 0))) = 1 from h, ENNReal.ofReal_one]

/-- `ℝ⁰` (coordinates) has volume `1`. -/
theorem volume_univ_fun : volume (univ : Set (Fin 0 → ℝ)) = 1 :=
  Measure.pi_empty_univ (fun _ : Fin 0 ↦ (volume : Measure ℝ))

/-- Hausdorff distances in `ℝ⁰` vanish. -/
theorem hausdorffDist_euclidean (s t : Set (EuclideanSpace ℝ (Fin 0))) :
    Metric.hausdorffDist s t = 0 := by
  by_cases hs : s.Nonempty
  · by_cases ht : t.Nonempty
    · rw [eq_univ_of_nonempty_euclidean hs, eq_univ_of_nonempty_euclidean ht,
        Metric.hausdorffDist_self_zero]
    · rw [not_nonempty_iff_eq_empty.mp ht, Metric.hausdorffDist_empty]
  · rw [not_nonempty_iff_eq_empty.mp hs, Metric.hausdorffDist_empty']

end Point

/-! ### The scheme and its sections in dimension zero -/

section Scheme

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (E : ClosedProjectiveEmbedding f)
  [SmoothOfRelativeDimension 0 f]

local instance pobDimZeroTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance pobDimZeroCharts : ChartedSpace (ComplexModel 0) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f 0
local instance pobDimZeroManifold [IsSeparated f] [QuasiCompact f] :
    IsComplexManifold 0 (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f 0

variable (Y : Fin (0 + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y)

include E Y hY in
/-- With the smooth flag `Y₀ = X` of the setting, `X(ℂ)` is connected of dimension `0`, hence a
single point. -/
theorem subsingleton_complexPoint : Subsingleton (SchemeComplexPoint f) := by
  let := E.isSeparated
  let := E.quasiCompact
  have := schemeSmoothFlag_connectedSpace f 0 Y hY
  exact SGPT.NPP.subsingleton_of_dim_zero

include E Y hY in
theorem nonempty_complexPoint : Nonempty (SchemeComplexPoint f) := by
  let := E.isSeparated
  let := E.quasiCompact
  obtain ⟨x, -⟩ := hY.last_eq_singleton
  exact ⟨x⟩

omit [SmoothOfRelativeDimension 0 f] in
/-- If a complex scheme of finite type has at most one complex point, it has at most one point:
every point specializes to the image of a complex point and every open neighbourhood of a point
contains the image of a complex point (`NANS.exists_mem_subvarietyPoints`, Nullstellensatz). -/
theorem subsingleton_scheme [LocallyOfFiniteType f] [Subsingleton (SchemeComplexPoint f)] :
    Subsingleton X := by
  have key : ∀ (q : SchemeComplexPoint f) (w : X),
      w ⤳ schemeComplexPointImage f q ∧ schemeComplexPointImage f q ⤳ w := by
    intro q w
    obtain ⟨q', hq', -⟩ := SGPT.NAPotential.NANS.exists_mem_subvarietyPoints (f := f) (y := w)
      (W := ⊤) trivial
    rw [Subsingleton.elim q q']
    refine ⟨hq', ?_⟩
    rw [specializes_iff_forall_open]
    intro s hs hws
    obtain ⟨q'', -, hq''⟩ := SGPT.NAPotential.NANS.exists_mem_subvarietyPoints (f := f) (y := w)
      (W := ⟨s, hs⟩) hws
    rw [Subsingleton.elim q' q'']
    exact hq''
  refine ⟨fun y z => ?_⟩
  obtain ⟨q, -⟩ := SGPT.NAPotential.NANS.exists_mem_subvarietyPoints (f := f) (y := y) (W := ⊤)
    trivial
  exact (((key q y).1.antisymm (key q y).2).trans ((key q z).1.antisymm (key q z).2).symm).eq

include E Y hY in
/-- In dimension `0` (with the flag of the setting) the scheme `X` has one point. -/
theorem subsingleton_scheme_of_flag : Subsingleton X := by
  have := E.locallyOfFiniteType
  have := subsingleton_complexPoint f E Y hY
  exact subsingleton_scheme f

omit [SmoothOfRelativeDimension 0 f] in
/-- On an integral scheme with one point, every power `Lᵏ` of a line bundle with an atlas has a
nonzero global section (the frame of the chart containing the point is global). -/
theorem exists_section_ne_zero_of_subsingleton [IsIntegral X] [Subsingleton X] {L : X.Modules}
    (a : LineBundleAtlas L) (k : ℕ) : ∃ s : bundlePowerGlobalSections L k, s ≠ 0 := by
  obtain ⟨x⟩ : Nonempty X := inferInstance
  obtain ⟨i, hi⟩ := a.covers x
  have htop : (⊤ : X.Opens) ≤ a.opens i := fun y _ => (Subsingleton.elim y x) ▸ hi
  let e := ((a.frame i).tensorPower k).coefficients (homOfLE htop)
  refine ⟨e.symm 1, fun h => ?_⟩
  have h1 : e (e.symm 1) = e 0 := congrArg e h
  rw [LinearEquiv.apply_symm_apply, map_zero] at h1
  have : Nonempty (⊤ : X.Opens) := ⟨⟨x, trivial⟩⟩
  have : IsDomain Γ(X, ⊤) := inferInstance
  exact one_ne_zero (α := Γ(X, ⊤)) h1

include E Y hY in
/-- **`H⁰(X, Lᵏ) ≠ 0` for every `k`** in dimension `0`. -/
theorem exists_section_ne_zero [IsIntegral X] {L : X.Modules} (a : LineBundleAtlas L) (k : ℕ) :
    ∃ s : bundlePowerGlobalSections L k, s ≠ 0 := by
  have := subsingleton_scheme_of_flag f E Y hY
  exact exists_section_ne_zero_of_subsingleton a k

include E Y hY in
/-- Every function on the point `X(ℂ)` is holomorphic. -/
theorem holomorphicAt_of_dim_zero (g : SchemeComplexPoint f → ℂ) (x : SchemeComplexPoint f) :
    letI := E.isSeparated
    letI := E.quasiCompact
    HolomorphicAt 0 g x := by
  let := E.isSeparated
  let := E.quasiCompact
  have := subsingleton_complexPoint f E Y hY
  have hg : g = fun _ => g x := funext fun y => congrArg g (Subsingleton.elim y x)
  rw [hg]
  exact holomorphicAt_const _

include Y hY in
/-- **`𝓘(kφ) = 𝒪_X`** in dimension `0`: every section of `Lᵏ` is a section of `Lᵏ ⊗ 𝓘(kφ)`. -/
theorem isMultiplierSection_of_dim_zero {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsGlobalQuasiPshPotential (n := 0) φ) {L : X.Modules} (k : ℕ)
    (s : bundlePowerGlobalSections L k) : IsMultiplierSection f 0 E φ k s := by
  let := E.isSeparated
  let := E.quasiCompact
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact Or.inl rfl
  refine Or.inr fun U α p _ => ?_
  exact (ZeroDimensionalQuasiPshMultiplierIdeals.mem_multiplierIdeal_iff_holomorphicAt hφ
    (by exact_mod_cast hk) p _).mpr (holomorphicAt_of_dim_zero f E Y hY _ p)

include Y hY in
/-- **`𝓘_∞(kφ) = 𝒪_X`** in dimension `0`: every section of `Lᵏ` is a section of
`Lᵏ ⊗ 𝓘_∞(kφ)`. -/
theorem isInftySection_of_dim_zero {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsGlobalQuasiPshPotential (n := 0) φ) {L : X.Modules} (k : ℕ)
    (s : bundlePowerGlobalSections L k) : IsInftySection f 0 E φ k s := by
  let := E.isSeparated
  let := E.quasiCompact
  have hsub := subsingleton_complexPoint f E Y hY
  intro U α p _
  refine ⟨holomorphicAt_of_dim_zero f E Y hY _ p, ?_⟩
  set g := sectionFrameCoefficient f 0 E α k s
  have hbot : φ p ≠ ⊥ := by
    obtain ⟨y, -, hy⟩ := hφ.2 p univ isOpen_univ (mem_univ p)
    rwa [Subsingleton.elim y p] at hy
  obtain ⟨t, ht⟩ : ∃ t : ℝ, φ p = t :=
    ⟨(φ p).toReal, (EReal.coe_toReal (hφ.1.ne_top p) hbot).symm⟩
  have hP : ((k : EReal) * φ p) = ((k * t : ℝ) : EReal) := by
    rw [ht, ← EReal.coe_natCast, ← EReal.coe_mul]
  refine ⟨‖g p‖ ^ 2 * Real.exp (-(1 * (k * t))) + 1, by positivity,
    Eventually.of_forall fun y => ?_⟩
  rw [Subsingleton.elim y p]
  change ENNReal.ofReal (‖g p‖ ^ 2) * multiplierWeight 1 ((k : EReal) * φ p) ≤ _
  rw [hP, multiplierWeight_coe, ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right zero_le_one)

end Scheme

/-! ### The section sets and the bodies in dimension zero -/

section Bodies

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (E : ClosedProjectiveEmbedding f)
  [SmoothOfRelativeDimension 0 f] [IsIntegral X]

local instance pobDimZeroBodiesTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance pobDimZeroBodiesCharts : ChartedSpace (ComplexModel 0) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f 0
local instance pobDimZeroBodiesManifold [IsSeparated f] [QuasiCompact f] :
    IsComplexManifold 0 (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f 0

variable (Y : Fin (0 + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y)
  {L : X.Modules} (a : LineBundleAtlas L)

/-- A section set `{(ν(s), k) : P k s}` whose degreewise condition holds for all sections is
`{(0, k) : k ∈ ℕ}` in dimension `0`. -/
theorem sectionValueSet_eq_of_forall {P : ∀ k : ℕ, bundlePowerGlobalSections L k → Prop}
    (hP : ∀ k s, P k s) :
    sectionValueSet f 0 E Y hY a P = (nonnegHeight : Set ((Fin 0 → ℤ) × ℤ)) := by
  ext z
  constructor
  · rintro ⟨k, s, hs, -, rfl⟩
    exact (mem_nonnegHeight (z := (_, (k : ℤ)))).mpr (Nat.cast_nonneg k)
  · intro hz
    have hz' : 0 ≤ z.2 := hz
    obtain ⟨s, hs⟩ := exists_section_ne_zero f E Y hY a z.2.toNat
    refine ⟨z.2.toNat, s, hs, hP _ s, ?_⟩
    ext i
    · exact i.elim0
    · exact (Int.toNat_of_nonneg hz').symm

/-- **`Γ(θ, φ) = {(0, k) : k ∈ ℕ}`** in dimension `0`, for every quasi-psh weight `φ`. -/
theorem multiplierSectionSet_eq {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsGlobalQuasiPshPotential (n := 0) φ) :
    multiplierSectionSet f 0 E Y hY a φ = (nonnegHeight : Set ((Fin 0 → ℤ) × ℤ)) :=
  sectionValueSet_eq_of_forall f E Y hY a fun k s => isMultiplierSection_of_dim_zero f E Y hY hφ k s

/-- **`Γ^∞(θ, φ) = {(0, k) : k ∈ ℕ}`** in dimension `0`, for every quasi-psh weight `φ`. -/
theorem inftySectionSet_eq {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsGlobalQuasiPshPotential (n := 0) φ) :
    inftySectionSet f 0 E Y hY a φ = (nonnegHeight : Set ((Fin 0 → ℤ) × ℤ)) :=
  sectionValueSet_eq_of_forall f E Y hY a fun k s => isInftySection_of_dim_zero f E Y hY hφ k s

/-- **`Γ(L) = {(0, k) : k ∈ ℕ}`** in dimension `0`. -/
theorem schemeProjectiveSectionSemigroup_eq :
    schemeProjectiveSectionSemigroup f 0 E Y hY a = nonnegHeight := by
  ext z
  constructor
  · rintro ⟨k, s, hs, rfl⟩
    exact (mem_nonnegHeight (z := (_, (k : ℤ)))).mpr (Nat.cast_nonneg k)
  · intro hz
    have hz' : 0 ≤ z.2 := hz
    obtain ⟨s, hs⟩ := exists_section_ne_zero f E Y hY a z.2.toNat
    refine ⟨z.2.toNat, s, hs, ?_⟩
    ext i
    · exact i.elim0
    · exact (Int.toNat_of_nonneg hz').symm

include E Y hY a in
/-- **`h⁰(X, Lᵏ) = 1`** for every `k` in dimension `0`. -/
theorem h0_eq_one (k : ℕ) : SGPT.LineBundle.h0 f L k = 1 := by
  have h := schemeProjectiveSectionSemigroup_slice_card_eq_finrank f 0 E Y hY a k
  rw [schemeProjectiveSectionSemigroup_eq f E Y hY a] at h
  have huniv : slice (nonnegHeight : Set ((Fin 0 → ℤ) × ℤ)) (k : ℤ) = univ :=
    eq_univ_of_forall fun x => (mem_nonnegHeight (z := (x, (k : ℤ)))).mpr (Nat.cast_nonneg k)
  rw [huniv, Nat.card_univ, Nat.card_unique] at h
  exact h.symm

include E Y hY a in
/-- **`vol L = 1`** in dimension `0` (`vol L = limsup 0! h⁰(Lᵏ)/k⁰`). -/
theorem lineBundle_volume_eq_one : SGPT.LineBundle.volume f L 0 = 1 := by
  have h : (fun k : ℕ => (((0 : ℕ).factorial : ENNReal) * (SGPT.LineBundle.h0 f L k : ENNReal)) /
      (k : ENNReal) ^ 0) = fun _ => 1 := by
    funext k
    rw [h0_eq_one f E Y hY a k]
    simp
  rw [SGPT.LineBundle.volume, h]
  exact limsup_const 1

include E Y hY a in
/-- Every line bundle is big in dimension `0`. -/
theorem isBig : SGPT.LineBundle.IsBig f L 0 :=
  ⟨1, one_pos, Eventually.of_forall fun k => by simp [h0_eq_one f E Y hY a k]⟩

/-- **`Δ(L) = ℝ⁰`** in dimension `0`. -/
theorem lineBundleOkounkovBody_eq_univ : lineBundleOkounkovBody f 0 E Y hY a = univ := by
  obtain ⟨s, hs⟩ := exists_section_ne_zero f E Y hY a 1
  exact eq_univ_of_nonempty_fun ⟨_, normalized_mem_lineBundleOkounkovBody f 0 E Y hY a one_pos s hs⟩

/-- The degree polytopes of `{(0, k) : k ∈ ℕ}` are `ℝ⁰`. -/
theorem degreePolytope_nonnegHeight (k : ℕ) :
    degreePolytope 0 (nonnegHeight : Set ((Fin 0 → ℤ) × ℤ)) k = univ := by
  apply eq_univ_of_nonempty_fun
  refine (Set.Nonempty.image _ ?_).convexHull
  exact ⟨0, (mem_nonnegHeight (z := ((0 : Fin 0 → ℤ), (k : ℤ)))).mpr (Nat.cast_nonneg k)⟩

/-- **`Δ_k(θ, φ) = ℝ⁰`** for every `k` in dimension `0`. -/
theorem multiplierDegreePolytope_eq_univ {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsGlobalQuasiPshPotential (n := 0) φ) (k : ℕ) :
    multiplierDegreePolytope f 0 E Y hY a φ k = univ := by
  rw [multiplierDegreePolytope, multiplierSectionSet_eq f E Y hY a hφ, degreePolytope_nonnegHeight]

/-- **`Δ_{k,T}(L) = ℝ⁰`** for every twist `T` and every `k` in dimension `0`. -/
theorem twistedDegreePolytope_eq_univ {T : X.Modules} (k : ℕ)
    (b : LineBundleAtlas (bundleTensor T (bundleTensorPower L k))) :
    twistedDegreePolytope f 0 E Y hY k b = univ := by
  apply eq_univ_of_nonempty_fun
  obtain ⟨s, hs⟩ := exists_section_ne_zero f E Y hY b 1
  rw [twistedDegreePolytope]
  exact (Set.Nonempty.image _ (⟨_, s, hs, rfl⟩ : Set.Nonempty {x : Fin 0 → ℤ | ∃
    (s : bundlePowerGlobalSections (bundleTensor T (bundleTensorPower L k)) 1) (hs : s ≠ 0),
      x = fun i => (schemeFubiniStudySectionVector f 0 E Y hY b 1 s hs i : ℤ)})).convexHull

/-- **`Δ_{k,T}(θ, φ) = ℝ⁰`** for every twist `T` and every `k` in dimension `0`. -/
theorem twistedMultiplierDegreePolytope_eq_univ {T : X.Modules} (k : ℕ)
    (b : LineBundleAtlas (bundleTensor T (bundleTensorPower L k)))
    {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsGlobalQuasiPshPotential (n := 0) φ) :
    twistedMultiplierDegreePolytope f 0 E Y hY k b φ = univ := by
  apply eq_univ_of_nonempty_fun
  obtain ⟨s, hs⟩ := exists_section_ne_zero f E Y hY b 1
  have hmult : k = 0 ∨ IsIdealSection f 0 E (multiplierIdeal (n := 0) (k : ℝ) φ) 1 s := by
    rcases Nat.eq_zero_or_pos k with hk | hk
    · exact Or.inl hk
    · let := E.isSeparated
      let := E.quasiCompact
      refine Or.inr fun U α p _ => ?_
      exact (ZeroDimensionalQuasiPshMultiplierIdeals.mem_multiplierIdeal_iff_holomorphicAt hφ
        (by exact_mod_cast hk) p _).mpr (holomorphicAt_of_dim_zero f E Y hY _ p)
  rw [twistedMultiplierDegreePolytope]
  exact (Set.Nonempty.image _ (⟨_, s, hs, hmult, rfl⟩ :
    (twistedMultiplierValues f 0 E Y hY k b φ).Nonempty)).convexHull

/-- `Γ(θ, φ)`, read in an admissible cone `C ∋ (0, 1)`, is `{(0, k) : k ∈ ℕ}`. -/
theorem multiplierSectionSet_subset {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsGlobalQuasiPshPotential (n := 0) φ) (C : AdmissibleCone 0)
    (h1 : ((0 : Fin 0 → ℝ), (1 : ℝ)) ∈ C.cone) :
    multiplierSectionSet f 0 E Y hY a φ ⊆ (latticePoints C.cone : Set _) := by
  rw [multiplierSectionSet_eq f E Y hY a hφ]
  exact nonnegHeight_le_latticePoints C h1

/-- **`Γ(θ, φ) ∈ 𝒮'(C)‾_{>0}`** (indeed `Γ(θ, φ) ∈ 𝒮'(C)`) in dimension `0`, for every
admissible cone `C ∋ (0, 1)`. -/
theorem multiplierConeSubset_mem_almostSemigroupLocus {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsGlobalQuasiPshPotential (n := 0) φ) (C : AdmissibleCone 0)
    (h1 : ((0 : Fin 0 → ℝ), (1 : ℝ)) ∈ C.cone) :
    (⟨_, multiplierSectionSet_subset f E Y hY a hφ C h1⟩ : ConeSubset C) ∈
      fullSemigroupLocus C ∧
    (⟨_, multiplierSectionSet_subset f E Y hY a hφ C h1⟩ : ConeSubset C) ∈
      almostSemigroupLocus C ∧
    ConeSubset.volume (⟨_, multiplierSectionSet_subset f E Y hY a hφ C h1⟩ : ConeSubset C) = 1 := by
  have hS := nonnegHeight_le_latticePoints C h1
  have heq : (⟨_, multiplierSectionSet_subset f E Y hY a hφ C h1⟩ : ConeSubset C) =
      sourceSubset C nonnegHeight hS :=
    Subtype.ext (multiplierSectionSet_eq f E Y hY a hφ)
  rw [heq]
  exact ⟨sourceSubset_nonnegHeight_mem_fullSemigroupLocus C hS,
    sourceSubset_nonnegHeight_mem_almostSemigroupLocus C hS,
    volume_sourceSubset_nonnegHeight C hS⟩

/-- **`Δ(θ, φ) = Δ(Γ(θ, φ)) = ℝ⁰`** in dimension `0`, for every quasi-psh weight `φ` and every
admissible cone `C ∋ (0, 1)` (in particular every cube cone). -/
theorem partialOkounkovBody_eq_univ {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsGlobalQuasiPshPotential (n := 0) φ) (C : AdmissibleCone 0)
    (h1 : ((0 : Fin 0 → ℝ), (1 : ℝ)) ∈ C.cone) :
    partialOkounkovBody f 0 E Y hY C a φ = univ := by
  rw [partialOkounkovBody_eq a φ (multiplierSectionSet_subset f E Y hY a hφ C h1)
    (multiplierConeSubset_mem_almostSemigroupLocus f E Y hY a hφ C h1).2.1]
  exact eq_univ_of_nonempty_euclidean (ConvexBody.nonempty _)

/-- `Δ(θ, φ) = ℝ⁰` for every cube cone `C([0, c]⁰)`. -/
theorem partialOkounkovBody_cubeCone_eq_univ {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsGlobalQuasiPshPotential (n := 0) φ) (c : ℝ) :
    partialOkounkovBody f 0 E Y hY (cubeCone c) a φ = univ :=
  partialOkounkovBody_eq_univ f E Y hY a hφ _ (mem_cubeCone_zero_one c)

end Bodies

/-! ### Potentials, volumes and the `𝓘`-order in dimension zero -/

section Potentials

variable {M : Type}

/-- Finite real multiples of finite functions are finite. -/
theorem finite_coe_mul {u : M → EReal} (hu : ∀ x, u x ≠ ⊤ ∧ u x ≠ ⊥) (c : ℝ) (x : M) :
    ((c : EReal) * u x) ≠ ⊤ ∧ ((c : EReal) * u x) ≠ ⊥ := by
  obtain ⟨t, ht⟩ : ∃ t : ℝ, u x = t :=
    ⟨(u x).toReal, (EReal.coe_toReal (hu x).1 (hu x).2).symm⟩
  rw [ht, ← EReal.coe_mul]
  exact ⟨EReal.coe_ne_top _, EReal.coe_ne_bot _⟩

/-- Sums of finite functions are finite. -/
theorem finite_add {u w : M → EReal} (hu : ∀ x, u x ≠ ⊤ ∧ u x ≠ ⊥)
    (hw : ∀ x, w x ≠ ⊤ ∧ w x ≠ ⊥) (x : M) : (u x + w x) ≠ ⊤ ∧ (u x + w x) ≠ ⊥ := by
  obtain ⟨t, ht⟩ : ∃ t : ℝ, u x = t :=
    ⟨(u x).toReal, (EReal.coe_toReal (hu x).1 (hu x).2).symm⟩
  obtain ⟨r, hr⟩ : ∃ r : ℝ, w x = r :=
    ⟨(w x).toReal, (EReal.coe_toReal (hw x).1 (hw x).2).symm⟩
  rw [ht, hr, ← EReal.coe_add]
  exact ⟨EReal.coe_ne_top _, EReal.coe_ne_bot _⟩

variable [TopologicalSpace M] [ChartedSpace (ComplexModel 0) M] [IsComplexManifold 0 M]

/-- In dimension `0`, a `θ`-psh potential is finite everywhere. -/
theorem finite_of_isThetaPshPotential {θ : SmoothRealForm 0 M 2} {u : M → EReal}
    (hu : IsThetaPshPotential θ u) (x : M) : u x ≠ ⊤ ∧ u x ≠ ⊥ :=
  ⟨hu.1.quasiPlurisubharmonic.ne_top x,
    RooftopDimZero.ne_bot_of_locallyNondegenerate_of_dim_zero rfl hu.2 x⟩

/-- In dimension `0`, every finite function is `θ`-psh, for every closed real `(1,1)`-form `θ`
(all such forms vanish). -/
theorem isThetaPshPotential_of_finite (θ : ClosedRealOneOneForm 0 M) {u : M → EReal}
    (hu : ∀ x, u x ≠ ⊤ ∧ u x ≠ ⊥) : IsThetaPshPotential θ.val u :=
  RooftopDimZero.isThetaPshPotential_of_dim_zero rfl
    (LocalPotentials.closedRealOneOne_hasLocalPotentials θ) (fun x => (hu x).1) (fun x => (hu x).2)

/-- In dimension `0`, every finite function is quasi-psh. -/
theorem isGlobalQuasiPshPotential_of_finite {u : M → EReal} (hu : ∀ x, u x ≠ ⊤ ∧ u x ≠ ⊥) :
    IsGlobalQuasiPshPotential (n := 0) u :=
  (isThetaPshPotential_of_finite (0 : ClosedRealOneOneForm 0 M) hu).quasiPshPotential

/-- In dimension `0` every potential precedes every quasi-psh potential in the `𝓘`-order:
`𝓘(cφ) ⊆ 𝓘(cψ) = 𝒪` for all `c > 0`. -/
theorem iOrderOnManifold_of_dim_zero (u : M → EReal) {w : M → EReal}
    (hw : IsGlobalQuasiPshPotential (n := 0) w) : IEnvelope.IOrderOnManifold (n := 0) u w :=
  ZeroDimensionalQuasiPshMultiplierIdeals.iOrderOnManifold_of_genuine_right u hw

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]

/-- **`∫_X θ_φ⁰ = 1`** on a point. -/
theorem diagonalPotentialMass_eq_one (θ : ClosedRealOneOneForm 0 M) {u : M → EReal}
    (hu : IsThetaPshPotential θ.val u) : DiagonalMass.diagonalPotentialMass θ u hu = 1 :=
  SGPT.Trace.RestVol.diagonalPotentialMass_eq_one_of_dim_zero θ hu

/-- **`vol θ_φ = 1`** on a point: in dimension `0`, `PSH(X, θ)_{>0} = PSH(X, θ)`. -/
theorem iVolume_eq_one [Nonempty M] (θ : ClosedRealOneOneForm 0 M)
    (hlocal : HasSmoothLocalPotentials θ.val) {u : M → EReal}
    (hu : IsThetaPshPotential θ.val u) : iVolume θ hlocal u hu = 1 :=
  diagonalPotentialMass_eq_one θ _

end Potentials

/-! ### Arbitrary valuations in dimension zero -/

section Valuation

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (E : ClosedProjectiveEmbedding f)
  [SmoothOfRelativeDimension 0 f] [IsIntegral X]

local instance pobDimZeroValTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance pobDimZeroValCharts : ChartedSpace (ComplexModel 0) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f 0
local instance pobDimZeroValManifold [IsSeparated f] [QuasiCompact f] :
    IsComplexManifold 0 (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f 0

variable (Y : Fin (0 + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y)
  {L : X.Modules} (a : LineBundleAtlas L) (c : X)
  (v : AddValuation X.functionField (WithTop (Lex (Fin 0 → ℤ))))

include E Y hY in
/-- For an arbitrary (rank-`0`) valuation `ν = v`, a section set whose degreewise condition holds
for all sections is `{(0, k) : k ∈ ℕ}` in dimension `0`. -/
theorem valuation_sectionValueSet_eq_of_forall
    {P : ∀ k : ℕ, bundlePowerGlobalSections L k → Prop} (hP : ∀ k s, P k s) :
    AlgebraicValuation.sectionValueSet v c a P = (nonnegHeight : Set ((Fin 0 → ℤ) × ℤ)) := by
  ext z
  constructor
  · rintro ⟨k, s, hs, -, rfl⟩
    exact (mem_nonnegHeight (z := (_, (k : ℤ)))).mpr (Nat.cast_nonneg k)
  · intro hz
    have hz' : 0 ≤ z.2 := hz
    obtain ⟨s, hs⟩ := exists_section_ne_zero f E Y hY a z.2.toNat
    refine ⟨z.2.toNat, s, hs, hP _ s, ?_⟩
    ext i
    · exact i.elim0
    · exact (Int.toNat_of_nonneg hz').symm

include E Y hY in
/-- **`Γ_ν(L) = {(0, k) : k ∈ ℕ}`** for an arbitrary valuation in dimension `0`; in particular the
conclusion `Γ_ν(L) ∈ 𝒮'(C)` of source `prop:Okounbiglbdl` holds for every valuation. -/
theorem valuation_sectionSemigroup_eq :
    AlgebraicValuation.sectionSemigroup v c a = nonnegHeight := by
  ext z
  rw [← SetLike.mem_coe, ← AlgebraicValuation.sectionValueSet_true,
    valuation_sectionValueSet_eq_of_forall f E Y hY a c v fun _ _ => trivial]
  rfl

include E Y hY in
/-- **`Γ_ν(θ, φ) = {(0, k) : k ∈ ℕ}`** for an arbitrary valuation in dimension `0`. -/
theorem valuation_multiplierSectionSet_eq {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsGlobalQuasiPshPotential (n := 0) φ) :
    AlgebraicValuation.multiplierSectionSet f 0 E v c a φ =
      (nonnegHeight : Set ((Fin 0 → ℤ) × ℤ)) :=
  valuation_sectionValueSet_eq_of_forall f E Y hY a c v fun k s =>
    isMultiplierSection_of_dim_zero f E Y hY hφ k s

include E Y hY in
/-- **`Γ^∞_ν(θ, φ) = {(0, k) : k ∈ ℕ}`** for an arbitrary valuation in dimension `0`. -/
theorem valuation_inftySectionSet_eq {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsGlobalQuasiPshPotential (n := 0) φ) :
    AlgebraicValuation.inftySectionSet f 0 E v c a φ =
      (nonnegHeight : Set ((Fin 0 → ℤ) × ℤ)) :=
  valuation_sectionValueSet_eq_of_forall f E Y hY a c v fun k s =>
    isInftySection_of_dim_zero f E Y hY hφ k s

include E Y hY in
/-- **`Δ_ν(θ, φ) = ℝ⁰`** for an arbitrary valuation in dimension `0` (every admissible cone
`C ∋ (0, 1)`). -/
theorem valuation_partialBody_eq_univ {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsGlobalQuasiPshPotential (n := 0) φ) (C : AdmissibleCone 0)
    (h1 : ((0 : Fin 0 → ℝ), (1 : ℝ)) ∈ C.cone) :
    SGPT.Okounkov.ValGen.partialBody f 0 E v c a C φ = univ := by
  have hS := nonnegHeight_le_latticePoints C h1
  have hsub : AlgebraicValuation.multiplierSectionSet f 0 E v c a φ ⊆
      (latticePoints C.cone : Set _) := by
    rw [valuation_multiplierSectionSet_eq f E Y hY a c v hφ]
    exact hS
  have heq : (⟨_, hsub⟩ : ConeSubset C) = sourceSubset C nonnegHeight hS :=
    Subtype.ext (valuation_multiplierSectionSet_eq f E Y hY a c v hφ)
  have hmem : (⟨_, hsub⟩ : ConeSubset C) ∈ almostSemigroupLocus C := by
    rw [heq]
    exact sourceSubset_nonnegHeight_mem_almostSemigroupLocus C hS
  rw [SGPT.Okounkov.ValGen.partialBody_eq a φ hsub hmem]
  exact eq_univ_of_nonempty_euclidean (ConvexBody.nonempty _)

include E Y hY in
/-- **`Δ_ν(L) = ℝ⁰`** for an arbitrary valuation in dimension `0`. -/
theorem valuation_okounkovBody_eq_univ : AlgebraicValuation.okounkovBody v c a = univ := by
  rw [AlgebraicValuation.okounkovBody, valuation_sectionSemigroup_eq f E Y hY a c v]
  have hS := nonnegHeight_le_latticePoints (cubeCone 0) (mem_cubeCone_zero_one 0)
  have hne := BodyGeometry.euclideanBody_nonempty (cubeCone 0) nonnegHeight hS
    generatedGroup_nonnegHeight
  obtain ⟨-, y, hy, -⟩ := hne
  exact eq_univ_of_nonempty_fun ⟨y, hy⟩

end Valuation

end SGPT.Okounkov.PobDimZero
