import SGPT.NAPotential.DivDict2Unconditional
import SGPT.NAPotential.NATraceSmooth
import SGPT.GAGA.H0SSchemeEmbedding

/-! # Non-trivial restrictions of non-Archimedean potentials (`lma:non-trivrest`)

Source `chapter_NApotential.tex`, `lma:non-trivrest`: for `Γ ∈ PSH^NA(X, θ)` and an irreducible
analytic subset `Y ⊆ X`, the following are equivalent:

1. `Γ^An(v_{Y,triv}) ≠ -∞`;
2. `Γ^An|_{Y^An} ≢ -∞`;
3. `Γ` has a well-defined restriction to `Y` (`def:NApotential:L623`).

The proof in the book: (1) ⟺ (2) is the maximum principle, and (1) ⟺ (3) follows from

`φ^An(v_{Y,triv}) = -∞` if `ν(φ, Y) > 0`, `φ^An(v_{Y,triv}) = 0` if `ν(φ, Y) = 0`,

for `φ ∈ PSH(X, θ)`.  Blueprint `claude-na-ns`.

## Formal setting

`X` is a smooth projective complex scheme (relative dimension `m + 1`, closed projective
embedding `E`), `X(ℂ) = SchemeComplexPoint f` with its complex-manifold structure, as in
`SGPT.NAPotential.DivDict2`.  The projective manifold `X(ℂ)` is algebraic, so (Chow) an
irreducible analytic subset is `Y(ℂ)` for an irreducible closed subvariety `Y = closure {y}`,
recorded by its generic point `y : X`; only then is the point `v_{Y,triv} ∈ X^An` (the trivial
valuation of `ℂ(Y) = κ(y)`, supported on `Y`) meaningful.

* `subvarietyTrivial y`: `v_{Y,triv}`; `subvarietyAn y`: `Y^An`, the semi-valuations supported
  in `Y` (`y ⤳ support`); `subvarietyPoints y`: `Y(ℂ)`, the complex points of `Y`.
* `ν(φ, Y)` is the generic Lelong number `inf_{q ∈ Y(ℂ)} ν(φ, q)`
  (`sourceGenericLelongNumber` along the inclusion `Y(ℂ) → X(ℂ)`); the well-definedness
  condition (3) is `NATrace.TraceWellDefined` along this inclusion: `ν(Γ^{θ+ω}_τ, Y) = 0` for all
  sufficiently negative `τ` and every Kähler form `ω`.
* `Γ^An` on `X^An` is the formula `eq:psiandef`,
  `Γ^An(v) = sup_{τ < Γ_max} (Γ^{θ+ω,An}_τ(v) + τ)`, evaluated at every `v ∈ X^An`
  (`naPotentialAnAt`).  The book evaluates at `v_{Y,triv}` and on `Y^An` the unique extension of
  `Γ^An|_{X^Div}` to `PSH(L^An)` (`cor:testcurvegivepshme`, Boucksom–Jonsson side); the
  identification of that extension with `naPotentialAnAt` off `X^Div` is not formalized here.

## Main results

* `stalkIdeal_algebraization_multiplierIdeal_eq_top_iff`: the algebraic model of `𝓘(cφ)` is the
  unit ideal at the generic point of `Y` iff `1 ∈ 𝓘(cφ)_q` for some `q ∈ Y(ℂ)`.
* `potentialAn_subvarietyTrivial_of_eq_zero`, `potentialAn_eq_bot_of_ne_zero`,
  `potentialAn_subvarietyTrivial`: the displayed formula of the proof (and `φ^An ≡ -∞` on `Y^An`
  when `ν(φ, Y) > 0`).
* `naPotentialAnAt_le_subvarietyTrivial`: the maximum principle `Γ^An ≤ Γ^An(v_{Y,triv})` on
  `Y^An`.
* `naPotentialAnAt_subvarietyTrivial_ne_bot_iff`, `source_nonTrivRest`: `lma:non-trivrest`.
* `naPotentialAnAt_subvarietyTrivial_eq_traceCutoff`: `Γ^An(v_{Y,triv}) = (Tr_Y Γ)_max` when the
  restriction is well defined (used in the proof of `thm:comp_traceop`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.NAPotential.NANS

open Set Filter
open scoped Topology ENNReal
open AlgebraicGeometry CategoryTheory IsLocalRing SGPT.Foundations.Schemes SGPT.Okounkov
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves SGPT.Foundations.Analysis.Pending
open SGPT.PSH.VariableComplexAtlas SGPT.NAPotential.Berkovich

/-! ### The trivial valuation of a subvariety -/

section Point

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)}

variable (f) in
/-- `v_{Y,triv} ∈ X^An` for `Y = closure {y}`: the trivial valuation of `ℂ(Y) = κ(y)`, a
semi-valuation with support `Y`. -/
def subvarietyTrivial (y : X) : BerkovichPoint f :=
  letI := Classical.decEq (X.residueField y)
  ⟨y, @SourceRealValuation.trivial _ _ (residueComplexAlgebra f y) _⟩

@[simp] theorem subvarietyTrivial_support (y : X) : (subvarietyTrivial f y).support = y := rfl

/-- For the generic point of an irreducible `X`, `v_{X,triv} = v_triv`. -/
theorem subvarietyTrivial_genericPoint [IrreducibleSpace X] :
    subvarietyTrivial f (genericPoint X) = BerkovichPoint.trivial f := rfl

theorem subvarietyTrivial_valAt_of_ne_zero (y : X) {g : X.residueField y} (hg : g ≠ 0) :
    (subvarietyTrivial f y).valAt g = 0 := by
  classical
  change (if g = 0 then ⊤ else 0 : WithTop ℝ) = 0
  convert if_neg hg

theorem subvarietyTrivial_valAt_eq_zero_or_top (y : X) (g : X.residueField y) :
    (subvarietyTrivial f y).valAt g = 0 ∨ (subvarietyTrivial f y).valAt g = ⊤ := by
  by_cases hg : g = 0
  · exact Or.inr (by rw [hg, BerkovichPoint.valAt_zero])
  · exact Or.inl (subvarietyTrivial_valAt_of_ne_zero y hg)

variable (f) in
/-- `Y^An ⊆ X^An`: the semi-valuations whose support lies in `Y = closure {y}`. -/
def subvarietyAn (y : X) : Set (BerkovichPoint f) :=
  {w | y ⤳ w.support}

theorem subvarietyTrivial_mem_subvarietyAn (y : X) :
    subvarietyTrivial f y ∈ subvarietyAn f y :=
  specializes_refl y

theorem subvarietyTrivial_valAt_nonneg (y : X) (a : X.residueField y) :
    0 ≤ (subvarietyTrivial f y).valAt a := by
  rcases subvarietyTrivial_valAt_eq_zero_or_top (f := f) y a with h | h <;> rw [h]
  exact le_top

/-- `y` is a centre of `v_{Y,triv}`. -/
theorem isCenter_subvarietyTrivial (y : X) : (subvarietyTrivial f y).IsCenter y := by
  refine ⟨specializes_refl y, fun g => subvarietyTrivial_valAt_nonneg y _, fun g hg => ?_⟩
  have key : ∀ a : X.residueField y, a = 0 → 0 < (subvarietyTrivial f y).valAt a := by
    rintro a rfl
    rw [BerkovichPoint.valAt_zero]
    exact WithTop.coe_lt_top 0
  apply key
  show (X.presheaf.stalkSpecializes (specializes_refl y) ≫ X.residue y).hom g = 0
  rw [TopCat.Presheaf.stalkSpecializes_refl, Category.id_comp]
  exact (IsLocalRing.residue_eq_zero_iff g).mpr hg

variable [IsProper f]

/-- The centre of `v_{Y,triv}` is the generic point `y` of `Y`. -/
theorem center_subvarietyTrivial (y : X) : (subvarietyTrivial f y).center = y :=
  (((subvarietyTrivial f y).isCenter_iff_eq_center _).mp (isCenter_subvarietyTrivial y)).symm

/-- The stalk of an ideal sheaf at `y` is the unit ideal iff some section over an affine
neighbourhood of `y` does not vanish at `y`. -/
theorem stalkIdeal_eq_top_iff (𝔞 : X.IdealSheafData) (y : X) :
    stalkIdeal 𝔞 y = ⊤ ↔
      ∃ (U : X.affineOpens) (r : Γ(X, U)), r ∈ 𝔞.ideal U ∧ y ∈ X.basicOpen r := by
  constructor
  · intro h
    by_contra hcon
    push Not at hcon
    have hle : stalkIdeal 𝔞 y ≤ maximalIdeal (X.presheaf.stalk y) := by
      apply iSup₂_le
      intro U hU
      rw [Ideal.map_le_iff_le_comap]
      intro r hr
      rw [Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff]
      intro hunit
      exact hcon U r hr ((X.mem_basicOpen r y hU).mpr hunit)
    rw [h] at hle
    exact (maximalIdeal.isMaximal (X.presheaf.stalk y)).ne_top (top_le_iff.mp hle)
  · rintro ⟨U, r, hr, hy⟩
    have hyU : y ∈ (U : X.Opens) := X.basicOpen_le r hy
    exact Ideal.eq_top_of_isUnit_mem _ (germ_mem_stalkIdeal 𝔞 U hyU hr)
      ((X.mem_basicOpen r y hyU).mp hy)

variable [IsLocallyNoetherian X]

/-- `v_{Y,triv}(𝔞) ∈ {0, ∞}`, and `v_{Y,triv}(𝔞) = 0` iff `𝔞` is the unit ideal at the generic
point of `Y`. -/
theorem subvarietyTrivial_idealVal_eq_zero_iff (𝔞 : X.IdealSheafData) (y : X) :
    (subvarietyTrivial f y).idealVal 𝔞 = 0 ↔ stalkIdeal 𝔞 y = ⊤ := by
  rw [BerkovichPoint.idealVal_eq_zero_iff, center_subvarietyTrivial]

theorem subvarietyTrivial_idealVal_eq_zero_or_top (𝔞 : X.IdealSheafData) (y : X) :
    (subvarietyTrivial f y).idealVal 𝔞 = 0 ∨ (subvarietyTrivial f y).idealVal 𝔞 = ⊤ := by
  obtain ⟨g, -, hg⟩ := (subvarietyTrivial f y).exists_idealVal_eq 𝔞
  rw [hg, BerkovichPoint.centerValENN, BerkovichPoint.centerVal]
  rcases subvarietyTrivial_valAt_eq_zero_or_top (f := f) y _ with h | h <;> rw [h]
  · exact Or.inl (by simp [toENNReal])
  · exact Or.inr (by simp [toENNReal])

omit [IsLocallyNoetherian X] in
/-- If `𝔞` vanishes at the generic point of `Y` (i.e. along `Y`), then `w(𝔞) = ∞` for every
semi-valuation `w` supported in `Y`. -/
theorem idealVal_eq_top_of_specializes {𝔞 : X.IdealSheafData} {y : X}
    (h𝔞 : stalkIdeal 𝔞 y ≠ ⊤) {w : BerkovichPoint f} (hw : w ∈ subvarietyAn f y) :
    w.idealVal 𝔞 = ⊤ := by
  have hker : stalkIdeal 𝔞 w.center ≤
      RingHom.ker (BerkovichPoint.specializationMap w.support_specializes_center).hom := by
    apply iSup₂_le
    intro U hU
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    rw [Ideal.mem_comap, RingHom.mem_ker]
    have hwU : w.support ∈ (U : X.Opens) :=
      w.support_specializes_center.mem_open (U : X.Opens).isOpen hU
    have heq : (BerkovichPoint.specializationMap w.support_specializes_center).hom
        ((X.presheaf.germ U w.center hU).hom r) = X.evaluation U w.support hwU r := by
      rw [BerkovichPoint.specializationMap, ← Scheme.germ_residue, ← TopCat.Presheaf.germ_stalkSpecializes
        X.presheaf hU w.support_specializes_center]
      rfl
    rw [heq, Scheme.evaluation_eq_zero_iff_notMem_basicOpen]
    intro hb
    have hyb : y ∈ X.basicOpen r := (show y ⤳ w.support from hw).mem_open
      (X.basicOpen r).isOpen hb
    exact h𝔞 ((stalkIdeal_eq_top_iff 𝔞 y).mpr ⟨U, r, hr, hyb⟩)
  apply top_le_iff.mp
  apply le_iInf₂
  intro g hg
  have h0 := hker hg
  rw [RingHom.mem_ker] at h0
  simp [BerkovichPoint.centerValENN, BerkovichPoint.centerVal, h0, BerkovichPoint.valAt_zero,
    toENNReal]

/-- `v_{Y,triv}(𝔞) = ∞` iff `𝔞` vanishes at the generic point of `Y`. -/
theorem subvarietyTrivial_idealVal_eq_top_iff (𝔞 : X.IdealSheafData) (y : X) :
    (subvarietyTrivial f y).idealVal 𝔞 = ⊤ ↔ stalkIdeal 𝔞 y ≠ ⊤ := by
  constructor
  · intro h htop
    rw [(subvarietyTrivial_idealVal_eq_zero_iff 𝔞 y).mpr htop] at h
    exact ENNReal.zero_ne_top h
  · intro h
    exact idealVal_eq_top_of_specializes h (subvarietyTrivial_mem_subvarietyAn y)

end Point

/-! ### Complex points of a subvariety -/

section ComplexPoints

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ))

/-- `Y(ℂ) ⊆ X(ℂ)`: the complex points of `Y = closure {y}`. -/
def subvarietyPoints (y : X) : Set (SchemeComplexPoint f) :=
  {q | y ⤳ schemeComplexPointImage f q}

variable {f}

/-- Complex points are dense in every subvariety: every open set meeting `Y = closure {y}`
(i.e. containing `y`) contains a complex point of `Y` (Nullstellensatz). -/
theorem exists_mem_subvarietyPoints [LocallyOfFiniteType f] {y : X} {W : X.Opens} (hy : y ∈ W) :
    ∃ q ∈ subvarietyPoints f y, schemeComplexPointImage f q ∈ W := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hyV, hVW⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hy W.isOpen
  set P := hV.primeIdealOf ⟨y, hyV⟩
  obtain ⟨M, hM, hPM⟩ := Ideal.exists_le_maximal P.asIdeal P.isPrime.ne_top
  obtain ⟨q, hq⟩ := exists_schemeComplexPoint_fromSpec f hV M hM
  refine ⟨q, ?_, ?_⟩
  · show y ⤳ schemeComplexPointImage f q
    have hy' : hV.fromSpec P = y := hV.fromSpec_primeIdealOf ⟨y, hyV⟩
    rw [hq, ← hy']
    exact ((PrimeSpectrum.le_iff_specializes P ⟨M, hM.isPrime⟩).mp hPM).map
      hV.fromSpec.continuous
  · rw [hq]
    apply hVW
    rw [← hV.range_fromSpec]
    exact ⟨_, rfl⟩

end ComplexPoints

/-! ### Multiplier ideals along a subvariety -/

section Multiplier

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} {n : ℕ} [SmoothOfRelativeDimension n f]
  {E : ClosedProjectiveEmbedding f} [IsProper f]

local instance nansPointTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance nansPointCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance nansPointManifold : IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n

/-- **The algebraic model of `𝓘(cφ)` along `Y`**: for quasi-psh `φ` and `c > 0`, the algebraic
coherent ideal `𝔞` with `𝔞^an = 𝓘(cφ)` is the unit ideal at the generic point of `Y` iff
`1 ∈ 𝓘(cφ)_q` (`e^{-cφ}` is integrable near `q`) for some complex point `q ∈ Y(ℂ)`. -/
theorem stalkIdeal_algebraization_multiplierIdeal_eq_top_iff {φ : SchemeComplexPoint f → EReal}
    (hφ : IsGlobalQuasiPshPotential (n := n) φ) {c : ℝ} (hc : 0 < c) (y : X) :
    stalkIdeal (algebraization f n E (multiplierIdeal (n := n) c φ)) y = ⊤ ↔
      ∃ q ∈ subvarietyPoints f y, (multiplierIdeal (n := n) c φ).mem q (fun _ => 1) := by
  have := E.locallyOfFiniteType
  have hAn := analytificationIdeal_algebraization_eq f n E
    (SGPT.GAGA.H0S.multiplierIdealAlgebraic f E n) hφ hc
  set 𝔞 := algebraization f n E (multiplierIdeal (n := n) c φ)
  constructor
  · intro h
    obtain ⟨U, r, hr, hyb⟩ := (stalkIdeal_eq_top_iff 𝔞 y).mp h
    obtain ⟨q, hyq, hqb⟩ := exists_mem_subvarietyPoints (f := f) hyb
    have hqU : schemeComplexPointImage f q ∈ (U : X.Opens) := X.basicOpen_le r hqb
    have hne := (SGPT.GAGA.H0S.schemeOpenRegularFunction_ne_zero_iff f E n U r q hqU).mpr hqb
    have hmem : (analytificationIdeal f n E 𝔞).mem q (schemeOpenRegularFunction f n E U r) := by
      refine ⟨schemeOpenRegularFunction_holomorphicAt f n E U r q hqU, 1,
        fun _ => schemeOpenRegularFunction f n E U r, fun _ => fun _ => 1, ?_, ?_, ?_⟩
      · intro _
        exact ⟨U, hqU, r, hr, rfl⟩
      · intro _
        exact holomorphicAt_const 1
      · filter_upwards with z
        simp
    rw [hAn] at hmem
    exact ⟨q, hyq, SkodaIntegrability.one_mem_multiplierIdeal_of_notMem_zeroLocus
      fun hz => hne (hz _ hmem)⟩
  · rintro ⟨q, hyq, h1⟩
    rw [← hAn] at h1
    obtain ⟨-, N, s, a, hs, -, hsum⟩ := h1
    have hval : ∑ i, a i q * s i q = 1 := hsum.self_of_nhds.symm
    obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero
      (show ∑ i, a i q * s i q ≠ 0 by rw [hval]; exact one_ne_zero)
    have hsi : s i q ≠ 0 := right_ne_zero_of_mul hi
    obtain ⟨U, hqU, r, hr, hsr⟩ := hs i
    rw [hsr] at hsi
    have hb := (SGPT.GAGA.H0S.schemeOpenRegularFunction_ne_zero_iff f E n U r q hqU).mp hsi
    have hyb : y ∈ X.basicOpen r := (show y ⤳ schemeComplexPointImage f q from hyq).mem_open
      (X.basicOpen r).isOpen hb
    exact (stalkIdeal_eq_top_iff 𝔞 y).mpr ⟨U, r, hr, hyb⟩

end Multiplier

/-! ### Generic Lelong numbers along an arbitrary family of points -/

section GenericLelong

open NonKahlerLocus SourceTraceRepresentativeDefinition

variable {n : ℕ} {M V : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- If `u ⪯_𝓘 v` (`u` `θ`-psh) and `ν(u, Y) = 0`, then `ν(v, Y) = 0`, for the generic Lelong
number along an arbitrary family of points `ι : V → M` (Skoda's integrability theorem and the
unit-multiplier Lelong bound; the smooth-target version is `SGPT.Trace`'s
`sourceGenericLelongNumber_eq_zero_of_iOrder`). -/
theorem genericLelong_eq_zero_of_iOrder (hn : 0 < n) {θ : ClosedRealOneOneForm n M}
    {u v : M → EReal} (hu : IsThetaPshPotential θ.val u)
    (huv : FirstPass.IEnvelope.IOrderOnManifold (n := n) u v) {ι : V → M}
    (hgen : sourceGenericLelongNumber (n := n) ι u = 0) :
    sourceGenericLelongNumber (n := n) ι v = 0 := by
  have hgenN := (nativeGeneric_zero_iff_source hn.ne' ι u).mpr hgen
  apply (nativeGeneric_zero_iff_source hn.ne' ι v).mp
  apply le_antisymm _ bot_le
  apply ENNReal.le_of_forall_pos_le_add
  intro δ hδ _
  let F : ℝ := (Module.finrank ℝ (ComplexModel n) : ℝ)
  have hF : 0 ≤ F := Nat.cast_nonneg _
  have hδR : (0 : ℝ) < δ := by exact_mod_cast hδ
  let c : ℝ := F / δ + 1
  have hc : 0 < c := by positivity
  have hFc : F / c ≤ δ := by
    rw [div_le_iff₀ hc]
    have : F = δ * (F / δ) := by field_simp
    nlinarith
  have hlt : (⨅ y : V, lelongNumber (n := n) u (ι y)) < ENNReal.ofReal (2 / c) := by
    rw [hgenN]
    exact ENNReal.ofReal_pos.mpr (div_pos two_pos hc)
  obtain ⟨y, hy⟩ := iInf_lt_iff.mp hlt
  have hmem₀ : (multiplierIdeal (n := n) c u).mem (ι y) (fun _ => (1 : ℂ)) :=
    SkodaIntegrability.one_mem_multiplierIdeal_of_lelongNumber_lt hu.1 hc hy
  have hmem : (multiplierIdeal (n := n) c v).mem (ι y) (fun _ => (1 : ℂ)) :=
    PositiveCurrentTraceMultiplier.multiplierIdeal_le_of_iOrderOnManifold huv hc _ _ hmem₀
  have hbound := ActualUnitMultiplierLelongBound.lelongNumber_le_of_unit_multiplierIdeal hn hmem
  calc (⨅ y', lelongNumber (n := n) v (ι y'))
      ≤ lelongNumber (n := n) v (ι y) := iInf_le _ y
    _ ≤ ENNReal.ofReal (F / c) := hbound
    _ ≤ 0 + (δ : ℝ≥0∞) := by
      rw [zero_add]
      exact (ENNReal.ofReal_le_ofReal hFc).trans_eq (ENNReal.ofReal_coe_nnreal)

end GenericLelong

/-! ### `φ^An` at `v_{Y,triv}` and on `Y^An` -/

section Potential

open NonKahlerLocus SourceTraceRepresentativeDefinition

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} {m : ℕ} [SmoothOfRelativeDimension (m + 1) f]
  {E : ClosedProjectiveEmbedding f} [IsProper f]

local instance nansPotPointTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance nansPotPointCharts : ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (m + 1)
local instance nansPotPointManifold : IsComplexManifold (m + 1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (m + 1)

/-- `ν(φ, Y) = 0` gives, for every `c > 0`, a point `q ∈ Y(ℂ)` with `1 ∈ 𝓘(cφ)_q` (Skoda). -/
theorem exists_one_mem_of_genericLelong_eq_zero {φ : SchemeComplexPoint f → EReal}
    {θ : SmoothRealForm (m + 1) (SchemeComplexPoint f) 2} (hφ : IsThetaPshPotential θ φ) {y : X}
    (h0 : sourceGenericLelongNumber (n := m + 1)
      (Subtype.val : subvarietyPoints f y → SchemeComplexPoint f) φ = 0)
    {c : ℝ} (hc : 0 < c) :
    ∃ q ∈ subvarietyPoints f y, (multiplierIdeal (n := m + 1) c φ).mem q (fun _ => 1) := by
  rw [← nativeGeneric_zero_iff_source (Nat.succ_ne_zero m)] at h0
  have hlt : (⨅ q : subvarietyPoints f y, lelongNumber (n := m + 1) φ q) <
      ENNReal.ofReal (2 / c) := by
    rw [h0]
    exact ENNReal.ofReal_pos.mpr (div_pos two_pos hc)
  obtain ⟨q, hq⟩ := iInf_lt_iff.mp hlt
  exact ⟨q.1, q.2, SkodaIntegrability.one_mem_multiplierIdeal_of_lelongNumber_lt hφ.1 hc hq⟩

/-- `ν(φ, Y) > 0` gives `c₀ > 0` such that `1 ∉ 𝓘(cφ)_q` for every `c ≥ c₀` and `q ∈ Y(ℂ)`
(the unit-multiplier Lelong bound `ν(φ, q) ≤ 2 dim / c`). -/
theorem exists_forall_not_one_mem_of_genericLelong_ne_zero {φ : SchemeComplexPoint f → EReal}
    {y : X} (hν : sourceGenericLelongNumber (n := m + 1)
      (Subtype.val : subvarietyPoints f y → SchemeComplexPoint f) φ ≠ 0) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ c : ℝ, c₀ ≤ c → ∀ q ∈ subvarietyPoints f y,
      ¬ (multiplierIdeal (n := m + 1) c φ).mem q (fun _ => 1) := by
  have h' : (⨅ q : subvarietyPoints f y, lelongNumber (n := m + 1) φ q) ≠ 0 := by
    rwa [Ne, nativeGeneric_zero_iff_source (Nat.succ_ne_zero m)]
  obtain ⟨r, -, hr1, hr2⟩ := ENNReal.lt_iff_exists_real_btwn.mp (pos_iff_ne_zero.mpr h')
  have hr : 0 < r := ENNReal.ofReal_pos.mp hr1
  set F : ℝ := (Module.finrank ℝ (ComplexModel (m + 1)) : ℝ)
  have hF : 0 ≤ F := Nat.cast_nonneg _
  refine ⟨F / r + 1, by positivity, fun c hc q hq h1 => ?_⟩
  have hcpos : 0 < c := lt_of_lt_of_le (by positivity) hc
  have hb := ActualUnitMultiplierLelongBound.lelongNumber_le_of_unit_multiplierIdeal
    (Nat.succ_pos m) h1
  have hFc : F / c < r := by
    rw [div_lt_iff₀ hcpos]
    have h1 : r * (F / r + 1) ≤ r * c := mul_le_mul_of_nonneg_left hc hr.le
    have h2 : r * (F / r + 1) = F + r := by field_simp
    linarith
  have hle : (⨅ q' : subvarietyPoints f y, lelongNumber (n := m + 1) φ q') ≤
      lelongNumber (n := m + 1) φ q :=
    iInf_le (fun q' : subvarietyPoints f y => lelongNumber (n := m + 1) φ q') ⟨q, hq⟩
  have : ENNReal.ofReal r < ENNReal.ofReal r :=
    calc ENNReal.ofReal r < _ := hr2
      _ ≤ lelongNumber (n := m + 1) φ q := hle
      _ ≤ ENNReal.ofReal (F / c) := hb
      _ < ENNReal.ofReal r := (ENNReal.ofReal_lt_ofReal_iff hr).mpr hFc
  exact lt_irrefl _ this

/-- **`φ^An(v_{Y,triv}) = 0` if `ν(φ, Y) = 0`** (proof of `lma:non-trivrest`). -/
theorem potentialAn_subvarietyTrivial_of_eq_zero {φ : SchemeComplexPoint f → EReal}
    {θ : SmoothRealForm (m + 1) (SchemeComplexPoint f) 2} (hφ : IsThetaPshPotential θ φ) {y : X}
    (h0 : sourceGenericLelongNumber (n := m + 1)
      (Subtype.val : subvarietyPoints f y → SchemeComplexPoint f) φ = 0) :
    potentialAn (m + 1) E φ (subvarietyTrivial f y) = 0 := by
  have := E.locallyOfFiniteType
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hq : IsGlobalQuasiPshPotential (n := m + 1) φ := ⟨hφ.1.quasiPlurisubharmonic, hφ.2⟩
  have h1 := BerkovichPoint.tendsto_potentialVal_of_multiplierIdealAlgebraic (m + 1) E
    (SGPT.GAGA.H0S.multiplierIdealAlgebraic f E (m + 1)) hφ (subvarietyTrivial f y)
  have h2 : Tendsto (fun j : ℕ => (subvarietyTrivial f y).multiplierIdealVal (m + 1) E φ j / j)
      atTop (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with j hj
    have hjpos : (0 : ℝ) < j := by exact_mod_cast hj
    unfold BerkovichPoint.multiplierIdealVal
    rw [(subvarietyTrivial_idealVal_eq_zero_iff _ y).mpr
      ((stalkIdeal_algebraization_multiplierIdeal_eq_top_iff hq hjpos y).mpr
        (exists_one_mem_of_genericLelong_eq_zero hφ h0 hjpos)), ENNReal.zero_div]
  unfold potentialAn
  rw [tendsto_nhds_unique h1 h2]
  simp

/-- **`φ^An ≡ -∞` on `Y^An` if `ν(φ, Y) > 0`**; in particular `φ^An(v_{Y,triv}) = -∞` (proof of
`lma:non-trivrest`). -/
theorem potentialAn_eq_bot_of_ne_zero {φ : SchemeComplexPoint f → EReal}
    {θ : SmoothRealForm (m + 1) (SchemeComplexPoint f) 2} (hφ : IsThetaPshPotential θ φ) {y : X}
    (hν : sourceGenericLelongNumber (n := m + 1)
      (Subtype.val : subvarietyPoints f y → SchemeComplexPoint f) φ ≠ 0)
    {w : BerkovichPoint f} (hw : w ∈ subvarietyAn f y) :
    potentialAn (m + 1) E φ w = ⊥ := by
  have := E.locallyOfFiniteType
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hq : IsGlobalQuasiPshPotential (n := m + 1) φ := ⟨hφ.1.quasiPlurisubharmonic, hφ.2⟩
  obtain ⟨c₀, hc₀, hnot⟩ := exists_forall_not_one_mem_of_genericLelong_ne_zero hν
  have h1 := BerkovichPoint.tendsto_potentialVal_of_multiplierIdealAlgebraic (m + 1) E
    (SGPT.GAGA.H0S.multiplierIdealAlgebraic f E (m + 1)) hφ w
  have h2 : Tendsto (fun j : ℕ => w.multiplierIdealVal (m + 1) E φ j / j) atTop (𝓝 ⊤) := by
    refine tendsto_const_nhds.congr' ?_
    obtain ⟨N, hN⟩ := exists_nat_ge c₀
    filter_upwards [eventually_ge_atTop N] with j hj
    have hjc : c₀ ≤ (j : ℝ) := le_trans hN (by exact_mod_cast hj)
    have hjpos : (0 : ℝ) < j := lt_of_lt_of_le hc₀ hjc
    have hstalk : stalkIdeal (algebraization f (m + 1) E
        (multiplierIdeal (n := m + 1) (j : ℝ) φ)) y ≠ ⊤ := by
      intro htop
      obtain ⟨q, hqY, h1q⟩ :=
        (stalkIdeal_algebraization_multiplierIdeal_eq_top_iff hq hjpos y).mp htop
      exact hnot j hjc q hqY h1q
    unfold BerkovichPoint.multiplierIdealVal
    rw [idealVal_eq_top_of_specializes hstalk hw,
      ENNReal.top_div_of_ne_top (ENNReal.natCast_ne_top j)]
  unfold potentialAn
  rw [tendsto_nhds_unique h1 h2]
  simp

/-- **Source, proof of `lma:non-trivrest`**: for `φ ∈ PSH(X, θ)`,
`φ^An(v_{Y,triv}) = 0` if `ν(φ, Y) = 0` and `φ^An(v_{Y,triv}) = -∞` if `ν(φ, Y) > 0`. -/
theorem potentialAn_subvarietyTrivial {φ : SchemeComplexPoint f → EReal}
    {θ : SmoothRealForm (m + 1) (SchemeComplexPoint f) 2} (hφ : IsThetaPshPotential θ φ)
    (y : X) :
    potentialAn (m + 1) E φ (subvarietyTrivial f y) =
      if sourceGenericLelongNumber (n := m + 1)
        (Subtype.val : subvarietyPoints f y → SchemeComplexPoint f) φ = 0 then 0 else ⊥ := by
  split_ifs with h
  · exact potentialAn_subvarietyTrivial_of_eq_zero hφ h
  · exact potentialAn_eq_bot_of_ne_zero hφ h (subvarietyTrivial_mem_subvarietyAn y)

/-- The maximum principle for `φ^An` on `Y^An`: `φ^An(w) ≤ φ^An(v_{Y,triv})` for every
semi-valuation `w` supported in `Y`. -/
theorem potentialAn_le_subvarietyTrivial {φ : SchemeComplexPoint f → EReal}
    {θ : SmoothRealForm (m + 1) (SchemeComplexPoint f) 2} (hφ : IsThetaPshPotential θ φ)
    {y : X} {w : BerkovichPoint f} (hw : w ∈ subvarietyAn f y) :
    potentialAn (m + 1) E φ w ≤ potentialAn (m + 1) E φ (subvarietyTrivial f y) := by
  by_cases h : sourceGenericLelongNumber (n := m + 1)
      (Subtype.val : subvarietyPoints f y → SchemeComplexPoint f) φ = 0
  · rw [potentialAn_subvarietyTrivial_of_eq_zero hφ h]
    exact potentialAn_nonpos (m + 1) E φ w
  · rw [potentialAn_eq_bot_of_ne_zero hφ h hw]
    exact bot_le

end Potential

/-! ### Non-Archimedean potentials: `lma:non-trivrest` -/

section NA

open SourceTraceRepresentativeDefinition

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} {m : ℕ} [SmoothOfRelativeDimension (m + 1) f]
  {E : ClosedProjectiveEmbedding f} [IsProper f]

local instance nansNAPointTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance nansNAPointCharts : ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (m + 1)
local instance nansNAPointManifold : IsComplexManifold (m + 1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (m + 1)

variable [MeasurableSpace (SchemeComplexPoint f)] [BorelSpace (SchemeComplexPoint f)]
  [CompactSpace (SchemeComplexPoint f)] [ConnectedSpace (SchemeComplexPoint f)]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel (m + 1) (SchemeComplexPoint f))}

variable (f) in
/-- The inclusion `Y(ℂ) → X(ℂ)` of the complex points of `Y = closure {y}`. -/
abbrev subvarietyInclusion (y : X) : subvarietyPoints f y → SchemeComplexPoint f :=
  Subtype.val

/-- `ν(Γ^{θ+ω}_τ, Y) = 0` does not depend on the Kähler index `ω` (for an arbitrary family of
points `ι`, e.g. a singular `Y(ℂ)`). -/
theorem sliceTraceable_index {V : Type} (ι : V → SchemeComplexPoint f) (Γ : SourceNAPotential θ)
    {κ ζ : SourceKahlerForm (m + 1) (SchemeComplexPoint f)} {τ : ℝ}
    (h : NATrace.SliceTraceable ι Γ κ τ) : NATrace.SliceTraceable ι Γ ζ τ := by
  obtain ⟨hτ, h0⟩ := h
  have hτ' : τ < (Γ.component ζ).val.max := by rwa [Γ.component_max_eq ζ κ]
  have he := NATrace.component_potential_iEquivalent Γ κ ζ τ hτ hτ'
  exact ⟨hτ', genericLelong_eq_zero_of_iOrder (Nat.succ_pos m)
    ((Γ.component κ).val.native_thetaPSH ⟨τ, hτ⟩)
    ((sourceIOrder_iff_native he.1.1 he.1.2.1).mp he.1) h0⟩

/-- `ν(Γ^{θ+ω}_τ, Y) = 0` descends to smaller parameters. -/
theorem sliceTraceable_of_le {V : Type} (ι : V → SchemeComplexPoint f) (Γ : SourceNAPotential θ)
    (κ : SourceKahlerForm (m + 1) (SchemeComplexPoint f)) {τ τ' : ℝ}
    (h : NATrace.SliceTraceable ι Γ κ τ') (hle : τ ≤ τ') : NATrace.SliceTraceable ι Γ κ τ := by
  obtain ⟨hτ', h0⟩ := h
  have hτ : τ < (Γ.component κ).val.max := lt_of_le_of_lt hle hτ'
  refine ⟨hτ, ?_⟩
  have hmono : ∀ x, (Γ.component κ).val.potential ⟨τ', hτ'⟩ x ≤
      (Γ.component κ).val.potential ⟨τ, hτ⟩ x := fun x =>
    (Γ.component κ).val.antitone x (show (⟨τ, hτ⟩ : Iio _) ≤ ⟨τ', hτ'⟩ from hle)
  exact genericLelong_eq_zero_of_iOrder (Nat.succ_pos m)
    ((Γ.component κ).val.native_thetaPSH ⟨τ', hτ'⟩)
    (iOrderOnManifold_of_le_add (C := 0)
      ((Γ.component κ).val.native_thetaPSH ⟨τ, hτ⟩).1.quasiPlurisubharmonic
      (fun x => by simpa only [EReal.coe_zero, add_zero] using hmono x)) h0

/-- The restriction of `Γ` to `Y` is well defined iff `ν(Γ^{θ+ω}_τ, Y) = 0` for one parameter
`τ < Γ_max`, at one (equivalently every) Kähler index `ω`. -/
theorem traceWellDefined_iff_exists {V : Type} (ι : V → SchemeComplexPoint f)
    (Γ : SourceNAPotential θ) (ω : SourceKahlerForm (m + 1) (SchemeComplexPoint f)) :
    NATrace.TraceWellDefined ι Γ ↔ ∃ τ, NATrace.SliceTraceable ι Γ ω τ := by
  constructor
  · intro h
    obtain ⟨τ₀, hτ₀⟩ := h ω
    exact ⟨τ₀ - 1, hτ₀ _ (by linarith)⟩
  · rintro ⟨τ, hτ⟩ κ
    exact ⟨τ, fun τ' hτ' => sliceTraceable_of_le ι Γ κ (sliceTraceable_index ι Γ hτ) hτ'.le⟩

/-- A slice with `ν(Γ_τ, Y) = 0` contributes `τ` to `Γ^An(v_{Y,triv})`. -/
theorem slice_term_of_sliceTraceable (Γ : SourceNAPotential θ)
    (ω : SourceKahlerForm (m + 1) (SchemeComplexPoint f)) (y : X)
    (τ : Iio (Γ.component ω).val.max)
    (h : NATrace.SliceTraceable (subvarietyInclusion f y) Γ ω τ) :
    potentialAn (m + 1) E ((Γ.component ω).val.potential τ) (subvarietyTrivial f y) +
      ((τ : ℝ) : EReal) = ((τ : ℝ) : EReal) := by
  rw [potentialAn_subvarietyTrivial_of_eq_zero
    (naComponent_potential_isThetaPshPotential (m + 1) Γ ω τ) h.2, zero_add]

/-- A slice with `ν(Γ_τ, Y) > 0` contributes `-∞` to `Γ^An(v_{Y,triv})`. -/
theorem slice_term_of_not_sliceTraceable (Γ : SourceNAPotential θ)
    (ω : SourceKahlerForm (m + 1) (SchemeComplexPoint f)) (y : X)
    (τ : Iio (Γ.component ω).val.max)
    (h : ¬ NATrace.SliceTraceable (subvarietyInclusion f y) Γ ω τ) :
    potentialAn (m + 1) E ((Γ.component ω).val.potential τ) (subvarietyTrivial f y) +
      ((τ : ℝ) : EReal) = ⊥ := by
  rw [potentialAn_eq_bot_of_ne_zero (naComponent_potential_isThetaPshPotential (m + 1) Γ ω τ)
    (fun h0 => h ⟨τ.2, h0⟩) (subvarietyTrivial_mem_subvarietyAn y), EReal.bot_add]

/-- **(1) ⟺ (3) of `lma:non-trivrest`**: `Γ^An(v_{Y,triv}) ≠ -∞` iff `ν(Γ^{θ+ω}_τ, Y) = 0` for
some `τ < Γ_max`. -/
theorem naPotentialAnAt_subvarietyTrivial_ne_bot_iff_exists (Γ : SourceNAPotential θ)
    (ω : SourceKahlerForm (m + 1) (SchemeComplexPoint f)) (y : X) :
    naPotentialAnAt (m + 1) E Γ ω (subvarietyTrivial f y) ≠ ⊥ ↔
      ∃ τ, NATrace.SliceTraceable (subvarietyInclusion f y) Γ ω τ := by
  unfold naPotentialAnAt
  rw [Ne, iSup_eq_bot]
  constructor
  · intro h
    push Not at h
    obtain ⟨τ, hτ⟩ := h
    by_contra hcon
    exact hτ (slice_term_of_not_sliceTraceable Γ ω y τ (fun h' => hcon ⟨τ, h'⟩))
  · rintro ⟨τ, hτ⟩ hall
    have h1 := hall ⟨τ, hτ.1⟩
    rw [slice_term_of_sliceTraceable Γ ω y ⟨τ, hτ.1⟩ hτ] at h1
    exact EReal.coe_ne_bot τ h1

/-- `lma:non-trivrest`, (1) ⟺ (3): `Γ^An(v_{Y,triv}) ≠ -∞` iff `Γ` has a well-defined
restriction to `Y`. -/
theorem naPotentialAnAt_subvarietyTrivial_ne_bot_iff (Γ : SourceNAPotential θ)
    (ω : SourceKahlerForm (m + 1) (SchemeComplexPoint f)) (y : X) :
    naPotentialAnAt (m + 1) E Γ ω (subvarietyTrivial f y) ≠ ⊥ ↔
      NATrace.TraceWellDefined (subvarietyInclusion f y) Γ :=
  (naPotentialAnAt_subvarietyTrivial_ne_bot_iff_exists Γ ω y).trans
    (traceWellDefined_iff_exists _ Γ ω).symm

/-- **The maximum principle on `Y^An`** (`[BJ22, Lemma 1.4(i)]` in the proof of
`lma:non-trivrest`): `Γ^An(w) ≤ Γ^An(v_{Y,triv})` for every semi-valuation `w` supported in
`Y`. -/
theorem naPotentialAnAt_le_subvarietyTrivial (Γ : SourceNAPotential θ)
    (ω : SourceKahlerForm (m + 1) (SchemeComplexPoint f)) {y : X} {w : BerkovichPoint f}
    (hw : w ∈ subvarietyAn f y) :
    naPotentialAnAt (m + 1) E Γ ω w ≤ naPotentialAnAt (m + 1) E Γ ω (subvarietyTrivial f y) :=
  iSup_mono fun τ => add_le_add (potentialAn_le_subvarietyTrivial
    (naComponent_potential_isThetaPshPotential (m + 1) Γ ω τ) hw) le_rfl

/-- **Source `lma:non-trivrest`**: for `Γ ∈ PSH^NA(X, θ)` and the irreducible subvariety
`Y = closure {y}` of `X`, the following are equivalent:
1. `Γ^An(v_{Y,triv}) ≠ -∞`;
2. `Γ^An|_{Y^An} ≢ -∞`;
3. `Γ` has a well-defined restriction (trace) to `Y`: `ν(Γ^{θ+ω'}_τ, Y) = 0` for all sufficiently
   negative `τ` and every Kähler form `ω'`.

Here `Γ^An` is `eq:psiandef` evaluated on `X^An` at the Kähler index `ω`. -/
theorem source_nonTrivRest (Γ : SourceNAPotential θ)
    (ω : SourceKahlerForm (m + 1) (SchemeComplexPoint f)) (y : X) :
    List.TFAE [naPotentialAnAt (m + 1) E Γ ω (subvarietyTrivial f y) ≠ ⊥,
      ∃ w ∈ subvarietyAn f y, naPotentialAnAt (m + 1) E Γ ω w ≠ ⊥,
      NATrace.TraceWellDefined (subvarietyInclusion f y) Γ] := by
  tfae_have 1 → 2 := fun h => ⟨_, subvarietyTrivial_mem_subvarietyAn y, h⟩
  tfae_have 2 → 1 := by
    rintro ⟨w, hw, h⟩ hbot
    apply h
    have hle := naPotentialAnAt_le_subvarietyTrivial (E := E) Γ ω hw
    rw [hbot] at hle
    exact le_bot_iff.mp hle
  tfae_have 1 ↔ 3 := naPotentialAnAt_subvarietyTrivial_ne_bot_iff Γ ω y
  tfae_finish

/-- When the restriction of `Γ` to `Y` is well defined, `Γ^An(v_{Y,triv}) = (Tr_Y Γ)_max`
(`def:NApotential:L623`); this is the endpoint identity used in the proof of
`thm:comp_traceop`. -/
theorem naPotentialAnAt_subvarietyTrivial_eq_traceCutoff (Γ : SourceNAPotential θ)
    (ω : SourceKahlerForm (m + 1) (SchemeComplexPoint f)) (y : X)
    (hwd : NATrace.TraceWellDefined (subvarietyInclusion f y) Γ) :
    naPotentialAnAt (m + 1) E Γ ω (subvarietyTrivial f y) =
      ((NATrace.traceCutoff (subvarietyInclusion f y) Γ ω : ℝ) : EReal) := by
  have hne := NATrace.traceCutoff_set_nonempty hwd ω
  have hbdd := NATrace.traceCutoff_set_bddAbove (subvarietyInclusion f y) Γ ω
  apply le_antisymm
  · refine iSup_le fun τ => ?_
    by_cases h : NATrace.SliceTraceable (subvarietyInclusion f y) Γ ω τ
    · rw [slice_term_of_sliceTraceable Γ ω y τ h]
      exact EReal.coe_le_coe_iff.mpr (le_csSup hbdd h)
    · rw [slice_term_of_not_sliceTraceable Γ ω y τ h]
      exact bot_le
  · by_contra hcon
    rw [not_le] at hcon
    obtain ⟨q, hSq, hq⟩ := EReal.lt_iff_exists_real_btwn.mp hcon
    have hq' : q < NATrace.traceCutoff (subvarietyInclusion f y) Γ ω := EReal.coe_lt_coe_iff.mp hq
    obtain ⟨s, hs, hqs⟩ := exists_lt_of_lt_csSup hne hq'
    have hqT : NATrace.SliceTraceable (subvarietyInclusion f y) Γ ω q :=
      sliceTraceable_of_le _ Γ ω hs hqs.le
    have hterm := le_iSup (fun τ : Iio (Γ.component ω).val.max =>
      potentialAn (m + 1) E ((Γ.component ω).val.potential τ) (subvarietyTrivial f y) +
        ((τ : ℝ) : EReal)) ⟨q, hqT.1⟩
    rw [slice_term_of_sliceTraceable Γ ω y ⟨q, hqT.1⟩ hqT] at hterm
    exact absurd hSq (not_lt.mpr hterm)

end NA

end SGPT.NAPotential.NANS

end
