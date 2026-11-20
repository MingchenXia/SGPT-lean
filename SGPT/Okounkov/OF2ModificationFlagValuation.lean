import SGPT.Okounkov.OF2AbhyankarShear
import SGPT.Okounkov.SchemeOriginalFunctionFieldValuation
import SGPT.Okounkov.FlagValuationEndpointCenter
import SGPT.Okounkov.IntrinsicModificationRestriction
import SGPT.Foundations.Analysis.Pending.MultiplierPullbackNonzero

/-!
# Flag valuations on modifications, read on `ℂ(X)`

Source: chapter *The theory of Okounkov bodies*, Section *Flags and valuations*, `rmk:Abhyankar`
("… a valuation induced by an admissible flag on a modification of `X`") and `rmk:valcurr`
("take a resolution `π : Y → X` such that there is a smooth flag `Y•` on `Y` … `ν = ν_{Y•} g`").

Let `X` be an integral smooth projective complex scheme of dimension `n`, `X(ℂ)` its complex
manifold, `π : X' → X(ℂ)` an analytic modification (`IsAnalyticModification`; every finite
sequence of blow-ups with smooth centres is one, `isAnalyticModification_of_isBlowupSequence`)
from a compact connected Kähler manifold `X'` carrying a smooth flag `W•` (bundled as an
`OriginalFlagGeometry`). The flag valuation `ν_{W•}` of meromorphic germs at the flag point `w`
induces a valuation of `ℂ(X)`:

`modificationFlagValuation F hπ (q) = ν_{W•}(π^* q)`, where `π^* q` is the pull-back of the
meromorphic germ of `q` at `π(w)`.

It is well defined because a modification does not collapse nonzero holomorphic germs
(`nativeHolGerm_comap_injective`). On the local ring `𝒪_{X,π(w)}` its values are flag vectors of
holomorphic germs, so it is coordinatewise nonnegative there
(`isCoordNonnegAt_modificationFlagValuation`); the same holds for the flag valuations of smooth
flags on `X` itself (`isCoordNonnegAt_schemeOriginalFlagFunctionFieldValuation`).

## `rmk:Abhyankar`, "not necessarily equal"

* `exists_lexEquivalent_ne_flagValuations`: for every surjective flag valuation `ν_{Y•}` of a smooth
  flag on `X` (dimension `n ≥ 2`) there is an equivalent valuation `ν' = ν_{Y•} G` (`G = I + N`),
  again of value group `ℤⁿ`, which is not equal to the valuation induced by any smooth flag on `X`
  nor by any smooth flag on any modification of `X`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.Okounkov.OF2

open CategoryTheory AlgebraicGeometry Set Filter SGPT.Foundations.Schemes
open SGPT.Okounkov SGPT.Okounkov.AlgebraicValuation SGPT.Okounkov.ValCurr
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
open scoped Topology Manifold ContDiff

universe u

/-! ### Modifications do not collapse germs -/

section Germs

variable {n : ℕ} {M N : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] [TopologicalSpace N] [ChartedSpace (ComplexModel n) N]
  [IsComplexManifold n N]

/-- The pull-back of holomorphic germs along an analytic modification is injective. -/
theorem nativeHolGerm_comap_injective {π : N → M}
    (hπ : IsAnalyticModification (n := n) π) (y : N) :
    Function.Injective (NativeHolGerm.comap π hπ.1 y) := by
  rw [injective_iff_map_eq_zero]
  intro g hg
  obtain ⟨F, hF, rfl⟩ := NativeHolGerm.exists_eq_mk g
  by_contra hne
  have hfreq : ∃ᶠ x in 𝓝 (π y), F x ≠ 0 := by
    intro hev
    apply hne
    have h0 : (0 : NativeHolGerm n M (π y)) =
        NativeHolGerm.mk (fun _ => (0 : ℂ)) (holomorphicAt_const 0) := rfl
    rw [h0]
    apply NativeHolGerm.mk_eq_mk_iff.mpr
    filter_upwards [hev] with x hx
    exact not_ne_iff.mp hx
  have hcomp := MultiplierPullbackNonzero.frequently_comp_ne_zero hπ y hF hfreq
  apply hcomp
  have h1 : ((NativeHolGerm.comap π hπ.1 y (NativeHolGerm.mk F hF) : NativeHolGerm n N y) :
      Germ (𝓝 y) ℂ) = ((0 : NativeHolGerm n N y) : Germ (𝓝 y) ℂ) := by
    rw [hg]
  rw [NativeHolGerm.comap_mk] at h1
  change ((F ∘ π : N → ℂ) : Germ (𝓝 y) ℂ) = ((fun _ => (0 : ℂ) : N → ℂ) : Germ (𝓝 y) ℂ) at h1
  filter_upwards [Germ.coe_eq.mp h1] with z hz
  exact not_not.mpr hz

end Germs

/-! ### Flag vectors of holomorphic germs are nonnegative -/

/-- Every coordinate of the flag valuation of a holomorphic germ is `≥ 0`: it is an order of
vanishing. -/
theorem originalFlagGermValuation_coord_nonneg {n : ℕ} (F : OriginalFlagGeometry.{u} n)
    (x : OriginalFlagGermPoint F) (h : NativeHolGerm n F.carrier x.1) (w : Lex (Fin n → ℤ))
    (hw : originalFlagGermValuation F x h = (w : WithTop (Lex (Fin n → ℤ)))) (i : Fin n) :
    0 ≤ ofLex w i := by
  by_cases h0 : h = 0
  · rw [h0, (originalFlagGermValuation F x).map_zero] at hw
    exact absurd hw WithTop.top_ne_coe
  rw [originalFlagGermValuation_apply_of_ne_zero F x h h0] at hw
  have hvec := WithTop.coe_injective hw
  rw [← hvec]
  exact Int.natCast_nonneg _

/-! ### The valuation of `ℂ(X)` induced by a flag on a modification -/

section Modification

variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f]

local instance of2ModTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance of2ModCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance of2ModManifold : IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n

/-- The flag point `W_n` of a smooth flag (the last member is a point). -/
def modificationFlagPoint (F : OriginalFlagGeometry.{0} n) : OriginalFlagGermPoint F :=
  Classical.choice inferInstance

variable {n}

/-- Pull-back of meromorphic germs along a modification `π`, at `y` and `π(y)`. -/
def modificationGermFractionMap (F : OriginalFlagGeometry.{0} n)
    {π : F.carrier → SchemeComplexPoint f} (hπ : IsAnalyticModification (n := n) π)
    (y : F.carrier) :
    FractionRing (NativeHolGerm n (SchemeComplexPoint f) (π y)) →+*
      FractionRing (NativeHolGerm n F.carrier y) :=
  IsFractionRing.map (nativeHolGerm_comap_injective hπ y)

omit [IsIntegral X] in
theorem modificationGermFractionMap_algebraMap (F : OriginalFlagGeometry.{0} n)
    {π : F.carrier → SchemeComplexPoint f} (hπ : IsAnalyticModification (n := n) π)
    (y : F.carrier) (g : NativeHolGerm n (SchemeComplexPoint f) (π y)) :
    modificationGermFractionMap f F hπ y (algebraMap _ _ g) =
      algebraMap _ _ (NativeHolGerm.comap π hπ.1 y g) := by
  unfold modificationGermFractionMap IsFractionRing.map
  exact IsLocalization.map_eq _ _

/-- **The valuation of `ℂ(X)` induced by a smooth flag `W•` on a modification `π : X' → X`**:
`q ↦ ν_{W•}(π^* q)`, the flag valuation at the flag point `w` of the pull-back of the meromorphic
germ of `q` at `π(w)`. -/
def modificationFlagValuation (F : OriginalFlagGeometry.{0} n)
    {π : F.carrier → SchemeComplexPoint f} (hπ : IsAnalyticModification (n := n) π) :
    AddValuation X.functionField (WithTop (Lex (Fin n → ℤ))) :=
  (originalFlagGermFractionValuation F (modificationFlagPoint n F)).comap
    ((modificationGermFractionMap f F hπ (modificationFlagPoint n F).1).comp
      (schemeNativeFunctionFieldGerm f n (π (modificationFlagPoint n F).1)))

/-- On functions regular at `π(w)`, the induced valuation is the flag valuation of the pulled-back
holomorphic germ. -/
theorem modificationFlagValuation_stalk (F : OriginalFlagGeometry.{0} n)
    {π : F.carrier → SchemeComplexPoint f} (hπ : IsAnalyticModification (n := n) π)
    (g : X.presheaf.stalk (schemeComplexPointImage f (π (modificationFlagPoint n F).1))) :
    modificationFlagValuation f F hπ (algebraMap _ X.functionField g) =
      originalFlagGermValuation F (modificationFlagPoint n F)
        (NativeHolGerm.comap π hπ.1 _
          (schemeNativeStalkGerm f n (π (modificationFlagPoint n F).1) g)) := by
  change originalFlagGermFractionValuation F (modificationFlagPoint n F)
      (modificationGermFractionMap f F hπ (modificationFlagPoint n F).1
        (schemeNativeFunctionFieldGerm f n (π (modificationFlagPoint n F).1)
          (algebraMap _ X.functionField g))) = _
  rw [schemeNativeFunctionFieldGerm_stalk, modificationGermFractionMap_algebraMap,
    originalFlagGermFractionValuation_algebraMap]

/-- The induced valuation is coordinatewise nonnegative on the local ring of `X` at `π(w)`. -/
theorem isCoordNonnegAt_modificationFlagValuation (F : OriginalFlagGeometry.{0} n)
    {π : F.carrier → SchemeComplexPoint f} (hπ : IsAnalyticModification (n := n) π) :
    IsCoordNonnegAt (modificationFlagValuation f F hπ)
      (schemeComplexPointImage f (π (modificationFlagPoint n F).1)) := by
  intro g w hw i
  rw [modificationFlagValuation_stalk] at hw
  exact originalFlagGermValuation_coord_nonneg F _ _ w hw i

omit [IsIntegral X] in
/-- Finite sequences of blow-ups with smooth centres (the book's modifications) are analytic
modifications, so they induce valuations of `ℂ(X)` as above. -/
theorem isAnalyticModification_of_blowupSequence (F : OriginalFlagGeometry.{0} n)
    {π : F.carrier → SchemeComplexPoint f}
    (hseq : BlowupSequences.IsBlowupSequence n (SchemeComplexPoint f) F.carrier π) :
    IsAnalyticModification (n := n) π :=
  isAnalyticModification_of_isBlowupSequence hseq

end Modification

/-! ### Flags on `X` itself -/

section OnX

variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f]

local instance of2OnXTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance of2OnXCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance of2OnXManifold [IsSeparated f] [QuasiCompact f] :
    IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n

/-- The flag valuation of a smooth flag on `X` is coordinatewise nonnegative on the local ring of
the flag point. -/
theorem isCoordNonnegAt_schemeOriginalFlagFunctionFieldValuation
    (e : ClosedProjectiveEmbedding f)
    (omega : letI := e.isSeparated; letI := e.quasiCompact;
      KahlerBackground n (SchemeComplexPoint f))
    (Y : Fin (n + 1) → Set (SchemeComplexPoint f))
    (hY : letI := e.isSeparated; letI := e.quasiCompact; IsSmoothFlag Y) :
    letI := e.isSeparated
    letI := e.quasiCompact
    IsCoordNonnegAt (schemeOriginalFlagFunctionFieldValuation f n e omega Y hY)
      (schemeComplexPointImage f (schemeProjectiveOriginalFlagPoint f n e omega Y hY).val) := by
  let := e.isSeparated
  let := e.quasiCompact
  intro g w hw i
  rw [schemeOriginalFlagFunctionFieldValuation_stalk] at hw
  exact originalFlagGermValuation_coord_nonneg _ _ _ w hw i

end OnX

/-! ### `rmk:Abhyankar`: equivalent but not equal to any flag valuation -/

section NotEqual

variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ)) {m : ℕ}
  [SmoothOfRelativeDimension (m + 2) f]

local instance of2NETopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance of2NECharts : ChartedSpace (ComplexModel (m + 2)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (m + 2)
local instance of2NEManifold [IsSeparated f] [QuasiCompact f] :
    IsComplexManifold (m + 2) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (m + 2)

/-- Images of complex points are closed points. -/
theorem isClosed_schemeComplexPointImage {Y : Scheme.{0}} (g : Y ⟶ Spec (.of ℂ))
    (p : SchemeComplexPoint g) : IsClosed ({schemeComplexPointImage g p} : Set Y) := by
  let : IsClosedImmersion p.val := isClosedImmersion_of_comp_eq_id g p.val p.property
  rw [← schemeComplexPoint_range g p]
  exact p.val.isClosedEmbedding.isClosed_range

/-- **`rmk:Abhyankar`, "not necessarily equal".** Let `X` be an integral smooth projective complex
scheme of dimension `n = m + 2 ≥ 2` and `Y•` a smooth flag on `X` whose valuation
`ν_{Y•} : ℂ(X)^× → ℤⁿ` is surjective. Then there is a valuation `ν'` equivalent to `ν_{Y•}`
(`ν' = ν_{Y•} G`, `G = I + N`), with value group `ℤⁿ`, which is **not equal** to

* the valuation of any smooth flag `Z•` on `X`, nor
* the valuation of `ℂ(X)` induced by any smooth flag on any modification `π : X' → X(ℂ)`
  (in particular on any finite sequence of blow-ups with smooth centres),

nor to any valuation of `ℂ(X)` which is coordinatewise nonnegative on some local ring of `X`. -/
theorem exists_lexEquivalent_ne_flagValuations (e : ClosedProjectiveEmbedding f)
    (omega : letI := e.isSeparated; letI := e.quasiCompact;
      KahlerBackground (m + 2) (SchemeComplexPoint f))
    (Y : Fin (m + 2 + 1) → Set (SchemeComplexPoint f))
    (hY : letI := e.isSeparated; letI := e.quasiCompact; IsSmoothFlag Y)
    (hsurj : Function.Surjective (schemeOriginalFlagFunctionFieldValuation f (m + 2) e omega Y hY)) :
    letI := e.isSeparated
    letI := e.quasiCompact
    ∃ v' : AddValuation X.functionField (WithTop (Lex (Fin (m + 2) → ℤ))),
      ValuationsLexEquivalent (schemeOriginalFlagFunctionFieldValuation f (m + 2) e omega Y hY) v' ∧
      Function.Surjective v' ∧
      (∀ (μ : AddValuation X.functionField (WithTop (Lex (Fin (m + 2) → ℤ)))) (c : X),
        IsCoordNonnegAt μ c → v' ≠ μ) ∧
      (∀ (omega' : KahlerBackground (m + 2) (SchemeComplexPoint f))
        (Z : Fin (m + 2 + 1) → Set (SchemeComplexPoint f)) (hZ : IsSmoothFlag Z),
        v' ≠ schemeOriginalFlagFunctionFieldValuation f (m + 2) e omega' Z hZ) ∧
      (∀ (F : OriginalFlagGeometry.{0} (m + 2)) {π : F.carrier → SchemeComplexPoint f}
        (hπ : IsAnalyticModification (n := m + 2) π),
        v' ≠ modificationFlagValuation f F hπ) := by
  let := e.isSeparated
  let := e.quasiCompact
  let := e.isProper
  set v := schemeOriginalFlagFunctionFieldValuation f (m + 2) e omega Y hY with hvdef
  have hcen : valuationCenter f v =
      schemeComplexPointImage f (schemeProjectiveOriginalFlagPoint f (m + 2) e omega Y hY).val :=
    ((isValuationCenter_iff_eq f v _).mp
      (schemeOriginalFlagFunctionFieldValuation_isCenter f (m + 2) e omega Y hY)).symm
  have hcl : IsClosed ({valuationCenter f v} : Set X) := by
    rw [hcen]
    exact isClosed_schemeComplexPointImage f _
  obtain ⟨v', hequiv, hv', hne⟩ := exists_lexEquivalent_forall_ne_of_isCoordNonnegAt f v hsurj hcl
  refine ⟨v', hequiv, hv', hne, ?_, ?_⟩
  · intro omega' Z hZ
    exact hne _ _ (isCoordNonnegAt_schemeOriginalFlagFunctionFieldValuation f (m + 2) e omega' Z hZ)
  · intro F π hπ
    exact hne _ _ (isCoordNonnegAt_modificationFlagValuation f F hπ)

end NotEqual

end SGPT.Okounkov.OF2
