import SGPT.PSH.SourceThetaPSHCompactness
import SGPT.PSH.NativeThetaCompactMaximum
import SGPT.PSH.SourceIEnvelope
import SGPT.PSH.SingularityOrder

/-!
# The auxiliary envelopes `P'` and the maximum principle

Source: `author/chapter_Bergman.tex`, Section "Quantization of partial equilibrium
measures". Before `lma:max_princ` the book introduces the auxiliary functions
\[
  P'_{\theta,K}[\varphi](v) = \sup\{\eta \in \mathrm{PSH}(X,\theta) :
    \eta|_K \le v,\ \eta \preceq \varphi\},\qquad
  P'_{\theta,K}[\varphi]_{\mathcal I}(v) = \sup\{\eta \in \mathrm{PSH}(X,\theta) :
    \eta|_K \le v,\ \eta \preceq_{\mathcal I} \varphi\}.
\]
These are *pointwise* suprema (no upper semicontinuous regularization) and the constraint on
`K` is imposed at every point of `K` (not quasi-everywhere). We define both and prove
`lma:max_princ`:
\[
  \sup_K(\eta - v) = \sup_{\{\eta \ne -\infty\}} (\eta - P'_{\theta,K}[\varphi](v))
    = \sup_{\{P'_{\theta,K}[\varphi](v) \ne -\infty\}} (\eta - P'_{\theta,K}[\varphi](v))
\]
for `η ∈ PSH(X,θ)` with `η ⪯ φ`, `K` closed non-pluripolar and `v ∈ C⁰(K)`.
All suprema and differences are taken in `EReal` (with `⊥ - a = ⊥`).
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.Bergman.MaximumPrinciple

open Set
open SGPT.PSH SGPT.PSH.VariableComplexAtlas
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Candidates for `P'_{θ,K}[φ](v)`: θ-psh `η` with `η ≤ v` at every point of `K` and
`η ⪯ φ`. -/
def primedCompetitors (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (φ : M → EReal)
    (K : Set M) (v : K → EReal) :=
  {η : M → EReal // (ofFixedModel n M).IsThetaPSH θ η ∧ (∀ x : K, η x ≤ v x) ∧
    SingularityLE η φ}

/-- Candidates for `P'_{θ,K}[φ]_I(v)`: θ-psh `η` with `η ≤ v` at every point of `K` and
`η ⪯_I φ`. -/
def primedICompetitors (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (φ : M → EReal)
    (K : Set M) (v : K → EReal) :=
  {η : M → EReal // (ofFixedModel n M).IsThetaPSH θ η ∧ (∀ x : K, η x ≤ v x) ∧
    sourceIOrder (ofFixedModel n M) η φ}

/-- The book's auxiliary function `P'_{θ,K}[φ](v)` (chapter_Bergman, before
`lma:max_princ`): the pointwise supremum of all candidates, without regularization. -/
def primedPartialEnvelope (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (φ : M → EReal)
    (K : Set M) (v : K → EReal) : M → EReal :=
  fun x => ⨆ η : primedCompetitors θ φ K v, η.1 x

/-- The book's auxiliary function `P'_{θ,K}[φ]_I(v)`: the pointwise supremum of all
candidates `η ⪯_I φ`, without regularization. -/
def primedPartialIEnvelope (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (φ : M → EReal)
    (K : Set M) (v : K → EReal) : M → EReal :=
  fun x => ⨆ η : primedICompetitors θ φ K v, η.1 x

theorem primedPartialEnvelope_le_on (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (φ : M → EReal) (K : Set M) (v : K → EReal) (y : K) :
    primedPartialEnvelope θ φ K v y ≤ v y :=
  iSup_le fun η => η.2.2.1 y

theorem le_primedPartialEnvelope {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}
    {φ : M → EReal} {K : Set M} {v : K → EReal} (η : primedCompetitors θ φ K v) (x : M) :
    η.1 x ≤ primedPartialEnvelope θ φ K v x :=
  le_iSup (fun η : primedCompetitors θ φ K v => η.1 x) η

theorem primedPartialIEnvelope_le_on (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (φ : M → EReal) (K : Set M) (v : K → EReal) (y : K) :
    primedPartialIEnvelope θ φ K v y ≤ v y :=
  iSup_le fun η => η.2.2.1 y

theorem le_primedPartialIEnvelope {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}
    {φ : M → EReal} {K : Set M} {v : K → EReal} (η : primedICompetitors θ φ K v) (x : M) :
    η.1 x ≤ primedPartialIEnvelope θ φ K v x :=
  le_iSup (fun η : primedICompetitors θ φ K v => η.1 x) η

/-- Elementary `EReal` rearrangement: for `a ≠ ⊤` and real `b, c`,
`a - b ≤ c ↔ a + (-c) ≤ b`. -/
theorem sub_coe_le_coe_iff {a : EReal} (ha : a ≠ ⊤) (b c : ℝ) :
    a - (b : EReal) ≤ (c : EReal) ↔ a + ((-c : ℝ) : EReal) ≤ (b : EReal) := by
  induction a with
  | bot => simp
  | coe x =>
    rw [← EReal.coe_sub, ← EReal.coe_add, EReal.coe_le_coe_iff, EReal.coe_le_coe_iff]
    constructor <;> intro h <;> linarith
  | top => exact absurd rfl ha

/-- Source `lma:max_princ`. Let `K` be closed and non-pluripolar, `v ∈ C⁰(K)`, and let
`η` be θ-psh with `η ⪯ φ`. Then
`sup_K (η - v) = sup_{η ≠ -∞} (η - P'_{θ,K}[φ](v)) = sup_{P' ≠ -∞} (η - P'_{θ,K}[φ](v))`.
The hypothesis `φ ∈ PSH(X,θ)` of the book is not needed. -/
theorem max_princ [CompactSpace M]
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ η : M → EReal}
    {K : Set M} (hKc : IsClosed K) (hK : (ofFixedModel n M).NonPluripolar K) (v : C(K, ℝ))
    (hη : (ofFixedModel n M).IsThetaPSH θ η) (hηφ : SingularityLE η φ) :
    (⨆ x : K, η x - (v x : EReal)) =
        (⨆ (x : M) (_ : η x ≠ ⊥),
          η x - primedPartialEnvelope θ φ K (fun y => (v y : EReal)) x) ∧
      (⨆ (x : M) (_ : η x ≠ ⊥),
          η x - primedPartialEnvelope θ φ K (fun y => (v y : EReal)) x) =
        ⨆ (x : M) (_ : primedPartialEnvelope θ φ K (fun y => (v y : EReal)) x ≠ ⊥),
          η x - primedPartialEnvelope θ φ K (fun y => (v y : EReal)) x := by
  set P := primedPartialEnvelope θ φ K (fun y => (v y : EReal)) with hPdef
  set S := ⨆ x : K, η x - (v x : EReal) with hSdef
  -- a point of `K` off the poles of `η`, since `K` is non-pluripolar
  have hpole := SGPT.PSH.ConnectedThetaPSHCompactness.source_poles_locallyPluripolar hη
  obtain ⟨x₀, hx₀K, hx₀⟩ : ∃ x ∈ K, η x ≠ ⊥ := by
    by_contra h
    push Not at h
    exact hK (hpole.mono fun x hx => h x hx)
  have : Nonempty M := ⟨x₀⟩
  -- `S` is a finite real number
  obtain ⟨C, hC⟩ := ((isThetaPSH_iff_nativeThetaPotential θ η).mp hη).exists_global_upper_bound
  have : CompactSpace K := isCompact_iff_compactSpace.mp hKc.isCompact
  have hR : ∀ y : K, -‖v‖ ≤ v y := by
    intro y
    have h := ContinuousMap.norm_coe_le_norm v y
    rw [Real.norm_eq_abs] at h
    linarith [neg_abs_le (v y)]
  have hSle : S ≤ ((C + ‖v‖ : ℝ) : EReal) := by
    apply iSup_le
    intro y
    calc η y - (v y : EReal) ≤ (C : EReal) - (v y : EReal) := EReal.sub_le_sub (hC y) le_rfl
      _ = ((C - v y : ℝ) : EReal) := (EReal.coe_sub _ _).symm
      _ ≤ ((C + ‖v‖ : ℝ) : EReal) := EReal.coe_le_coe_iff.mpr (by linarith [hR y])
  have hSge : η x₀ - (v ⟨x₀, hx₀K⟩ : EReal) ≤ S :=
    le_iSup (fun x : K => η x - (v x : EReal)) ⟨x₀, hx₀K⟩
  have hη₀ : η x₀ = ((η x₀).toReal : EReal) := (EReal.coe_toReal (hη.1 x₀) hx₀).symm
  have hSbot : S ≠ ⊥ := by
    intro h
    rw [h, hη₀, ← EReal.coe_sub] at hSge
    exact EReal.coe_ne_bot _ (le_bot_iff.mp hSge)
  have hStop : S ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) hSle
  set c := S.toReal with hcdef
  have hSc : S = (c : EReal) := (EReal.coe_toReal hStop hSbot).symm
  -- the translate `η - c` is a candidate for `P'`
  have hcand : (ofFixedModel n M).IsThetaPSH θ (fun x => η x + ((-c : ℝ) : EReal)) ∧
      (∀ y : K, (fun x => η x + ((-c : ℝ) : EReal)) y ≤ (v y : EReal)) ∧
      SingularityLE (fun x => η x + ((-c : ℝ) : EReal)) φ := by
    refine ⟨(isThetaPSH_iff_nativeThetaPotential θ _).mpr
      (((isThetaPSH_iff_nativeThetaPotential θ η).mp hη).add_const (-c)), ?_, ?_⟩
    · intro y
      have hy : η y - (v y : EReal) ≤ (c : EReal) := by
        rw [← hSc]
        exact le_iSup (fun x : K => η x - (v x : EReal)) y
      exact (sub_coe_le_coe_iff (hη.1 y) (v y) c).mp hy
    · obtain ⟨D, hD⟩ := (singularityLE_iff_exists_real _ _).mp hηφ
      refine (singularityLE_iff_exists_real _ _).mpr ⟨D + -c, fun x => ?_⟩
      calc η x + ((-c : ℝ) : EReal) ≤ (φ x + (D : EReal)) + ((-c : ℝ) : EReal) :=
            add_le_add (hD x) le_rfl
        _ = φ x + ((D + -c : ℝ) : EReal) := by rw [add_assoc, ← EReal.coe_add]
  have hlow : ∀ x, η x + ((-c : ℝ) : EReal) ≤ P x :=
    fun x => le_primedPartialEnvelope ⟨_, hcand⟩ x
  have hPv : ∀ y : K, P y ≤ (v y : EReal) :=
    primedPartialEnvelope_le_on θ φ K (fun y => (v y : EReal))
  -- the poles of `P'` are among the poles of `η`
  have hPbot : ∀ x, η x ≠ ⊥ → P x ≠ ⊥ := by
    intro x hx hP
    have h := hlow x
    rw [hP, le_bot_iff] at h
    exact (EReal.add_ne_bot_iff.mpr ⟨hx, EReal.coe_ne_bot _⟩) h
  -- the middle supremum is bounded by `c`
  have hmid : (⨆ (x : M) (_ : η x ≠ ⊥), η x - P x) ≤ S := by
    rw [hSc]
    refine iSup₂_le fun x hx => ?_
    have hxr : η x = ((η x).toReal : EReal) := (EReal.coe_toReal (hη.1 x) hx).symm
    calc η x - P x ≤ η x - (η x + ((-c : ℝ) : EReal)) := EReal.sub_le_sub le_rfl (hlow x)
      _ = (c : EReal) := by
        rw [hxr, ← EReal.coe_add, ← EReal.coe_sub]
        congr 1
        ring
  refine ⟨le_antisymm ?_ hmid, le_antisymm ?_ ?_⟩
  · refine iSup_le fun y => ?_
    by_cases hy : η y = ⊥
    · rw [hy, EReal.bot_sub]
      exact bot_le
    · exact (EReal.sub_le_sub le_rfl (hPv y)).trans
        (le_iSup₂_of_le (f := fun (x : M) (_ : η x ≠ ⊥) => η x - P x) y.val hy le_rfl)
  · exact iSup₂_le fun x hx =>
      le_iSup₂_of_le (f := fun (x : M) (_ : P x ≠ ⊥) => η x - P x) x (hPbot x hx) le_rfl
  · refine iSup₂_le fun x hx => ?_
    by_cases hηx : η x = ⊥
    · rw [hηx, EReal.bot_sub]
      exact bot_le
    · exact le_iSup₂_of_le (f := fun (x : M) (_ : η x ≠ ⊥) => η x - P x) x hηx le_rfl

end SGPT.Bergman.MaximumPrinciple
