import SGPT.PSH.OriginalAnalyticConventions

/-! # Genuine holomorphic germs and optional coherent type in varying dimensions

The finite-generation convention is the same stalkwise coherent-ideal
convention as the native `GermIdeal`. Global type is an additional condition,
as authorized by the source correction; no local-to-global existence is claimed.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open scoped Topology Manifold ContDiff

universe u
variable {X : Type u} [TopologicalSpace X]

/-- A scalar germ is genuinely holomorphic in every original chart on some
original open neighborhood, independently of the dimensions of those charts. -/
def AtlasHolomorphicAt (A : VariableComplexAtlas X) (g : X → ℂ) (x : X) : Prop :=
  ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ A.ChartHolomorphicOn g U

/-- Actual finite ideal combinations of original holomorphic germs. -/
def AtlasIsInSpanAt (A : VariableComplexAtlas X) (S : (X → ℂ) → Prop)
    (x : X) (g : X → ℂ) : Prop :=
  A.AtlasHolomorphicAt g x ∧
    ∃ (N : ℕ) (s a : Fin N → X → ℂ), (∀ i, S (s i)) ∧
      (∀ i, A.AtlasHolomorphicAt (a i) x) ∧
      g =ᶠ[𝓝 x] fun y => ∑ i, a i y * s i y

/-- Original germ-membership data; coherence below imposes the genuine local
finite ideal equations, using the same convention as the native `GermIdeal`. -/
@[ext] structure AtlasGermIdeal (A : VariableComplexAtlas X) where
  mem : X → (X → ℂ) → Prop

/-- Local finite holomorphic generators at every point of the whole original
neighborhood. No global denominator, generator count or dimension is assumed. -/
def AtlasGermIdeal.IsCoherent {A : VariableComplexAtlas X} (I : AtlasGermIdeal A) : Prop :=
  ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ ∃ (N : ℕ) (s : Fin N → X → ℂ),
    (∀ i, A.ChartHolomorphicOn (s i) U) ∧
      ∀ y ∈ U, ∀ g, I.mem y g ↔ A.AtlasIsInSpanAt (· ∈ range s) y g

/-- The additional global type condition on the original variable atlas.
It keeps ONE supplied positive rational coefficient and ONE coherent ideal. -/
def HasAtlasCoherentRationalAnalyticType (A : VariableComplexAtlas X) (u : X → EReal)
    (c : ℚ) (I : AtlasGermIdeal A) : Prop :=
  0 < c ∧ I.IsCoherent ∧
    ∀ x : X, ∃ (N : ℕ) (f : Fin N → X → ℂ) (b : X → ℝ) (C : ℝ) (U : Set X),
      0 ≤ C ∧ IsOpen U ∧ IsConnected U ∧ x ∈ U ∧
        (∀ j, A.ChartHolomorphicOn (f j) U) ∧
        (∀ y ∈ U, ∀ g, I.mem y g ↔ A.AtlasIsInSpanAt (· ∈ range f) y g) ∧
        (∀ y ∈ U, |b y| ≤ C) ∧
        EqOn u (fun y => ((c : ℝ) : EReal) * generatorLog f y + (b y : EReal)) U

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Whole original native-atlas scalar germs are exactly native germs. -/
theorem atlasHolomorphicAt_iff_native {g : M → ℂ} {x : M} :
    (ofFixedModel n M).AtlasHolomorphicAt g x ↔ HolomorphicAt n g x := by
  constructor
  · rintro ⟨U, hU, hxU, hg⟩
    have hn := (chartHolomorphicOn_iff_native hU).mp hg
    exact eventually_of_mem (hU.mem_nhds hxU) fun y hy =>
      hn.mdifferentiableAt (hU.mem_nhds hy)
  · intro hg
    obtain ⟨U, hUsub, hU, hxU⟩ := mem_nhds_iff.mp hg
    refine ⟨U, hU, hxU, (chartHolomorphicOn_iff_native hU).mpr ?_⟩
    exact fun y hy => (hUsub hy).mdifferentiableWithinAt

/-- The same original finite sums and germ equalities give exactly native spans. -/
theorem atlasIsInSpanAt_iff_native {S : (M → ℂ) → Prop} {x : M} {g : M → ℂ} :
    (ofFixedModel n M).AtlasIsInSpanAt S x g ↔ IsInSpanAt (n := n) S x g := by
  simp only [AtlasIsInSpanAt, IsInSpanAt, atlasHolomorphicAt_iff_native]

/-- Keep the entire original ideal's germ-membership predicate unchanged. -/
def AtlasGermIdeal.toNative (I : AtlasGermIdeal (ofFixedModel n M)) : GermIdeal n M :=
  ⟨I.mem⟩

/-- Keep every native ideal membership in the whole original atlas. -/
def nativeGermIdealToAtlas (I : GermIdeal n M) : AtlasGermIdeal (ofFixedModel n M) :=
  ⟨I.mem⟩

/-- Both ideal conversions are literal inverses on the whole membership data. -/
theorem atlasGermIdeal_native_inverse (I : AtlasGermIdeal (ofFixedModel n M)) :
    nativeGermIdealToAtlas I.toNative = I := by cases I; rfl

/-- Both ideal conversions preserve every original native membership. -/
theorem nativeGermIdeal_atlas_inverse (I : GermIdeal n M) :
    (nativeGermIdealToAtlas I).toNative = I := by cases I; rfl

/-- Coherence has exactly the same local original families and native spans. -/
theorem atlasGermIdeal_isCoherent_iff_native (I : AtlasGermIdeal (ofFixedModel n M)) :
    I.IsCoherent ↔ I.toNative.IsCoherent := by
  constructor
  · intro h x
    obtain ⟨U, hU, hxU, N, s, hs, hgen⟩ := h x
    refine ⟨U, hU, hxU, N, s, fun i => (chartHolomorphicOn_iff_native hU).mp (hs i), ?_⟩
    intro y hy g
    exact (hgen y hy g).trans atlasIsInSpanAt_iff_native
  · intro h x
    obtain ⟨U, hU, hxU, N, s, hs, hgen⟩ := h x
    refine ⟨U, hU, hxU, N, s, fun i => (chartHolomorphicOn_iff_native hU).mpr (hs i), ?_⟩
    intro y hy g
    exact (hgen y hy g).trans atlasIsInSpanAt_iff_native.symm

/-- Optional variable-ideal type is the exact canonical original native type,
with the same supplied c, every stalk, connected neighborhood and generator. -/
theorem hasAtlasCoherentRationalAnalyticType_iff_native {u : M → EReal} {c : ℚ}
    {I : AtlasGermIdeal (ofFixedModel n M)} :
    (ofFixedModel n M).HasAtlasCoherentRationalAnalyticType u c I ↔
      (ofFixedModel n M).HasCoherentRationalAnalyticType u c I.toNative := by
  constructor
  · rintro ⟨hc, hI, hp⟩
    refine ⟨hc, (atlasGermIdeal_isCoherent_iff_native I).mp hI, ?_⟩
    intro x
    obtain ⟨N, f, b, C, U, hC, hU, hconn, hxU, hf, hgen, hb, heq⟩ := hp x
    refine ⟨N, f, b, C, U, hC, hU, hconn, hxU, hf, ?_, hb, heq⟩
    intro y hy g
    exact (hgen y hy g).trans atlasIsInSpanAt_iff_native
  · rintro ⟨hc, hI, hp⟩
    refine ⟨hc, (atlasGermIdeal_isCoherent_iff_native I).mpr hI, ?_⟩
    intro x
    obtain ⟨N, f, b, C, U, hC, hU, hconn, hxU, hf, hgen, hb, heq⟩ := hp x
    refine ⟨N, f, b, C, U, hC, hU, hconn, hxU, hf, ?_, hb, heq⟩
    intro y hy g
    exact (hgen y hy g).trans atlasIsInSpanAt_iff_native.symm

variable {A : VariableComplexAtlas X}

/-- Forget only the optional global ideal and its stalk equations; do not
assert that an intrinsic local analytic type supplies a global coherent type. -/
theorem HasAtlasCoherentRationalAnalyticType.intrinsic {u : X → EReal} {c : ℚ}
    {I : AtlasGermIdeal A} (hu : A.HasAtlasCoherentRationalAnalyticType u c I) :
    A.HasRationalAnalyticType u := by
  obtain ⟨hc, _hI, hp⟩ := hu
  intro x
  obtain ⟨N, f, b, C, U, hC, hU, hconn, hxU, hf, _hgen, hb, heq⟩ := hp x
  exact ⟨c, N, f, b, C, U, hc, hC, hU, hconn, hxU, hf, hb, heq⟩

/-- Genuine original variable-atlas QPSH produces a nonzero point of the SAME
global-type generators in their SAME neighborhood; no nonzero witness is input. -/
theorem IsQPSH.exists_atlasCoherent_intrinsic_presentation {u : X → EReal} {c : ℚ}
    {I : AtlasGermIdeal A} (hu : A.IsQPSH u)
    (ht : A.HasAtlasCoherentRationalAnalyticType u c I) (x : X) :
    ∃ (N : ℕ) (f : Fin N → X → ℂ) (b : X → ℝ) (C : ℝ) (U : Set X),
      0 < c ∧ 0 ≤ C ∧ IsOpen U ∧ IsConnected U ∧ x ∈ U ∧
        (∀ j, A.ChartHolomorphicOn (f j) U) ∧
        (∀ y ∈ U, ∀ g, I.mem y g ↔ A.AtlasIsInSpanAt (· ∈ range f) y g) ∧
        (∀ y ∈ U, |b y| ≤ C) ∧
        EqOn u (fun y => ((c : ℝ) : EReal) * generatorLog f y + (b y : EReal)) U ∧
        ∃ y ∈ U, ∃ j, f j y ≠ 0 := by
  obtain ⟨hc, _hI, hp⟩ := ht
  obtain ⟨N, f, b, C, U, hC, hU, hconn, hxU, hf, hgen, hb, heq⟩ := hp x
  obtain ⟨y, hy, hfin⟩ := hu.locallyNondegenerate x U hU hxU
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have hnonzero : ¬ ∀ j, f j y = 0 := by
    intro hz
    exact hfin ((heq hy).trans ((scaled_generatorLog_add_eq_bot_iff f y hcR (b y)).mpr hz))
  push Not at hnonzero
  exact ⟨N, f, b, C, U, hc, hC, hU, hconn, hxU, hf, hgen, hb, heq, y, hy, hnonzero⟩

end SGPT.PSH.VariableComplexAtlas
