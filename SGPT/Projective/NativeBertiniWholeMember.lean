import SGPT.Bergman.SiuKodairaEmbedding
import SGPT.Bergman.SiuNativeSectionMetric
import SGPT.GAGA.SmoothFlagsBertini
import SGPT.Trace.BertiniHyperplaneQuotientFrame
import SGPT.Foundations.Analysis.Pending.SubmanifoldKahlerRestriction

/-! Actual whole regular members of the original native Kodaira family.
Blueprint: `native-bertini-whole-member.tex`. -/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.Projective.NumEq.CompleteIntersections

open Set Filter Bundle
open scoped Topology Manifold ContDiff BigOperators
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.NumericalRestrictedVolumeScaffold
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.QuantizationDraft
open SGPT.Bergman.CompactHolomorphicSectionsDraft
open SGPT.Bergman.PolynomialH0Growth SGPT.Bergman.NativeHermitianMetric
open SGPT.Bergman.AnalyticSectionProducts
open HermitianHolomorphicLineBundle
open SGPT.PSH.GlobalL2 SGPT.Trace.Bertini
open SGPT.Projective.ComplexProjectiveSpace

variable {n N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-- The literal finite linear combination in the original physical bundle. -/
def linearSection (L : HermitianHolomorphicLineBundle.{0,0} n X)
    (s : Fin (N + 1) → HolomorphicSections (n := n) L.Fiber)
    (l : HyperplaneSpace N) : HolomorphicSections (n := n) L.Fiber :=
  ∑ i, l.rep i • s i

/-- Exact equality of full physical zero sets; no component is selected. -/
theorem linearSection_zero_iff
    (L : HermitianHolomorphicLineBundle.{0,0} n X)
    (s : Fin (N + 1) → HolomorphicSections (n := n) L.Fiber)
    (hgen : ∀ x : X, ∃ j, s j x ≠ 0) (l : HyperplaneSpace N) (x : X) :
    linearSection L s l x = 0 ↔
      x ∈ member (sourceNativeFiniteSectionProjectiveMap L s hgen) l := by
  classical
  let ev : HolomorphicSections (n := n) L.Fiber →ₗ[ℂ] L.Fiber x := {
    toFun t := t x
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  have heval : linearSection L s l x = ∑ i, l.rep i • s i x := by
    change ev (∑ i, l.rep i • s i) = _
    rw [map_sum]
    rfl
  rw [heval, nativeSectionFamily_linear_zero_iff L s hgen l.rep x]
  change pairing l.rep (sourceNativeFiniteSectionProjectiveMap L s hgen x).rep = 0 ↔ _
  exact (mem_hyperplane_mk_iff l
    (sourceNativeFiniteSectionProjectiveMap L s hgen x).rep_ne_zero).symm.trans
      (by rw [mk_rep]; rfl)

/-- The SAME actual section is densely nonzero, including on disconnected X. -/
theorem linearSection_dense_nonzero
    (hn : 0 < n) (L : HermitianHolomorphicLineBundle.{0,0} n X)
    (s : Fin (N + 1) → HolomorphicSections (n := n) L.Fiber)
    (hgen : ∀ x : X, ∃ j, s j x ≠ 0) (l : HyperplaneSpace N)
    (hp : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) ∞
      (sourceNativeFiniteSectionProjectiveMap L s hgen))
    (hl : IsSmoothHypersurfaceMember n (sourceNativeFiniteSectionProjectiveMap L s hgen) l) :
    ∀ U : Set X, IsOpen U → U.Nonempty → ∃ y ∈ U, linearSection L s l y ≠ 0 := by
  intro U hU hUne
  by_contra h
  push Not at h
  have hsub : U ⊆ member (sourceNativeFiniteSectionProjectiveMap L s hgen) l :=
    fun y hy => (linearSection_zero_iff L s hgen l y).mp (h y hy)
  obtain ⟨x, hx⟩ := hUne
  have hfull : RegularAtDim (n := n)
      (member (sourceNativeFiniteSectionProjectiveMap L s hgen) l) x n := by
    refine RegularPointDimension.regularAtDim_of_inter_eq hU hx ?_
      (AnalyticIrreducibleComponents.regularAtDim_univ x)
    rw [univ_inter, inter_eq_right.mpr hsub]
  have hpred := regularAtDim_member _ hp hl (hsub hx)
  have heq := RegularPointDimension.eq_of_regularAtDim hfull hpred
  omega

/-- A positive original native bundle produces a regular section in ONE
literal positive power, with the SAME original finite family/map/member. -/
theorem exists_positivePower_regularSection [CompactSpace X]
    (hn : 0 < n) (L : HermitianHolomorphicLineBundle.{0,0} n X)
    (hL : IsSourceSmoothHermitianMetric L) (θ : ClosedRealOneOneForm n X)
    (hθ : IsOwnFirstChernForm L θ) (hK : θ.val.IsKahler) :
    ∃ (d : ℕ), 0 < d ∧ ∃ (N : ℕ)
      (s : Fin (N + 1) → HolomorphicSections (n := n) (positivePower L (d - 1)).Fiber)
      (hgen : ∀ x : X, ∃ j, s j x ≠ 0) (l : HyperplaneSpace N),
      ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) ∞
        (sourceNativeFiniteSectionProjectiveMap (positivePower L (d - 1)) s hgen) ∧
      IsSmoothHypersurfaceMember n
        (sourceNativeFiniteSectionProjectiveMap (positivePower L (d - 1)) s hgen) l ∧
      ∀ U : Set X, IsOpen U → U.Nonempty → ∃ y ∈ U,
        linearSection (positivePower L (d - 1)) s l y ≠ 0 := by
  obtain ⟨d, hd, N, s, hgen, hp, hemb, _himm⟩ :=
    SGPT.Bergman.SiuKodaira.kodairaEmbedding L hL θ hθ hK
  let p := sourceNativeFiniteSectionProjectiveMap (positivePower L (d - 1)) s hgen
  have hex : ∃ l : HyperplaneSpace N, IsSmoothHypersurfaceMember n p l := by
    by_cases hX : Nonempty X
    · have : Nonempty X := hX
      obtain ⟨a, b, hab⟩ := SGPT.GAGA.SmoothFlags.exists_ne_of_one_le hn (W := X)
      have hN : 1 ≤ N := by
        by_contra h
        obtain rfl : N = 0 := by omega
        exact hab (hemb.injective
          (SGPT.GAGA.SmoothFlags.subsingleton_complexProjectiveSpace_zero.elim _ _))
      by_contra h
      push Not at h
      have huniv : singularMemberSet n p = univ := eq_univ_of_forall h
      have hint := interior_singularMemberSet p hp hN
      rw [huniv, interior_univ] at hint
      exact univ_nonempty.ne_empty hint
    · exact ⟨affinePoint 0 0, fun x => (hX ⟨x⟩).elim⟩
  obtain ⟨l, hl⟩ := hex
  exact ⟨d, hd, N, s, hgen, l, hp, hl,
    linearSection_dense_nonzero hn _ s hgen l hp hl⟩

/-- The WHOLE regular member carries the genuine induced Kähler background.
It is the original ambient form pulled back by the literal inclusion. -/
def wholeMemberKahler
    (p : X → ComplexProjectiveSpace N)
    (hp : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) ∞ p)
    (l : HyperplaneSpace N) (hl : IsSmoothHypersurfaceMember n p l)
    (omega : KahlerBackground n X) :
    letI := SubmanifoldChartedSpace.chartedSpace (Nat.sub_le n 1)
      (fun _ hx => regularAtDim_member p hp hl hx)
    letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (Nat.sub_le n 1)
      (fun _ hx => regularAtDim_member p hp hl hx)
    KahlerBackground (n - 1) (member p l) :=
  SubmanifoldKahlerRestriction.kahlerBackground (Nat.sub_le n 1)
    (fun _ hx => regularAtDim_member p hp hl hx) omega

section Metric

variable (hn : 0 < n) (L : HermitianHolomorphicLineBundle.{0,0} n X)
  (s : Fin (N + 1) → HolomorphicSections (n := n) L.Fiber)
  (hgen : ∀ x : X, ∃ j, s j x ≠ 0) (l : HyperplaneSpace N)
  (hp : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) ∞
    (sourceNativeFiniteSectionProjectiveMap L s hgen))
  (hl : IsSmoothHypersurfaceMember n (sourceNativeFiniteSectionProjectiveMap L s hgen) l)

/-- Actual full original Cartier ideal of the SAME regular linear section. -/
def wholeMemberCartierDivisor :
    SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves.EffectiveDivisor n X :=
  SGPT.BDivisor.NSKodaira.nativeSectionCartierDivisor L (linearSection L s l)
    (linearSection_dense_nonzero hn L s hgen l hp hl)

/-- Actual physical log norm in the SAME original bundle metric. -/
def wholeMemberDivisorMetric (hL : IsSourceSmoothHermitianMetric L) :
    MeteredEffectiveQDivisor n X :=
  SGPT.BDivisor.NSKodaira.nativeSectionDivisorMetric L hL (linearSection L s l)
    (linearSection_dense_nonzero hn L s hgen l hp hl)

/-- Its original full Cartier ideal and physical metric agree in every stalk. -/
theorem wholeMemberDivisorMetric_isDivisorMetric (hL : IsSourceSmoothHermitianMetric L) :
    DivisorMetric.IsDivisorMetric (wholeMemberCartierDivisor hn L s hgen l hp hl)
      (wholeMemberDivisorMetric hn L s hgen l hp hl hL) :=
  SGPT.BDivisor.NSKodaira.nativeSectionDivisorMetric_isDivisorMetric
    L hL (linearSection L s l) (linearSection_dense_nonzero hn L s hgen l hp hl)

/-- Exact original curvature, with no metric chosen independently of the section. -/
theorem wholeMemberDivisorMetric_curvature (hL : IsSourceSmoothHermitianMetric L) :
    (wholeMemberDivisorMetric hn L s hgen l hp hl hL).curvature =
      sourceNativeFirstChernForm L hL := rfl

end Metric

omit [IsComplexManifold n X] in
/-- The whole zero subtype is compact, independently of connectedness. -/
theorem wholeMember_compact [CompactSpace X]
    (p : X → ComplexProjectiveSpace N)
    (hp : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) ∞ p)
    (l : HyperplaneSpace N) : CompactSpace (member p l) :=
  isCompact_iff_compactSpace.mp (isClosed_member p hp.continuous l).isCompact

end SGPT.Projective.NumEq.CompleteIntersections
