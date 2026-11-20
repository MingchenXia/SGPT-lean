import SGPT.BDivisor.DFAlgNeronSeveri
import SGPT.BDivisor.BDivNSDangFavre
import SGPT.Hodge.SourceCartierSequence

/-!
# The algebraic side of the Dang--Favre comparison

Lane DF-ALG, blueprint `claude-df-alg.tex`. Source `rmk:bdiv:L749` (`chapter_bdiv.tex`):
"The algebraic nef b-divisors are introduced by Dang--Favre [DF20], as their intersection
theory. It is a straightforward application of the results proved in this section that our
transcendental intersection theory coincides with theirs in the algebraic setting."

`SGPT.BDivisor.DangFavre` (`BDivNSDangFavre.lean`) proves the transcendental content: the
product of `def:DF_ext` is the classical intersection number on nef Cartier tuples, is the limit
along every decreasing net of nef Cartier tuples, is the infimum over nef Cartier majorants and is
characterized by these properties. Here we add the **algebraic side**. Dang--Favre's b-divisor
classes are compatible families of classes in the Néron--Severi spaces `N¹(Y)_ℝ` of the models;
the cycle class map sends `N¹(Y)_ℝ` onto `NS(Y)_ℝ = SGPT.BDivisor.DFAlg.neronSeveri (m+1) Y`
(`DFAlgNeronSeveri.lean`), and the images of their objects are:

* `IsAlgebraicAny D` — every incarnation `D_Y` lies in `NS(Y)_ℝ` (Dang--Favre Weil classes);
* `IsAlgNefCartierAny C` — `C` is realized on some model `Y` by a nef class of `NS(Y)_ℝ`
  (Dang--Favre nef Cartier classes);
* `IsAlgNefAny D` — `D` is algebraic and the limit of a net of algebraic nef Cartier
  b-divisors (Dang--Favre nef classes).

The algebraic setting (`X` projective) is expressed by a Kähler form `ω` with `{ω} ∈ NS(X)_ℝ`
(a Hodge form). Main results, `X` compact connected of dimension `m + 1`:

* `isAlgNefCartierAny_currentBDivisor`: for a current `θ + ddᶜu` with analytic singularities and
  `{θ} ∈ NS(X)_ℝ`, the nef Cartier b-divisor `𝔻(θ + ddᶜu)` is algebraic: on a log resolution it
  is realized by `π^*{θ} - c {[D]}`;
* `exists_antitone_algNefCartier_seq` (**decreasing algebraic nef Cartier approximation**, the
  main technical theorem of [DF20]): on projective `X`, every nef b-divisor whose root class lies
  in `NS(X)_ℝ` is the limit of a decreasing sequence of big algebraic nef Cartier b-divisors;
* `isAlgNefAny_iff_isNefAny` (**compatibility of nefness**): on projective `X`, an algebraic
  b-divisor is nef in the sense of Dang--Favre iff it is nef in the sense of `def:nefbdiv`;
* `tendsto_intersection_of_antitone_alg`, `exists_antitone_algCartier_approximation`,
  `nefIntersection_toReal_eq_sInf_alg`, `eq_nefIntersection_of_algCartier_of_antitone`:
  **the Dang--Favre product of algebraic nef classes is the product of `def:DF_ext`**: Dang--Favre's
  limits of classical intersection numbers along decreasing algebraic nef Cartier
  approximations, their infimum over algebraic nef Cartier majorants, and every function with
  Dang--Favre's two characterizing properties on algebraic data, all equal the b-divisor product.

Not formalized (see the blueprint): the identification of `N¹(Y)_ℝ` (numerical classes) with
`NS(Y)_ℝ` and of the cycle class with push-forwards, the identification of the algebraic
intersection numbers of Cartier divisors with `∫_Y θ_1 ∧ ⋯ ∧ θ_n`, the identification of
Dang--Favre's nef cone of `N¹(Y)_ℝ` (curve positivity) with the nef classes in `NS(Y)_ℝ` (Kleiman,
Kodaira), the identification of "`NS(X)_ℝ` contains a Kähler class" with projectivity (Kodaira),
and the cofinality of blow-up models among all normal projective models (resolution).
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.BDivisor.DFAlg

open Set Filter
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses
  SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
  SGPT.Foundations.Analysis.FirstPass.GlobalAnalyticSingularities
  SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
  SGPT.Foundations.Analysis.Pending NaturalThetaPshGeometricCurrent
  SGPT.BDivisor SGPT.BDivisor.DangFavre
  SGPT.Hodge.BDivChain SGPT.Hodge.BDivChain.NativeDraft
  SGPT.Hodge.BDivChain.NativeDraft.VolumeNetDraft
  SGPT.Hodge.BDivChain.SourceNefIntersectionDraft SGPT.Hodge.BDivChain.SourceMixedOrderDraft
  SGPT.Hodge.BDivChain.SourceCartierSequenceDraft
  SGPT.Hodge.BDivChain.NativeDraft.GlobalDistributionTwo
  SGPT.Hodge.BDivChain.SourceNefProjectiveDraft

/-! ### The images of the Dang--Favre objects -/

section Objects

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [CompactSpace X]

/-- **Algebraic b-divisors** (the images of Dang--Favre's Weil b-divisor classes under the cycle
class map): every incarnation `D_Y` lies in the Néron--Severi space `NS(Y)_ℝ`. -/
def IsAlgebraicAny {S : ModelSystem n X} (D : WeilFamilyAny S) : Prop :=
  ∀ π : S.Model, D.val π ∈ neronSeveri n π.1.carrier

/-- **Algebraic nef Cartier b-divisors** (the images of Dang--Favre's nef Cartier classes): `C` is
realized on some model `Y` by a nef class of `NS(Y)_ℝ`. -/
def IsAlgNefCartierAny {S : ModelSystem n X} (C : WeilFamilyAny S) : Prop :=
  ∃ (π : S.Model) (α : RealBottChern n π.1.carrier), α ∈ neronSeveri n π.1.carrier ∧
    IsRealizationAny C π α ∧ ∃ κ : KahlerBackground n π.1.carrier, ClassNefWithRespectTo κ α

/-- **Algebraic nef b-divisors** (the images of Dang--Favre's nef classes): algebraic b-divisors
which are limits of nets of algebraic nef Cartier b-divisors. -/
def IsAlgNefAny {S : ModelSystem n X} (D₀ : WeilFamilyAny S) : Prop :=
  IsAlgebraicAny D₀ ∧
    ∃ (ι : Type (u + 1)) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι)
      (D : ι → WeilFamilyAny S), (∀ i, IsAlgNefCartierAny (D i)) ∧ ConvergesAny atTop D D₀

/-- Algebraic nef Cartier b-divisors are nef Cartier. -/
theorem IsAlgNefCartierAny.isNefCartierAny {S : ModelSystem n X} {C : WeilFamilyAny S}
    (hC : IsAlgNefCartierAny C) : IsNefCartierAny C := by
  obtain ⟨π, α, -, hr, hn⟩ := hC
  exact ⟨π, α, hr, hn⟩

/-- Algebraic nef b-divisors are nef (`def:nefbdiv`). -/
theorem IsAlgNefAny.isNefAny {S : ModelSystem n X} {D : WeilFamilyAny S} (hD : IsAlgNefAny D) :
    IsNefAny D := by
  obtain ⟨-, ι, i₁, i₂, i₃, F, hF, hc⟩ := hD
  exact ⟨ι, i₁, i₂, i₃, F, fun i => (hF i).isNefCartierAny, hc⟩

/-- The root incarnation of an algebraic b-divisor is algebraic. -/
theorem IsAlgebraicAny.sourceRootClass_mem [MeasurableSpace X] [BorelSpace X] [ConnectedSpace X]
    {D : WeilFamilyAny (ModelSystem.blowup n X)} (hD : IsAlgebraicAny D) :
    sourceRootClass D ∈ neronSeveri n X :=
  hD ModelSystem.Model.root

/-- A sequence of algebraic nef Cartier b-divisors converging to an algebraic b-divisor exhibits
it as algebraic nef. -/
theorem isAlgNefAny_of_seq {S : ModelSystem n X} {D : WeilFamilyAny S} (hD : IsAlgebraicAny D)
    (F : ℕ → WeilFamilyAny S) (hF : ∀ i, IsAlgNefCartierAny (F i))
    (hc : ConvergesAny atTop F D) : IsAlgNefAny D := by
  refine ⟨hD, ULift.{u + 1} ℕ, inferInstance, inferInstance, inferInstance,
    fun i => F i.down, fun i => hF i.down, fun π => ?_⟩
  have hdown : Tendsto (ULift.down : ULift.{u + 1} ℕ → ℕ) atTop atTop :=
    tendsto_atTop_atTop.mpr fun b => ⟨ULift.up b, fun a ha => ha⟩
  exact (hc π).comp hdown

end Objects

/-! ### `𝔻(T)` of a current with analytic singularities in an algebraic class -/

section AnalyticSingularities

variable {m : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X]
  [IsComplexManifold (m + 1) X] [CompactSpace X] [ConnectedSpace X]

/-- **`𝔻(T)` is algebraic nef Cartier for `T` with analytic singularities in an algebraic
class.** If `u ∈ PSH(X, θ)` has analytic singularities of type `(c, 𝔞)` and `{θ} ∈ NS(X)_ℝ`, then
`𝔻(θ + ddᶜu)` is realized on a log resolution `π : Y → X` by the nef class
`π^*{θ} - c {[D]} ∈ NS(Y)_ℝ` (`D` the effective divisor with `π^*𝔞 = 𝒪(-D)`). -/
theorem isAlgNefCartier_currentBDivisorOn (ωX : KahlerBackground (m + 1) X)
    (θ : ClosedRealOneOneForm (m + 1) X) {u : X → EReal}
    (hu : IsThetaPshPotential θ.val u) {c : ℚ} {𝔞 : GermIdeal (m + 1) X}
    (htype : HasAnalyticSingularitiesOfType u c 𝔞)
    (hθ : RealBottChern.ofRepresentative θ ∈ neronSeveri (m + 1) X) :
    ∃ (π : (ModelSystem.blowup (m + 1) X).Model) (α : RealBottChern (m + 1) π.1.carrier),
      α ∈ neronSeveri (m + 1) π.1.carrier ∧
      (currentBDivisorOn (ModelSystem.blowup (m + 1) X) (thetaPotentialCurrent θ.val u hu)
        (SGPT.Siu.isClosedPositiveCurrent_thetaPotentialCurrent _ _ hu)).IsRealization π α ∧
      ∃ κ : KahlerBackground (m + 1) π.1.carrier, ClassNefWithRespectTo κ α := by
  obtain ⟨Y, tY, cY, mY, π, hπ, D, EH, -, -, ⟨κ⟩, -, -, -, hEH, -, ⟨L⟩, hnef⟩ :=
    SGPT.PSH.exists_kahler_logResolution ωX θ hu htype
  let πM : (ModelSystem.blowup (m + 1) X).Model :=
    ⟨Modification.ofIsBlowupSequence hπ, Modification.isBlowupModel_ofIsBlowupSequence hπ⟩
  have hreal := currentBDivisorOn_isRealization_of_logSingularities
    (ModelSystem.blowup (m + 1) X) πM θ hu _ L
  refine ⟨πM, _, ?_, hreal, κ, ?_⟩
  · exact Submodule.sub_mem _ (classPullback_map_mem_neronSeveri πM.1 hθ)
      (curvature_smul_mem_neronSeveri hEH htype.1.le)
  · have hsub : ∀ a b : ClosedRealOneOneForm (m + 1) Y, RealBottChern.ofRepresentative (a - b) =
        RealBottChern.ofRepresentative a - RealBottChern.ofRepresentative b := by
      intro a b
      have hab : a - b = a + (-1 : ℝ) • b := by rw [neg_one_smul, sub_eq_add_neg]
      rw [hab, RealBottChern.ofRepresentative_add, RealBottChern.ofRepresentative_smul,
        neg_one_smul, sub_eq_add_neg]
    change ClassNefWithRespectTo κ (RealBottChern.ofRepresentative
        (ClosedRealOneOneForm.pullback hπ.contMDiff θ) -
      RealBottChern.ofRepresentative (MeteredDivisorScaling.smul htype.1.le EH).curvature)
    rw [← hsub]
    exact hnef κ

/-- The represented b-divisor `𝔻(θ + ddᶜu)` of a potential with analytic singularities in an
algebraic class is algebraic nef Cartier. -/
theorem isAlgNefCartierAny_representedCurrent (ωX : KahlerBackground (m + 1) X)
    (θ : ClosedRealOneOneForm (m + 1) X) (u : X → EReal)
    (hu : IsThetaPshPotential θ.val u) {c : ℚ} {𝔞 : GermIdeal (m + 1) X}
    (htype : HasAnalyticSingularitiesOfType u c 𝔞)
    (hθ : RealBottChern.ofRepresentative θ ∈ neronSeveri (m + 1) X) :
    IsAlgNefCartierAny
      (currentBDivisorAnyOn (ModelSystem.blowup (m + 1) X) (representedCurrent θ u hu)) := by
  let A := representedCurrent θ u hu
  have hp := (isPresentationAny_iff_book A θ u).mp (representedCurrent_isPresentation θ u hu)
  have hA := SGPT.Siu.isClosedPositiveCurrent_bookCurrent (toBookCurrent A)
  have hT := SGPT.Siu.isClosedPositiveCurrent_thetaPotentialCurrent _ _ hu
  have he := (currentBDivisorAnyOn_eq_existing (ModelSystem.blowup (m + 1) X) A).trans
    (currentBDivisorOn_congr _ hp.2 hA hT)
  obtain ⟨π, α, hα, hr, hn⟩ := isAlgNefCartier_currentBDivisorOn ωX θ hu htype hθ
  refine ⟨π, α, hα, ?_, hn⟩
  rw [isRealizationAny_iff_existing (Nat.succ_pos m), he]
  exact hr

end AnalyticSingularities

/-! ### Decreasing algebraic nef Cartier approximations -/

section Approximation

variable {m : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X]
  [IsComplexManifold (m + 1) X] [CompactSpace X] [ConnectedSpace X] [MeasurableSpace X]
  [BorelSpace X]

/-- **Decreasing algebraic nef Cartier approximation** (positive dimension). On a projective
`X` (a Kähler form `ω` with `{ω} ∈ NS(X)_ℝ`), every nef b-divisor `D` whose root class `D_X` lies
in `NS(X)_ℝ` is the limit of a decreasing sequence of big algebraic nef Cartier b-divisors. The
approximants are the b-divisors `𝔻(T_i)` of `cor:nef_Cartierseq`: currents with analytic
singularities in the algebraic classes `D_X + (i+1)⁻¹{ω}`. -/
theorem exists_antitone_algNefCartier_seq_pos (ω : KahlerBackground (m + 1) X)
    (hω : RealBottChern.ofRepresentative ω.form ∈ neronSeveri (m + 1) X)
    (D : WeilFamilyAny (ModelSystem.blowup (m + 1) X)) (hD : IsNefAny D)
    (hDX : sourceRootClass D ∈ neronSeveri (m + 1) X) :
    ∃ F : ℕ → WeilFamilyAny (ModelSystem.blowup (m + 1) X),
      (∀ i, IsAlgNefCartierAny (F i) ∧ 0 < volumeAny (F i)) ∧
      (∀ i j : ℕ, i ≤ j → LEAny (F j) (F i)) ∧ ConvergesAny atTop F D := by
  obtain ⟨θ, u, hu, hK, hclass, hfamily⟩ := exists_kahler_realization_rows ω D hD
  have hθNS : ∀ i, RealBottChern.ofRepresentative (θ i) ∈ neronSeveri (m + 1) X := fun i => by
    rw [hclass i]
    exact Submodule.add_mem _ hDX (Submodule.smul_mem _ _ hω)
  have hI := realization_rows_IEquivalent ω D θ u hu hclass hfamily
  choose U threshold hQ hgentle hterm using fun i => exists_eventuallyKahler_exactDyadicQEA (hK i)
  let k := threshold 0
  let V (i j : ℕ) := U i (j + k)
  have hV₀ (j : ℕ) : IsThetaPshPotential (θ 0).val (V 0 j) ∧
      IsKahlerCurrentPotential (θ 0) (V 0 j) :=
    hterm 0 (j + k) (Nat.le_add_left _ _)
  have hV (i j : ℕ) (hj : threshold i ≤ j) : IsThetaPshPotential (θ i).val (V i j) ∧
      IsKahlerCurrentPotential (θ i) (V i j) :=
    hterm i (j + k) (hj.trans (Nat.le_add_right _ _))
  have hQ₀ : SGPT.PSH.SourceQuasiEquisingularApproximation (θ 0) (u 0) (V 0) :=
    SGPT.PSH.sourceQuasiEquisingularApproximation_tail (hQ 0) k
  let C := rootCartierAny (RealBottChern.ofRepresentative ω.form)
  let S (j : ℕ) := currentBDivisorAnyOn (ModelSystem.blowup (m + 1) X)
    (representedCurrent (θ 0) (V 0 j) (hV₀ j).1)
  let B (j : ℕ) := S j - C
  have hSanti := representedFamily_antitone_of_qea (θ 0) (u 0) (V 0) hQ₀ (fun j => (hV₀ j).1)
  have hBanti (i j : ℕ) (hij : i ≤ j) : LEAny (B j) (B i) :=
    leAny_sub_const (hSanti i j hij) C
  have hSconv : ConvergesAny atTop S (D + C) := by
    have hc := representedFamily_converges_of_kahler_qea ω (θ 0) (u 0) (hu 0) (hK 0)
      (V 0) hQ₀ (fun j => (hV₀ j).1)
    rw [hfamily 0] at hc
    simpa only [reciprocalStep, Nat.cast_zero, zero_add, div_one, one_smul] using hc
  have hBconv : ConvergesAny atTop B D := by
    simpa only [add_sub_cancel_right] using convergesAny_sub_const hSconv C
  let j := fastIndex threshold
  have hj (i : ℕ) : threshold i ≤ j i := fastIndex_ge threshold i
  let F (i : ℕ) := currentBDivisorAnyOn (ModelSystem.blowup (m + 1) X)
    (representedCurrent (θ i) (V i (j i)) (hV i (j i) (hj i)).1)
  have hF (i : ℕ) : IsAlgNefCartierAny (F i) ∧ 0 < volumeAny (F i) :=
    ⟨isAlgNefCartierAny_representedCurrent ω (θ i) (V i (j i)) (hV i (j i) (hj i)).1
        (hgentle i (j i + k)).2.2.1 (hθNS i),
      (representedFamily_big_nefCartier ω (θ i) (V i (j i))
        (hV i (j i) (hj i)).1 (hV i (j i) (hj i)).2 (hgentle i (j i + k)).2.2.1).2⟩
  have hmatch (i : ℕ) : F i = B (j i) + reciprocalStep i • C := by
    have hs := sameDyadicType_of_IEquivalent (hI i) (hgentle i) (hgentle 0) (j i + k)
    exact matchedRow_family_minus_shift ω (sourceRootClass D) θ hclass i
      (V i (j i)) (V 0 (j i)) (hV i (j i) (hj i)).1 (hV₀ (j i)).1 hs
  refine ⟨F, hF, ?_, ?_⟩
  · intro a b hab
    rw [hmatch a, hmatch b]
    exact leAny_add_smul (hBanti (j a) (j b) ((fastIndex_strictMono threshold).monotone hab))
      (rootKahler_isPseudoeffectiveAny ω) (reciprocalStep_antitone hab)
  · have hc := convergesAny_add_smul_zero
      (convergesAny_comp hBconv (fastIndex_tendsto threshold)) C reciprocalStep_tendsto
    have heF : F = (fun i => B (j i) + reciprocalStep i • C) := funext hmatch
    rw [heF]
    exact hc

end Approximation

/-! ### Dimension zero -/

section DimZero

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel 0) X]
  [IsComplexManifold 0 X] [CompactSpace X]

/-- In dimension `0` every class vanishes, so every b-divisor is algebraic. -/
theorem isAlgebraicAny_of_dim_zero {S : ModelSystem 0 X} (D : WeilFamilyAny S) :
    IsAlgebraicAny D := fun π => by
  rw [realBottChern_eq_zero_of_dim_zero (D.val π)]
  exact Submodule.zero_mem _

/-- In dimension `0` every b-divisor is algebraic nef Cartier. -/
theorem isAlgNefCartierAny_of_dim_zero {S : ModelSystem 0 X} (D : WeilFamilyAny S) :
    IsAlgNefCartierAny D := by
  obtain ⟨π, α, hr, hn⟩ := isNefCartierAny_zero D
  refine ⟨π, α, ?_, hr, hn⟩
  rw [realBottChern_eq_zero_of_dim_zero α]
  exact Submodule.zero_mem _

/-- In dimension `0` every b-divisor is algebraic nef; hence the dimension-zero comparison
(`SGPT.BDivisor.DangFavre.eq_nefIntersection_of_dim_zero` and its companions) is the comparison on
algebraic data. -/
theorem isAlgNefAny_of_dim_zero {S : ModelSystem 0 X} (D : WeilFamilyAny S) :
    IsAlgNefAny D :=
  isAlgNefAny_of_seq (isAlgebraicAny_of_dim_zero D) (fun _ => D)
    (fun _ => isAlgNefCartierAny_of_dim_zero D) fun π => by
      let : TopologicalSpace (RealBottChern 0 π.1.carrier) := euclideanTopology _
      exact tendsto_const_nhds

end DimZero

/-- **Decreasing algebraic nef Cartier approximation**, in every dimension (in dimension `0`
every class vanishes, so every b-divisor is algebraic nef Cartier). On a projective `X`, every
nef b-divisor with algebraic root class is the limit of a decreasing sequence of big algebraic nef
Cartier b-divisors. -/
theorem exists_antitone_algNefCartier_seq {n : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] [CompactSpace X] [ConnectedSpace X]
    [MeasurableSpace X] [BorelSpace X] (ω : KahlerBackground n X)
    (hω : RealBottChern.ofRepresentative ω.form ∈ neronSeveri n X)
    (D : WeilFamilyAny (ModelSystem.blowup n X)) (hD : IsNefAny D)
    (hDX : sourceRootClass D ∈ neronSeveri n X) :
    ∃ F : ℕ → WeilFamilyAny (ModelSystem.blowup n X),
      (∀ i, IsAlgNefCartierAny (F i) ∧ 0 < volumeAny (F i)) ∧
      (∀ i j : ℕ, i ≤ j → LEAny (F j) (F i)) ∧ ConvergesAny atTop F D := by
  cases n with
  | zero =>
    refine ⟨fun _ => D, fun _ => ⟨?_, ?_⟩, ?_, ?_⟩
    · exact isAlgNefCartierAny_of_dim_zero D
    · rw [volumeAny_eq_one_of_dim_zero]
      exact zero_lt_one
    · intro _ _ _ π
      exact classPseudoeffective_of_dim_zero _
    · intro π
      let : TopologicalSpace (RealBottChern 0 π.1.carrier) := euclideanTopology _
      exact tendsto_const_nhds
  | succ m => exact exists_antitone_algNefCartier_seq_pos ω hω D hD hDX

/-- **Compatibility of nefness.** On a projective `X` (a Kähler form with algebraic class), an
algebraic b-divisor is nef in the sense of Dang--Favre (a limit of algebraic nef Cartier
b-divisors) iff it is nef in the sense of `def:nefbdiv` (a limit of nef Cartier b-divisors). -/
theorem isAlgNefAny_iff_isNefAny {n : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] [CompactSpace X] [ConnectedSpace X]
    [MeasurableSpace X] [BorelSpace X] (ω : KahlerBackground n X)
    (hω : RealBottChern.ofRepresentative ω.form ∈ neronSeveri n X)
    {D : WeilFamilyAny (ModelSystem.blowup n X)} (hD : IsAlgebraicAny D) :
    IsAlgNefAny D ↔ IsNefAny D := by
  refine ⟨IsAlgNefAny.isNefAny, fun h => ?_⟩
  obtain ⟨F, hF, -, hc⟩ := exists_antitone_algNefCartier_seq ω hω D h hD.sourceRootClass_mem
  exact isAlgNefAny_of_seq hD F (fun i => (hF i).1) hc

/-! ### The Dang--Favre product of algebraic nef b-divisors -/

section Intersection

variable {m : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X]
  [IsComplexManifold (m + 1) X] [CompactSpace X] [ConnectedSpace X] [MeasurableSpace X]
  [BorelSpace X]

local notation "Sys" => ModelSystem.blowup (m + 1) X

/-- **The Dang--Favre limit formula on algebraic data.** Let `(C i j)_j` be decreasing nets of
algebraic nef Cartier b-divisors converging to `D i`, with common nef realizations of the tuples
`(C i j)_i`. Then the `D i` are nef and the classical intersection numbers converge to the
b-divisor product `(D_1, …, D_{m+1})` (if the `D i` are algebraic and the nets are sequences,
the `D i` are moreover algebraic nef, `isAlgNefAny_of_seq`). -/
theorem tendsto_intersection_of_antitone_alg (ω : KahlerBackground (m + 1) X)
    {J : Type*} [Preorder J] [IsDirected J (· ≤ ·)] [Nonempty J]
    (C : Fin (m + 1) → J → WeilFamilyAny Sys) (D : Fin (m + 1) → WeilFamilyAny Sys)
    (hC : ∀ i j, IsAlgNefCartierAny (C i j))
    (ha : ∀ i j k, j ≤ k → LEAny (C i k) (C i j))
    (hc : ∀ i, ConvergesAny atTop (C i) (D i))
    (r : ∀ j, CommonNefRealization (fun i => C i j)) :
    (∀ i, IsNefAny (D i)) ∧
      Tendsto (fun j => (r j).intersection) atTop (𝓝 (nefIntersection D).toReal) :=
  tendsto_intersection_of_antitone ω C D (fun i j => (hC i j).isNefCartierAny) ha hc r

/-- **Existence of the Dang--Favre approximations.** On a projective `X`, every tuple of
algebraic nef b-divisors is approximated by decreasing sequences of algebraic nef Cartier
b-divisors with common nef realizations, along which the classical intersection numbers converge
to the b-divisor product. -/
theorem exists_antitone_algCartier_approximation (ω : KahlerBackground (m + 1) X)
    (hω : RealBottChern.ofRepresentative ω.form ∈ neronSeveri (m + 1) X)
    (D : Fin (m + 1) → WeilFamilyAny Sys) (hD : ∀ i, IsAlgNefAny (D i)) :
    ∃ (C : Fin (m + 1) → ℕ → WeilFamilyAny Sys)
      (r : ∀ j, CommonNefRealization (fun i => C i j)),
      (∀ i j, IsAlgNefCartierAny (C i j)) ∧ (∀ i j k, j ≤ k → LEAny (C i k) (C i j)) ∧
        (∀ i, ConvergesAny atTop (C i) (D i)) ∧
          Tendsto (fun j => (r j).intersection) atTop (𝓝 (nefIntersection D).toReal) := by
  choose C hC ha hc using fun i =>
    exists_antitone_algNefCartier_seq_pos ω hω (D i) (hD i).isNefAny (hD i).1.sourceRootClass_mem
  have hCart : ∀ i j, IsAlgNefCartierAny (C i j) := fun i j => (hC i j).1
  have r : ∀ j, CommonNefRealization (fun i => C i j) := fun j =>
    Classical.choice (nonempty_commonNefRealization ω (fun i => C i j)
      (fun i => (hCart i j).isNefCartierAny))
  exact ⟨C, r, hCart, ha, hc, (tendsto_intersection_of_antitone_alg ω C D hCart ha hc r).2⟩

/-- **The Dang--Favre infimum formula on algebraic data.** On a projective `X`, the
intersection product of algebraic nef b-divisors is the infimum of the classical intersection
numbers of the algebraic nef Cartier b-divisors dominating them. -/
theorem nefIntersection_toReal_eq_sInf_alg (ω : KahlerBackground (m + 1) X)
    (hω : RealBottChern.ofRepresentative ω.form ∈ neronSeveri (m + 1) X)
    (D : Fin (m + 1) → WeilFamilyAny Sys) (hD : ∀ i, IsAlgNefAny (D i)) :
    (nefIntersection D).toReal = sInf {x : ℝ | ∃ (C : Fin (m + 1) → WeilFamilyAny Sys)
      (r : CommonNefRealization C), (∀ i, IsAlgNefCartierAny (C i)) ∧
        (∀ i, LEAny (D i) (C i)) ∧ x = r.intersection} := by
  set S := {x : ℝ | ∃ (C : Fin (m + 1) → WeilFamilyAny Sys)
      (r : CommonNefRealization C), (∀ i, IsAlgNefCartierAny (C i)) ∧
        (∀ i, LEAny (D i) (C i)) ∧ x = r.intersection}
  have hlow : ∀ x ∈ S, (nefIntersection D).toReal ≤ x := by
    rintro x ⟨C, r, -, hDC, rfl⟩
    rw [r.intersection_eq ω]
    exact ENNReal.toReal_mono (nefIntersection_lt_top C).ne
      (source_nefIntersection_mono ω D C (fun i => (hD i).isNefAny)
        (fun i => isNefAny_of_isNefCartierAny (r.isNefCartierAny i)) hDC)
  obtain ⟨C, r, hC, ha, hc, ht⟩ := exists_antitone_algCartier_approximation ω hω D hD
  have hmem : ∀ j, (r j).intersection ∈ S := fun j =>
    ⟨fun i => C i j, r j, fun i => hC i j, fun i => leAny_of_antitone_converges ω (C i) (D i)
      (fun j k hjk => ha i j k hjk) (hc i) j, rfl⟩
  have hglb : IsGLB S (nefIntersection D).toReal :=
    ⟨hlow, fun b hb => ge_of_tendsto ht (Eventually.of_forall fun j => hb (hmem j))⟩
  exact (hglb.csInf_eq ⟨_, hmem 0⟩).symm

/-- **Uniqueness on algebraic data (the Dang--Favre characterization).** On a projective `X`,
a real function `I` on tuples of b-divisors which equals the classical intersection number on
every tuple of algebraic nef Cartier b-divisors with a common nef realization, and which is
continuous along decreasing sequences of algebraic nef Cartier tuples converging to algebraic nef
tuples, coincides with the b-divisor intersection product on all tuples of algebraic nef
b-divisors. Dang--Favre's product of nef b-divisor classes has these two properties, so (read
through the cycle class map) it is the product of `def:DF_ext`. -/
theorem eq_nefIntersection_of_algCartier_of_antitone (ω : KahlerBackground (m + 1) X)
    (hω : RealBottChern.ofRepresentative ω.form ∈ neronSeveri (m + 1) X)
    (I : (Fin (m + 1) → WeilFamilyAny Sys) → ℝ)
    (hcart : ∀ (C : Fin (m + 1) → WeilFamilyAny Sys) (r : CommonNefRealization C),
      (∀ i, IsAlgNefCartierAny (C i)) → I C = r.intersection)
    (hdec : ∀ (C : Fin (m + 1) → ℕ → WeilFamilyAny Sys) (D : Fin (m + 1) → WeilFamilyAny Sys),
      (∀ i j, IsAlgNefCartierAny (C i j)) → (∀ i j k, j ≤ k → LEAny (C i k) (C i j)) →
        (∀ i, ConvergesAny atTop (C i) (D i)) → (∀ i, IsAlgNefAny (D i)) →
          Tendsto (fun j => I (fun i => C i j)) atTop (𝓝 (I D)))
    (D : Fin (m + 1) → WeilFamilyAny Sys) (hD : ∀ i, IsAlgNefAny (D i)) :
    I D = (nefIntersection D).toReal := by
  obtain ⟨C, r, hC, ha, hc, ht⟩ := exists_antitone_algCartier_approximation ω hω D hD
  have hI := hdec C D hC ha hc hD
  have hI' : Tendsto (fun j => (r j).intersection) atTop (𝓝 (I D)) :=
    hI.congr' (Eventually.of_forall fun j => hcart (fun i => C i j) (r j) (fun i => hC i j))
  exact tendsto_nhds_unique hI' ht

/-- The b-divisor intersection product has the two Dang--Favre properties on algebraic data:
it is the classical intersection number on algebraic nef Cartier tuples with a common nef
realization, and it is continuous along decreasing nets of algebraic nef Cartier tuples. -/
theorem nefIntersection_isDangFavre_alg (ω : KahlerBackground (m + 1) X) :
    (∀ (C : Fin (m + 1) → WeilFamilyAny Sys) (r : CommonNefRealization C),
      (∀ i, IsAlgNefCartierAny (C i)) → (nefIntersection C).toReal = r.intersection) ∧
    (∀ {J : Type u} [Preorder J] [IsDirected J (· ≤ ·)] [Nonempty J]
      (C : Fin (m + 1) → J → WeilFamilyAny Sys) (D : Fin (m + 1) → WeilFamilyAny Sys),
      (∀ i j, IsAlgNefCartierAny (C i j)) → (∀ i j k, j ≤ k → LEAny (C i k) (C i j)) →
        (∀ i, ConvergesAny atTop (C i) (D i)) →
          Tendsto (fun j => (nefIntersection (fun i => C i j)).toReal) atTop
            (𝓝 (nefIntersection D).toReal)) := by
  obtain ⟨h₁, h₂⟩ := nefIntersection_isDangFavre ω
  exact ⟨fun C r _ => h₁ C r, fun C D hC ha hc =>
    h₂ C D (fun i j => (hC i j).isNefCartierAny) ha hc⟩

end Intersection

end SGPT.BDivisor.DFAlg
