import SGPT.BDivisor.BD7NumericalInverseLimit
import SGPT.Projective.BDivOriginalPrimeNumericalPushforward

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.BDivisor.BD7

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes SGPT.Okounkov
open SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open scoped Manifold ContDiff

local instance canonicalNumericalPointTopology {S : Scheme.{0}} (g : S ⟶ Spec (.of ℂ)) :
    TopologicalSpace (SchemeComplexPoint g) :=
  schemeAnalyticPointTopology g

local instance canonicalNumericalPointCharts {S : Scheme.{0}} (g : S ⟶ Spec (.of ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d g] : ChartedSpace (ComplexModel d) (SchemeComplexPoint g) :=
  schemeAnalyticTNChartedSpace g d

local instance canonicalNumericalPointManifold {S : Scheme.{0}} (g : S ⟶ Spec (.of ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d g] [IsSeparated g] [QuasiCompact g] :
    IsComplexManifold d (SchemeComplexPoint g) :=
  schemeAnalyticTN_isComplexManifold g d

variable {Z : Scheme.{0}} {f : Z ⟶ Spec (.of ℂ)} {m : ℕ}
    [IsIntegral Z] [SmoothOfRelativeDimension (m + 1) f]
    [IsSeparated f] [QuasiCompact f] [CompactSpace (SchemeComplexPoint f)]
    (E : ClosedProjectiveEmbedding f)

local notation "M" => SmoothAlgebraicModel f (m + 1)
local notation "N" => SmoothModelNumericalClasses (f := f) (d := m + 1)
local notation "Book" => BookBlowupModel (f := f) (d := m + 1)

def smoothModelOriginalPrimeNumerical (A : M) (x : {x : A.V // Order.coheight x = 1}) : N A := by
  letI := A.embedding.isSeparated
  letI := A.embedding.quasiCompact
  letI := A.embedding.analyticCompact
  letI := smoothProjectiveNativeConnected (A.p ≫ f) (m + 1) A.embedding
  exact originalPrimeNumerical (A.p ≫ f) A.embedding
    (m := m) normalizationProjectiveForCurves_bd7 x

/-- All actual original Cartier prime classes span the all-curve numerical
quotient of every smooth projective algebraic model. -/
theorem smoothModelOriginalPrimeNumerical_span (B : M) :
    Submodule.span ℝ (Set.range (smoothModelOriginalPrimeNumerical B)) = ⊤ := by
  letI := B.embedding.isSeparated
  letI := B.embedding.quasiCompact
  letI := B.embedding.analyticCompact
  letI := smoothProjectiveNativeConnected (B.p ≫ f) (m + 1) B.embedding
  letI : LocallyOfFiniteType (B.p ≫ f) := B.embedding.locallyOfFiniteType
  let S := DFAlg.neronSeveri (m + 1) (SchemeComplexPoint (B.p ≫ f))
  let c : N B ≃ₗ[ℝ] S :=
    integralNumericalEquivNS_bd7 (B.p ≫ f) B.embedding m normalizationProjectiveForCurves_bd7
  let F : N B →ₗ[ℝ] RealBottChern (m + 1) (SchemeComplexPoint (B.p ≫ f)) :=
    S.subtype.comp c.toLinearMap
  have hinj : Function.Injective F := S.injective_subtype.comp c.injective
  have hrange : LinearMap.range F = S := by
    ext v
    rw [LinearMap.mem_range]
    constructor
    · rintro ⟨x, rfl⟩
      exact (c x).property
    · intro hv
      exact ⟨c.symm ⟨v, hv⟩, congrArg Subtype.val (c.apply_symm_apply ⟨v, hv⟩)⟩
  let cycle := fun P : SGPT.PSH.GeometricPrimeCarrier (m + 1) (SchemeComplexPoint (B.p ≫ f)) =>
    DFAlg.cycleClass (SGPT.Siu.primeEffectiveDivisor P)
  have hC (x : {x : B.V // Order.coheight x = 1}) :
      F (smoothModelOriginalPrimeNumerical B x) =
        cycle (nativePrimeOfOriginalPoint (B.p ≫ f) B.embedding (m := m) x) :=
    numericalChern_originalPrimeNumerical (B.p ≫ f) B.embedding (m := m)
      normalizationProjectiveForCurves_bd7 x
  have himage : F '' Set.range (smoothModelOriginalPrimeNumerical B) = Set.range cycle := by
    ext v
    constructor
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨_, (hC x).symm⟩
    · rintro ⟨P, rfl⟩
      obtain ⟨z, I, hI, hz, _, htrace, _⟩ :=
        SGPT.Projective.BDivNov16.exists_originalCartierCodimOnePrime_cycleClass
          (B.p ≫ f) m B.embedding P
      let x : {x : B.V // Order.coheight x = 1} := ⟨z, hz⟩
      have hP : nativePrimeOfOriginalPoint (B.p ≫ f) B.embedding (m := m) x = P :=
        SGPT.PSH.GeometricPrimeCarrier.ext
          ((nativePrimeOfOriginalPoint_val (B.p ≫ f) B.embedding (m := m) x).trans htrace.symm)
      refine ⟨smoothModelOriginalPrimeNumerical B x, ⟨x, rfl⟩, ?_⟩
      exact (hC x).trans (congrArg cycle hP)
  apply Submodule.map_injective_of_injective hinj
  rw [Submodule.map_span, Submodule.map_top, himage, hrange]
  exact SGPT.Projective.BDivNov16.neronSeveri_eq_span_primeCycleClass.symm

/-- The current transport takes the original algebraic prime to its actual
residue-weighted cycle image under the selected scheme morphism. -/
theorem smoothModelTransportedAnalyticPushforward_originalPrime
    (E : ClosedProjectiveEmbedding f) {A B : M} (h : A ≤ B) (x : {x : B.V // Order.coheight x = 1}) :
    smoothModelTransportedAnalyticPushforward E h (smoothModelOriginalPrimeNumerical B x) =
      algebraicPrimeImageClass (A.p ≫ f) A.embedding (A.homOfLE h)
        (smoothModelOriginalPrimeNumerical A) x := by
  letI := A.embedding.isSeparated
  letI := A.embedding.quasiCompact
  letI := B.embedding.isSeparated
  letI := B.embedding.quasiCompact
  letI := A.embedding.analyticCompact
  letI := B.embedding.analyticCompact
  letI := smoothProjectiveNativeConnected (A.p ≫ f) (m + 1) A.embedding
  letI := smoothProjectiveNativeConnected (B.p ≫ f) (m + 1) B.embedding
  exact SmoothAlgebraicModel.homOfLE_originalPrimeNumerical_pushforward
    E h normalizationProjectiveForCurves_bd7 x

/-- A transition induced by the literal prime cycle formula is uniquely determined
on the all-curve numerical quotient once the original Cartier prime classes span it. -/
theorem smoothModelOriginalCyclePushforward_existsUnique
    (E : ClosedProjectiveEmbedding f) {A B : M} (h : A ≤ B)
    (hspan : Submodule.span ℝ (Set.range (smoothModelOriginalPrimeNumerical B)) = ⊤) :
    ∃! L : N B →ₗ[ℝ] N A, ∀ x,
      L (smoothModelOriginalPrimeNumerical B x) =
        algebraicPrimeImageClass (A.p ≫ f) A.embedding (A.homOfLE h)
          (smoothModelOriginalPrimeNumerical A) x := by
  classical
  refine ⟨smoothModelTransportedAnalyticPushforward E h,
    smoothModelTransportedAnalyticPushforward_originalPrime E h, ?_⟩
  intro L hL
  apply LinearMap.ext
  intro v
  have hv : v ∈ Submodule.span ℝ (Set.range (smoothModelOriginalPrimeNumerical B)) := by
    rw [hspan]
    exact Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨x, rfl⟩ := hw
    rw [hL, smoothModelTransportedAnalyticPushforward_originalPrime]
  | zero => simp only [map_zero]
  | add a b _ _ ha hb => rw [map_add, map_add, ha, hb]
  | smul r a _ ha => rw [map_smul, map_smul, ha]

/-- The numerical algebraic cycle pushforward chosen by its unique prime formula. -/
def smoothModelOriginalCyclePushforward (E : ClosedProjectiveEmbedding f) ⦃A B : M⦄ (h : A ≤ B) : N B →ₗ[ℝ] N A :=
  Classical.choose (ExistsUnique.exists
    (smoothModelOriginalCyclePushforward_existsUnique E h (smoothModelOriginalPrimeNumerical_span B)))

theorem smoothModelOriginalCyclePushforward_eq_transport
    (E : ClosedProjectiveEmbedding f) {A B : M} (h : A ≤ B) :
    smoothModelOriginalCyclePushforward E h =
      smoothModelTransportedAnalyticPushforward E h :=
  (smoothModelOriginalCyclePushforward_existsUnique E h (smoothModelOriginalPrimeNumerical_span B)).unique
    (Classical.choose_spec (ExistsUnique.exists
      (smoothModelOriginalCyclePushforward_existsUnique E h (smoothModelOriginalPrimeNumerical_span B))))
    (smoothModelTransportedAnalyticPushforward_originalPrime E h)

/-- The actual algebraic cycle system is identified with the book's algebraic
Weil b-divisors by the coordinatewise canonical Chern map. -/
def canonicalOriginalNumericalWeilEquiv [ConnectedSpace (SchemeComplexPoint f)]
    (E : ClosedProjectiveEmbedding f) :
    compatibleLinearFamilies (R := ℝ) (I := M) (E := N)
      (smoothModelOriginalCyclePushforward E) ≃ₗ[ℝ]
      DFAlg.algebraicWeilFamilies m (SchemeComplexPoint f) :=
  originalNumericalAlgebraicWeilEquiv E
    (fun π : Book => chooseBookModelAlgebraization E π)
    (smoothModelOriginalCyclePushforward E)
    (fun {A B} h => smoothModelOriginalCyclePushforward_eq_transport E (A := A) (B := B) h)

theorem canonicalOriginalNumericalWeilEquiv_apply [ConnectedSpace (SchemeComplexPoint f)]
    (E : ClosedProjectiveEmbedding f)
    (D : compatibleLinearFamilies (R := ℝ) (I := M) (E := N)
      (smoothModelOriginalCyclePushforward E)) (π : Book) :
    (canonicalOriginalNumericalWeilEquiv E D).val.val π =
      (bookModelNumericalChern (fun τ : Book => chooseBookModelAlgebraization E τ) π
        (D.val (chooseBookModelAlgebraization E π).A)).val := by
  unfold canonicalOriginalNumericalWeilEquiv
  exact originalNumericalAlgebraicWeilEquiv_apply E _ _ _ D π

end SGPT.BDivisor.BD7
