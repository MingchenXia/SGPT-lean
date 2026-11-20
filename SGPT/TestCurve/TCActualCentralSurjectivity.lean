import SGPT.TestCurve.TCAmpleProjectivity
import SGPT.Projective.OriginalAmpleSerreVanishing
import SGPT.Foundations.Envelope.AlgGeom.ProjectiveCentralFiberSectionLifting

/-! Genuine original eventual central-fibre restriction and modulo-t base change. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.TestCurve.CentralFiber
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry SGPT.Foundations.Schemes Opposite
open SGPT.LineBundle SGPT.TestCurve.TCEnc SGPT.TestCurve.TCLin SGPT.TestCurve.TCOko
open SGPT.Projective.NumEq.AlgebraicCurveDegree
open SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} {L : X.Modules}
  {a : LineBundleAtlas L} (T : TestConfiguration f a)

/-- Original relative ampleness yields actual H1 vanishing on the ENTIRE original central fibre. -/
theorem centralFiber_exists_sheafH1_bound (hA : T.IsAmple) :
    ∃ B : ℕ, ∀ m : ℕ, B ≤ m → Subsingleton
      (CategoryTheory.Sheaf.H (bundleTensorPower (centralFiberLine T) m).sheaf 1) := by
  obtain ⟨P⟩ := centralFiber_exists_amplePolarization T hA
  exact exists_originalAmple_sheafH1_bound (centralFiberAtlas T) P

private theorem originalAffinePullback_eq_unit {Y Z : Scheme.{0}} (j : Z ⟶ Y)
    (N : Y.Modules) (s : Γ(N, ⊤)) :
    Scheme.Modules.affinePullbackUnitTop j N s =
      (((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app N).val.app (op ⊤)) s := by
  let P := (Scheme.Modules.pullback j).obj N
  change P.presheaf.map (𝟙 (op ⊤))
    ((((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app N).val.app (op ⊤)) s) = _
  exact congrArg (fun q => q
    ((((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app N).val.app (op ⊤)) s))
      (P.presheaf.map_id (op ⊤))

/-- Eventual surjectivity of the SAME actual original restriction; no H1/base-change certificate input. -/
theorem exists_centralFiberRestriction_surjective [IsIntegral X]
    (E : ClosedProjectiveEmbedding f) (hA : T.IsAmple) :
    ∃ B : ℕ, ∀ m : ℕ, B ≤ m → Function.Surjective (centralFiberRestriction T m) := by
  let : IsIntegral T.space := T.isIntegral_space_of_embedding E
  let : IsDominant T.toLine := toLine_isDominant T
  obtain ⟨B, hB⟩ := centralFiber_exists_sheafH1_bound T hA
  refine ⟨B, fun m hm => ?_⟩
  let j := centralFiberInclusion T
  let N := bundleTensorPower T.line m
  let e := originalLinePullbackPowerIso j T.atlas m
  let eH := (CategoryTheory.Sheaf.functorH
    (_root_.Opens.grothendieckTopology (centralFiberScheme T)) 1).mapIso
      ((Scheme.Modules.toSheaf (centralFiberScheme T)).mapIso e)
  have h0 : Subsingleton (CategoryTheory.Sheaf.H ((Scheme.Modules.pullback j).obj N).sheaf 1) :=
    AddCommGrpCat.subsingleton_of_isZero
      (IsZero.of_iso (@AddCommGrpCat.isZero_of_subsingleton _ (hB m hm)) eH)
  have hsurj := SGPT.Foundations.Envelope.ProjectiveCentralFiberSectionLifting.restriction_surjective_of_hone_zero
    T.toLine (toLine_projectiveFactorization_of_ample T hA) N
      (originalAtlas_isInvertible (T.atlas.tensorPower m)) h0
  intro σ
  let y := e.inv.val.app (op ⊤) σ
  obtain ⟨s, hs⟩ := hsurj y
  refine ⟨s, ?_⟩
  have hunit : (((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app N).val.app (op ⊤)) s = y :=
    (originalAffinePullback_eq_unit j N s).symm.trans hs
  change e.hom.val.app (op ⊤)
    ((((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app N).val.app (op ⊤)) s) = σ
  rw [hunit]
  exact congrArg (fun q => q.val.app (op ⊤) σ) e.inv_hom_id

/-- The SAME quotient restriction is genuinely bijective at all sufficiently large degrees. -/
theorem exists_centralFiberQuotientRestriction_bijective [IsIntegral X]
    (E : ClosedProjectiveEmbedding f) (hA : T.IsAmple) :
    ∃ B : ℕ, ∀ m : ℕ, B ≤ m → Function.Bijective (centralFiberQuotientRestriction T m) := by
  obtain ⟨B, hB⟩ := exists_centralFiberRestriction_surjective T E hA
  refine ⟨B, fun m hm => ⟨centralFiberQuotientRestriction_injective T E m, ?_⟩⟩
  intro σ
  obtain ⟨s, hs⟩ := hB m hm σ
  exact ⟨(LinearMap.range (tMul T m)).mkQ s, hs⟩

/-- Actual eventual modulo-t/ENTIRE-central-H0 linear isomorphisms with the literal original map. -/
theorem exists_eventual_centralFiberBaseChange [IsIntegral X]
    (E : ClosedProjectiveEmbedding f) (hA : T.IsAmple) :
    ∃ B : ℕ, ∀ m : ℕ, B ≤ m →
      ∃ e : CentralQuotient T m ≃ₗ[ℂ] centralFiberSectionSpace T m,
        e.toLinearMap = centralFiberQuotientRestriction T m := by
  obtain ⟨B, hB⟩ := exists_centralFiberQuotientRestriction_bijective T E hA
  exact ⟨B, fun m hm => ⟨LinearEquiv.ofBijective (centralFiberQuotientRestriction T m) (hB m hm), rfl⟩⟩

end SGPT.TestCurve.CentralFiber
