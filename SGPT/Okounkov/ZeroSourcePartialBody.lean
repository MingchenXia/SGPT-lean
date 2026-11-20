import SGPT.Okounkov.ValuativeTestCurve
import SGPT.Okounkov.TranscendentalCoreGentleSum
import SGPT.NPP.DimensionZero
import SGPT.Hodge.BDivChainZero
import SGPT.Foundations.Analysis.Pending.MeteredDivisorOperations

/-!
# Genuine zero-dimensional source partial bodies

Source: revised SGPT 69360cfd, the zero-dimensional branch of `thm:Okountescurvex`.

The actual valuation closure is proved nonempty using a
zero gentle Kähler current below the given finite potential. The source
resolution formula uses an actual identity lifting, zero metered divisor
and bounded original potential. The Kähler-approximation and perturbation
intersections are retained before passing to a singleton convex body.
-/

set_option autoImplicit false
noncomputable section
universe u

namespace SGPT.Okounkov.ZeroSource

open Set Filter MeasureTheory
open scoped Topology ENNReal Matrix Pointwise
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.FirstPass.GlobalAnalyticSingularities
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
open SGPT.Foundations.Analysis.Pending.IdealWeightPowers
open SGPT.PSH SGPT.Okounkov.TranscendentalCore SGPT.Okounkov.TranscendentalPartial
open SGPT.Okounkov.TranscendentalLifting
open SGPT.Okounkov.PartialBody SGPT.PSH.VariableComplexAtlas

variable (F : OriginalFlagGeometry.{u} 0)

/-- Every original zero-dimensional positive potential is a Kähler current. -/
theorem isKahler_of_thetaPsh {θ : ClosedRealOneOneForm 0 F.carrier}
    {u : F.carrier → EReal} (hu : IsThetaPshPotential θ.val u) :
    IsKahlerCurrentPotential θ u := by
  refine ⟨F.omega, ?_⟩
  simpa only [SGPT.Hodge.BDivChain.closedRealOneOneForm_eq_zero_of_dim_zero F.omega.form,
    sub_zero] using hu

/-- Every genuine zero-dimensional potential is finite and constant on the
actual connected carrier. The finite real value is produced, not assumed. -/
theorem exists_real_constant {θ : ClosedRealOneOneForm 0 F.carrier}
    {u : F.carrier → EReal} (hu : IsThetaPshPotential θ.val u) :
    ∃ a : ℝ, ∀ x, u x = (a : EReal) := by
  let : Subsingleton F.carrier := SGPT.NPP.subsingleton_of_dim_zero
  obtain ⟨x₀⟩ := (inferInstance : Nonempty F.carrier)
  have htop := hu.1.quasiPlurisubharmonic.ne_top x₀
  have hbot := RooftopDimZero.ne_bot_of_locallyNondegenerate_of_dim_zero rfl hu.2 x₀
  lift u x₀ to ℝ using ⟨htop, hbot⟩ with a ha
  exact ⟨a, fun x => by rw [Subsingleton.elim x x₀, ha]⟩

/-- A true zero gentle Kähler current lies below the given finite source
potential, so its actual valuation participates in the generating set. -/
theorem zero_mem_gentleKahlerCurrentsBelow {θ : ClosedRealOneOneForm 0 F.carrier}
    {u : F.carrier → EReal} (hu : IsThetaPshPotential θ.val u) :
    (fun _ : F.carrier => (0 : EReal)) ∈ gentleKahlerCurrentsBelow θ u := by
  have hz : IsThetaPshPotential θ.val (fun _ : F.carrier => (0 : EReal)) :=
    RooftopDimZero.isThetaPshPotential_of_dim_zero rfl
      (LocalPotentials.closedRealOneOne_hasLocalPotentials θ)
      (fun _ => EReal.coe_ne_top 0) (fun _ => EReal.coe_ne_bot 0)
  have hgentle : SourceGentleAnalyticSingularities (fun _ : F.carrier => (0 : EReal))
      1 (unitIdeal 0 F.carrier) :=
    ⟨⟨θ, hz⟩, hasGentleAnalyticSingularitiesOfType_zero ⟨F.omega⟩⟩
  obtain ⟨a, ha⟩ := exists_real_constant F hu
  refine ⟨⟨⟨hz, 1, unitIdeal 0 F.carrier, hgentle⟩,
    isKahler_of_thetaPsh F hz⟩, -a, ?_⟩
  intro x _
  rw [ha x, ← EReal.coe_add, add_neg_cancel, EReal.coe_zero]

/-- The actual source valuation closure is the unique zero-dimensional
vector space, with a genuine current witness for nonemptiness. -/
theorem partialOkounkovBody_eq_univ {θ : ClosedRealOneOneForm 0 F.carrier}
    {u : F.carrier → EReal} (hu : IsThetaPshPotential θ.val u) :
    partialOkounkovBody F θ u = univ := by
  apply eq_univ_of_forall
  intro x
  have hmem := flagValuation_mem_partialOkounkovBody
    (F := F) (zero_mem_gentleKahlerCurrentsBelow F hu)
  simpa only [Subsingleton.elim x
    (flagValuation F (fun _ : F.carrier => (0 : EReal)))] using hmem

/-- The traditional valuation body of every actual zero-dimensional class
also has a genuine generating potential, the original zero potential. -/
theorem tradOkounkovBody_eq_univ (θ : ClosedRealOneOneForm 0 F.carrier) :
    tradOkounkovBody F θ = univ := by
  have hz : IsThetaPshPotential θ.val (fun _ : F.carrier => (0 : EReal)) :=
    RooftopDimZero.isThetaPshPotential_of_dim_zero rfl
      (LocalPotentials.closedRealOneOne_hasLocalPotentials θ)
      (fun _ => EReal.coe_ne_top 0) (fun _ => EReal.coe_ne_bot 0)
  apply eq_univ_of_forall
  intro x
  apply partialOkounkovBody_subset_tradOkounkovBody θ (fun _ => (0 : EReal))
  rw [partialOkounkovBody_eq_univ F hz]
  exact mem_univ x

/-- The actual identity map lifts the original zero-dimensional flag. -/
theorem identityFlagLifting : IsFlagLifting F F id := by
  refine ⟨isAnalyticModification_identity, fun i => ⟨fun _ h => h, ?_⟩⟩
  let := F.componentCharts i
  let := F.componentComplex i
  change IsAnalyticModification (n := 0 - (i : ℕ)) (id : F.flag i → F.flag i)
  exact isAnalyticModification_identity

/-- Literal zero-dimensional counterpart of the source resolution premises:
a genuine map/lifting, divisor, and bounded residual decomposition. -/
structure Resolution (θ : ClosedRealOneOneForm 0 F.carrier) (u : F.carrier → EReal)
    {W : OriginalFlagGeometry.{u} 0} {π : W.carrier → F.carrier}
    (hπ : IsFlagLifting F W π) (D : MeteredEffectiveQDivisor 0 W.carrier)
    (b : W.carrier → EReal) : Prop where
  psh : IsThetaPshPotential (ClosedRealOneOneForm.pullback hπ.1.1 θ - D.curvature).val b
  bounded : ∃ C : ℝ, ∀ y, ((-C : ℝ) : EReal) ≤ b y ∧ b y ≤ (C : EReal)
  eq : ∀ y, u (π y) = D.weight y + b y

/-- The original source potential itself supplies the bounded residual in
an actual identity/zero-divisor resolution. -/
theorem identityResolution {θ : ClosedRealOneOneForm 0 F.carrier}
    {u : F.carrier → EReal} (hu : IsThetaPshPotential θ.val u) :
    Resolution F θ u (identityFlagLifting F) (MeteredDivisorOperations.zero 0 F.carrier) u := by
  refine ⟨?_, ?_, ?_⟩
  · have hform : ClosedRealOneOneForm.pullback (identityFlagLifting F).1.1 θ -
        (MeteredDivisorOperations.zero 0 F.carrier).curvature = θ :=
      (SGPT.Hodge.BDivChain.closedRealOneOneForm_eq_zero_of_dim_zero _).trans
        (SGPT.Hodge.BDivChain.closedRealOneOneForm_eq_zero_of_dim_zero θ).symm
    rw [hform]
    exact hu
  · obtain ⟨a, ha⟩ := exists_real_constant F hu
    refine ⟨|a|, fun y => ?_⟩
    rw [ha y]
    exact ⟨EReal.coe_le_coe_iff.mpr (neg_abs_le a),
      EReal.coe_le_coe_iff.mpr (le_abs_self a)⟩
  · intro y
    simp only [MeteredDivisorOperations.zero, zero_add, id_eq]

/-- Original resolution choices, with no body equality as an input field. -/
structure ResolutionData (θ : ClosedRealOneOneForm 0 F.carrier) (u : F.carrier → EReal) where
  model : OriginalFlagGeometry.{u} 0
  map : model.carrier → F.carrier
  lifting : IsFlagLifting F model map
  divisor : MeteredEffectiveQDivisor 0 model.carrier
  residual : model.carrier → EReal
  valid : Resolution F θ u lifting divisor residual

/-- Actual source resolution choices exist for every given genuine potential. -/
theorem nonempty_resolutionData {θ : ClosedRealOneOneForm 0 F.carrier}
    {u : F.carrier → EReal} (hu : IsThetaPshPotential θ.val u) :
    Nonempty (ResolutionData F θ u) :=
  ⟨⟨F, id, identityFlagLifting F, MeteredDivisorOperations.zero 0 F.carrier,
    u, identityResolution F hu⟩⟩

/-- The source's actual resolution formula, retaining the given model,
curvature, correction matrix and valuation shift, in dimension zero. -/
def analyticBodyOf (θ : ClosedRealOneOneForm 0 F.carrier)
    {W : OriginalFlagGeometry.{u} 0} {π : W.carrier → F.carrier}
    (hπ : IsFlagLifting F W π) (D : MeteredEffectiveQDivisor 0 W.carrier) : Set (Fin 0 → ℝ) :=
  (flagValuation W D.weight ᵥ* (correctionMatrixReal hπ)⁻¹) +ᵥ
    ((fun x => x ᵥ* (correctionMatrixReal hπ)⁻¹) ''
      tradOkounkovBody W (ClosedRealOneOneForm.pullback hπ.1.1 θ - D.curvature))

/-- Every actual source resolution gives the same genuine valuation body. -/
theorem analyticBodyOf_eq_univ (θ : ClosedRealOneOneForm 0 F.carrier)
    {W : OriginalFlagGeometry.{u} 0} {π : W.carrier → F.carrier}
    (hπ : IsFlagLifting F W π) (D : MeteredEffectiveQDivisor 0 W.carrier) :
    analyticBodyOf F θ hπ D = univ := by
  rw [analyticBodyOf, tradOkounkovBody_eq_univ]
  have himg : (fun x : Fin 0 → ℝ => x ᵥ* (correctionMatrixReal hπ)⁻¹) '' univ = univ := by
    apply eq_univ_of_forall
    intro x
    exact ⟨0, mem_univ _, Subsingleton.elim _ _⟩
  rw [himg]
  simp

/-- The literal source analytic body, choosing actual proved resolution
premises rather than supplying a singleton body as a parameter. -/
def analyticBody (θ : ClosedRealOneOneForm 0 F.carrier) (u : F.carrier → EReal)
    (hu : IsThetaPshPotential θ.val u) : Set (Fin 0 → ℝ) :=
  let R := Classical.choice (nonempty_resolutionData F hu)
  analyticBodyOf F θ R.lifting R.divisor

/-- The book's resolution formula equals its true valuation-closure body. -/
theorem analyticBody_eq_partial (θ : ClosedRealOneOneForm 0 F.carrier)
    (u : F.carrier → EReal) (hu : IsThetaPshPotential θ.val u) :
    analyticBody F θ u hu = partialOkounkovBody F θ u := by
  rw [partialOkounkovBody_eq_univ F hu]
  exact analyticBodyOf_eq_univ F θ _ _

/-- The actual source Kähler-current approximants are produced, including
in dimension zero, from the already verified regularization theorem. -/
theorem exists_kahlerApproximation {θ : ClosedRealOneOneForm 0 F.carrier}
    {u : F.carrier → EReal} (hu : IsThetaPshPotential θ.val u) :
    ∃ U, IsKahlerQEA θ u U :=
  exists_isKahlerQEA (isKahler_of_thetaPsh F hu)

/-- Original approximation intersection, with actual source terms. -/
def kahlerBodyOf (θ : ClosedRealOneOneForm 0 F.carrier)
    {u : F.carrier → EReal} (U : ℕ → F.carrier → EReal) (hU : IsKahlerQEA θ u U) :
    Set (Fin 0 → ℝ) :=
  ⋂ j, analyticBody F θ (U j) (hU.2 j).1.1

/-- Every source Kähler approximation gives the same true partial body. -/
theorem kahlerBodyOf_eq_partial {θ : ClosedRealOneOneForm 0 F.carrier}
    {u : F.carrier → EReal} (hu : IsThetaPshPotential θ.val u)
    (U : ℕ → F.carrier → EReal) (hU : IsKahlerQEA θ u U) :
    kahlerBodyOf F θ U hU = partialOkounkovBody F θ u := by
  rw [partialOkounkovBody_eq_univ F hu]
  unfold kahlerBodyOf
  have hterm : ∀ j, analyticBody F θ (U j) (hU.2 j).1.1 = univ := by
    intro j
    rw [analyticBody_eq_partial, partialOkounkovBody_eq_univ F (hU.2 j).1.1]
  simp only [hterm, iInter_univ]

/-- Original Kähler-current body defined through a produced actual approximation. -/
def kahlerBody (θ : ClosedRealOneOneForm 0 F.carrier) (u : F.carrier → EReal)
    (hu : IsThetaPshPotential θ.val u) : Set (Fin 0 → ℝ) :=
  let h := exists_kahlerApproximation F hu
  kahlerBodyOf F θ (Classical.choose h) (Classical.choose_spec h)

/-- The chosen source approximation is identified with the true closure. -/
theorem kahlerBody_eq_partial (θ : ClosedRealOneOneForm 0 F.carrier)
    (u : F.carrier → EReal) (hu : IsThetaPshPotential θ.val u) :
    kahlerBody F θ u hu = partialOkounkovBody F θ u := by
  let h := exists_kahlerApproximation F hu
  exact kahlerBodyOf_eq_partial F hu (Classical.choose h) (Classical.choose_spec h)

/-- The source's positive Kähler perturbation at its exact integer index. -/
def perturbation (θ : ClosedRealOneOneForm 0 F.carrier) (j : ℕ) :
    ClosedRealOneOneForm 0 F.carrier :=
  θ + ((j : ℝ) + 1)⁻¹ • F.omega.form

/-- The perturbation is a genuine source theta-PSH background for the same potential. -/
theorem thetaPsh_perturbation {θ : ClosedRealOneOneForm 0 F.carrier}
    {u : F.carrier → EReal} (hu : IsThetaPshPotential θ.val u) (j : ℕ) :
    IsThetaPshPotential (perturbation F θ j).val u := by
  simpa only [perturbation,
    SGPT.Hodge.BDivChain.closedRealOneOneForm_eq_zero_of_dim_zero F.omega.form,
    smul_zero, add_zero] using hu

/-- The final original book definition keeps its full perturbation/intersection. -/
def generalBody (θ : ClosedRealOneOneForm 0 F.carrier) (u : F.carrier → EReal)
    (hu : IsThetaPshPotential θ.val u) : Set (Fin 0 → ℝ) :=
  ⋂ j, kahlerBody F (perturbation F θ j) u (thetaPsh_perturbation F hu j)

/-- Source resolution, source approximation and source perturbation bodies
are identified before any singleton convex-body packaging. -/
theorem generalBody_eq_partial (θ : ClosedRealOneOneForm 0 F.carrier)
    (u : F.carrier → EReal) (hu : IsThetaPshPotential θ.val u) :
    generalBody F θ u hu = partialOkounkovBody F θ u := by
  rw [partialOkounkovBody_eq_univ F hu]
  unfold generalBody
  have hterm : ∀ j, kahlerBody F (perturbation F θ j) u
      (thetaPsh_perturbation F hu j) = univ := by
    intro j
    rw [kahlerBody_eq_partial, partialOkounkovBody_eq_univ F (thetaPsh_perturbation F hu j)]
  simp only [hterm, iInter_univ]

/-- The actual source general body as the actual Euclidean-space carrier. -/
theorem euclidean_generalBody_eq_singleton_zero (θ : ClosedRealOneOneForm 0 F.carrier)
    (u : F.carrier → EReal) (hu : IsThetaPshPotential θ.val u) :
    TranscendentalMain.euclideanImage (generalBody F θ u hu) =
      ({0} : Set (EuclideanSpace ℝ (Fin 0))) := by
  rw [generalBody_eq_partial, partialOkounkovBody_eq_univ F hu]
  ext x
  constructor
  · intro _
    exact Subsingleton.elim _ _
  · intro _
    exact ⟨0, mem_univ _, Subsingleton.elim _ _⟩

/-- The convex-body structure packages the original source general body,
after its genuine geometric and approximation bridges have been proved. -/
def partialConvexBody (θ : ClosedRealOneOneForm 0 F.carrier)
    (u : F.carrier → EReal) (hu : IsThetaPshPotential θ.val u) :
    ConvexBody (EuclideanSpace ℝ (Fin 0)) where
  carrier := TranscendentalMain.euclideanImage (generalBody F θ u hu)
  convex' := by rw [euclidean_generalBody_eq_singleton_zero F θ u hu]; exact convex_singleton 0
  isCompact' := by rw [euclidean_generalBody_eq_singleton_zero F θ u hu]; exact isCompact_singleton
  nonempty' := by rw [euclidean_generalBody_eq_singleton_zero F θ u hu]; exact singleton_nonempty 0

/-- Exact source carrier readback. -/
theorem coe_partialConvexBody (θ : ClosedRealOneOneForm 0 F.carrier)
    (u : F.carrier → EReal) (hu : IsThetaPshPotential θ.val u) :
    (partialConvexBody F θ u hu : Set (EuclideanSpace ℝ (Fin 0))) =
      TranscendentalMain.euclideanImage (generalBody F θ u hu) := rfl

/-- The genuine source bodies are all equal after their original carriers
have been proved to be the same unique zero-dimensional vector. -/
theorem partialConvexBody_eq (θ θ' : ClosedRealOneOneForm 0 F.carrier)
    (u v : F.carrier → EReal) (hu : IsThetaPshPotential θ.val u)
    (hv : IsThetaPshPotential θ'.val v) :
    partialConvexBody F θ u hu = partialConvexBody F θ' v hv := by
  apply ConvexBody.ext
  exact (euclidean_generalBody_eq_singleton_zero F θ u hu).trans
    (euclidean_generalBody_eq_singleton_zero F θ' v hv).symm

end SGPT.Okounkov.ZeroSource
