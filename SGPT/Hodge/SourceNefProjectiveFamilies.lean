import SGPT.Hodge.SourceNefSmoothShift

set_option autoImplicit false
noncomputable section
universe u

namespace SGPT.Hodge.BDivChain.SourceNefProjectiveDraft

open Set Filter SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending
  SGPT.PSH.VariableComplexAtlas SGPT.BDivisor SGPT.Hodge.BDivChain.NativeDraft
  SGPT.Hodge.BDivChain.SourceCorrespondenceDraft
open scoped Topology ENNReal

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [CompactSpace X] [ConnectedSpace X]

omit [ConnectedSpace X] in
/-- Original nefness is detected by ALL genuine Kähler shifts. The epsilon
sequence appears only internally in the proof of the closed-cone limit. -/
theorem isNefAny_of_forall_add_rootKahler (ω : KahlerBackground n X)
    (D : WeilFamilyAny (ModelSystem.blowup n X))
    (hD : ∀ κ : KahlerBackground n X,
      IsNefAny (D + rootCartierAny (RealBottChern.ofRepresentative κ.form))) : IsNefAny D := by
  cases n with
  | zero => exact isNefAny_zero D
  | succ m =>
    rw [isNefAny_iff_existing (Nat.succ_pos m)]
    let ε : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
    let κ : ℕ → KahlerBackground (m + 1) X := fun k =>
      KahlerBackground.smul (by dsimp [ε]; positivity : 0 < ε k) ω
    have hshift : ∀ k : ℕ, (toExisting _ (Nat.succ_pos m) D +
        ε k • rootCartier (RealBottChern.ofRepresentative ω.form)).IsNef := by
      intro k
      have h := (isNefAny_iff_existing (Nat.succ_pos m) _).mp (hD (κ k))
      have he : toExisting _ (Nat.succ_pos m)
          (D + rootCartierAny (RealBottChern.ofRepresentative (κ k).form)) =
          toExisting _ (Nat.succ_pos m) D +
            ε k • rootCartier (RealBottChern.ofRepresentative ω.form) := by
        apply WeilBDivisorOn.ext
        intro π
        change D.val π +
          (rootCartierAny (RealBottChern.ofRepresentative (ε k • ω.form))).val π = _
        rw [RealBottChern.ofRepresentative_smul, rootCartierAny_smul]
        rfl
      exact he ▸ h
    apply WeilBDivisorOn.IsNef.of_converges hshift
    rw [WeilBDivisorOn.converges_iff_forall_dual]
    intro π f
    simp_rw [WeilBDivisorOn.add_onModel, WeilBDivisorOn.smul_onModel,
      map_add, map_smul, smul_eq_mul]
    have hε : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    simpa using tendsto_const_nhds.add
      (hε.mul_const (f ((rootCartier (RealBottChern.ofRepresentative ω.form)).onModel π)))

/-- Exact original root-alpha nef families, with no positive-volume restriction. -/
def NefRoot (α : RealBottChern n X) :=
  {D : WeilFamilyAny (ModelSystem.blowup n X) //
    IsNefAny D ∧ D.val ModelSystem.Model.root = α}

/-- Every geometric Kähler form is an index, represented by its actual closed form. -/
def indexClass (κ : SourceKahlerForm n X) : RealBottChern n X :=
  RealBottChern.ofRepresentative (sourceKahlerFormRepresentative κ).form

def indexCartier (κ : SourceKahlerForm n X) : WeilFamilyAny (ModelSystem.blowup n X) :=
  rootCartierAny (indexClass κ)

def indexDifference (κ ζ : SourceKahlerForm n X) : ClosedRealOneOneForm n X :=
  (sourceKahlerFormRepresentative ζ).form - (sourceKahlerFormRepresentative κ).form

omit [CompactSpace X] [ConnectedSpace X] in
theorem indexDifference_class (κ ζ : SourceKahlerForm n X) :
    RealBottChern.ofRepresentative (indexDifference κ ζ) = indexClass ζ - indexClass κ := by
  exact map_sub RealBottChern.ofRepresentativeLinearMap _ _

omit [ConnectedSpace X] in
theorem indexDifference_cartier (κ ζ : SourceKahlerForm n X) :
    rootCartierAny (RealBottChern.ofRepresentative (indexDifference κ ζ)) =
      indexCartier ζ - indexCartier κ := by
  rw [indexDifference_class, rootCartierAny_sub]
  rfl

omit [ConnectedSpace X] in
theorem indexCartier_root (κ : SourceKahlerForm n X) :
    (indexCartier κ).val ModelSystem.Model.root = indexClass κ := rootCartierAny_root _

/-- The actual shifted family belongs to the entire original big-nef component. -/
def nefRootComponent (ω : KahlerBackground n X) (α : RealBottChern n X)
    (D : NefRoot α) (κ : SourceKahlerForm n X) : BigNefRoot (α + indexClass κ) :=
  ⟨D.val + indexCartier κ,
    volumeAny_pos_add_rootKahler ω D.val D.property.1 (sourceKahlerFormRepresentative κ),
    isNefAny_add_root_semipositive ω D.val D.property.1 _
      (sourceKahlerFormRepresentative κ).isSemipositive,
    by
      change D.val.val ModelSystem.Model.root +
        (indexCartier κ).val ModelSystem.Model.root = α + indexClass κ
      rw [D.property.2, indexCartier_root]
      rfl⟩

/-- The original smooth-addition transition on entire big-nef components. -/
def bigNefTransition (ω : KahlerBackground n X) (α : RealBottChern n X)
    {κ ζ : SourceKahlerForm n X} (hκζ : sourceKahlerFormLE κ ζ)
    (D : BigNefRoot (α + indexClass κ)) : BigNefRoot (α + indexClass ζ) :=
  ⟨D.val + rootCartierAny (RealBottChern.ofRepresentative (indexDifference κ ζ)),
    D.property.1.trans_le (volumeAny_le_add_root_semipositive ω D.val D.property.2.1 _ hκζ),
    isNefAny_add_root_semipositive ω D.val D.property.2.1 _ hκζ,
    by
      change D.val.val ModelSystem.Model.root +
        (rootCartierAny (RealBottChern.ofRepresentative (indexDifference κ ζ))).val
          ModelSystem.Model.root = α + indexClass ζ
      rw [D.property.2.2, rootCartierAny_root, indexDifference_class]
      abel⟩

/-- The literal all-Kähler-index compatible family, with reverse-domination
orientation: κ≤ζ has transition from the κ component to the ζ component. -/
def BigNefProjectiveLimit (ω : KahlerBackground n X) (α : RealBottChern n X) :=
  {F : ∀ κ : SourceKahlerForm n X, BigNefRoot (α + indexClass κ) //
    ∀ (κ ζ : SourceKahlerForm n X) (h : sourceKahlerFormLE κ ζ),
      bigNefTransition ω α h (F κ) = F ζ}

end SGPT.Hodge.BDivChain.SourceNefProjectiveDraft
