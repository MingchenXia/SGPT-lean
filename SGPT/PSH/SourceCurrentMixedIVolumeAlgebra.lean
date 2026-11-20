import SGPT.PSH.SourceCurrentMixedIVolume
import SGPT.PSH.SourceGeneralMixedIVolumeAlgebra
import SGPT.Okounkov.ThetaPotentialCurrentCombinations
import SGPT.Okounkov.CurrentFlagValuationOrder

/-! # Five mixed I-volume laws for the original whole positive currents

Natural current domains and genuine representations are produced internally.
The separate Reg clause is not asserted. Actual degree-two current scope is
positive dimension; the existing represented laws retain dimension zero.
-/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas

open Set MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.IEnvelope
open SGPT.Foundations.Analysis.Pending
open NaturalThetaPshGeometricCurrent NaturalThetaPshClosedCurrent CanonicalCurrentFrame
open GlobalPositiveCurrentACRestriction CurrentBottChernClass

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]

/-- The original existential genuine-potential multiplier order, on arbitrary
original whole currents. No flag or selected representation is part of the input. -/
def sourceCurrentIOrder
    (T S : GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m))) : Prop :=
  ∃ (θ σ : ClosedRealOneOneForm (m + 1) M) (u v : M → EReal)
    (hu : IsThetaPshPotential θ.val u) (hv : IsThetaPshPotential σ.val v),
    T = thetaPotentialCurrent θ.val u hu ∧
    S = thetaPotentialCurrent σ.val v hv ∧ IOrderOnManifold (n := m + 1) u v

/-- Every genuine presentation reads the same original current multiplier order. -/
theorem sourceCurrentIOrder_iff_of_representation (ω : KahlerBackground (m + 1) M)
    {T S : GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m))}
    {θ σ : ClosedRealOneOneForm (m + 1) M} {u v : M → EReal}
    (hu : IsThetaPshPotential θ.val u) (hv : IsThetaPshPotential σ.val v)
    (hT : T = thetaPotentialCurrent θ.val u hu)
    (hS : S = thetaPotentialCurrent σ.val v hv) :
    sourceCurrentIOrder T S ↔ IOrderOnManifold (n := m + 1) u v := by
  constructor
  · rintro ⟨θ₀, σ₀, u₀, v₀, hu₀, hv₀, hT₀, hS₀, hI₀⟩
    have hleft := SGPT.Okounkov.iEquivalent_of_thetaPotentialCurrent_eq ω hu hu₀
      (hT.symm.trans hT₀)
    have hright := SGPT.Okounkov.iEquivalent_of_thetaPotentialCurrent_eq ω hv₀ hv
      (hS₀.symm.trans hS)
    exact hleft.1.trans (hI₀.trans hright.1)
  · exact fun hI => ⟨θ, σ, u, v, hu, hv, hT, hS, hI⟩

/-- The generic intrinsic relation specializes to the existing original flag
relation by its exact existential formula, without a replacement convention. -/
theorem sourceCurrentIOrder_iff_originalFlag (F : SGPT.Okounkov.OriginalFlagGeometry (m + 1))
    (T S : GlobalCurrent (m + 1) F.carrier (degreeTwo (Nat.succ_pos m))) :
    sourceCurrentIOrder T S ↔ SGPT.Okounkov.OriginalCurrentsIOrder F T S := Iff.rfl

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
private theorem nativePSHToSource {θ : ClosedRealOneOneForm (m + 1) M} {u : M → EReal}
    (hu : IsThetaPshPotential θ.val u) :
    (ofFixedModel (m + 1) M).IsThetaPSH (nativeClosedFormToAtlas θ) u := by
  apply (isThetaPSH_iff_nativeThetaPotential _ _).mpr
  simpa only [sourceNativeAtlasForm_roundTrip] using hu

omit [MeasurableSpace M] [BorelSpace M] [ConnectedSpace M] in
private theorem tupleRepresentation
    (T : Fin (m + 1) → GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m)))
    (hc : ∀ i, (T i).IsClosed (canonicalBasis (m + 1)))
    (h11 : ∀ i, (T i).IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m))
    (hp : ∀ i, IsFullPositive (T i)) :
    ∃ (θ : Fin (m + 1) → ClosedRealOneOneForm (m + 1) M)
      (u : Fin (m + 1) → M → EReal) (hu : ∀ i, IsThetaPshPotential (θ i).val (u i)),
      ∀ i, T i = thetaPotentialCurrent (θ i).val (u i) (hu i) := by
  choose θ u hu hread hchart using fun i =>
    OriginalPositiveCurrentThetaRepresentation.exists_theta_representation_of_original_closed_full_positive
      (T i) (hc i) (h11 i) (hp i)
  exact ⟨θ, u, hu, hread⟩

private theorem updatedProperty {C : Type*} {P : C → Prop}
    {T : Fin (m + 1) → C} (hT : ∀ i, P (T i)) (a : Fin (m + 1))
    {S : C} (hS : P S) : ∀ i, P (Function.update T a S i) := by
  intro i
  by_cases hi : i = a
  · subst i
    simpa only [Function.update_self] using hS
  · simpa only [Function.update_of_ne hi] using hT i

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
private theorem updatedNativePSH
    {θ : Fin (m + 1) → ClosedRealOneOneForm (m + 1) M} {u : Fin (m + 1) → M → EReal}
    (hu : ∀ i, IsThetaPshPotential (θ i).val (u i)) (a : Fin (m + 1))
    {σ : ClosedRealOneOneForm (m + 1) M} {v : M → EReal}
    (hv : IsThetaPshPotential σ.val v) :
    ∀ i, IsThetaPshPotential (Function.update θ a σ i).val (Function.update u a v i) := by
  intro i
  by_cases hi : i = a
  · subst i
    simpa only [Function.update_self] using hv
  · simpa only [Function.update_of_ne hi] using hu i

omit [BorelSpace M] in
private theorem representedVolume_congr
    {θ η : Fin (m + 1) → AtlasClosedRealOneOneForm (ofFixedModel (m + 1) M)}
    {u v : Fin (m + 1) → M → EReal}
    (ω : KahlerBackground (m + 1) M)
    (hu : ∀ i, (ofFixedModel (m + 1) M).IsThetaPSH (θ i) (u i))
    (hv : ∀ i, (ofFixedModel (m + 1) M).IsThetaPSH (η i) (v i))
    (hθ : θ = η) (huv : u = v) :
    sourceGeneralMixedIVolume ω θ u hu = sourceGeneralMixedIVolume ω η v hv := by
  subst η
  subst v
  rfl

/-- Symmetry for arbitrary original closed fully positive current tuples,
including currents of zero original I-volume. -/
theorem sourceCurrentMixedIVolume_perm (ω : KahlerBackground (m + 1) M)
    (T : Fin (m + 1) → GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m)))
    (hc : ∀ i, (T i).IsClosed (canonicalBasis (m + 1)))
    (h11 : ∀ i, (T i).IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m))
    (hp : ∀ i, IsFullPositive (T i)) (π : Equiv.Perm (Fin (m + 1))) :
    sourceCurrentMixedIVolume ω (fun i => T (π i)) (fun i => hc (π i))
      (fun i => h11 (π i)) (fun i => hp (π i)) = sourceCurrentMixedIVolume ω T hc h11 hp := by
  obtain ⟨θ, u, hu, hread⟩ := tupleRepresentation T hc h11 hp
  rw [sourceCurrentMixedIVolume_eq_representation ω _ _ _ _
      (fun i => θ (π i)) (fun i => u (π i)) (fun i => hu (π i)) (fun i => hread (π i)),
    sourceCurrentMixedIVolume_eq_representation ω T hc h11 hp θ u hu hread]
  exact sourceGeneralMixedIVolume_perm ω _ u (fun i => nativePSHToSource (hu i)) π

/-- Independent addition on the ORIGINAL current in every slot. All three
natural properties of the sum current are OUTPUTS; no sum-domain assumption. -/
theorem sourceCurrentMixedIVolume_add_slot (ω : KahlerBackground (m + 1) M)
    (T : Fin (m + 1) → GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m)))
    (hc : ∀ i, (T i).IsClosed (canonicalBasis (m + 1)))
    (h11 : ∀ i, (T i).IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m))
    (hp : ∀ i, IsFullPositive (T i)) (a : Fin (m + 1))
    (S : GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m)))
    (hSc : S.IsClosed (canonicalBasis (m + 1)))
    (hS11 : S.IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m)) (hSp : IsFullPositive S) :
    ∃ (hAc : (T a + S).IsClosed (canonicalBasis (m + 1)))
      (hA11 : (T a + S).IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m))
      (hAp : IsFullPositive (T a + S)),
      sourceCurrentMixedIVolume ω (Function.update T a (T a + S))
        (updatedProperty hc a hAc) (updatedProperty h11 a hA11) (updatedProperty hp a hAp) =
        sourceCurrentMixedIVolume ω T hc h11 hp +
        sourceCurrentMixedIVolume ω (Function.update T a S)
          (updatedProperty hc a hSc) (updatedProperty h11 a hS11) (updatedProperty hp a hSp) := by
  classical
  obtain ⟨θ, u, hu, hread⟩ := tupleRepresentation T hc h11 hp
  obtain ⟨σ, v, hv, hSread, _⟩ :=
    OriginalPositiveCurrentThetaRepresentation.exists_theta_representation_of_original_closed_full_positive
      S hSc hS11 hSp
  obtain ⟨huv, hsum⟩ := SGPT.Okounkov.exists_thetaPotentialCurrent_add (hu a) hv
  have hAread : T a + S = thetaPotentialCurrent (θ a + σ).val (fun x => u a x + v x) huv := by
    rw [hread a, hSread]
    exact hsum.symm
  obtain ⟨hAc, hA11, hAp⟩ :=
    thetaPotentialCurrent_closed_type_positive (θ a + σ).val (fun x => u a x + v x) huv
  rw [← hAread] at hAc hA11 hAp
  refine ⟨hAc, hA11, hAp, ?_⟩
  have hreadA : ∀ i, Function.update T a (T a + S) i =
      thetaPotentialCurrent (Function.update θ a (θ a + σ) i).val
        (Function.update u a (fun x => u a x + v x) i) (updatedNativePSH hu a huv i) := by
    intro i
    by_cases hi : i = a
    · subst i
      simpa only [Function.update_self] using hAread
    · simpa only [Function.update_of_ne hi] using hread i
  have hreadS : ∀ i, Function.update T a S i =
      thetaPotentialCurrent (Function.update θ a σ i).val
        (Function.update u a v i) (updatedNativePSH hu a hv i) := by
    intro i
    by_cases hi : i = a
    · subst i
      simpa only [Function.update_self] using hSread
    · simpa only [Function.update_of_ne hi] using hread i
  rw [sourceCurrentMixedIVolume_eq_representation ω _ _ _ _ _ _
      (updatedNativePSH hu a huv) hreadA,
    sourceCurrentMixedIVolume_eq_representation ω T hc h11 hp θ u hu hread,
    sourceCurrentMixedIVolume_eq_representation ω _ _ _ _ _ _
      (updatedNativePSH hu a hv) hreadS]
  have hform : (fun i => nativeClosedFormToAtlas (Function.update θ a (θ a + σ) i)) =
      Function.update (fun i => nativeClosedFormToAtlas (θ i)) a
        (nativeClosedFormToAtlas (atlasClosedFormToNative (nativeClosedFormToAtlas (θ a)) +
          atlasClosedFormToNative (nativeClosedFormToAtlas σ))) := by
    funext i
    by_cases hi : i = a
    · subst i
      simp only [Function.update_self, sourceNativeAtlasForm_roundTrip]
    · simp only [Function.update_of_ne hi]
  have hformS : (fun i => nativeClosedFormToAtlas (Function.update θ a σ i)) =
      Function.update (fun i => nativeClosedFormToAtlas (θ i)) a (nativeClosedFormToAtlas σ) := by
    funext i
    by_cases hi : i = a
    · subst i
      simp only [Function.update_self]
    · simp only [Function.update_of_ne hi]
  have hadd := sourceGeneralMixedIVolume_add_slot ω
    (fun i => nativeClosedFormToAtlas (θ i)) u (fun i => nativePSHToSource (hu i))
    a (nativeClosedFormToAtlas σ) v (nativePSHToSource hv)
  exact (representedVolume_congr ω _ _ hform rfl).trans
    (hadd.trans (congrArg (fun z => sourceGeneralMixedIVolume ω
      (fun i => nativeClosedFormToAtlas (θ i)) u (fun i => nativePSHToSource (hu i)) + z)
      (representedVolume_congr ω _ _ hformS.symm rfl)))

/-- Every original nonnegative REAL scalar, including zero. Natural scaled
current domains are produced before applying represented homogeneity. -/
theorem sourceCurrentMixedIVolume_nonneg_smul_slot (ω : KahlerBackground (m + 1) M)
    (T : Fin (m + 1) → GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m)))
    (hc : ∀ i, (T i).IsClosed (canonicalBasis (m + 1)))
    (h11 : ∀ i, (T i).IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m))
    (hp : ∀ i, IsFullPositive (T i)) (a : Fin (m + 1)) {c : ℝ} (hc0 : 0 ≤ c) :
    ∃ (hCc : (c • T a).IsClosed (canonicalBasis (m + 1)))
      (hC11 : (c • T a).IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m))
      (hCp : IsFullPositive (c • T a)),
      sourceCurrentMixedIVolume ω (Function.update T a (c • T a))
        (updatedProperty hc a hCc) (updatedProperty h11 a hC11) (updatedProperty hp a hCp) =
        ENNReal.ofReal c * sourceCurrentMixedIVolume ω T hc h11 hp := by
  classical
  obtain ⟨θ, u, hu, hread⟩ := tupleRepresentation T hc h11 hp
  obtain ⟨hcu, hscaled⟩ := SGPT.Okounkov.exists_thetaPotentialCurrent_nonneg_smul (hu a) hc0
  have hCread : c • T a =
      thetaPotentialCurrent (c • θ a).val (fun x => (c : EReal) * u a x) hcu := by
    rw [hread a]
    exact hscaled.symm
  obtain ⟨hCc, hC11, hCp⟩ :=
    thetaPotentialCurrent_closed_type_positive (c • θ a).val (fun x => (c : EReal) * u a x) hcu
  rw [← hCread] at hCc hC11 hCp
  refine ⟨hCc, hC11, hCp, ?_⟩
  have hreadC : ∀ i, Function.update T a (c • T a) i =
      thetaPotentialCurrent (Function.update θ a (c • θ a) i).val
        (Function.update u a (fun x => (c : EReal) * u a x) i) (updatedNativePSH hu a hcu i) := by
    intro i
    by_cases hi : i = a
    · subst i
      simpa only [Function.update_self] using hCread
    · simpa only [Function.update_of_ne hi] using hread i
  rw [sourceCurrentMixedIVolume_eq_representation ω _ _ _ _ _ _
      (updatedNativePSH hu a hcu) hreadC,
    sourceCurrentMixedIVolume_eq_representation ω T hc h11 hp θ u hu hread]
  have hform : (fun i => nativeClosedFormToAtlas (Function.update θ a (c • θ a) i)) =
      Function.update (fun i => nativeClosedFormToAtlas (θ i)) a
        (nativeClosedFormToAtlas (c • atlasClosedFormToNative (nativeClosedFormToAtlas (θ a)))) := by
    funext i
    by_cases hi : i = a
    · subst i
      simp only [Function.update_self, sourceNativeAtlasForm_roundTrip]
    · simp only [Function.update_of_ne hi]
  exact (representedVolume_congr ω _ _ hform rfl).trans
    (sourceGeneralMixedIVolume_nonneg_smul_slot ω _ u (fun i => nativePSHToSource (hu i)) a hc0)

/-- The book's actual current Bott--Chern classes and intrinsic current
multiplier order imply monotonicity, without restricting the manifold to a flag. -/
theorem sourceCurrentMixedIVolume_mono_of_class_eq_of_IOrder (ω : KahlerBackground (m + 1) M)
    (T S : Fin (m + 1) → GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m)))
    (hTc : ∀ i, (T i).IsClosed (canonicalBasis (m + 1)))
    (hT11 : ∀ i, (T i).IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m))
    (hTp : ∀ i, IsFullPositive (T i))
    (hSc : ∀ i, (S i).IsClosed (canonicalBasis (m + 1)))
    (hS11 : ∀ i, (S i).IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m))
    (hSp : ∀ i, IsFullPositive (S i))
    (hclass : ∀ i, bottChernClass (canonicalBasis (m + 1)) (Nat.succ_pos m)
        (⟨T i, hTc i, hT11 i⟩ : ClosedOneOneCurrent (canonicalBasis (m + 1)) (Nat.succ_pos m)) =
      bottChernClass (canonicalBasis (m + 1)) (Nat.succ_pos m)
        (⟨S i, hSc i, hS11 i⟩ : ClosedOneOneCurrent (canonicalBasis (m + 1)) (Nat.succ_pos m)))
    (hI : ∀ i, sourceCurrentIOrder (T i) (S i)) :
    sourceCurrentMixedIVolume ω T hTc hT11 hTp ≤ sourceCurrentMixedIVolume ω S hSc hS11 hSp := by
  obtain ⟨θ, u, hu, hTread⟩ := tupleRepresentation T hTc hT11 hTp
  obtain ⟨η, v, hv, hSread⟩ := tupleRepresentation S hSc hS11 hSp
  rw [sourceCurrentMixedIVolume_eq_representation ω T hTc hT11 hTp θ u hu hTread,
    sourceCurrentMixedIVolume_eq_representation ω S hSc hS11 hSp η v hv hSread]
  have hc i : RealBottChern.ofRepresentative (θ i) = RealBottChern.ofRepresentative (η i) := by
    have hTsub : (⟨T i, hTc i, hT11 i⟩ :
        ClosedOneOneCurrent (canonicalBasis (m + 1)) (Nat.succ_pos m)) =
        ThetaPotentialCurrentBottChernClass.thetaClosedCurrent (θ i) (u i) (hu i) :=
      Subtype.ext (hTread i)
    have hSsub : (⟨S i, hSc i, hS11 i⟩ :
        ClosedOneOneCurrent (canonicalBasis (m + 1)) (Nat.succ_pos m)) =
        ThetaPotentialCurrentBottChernClass.thetaClosedCurrent (η i) (v i) (hv i) :=
      Subtype.ext (hSread i)
    have h := hclass i
    rw [hTsub, hSsub,
      ThetaPotentialCurrentBottChernClass.bottChernClass_thetaClosedCurrent,
      ThetaPotentialCurrentBottChernClass.bottChernClass_thetaClosedCurrent] at h
    exact h
  apply sourceGeneralMixedIVolume_mono_of_class_eq_of_sourceIOrder ω
    (fun i => nativeClosedFormToAtlas (θ i)) (fun i => nativeClosedFormToAtlas (η i))
    u v (fun i => nativePSHToSource (hu i)) (fun i => nativePSHToSource (hv i))
  · intro i
    simpa only [sourceNativeAtlasForm_roundTrip] using hc i
  · intro i
    apply (sourceIOrder_iff_native ⟨nativeClosedFormToAtlas (θ i), nativePSHToSource (hu i)⟩
      ⟨nativeClosedFormToAtlas (η i), nativePSHToSource (hv i)⟩).mpr
    exact (sourceCurrentIOrder_iff_of_representation ω (hu i) (hv i) (hTread i) (hSread i)).mp (hI i)

/-- Every genuine representation of the ORIGINAL current reads the diagonal
as its single I-volume, including zero volumes and actual singular poles. -/
theorem sourceCurrentMixedIVolume_diagonal_eq_IVolume_of_representation
    (ω : KahlerBackground (m + 1) M)
    (T : GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m)))
    (hc : T.IsClosed (canonicalBasis (m + 1)))
    (h11 : T.IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m))
    (hp : IsFullPositive T) (θ : ClosedRealOneOneForm (m + 1) M) (u : M → EReal)
    (hu : IsThetaPshPotential θ.val u) (hread : T = thetaPotentialCurrent θ.val u hu) :
    sourceCurrentMixedIVolume ω (fun _ => T) (fun _ => hc) (fun _ => h11) (fun _ => hp) =
      sourceIVolume (nativeClosedFormToAtlas θ) u (nativePSHToSource hu) := by
  rw [sourceCurrentMixedIVolume_eq_representation ω _ _ _ _
    (fun _ => θ) (fun _ => u) (fun _ => hu) (fun _ => hread)]
  exact sourceGeneralMixedIVolume_diagonal ω (nativePSHToSource hu)

end SGPT.PSH.VariableComplexAtlas
