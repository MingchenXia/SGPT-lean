import SGPT.Hodge.SourceCompactNefFamilyUpper
import SGPT.Hodge.SourceFiniteMixedPerturbation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace SGPT.Hodge.BDivChain.SourceCompactPerturbationDraft
open Set Filter MeasureTheory
open scoped Topology BigOperators ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.NefMixedMass
  SGPT.PSH.VariableComplexAtlas SGPT.BDivisor SGPT.Hodge.BDivChain.NativeDraft
  SGPT.Hodge.BDivChain.NativeDraft.VolumeNetDraft
  SGPT.Hodge.BDivChain.SourceIntersection SGPT.Hodge.BDivChain.SourceNefIntersectionDraft
  SGPT.Hodge.BDivChain.SourceMixedOrderDraft SGPT.Hodge.BDivChain.SourceNefProjectiveDraft
section Positive
variable {m : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (m+1)) X] [IsComplexManifold (m+1) X]
  [CompactSpace X] [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X]
local notation "Sys" => ModelSystem.blowup (m+1) X

/-- Original compact roots INTERNALLY give one uniform mixed-intersection
perturbation constant for all original nef families and every epsilon in [0,1]. -/
theorem source_perturbDF_pos (ω : KahlerBackground (m+1) X)
    (K : Set (RealBottChern (m+1) X))
    (hK : @IsCompact _ (SGPT.BDivisor.euclideanTopology _) K) :
    ∃ L : ℝ,0≤L ∧ ∀ D : Fin (m+1) → WeilFamilyAny Sys,
      (∀ i,IsNefAny (D i)) → (∀ i,rootClassLinear (D i)∈K) →
      ∀ ε∈Icc (0 : ℝ) 1,
        0≤(nefIntersection (fun i => D i+ε • rootCartierAny (RealBottChern.ofRepresentative ω.form))).toReal-
            (nefIntersection D).toReal ∧
        (nefIntersection (fun i => D i+ε • rootCartierAny (RealBottChern.ofRepresentative ω.form))).toReal-
            (nefIntersection D).toReal≤L*ε := by
  obtain ⟨R,hR,hbound⟩ := exists_uniform_family_upper_of_compact_root_pos ω K hK
  let C := rootCartierAny (RealBottChern.ofRepresentative ω.form)
  have hCcart : IsNefCartierAny C := by
    change IsNefCartierAny (modelCartier ModelSystem.Model.root (RealBottChern.ofRepresentative ω.form))
    exact modelCartier_isNefCartier ModelSystem.Model.root ω
      (nefWithRespectTo_of_isSemipositive ω.isSemipositive)
  have hCnef : IsNefAny C := isNefAny_of_isNefCartierAny hCcart
  have hCp : IsPseudoeffectiveAny C := rootKahler_pseudoeffective ω
  let U := (R+1) • C
  have hUnef : IsNefAny U := isNefAny_of_isNefCartierAny
    (isNefCartierAny_smul hCcart (by linarith : 0≤R+1))
  let M := nefIntersectionReal (fun _ : Fin (m+1) => U)
  have hM : 0≤M := nefIntersectionReal_nonneg ω _ (fun _ => hUnef)
  have hscalar {a b : ℝ} (hab : a≤b) : LEAny (a • C) (b • C) := by
    intro π
    have hp := SGPT.Okounkov.TranscendentalVolumeConcavity.classPseudoeffective_smul
      (hCp π) (sub_nonneg.mpr hab)
    change ClassPseudoeffectiveViaPotentials (b • C.val π-a • C.val π)
    convert hp using 1; module
  refine ⟨((m+1 : ℕ) : ℝ)*M,mul_nonneg (Nat.cast_nonneg _) hM,?_⟩
  intro D hD hDK ε hε
  have hεC : IsNefAny (ε • C) := isNefAny_of_isNefCartierAny (isNefCartierAny_smul hCcart hε.1)
  have hplus (i) : IsNefAny (D i+ε • C) := by
    have hσ : (ε • ω.form).val.IsSemipositive :=
      KahlerDomination.isSemipositive_smul ω.isSemipositive hε.1
    have h := isNefAny_add_root_semipositive ω (D i) (hD i) (ε • ω.form) hσ
    rw [RealBottChern.ofRepresentative_smul,rootCartierAny_smul] at h
    exact h
  have hDplus (i) : LEAny (D i) (D i+ε • C) := by
    intro π
    have hp := SGPT.Okounkov.TranscendentalVolumeConcavity.classPseudoeffective_smul (hCp π) hε.1
    change ClassPseudoeffectiveViaPotentials (((D i).val π+ε • C.val π)-(D i).val π)
    convert hp using 1; module
  have hDU (i) : LEAny (D i) U := leAny_trans (hbound (D i) (hD i) (hDK i))
    (hscalar (by linarith : R≤R+1))
  have hCU : LEAny C U := by
    have h := hscalar (by linarith : (1 : ℝ)≤R+1)
    simpa only [one_smul] using h
  have hplusU (i) : LEAny (D i+ε • C) U := by
    have h := leAny_add (hbound (D i) (hD i) (hDK i)) (hscalar hε.2)
    have he : R • C+(1 : ℝ) • C=U := by dsimp [U]; module
    rw [←he]
    exact h
  have hb := finite_mixed_perturbation_bound ω D C U hD hCnef hUnef ε hε.1 hεC
    hplus hDplus hDU hCU hplusU
  rw [nefIntersection_toReal_eq ω _ hplus,nefIntersection_toReal_eq ω D hD]
  exact hb
end Positive

section Whole
variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [CompactSpace X] [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X]

/-- WHOLE original lma:perturbDF. A single constant depends only on the original
compact root-class set and the actual Kähler form, uniformly over EVERY original
nef tuple, every epsilon in the literal interval [0,1], and every natural dimension.
No uniform bound, realization, approximation or desired estimate is supplied. -/
theorem source_perturbDF_whole (ω : KahlerBackground n X)
    (K : Set (RealBottChern n X))
    (hK : @IsCompact _ (SGPT.BDivisor.euclideanTopology _) K) :
    ∃ L : ℝ,0≤L ∧ ∀ D : Fin n → WeilFamilyAny (ModelSystem.blowup n X),
      (∀ i,IsNefAny (D i)) → (∀ i,rootClassLinear (D i)∈K) →
      ∀ ε∈Icc (0 : ℝ) 1,
        0≤(nefIntersection (fun i => D i+ε • rootCartierAny (RealBottChern.ofRepresentative ω.form))).toReal-
            (nefIntersection D).toReal ∧
        (nefIntersection (fun i => D i+ε • rootCartierAny (RealBottChern.ofRepresentative ω.form))).toReal-
            (nefIntersection D).toReal≤L*ε := by
  cases n with
  | zero =>
    refine ⟨0,le_rfl,?_⟩
    intro D hD hDK ε hε
    rw [source_nefIntersection_dim_zero _,source_nefIntersection_dim_zero D]
    simp
  | succ m => exact source_perturbDF_pos ω K hK

/-- The SAME constant works for every genuine Kähler representative of the SAME
original cohomology class, making its dependence on {omega} explicit. -/
theorem source_perturbDF_class_uniform (ω : KahlerBackground n X)
    (K : Set (RealBottChern n X))
    (hK : @IsCompact _ (SGPT.BDivisor.euclideanTopology _) K) :
    ∃ L : ℝ,0≤L ∧ ∀ κ : KahlerBackground n X,
      RealBottChern.ofRepresentative κ.form=RealBottChern.ofRepresentative ω.form →
      ∀ D : Fin n → WeilFamilyAny (ModelSystem.blowup n X),
      (∀ i,IsNefAny (D i)) → (∀ i,rootClassLinear (D i)∈K) →
      ∀ ε∈Icc (0 : ℝ) 1,
        0≤(nefIntersection (fun i => D i+ε • rootCartierAny (RealBottChern.ofRepresentative κ.form))).toReal-
            (nefIntersection D).toReal ∧
        (nefIntersection (fun i => D i+ε • rootCartierAny (RealBottChern.ofRepresentative κ.form))).toReal-
            (nefIntersection D).toReal≤L*ε := by
  obtain ⟨L,hL,hbound⟩ := source_perturbDF_whole ω K hK
  refine ⟨L,hL,?_⟩
  intro κ hκ D hD hDK ε hε
  simpa only [hκ] using hbound D hD hDK ε hε

end Whole
end SGPT.Hodge.BDivChain.SourceCompactPerturbationDraft
