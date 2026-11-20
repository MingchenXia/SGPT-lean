import SGPT.Hodge.SourceNefCurrentPolarization
import SGPT.Hodge.SourceNefFamilyVolumeContinuity

set_option autoImplicit false
noncomputable section
universe u
namespace SGPT.Hodge.BDivChain.SourceNefIntersectionDraft
open Set Filter MeasureTheory
open scoped Topology BigOperators ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending
  SGPT.PSH.VariableComplexAtlas SGPT.BDivisor SGPT.Hodge.BDivChain.NativeDraft
  SGPT.Hodge.BDivChain.NativeDraft.VolumeNetDraft
  SGPT.Hodge.BDivChain.NativeDraft.VolumeNetRealDraft
  SGPT.Hodge.BDivChain.SourceCorrespondenceDraft SGPT.Hodge.BDivChain.SourceIntersection
  SGPT.Hodge.BDivChain.SourceNefProjectiveDraft
  SGPT.Hodge.BDivChain.SourceCartierSequenceDraft

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [CompactSpace X] [ConnectedSpace X]
local notation "Sys" => ModelSystem.blowup n X

/-- An explicit finite expression in ORIGINAL pure family volumes. -/
def familyVolumePolarization (D : Fin n → WeilFamilyAny Sys) : ℝ :=
  ∑ S : Finset (Fin n),(-1 : ℝ)^(n-S.card) * volumeRealAny (∑ j ∈ S,D j)

/-- The actual all-nef candidate; its literal source limit and positivity
are proved below, not assumed or put in its data. -/
def nefIntersectionReal (D : Fin n → WeilFamilyAny Sys) : ℝ :=
  familyVolumePolarization D / (n.factorial : ℝ)

theorem nefIntersectionReal_zero {Y : Type u} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel 0) Y] [IsComplexManifold 0 Y]
    [CompactSpace Y] [ConnectedSpace Y]
    (D : Fin 0 → WeilFamilyAny (ModelSystem.blowup 0 Y)) : nefIntersectionReal D=1 := by
  simp [nefIntersectionReal,familyVolumePolarization,volumeRealAny,volumeAny_eq_one_of_dim_zero]

variable [MeasurableSpace X] [BorelSpace X]

/-- Exact actual big-nef intersection readback in EVERY dimension. -/
theorem factorial_mul_bigNefIntersection_eq_polarization (ω : KahlerBackground n X)
    (D : Fin n → BigNefFamily (n := n) (X := X)) :
    (n.factorial : ℝ)*(bigNefIntersection ω D).toReal=
      familyVolumePolarization (fun i => (D i).val) := by
  cases n with
  | zero =>
    have hd : bigNefIntersection ω D=1 :=
      SGPT.IGood.LogVolume.sourceGeneralMixedIVolume_eq_one_of_dim_zero ω _ _ _
    simp [hd,familyVolumePolarization,volumeRealAny,volumeAny_eq_one_of_dim_zero]
  | succ m => exact factorial_mul_bigNefIntersection_eq_polarization_pos ω D

theorem bigNefIntersection_eq_nefIntersectionReal (ω : KahlerBackground n X)
    (D : Fin n → BigNefFamily (n := n) (X := X)) :
    (bigNefIntersection ω D).toReal=nefIntersectionReal (fun i => (D i).val) := by
  have hn : (n.factorial : ℝ)≠0 := by exact_mod_cast Nat.factorial_ne_zero n
  apply (eq_div_iff hn).mpr
  simpa only [mul_comm] using factorial_mul_bigNefIntersection_eq_polarization ω D

omit [MeasurableSpace X] [BorelSpace X] in
/-- The genuine all-nef mixed expression is continuous on every ORIGINAL
decreasing directed net, by actual pure-volume limits for all subset sums. -/
theorem nefIntersectionReal_tendsto_of_antitone (ω : KahlerBackground n X)
    {J : Type*} [Preorder J] [IsDirected J (·≤·)] [Nonempty J]
    (D : Fin n → J → WeilFamilyAny Sys) (E : Fin n → WeilFamilyAny Sys)
    (hD : ∀ i j,IsNefAny (D i j))
    (ha : ∀ i j k,j≤k → LEAny (D i k) (D i j))
    (hc : ∀ i,ConvergesAny atTop (D i) (E i)) :
    Tendsto (fun j => nefIntersectionReal (fun i => D i j)) atTop (𝓝 (nefIntersectionReal E)) := by
  have hs (S : Finset (Fin n)) :
      Tendsto (fun j => volumeRealAny (∑ i ∈ S,D i j)) atTop
        (𝓝 (volumeRealAny (∑ i ∈ S,E i))) :=
    volumeRealAny_sum_tendsto_of_antitone ω S D E
      (fun i _ j => isPseudoeffectiveAny_of_isNef ω _ (hD i j))
      (fun i _ j k hjk => ha i j k hjk) (fun i _ => hc i)
  have hsum := tendsto_finsetSum (Finset.univ : Finset (Finset (Fin n)))
    (fun S _ => (hs S).const_mul ((-1 : ℝ)^(n-S.card)))
  exact hsum.div_const (n.factorial : ℝ)

omit [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X] in
theorem rootKahler_pseudoeffective (ω : KahlerBackground n X) :
    IsPseudoeffectiveAny (rootCartierAny (RealBottChern.ofRepresentative ω.form)) := by
  cases n with
  | zero => exact isPseudoeffectiveAny_of_dim_zero _
  | succ m => exact rootKahler_isPseudoeffectiveAny ω

omit [MeasurableSpace X] [BorelSpace X] in
/-- The literal finite expression has the correct limit for EVERY vanishing
nonnegative scalar filter; no monotone-output assumption is imposed. -/
theorem nefIntersectionReal_add_smul_tendsto (ω : KahlerBackground n X)
    {I : Type*} {l : Filter I} [l.NeBot]
    (D : Fin n → WeilFamilyAny Sys) (hD : ∀ i,IsNefAny (D i))
    (C : WeilFamilyAny Sys) (hC : IsPseudoeffectiveAny C)
    (c : I → ℝ) (hc : ∀ i,0≤c i) (hc0 : Tendsto c l (𝓝 0)) :
    Tendsto (fun j => nefIntersectionReal (fun i => D i+c j • C)) l
      (𝓝 (nefIntersectionReal D)) := by
  classical
  have hs (S : Finset (Fin n)) :
      Tendsto (fun j => volumeRealAny (∑ i ∈ S,(D i+c j • C))) l
        (𝓝 (volumeRealAny (∑ i ∈ S,D i))) := by
    have hpD := isPseudoeffectiveAny_sum ω S D
      (fun i _ => isPseudoeffectiveAny_of_isNef ω _ (hD i))
    have hpC := isPseudoeffectiveAny_sum ω S (fun _ => C) (fun _ _ => hC)
    have he j : (∑ i ∈ S,(D i+c j • C))=
        (∑ i ∈ S,D i)+c j • (∑ _i ∈ S,C) := by
      rw [Finset.sum_add_distrib,Finset.smul_sum]
    simp_rw [he]
    exact (ENNReal.tendsto_toReal (volumeAny_lt_top_blowup ⟨ω⟩ _).ne).comp
      (volumeAny_add_smul_tendsto ω _ _ hpD hpC c hc hc0)
  have hsum := tendsto_finsetSum (Finset.univ : Finset (Finset (Fin n)))
    (fun S _ => (hs S).const_mul ((-1 : ℝ)^(n-S.card)))
  exact hsum.div_const (n.factorial : ℝ)

omit [MeasurableSpace X] [BorelSpace X] in
/-- Every strictly positive source Kähler perturbation is internally
proved to belong to the entire original big-nef domain. -/
def kahlerPerturbedBigNef (ω κ : KahlerBackground n X)
    (D : WeilFamilyAny Sys) (hD : IsNefAny D) (ε : ℝ) (hε : 0<ε) :
    BigNefFamily (n := n) (X := X) := by
  let ζ := KahlerBackground.smul hε κ
  have he : rootCartierAny (RealBottChern.ofRepresentative ζ.form)=
      ε • rootCartierAny (RealBottChern.ofRepresentative κ.form) := by
    rw [show ζ.form=ε • κ.form from rfl,RealBottChern.ofRepresentative_smul,rootCartierAny_smul]
  refine ⟨D+ε • rootCartierAny (RealBottChern.ofRepresentative κ.form),?_,?_⟩
  · rw [←he]
    exact volumeAny_pos_add_rootKahler ω D hD ζ
  · rw [←he]
    exact isNefAny_add_root_semipositive ω D hD ζ.form ζ.isSemipositive

/-- The all-nef finite expression is nonnegative because it is the limit
of the actual nonnegative big-nef original mixed I-volumes. -/
theorem nefIntersectionReal_nonneg (ω : KahlerBackground n X)
    (D : Fin n → WeilFamilyAny Sys) (hD : ∀ i,IsNefAny (D i)) :
    0≤nefIntersectionReal D := by
  let c : ℕ → ℝ := fun j => 1/((j : ℝ)+1)
  have hp j : 0<c j := by dsimp [c]; positivity
  have hc0 : Tendsto c atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hlim := nefIntersectionReal_add_smul_tendsto ω D hD
    (rootCartierAny (RealBottChern.ofRepresentative ω.form))
    (rootKahler_pseudoeffective ω) c (fun j => (hp j).le) hc0
  apply le_of_tendsto_of_tendsto' tendsto_const_nhds hlim
  intro j
  have h := bigNefIntersection_eq_nefIntersectionReal ω
    (fun i => kahlerPerturbedBigNef ω ω (D i) (hD i) (c j) (hp j))
  have he : (fun i => (kahlerPerturbedBigNef ω ω (D i) (hD i) (c j) (hp j)).val)=
      (fun i => D i+c j • rootCartierAny (RealBottChern.ofRepresentative ω.form)) := rfl
  rw [he] at h
  rw [←h]
  exact ENNReal.toReal_nonneg

end SGPT.Hodge.BDivChain.SourceNefIntersectionDraft
