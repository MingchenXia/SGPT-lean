import SGPT.Siu.SiuDecompositionCountable
import SGPT.Siu.CurrentLevelSets

/-!
# Siu's divisorial decomposition

Source: `eq:Siudec` (chapter *Plurisubharmonic functions*, after `lma:Siudec`): every closed
positive `(1,1)`-current `T` on a compact complex manifold `X` decomposes as
`T = Reg T + ∑ᵢ cᵢ [Eᵢ]`, where `{Eᵢ}` is a countable collection of prime divisors and `cᵢ > 0`;
and `def:nd_curr` (non-divisorial and divisorial currents).  The book gives no proof; we follow
Xia, *Foundations of pluripotential theory*, `thm:siu-divisorial-decomposition`, Steps 2–3:
the coefficients are the generic Lelong numbers `cᵢ = ν(T, Eᵢ)` and the residual current `Reg T`
has `ν(Reg T, D) = 0` for every prime divisor `D` (equivalently, every upper level set
`E_c(Reg T)`, `c > 0`, contains no prime divisor, i.e. has codimension at least two).

* `isClosedPositiveCurrent_sub_finsetSum`: the finite induction `T - ∑_{D ∈ F} ν(T, D)[D] ≥ 0`.
  At a point of `D₀` off the other divisors of `F`, the Lelong number of `T - ∑_F` is that of `T`;
  these points are dense in `D₀` (`subset_closure_diff_biUnion`) and the upper level sets of the
  Lelong numbers are closed (Siu), so Siu's lemma applies with the full coefficient `ν(T, D₀)`.
* `countable_support_currentGenericLelong`: only countably many prime divisors have
  `ν(T, D) > 0` (`countable_of_finset_dominated`).
* `siuDivisorialPart T`: the weak sum `∑_D ν(T, D)[D]` (over the finite subsets of prime divisors,
  `exists_tendsto_of_monotone_dominated`), and `siuRegularPart T = Reg T = T - ∑_D ν(T, D)[D]`.
* `siu_decomposition`: **Siu's decomposition** `eq:Siudec`.
* `IsNonDivisorial`, `IsDivisorial` (`def:nd_curr`), with `isNonDivisorial_iff`:
  `T` is non-divisorial iff `ν(T, D) = 0` for every prime divisor `D`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter TopologicalSpace
open scoped Topology Distributions ENNReal

namespace SGPT.Siu

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open GlobalCurrents CanonicalCurrentFrame GlobalPositiveCurrentACRestriction
open _root_.SGPT.Foundations.Analysis.LocalCurrents

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

local notation "Cur" => GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m))
local notation "Prime" => SGPT.PSH.GeometricPrimeCarrier (m + 1) M

/-! ### Preliminaries -/

theorem inChart_finsetSum {ι : Type*} (F : Finset ι) (A : ι → Cur) (e : ComplexChart (m + 1) M)
    (η : TestForm (chartTarget e) (Module.finrank ℝ (ComplexModel (m + 1)) - 2)) :
    (∑ i ∈ F, A i).inChart e η = ∑ i ∈ F, (A i).inChart e η := by
  classical
  induction F using Finset.induction_on with
  | empty => rfl
  | @insert i F hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, ← ih]
      rfl

theorem IsClosedPositiveCurrent.sub_of_isFullPositive {S T : Cur}
    (hS : IsClosedPositiveCurrent S) (hT : IsClosedPositiveCurrent T)
    (hpos : IsFullPositive (T - S)) : IsClosedPositiveCurrent (T - S) := by
  have hsub : T - S = T + (-1 : ℝ) • S := by module
  rw [hsub] at hpos ⊢
  exact ⟨hT.1.add _ (hS.1.smul _ (-1)), hT.2.1.add _ (hS.2.1.smul _ (-1)), hpos⟩

theorem finsetSum_sub_smul {ι : Type*} (F : Finset ι) (a b : ι → ℝ) (A : ι → Cur) :
    ∑ i ∈ F, (a i - b i) • A i = ∑ i ∈ F, a i • A i - ∑ i ∈ F, b i • A i := by
  classical
  induction F using Finset.induction_on with
  | empty =>
      rw [Finset.sum_empty, Finset.sum_empty, Finset.sum_empty]
      abel
  | @insert i F hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, Finset.sum_insert hi, ih]
      module

/-- Lelong numbers of a finite nonnegative combination of currents of prime divisors. -/
theorem currentLelong_finsetSum_primeDivisorCurrent [CompactSpace M] (F : Finset Prime)
    (a : Prime → ℝ) (ha : ∀ D ∈ F, 0 ≤ a D)
    (h : IsClosedPositiveCurrent (∑ D ∈ F, a D • primeDivisorCurrent D)) (x : M) :
    currentLelong (∑ D ∈ F, a D • primeDivisorCurrent D) h x =
      ∑ D ∈ F, ENNReal.ofReal (a D) *
        currentLelong (primeDivisorCurrent D)
          (isClosedPositiveCurrent_primeDivisorCurrent D) x := by
  classical
  induction F using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      exact currentLelong_zero x
  | @insert D F hD ih =>
      have ha' : ∀ D' ∈ F, 0 ≤ a D' := fun D' h' => ha D' (Finset.mem_insert_of_mem h')
      have hF := isClosedPositiveCurrent_finsetSum F a primeDivisorCurrent ha'
        (fun D' _ => isClosedPositiveCurrent_primeDivisorCurrent D')
      have hDa := ha D (Finset.mem_insert_self D F)
      have hsD := (isClosedPositiveCurrent_primeDivisorCurrent D).smul hDa
      have heq : (∑ D' ∈ insert D F, a D' • primeDivisorCurrent D') =
          a D • primeDivisorCurrent D + ∑ D' ∈ F, a D' • primeDivisorCurrent D' :=
        Finset.sum_insert hD
      have hsum : IsClosedPositiveCurrent
          (a D • primeDivisorCurrent D + ∑ D' ∈ F, a D' • primeDivisorCurrent D') := heq ▸ h
      have h1 : currentLelong (∑ D' ∈ insert D F, a D' • primeDivisorCurrent D') h x =
          currentLelong (a D • primeDivisorCurrent D + ∑ D' ∈ F, a D' • primeDivisorCurrent D')
            hsum x := by
        congr 1
      rw [h1, currentLelong_add hsD hF hsum, currentLelong_smul _ hDa hsD, ih ha' hF,
        Finset.sum_insert hD]

/-! ### The finite induction -/

/-- **The finite step of Siu's decomposition**: for every finite set `F` of prime divisors,
`T - ∑_{D ∈ F} ν(T, D)[D]` is a closed positive current. -/
theorem isClosedPositiveCurrent_sub_finsetSum [CompactSpace M] {T : Cur}
    (hT : IsClosedPositiveCurrent T) (F : Finset Prime) :
    IsClosedPositiveCurrent
      (T - ∑ D ∈ F, (currentGenericLelong T hT D).toReal • primeDivisorCurrent D) := by
  classical
  induction F using Finset.induction_on with
  | empty =>
      rw [Finset.sum_empty]
      convert hT using 1
      exact sub_zero T
  | @insert D₀ F hD₀ ih =>
      set c : Prime → ℝ := fun D => (currentGenericLelong T hT D).toReal with hcdef
      have hc0 : ∀ D, 0 ≤ c D := fun D => ENNReal.toReal_nonneg
      set S := ∑ D ∈ F, c D • primeDivisorCurrent D with hSdef
      have hS : IsClosedPositiveCurrent S := isClosedPositiveCurrent_finsetSum F c _
        (fun D _ => hc0 D) (fun D _ => isClosedPositiveCurrent_primeDivisorCurrent D)
      set R := T - S with hRdef
      have hR : IsClosedPositiveCurrent R := ih
      have hTRS : T = R + S := (sub_add_cancel T S).symm
      have hTRS' : IsClosedPositiveCurrent (R + S) := hTRS ▸ hT
      -- the Lelong numbers of `R` along `D₀` are at least `ν(T, D₀)`
      have hfinT : currentGenericLelong T hT D₀ ≠ ⊤ := currentGenericLelong_ne_top hT D₀
      have hoff : ∀ y ∈ D₀.val \ ⋃ D ∈ F, D.val,
          ENNReal.ofReal (c D₀) ≤ currentLelong R hR y := by
        intro y hy
        have hyF : ∀ D ∈ F, y ∉ D.val := by
          intro D hD hyD
          exact hy.2 (mem_iUnion₂.2 ⟨D, hD, hyD⟩)
        have hSy : currentLelong S hS y = 0 := by
          rw [currentLelong_finsetSum_primeDivisorCurrent F c (fun D _ => hc0 D) hS y]
          apply Finset.sum_eq_zero
          intro D hD
          rw [currentLelong_primeDivisorCurrent_eq_zero D (hyF D hD), mul_zero]
        have hTy : currentLelong T hT y = currentLelong R hR y := by
          have h1 : currentLelong T hT y = currentLelong (R + S) hTRS' y := by
            congr 1
          rw [h1, currentLelong_add hR hS hTRS' y, hSy, add_zero]
        rw [← hTy, ENNReal.ofReal_toReal hfinT]
        exact currentGenericLelong_le hT D₀ hy.1
      have hclosed := isClosed_currentLelong_superlevel hR (ENNReal.ofReal (c D₀))
      have hge : ENNReal.ofReal (c D₀) ≤ currentGenericLelong R hR D₀ := by
        refine le_iInf₂ fun x hx => ?_
        have hxcl := subset_closure_diff_biUnion F hD₀ hx
        exact (closure_minimal (fun y hy => hoff y hy) hclosed) hxcl
      have hfinR : currentGenericLelong R hR D₀ ≠ ⊤ := currentGenericLelong_ne_top hR D₀
      have hle : c D₀ ≤ (currentGenericLelong R hR D₀).toReal :=
        (ENNReal.ofReal_le_iff_le_toReal hfinR).mp hge
      -- Siu's lemma for `R` and `D₀`
      have hSiu := isClosedPositiveCurrent_sub_currentGenericLelong_smul hR D₀
      have hrest := (isClosedPositiveCurrent_primeDivisorCurrent D₀).smul
        (sub_nonneg.mpr hle)
      have hsum := hSiu.add hrest
      have key : ∀ (A B C : Cur) (a b : ℝ), A - (b • C + B) = (A - B - a • C) + (a - b) • C := by
        intro A B C a b
        module
      have heq : T - ∑ D ∈ insert D₀ F, c D • primeDivisorCurrent D =
          (R - (currentGenericLelong R hR D₀).toReal • primeDivisorCurrent D₀) +
            ((currentGenericLelong R hR D₀).toReal - c D₀) • primeDivisorCurrent D₀ := by
        rw [Finset.sum_insert hD₀]
        exact key T S _ _ _
      rw [heq]
      exact hsum

/-! ### Countability -/

/-- **Only countably many prime divisors carry positive generic Lelong number.** -/
theorem countable_support_currentGenericLelong [CompactSpace M] {T : Cur}
    (hT : IsClosedPositiveCurrent T) :
    {D : Prime | currentGenericLelong T hT D ≠ 0}.Countable := by
  classical
  have hcover : {D : Prime | currentGenericLelong T hT D ≠ 0} ⊆
      ⋃ j : ℕ, {D : Prime | ENNReal.ofReal (1 / ((j : ℝ) + 1)) ≤ currentGenericLelong T hT D} := by
    intro D hD
    have hpos : 0 < (currentGenericLelong T hT D).toReal :=
      ENNReal.toReal_pos hD (currentGenericLelong_ne_top hT D)
    obtain ⟨j, hj⟩ := exists_nat_one_div_lt hpos
    refine mem_iUnion.2 ⟨j, ?_⟩
    rw [mem_ofPred_eq, ENNReal.ofReal_le_iff_le_toReal (currentGenericLelong_ne_top hT D)]
    exact hj.le
  refine (Set.countable_iUnion fun j => ?_).mono hcover
  have hc : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
  apply countable_of_finset_dominated T hc
  intro F hF
  obtain ⟨c, hcdef⟩ : ∃ c : Prime → ℝ, c = fun D => (currentGenericLelong T hT D).toReal :=
    ⟨_, rfl⟩
  have hcj : ∀ D ∈ F, 1 / ((j : ℝ) + 1) ≤ c D := by
    intro D hD
    rw [hcdef]
    exact (ENNReal.ofReal_le_iff_le_toReal (currentGenericLelong_ne_top hT D)).mp (hF hD)
  have hmain : IsClosedPositiveCurrent (T - ∑ D ∈ F, c D • primeDivisorCurrent D) := by
    rw [hcdef]
    exact isClosedPositiveCurrent_sub_finsetSum hT F
  have hrest := isClosedPositiveCurrent_finsetSum F (fun D => c D - 1 / ((j : ℝ) + 1))
    primeDivisorCurrent (fun D hD => sub_nonneg.mpr (hcj D hD))
    (fun D _ => isClosedPositiveCurrent_primeDivisorCurrent D)
  have h1 := finsetSum_sub_smul F c (fun _ => 1 / ((j : ℝ) + 1)) primeDivisorCurrent
  have heq : T - ∑ D ∈ F, (1 / ((j : ℝ) + 1)) • primeDivisorCurrent D =
      (T - ∑ D ∈ F, c D • primeDivisorCurrent D) +
        ∑ D ∈ F, (c D - 1 / ((j : ℝ) + 1)) • primeDivisorCurrent D := by
    rw [h1]
    abel
  rw [heq]
  exact (hmain.add hrest).2.2

/-! ### The divisorial part and the residual current -/

/-- The partial sums `∑_{D ∈ F} ν(T, D)[D]` over finite sets of prime divisors. -/
def siuPartialSum [CompactSpace M] (T : Cur) (hT : IsClosedPositiveCurrent T)
    (F : Finset Prime) : Cur :=
  ∑ D ∈ F, (currentGenericLelong T hT D).toReal • primeDivisorCurrent D

theorem isClosedPositiveCurrent_siuPartialSum [CompactSpace M] {T : Cur}
    (hT : IsClosedPositiveCurrent T) (F : Finset Prime) :
    IsClosedPositiveCurrent (siuPartialSum T hT F) :=
  isClosedPositiveCurrent_finsetSum F _ _ (fun _ _ => ENNReal.toReal_nonneg)
    (fun D _ => isClosedPositiveCurrent_primeDivisorCurrent D)

theorem exists_siuDivisorialPart [CompactSpace M] {T : Cur} (hT : IsClosedPositiveCurrent T) :
    ∃ S : Cur, IsClosedPositiveCurrent S ∧ IsFullPositive (T - S) ∧
      (∀ F, IsFullPositive (S - siuPartialSum T hT F)) ∧
      ∀ (e : ComplexChart (m + 1) M)
        (η : TestForm (chartTarget e) (Module.finrank ℝ (ComplexModel (m + 1)) - 2)),
        Tendsto (fun F => (siuPartialSum T hT F).inChart e η) atTop (𝓝 (S.inChart e η)) := by
  classical
  apply exists_tendsto_of_monotone_dominated (siuPartialSum T hT) T
    (isClosedPositiveCurrent_siuPartialSum hT)
  · intro F G hFG
    have heq : siuPartialSum T hT G - siuPartialSum T hT F =
        ∑ D ∈ G \ F, (currentGenericLelong T hT D).toReal • primeDivisorCurrent D := by
      rw [siuPartialSum, siuPartialSum, ← Finset.sum_sdiff hFG]
      abel
    rw [heq]
    exact (isClosedPositiveCurrent_finsetSum _ _ _ (fun _ _ => ENNReal.toReal_nonneg)
      (fun D _ => isClosedPositiveCurrent_primeDivisorCurrent D)).2.2
  · intro F
    exact (isClosedPositiveCurrent_sub_finsetSum hT F).2.2

/-- **The divisorial part** `∑_D ν(T, D)[D]` of a closed positive current: the weak limit of the
partial sums over finite sets of prime divisors. -/
def siuDivisorialPart [CompactSpace M] (T : Cur) (hT : IsClosedPositiveCurrent T) : Cur :=
  Classical.choose (exists_siuDivisorialPart hT)

/-- **The residual current** `Reg T = T - ∑_D ν(T, D)[D]` of `eq:Siudec`. -/
def siuRegularPart [CompactSpace M] (T : Cur) (hT : IsClosedPositiveCurrent T) : Cur :=
  T - siuDivisorialPart T hT

theorem siuDivisorialPart_spec [CompactSpace M] {T : Cur} (hT : IsClosedPositiveCurrent T) :
    IsClosedPositiveCurrent (siuDivisorialPart T hT) ∧
      IsFullPositive (T - siuDivisorialPart T hT) ∧
      (∀ F, IsFullPositive (siuDivisorialPart T hT - siuPartialSum T hT F)) ∧
      ∀ (e : ComplexChart (m + 1) M)
        (η : TestForm (chartTarget e) (Module.finrank ℝ (ComplexModel (m + 1)) - 2)),
        Tendsto (fun F => (siuPartialSum T hT F).inChart e η) atTop
          (𝓝 ((siuDivisorialPart T hT).inChart e η)) :=
  Classical.choose_spec (exists_siuDivisorialPart hT)

theorem isClosedPositiveCurrent_siuDivisorialPart [CompactSpace M] {T : Cur}
    (hT : IsClosedPositiveCurrent T) : IsClosedPositiveCurrent (siuDivisorialPart T hT) :=
  (siuDivisorialPart_spec hT).1

theorem isClosedPositiveCurrent_siuRegularPart [CompactSpace M] {T : Cur}
    (hT : IsClosedPositiveCurrent T) : IsClosedPositiveCurrent (siuRegularPart T hT) :=
  IsClosedPositiveCurrent.sub_of_isFullPositive (isClosedPositiveCurrent_siuDivisorialPart hT) hT
    (siuDivisorialPart_spec hT).2.1

/-- The divisorial part is the weak sum of the series `∑_D ν(T, D)[D]` over all prime divisors. -/
theorem hasSum_siuDivisorialPart [CompactSpace M] {T : Cur} (hT : IsClosedPositiveCurrent T)
    (e : ComplexChart (m + 1) M)
    (η : TestForm (chartTarget e) (Module.finrank ℝ (ComplexModel (m + 1)) - 2)) :
    HasSum (fun D : Prime =>
      ((currentGenericLelong T hT D).toReal • primeDivisorCurrent D).inChart e η)
      ((siuDivisorialPart T hT).inChart e η) := by
  have h := (siuDivisorialPart_spec hT).2.2.2 e η
  have h' : Tendsto (fun F : Finset Prime => ∑ D ∈ F,
      ((currentGenericLelong T hT D).toReal • primeDivisorCurrent D).inChart e η) atTop
      (𝓝 ((siuDivisorialPart T hT).inChart e η)) :=
    h.congr fun F => inChart_finsetSum F _ e η
  simpa only [HasSum, SummationFilter.unconditional_filter] using h'

/-- The weak sum is unique: any current which is the weak sum of `∑_D ν(T, D)[D]` is the
divisorial part. -/
theorem eq_siuDivisorialPart_of_hasSum [CompactSpace M] {T : Cur} (hT : IsClosedPositiveCurrent T)
    {S : Cur} (hS : ∀ (e : ComplexChart (m + 1) M)
      (η : TestForm (chartTarget e) (Module.finrank ℝ (ComplexModel (m + 1)) - 2)),
      HasSum (fun D : Prime =>
        ((currentGenericLelong T hT D).toReal • primeDivisorCurrent D).inChart e η)
        (S.inChart e η)) :
    S = siuDivisorialPart T hT :=
  GlobalCurrent.ext fun e η => (hS e η).unique (hasSum_siuDivisorialPart hT e η)

/-- `S - ν(T, D)[D]` is positive for the divisorial part `S`: it is the sum of the other terms. -/
theorem isClosedPositiveCurrent_siuDivisorialPart_sub [CompactSpace M] {T : Cur}
    (hT : IsClosedPositiveCurrent T) (D : Prime) :
    IsClosedPositiveCurrent
      (siuDivisorialPart T hT - (currentGenericLelong T hT D).toReal • primeDivisorCurrent D) := by
  have h := (siuDivisorialPart_spec hT).2.2.1 {D}
  simp only [siuPartialSum, Finset.sum_singleton] at h
  exact IsClosedPositiveCurrent.sub_of_isFullPositive
    ((isClosedPositiveCurrent_primeDivisorCurrent D).smul ENNReal.toReal_nonneg)
    (isClosedPositiveCurrent_siuDivisorialPart hT) h

/-- **`Reg T` has no divisorial part**: `ν(Reg T, D) = 0` for every prime divisor `D`. -/
theorem currentGenericLelong_siuRegularPart [CompactSpace M] {T : Cur}
    (hT : IsClosedPositiveCurrent T) (D : Prime) :
    currentGenericLelong (siuRegularPart T hT) (isClosedPositiveCurrent_siuRegularPart hT) D =
      0 := by
  set R := siuRegularPart T hT
  have hR := isClosedPositiveCurrent_siuRegularPart hT
  set c := (currentGenericLelong T hT D).toReal with hcdef
  have hc0 : 0 ≤ c := ENNReal.toReal_nonneg
  have hcD := (isClosedPositiveCurrent_primeDivisorCurrent D).smul hc0
  have hrest := isClosedPositiveCurrent_siuDivisorialPart_sub hT D
  have hRc := hR.add hcD
  have hRcr := hRc.add hrest
  have heq : T = (R + c • primeDivisorCurrent D) +
      (siuDivisorialPart T hT - c • primeDivisorCurrent D) := by
    show T = (T - siuDivisorialPart T hT + c • primeDivisorCurrent D) +
      (siuDivisorialPart T hT - c • primeDivisorCurrent D)
    abel
  have hT' : IsClosedPositiveCurrent ((R + c • primeDivisorCurrent D) +
      (siuDivisorialPart T hT - c • primeDivisorCurrent D)) := heq ▸ hT
  have hfin : currentGenericLelong T hT D ≠ ⊤ := currentGenericLelong_ne_top hT D
  have hpt : ∀ x ∈ D.val, currentLelong R hR x + currentGenericLelong T hT D ≤
      currentLelong T hT x := by
    intro x hx
    have h1 : currentLelong T hT x = currentLelong ((R + c • primeDivisorCurrent D) +
        (siuDivisorialPart T hT - c • primeDivisorCurrent D)) hT' x := by
      congr 1
    rw [h1, currentLelong_add hRc hrest hT', currentLelong_add hR hcD hRc,
      currentLelong_smul (isClosedPositiveCurrent_primeDivisorCurrent D) hc0 hcD, hcdef,
      ENNReal.ofReal_toReal hfin]
    calc currentLelong R hR x + currentGenericLelong T hT D
        ≤ currentLelong R hR x + currentGenericLelong T hT D *
            currentLelong (primeDivisorCurrent D)
              (isClosedPositiveCurrent_primeDivisorCurrent D) x := by
          gcongr
          exact le_mul_of_one_le_right' (one_le_currentLelong_primeDivisorCurrent D hx)
      _ ≤ _ := le_self_add
  have hinf : currentGenericLelong R hR D + currentGenericLelong T hT D ≤
      currentGenericLelong T hT D := by
    refine le_iInf₂ fun x hx => ?_
    exact (add_le_add (currentGenericLelong_le hR D hx) le_rfl).trans (hpt x hx)
  have h0 : currentGenericLelong R hR D + currentGenericLelong T hT D ≤
      0 + currentGenericLelong T hT D := by rwa [zero_add]
  exact le_antisymm ((ENNReal.add_le_add_iff_right hfin).mp h0) bot_le

/-- The coefficients of the decomposition are positive on its (countable) support. -/
theorem siu_decomposition_hasSum_support [CompactSpace M] {T : Cur}
    (hT : IsClosedPositiveCurrent T) (e : ComplexChart (m + 1) M)
    (η : TestForm (chartTarget e) (Module.finrank ℝ (ComplexModel (m + 1)) - 2)) :
    HasSum (fun D : {D : Prime | currentGenericLelong T hT D ≠ 0} =>
      ((currentGenericLelong T hT D).toReal • primeDivisorCurrent (D : Prime)).inChart e η)
      ((siuDivisorialPart T hT).inChart e η) := by
  have hsupp : Function.support (fun D : Prime =>
      ((currentGenericLelong T hT D).toReal • primeDivisorCurrent D).inChart e η) ⊆
      {D : Prime | currentGenericLelong T hT D ≠ 0} := by
    intro D hD hD0
    apply hD
    simp only [hD0, ENNReal.toReal_zero, zero_smul, GlobalCurrent.inChart_zero,
      _root_.zero_apply]
  exact (hasSum_subtype_iff_of_support_subset hsupp).mpr (hasSum_siuDivisorialPart hT e η)

/-- **Siu's decomposition** (`eq:Siudec`).  Let `T` be a closed positive `(1,1)`-current on a
compact complex manifold `X`.  Then
`T = Reg T + ∑_D ν(T, D)[D]`,
where:
* the set `{D : ν(T, D) > 0}` of prime divisors is countable and the coefficients
  `c_D = ν(T, D)` are positive on it;
* the series converges weakly (in every chart, on every test form; as an unconditional sum over
  all prime divisors, the other terms being zero) to the divisorial part
  `siuDivisorialPart T`, a closed positive current;
* `Reg T = siuRegularPart T` is a closed positive current with `ν(Reg T, D) = 0` for every prime
  divisor `D`; equivalently, for every `c > 0` the upper level set `E_c(Reg T)` (an analytic set
  by Siu's theorem) contains no prime divisor, i.e. has codimension at least two. -/
theorem siu_decomposition [CompactSpace M] {T : Cur} (hT : IsClosedPositiveCurrent T) :
    T = siuRegularPart T hT + siuDivisorialPart T hT ∧
      IsClosedPositiveCurrent (siuRegularPart T hT) ∧
      IsClosedPositiveCurrent (siuDivisorialPart T hT) ∧
      {D : Prime | currentGenericLelong T hT D ≠ 0}.Countable ∧
      (∀ (e : ComplexChart (m + 1) M)
        (η : TestForm (chartTarget e) (Module.finrank ℝ (ComplexModel (m + 1)) - 2)),
        HasSum (fun D : Prime =>
          ((currentGenericLelong T hT D).toReal • primeDivisorCurrent D).inChart e η)
          ((siuDivisorialPart T hT).inChart e η)) ∧
      (∀ D : Prime,
        currentGenericLelong (siuRegularPart T hT) (isClosedPositiveCurrent_siuRegularPart hT) D
          = 0) ∧
      ∀ c : ℝ, 0 < c → ∀ D : Prime, ¬ D.val ⊆ {x | ENNReal.ofReal c ≤
        currentLelong (siuRegularPart T hT) (isClosedPositiveCurrent_siuRegularPart hT) x} := by
  refine ⟨by rw [siuRegularPart]; exact (sub_add_cancel T _).symm,
    isClosedPositiveCurrent_siuRegularPart hT,
    isClosedPositiveCurrent_siuDivisorialPart hT, countable_support_currentGenericLelong hT,
    hasSum_siuDivisorialPart hT, currentGenericLelong_siuRegularPart hT, ?_⟩
  intro c hc D hsub
  have h0 := currentGenericLelong_siuRegularPart hT D
  have hge : ENNReal.ofReal c ≤ currentGenericLelong (siuRegularPart T hT)
      (isClosedPositiveCurrent_siuRegularPart hT) D :=
    le_iInf₂ fun x hx => hsub hx
  rw [h0] at hge
  exact absurd (ENNReal.ofReal_pos.mpr hc) (not_lt.mpr hge)

/-! ### Non-divisorial and divisorial currents (`def:nd_curr`) -/

/-- **Non-divisorial currents** (`def:nd_curr`): `T = Reg T`. -/
def IsNonDivisorial [CompactSpace M] (T : Cur) (hT : IsClosedPositiveCurrent T) : Prop :=
  T = siuRegularPart T hT

/-- **Divisorial currents** (`def:nd_curr`): `Reg T = 0`. -/
def IsDivisorial [CompactSpace M] (T : Cur) (hT : IsClosedPositiveCurrent T) : Prop :=
  siuRegularPart T hT = 0

/-- A divisorial current is the weak sum of its divisorial series. -/
theorem isDivisorial_iff [CompactSpace M] {T : Cur} (hT : IsClosedPositiveCurrent T) :
    IsDivisorial T hT ↔ T = siuDivisorialPart T hT := by
  rw [IsDivisorial, siuRegularPart]
  exact sub_eq_zero (a := T) (b := siuDivisorialPart T hT)

/-- **A current is non-divisorial iff all its generic Lelong numbers along prime divisors
vanish.** -/
theorem isNonDivisorial_iff [CompactSpace M] {T : Cur} (hT : IsClosedPositiveCurrent T) :
    IsNonDivisorial T hT ↔ ∀ D : Prime, currentGenericLelong T hT D = 0 := by
  constructor
  · intro hnd D
    have hS0 : siuDivisorialPart T hT = 0 := by
      have h : T = T - siuDivisorialPart T hT := hnd
      have h2 : siuDivisorialPart T hT = T - (T - siuDivisorialPart T hT) :=
        (sub_sub_cancel T _).symm
      rw [← h] at h2
      exact h2.trans (sub_self T)
    set c := (currentGenericLelong T hT D).toReal with hcdef
    have hc0 : 0 ≤ c := ENNReal.toReal_nonneg
    have hneg : IsClosedPositiveCurrent (-(c • primeDivisorCurrent D)) := by
      have h := isClosedPositiveCurrent_siuDivisorialPart_sub hT D
      rw [hS0] at h
      convert h using 1
      exact (zero_sub (c • primeDivisorCurrent D)).symm
    have hcD := (isClosedPositiveCurrent_primeDivisorCurrent D).smul hc0
    have hsum := hneg.add hcD
    obtain ⟨x, hx⟩ := D.nonempty
    have hL := currentLelong_add hneg hcD hsum x
    have h1 : currentLelong (-(c • primeDivisorCurrent D) + c • primeDivisorCurrent D) hsum x =
        currentLelong (0 : Cur) isClosedPositiveCurrent_zero x := by
      congr 1
      exact neg_add_cancel (c • primeDivisorCurrent D)
    rw [h1, currentLelong_zero, currentLelong_smul _ hc0 hcD] at hL
    have hmul : ENNReal.ofReal c *
        currentLelong (primeDivisorCurrent D) (isClosedPositiveCurrent_primeDivisorCurrent D) x
          = 0 := by
      have := hL.symm
      exact (add_eq_zero.mp this).2
    have hone := one_le_currentLelong_primeDivisorCurrent D hx
    have hc : ENNReal.ofReal c = 0 := by
      rcases mul_eq_zero.mp hmul with h | h
      · exact h
      · rw [h] at hone; exact absurd hone (by norm_num)
    have hfin := currentGenericLelong_ne_top hT D
    rwa [hcdef, ENNReal.ofReal_toReal hfin] at hc
  · intro h0
    have hS : siuDivisorialPart T hT = 0 := by
      symm
      apply eq_siuDivisorialPart_of_hasSum hT
      intro e η
      simp only [h0, ENNReal.toReal_zero, zero_smul, GlobalCurrent.inChart_zero, _root_.zero_apply]
      exact hasSum_zero
    rw [IsNonDivisorial, siuRegularPart, hS]
    exact (sub_zero T).symm

end SGPT.Siu
