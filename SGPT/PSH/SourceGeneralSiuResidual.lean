import SGPT.Foundations.Analysis.Pending.LocalProductCurrents
import SGPT.Foundations.Analysis.Pending.DominatedFullCurrentWeakCompactness
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Algebra.InfiniteSum.Basic

set_option autoImplicit false

/-! # Genuine monotone local-current limits for countable divisorial tails

The local currents act on the original `formSpan` and genuine LF scalar
 distributions. Positivity is tested on every finite variable strongly positive
 form. This local countable-limit step does not assert arbitrary singular-prime
 extraction, full native gluing, or the mixed-volume Reg identity.
-/

noncomputable section

namespace SGPT.PSH

open Set Filter TopologicalSpace
open scoped Topology Distributions
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open LocalProductCurrents StronglyPositiveForms

variable {n q : ℕ} {U : Opens (ComplexModel n)}

/-- A fixed constant form has one order-zero domination constant valid for
EVERY positive local current and EVERY original nonnegative scalar test. -/
theorem sourceLocalCurrent_exists_uniform_coefficient_bound (γ : formSpan n q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ P : LocalProductCurrent n U q, IsPositive P →
      ∀ φ : 𝓓(U, ℝ), (∀ x, 0 ≤ φ x) →
        |P γ φ| ≤ C * P (kahlerPower n q) φ := by
  let : AddCommGroup (formSpan n q) := Submodule.addCommGroup _
  obtain ⟨C, hC, hminus, hplus⟩ := exists_orderUnit γ.property
  refine ⟨C, hC, fun P hP φ hφ => ?_⟩
  let η : formSpan n q := kahlerPower n q
  have hminus' : ((C • η - γ : formSpan n q) : RealForm n (2 * q)) ∈ spCone q := by
    simpa only [η, kahlerPower, Submodule.coe_sub, Submodule.coe_smul] using hminus
  have hplus' : ((C • η + γ : formSpan n q) : RealForm n (2 * q)) ∈ spCone q := by
    simpa only [η, kahlerPower, Submodule.coe_add, Submodule.coe_smul] using hplus
  have hm := hP.positiveDistribution hminus' φ hφ
  have hp := hP.positiveDistribution hplus' φ hφ
  simp only [map_sub, map_add, map_smul, _root_.sub_apply, _root_.add_apply,
    _root_.smul_apply, smul_eq_mul] at hm hp
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Naturally increasing positive local currents dominated by one positive
current have a genuine LF distribution-valued limit along the WHOLE filter
at infinity. Every variable positive test and every positive remainder is
retained; no limiting functional, continuity or residual certificate is input. -/
theorem sourceLocalCurrent_exists_monotone_dominated_limit
    {κ : Type*} [Preorder κ] [IsDirectedOrder κ] [Nonempty κ]
    (P : κ → LocalProductCurrent n U q) (T : LocalProductCurrent n U q)
    (hP : ∀ j, IsPositive (P j))
    (hmono : ∀ j k, j ≤ k → IsPositive (P k - P j))
    (hdom : ∀ j, IsPositive (T - P j)) :
    ∃ S : LocalProductCurrent n U q,
      IsPositive S ∧ IsPositive (T - S) ∧ (∀ j, IsPositive (S - P j)) ∧
      ∀ (γ : formSpan n q) (φ : 𝓓(U, ℝ)),
        Tendsto (fun j => P j γ φ) atTop (𝓝 (S γ φ)) := by
  classical
  let 𝒰 : Ultrafilter κ := Ultrafilter.of atTop
  have h𝒰 : (𝒰 : Filter κ) ≤ atTop := Ultrafilter.of_le atTop
  let η : formSpan n q := kahlerPower n q
  have htrace (j : κ) : PositiveDistribution (P j η) :=
    (hP j).positiveDistribution_trace
  have htrace_bound : ∀ χ : 𝓓(U, ℝ), (∀ x, 0 ≤ χ x) →
      ∃ B : ℝ, ∀ j, P j η χ ≤ B := by
    intro χ hχ
    refine ⟨T η χ, fun j => ?_⟩
    have h := (hdom j).positiveDistribution_trace χ hχ
    change 0 ≤ T η χ - P j η χ at h
    linarith
  have hcoeff (γ : formSpan n q) : ∃ D : 𝓓'(U, ℝ),
      ∀ φ : 𝓓(U, ℝ), Tendsto (fun j => P j γ φ) (𝒰 : Filter κ) (𝓝 (D φ)) := by
    obtain ⟨C, hC, hbound⟩ := sourceLocalCurrent_exists_uniform_coefficient_bound (U := U) γ
    exact DominatedFullCurrentWeakCompactness.exists_tendsto_dominatedDistribution 𝒰
      (fun j => P j γ) (fun j => P j η) htrace htrace_bound C hC
      (fun j φ hφ => hbound (P j) (hP j) φ hφ)
  choose D hD using hcoeff
  let S : LocalProductCurrent n U q :=
    { toFun := D
      map_add' := fun γ δ => by
        ext φ
        exact tendsto_nhds_unique (hD (γ + δ) φ)
          (((hD γ φ).add (hD δ φ)).congr fun j =>
            congrArg (fun d : 𝓓'(U, ℝ) => d φ) ((P j).map_add γ δ).symm)
      map_smul' := fun c γ => by
        ext φ
        exact tendsto_nhds_unique (hD (c • γ) φ)
          (((hD γ φ).const_smul c).congr fun j =>
            congrArg (fun d : 𝓓'(U, ℝ) => d φ) ((P j).map_smul c γ).symm) }
  have hS (γ : formSpan n q) (φ : 𝓓(U, ℝ)) :
      Tendsto (fun j => P j γ φ) (𝒰 : Filter κ) (𝓝 (S γ φ)) := hD γ φ
  have hpositive : IsPositive S := by
    intro ι _ γ φ hγφ
    exact ge_of_tendsto (tendsto_finsetSum _ fun i _ => hS (γ i) (φ i))
      (Eventually.of_forall fun j => hP j ι γ φ hγφ)
  have hremaining : IsPositive (T - S) := by
    intro ι _ γ φ hγφ
    have hlim := tendsto_finsetSum Finset.univ fun i _ =>
      (tendsto_const_nhds (x := T (γ i) (φ i))).sub (hS (γ i) (φ i))
    exact ge_of_tendsto hlim (Eventually.of_forall fun j => hdom j ι γ φ hγφ)
  have hstage (j : κ) : IsPositive (S - P j) := by
    intro ι _ γ φ hγφ
    have hlim := tendsto_finsetSum Finset.univ fun i _ =>
      (hS (γ i) (φ i)).sub (tendsto_const_nhds (x := P j (γ i) (φ i)))
    have hk : ∀ᶠ k in (𝒰 : Filter κ), j ≤ k := h𝒰 (eventually_ge_atTop j)
    exact ge_of_tendsto hlim (hk.mono fun k hjk => hmono j k hjk ι γ φ hγφ)
  have hpos_test (γ : formSpan n q) (hγ : (γ : RealForm n (2 * q)) ∈ spCone q)
      (φ : 𝓓(U, ℝ)) (hφ : ∀ x, 0 ≤ φ x) :
      Tendsto (fun j => P j γ φ) atTop (𝓝 (S γ φ)) := by
    have hm : Monotone (fun j => P j γ φ) := by
      intro j k hjk
      have h := (hmono j k hjk).positiveDistribution hγ φ hφ
      change 0 ≤ P k γ φ - P j γ φ at h
      linarith
    have hb : BddAbove (range (fun j => P j γ φ)) := by
      refine ⟨T γ φ, ?_⟩
      rintro _ ⟨j, rfl⟩
      have h := (hdom j).positiveDistribution hγ φ hφ
      change 0 ≤ T γ φ - P j γ φ at h
      linarith
    have hall := tendsto_atTop_ciSup hm hb
    have heq : (⨆ j, P j γ φ) = S γ φ :=
      tendsto_nhds_unique (hall.mono_left h𝒰) (hS γ φ)
    simpa only [heq] using hall
  have hpos_form (γ : formSpan n q) (hγ : (γ : RealForm n (2 * q)) ∈ spCone q)
      (φ : 𝓓(U, ℝ)) : Tendsto (fun j => P j γ φ) atTop (𝓝 (S γ φ)) := by
    obtain ⟨χ, hχ, hχdom⟩ := exists_nonneg_testFunction_abs_le
      (testFunctionToCompactlySupportedLM U φ)
    have habs (x : ComplexModel n) : |φ x| ≤ χ x := by
      by_cases hx : x ∈ U
      · exact hχdom ⟨x, hx⟩
      · rw [image_eq_zero_of_notMem_tsupport (fun h => hx (φ.tsupport_subset h)), abs_zero]
        exact hχ x
    have hsum : ∀ x, 0 ≤ (χ + φ) x := by
      intro x
      change 0 ≤ χ x + φ x
      have h := (neg_le_abs (φ x)).trans (habs x)
      linarith
    have hlim := (hpos_test γ hγ (χ + φ) hsum).sub (hpos_test γ hγ χ hχ)
    simpa only [map_add, _root_.add_apply, add_sub_cancel_left] using hlim
  refine ⟨S, hpositive, hremaining, hstage, fun γ φ => ?_⟩
  obtain ⟨C, hC, _hminus, hplus⟩ := exists_orderUnit γ.property
  have hplus' : ((C • η + γ : formSpan n q) : RealForm n (2 * q)) ∈ spCone q := by
    simpa only [η, kahlerPower, Submodule.coe_add, Submodule.coe_smul] using hplus
  have hCη : ((C • η : formSpan n q) : RealForm n (2 * q)) ∈ spCone q := by
    exact smul_mem_spCone
      (formPower_mem_spCone isSemipositiveOneOne_kahlerForm q) hC
  have hlim := (hpos_form (C • η + γ) hplus' φ).sub (hpos_form (C • η) hCη φ)
  simpa only [map_add, _root_.add_apply, add_sub_cancel_left] using hlim

/-- Countably many actual positive local currents, whose finite partial sums
are dominated by one current, sum on every original coefficient/test. Their
actual positive current tails tend to zero, including on signed tests. -/
theorem sourceLocalCurrent_exists_positive_series_limit
    (A : ℕ → LocalProductCurrent n U q) (T : LocalProductCurrent n U q)
    (hA : ∀ i, IsPositive (A i))
    (hdom : ∀ F : Finset ℕ, IsPositive (T - ∑ i ∈ F, A i)) :
    ∃ S : LocalProductCurrent n U q,
      IsPositive S ∧ IsPositive (T - S) ∧
      (∀ F : Finset ℕ, IsPositive (S - ∑ i ∈ F, A i)) ∧
      (∀ (γ : formSpan n q) (φ : 𝓓(U, ℝ)),
        HasSum (fun i => A i γ φ) (S γ φ)) ∧
      ∀ (γ : formSpan n q) (φ : 𝓓(U, ℝ)),
        Tendsto (fun F : Finset ℕ => (S - ∑ i ∈ F, A i) γ φ)
          atTop (𝓝 0) := by
  classical
  have hsum (F : Finset ℕ) : IsPositive (∑ i ∈ F, A i) := by
    induction F using Finset.induction_on with
    | empty => simpa only [Finset.sum_empty] using
        (isPositive_zero : IsPositive (0 : LocalProductCurrent n U q))
    | @insert i F hi hF =>
        simpa only [Finset.sum_insert hi] using (hA i).add hF
  have hm (F G : Finset ℕ) (hFG : F ≤ G) :
      IsPositive ((∑ i ∈ G, A i) - ∑ i ∈ F, A i) := by
    have heq : (∑ i ∈ G, A i) = (∑ i ∈ G \ F, A i) + ∑ i ∈ F, A i :=
      (Finset.sum_sdiff hFG).symm
    rw [heq, add_sub_cancel_right]
    exact hsum _
  obtain ⟨S, hS, hTS, hSF, hlim⟩ :=
    sourceLocalCurrent_exists_monotone_dominated_limit
      (fun F : Finset ℕ => ∑ i ∈ F, A i) T hsum hm hdom
  refine ⟨S, hS, hTS, hSF, ?_, ?_⟩
  · intro γ φ
    simpa only [HasSum, SummationFilter.unconditional_filter, LinearMap.sum_apply, _root_.sum_apply] using hlim γ φ
  · intro γ φ
    have htail := (tendsto_const_nhds (x := S γ φ)).sub (hlim γ φ)
    simpa only [LinearMap.sub_apply, _root_.sub_apply, sub_self] using htail

end SGPT.PSH
