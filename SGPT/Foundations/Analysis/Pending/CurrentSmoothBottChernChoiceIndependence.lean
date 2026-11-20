import SGPT.Foundations.Analysis.Pending.GlobalSmoothScalarDistribution
import SGPT.Foundations.Analysis.Pending.ClosedCurrentSmoothBottChernRepresentative

set_option autoImplicit false

/-! Choice independence in the ACTUAL smooth Bott--Chern quotient, from
full native readings of the SAME original signed current. Entire mathematical
statements and proofs precede this source. No incoming class or smooth scalar
witness; no positivity, Kähler or connectedness substitution. -/

noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Distributions ContDiff Topology

namespace SGPT.Foundations.Analysis.Pending.CurrentSmoothBottChernChoiceIndependence
open FirstPass _root_.SGPT.Foundations.Analysis.LocalCurrents LelongPoincareDivisor
  FiniteScalarDistributionGluing GlobalSmoothScalarDistribution
  ClosedCurrentSmoothBottChernRepresentative

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

omit [IsComplexManifold n M] in
private theorem scalarFamilyCompatible_sub
    (R S : (e : ComplexChart n M) → 𝓓'(chartTarget e, ℝ))
    (hR : ScalarFamilyCompatible R) (hS : ScalarFamilyCompatible S) :
    ScalarFamilyCompatible (fun e => R e - S e) := by
  intro e f η θ hrel
  change R e (TestFunction.monoCLM ℝ η) - S e (TestFunction.monoCLM ℝ η) =
    R f (TestFunction.monoCLM ℝ θ) - S f (TestFunction.monoCLM ℝ θ)
  rw [hR e f η θ hrel, hS e f η θ hrel]

private theorem ddC_sub {V : Opens (ComplexModel n)} (R S : 𝓓'(V, ℝ)) :
    ddC (R - S) = ddC R - ddC S := by
  ext v : 1
  have hv : v = ![v 0, v 1] := by ext i; fin_cases i <;> rfl
  rw [hv, AlternatingMap.sub_apply, ddC_apply, ddC_apply, ddC_apply]
  simp only [map_sub, smul_sub]
  abel

private theorem coefficient_sub (σ τ : ClosedRealOneOneForm n M)
    (e : ComplexChart n M) (z : ComplexModel n) :
    (τ - σ).val.coeff e z = τ.val.coeff e z - σ.val.coeff e z := by
  rw [sub_eq_add_neg, ClosedRealOneOneForm.coeff_add,
    ClosedRealOneOneForm.coeff_neg, ← sub_eq_add_neg]

/-- Equal full native readings internally produce the actual globally smooth
exact difference, ALLn including empty/noncompact/disconnected manifolds. -/
theorem bottChernRel_of_equal_native_readings
    (b : Module.Basis (Fin (Module.finrank ℝ (ComplexModel n))) ℝ (ComplexModel n))
    (σ τ : ClosedRealOneOneForm n M)
    (R S : (e : ComplexChart n M) → 𝓓'(chartTarget e, ℝ))
    (hR : ScalarFamilyCompatible R) (hS : ScalarFamilyCompatible S)
    (hread : ∀ e, smoothFormDistribution b σ.val e + ddC (R e) =
      smoothFormDistribution b τ.val e + ddC (S e)) :
    σ.BottChernRel τ := by
  have hD : ScalarFamilyCompatible (fun e => R e - S e) :=
    scalarFamilyCompatible_sub R S hR hS
  have hcurv (e : ComplexChart n M) :
      ddC (R e - S e) = smoothFormDistribution b (τ - σ).val e := by
    rw [ddC_sub, smoothFormDistribution_sub]
    calc
      ddC (R e) - ddC (S e) =
          (smoothFormDistribution b σ.val e + ddC (R e)) -
            smoothFormDistribution b σ.val e - ddC (S e) := by abel
      _ = (smoothFormDistribution b τ.val e + ddC (S e)) -
            smoothFormDistribution b σ.val e - ddC (S e) := by rw [hread e]
      _ = smoothFormDistribution b τ.val e - smoothFormDistribution b σ.val e := by abel
  obtain ⟨h,hsm,_hreg,hcoeff⟩ :=
    exists_global_smooth_of_smooth_ddC b (τ - σ) (fun e => R e - S e) hD hcurv
  refine ⟨h,hsm,?_⟩
  intro e z hz
  rw [hcoeff e z hz,coefficient_sub]
  abel

/-- Original signed compact closed type-(1,1) T internally supplies a smooth
representative and full scalar readings, with ONE class for ALL alternatives.
No compatibility/atlas/scalar/class witness is an existence input. -/
theorem exists_unique_smooth_class_of_closed_current [CompactSpace M]
    (b : Module.Basis (Fin (Module.finrank ℝ (ComplexModel n))) ℝ (ComplexModel n))
    (hn : 0 < n) (T : GlobalCurrent n M (degreeTwo hn))
    (hclosed : T.IsClosed b) (h11 : T.IsTypeOneOne b hn) :
    ∃ (σ : ClosedRealOneOneForm n M)
      (R : (e : ComplexChart n M) → 𝓓'(chartTarget e, ℝ)),
      ScalarFamilyCompatible R ∧
      (∀ e, T.coefficients b e = smoothFormDistribution b σ.val e + ddC (R e)) ∧
      ∀ (τ : ClosedRealOneOneForm n M)
        (S : (e : ComplexChart n M) → 𝓓'(chartTarget e, ℝ)),
        ScalarFamilyCompatible S →
        (∀ e, T.coefficients b e = smoothFormDistribution b τ.val e + ddC (S e)) →
        RealBottChern.ofRepresentative σ = RealBottChern.ofRepresentative τ := by
  obtain ⟨m,g,P,hP,R,χ,hχ,hc,hs,Q,σ,_hnon,_hsP,_hsum,_hR,_hT,hread,_hQ⟩ :=
    exists_smooth_native_bott_chern_representative b hn T hclosed h11
  let U := finiteScalarFamily g χ hχ hc hs R
  have hU : ScalarFamilyCompatible U := finiteScalarFamily_compatible g χ hχ hc hs R
  refine ⟨σ,U,hU,hread,?_⟩
  intro τ S hS hτ
  apply (RealBottChern.ofRepresentative_eq_iff σ τ).mpr
  apply bottChernRel_of_equal_native_readings b σ τ U S hU hS
  intro e
  exact (hread e).symm.trans (hτ e)

end SGPT.Foundations.Analysis.Pending.CurrentSmoothBottChernChoiceIndependence
