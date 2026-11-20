import SGPT.Projective.NativeCITowerDegree
import SGPT.Projective.NumEqPositiveCartierTwist
import SGPT.Bergman.SiuNativeProjectiveEquivalence

/-! Original Cartier-span numerical injectivity from actual original
positive bundle CI curves, actual finite NS periods and genuine Hodge index. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Projective.NumEq
open Set
open scoped Topology Manifold ContDiff BigOperators
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.NefMixedMass
open SGPT.Hodge.BDivChain.SourceMixedOrderDraft SGPT.BDivisor.NSKodaira
open SGPT.Projective.NumEq.CompleteIntersections

/-- Actual curve degree-zero tests force the ORIGINAL real Cartier-span
class to vanish. The positive native bundle is ordinary original input;
every actual twist bundle, CI curve and mixed vanishing is produced. -/
theorem ofRepresentative_eq_zero_of_numericallyTrivial_of_positive_native_bundle
    {m : ℕ} {X : Type} [TopologicalSpace X]
    [ChartedSpace (ComplexModel (m + 2)) X] [IsComplexManifold (m + 2) X]
    [CompactSpace X] [ConnectedSpace X]
    (A : NativePositiveLine (m + 2) X) (alpha : ClosedRealOneOneForm (m + 2) X)
    (hNS : RealBottChern.ofRepresentative alpha ∈ SGPT.BDivisor.DFAlg.neronSeveri (m + 2) X)
    (hnum : IsNumericallyTrivial alpha) : RealBottChern.ofRepresentative alpha = 0 := by
  classical
  let : MeasurableSpace X := borel X
  let : BorelSpace X := ⟨rfl⟩
  let κ := A.background
  have hfirst := slotIntegral_positive_tuple_eq_zero_of_numericallyTrivial (m + 1) X
    (fun _ => A) κ alpha hnum
  have h1 : slotIntegral κ (oneSlot κ alpha) = 0 := by
    rw [oneSlot_eq_cons]
    exact hfirst
  obtain ⟨N, D, E, a, hE, hquadratic⟩ := exists_finite_divisor_twoSlot_formula κ alpha hNS
  have hdivisor (i : Fin N) :
      slotIntegral κ (Function.update (oneSlot κ alpha) 1 (E i).curvature) = 0 := by
    obtain ⟨M, _hM, B, hB, hOwn, hPos⟩ := exists_positive_native_divisor_twist
      A.bundle A.smooth A.curvature A.own A.positive (D i) (E i) (hE i)
    let BP : NativePositiveLine (m + 2) X := ⟨B, hB, (E i).curvature + (M : ℝ) • A.curvature, hOwn, hPos⟩
    have htwist := slotIntegral_positive_tuple_eq_zero_of_numericallyTrivial (m + 1) X
      (Fin.cons BP (fun _ : Fin m => A)) κ alpha hnum
    have hcurv :
        (fun j : Fin (m + 1) =>
          ((Fin.cons BP (fun _ : Fin m => A) : Fin (m + 1) → NativePositiveLine (m + 2) X) j).curvature) =
        (Fin.cons BP.curvature (fun _ : Fin m => A.curvature) :
          Fin (m + 1) → ClosedRealOneOneForm (m + 2) X) := by
      funext j
      refine Fin.cases rfl (fun _ => rfl) j
    rw [hcurv] at htwist
    change slotIntegral κ (Fin.cons alpha
      (Fin.cons ((E i).curvature + (M : ℝ) • κ.form) (fun _ : Fin m => κ.form))) = 0 at htwist
    rw [← update_oneSlot_eq_cons κ alpha ((E i).curvature + (M : ℝ) • κ.form)] at htwist
    rw [slotIntegral_update_add κ (oneSlot κ alpha) 1,
      slotIntegral_update_smul κ (oneSlot κ alpha) 1] at htwist
    have hrestore : Function.update (oneSlot κ alpha) 1 κ.form = oneSlot κ alpha := by
      apply Function.update_eq_self_iff.mpr
      simp [oneSlot]
    rw [hrestore, h1, smul_zero, add_zero] at htwist
    exact htwist
  have h2 : slotIntegral κ (twoSlot κ alpha) = 0 := by
    rw [hquadratic]
    simp only [hdivisor, mul_zero, Finset.sum_const_zero]
  exact ofRepresentative_eq_zero_of_slotIntegral_twoSlot_eq_zero κ alpha h1 h2

/-- The original source-facing analytic projectivity predicate produces
the actual positive native bundle; the actual original NS numerical class
is zero in every dimension, with genuine dimension-zero/curve cases. -/
theorem ofRepresentative_eq_zero_of_numericallyTrivial_of_isProjectiveManifold
    {n : ℕ} {X : Type} [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    [CompactSpace X] [ConnectedSpace X]
    (hproj : SGPT.Trace.Bertini.IsProjectiveManifold n X)
    (alpha : ClosedRealOneOneForm n X)
    (hNS : RealBottChern.ofRepresentative alpha ∈ SGPT.BDivisor.DFAlg.neronSeveri n X)
    (hnum : IsNumericallyTrivial alpha) : RealBottChern.ofRepresentative alpha = 0 := by
  obtain ⟨omega, hK, hωNS⟩ := isProjectiveManifold_iff_exists_kahler_mem_neronSeveri.mp hproj
  obtain ⟨B, hB, theta, hOwn, hPos⟩ := exists_positive_native_bundle_of_kahler_mem_neronSeveri
    omega hK hωNS
  let A : NativePositiveLine n X := ⟨B, hB, theta, hOwn, hPos⟩
  cases n with
  | zero =>
      have hzero : alpha = 0 := by
        apply ClosedRealOneOneForm.ext
        intro e z
        apply ContinuousAlternatingMap.ext
        intro v
        change (alpha.val.coeff e z) v = 0
        exact (alpha.val.coeff e z).map_coord_zero (0 : Fin 2) (Subsingleton.elim (v 0) 0)
      rw [hzero, RealBottChern.ofRepresentative_zero]
  | succ n =>
      cases n with
      | zero => exact (isNumericallyTrivial_iff_dim_one A.background alpha).mp hnum
      | succ m => exact ofRepresentative_eq_zero_of_numericallyTrivial_of_positive_native_bundle A alpha hNS hnum

/-- Original NS classes on the SAME analytically projective manifold are
numerically trivial on actual compact curves exactly when they are zero. -/
theorem isNumericallyTrivial_iff_of_isProjectiveManifold
    {n : ℕ} {X : Type} [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    [CompactSpace X] [ConnectedSpace X]
    (hproj : SGPT.Trace.Bertini.IsProjectiveManifold n X)
    (alpha : ClosedRealOneOneForm n X)
    (hNS : RealBottChern.ofRepresentative alpha ∈ SGPT.BDivisor.DFAlg.neronSeveri n X) :
    IsNumericallyTrivial alpha ↔ RealBottChern.ofRepresentative alpha = 0 :=
  ⟨ofRepresentative_eq_zero_of_numericallyTrivial_of_isProjectiveManifold hproj alpha hNS,
    isNumericallyTrivial_of_ofRepresentative_eq_zero⟩

/-- The actual degree along the SAME original compact curve is additive
under subtraction, by literal original pullback and one-slot linearity. -/
theorem degreeAlong_sub_actual {n : ℕ} {X C : Type}
    [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    [TopologicalSpace C] [ChartedSpace (ComplexModel 1) C] [IsComplexManifold 1 C] [CompactSpace C]
    (κ : KahlerBackground 1 C) {g : C → X}
    (hg : ContMDiff 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ComplexModel n) ∞ g)
    (alpha beta : ClosedRealOneOneForm n X) :
    degreeAlong κ hg (alpha - beta) = degreeAlong κ hg alpha - degreeAlong κ hg beta := by
  let : MeasurableSpace C := borel C
  let : BorelSpace C := ⟨rfl⟩
  have hpb : ClosedRealOneOneForm.pullback hg (alpha - beta) =
      ClosedRealOneOneForm.pullback hg alpha - ClosedRealOneOneForm.pullback hg beta := by
    apply ClosedRealOneOneForm.ext
    intro e z
    ext v
    rfl
  change slotIntegral κ (fun _ => ClosedRealOneOneForm.pullback hg (alpha - beta)) =
    slotIntegral κ (fun _ => ClosedRealOneOneForm.pullback hg alpha) -
      slotIntegral κ (fun _ => ClosedRealOneOneForm.pullback hg beta)
  rw [hpb]
  have hm := (slotIntegralMultilinear κ).map_update_sub (fun _ => κ.form) 0
    (ClosedRealOneOneForm.pullback hg alpha) (ClosedRealOneOneForm.pullback hg beta)
  simp only [slotIntegralMultilinear, MultilinearMap.mk'_apply] at hm
  rw [← fun_eq_update_dim_one, ← fun_eq_update_dim_one, ← fun_eq_update_dim_one] at hm
  exact hm

/-- Actual original numerical equivalence is injective on the ORIGINAL
real Cartier-span classes, with the SAME existing projectivity predicate. -/
theorem ofRepresentative_eq_of_numericallyEquivalent_of_isProjectiveManifold
    {n : ℕ} {X : Type} [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    [CompactSpace X] [ConnectedSpace X]
    (hproj : SGPT.Trace.Bertini.IsProjectiveManifold n X)
    (alpha beta : ClosedRealOneOneForm n X)
    (hNSalpha : RealBottChern.ofRepresentative alpha ∈ SGPT.BDivisor.DFAlg.neronSeveri n X)
    (hNSbeta : RealBottChern.ofRepresentative beta ∈ SGPT.BDivisor.DFAlg.neronSeveri n X)
    (hnum : NumericallyEquivalent alpha beta) :
    RealBottChern.ofRepresentative alpha = RealBottChern.ofRepresentative beta := by
  have hclass : RealBottChern.ofRepresentative (alpha - beta) =
      RealBottChern.ofRepresentative alpha - RealBottChern.ofRepresentative beta := by
    rw [sub_eq_add_neg, RealBottChern.ofRepresentative_add, RealBottChern.ofRepresentative_neg,
      ← sub_eq_add_neg]
  have hNS : RealBottChern.ofRepresentative (alpha - beta) ∈ SGPT.BDivisor.DFAlg.neronSeveri n X := by
    rw [hclass]
    exact (SGPT.BDivisor.DFAlg.neronSeveri n X).sub_mem hNSalpha hNSbeta
  have hsub : IsNumericallyTrivial (alpha - beta) := by
    intro C _ _ _ _ _ κ g hg
    rw [degreeAlong_sub_actual, hnum C κ g hg, sub_self]
  have hzero := ofRepresentative_eq_zero_of_numericallyTrivial_of_isProjectiveManifold
    hproj (alpha - beta) hNS hsub
  rw [hclass] at hzero
  exact sub_eq_zero.mp hzero

/-- The SAME original compact-curve numerical equivalence relation on
the original real Cartier span is exactly original Bott--Chern equality. -/
theorem numericallyEquivalent_iff_of_isProjectiveManifold
    {n : ℕ} {X : Type} [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    [CompactSpace X] [ConnectedSpace X]
    (hproj : SGPT.Trace.Bertini.IsProjectiveManifold n X)
    (alpha beta : ClosedRealOneOneForm n X)
    (hNSalpha : RealBottChern.ofRepresentative alpha ∈ SGPT.BDivisor.DFAlg.neronSeveri n X)
    (hNSbeta : RealBottChern.ofRepresentative beta ∈ SGPT.BDivisor.DFAlg.neronSeveri n X) :
    NumericallyEquivalent alpha beta ↔
      RealBottChern.ofRepresentative alpha = RealBottChern.ofRepresentative beta :=
  ⟨ofRepresentative_eq_of_numericallyEquivalent_of_isProjectiveManifold hproj alpha beta hNSalpha hNSbeta,
    numericallyEquivalent_of_ofRepresentative_eq⟩

end SGPT.Projective.NumEq
