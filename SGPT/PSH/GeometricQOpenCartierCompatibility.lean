import SGPT.PSH.LocalIntegralGlobalOpenCoefficients
import SGPT.PSH.CanonicalCartierFaithfulness
import SGPT.PSH.CartierOpenStalkCoefficient

set_option autoImplicit false
noncomputable section
namespace SGPT.PSH
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending
open scoped Topology Manifold ContDiff

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

/-- An explicit ORIGINAL local Cartier coefficient identity survives the
genuine rational open restriction, including every split prime. The later
original-input pullback producer manufactures this hypothesis internally. -/
theorem geometricQDivisorOpenRestriction_coefficient_of_local_cartier_coefficients
    (D : EffectiveGeometricQDivisor (m + 1) M) (H : EffectiveDivisor (m + 1) M)
    (c : ℚ) (hc : 0 < c) (V : Set M)
    (hcoeff : ∀ P : GeometricPrimeCarrier (m + 1) M, (P.val ∩ V).Nonempty →
      D.coefficient P = c * (cartierGeometricPrimeCoefficient H P : ℚ))
    (U : Opens M) (A : GeometricPrimeCarrier (m + 1) U)
    (hA : (A.val ∩ (Subtype.val : U → M) ⁻¹' V).Nonempty) :
    (geometricQDivisorOpenRestriction D U).coefficient A =
      c * (cartierGeometricPrimeCoefficient (cartierOpenRestriction H U) A : ℚ) := by
  classical
  obtain ⟨y, hyA, hyV⟩ := hA
  obtain ⟨W, hyW, s, d, a, _hs, hd, _ha, hglobal, hopen⟩ :=
    exists_geometric_q_local_integral_global_open_coefficients D (y : M)
  let F := ∑ P ∈ s, a P • geometricPrimeCarrierEffectiveDivisor P.val
  obtain ⟨k, b, hk, hb⟩ := exists_finite_positive_rational_denominator
    ({()} : Finset Unit) (fun _ => c) (fun _ _ => hc)
  have hcfrac : c = (b () : ℚ) / (k : ℚ) := (hb () (by simp)).2
  have hdQ : (0 : ℚ) < d := by exact_mod_cast hd
  have hkQ : (0 : ℚ) < k := by exact_mod_cast hk
  have hscaled (P : GeometricPrimeCarrier (m + 1) M)
      (hP : (P.val ∩ (V ∩ (W : Set M))).Nonempty) :
      cartierGeometricPrimeCoefficient (k • F) P =
        cartierGeometricPrimeCoefficient ((d * b ()) • H) P := by
    have hPV : (P.val ∩ V).Nonempty := hP.mono (fun _ hz => ⟨hz.1, hz.2.1⟩)
    have hPW : (P.val ∩ (W : Set M)).Nonempty := hP.mono (fun _ hz => ⟨hz.1, hz.2.2⟩)
    have heq : (cartierGeometricPrimeCoefficient F P : ℚ) / (d : ℚ) =
        ((b () : ℚ) / (k : ℚ)) * (cartierGeometricPrimeCoefficient H P : ℚ) := by
      exact (hglobal P hPW).symm.trans ((hcoeff P hPV).trans (by rw [hcfrac]))
    have hmul : (k : ℚ) * (cartierGeometricPrimeCoefficient F P : ℚ) =
        (d : ℚ) * (b () : ℚ) * (cartierGeometricPrimeCoefficient H P : ℚ) := by
      field_simp [ne_of_gt hdQ, ne_of_gt hkQ] at heq
      nlinarith [heq]
    rw [cartierGeometricPrimeCoefficient_nsmul, cartierGeometricPrimeCoefficient_nsmul]
    exact_mod_cast hmul
  have hle₁ := cartierIdeal_le_on_of_geometricPrimeCoefficient_le
    (k • F) ((d * b ()) • H) (V ∩ (W : Set M)) (fun P hP => (hscaled P hP).le)
  have hle₂ := cartierIdeal_le_on_of_geometricPrimeCoefficient_le
    ((d * b ()) • H) (k • F) (V ∩ (W : Set M)) (fun P hP => (hscaled P hP).symm.le)
  have hscaledA := cartierGeometricPrimeCoefficient_open_eq_of_stalk_ideal_eq
    (k • F) ((d * b ()) • H) U A y hyA
    (fun f => ⟨hle₂ y ⟨hyV, hyW⟩ f, hle₁ y ⟨hyV, hyW⟩ f⟩)
  change cartierGeometricPrimeCoefficient ((cartierOpenRestrictionHom U) (k • F)) A =
    cartierGeometricPrimeCoefficient ((cartierOpenRestrictionHom U) ((d * b ()) • H)) A at hscaledA
  rw [map_nsmul, map_nsmul, cartierGeometricPrimeCoefficient_nsmul,
    cartierGeometricPrimeCoefficient_nsmul] at hscaledA
  have hscaledQ : (k : ℚ) *
      (cartierGeometricPrimeCoefficient (cartierOpenRestriction F U) A : ℚ) =
      (d : ℚ) * (b () : ℚ) *
        (cartierGeometricPrimeCoefficient (cartierOpenRestriction H U) A : ℚ) := by
    exact_mod_cast hscaledA
  rw [hopen U A ⟨y, hyA, hyW⟩, hcfrac]
  field_simp [ne_of_gt hdQ, ne_of_gt hkQ]
  nlinarith [hscaledQ]

end SGPT.PSH
