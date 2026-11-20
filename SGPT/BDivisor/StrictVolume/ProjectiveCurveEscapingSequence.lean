import SGPT.BDivisor.StrictVolume.HomogeneousDehomogenization
import SGPT.BDivisor.StrictVolume.AffineCurveEscapingSequence
import Mathlib.RingTheory.Nullstellensatz

/-! Actual original projective points and native algebraic-cone incidence.
The native ProjectiveSpectrum point dictionary is supplied by the subsequent module.
Kernel status and retained attempts are recorded separately in the owned check packets. -/

set_option autoImplicit false
noncomputable section

namespace SGPT.BDivisor.ProjectiveCurveEscapeNext

open Filter Topology SGPT.Projective
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.BDivisor.StrictSequenceNext

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The exact original projective-chart points used by the moving-centre cone. -/
def projectiveCurveEscapingSequence (n : ℕ) : ComplexProjectiveSpace 2 :=
  ComplexProjectiveSpace.affinePoint 0 (WithLp.toLp 2 ![(n : ℂ), Complex.exp (n : ℂ)])

theorem projectiveCurveEscapingSequence_eq_original_affine (n : ℕ) :
    projectiveCurveEscapingSequence n = ComplexProjectiveSpace.affinePoint 0
      (WithLp.toLp 2 ![(affineCurveEscapingSequence n).1, (affineCurveEscapingSequence n).2]) := by
  simp only [projectiveCurveEscapingSequence, affineCurveEscapingSequence,
    Complex.ofReal_exp, Complex.ofReal_natCast]

theorem projectiveCurveEscapingSequence_injective :
    Function.Injective projectiveCurveEscapingSequence := by
  intro i j hij
  have hz := congrArg (ComplexProjectiveSpace.affineChart 0) hij
  simp only [projectiveCurveEscapingSequence,
    ComplexProjectiveSpace.affineChart_affinePoint] at hz
  have hx := congrArg (fun z : ComplexModel 2 => z 0) hz
  change (i : ℂ) = (j : ℂ) at hx
  exact_mod_cast hx

/-- The literal polynomial zero locus on the original projective carrier. -/
def actualProjectiveHypersurface (P : MvPolynomial (Fin 3) ℂ) :
    Set (ComplexProjectiveSpace 2) :=
  {p | MvPolynomial.eval (ComplexProjectiveSpace.rep p) P = 0}

theorem mem_actualProjectiveHypersurface_mk
    {P : MvPolynomial (Fin 3) ℂ} {d : ℕ} (hP : P.IsHomogeneous d)
    (v : Fin 3 → ℂ) (hv : v ≠ 0) :
    ComplexProjectiveSpace.mk v hv ∈ actualProjectiveHypersurface P ↔
      MvPolynomial.eval v P = 0 := by
  obtain ⟨c, hc, hrep⟩ :=
    ComplexProjectiveSpace.rep_smul (ComplexProjectiveSpace.mk v hv) hv rfl
  change MvPolynomial.eval (ComplexProjectiveSpace.rep (ComplexProjectiveSpace.mk v hv)) P = 0 ↔ _
  rw [hrep, ComplexProjectiveSpace.eval_smul_of_isHomogeneous hP]
  simp only [mul_eq_zero, pow_ne_zero _ hc, false_or]

theorem mem_actualProjectiveHypersurface_affinePoint0
    {P : MvPolynomial (Fin 3) ℂ} {d : ℕ} (hP : P.IsHomogeneous d) (x y : ℂ) :
    ComplexProjectiveSpace.affinePoint 0 (WithLp.toLp 2 ![x, y]) ∈
        actualProjectiveHypersurface P ↔
      MvPolynomial.eval ![x, y] (actualDehomogenize0 P) = 0 := by
  rw [ComplexProjectiveSpace.affinePoint, mem_actualProjectiveHypersurface_mk hP]
  have hlift : ComplexProjectiveSpace.affineLift 0 (WithLp.toLp 2 ![x, y]) =
      Fin.cons 1 ![x, y] := by
    ext i
    fin_cases i <;> rfl
  rw [hlift, ← actualDehomogenize0_eval]

theorem projectiveCurveEscapingSequence_eventually_outside_hypersurface
    {P : MvPolynomial (Fin 3) ℂ} {d : ℕ} (hP : P.IsHomogeneous d) (hP0 : P ≠ 0) :
    ∀ᶠ n : ℕ in atTop, projectiveCurveEscapingSequence n ∉ actualProjectiveHypersurface P := by
  have hD := actualBivariateEncode_dehomogenize_ne_zero hP hP0
  filter_upwards [affineCurveEscapingSequence_eventually_outside
    (actualBivariateEncode (actualDehomogenize0 P)) hD] with n hn
  rw [projectiveCurveEscapingSequence_eq_original_affine,
    mem_actualProjectiveHypersurface_affinePoint0 hP]
  rw [actualBivariateEncode_eval] at hn
  exact hn

theorem projectiveCurveEscapingSequence_hypersurface_incidence_finite
    {P : MvPolynomial (Fin 3) ℂ} {d : ℕ} (hP : P.IsHomogeneous d) (hP0 : P ≠ 0) :
    {n : ℕ | projectiveCurveEscapingSequence n ∈ actualProjectiveHypersurface P}.Finite := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (projectiveCurveEscapingSequence_eventually_outside_hypersurface hP hP0)
  refine (Set.finite_Iio N).subset ?_
  intro n hn
  show n < N
  by_contra h
  exact hN n (le_of_not_gt h) hn

/-- A native homogeneous ideal internally supplies its nonzero homogeneous witness. -/
theorem exists_nonzero_homogeneous_mem_native_ideal
    (I : Ideal (MvPolynomial (Fin 3) ℂ))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin 3) ℂ)) (hI0 : I ≠ ⊥) :
    ∃ (d : ℕ) (P : MvPolynomial (Fin 3) ℂ),
      P ∈ I ∧ P.IsHomogeneous d ∧ P ≠ 0 := by
  classical
  obtain ⟨f, hf, hf0⟩ : ∃ f : MvPolynomial (Fin 3) ℂ, f ∈ I ∧ f ≠ 0 := by
    by_contra h
    apply hI0
    ext f
    simp only [Ideal.mem_bot]
    constructor
    · intro hf
      by_contra hf0
      exact h ⟨f, hf, hf0⟩
    · rintro rfl
      exact I.zero_mem
  obtain ⟨d, hd⟩ : ∃ d : ℕ, MvPolynomial.homogeneousComponent d f ≠ 0 := by
    by_contra h
    push Not at h
    apply hf0
    rw [← MvPolynomial.sum_homogeneousComponent f]
    exact Finset.sum_eq_zero (fun d _ => h d)
  exact ⟨d, MvPolynomial.homogeneousComponent d f,
    MvPolynomial.homogeneousComponent_mem_of_mem hI hf d,
    MvPolynomial.homogeneousComponent_isHomogeneous d f, hd⟩

/-- The actual projectivized native affine algebraic zero locus, with the zero vector removed. -/
def actualProjectiveIdealZeroLocus (I : Ideal (MvPolynomial (Fin 3) ℂ)) :
    Set (ComplexProjectiveSpace 2) :=
  {p | ∃ (v : Fin 3 → ℂ) (hv : v ≠ 0),
    ComplexProjectiveSpace.mk v hv = p ∧ v ∈ MvPolynomial.zeroLocus ℂ I}

theorem actualProjectiveIdealZeroLocus_subset_hypersurface
    {I : Ideal (MvPolynomial (Fin 3) ℂ)} {P : MvPolynomial (Fin 3) ℂ} {d : ℕ}
    (hPI : P ∈ I) (hP : P.IsHomogeneous d) :
    actualProjectiveIdealZeroLocus I ⊆ actualProjectiveHypersurface P := by
  rintro p ⟨v, hv, rfl, hvI⟩
  apply (mem_actualProjectiveHypersurface_mk hP v hv).mpr
  have hvP := hvI P hPI
  exact hvP

theorem native_projective_algebraic_zero_locus_incidence_finite
    (I : Ideal (MvPolynomial (Fin 3) ℂ))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin 3) ℂ))
    (hproper : actualProjectiveIdealZeroLocus I ≠ Set.univ) :
    {n : ℕ | projectiveCurveEscapingSequence n ∈ actualProjectiveIdealZeroLocus I}.Finite := by
  have hI0 : I ≠ ⊥ := by
    intro h
    apply hproper
    apply Set.eq_univ_of_forall
    intro p
    refine ⟨ComplexProjectiveSpace.rep p, ComplexProjectiveSpace.rep_ne_zero p,
      ComplexProjectiveSpace.mk_rep p, ?_⟩
    rw [h, MvPolynomial.zeroLocus_bot]
    trivial
  obtain ⟨d, P, hPI, hP, hP0⟩ := exists_nonzero_homogeneous_mem_native_ideal I hI hI0
  exact (projectiveCurveEscapingSequence_hypersurface_incidence_finite hP hP0).subset
    (fun _ hn => actualProjectiveIdealZeroLocus_subset_hypersurface hPI hP hn)

end SGPT.BDivisor.ProjectiveCurveEscapeNext
