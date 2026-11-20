import SGPT.BDivisor.StrictVolume.ProjectiveCurveEscapingSequence
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Topology
import Mathlib.RingTheory.GradedAlgebra.Radical

/-! The actual original complex projective points as native projective-spectrum points.
The native homogeneous core manufactures the dictionary; no curve equation is supplied.
Kernel status and retained attempts are recorded separately in the owned check packets. -/

set_option autoImplicit false
noncomputable section

namespace SGPT.BDivisor.ProjectiveCurveEscapeNext

open SGPT.Projective

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The genuine homogeneous ideal of the line spanned by the original vector. -/
def actualNativeHomogeneousPointIdeal (v : Fin 3 → ℂ) :
    HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 3) ℂ) :=
  (MvPolynomial.vanishingIdeal ℂ ({v} : Set (Fin 3 → ℂ))).homogeneousCore
    (MvPolynomial.homogeneousSubmodule (Fin 3) ℂ)

/-- The actual relevant homogeneous prime determined by a nonzero vector. -/
def nativeProjectivePointOfVector (v : Fin 3 → ℂ) (hv : v ≠ 0) :
    ProjectiveSpectrum (MvPolynomial.homogeneousSubmodule (Fin 3) ℂ) where
  asHomogeneousIdeal := actualNativeHomogeneousPointIdeal v
  isPrime := (inferInstance :
    (MvPolynomial.vanishingIdeal ℂ ({v} : Set (Fin 3 → ℂ))).IsPrime).homogeneousCore
  not_irrelevant_le := by
    intro h
    obtain ⟨j, hj⟩ : ∃ j : Fin 3, v j ≠ 0 := by
      by_contra h
      apply hv
      ext j
      by_contra hj
      exact h ⟨j, hj⟩
    have hX := h (HomogeneousIdeal.mem_irrelevant_of_mem
      (MvPolynomial.homogeneousSubmodule (Fin 3) ℂ) (by decide : 0 < (1 : ℕ))
      (MvPolynomial.isHomogeneous_X ℂ j))
    have hXeval := Ideal.toIdeal_homogeneousCore_le
      (MvPolynomial.homogeneousSubmodule (Fin 3) ℂ)
      (MvPolynomial.vanishingIdeal ℂ ({v} : Set (Fin 3 → ℂ))) hX
    apply hj
    have := (MvPolynomial.mem_vanishingIdeal_singleton_iff v (MvPolynomial.X j)).mp hXeval
    simpa only [MvPolynomial.aeval_X] using this

theorem nativeProjectivePointOfVector_homogeneous_mem
    (v : Fin 3 → ℂ) (hv : v ≠ 0)
    {P : MvPolynomial (Fin 3) ℂ} {d : ℕ} (hP : P.IsHomogeneous d) :
    P ∈ (nativeProjectivePointOfVector v hv).asHomogeneousIdeal ↔
      MvPolynomial.eval v P = 0 := by
  constructor
  · intro h
    have hmem := Ideal.toIdeal_homogeneousCore_le
      (MvPolynomial.homogeneousSubmodule (Fin 3) ℂ)
      (MvPolynomial.vanishingIdeal ℂ ({v} : Set (Fin 3 → ℂ))) h
    exact (MvPolynomial.mem_vanishingIdeal_singleton_iff v P).mp hmem
  · intro h
    exact Ideal.mem_homogeneousCore_of_homogeneous_of_mem ⟨d, hP⟩
      ((MvPolynomial.mem_vanishingIdeal_singleton_iff v P).mpr h)

/-- The native projective-spectrum point of the original canonical projective point. -/
def actualNativeProjectivePoint (p : ComplexProjectiveSpace 2) :
    ProjectiveSpectrum (MvPolynomial.homogeneousSubmodule (Fin 3) ℂ) :=
  nativeProjectivePointOfVector (ComplexProjectiveSpace.rep p)
    (ComplexProjectiveSpace.rep_ne_zero p)

theorem actualNativeProjectivePoint_mk (v : Fin 3 → ℂ) (hv : v ≠ 0) :
    actualNativeProjectivePoint (ComplexProjectiveSpace.mk v hv) =
      nativeProjectivePointOfVector v hv := by
  apply ProjectiveSpectrum.ext
  apply HomogeneousIdeal.ext'
  intro d P hP
  change P ∈ (nativeProjectivePointOfVector
      (ComplexProjectiveSpace.rep (ComplexProjectiveSpace.mk v hv)) _).asHomogeneousIdeal ↔
    P ∈ (nativeProjectivePointOfVector v hv).asHomogeneousIdeal
  rw [nativeProjectivePointOfVector_homogeneous_mem _ _ hP,
    nativeProjectivePointOfVector_homogeneous_mem v hv hP]
  obtain ⟨c, hc, hrep⟩ :=
    ComplexProjectiveSpace.rep_smul (ComplexProjectiveSpace.mk v hv) hv rfl
  rw [hrep, ComplexProjectiveSpace.eval_smul_of_isHomogeneous hP]
  simp only [mul_eq_zero, pow_ne_zero _ hc, false_or]

theorem nativeProjectivePointOfVector_mem_zeroLocus
    (v : Fin 3 → ℂ) (hv : v ≠ 0) (I : Ideal (MvPolynomial (Fin 3) ℂ))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin 3) ℂ)) :
    nativeProjectivePointOfVector v hv ∈ ProjectiveSpectrum.zeroLocus
        (MvPolynomial.homogeneousSubmodule (Fin 3) ℂ) (I : Set _) ↔
      v ∈ MvPolynomial.zeroLocus ℂ I := by
  rw [ProjectiveSpectrum.mem_zeroLocus, MvPolynomial.mem_zeroLocus_iff]
  constructor
  · intro h P hPI
    have hmem := Ideal.toIdeal_homogeneousCore_le
      (MvPolynomial.homogeneousSubmodule (Fin 3) ℂ)
      (MvPolynomial.vanishingIdeal ℂ ({v} : Set (Fin 3 → ℂ))) (h hPI)
    exact (MvPolynomial.mem_vanishingIdeal_singleton_iff v P).mp hmem
  · intro h P hPI
    apply (MvPolynomial.mem_iff_homogeneousComponent_mem
      (actualNativeHomogeneousPointIdeal v).isHomogeneous P).mpr
    intro d
    apply (nativeProjectivePointOfVector_homogeneous_mem v hv
      (MvPolynomial.homogeneousComponent_isHomogeneous d P)).mpr
    exact h _ (MvPolynomial.homogeneousComponent_mem_of_mem hI hPI d)

theorem actualNativeProjectivePoint_preimage_zeroLocus
    (I : Ideal (MvPolynomial (Fin 3) ℂ))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin 3) ℂ)) :
    actualNativeProjectivePoint ⁻¹' ProjectiveSpectrum.zeroLocus
        (MvPolynomial.homogeneousSubmodule (Fin 3) ℂ) (I : Set _) =
      actualProjectiveIdealZeroLocus I := by
  ext p
  constructor
  · intro hp
    refine ⟨ComplexProjectiveSpace.rep p, ComplexProjectiveSpace.rep_ne_zero p,
      ComplexProjectiveSpace.mk_rep p, ?_⟩
    exact (nativeProjectivePointOfVector_mem_zeroLocus
      (ComplexProjectiveSpace.rep p) (ComplexProjectiveSpace.rep_ne_zero p) I hI).mp hp
  · rintro ⟨v, hv, rfl, hvI⟩
    change actualNativeProjectivePoint (ComplexProjectiveSpace.mk v hv) ∈
      ProjectiveSpectrum.zeroLocus (MvPolynomial.homogeneousSubmodule (Fin 3) ℂ)
        (I : Set (MvPolynomial (Fin 3) ℂ))
    rw [actualNativeProjectivePoint_mk]
    exact (nativeProjectivePointOfVector_mem_zeroLocus v hv I hI).mpr hvI

theorem native_projective_spectrum_zero_locus_incidence_finite
    (I : Ideal (MvPolynomial (Fin 3) ℂ))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin 3) ℂ)) (hI0 : I ≠ ⊥) :
    {n : ℕ | actualNativeProjectivePoint (projectiveCurveEscapingSequence n) ∈
      ProjectiveSpectrum.zeroLocus (MvPolynomial.homogeneousSubmodule (Fin 3) ℂ)
        (I : Set _)}.Finite := by
  obtain ⟨d, P, hPI, hP, hP0⟩ := exists_nonzero_homogeneous_mem_native_ideal I hI hI0
  refine (projectiveCurveEscapingSequence_hypersurface_incidence_finite hP hP0).subset ?_
  intro n hn
  have hmem := (ProjectiveSpectrum.mem_zeroLocus _ _ _).mp hn hPI
  change MvPolynomial.eval (ComplexProjectiveSpace.rep (projectiveCurveEscapingSequence n)) P = 0
  exact (nativeProjectivePointOfVector_homogeneous_mem
    (ComplexProjectiveSpace.rep (projectiveCurveEscapingSequence n))
    (ComplexProjectiveSpace.rep_ne_zero (projectiveCurveEscapingSequence n)) hP).mp hmem

/-- The native source curve condition, in fact for every proper projective algebraic closed set. -/
theorem every_proper_native_projective_algebraic_closed_incidence_finite
    (Z : Set (ProjectiveSpectrum (MvPolynomial.homogeneousSubmodule (Fin 3) ℂ)))
    (hZ : IsClosed Z) (hproper : Z ≠ Set.univ) :
    {n : ℕ | actualNativeProjectivePoint (projectiveCurveEscapingSequence n) ∈ Z}.Finite := by
  let J := ProjectiveSpectrum.vanishingIdeal Z
  have hzero : ProjectiveSpectrum.zeroLocus
      (MvPolynomial.homogeneousSubmodule (Fin 3) ℂ)
      (J.toIdeal : Set (MvPolynomial (Fin 3) ℂ)) = Z := by
    exact (ProjectiveSpectrum.zeroLocus_vanishingIdeal_eq_closure
      (MvPolynomial.homogeneousSubmodule (Fin 3) ℂ) Z).trans hZ.closure_eq
  have hJ0 : J.toIdeal ≠ ⊥ := by
    intro h
    apply hproper
    rw [← hzero, h, ProjectiveSpectrum.zeroLocus_bot]
  have hfin := native_projective_spectrum_zero_locus_incidence_finite
    J.toIdeal J.isHomogeneous hJ0
  simpa only [hzero] using hfin

end SGPT.BDivisor.ProjectiveCurveEscapeNext
