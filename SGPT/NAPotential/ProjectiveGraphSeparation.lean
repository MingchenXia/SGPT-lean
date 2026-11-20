import SGPT.NAPotential.ProjectiveGraphRelationCore
import SGPT.NAPotential.ProjectiveGraphSegreEquations

/-!
# Actual homogeneous relations separate the regular Segre graph

Relations are constructed in every Segre column. A nonzero column removes the
extra-fibre factor that a single padded cross-multiplication relation would have.
Blueprint: `projective-graph-separation.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.NAPotential.AlgPrimes3.ProjectiveGraphSeparation

open MvPolynomial ProjectiveGraphRelations ProjectiveGraphRelationCore
open ProjectiveGraphSegreEquations

attribute [local instance] MvPolynomial.gradedAlgebra

variable {I J L A K F : Type*} [CommRing A] [CommRing K] [Algebra A K]

/-- An actual polynomial on the original base, inserted in one actual Segre column. -/
def columnPolynomial (e : L ≃ I × J) (j : J) (p : MvPolynomial I A) : MvPolynomial L A :=
  rename (fun i => e.symm (i, j)) p

/-- An actual homogeneous Segre relation enforcing an original numerator/denominator equation. -/
def columnRelation (e : L ≃ I × J) (i₀ : I) (j₀ j l : J)
    (d a : MvPolynomial I A) : MvPolynomial L A :=
  columnPolynomial e j d * X (e.symm (i₀, l)) -
    columnPolynomial e j a * X (e.symm (i₀, j₀))

theorem columnRelation_isHomogeneous (e : L ≃ I × J) (i₀ : I) (j₀ j l : J)
    {d a : MvPolynomial I A} {n : ℕ} (hd : d.IsHomogeneous n) (ha : a.IsHomogeneous n) :
    (columnRelation e i₀ j₀ j l d a).IsHomogeneous (n + 1) :=
  (hd.rename_isHomogeneous.mul (isHomogeneous_X A _)).sub
    (ha.rename_isHomogeneous.mul (isHomogeneous_X A _))

/-- The actual column relation evaluates to its original numerator/denominator equation. -/
theorem aeval_columnRelation (e : L ≃ I × J) (i₀ : I) (j₀ j l : J)
    {d a : MvPolynomial I A} {n : ℕ} (hd : d.IsHomogeneous n) (ha : a.IsHomogeneous n)
    (x : I → K) (y : J → K) :
    aeval (segreVector e x y) (columnRelation e i₀ j₀ j l d a) =
      y j ^ n * x i₀ * (aeval x d * y l - aeval x a * y j₀) := by
  have hd' : aeval (fun i => x i * y j) d = y j ^ n * aeval x d := by
    simpa only [aeval_eq_eval₂Hom, mul_comm] using
      eval₂Hom_scale_of_isHomogeneous hd (algebraMap A K) x (y j)
  have ha' : aeval (fun i => x i * y j) a = y j ^ n * aeval x a := by
    simpa only [aeval_eq_eval₂Hom, mul_comm] using
      eval₂Hom_scale_of_isHomogeneous ha (algebraMap A K) x (y j)
  simp only [columnRelation, columnPolynomial, map_sub, map_mul, aeval_rename,
    aeval_X, Function.comp_def, segreVector, Equiv.apply_symm_apply]
  rw [hd', ha']
  ring

/-- Each constructed column polynomial is a member of the full original relation ideal. -/
theorem columnRelation_mem (e : L ≃ I × J) (i₀ : I) (j₀ j l : J)
    {d a : MvPolynomial I A} {n : ℕ} (hd : d.IsHomogeneous n) (ha : a.IsHomogeneous n)
    (c : I → K) (b : J → K) (hrel : aeval c d * b l = aeval c a * b j₀) :
    columnRelation e i₀ j₀ j l d a ∈ (relationCore (A := A) (segreVector e c b)).toIdeal := by
  apply Ideal.mem_homogeneousCore_of_homogeneous_of_mem
    ⟨n + 1, columnRelation_isHomogeneous e i₀ j₀ j l hd ha⟩
  change aeval (segreVector e c b) (columnRelation e i₀ j₀ j l d a) = 0
  rw [aeval_columnRelation e i₀ j₀ j l hd ha, hrel, sub_self, mul_zero]

variable [Field F] [Algebra A F]

/-- Full original relations enforce the original linear equation on every nonzero Segre fibre. -/
theorem equation_of_fullRelations (e : L ≃ I × J) (i₀ : I) (j₀ l : J)
    (c : I → K) (b : J → K) (x : I → F) (y : J → F)
    (hx : x i₀ ≠ 0) (hy : y ≠ 0)
    (hz : ∀ p ∈ (relationCore (A := A) (segreVector e c b)).toIdeal,
      aeval (segreVector e x y) p = 0)
    {d a : MvPolynomial I A} {n : ℕ} (hd : d.IsHomogeneous n) (ha : a.IsHomogeneous n)
    (hrel : aeval c d * b l = aeval c a * b j₀) :
    aeval x d * y l = aeval x a * y j₀ := by
  classical
  obtain ⟨j, hj⟩ : ∃ j, y j ≠ 0 := Function.ne_iff.mp hy
  have hzero := hz _ (columnRelation_mem e i₀ j₀ j l hd ha c b hrel)
  rw [aeval_columnRelation e i₀ j₀ j l hd ha] at hzero
  exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left (mul_ne_zero (pow_ne_zero n hj) hx))

/-- Actual denominator values and the full original relations determine the entire projective fibre. -/
theorem coordinates_of_fullRelations (e : L ≃ I × J) (i₀ : I) (j₀ : J)
    (c : I → K) (b : J → K) (x : I → F) (y u : J → F)
    (hx : x i₀ ≠ 0) (hy : y ≠ 0)
    (hz : ∀ p ∈ (relationCore (A := A) (segreVector e c b)).toIdeal,
      aeval (segreVector e x y) p = 0)
    (hrep : ∀ l, ∃ (n : ℕ) (d a : MvPolynomial I A),
      d.IsHomogeneous n ∧ a.IsHomogeneous n ∧
      aeval c d * b l = aeval c a * b j₀ ∧
      aeval x d ≠ 0 ∧ aeval x a = aeval x d * u l) :
    y j₀ ≠ 0 ∧ y = y j₀ • u := by
  have heq (l : J) : y l = y j₀ * u l := by
    obtain ⟨n, d, a, hd, ha, hrel, hden, hval⟩ := hrep l
    have h := equation_of_fullRelations e i₀ j₀ l c b x y hx hy hz hd ha hrel
    rw [hval] at h
    apply mul_left_cancel₀ hden
    calc
      aeval x d * y l = (aeval x d * u l) * y j₀ := h
      _ = aeval x d * (y j₀ * u l) := by ring
  refine ⟨?_, funext heq⟩
  intro hzero
  apply hy
  funext l
  simpa [hzero] using heq l

/-- Actual homogeneous lift at a prescribed sufficiently large common degree. -/
def homogenizeTo (n : ℕ) (p : MvPolynomial I A) : MvPolynomial (Option I) A :=
  homogenize p * X none ^ (n - p.totalDegree)

theorem homogenizeTo_isHomogeneous (n : ℕ) (p : MvPolynomial I A) (hp : p.totalDegree ≤ n) :
    (homogenizeTo n p).IsHomogeneous n := by
  simpa only [homogenizeTo, Nat.add_sub_of_le hp] using
    (isHomogeneous_homogenize p).mul (isHomogeneous_X_pow none (n - p.totalDegree))

theorem aeval_homogenizeTo (n : ℕ) (p : MvPolynomial I A) (x : I → K) :
    aeval (graphCoordinates x) (homogenizeTo n p) = aeval x p := by
  simp only [homogenizeTo, map_mul, map_pow, aeval_X, graphCoordinates, one_pow, mul_one,
    aeval_graphCoordinates, dehomogenize_homogenize]

/-- The same actual homogeneous lift, with its pivot at the original projective coordinate. -/
def baseHomogenize {N : ℕ} (i : Fin (N + 1)) (n : ℕ)
    (p : MvPolynomial (Fin N) A) : MvPolynomial (Fin (N + 1)) A :=
  rename (fun o : Option (Fin N) => o.elim i i.succAbove) (homogenizeTo n p)

theorem baseHomogenize_isHomogeneous {N : ℕ} (i : Fin (N + 1)) (n : ℕ)
    (p : MvPolynomial (Fin N) A) (hp : p.totalDegree ≤ n) :
    (baseHomogenize i n p).IsHomogeneous n :=
  (homogenizeTo_isHomogeneous n p hp).rename_isHomogeneous

/-- Its evaluation in the actual normalized original chart retains the original affine polynomial. -/
theorem aeval_baseHomogenize {N : ℕ} (i : Fin (N + 1)) (n : ℕ)
    (p : MvPolynomial (Fin N) A) (x : Fin (N + 1) → K) (hx : x i = 1) :
    aeval x (baseHomogenize i n p) = aeval (fun k => x (i.succAbove k)) p := by
  rw [baseHomogenize, aeval_rename]
  have heq : (x ∘ fun o : Option (Fin N) => o.elim i i.succAbove) =
      graphCoordinates (fun k => x (i.succAbove k)) := by
    funext o
    cases o <;> simp [graphCoordinates, hx]
  rw [heq, aeval_homogenizeTo]

end SGPT.NAPotential.AlgPrimes3.ProjectiveGraphSeparation
