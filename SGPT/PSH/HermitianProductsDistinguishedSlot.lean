import SGPT.PSH.HermitianProducts

/-!
# The actual distinguished outer Bedford--Taylor slot

The first potential of the recursive product is the outer normalized
Hessian. The existing unconditional induction peeling this slot supplies
the exact `Fin.cons` formula below. Actual simultaneous decreasing PSH
tuples then give weak convergence of the corresponding weighted Hessians
by the ordinary Bedford--Taylor theorem, with no continuity premise.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianProducts

open Set Filter MeasureTheory TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open FirstPass.MongeAmpere LocalProductCurrents LocalBedfordTaylorProducts
  LocalBedfordTaylorCollar LocalBedfordTaylorContinuity LocalBedfordTaylorDecreasing
open scoped Topology Distributions

variable {n : ℕ} {U : Opens (ComplexModel n)}

/-- Degree transport commutes with the actual weighted normalized
Hessian, for arbitrary functions and arbitrary coefficient currents. -/
theorem ddcMul_castLPC {r s : ℕ} (h : r = s)
    (T : LocalProductCurrent n U (r + 1)) (a : ComplexModel n → ℝ) :
    ddcMul (castLPC (congrArg (fun k => k + 1) h) T) a =
      castLPC h (ddcMul T a) := by
  subst h
  rfl

/-- The requested literal distinguished-slot identity. The mother
`btProduct_succ_eq_ddcMul` is the unconditional induction on the actual
last-slot recursion, including its explicit `ddcMul_heq` transport step. -/
theorem ddcMul_btProduct_eq_btProduct_cons (q r : ℕ)
    (T : LocalProductCurrent n U (r + 1 + q))
    (v : Fin q → ComplexModel n → ℝ) (a : ComplexModel n → ℝ) :
    ddcMul (btProduct q (r + 1) v T) a =
      btProduct (q + 1) r (Fin.cons a v)
        (castLPC (by omega : r + 1 + q = r + (q + 1)) T) := by
  have hdegree : r + 1 + q = r + (q + 1) := by omega
  have h := btProduct_succ_eq_ddcMul q r (Fin.cons a v)
    (castLPC hdegree T) T (heq_castLPC hdegree T).symm
  simpa only [Fin.tail_cons, Fin.cons_zero] using h.symm

/-- Actual bounded PSH decreasing approximation of the distinguished
weight and every ordinary slot gives weak convergence of the literal
weighted Hessian current. All analytic continuity is supplied by the
proved ordinary Bedford--Taylor theorem on the assembled genuine tuple. -/
theorem weakTendsto_ddcMul_btProduct_of_antitone (q r : ℕ)
    (T : LocalProductCurrent n U (r + 1 + q)) (hT : IsPositive T)
    (hTc : IsClosedAny (r + 1 + q) T)
    (v : ℕ → Fin q → ComplexModel n → ℝ) (v₀ : Fin q → ComplexModel n → ℝ)
    (a : ℕ → ComplexModel n → ℝ) (a₀ : ComplexModel n → ℝ)
    (hv : ∀ j i, IsLocallyBoundedPshOn U (v j i))
    (hv₀ : ∀ i, IsLocallyBoundedPshOn U (v₀ i))
    (ha : ∀ j, IsLocallyBoundedPshOn U (a j)) (ha₀ : IsLocallyBoundedPshOn U a₀)
    (hanti_v : ∀ i z, z ∈ U → Antitone fun j => v j i z)
    (hlim_v : ∀ i z, z ∈ U → Tendsto (fun j => v j i z) atTop (𝓝 (v₀ i z)))
    (hanti_a : ∀ z, z ∈ U → Antitone fun j => a j z)
    (hlim_a : ∀ z, z ∈ U → Tendsto (fun j => a j z) atTop (𝓝 (a₀ z))) :
    WeakTendsto (fun j => ddcMul (btProduct q (r + 1) (v j) T) (a j))
      (ddcMul (btProduct q (r + 1) v₀ T) a₀) := by
  let w : ℕ → Fin (q + 1) → ComplexModel n → ℝ := fun j => Fin.cons (a j) (v j)
  let w₀ : Fin (q + 1) → ComplexModel n → ℝ := Fin.cons a₀ v₀
  have hw (j : ℕ) (i : Fin (q + 1)) : IsLocallyBoundedPshOn U (w j i) := by
    refine Fin.cases ?_ (fun i => ?_) i
    · simpa only [w, Fin.cons_zero] using ha j
    · simpa only [w, Fin.cons_succ] using hv j i
  have hw₀ (i : Fin (q + 1)) : IsLocallyBoundedPshOn U (w₀ i) := by
    refine Fin.cases ?_ (fun i => ?_) i
    · simpa only [w₀, Fin.cons_zero] using ha₀
    · simpa only [w₀, Fin.cons_succ] using hv₀ i
  have hanti (i : Fin (q + 1)) : ∀ z, z ∈ U → Antitone fun j => w j i z := by
    refine Fin.cases ?_ (fun i => ?_) i
    · simpa only [w, Fin.cons_zero] using hanti_a
    · simpa only [w, Fin.cons_succ] using hanti_v i
  have hlim (i : Fin (q + 1)) :
      ∀ z, z ∈ U → Tendsto (fun j => w j i z) atTop (𝓝 (w₀ i z)) := by
    refine Fin.cases ?_ (fun i => ?_) i
    · simpa only [w, w₀, Fin.cons_zero] using hlim_a
    · simpa only [w, w₀, Fin.cons_succ] using hlim_v i
  have hdegree : r + 1 + q = r + (q + 1) := by omega
  have hconv := weakTendsto_btProduct_of_antitone (q + 1) r (castLPC hdegree T)
    (isPositive_castLPC hdegree hT) (isClosedAny_castLPC hdegree hTc)
    w w₀ hw hw₀ hanti hlim
  simpa only [w, w₀, ← ddcMul_btProduct_eq_btProduct_cons] using hconv

end SGPT.PSH.HermitianProducts
