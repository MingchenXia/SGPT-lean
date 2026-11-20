import SGPT.Foundations.Analysis.Pending.FibrePotentialLevi
import SGPT.Foundations.Analysis.Pending.SlotFormCompactIBP
import Mathlib.GroupTheory.Perm.Fin

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Stokes on `X × X`: `R_α = c [X] ∧ a + ddᶜ v` on the Levi test forms

Source: Demailly--Păun, proof of Theorem 2.12 (`dp04-kahler-cone:2.12`), Boucksom, proof of
Theorem 4.8 (`bou02-volume:4.8`).  TN.4 plan, step B6, finding F6 route (i), piece (i-1)
: for `α = A + ddᶜg` on `X × X` (`A = p₁^*a + p₂^*a`),
`αⁿ - Aⁿ = ddᶜg ∧ Σ_k α^k ∧ A^{n-1-k}`, and two integrations by parts move `ddᶜ` from `g` to the
test form.

## The pointwise telescoping

`actualMixedTopDensity_telescope`: for a fixed family `F` and two-forms `A`, `D`,
`D(F, (A + D)^{s+1}) - D(F, A^{s+1}) = Σ_k D(D, F, (A + D)^k, A^{s-k})` (the `k`-th difference moves
one slot from `A` to `A + D`; the slot `D` is then rotated to the front, `Fin.cycleRange`).
-/

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ContDiff Distributions

namespace SGPT.Foundations.Analysis.Pending.ProductStokesLevi

open FirstPass FirstPass.MongeAmpere FirstPass.PositiveClasses StronglyPositiveForms
  ProductTestForms PositiveProductCurrents IntegrationCurrent TopDegreeDensity
  SmoothCurrentTraceMeasure CurrentTraceMeasure SmoothDDCForm ChartPartition SlotTestForms
  ManifoldTubePositivity DirectionalLeviDensity PositivityLeviLink ClosedProductCurrents
  FibrePotentialLevi VerticalDensityFactorization FibrePushforwardProductForm

/-! ### The pointwise telescoping -/

section Telescope

variable {r s : ℕ}

/-- `(A + D)^k ∧ A^{s-k}` as a family of `s` slots. -/
def teleSlots {N : ℕ} (A D : CoordinateRealTwoForm N) (k : ℕ) (s : ℕ) :
    Fin s → CoordinateRealTwoForm N :=
  fun j => if (j : ℕ) < k then A + D else A

/-- Rotating one slot to the front does not change the mixed density. -/
theorem actualMixedTopDensity_cons_removeNth {N : ℕ}
    (F : Fin (N + 1) → CoordinateRealTwoForm (N + 1)) (p : Fin (N + 1)) :
    actualMixedTopDensity (Fin.cons (F p) (p.removeNth F) : Fin (N + 1) → _) =
      actualMixedTopDensity F := by
  rw [Fin.cons_removeNth_eq_comp_cycleRange_symm]
  exact actualMixedTopDensity_perm F p.cycleRange.symm

theorem removeNth_append_update (Fam : Fin r → CoordinateRealTwoForm (r + (s + 1)))
    (A D : CoordinateRealTwoForm (r + (s + 1))) (k : Fin (s + 1)) :
    (Fin.natAdd r k).removeNth
        (Fin.append Fam (Function.update (teleSlots A D k (s + 1)) k D) :
          Fin (r + (s + 1)) → CoordinateRealTwoForm (r + (s + 1))) =
      Fin.append Fam (teleSlots A D k s) := by
  funext j
  rw [Fin.removeNth_apply]
  refine Fin.addCases (fun i => ?_) (fun j' => ?_) j
  · have hlt : Fin.castSucc (Fin.castAdd s i) < Fin.natAdd r k := by
      rw [Fin.lt_def]
      simp only [Fin.val_castSucc, Fin.val_castAdd, Fin.val_natAdd]
      omega
    rw [Fin.succAbove_of_castSucc_lt _ _ hlt, Fin.append_left]
    have : (Fin.castSucc (Fin.castAdd s i) : Fin (r + (s + 1))) = Fin.castAdd (s + 1) i := by
      ext; simp
    rw [this, Fin.append_left]
  · rw [Fin.append_right]
    by_cases hj : (j' : ℕ) < k
    · have hlt : Fin.castSucc (Fin.natAdd r j') < Fin.natAdd r k := by
        rw [Fin.lt_def]
        simp only [Fin.val_castSucc, Fin.val_natAdd]
        omega
      rw [Fin.succAbove_of_castSucc_lt _ _ hlt]
      have : (Fin.castSucc (Fin.natAdd r j') : Fin (r + (s + 1))) =
          Fin.natAdd r (Fin.castSucc j') := by ext; simp
      rw [this, Fin.append_right, Function.update_of_ne]
      · simp only [teleSlots, Fin.val_castSucc, hj, if_true]
      · intro h
        rw [Fin.ext_iff, Fin.val_castSucc] at h
        omega
    · have hle : Fin.natAdd r k ≤ Fin.castSucc (Fin.natAdd r j') := by
        rw [Fin.le_def]
        simp only [Fin.val_castSucc, Fin.val_natAdd]
        omega
      rw [Fin.succAbove_of_le_castSucc _ _ hle]
      have : (Fin.succ (Fin.natAdd r j') : Fin (r + (s + 1))) = Fin.natAdd r (Fin.succ j') := by
        ext
        simp only [Fin.val_succ, Fin.val_natAdd]
        omega
      rw [this, Fin.append_right, Function.update_of_ne]
      · have h1 : ¬ ((Fin.succ j' : Fin (s + 1)) : ℕ) < k := by
          simp only [Fin.val_succ]
          omega
        simp only [teleSlots, h1, hj, if_false]
      · intro h
        rw [Fin.ext_iff, Fin.val_succ] at h
        omega

/-- **The telescoping identity** for the mixed density. -/
theorem actualMixedTopDensity_telescope (Fam : Fin r → CoordinateRealTwoForm (r + (s + 1)))
    (A D : CoordinateRealTwoForm (r + (s + 1))) :
    actualMixedTopDensity (Fin.append Fam (fun _ : Fin (s + 1) => A + D) :
        Fin (r + (s + 1)) → _) -
      actualMixedTopDensity (Fin.append Fam (fun _ : Fin (s + 1) => A) :
        Fin (r + (s + 1)) → _) =
      ∑ k : Fin (s + 1), actualMixedTopDensity
        (Fin.cons D (Fin.append Fam (teleSlots A D k s)) : Fin (r + (s + 1)) → _) := by
  set F : (Fin (s + 1) → CoordinateRealTwoForm (r + (s + 1))) → ℝ :=
    fun γ => actualMixedTopDensity (Fin.append Fam γ : Fin (r + (s + 1)) → _) with hF
  have h0 : (fun _ : Fin (s + 1) => A) = teleSlots A D 0 (s + 1) := by
    funext j; simp [teleSlots]
  have hs : (fun _ : Fin (s + 1) => A + D) = teleSlots A D (s + 1) (s + 1) := by
    funext j; simp [teleSlots, j.isLt]
  change F _ - F _ = _
  rw [h0, hs, ← Finset.sum_range_sub (fun k => F (teleSlots A D k (s + 1))) (s + 1),
    ← Fin.sum_univ_eq_sum_range (fun k => F (teleSlots A D (k + 1) (s + 1)) -
      F (teleSlots A D k (s + 1)))]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hup1 : teleSlots A D ((k : ℕ) + 1) (s + 1) =
      Function.update (teleSlots A D k (s + 1)) k (A + D) := by
    funext j
    by_cases hjk : j = k
    · subst hjk; simp [teleSlots]
    · rw [Function.update_of_ne hjk]
      have : (j : ℕ) ≠ k := fun h => hjk (Fin.ext h)
      simp only [teleSlots]
      by_cases hj : (j : ℕ) < k
      · simp [hj, show (j : ℕ) < k + 1 by omega]
      · simp [hj, show ¬ (j : ℕ) < k + 1 by omega]
  have hup0 : teleSlots A D k (s + 1) = Function.update (teleSlots A D k (s + 1)) k A := by
    funext j
    by_cases hjk : j = k
    · subst hjk; simp [teleSlots]
    · rw [Function.update_of_ne hjk]
  have hadd : F (Function.update (teleSlots A D k (s + 1)) k (A + D)) =
      F (Function.update (teleSlots A D k (s + 1)) k A) +
        F (Function.update (teleSlots A D k (s + 1)) k D) := by
    simp only [hF, append_update_right]
    exact actualMixedTopDensityMultilinear.map_update_add _ _ _ _
  rw [hup1, hadd, ← hup0, add_sub_cancel_left, hF]
  simp only
  set F'' : Fin (r + (s + 1)) → CoordinateRealTwoForm (r + (s + 1)) :=
    Fin.append Fam (Function.update (teleSlots A D k (s + 1)) k D) with hF''
  have key := actualMixedTopDensity_cons_removeNth (N := r + s) F'' (Fin.natAdd r k)
  have hp : F'' (Fin.natAdd r k) = D := by
    rw [hF'', Fin.append_right, Function.update_self]
  rw [hp, hF'', removeNth_append_update] at key
  exact key.symm

/-- `(x, b, w, t)` read in two bracketings. -/
theorem append_cons_cons {α : Type*} (x w : α) (b : Fin r → α) (t : Fin s → α) :
    (Fin.append (Fin.cons x b) (Fin.cons w t) : Fin ((r + 1) + (s + 1)) → α) =
      (Fin.cons x (Fin.append (Fin.snoc b w) t) : Fin (r + 1 + s + 1) → α) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · have h0 : (0 : Fin (r + 1 + s + 1)) = (Fin.castAdd (s + 1) (0 : Fin (r + 1)) :
        Fin ((r + 1) + (s + 1))) := by ext; simp
    rw [Fin.cons_zero]
    change Fin.append (Fin.cons x b) (Fin.cons w t) (0 : Fin (r + 1 + s + 1)) = x
    rw [h0, Fin.append_left, Fin.cons_zero]
  · rw [Fin.cons_succ]
    refine Fin.addCases (fun j₁ => ?_) (fun j₃ => ?_) j
    · rw [Fin.append_left]
      refine Fin.lastCases ?_ (fun j₂ => ?_) j₁
      · rw [Fin.snoc_last]
        have hi : (Fin.succ (Fin.castAdd s (Fin.last r)) : Fin (r + 1 + s + 1)) =
            (Fin.natAdd (r + 1) (0 : Fin (s + 1)) : Fin ((r + 1) + (s + 1))) := by
          ext; simp
        change Fin.append (Fin.cons x b) (Fin.cons w t)
          (Fin.succ (Fin.castAdd s (Fin.last r)) : Fin (r + 1 + s + 1)) = w
        rw [hi, Fin.append_right, Fin.cons_zero]
      · rw [Fin.snoc_castSucc]
        have hi : (Fin.succ (Fin.castAdd s (Fin.castSucc j₂)) : Fin (r + 1 + s + 1)) =
            (Fin.castAdd (s + 1) (Fin.succ j₂) : Fin ((r + 1) + (s + 1))) := by
          ext; simp
        change Fin.append (Fin.cons x b) (Fin.cons w t)
          (Fin.succ (Fin.castAdd s (Fin.castSucc j₂)) : Fin (r + 1 + s + 1)) = b j₂
        rw [hi, Fin.append_left, Fin.cons_succ]
    · rw [Fin.append_right]
      have hi : (Fin.succ (Fin.natAdd (r + 1) j₃) : Fin (r + 1 + s + 1)) =
          (Fin.natAdd (r + 1) (Fin.succ j₃) : Fin ((r + 1) + (s + 1))) := by
        ext; simp; omega
      change Fin.append (Fin.cons x b) (Fin.cons w t)
        (Fin.succ (Fin.natAdd (r + 1) j₃) : Fin (r + 1 + s + 1)) = t j₃
      rw [hi, Fin.append_right, Fin.cons_succ]

end Telescope

/-! ### `[M]` is closed -/

section Closed

variable {N : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel N) M]
  [IsComplexManifold N M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- The integration current of a compact manifold is closed (Stokes; the smooth current with no
slots, `SmoothCurrentClosedness.isClosedCurrent_smoothCurrent`). -/
theorem isClosedCurrent_integrationCurrent (W : KahlerBackground N M) :
    IsClosedCurrent (integrationCurrent W) :=
  SmoothCurrentClosedness.isClosedCurrent_smoothCurrent (q := N) (p := 0) W Fin.elim0

end Closed

/-! ### The two sides of the Stokes identity on `X × X`, chart by chart -/

section Product

open scoped ProductComplexManifold Manifold
open ProductComplexManifold ProductMixedMeasure DiagonalFibreIntegration

variable {q : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel (q + 1)) X]
  [IsComplexManifold (q + 1) X]

/-- The lifted test function `h = (φ ∘ e) ∘ p₁` on `X × X`. -/
def liftTest (e : ComplexChart (q + 1) X) (φ : 𝓓(chartTarget e, ℝ)) : X × X → ℝ :=
  fun p => chartExtend e φ p.1

theorem chartSmooth_liftTest (e : ComplexChart (q + 1) X) (φ : 𝓓(chartTarget e, ℝ)) :
    ChartSmooth (n := (q + 1) + (q + 1)) (liftTest e φ) :=
  chartSmooth_comp contMDiff_fst (chartSmooth_testFunction e φ)

/-- The fibre family `p₁^*β_a, …, p₁^*β_a, p₂^*ω` (`q + 1` closed slots). -/
def fibreFam (w : KahlerBackground (q + 1) X) (e : ComplexChart (q + 1) X)
    (ψ : 𝓓(chartTarget e, ℝ)) (a : ComplexModel (q + 1)) :
    Fin (q + 1) → ClosedRealOneOneForm ((q + 1) + (q + 1)) (X × X) :=
  Fin.snoc (fun _ : Fin q => ClosedRealOneOneForm.pullback contMDiff_fst (leviSlot e ψ a))
    (ClosedRealOneOneForm.pullback contMDiff_snd w.form)

/-- `α, …, α, A, …, A` (`k` copies of `α`) as closed slots. -/
def teleForms {N : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel N) M]
    [IsComplexManifold N M] (A α : ClosedRealOneOneForm N M) (k s : ℕ) :
    Fin s → ClosedRealOneOneForm N M :=
  fun j => if (j : ℕ) < k then α else A

/-- The test form `p₁^*((φ ∘ e) β_a^q) ∧ p₂^*ω` against which `Θ` is evaluated. -/
def fibreLeviTest (w : KahlerBackground (q + 1) X) (e : ComplexChart (q + 1) X)
    (ψ φ : 𝓓(chartTarget e, ℝ)) (a : ComplexModel (q + 1)) :
    testSpace ((q + 1) + (q + 1)) (X × X) (q + 1) :=
  wedgeTestLM (isTypeOneOne_pullback contMDiff_snd w.form.2.2) q
    (pullbackTestLM contMDiff_fst q (leviTest e ψ a φ))

theorem fibreFam_coeff (w : KahlerBackground (q + 1) X) (e : ComplexChart (q + 1) X)
    (ψ : 𝓓(chartTarget e, ℝ)) (a : ComplexModel (q + 1))
    (E : ComplexChart ((q + 1) + (q + 1)) (X × X)) (z : ComplexModel ((q + 1) + (q + 1))) :
    (fun j => (fibreFam w e ψ a j).val.coeff E z) =
      Fin.snoc (fun _ : Fin q =>
        (SmoothRealForm.pullback contMDiff_fst (leviSlot e ψ a).val).coeff E z)
        ((SmoothRealForm.pullback contMDiff_snd w.form.val).coeff E z) := by
  funext j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · simp [fibreFam]
  · simp [fibreFam]

/-- The coefficient of the fibre test form: `h · p₁^*β_a ∧ ⋯ ∧ p₁^*β_a ∧ p₂^*ω`. -/
theorem fibreLeviTest_coeff (w : KahlerBackground (q + 1) X) (e : ComplexChart (q + 1) X)
    (ψ φ : 𝓓(chartTarget e, ℝ)) (a : ComplexModel (q + 1))
    (E : ComplexChart ((q + 1) + (q + 1)) (X × X)) (z : ComplexModel ((q + 1) + (q + 1))) :
    ((fibreLeviTest w e ψ φ a : testSpace ((q + 1) + (q + 1)) (X × X) (q + 1)) :
        SmoothRealForm ((q + 1) + (q + 1)) (X × X) (2 * (q + 1))).coeff E z =
      liftTest e φ (E.val.symm z) •
        wedgeProd (q + 1) (fun j => (fibreFam w e ψ a j).val.coeff E z) := by
  rw [fibreFam_coeff, fibreLeviTest, coe_fibreTest w.form.2.2, wedgeTwo_coeff]
  have hη : ((leviTest e ψ a φ : testSpace (q + 1) X q) : SmoothRealForm (q + 1) X (2 * q)) =
      smulFun (chartExtend e φ) (chartSmooth_testFunction e φ) (formPow (leviSlot e ψ a).val q) :=
    rfl
  rw [hη, pullback_smulFun, pullback_formPow, smulFun_coeff, formPow_coeff,
    formPower_eq_wedgeProd, coordinateWedge_smul_left, wedgeProd_snoc]
  rfl

/-- The density of `Ψ ∧ γ^{q+1}` at a chart point. -/
theorem topDensity_chain_fibreLeviTest (w : KahlerBackground (q + 1) X)
    (e : ComplexChart (q + 1) X) (ψ φ : 𝓓(chartTarget e, ℝ)) (a : ComplexModel (q + 1))
    (γ : ClosedRealOneOneForm ((q + 1) + (q + 1)) (X × X))
    (E : ComplexChart ((q + 1) + (q + 1)) (X × X)) (z : ComplexModel ((q + 1) + (q + 1))) :
    topDensity (((chainTestLM (q + 1) (fun _ => γ.val) (fun _ => γ.2.2) (q + 1)
        (fibreLeviTest w e ψ φ a) : testSpace ((q + 1) + (q + 1)) (X × X) ((q + 1) + (q + 1))) :
          SmoothRealForm ((q + 1) + (q + 1)) (X × X) (2 * ((q + 1) + (q + 1)))).coeff E z) =
      liftTest e φ (E.val.symm z) * actualMixedTopDensity
        (Fin.append (fun j => (fibreFam w e ψ a j).val.coeff E z)
          (fun _ : Fin (q + 1) => γ.val.coeff E z)) := by
  rw [chainTestLM_coeff_eq, fibreLeviTest_coeff, map_smul, coordChain_wedgeProd, topDensity_smul,
    topDensity_wedgeProd]

/-- The density of the slot form `h ddᶜg ∧ p₁^*β_a^q ∧ p₂^*ω ∧ α^k ∧ A^{q-k}` at a chart point. -/
theorem topDensity_slot_fibre (w : KahlerBackground (q + 1) X) (e : ComplexChart (q + 1) X)
    (ψ φ : 𝓓(chartTarget e, ℝ)) (a : ComplexModel (q + 1))
    (A : ClosedRealOneOneForm ((q + 1) + (q + 1)) (X × X)) {g : X × X → ℝ}
    (hg : ChartSmooth (n := (q + 1) + (q + 1)) g) (k : ℕ)
    (E : ComplexChart ((q + 1) + (q + 1)) (X × X)) {z : ComplexModel ((q + 1) + (q + 1))}
    (hz : z ∈ E.val.target) :
    topDensity (((slotForm (smulFun (liftTest e φ) (chartSmooth_liftTest e φ) (ddcForm g hg))
        (q + 1 + q) (Fin.append (fibreFam w e ψ a) (teleForms A (A + ddcClosedForm g hg) k q)) :
          testSpace ((q + 1) + (q + 1)) (X × X) ((q + 1) + (q + 1))) :
            SmoothRealForm ((q + 1) + (q + 1)) (X × X) (2 * ((q + 1) + (q + 1)))).coeff E z) =
      liftTest e φ (E.val.symm z) * actualMixedTopDensity
        (Fin.cons (smoothDDC (fun y => g (E.val.symm y)) z)
          (Fin.append (fun j => (fibreFam w e ψ a j).val.coeff E z)
            (teleSlots (A.val.coeff E z) (smoothDDC (fun y => g (E.val.symm y)) z) k q)) :
          Fin ((q + 1) + (q + 1)) → RealForm ((q + 1) + (q + 1)) 2) := by
  set D := smoothDDC (fun y => g (E.val.symm y)) z with hD
  have hg2 : ContDiffAt ℝ 2 (fun y => g (E.val.symm y)) z :=
    ((hg E).contDiffAt (E.val.open_target.mem_nhds hz)).of_le (WithTop.coe_le_coe.mpr le_top)
  have hslots : (fun j => (Fin.append (fibreFam w e ψ a)
      (teleForms A (A + ddcClosedForm g hg) k q) j).val.coeff E z) =
      Fin.append (fun j => (fibreFam w e ψ a j).val.coeff E z)
        (teleSlots (A.val.coeff E z) D k q) := by
    funext j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simp only [Fin.append_left]
    · simp only [Fin.append_right, teleForms, teleSlots]
      split_ifs
      · rw [ClosedRealOneOneForm.coeff_add, hD]
        rfl
      · rfl
  have hfirst : pi11 ((smulFun (liftTest e φ) (chartSmooth_liftTest e φ) (ddcForm g hg)).coeff E z) =
      liftTest e φ (E.val.symm z) • D := by
    rw [smulFun_coeff, pi11_smul, ddcForm_coeff, ← hD, pi11_eq_self (MongeAmpere.smoothDDC_isOneOne hg2)]
  rw [slotForm_coeff, hfirst, hslots]
  change topDensity (wedgeProd ((q + 1) + (q + 1)) (Fin.cons (liftTest e φ (E.val.symm z) • D)
    (Fin.append (fun j => (fibreFam w e ψ a j).val.coeff E z)
      (teleSlots (A.val.coeff E z) D k q)))) = _
  rw [topDensity_wedgeProd]
  have hupd : (Fin.cons (liftTest e φ (E.val.symm z) • D)
      (Fin.append (fun j => (fibreFam w e ψ a j).val.coeff E z) (teleSlots (A.val.coeff E z) D k q)) :
        Fin ((q + 1) + (q + 1)) → RealForm ((q + 1) + (q + 1)) 2) =
      Function.update (Fin.cons D (Fin.append (fun j => (fibreFam w e ψ a j).val.coeff E z)
        (teleSlots (A.val.coeff E z) D k q))) 0 (liftTest e φ (E.val.symm z) • D) := by
    rw [Fin.update_cons_zero]
  rw [hupd, ← actualMixedTopDensityMultilinear_apply, MultilinearMap.map_update_smul,
    Fin.update_cons_zero, smul_eq_mul, actualMixedTopDensityMultilinear_apply]

variable [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

/-- **Telescoping on `X × X`**: for `α = A + ddᶜg`,
`[X × X] ∧ α^{q+1} (Ψ) - [X × X] ∧ A^{q+1} (Ψ) = Σ_k [X × X](h ddᶜg ∧ p₁^*β_a^q ∧ p₂^*ω ∧ α^k ∧ A^{q-k})`
on the fibre test form `Ψ = p₁^*((φ ∘ e) β_a^q) ∧ p₂^*ω`, `h = φ ∘ e ∘ p₁`. -/
theorem smoothCurrent_sub_eq_sum_slot (w : KahlerBackground (q + 1) X)
    (A : ClosedRealOneOneForm ((q + 1) + (q + 1)) (X × X)) {g : X × X → ℝ}
    (hg : ChartSmooth (n := (q + 1) + (q + 1)) g) (e : ComplexChart (q + 1) X)
    (ψ φ : 𝓓(chartTarget e, ℝ)) (a : ComplexModel (q + 1)) :
    smoothCurrent (q := q + 1) (p := q + 1) (prodKahlerBackground w w)
        (fun _ => A + ddcClosedForm g hg) (fibreLeviTest w e ψ φ a) -
      smoothCurrent (q := q + 1) (p := q + 1) (prodKahlerBackground w w) (fun _ => A)
        (fibreLeviTest w e ψ φ a) =
      ∑ k : Fin (q + 1), integrationCurrent (prodKahlerBackground w w)
        (slotForm (smulFun (liftTest e φ) (chartSmooth_liftTest e φ) (ddcForm g hg)) (q + 1 + q)
          (Fin.append (fibreFam w e ψ a) (teleForms A (A + ddcClosedForm g hg) k q))) := by
  set W := prodKahlerBackground w w
  rw [smoothCurrent_apply, smoothCurrent_apply, integrationCurrent_apply, integrationCurrent_apply,
    ← integral_sub (integrable_topRatio _ _) (integrable_topRatio _ _)]
  simp only [integrationCurrent_apply]
  rw [← integral_finsetSum _ fun k _ => integrable_topRatio _ _]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  simp only [topRatio, chartRatio]
  set E := complexChartAt (n := (q + 1) + (q + 1)) p
  have hz : E.val p ∈ E.val.target := E.val.map_source (mem_complexChartAt_source p)
  rw [← sub_div, ← Finset.sum_div, topDensity_chain_fibreLeviTest,
    topDensity_chain_fibreLeviTest]
  congr 1
  simp_rw [topDensity_slot_fibre w e ψ φ a A hg _ E hz]
  rw [← mul_sub, ← Finset.mul_sum]
  congr 1
  have hα : (A + ddcClosedForm g hg).val.coeff E (E.val p) =
      A.val.coeff E (E.val p) + smoothDDC (fun y => g (E.val.symm y)) (E.val p) := by
    rw [ClosedRealOneOneForm.coeff_add]
    rfl
  rw [hα]
  exact actualMixedTopDensity_telescope _ _ _

/-- In a product chart, `ddᶜ h = p₁^* ddᶜ(φ ∘ e)`. -/
theorem smoothDDC_liftTest (e : ComplexChart (q + 1) X) (φ : 𝓓(chartTarget e, ℝ))
    (e₁ e₂ : ComplexChart (q + 1) X) {z₁ z₂ : ComplexModel (q + 1)} (hz₁ : z₁ ∈ e₁.val.target) :
    smoothDDC (fun y => liftTest e φ ((prodComplexChart e₁ e₂).val.symm y))
        (prodModelEquiv (q + 1) (q + 1) (z₁, z₂)) =
      ((ddcTest e φ).val.coeff e₁ z₁).compContinuousLinearMap (projFst (q + 1) (q + 1)) := by
  set ρ : ComplexModel (q + 1) → ℝ := fun y₁ => chartExtend e φ (e₁.val.symm y₁) with hρ
  have hfun : (fun y => liftTest e φ ((prodComplexChart e₁ e₂).val.symm y)) =
      fun y => ρ (projFst (q + 1) (q + 1) y) := rfl
  have hF : ContDiff ℂ ∞ (projFst (q + 1) (q + 1) : ComplexModel ((q + 1) + (q + 1)) →
      ComplexModel (q + 1)) :=
    ((ContinuousLinearMap.fst ℂ (ComplexModel (q + 1)) (ComplexModel (q + 1))).comp
      ((prodModelEquiv (q + 1) (q + 1)).symm :
        ComplexModel ((q + 1) + (q + 1)) →L[ℂ] _)).contDiff
  have hproj : projFst (q + 1) (q + 1) (prodModelEquiv (q + 1) (q + 1) (z₁, z₂)) = z₁ := by
    simp [projFst_apply]
  have hU : IsOpen ((projFst (q + 1) (q + 1)) ⁻¹' e₁.val.target) :=
    e₁.val.open_target.preimage (projFst (q + 1) (q + 1)).continuous
  rw [hfun, HolomorphicDDC.smoothDDC_comp hU e₁.val.open_target hF.contDiffOn
    (chartSmooth_testFunction e φ e₁) (fun y hy => hy) (by simpa [hproj] using hz₁), hproj,
    ContinuousLinearMap.fderiv]
  rfl

/-- `p₂^*ω, α, …, α, A, …, A` (`k` copies of `α`): the vertical slots of the `k`-th term. -/
def vertSlots (w : KahlerBackground (q + 1) X)
    (A α : ClosedRealOneOneForm ((q + 1) + (q + 1)) (X × X)) (k : ℕ) :
    Fin (q + 1) → ClosedRealOneOneForm ((q + 1) + (q + 1)) (X × X) :=
  Fin.cons (ClosedRealOneOneForm.pullback contMDiff_snd w.form) (teleForms A α k q)

theorem map_cons_comp {k l N : ℕ} (x : CoordinateRealTwoForm k) (b : Fin N → CoordinateRealTwoForm k)
    (L : ComplexModel l →L[ℝ] ComplexModel k) :
    (fun i => ((Fin.cons x b : Fin (N + 1) → CoordinateRealTwoForm k) i).compContinuousLinearMap L) =
      Fin.cons (x.compContinuousLinearMap L) (fun i => (b i).compContinuousLinearMap L) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

/-- **The integration by parts output is the Fubini form**: on `X × X`,
`[X × X](g ddᶜh ∧ p₁^*β_a^q ∧ p₂^*ω ∧ α^k ∧ A^{q-k}) = [X × X](g · p₁^*(ddᶜ(φ ∘ e) ∧ β_a^q) ∧ p₂^*ω ∧ α^k ∧ A^{q-k})`. -/
theorem integrationCurrent_slot_ibp_eq_chain
    (w : KahlerBackground (q + 1) X) (A α : ClosedRealOneOneForm ((q + 1) + (q + 1)) (X × X))
    {g : X × X → ℝ} (hg : ChartSmooth (n := (q + 1) + (q + 1)) g) (e : ComplexChart (q + 1) X)
    (ψ φ : 𝓓(chartTarget e, ℝ)) (a : ComplexModel (q + 1)) (k : ℕ) :
    integrationCurrent (prodKahlerBackground w w)
        (slotForm (smulFun g hg (ddcForm (liftTest e φ) (chartSmooth_liftTest e φ))) (q + 1 + q)
          (Fin.append (fibreFam w e ψ a) (teleForms A α k q))) =
      integrationCurrent (prodKahlerBackground w w)
        (chainTestLM (q + 1) (fun j => (vertSlots w A α k j).val) (fun j => (vertSlots w A α k j).2.2)
          (q + 1) (smulTest g hg (pullbackTestLM contMDiff_fst (q + 1) (leviDDCTest e ψ φ a)))) := by
  rw [integrationCurrent_apply, integrationCurrent_apply]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  obtain ⟨x, y⟩ := p
  simp only [topRatio, chartRatio]
  set e₁ := complexChartAt (n := q + 1) x
  set e₂ := complexChartAt (n := q + 1) y
  have hz₁ : e₁.val x ∈ e₁.val.target := e₁.val.map_source (mem_complexChartAt_source x)
  have hz₂ : e₂.val y ∈ e₂.val.target := e₂.val.map_source (mem_complexChartAt_source y)
  have hE : complexChartAt (n := (q + 1) + (q + 1)) (x, y) = prodComplexChart e₁ e₂ := rfl
  have hEx : (prodComplexChart e₁ e₂).val (x, y) =
      prodModelEquiv (q + 1) (q + 1) (e₁.val x, e₂.val y) := rfl
  have hsrc : (x, y) ∈ (prodComplexChart e₁ e₂).val.source :=
    hE ▸ mem_complexChartAt_source (x, y)
  have hpt := mem_prodComplexChart_target (e := e₁) (e' := e₂) hz₁ hz₂
  have hg' : g ((prodComplexChart e₁ e₂).val.symm
      (prodModelEquiv (q + 1) (q + 1) (e₁.val x, e₂.val y))) = g (x, y) := by
    rw [← hEx, (prodComplexChart e₁ e₂).val.left_inv hsrc]
  rw [hE, hEx]
  congr 1
  -- the two coefficients
  set z := prodModelEquiv (q + 1) (q + 1) (e₁.val x, e₂.val y)
  set Dφ := (ddcTest e φ).val.coeff e₁ (e₁.val x)
  set B := (leviSlot e ψ a).val.coeff e₁ (e₁.val x)
  set W := w.form.val.coeff e₂ (e₂.val y)
  set T := fun j : Fin q => (teleForms A α k q j).val.coeff (prodComplexChart e₁ e₂) z
  have hφ2 : ContDiffAt ℝ 2 (fun y₁ => chartExtend e φ (e₁.val.symm y₁)) (e₁.val x) :=
    ((chartSmooth_testFunction e φ e₁).contDiffAt (e₁.val.open_target.mem_nhds hz₁)).of_le
      (WithTop.coe_le_coe.mpr le_top)
  have hDφ : IsOneOne Dφ := MongeAmpere.smoothDDC_isOneOne hφ2
  have hfam : (fun j => (fibreFam w e ψ a j).val.coeff (prodComplexChart e₁ e₂) z) =
      Fin.snoc (fun _ : Fin q => B.compContinuousLinearMap (projFst (q + 1) (q + 1)))
        (W.compContinuousLinearMap (projSnd (q + 1) (q + 1))) := by
    rw [fibreFam_coeff, pullback_fst_coeff _ e₁ e₂ hz₁ hz₂, pullback_snd_coeff _ e₁ e₂ hz₁ hz₂]
  have hvert : (fun j => (vertSlots w A α k j).val.coeff (prodComplexChart e₁ e₂) z) =
      Fin.cons (W.compContinuousLinearMap (projSnd (q + 1) (q + 1))) T := by
    funext j
    refine Fin.cases ?_ (fun j => ?_) j
    · simp only [vertSlots, Fin.cons_zero, ClosedRealOneOneForm.pullback_val]
      exact pullback_snd_coeff _ e₁ e₂ hz₁ hz₂
    · simp only [vertSlots, Fin.cons_succ, T]
  -- left side
  have hL : topDensity (((slotForm (smulFun g hg (ddcForm (liftTest e φ) (chartSmooth_liftTest e φ)))
      (q + 1 + q) (Fin.append (fibreFam w e ψ a) (teleForms A α k q)) :
        testSpace ((q + 1) + (q + 1)) (X × X) ((q + 1) + (q + 1))) :
          SmoothRealForm ((q + 1) + (q + 1)) (X × X) (2 * ((q + 1) + (q + 1)))).coeff
            (prodComplexChart e₁ e₂) z) =
      g (x, y) * actualMixedTopDensity (Fin.cons (Dφ.compContinuousLinearMap (projFst (q + 1) (q + 1)))
        (Fin.append (Fin.snoc (fun _ : Fin q => B.compContinuousLinearMap (projFst (q + 1) (q + 1)))
          (W.compContinuousLinearMap (projSnd (q + 1) (q + 1)))) T) :
            Fin ((q + 1) + (q + 1)) → RealForm ((q + 1) + (q + 1)) 2) := by
    have hslots : (fun j => (Fin.append (fibreFam w e ψ a) (teleForms A α k q) j).val.coeff
        (prodComplexChart e₁ e₂) z) =
        Fin.append (Fin.snoc (fun _ : Fin q => B.compContinuousLinearMap (projFst (q + 1) (q + 1)))
          (W.compContinuousLinearMap (projSnd (q + 1) (q + 1)))) T := by
      rw [← hfam]
      funext j
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · simp only [Fin.append_left]
      · simp only [Fin.append_right, T]
    have hfirst : pi11 ((smulFun g hg (ddcForm (liftTest e φ) (chartSmooth_liftTest e φ))).coeff
        (prodComplexChart e₁ e₂) z) =
        g (x, y) • Dφ.compContinuousLinearMap (projFst (q + 1) (q + 1)) := by
      rw [smulFun_coeff, hg', pi11_smul, ddcForm_coeff, smoothDDC_liftTest e φ e₁ e₂ hz₁,
        pi11_eq_self (isOneOne_comp_projFst hDφ)]
    rw [slotForm_coeff, hfirst, hslots]
    change topDensity (wedgeProd ((q + 1) + (q + 1)) (Fin.cons
      (g (x, y) • Dφ.compContinuousLinearMap (projFst (q + 1) (q + 1)))
      (Fin.append (Fin.snoc (fun _ : Fin q => B.compContinuousLinearMap (projFst (q + 1) (q + 1)))
        (W.compContinuousLinearMap (projSnd (q + 1) (q + 1)))) T))) = _
    rw [topDensity_wedgeProd, ← Fin.update_cons_zero (Dφ.compContinuousLinearMap (projFst (q + 1) (q + 1))),
      ← actualMixedTopDensityMultilinear_apply, MultilinearMap.map_update_smul,
      Fin.update_cons_zero, smul_eq_mul, actualMixedTopDensityMultilinear_apply]
  -- right side
  have hR : topDensity (((chainTestLM (q + 1) (fun j => (vertSlots w A α k j).val)
      (fun j => (vertSlots w A α k j).2.2) (q + 1)
        (smulTest g hg (pullbackTestLM contMDiff_fst (q + 1) (leviDDCTest e ψ φ a))) :
          testSpace ((q + 1) + (q + 1)) (X × X) ((q + 1) + (q + 1))) :
            SmoothRealForm ((q + 1) + (q + 1)) (X × X) (2 * ((q + 1) + (q + 1)))).coeff
              (prodComplexChart e₁ e₂) z) =
      g (x, y) * actualMixedTopDensity (Fin.append
        (Fin.cons (Dφ.compContinuousLinearMap (projFst (q + 1) (q + 1)))
          (fun _ : Fin q => B.compContinuousLinearMap (projFst (q + 1) (q + 1))))
        (Fin.cons (W.compContinuousLinearMap (projSnd (q + 1) (q + 1))) T)) := by
    rw [coeff_chain_pullback _ _ g hg e₁ e₂ hz₁ hz₂, hg', topDensity_smul, hvert]
    have hΛ : ((leviDDCTest e ψ φ a : testSpace (q + 1) X (q + 1)) :
        SmoothRealForm (q + 1) X (2 * (q + 1))).coeff e₁ (e₁.val x) =
        wedgeProd (q + 1) (Fin.cons Dφ fun _ : Fin q => B) := by
      rw [leviDDCTest, slotForm_coeff, pi11_eq_self hDφ]
    rw [hΛ, wedgeProd_compContinuousLinearMap, map_cons_comp, coordChain_wedgeProd,
      topDensity_wedgeProd]
  rw [hL, hR, append_cons_cons]

/-! ### The `ε`-level Levi identity -/

/-- **The fibre potential of `R_α`**: `v = Σ_k v_k`, `v_k` the fibre potential of `g` against the
vertical slots `p₂^*ω, α^k, A^{q-k}`. -/
def fibreV (w : KahlerBackground (q + 1) X) (A α : ClosedRealOneOneForm ((q + 1) + (q + 1)) (X × X))
    (g : X × X → ℝ) (x : X) : ℝ :=
  ∑ k : Fin (q + 1), fibrePotential w w (vertSlots w A α k) g x

theorem continuous_fibreV (w : KahlerBackground (q + 1) X)
    (A α : ClosedRealOneOneForm ((q + 1) + (q + 1)) (X × X)) {g : X × X → ℝ} (hg : Continuous g) :
    Continuous (fibreV w A α g) :=
  continuous_finsetSum _ fun _ _ => continuous_fibrePotential w w _ hg

theorem locallyIntegrableOn_fibreV (w : KahlerBackground (q + 1) X)
    (A α : ClosedRealOneOneForm ((q + 1) + (q + 1)) (X × X)) {g : X × X → ℝ} (hg : Continuous g)
    (e : ComplexChart (q + 1) X) :
    LocallyIntegrableOn (fun z => fibreV w A α g (e.val.symm z)) (chartTarget e) volume :=
  ((continuous_fibreV w A α hg).comp_continuousOn e.val.continuousOn_symm).locallyIntegrableOn
    (chartTarget e).isOpen.measurableSet

/-- `[X] ∧ (c θ) = c [X] ∧ θ` on test forms. -/
theorem smoothCurrent_smul_apply (w : KahlerBackground (q + 1) X) (c : ℝ)
    (θ : ClosedRealOneOneForm (q + 1) X) (η : testSpace (q + 1) X q) :
    smoothCurrent (q := q) (p := 1) w ![c • θ] η = c * smoothCurrent (q := q) (p := 1) w ![θ] η := by
  have h : chainTestLM 1 (fun j => (![c • θ] j).val) (fun j => (![c • θ] j).2.2) q η =
      c • chainTestLM 1 (fun j => (![θ] j).val) (fun j => (![θ] j).2.2) q η := by
    apply Subtype.ext
    apply smoothRealForm_ext
    intro e z
    change coordinateWedge ((η : SmoothRealForm (q + 1) X (2 * q)).coeff e z)
        ((c • θ).val.coeff e z) =
      c • coordinateWedge ((η : SmoothRealForm (q + 1) X (2 * q)).coeff e z) (θ.val.coeff e z)
    rw [ClosedRealOneOneForm.coeff_smul, coordinateWedge_smul_right]
  rw [smoothCurrent_apply, smoothCurrent_apply, h, map_smul, smul_eq_mul]

/-- **The `ε`-level Levi identity (step (i-1) of F6)**: for a closed real `(1,1)`-form `b` on `X` and
a chart-smooth `g` on `X × X`, the current `R = p₁_*([X × X] ∧ (p₁^*b + p₂^*b + ddᶜg)^{q+1} ∧ p₂^*ω)`
satisfies `R = c · b + ddᶜ v` on the Levi test forms, with `c = (q + 1) ∫_X b^q ∧ ω` and the
continuous fibre potential `v = fibreV`.  No positivity is assumed. -/
theorem leviTestIdentity_fibrePushforward (w : KahlerBackground (q + 1) X)
    (b : ClosedRealOneOneForm (q + 1) X) {g : X × X → ℝ}
    (hg : ChartSmooth (n := (q + 1) + (q + 1)) g) :
    LeviTestIdentity w
      (fibrePushforward w.form.2.2 (smoothCurrent (q := q + 1) (p := q + 1)
        (prodKahlerBackground w w) (fun _ => prodForm b b + ddcClosedForm g hg)))
      ((((q + 1 : ℕ) : ℝ) * fibreIntegral w b w.form.val) • b)
      (fun e => regularDistribution volume
        (fun z => fibreV w (prodForm b b) (prodForm b b + ddcClosedForm g hg) g (e.val.symm z))
        (locallyIntegrableOn_fibreV w _ _ (ChartSmooth.continuous hg) e)) := by
  intro e ψ φ a ha hφ hψ
  set A := prodForm b b with hAdef
  set α := A + ddcClosedForm g hg with hαdef
  set W := prodKahlerBackground w w with hWdef
  have hgc : Continuous g := ChartSmooth.continuous hg
  -- `R(η) = Θ_α(Ψ)` and `Θ_A(Ψ) = c [X] ∧ b (η)`
  have hR : fibrePushforward w.form.2.2 (smoothCurrent (q := q + 1) (p := q + 1) W (fun _ => α))
      (leviTest e ψ a φ) = smoothCurrent (q := q + 1) (p := q + 1) W (fun _ => α)
        (fibreLeviTest w e ψ φ a) := rfl
  have hA : smoothCurrent (q := q + 1) (p := q + 1) W (fun _ => A) (fibreLeviTest w e ψ φ a) =
      (((q + 1 : ℕ) : ℝ) * fibreIntegral w b w.form.val) *
        smoothCurrent (q := q) (p := 1) w ![b] (leviTest e ψ a φ) := by
    have h := congrArg (fun T => T (leviTest e ψ a φ))
      (fibrePushforward_smoothCurrent_prodForm w w b b w.form.2.2)
    simp only [LinearMap.smul_apply, smul_eq_mul] at h
    exact h
  -- telescoping, integration by parts, Fubini
  have htel := smoothCurrent_sub_eq_sum_slot w A hg e ψ φ a
  have hterm : ∀ k : Fin (q + 1), integrationCurrent W
      (slotForm (smulFun (liftTest e φ) (chartSmooth_liftTest e φ) (ddcForm g hg)) (q + 1 + q)
        (Fin.append (fibreFam w e ψ a) (teleForms A α k q))) =
      ∫ x, fibrePotential w w (vertSlots w A α k) g x *
        topRatio w.form.val ((leviDDCTest e ψ φ a : testSpace (q + 1) X (q + 1)) :
          SmoothRealForm (q + 1) X (2 * (q + 1))) x ∂(kahlerVolume w) := by
    intro k
    rw [SlotFormCompactIBP.slotForm_ibp_of_compact (n := (q + 1) + (q + 1)) (M := X × X)
      (T := integrationCurrent W) (k := q + 1 + q)
      (isPositive_integrationCurrent W) (isClosedCurrent_integrationCurrent W) _
      (chartSmooth_liftTest e φ) hg, integrationCurrent_slot_ibp_eq_chain,
      integrationCurrent_chain_pullback]
  have hsum : ∑ k : Fin (q + 1), ∫ x, fibrePotential w w (vertSlots w A α k) g x *
      topRatio w.form.val ((leviDDCTest e ψ φ a : testSpace (q + 1) X (q + 1)) :
        SmoothRealForm (q + 1) X (2 * (q + 1))) x ∂(kahlerVolume w) =
      ∫ x, fibreV w A α g x * topRatio w.form.val ((leviDDCTest e ψ φ a :
        testSpace (q + 1) X (q + 1)) : SmoothRealForm (q + 1) X (2 * (q + 1))) x
          ∂(kahlerVolume w) := by
    rw [← integral_finsetSum]
    · refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only [fibreV, Finset.sum_mul]
    · intro k _
      exact ((continuous_fibrePotential w w _ hgc).mul
        (continuous_topRatio w.isKahler.1 _)).integrable_of_hasCompactSupport
          (isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (subset_univ _))
  have hchart := integral_mul_topRatio_leviDDCTest w ha hψ (continuous_fibreV w A α hgc)
    (locallyIntegrableOn_fibreV w A α hgc e)
  rw [hR, smoothCurrent_smul_apply, ← hA, ← hchart, ← hsum, ← Finset.sum_congr rfl
    (fun k _ => hterm k), ← htel]
  ring

/-- **The `ε`-level link**: if `α = p₁^*b + p₂^*b + ddᶜg ≥ 0` and `θ = c · b` has smooth local
potentials, the chart distributions of the fibre potential are locally `θ`-psh (`c` the fibre constant
of `leviTestIdentity_fibrePushforward`). -/
theorem isLocallyThetaPshDistribution_fibreV (w : KahlerBackground (q + 1) X)
    (b : ClosedRealOneOneForm (q + 1) X) {g : X × X → ℝ}
    (hg : ChartSmooth (n := (q + 1) + (q + 1)) g)
    (hα : ThetaPlurisubharmonic (prodForm b b + ddcClosedForm g hg).val (fun _ => 0))
    (hθ : HasSmoothLocalPotentials ((((q + 1 : ℕ) : ℝ) * fibreIntegral w b w.form.val) • b).val)
    (e : ComplexChart (q + 1) X) :
    ThetaPshChartLimitGluing.IsLocallyThetaPshDistribution volume
      ((((q + 1 : ℕ) : ℝ) * fibreIntegral w b w.form.val) • b).val e
      (regularDistribution volume
        (fun z => fibreV w (prodForm b b) (prodForm b b + ddcClosedForm g hg) g (e.val.symm z))
        (locallyIntegrableOn_fibreV w _ _ (ChartSmooth.continuous hg) e)) := by
  have hΘ : IsPositive (smoothCurrent (q := q + 1) (p := q + 1) (prodKahlerBackground w w)
      (fun _ => prodForm b b + ddcClosedForm g hg)) :=
    isPositive_smoothCurrent _ _ fun _ => hα
  have hP := IsPositive.fibrePushforward w.form.2.2
    (fun e' z hz => isSemipositiveOneOne_of_isHermitian w.isKahler.1 e' hz) hΘ
  exact isLocallyThetaPshDistribution_of_leviTest w hP _ hθ _
    (leviTestIdentity_fibrePushforward w b hg) e

end Product

end SGPT.Foundations.Analysis.Pending.ProductStokesLevi
