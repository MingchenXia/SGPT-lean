import SGPT.Unibranch.KS2KahlerSpace
import SGPT.Foundations.Analysis.Pending.LeviFormHolomorphicComp
import SGPT.Foundations.Analysis.Pending.ConcentrationPotentialLevi

/-!
# The local positivity estimate behind the Kähler form of a finite map

Analytic core of the construction of a Kähler form on the normalization `Ỹ` (footnote of
`def:traceop`; [GK20, Prop. 3.6], Varouchas). In a local embedding `V ↪ T ⊆ ℂ^N` of `Ỹ` near a
point `b`, the normalization map is induced by a holomorphic `P : T → ℂ^n` (a chart of `X`), the
Kähler form of `X` is a strictly positive form `w` on the chart, and the glued potential is

  `R(z) = χ₀(P z) ‖z‖² + Σ_a χ_a(P z) ‖G_a z‖²`

with cutoffs `χ ≥ 0` pulled back from `X`, `χ₀(P b) > 0`, and `G_a` holomorphic.

* `leviForm_cutoff_mul_normSq`: in a direction `u` with `dP u = 0`, the Levi form of
  `χ(P z) ‖G z‖²` is `χ(P z) ‖dG u‖²` (the cutoff is constant along the fibre directions).
* `leviForm_potential_pos_of_fderiv_eq_zero`: hence the Levi form of `R` at `b` is positive on
  `ker dP_b \ {0}`.
* `exists_isStrictlyPositive_near`: **for one `B₀` and one open `U ∋ b`, the form
  `ddᶜ R + B · P^*w` is strictly positive on `U` for every `B ≥ B₀`** (the uniform tube estimate
  `UniformTubePositivity.exists_forall_isStrictlyPositive_add_smul_of_pos_on_null_familyOn`).
* `extDeriv_pullback_add_ddc`, `isOneOne_pullback_add_ddc`: the form `P^*w + ddᶜ R` is closed and
  of type `(1,1)` when `w` is.

Blueprint: `blueprint/src/KS2.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter
open scoped Topology ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.PositivityPerturbation

namespace SGPT.Unibranch.KS2LeviEstimate

private theorem two_le_infty : ((2 : ℕ) : WithTop ℕ∞) ≤ ∞ :=
  ENat.natCast_le_of_coe_top_le_withTop le_rfl 2

/-- In a direction killed by `dP`, the Levi form of `χ(P z) ‖G z‖²` is `χ(P z) ‖dG u‖²`. -/
theorem leviForm_cutoff_mul_normSq {N n m : ℕ} {T : Set (ComplexModel N)} (hT : IsOpen T)
    {O : Set (ComplexModel n)} (hO : IsOpen O) {P : ComplexModel N → ComplexModel n}
    (hP : ContDiffOn ℂ ∞ P T) (hPO : MapsTo P T O) {χ : ComplexModel n → ℝ}
    (hχ : ContDiffOn ℝ ∞ χ O) {G : ComplexModel N → ComplexModel m} (hG : ContDiffOn ℂ ∞ G T)
    {z : ComplexModel N} (hz : z ∈ T) {u : ComplexModel N} (hu : fderiv ℝ P z u = 0) :
    leviForm (fun w => χ (P w) * ‖G w‖ ^ 2) z u = χ (P z) * ‖fderiv ℝ G z u‖ ^ 2 := by
  have hPz : DifferentiableAt ℂ P z :=
    (hP.differentiableOn (by simp)).differentiableAt (hT.mem_nhds hz)
  have hf2 : ContDiffAt ℝ 2 (fun w => χ (P w)) z :=
    ((hχ.comp (hP.restrict_scalars ℝ) hPO).contDiffAt (hT.mem_nhds hz)).of_le two_le_infty
  have hh2 : ContDiffAt ℝ 2 (fun w => ‖G w‖ ^ 2) z :=
    (((contDiff_norm_sq ℝ).comp_contDiffOn (hG.restrict_scalars ℝ)).contDiffAt
      (hT.mem_nhds hz)).of_le two_le_infty
  rw [Pending.ConcentrationPotentialLevi.leviForm_mul hf2 hh2]
  have hL1 : leviForm (fun w => χ (P w)) z u = 0 := by
    rw [Pending.LeviFormHolomorphicComp.leviForm_comp hT hO hP hχ hPO hz u, hu, leviForm_zero]
  have hL2 : leviForm (fun w => ‖G w‖ ^ 2) z u = ‖fderiv ℝ G z u‖ ^ 2 := by
    rw [Pending.LeviFormHolomorphicComp.leviForm_comp hT isOpen_univ hG
      (contDiff_norm_sq ℝ).contDiffOn (mapsTo_univ _ _) hz u, leviForm_norm_sq]
  have hχd : DifferentiableAt ℝ χ (P z) :=
    (hχ.contDiffAt (hO.mem_nhds (hPO hz))).differentiableAt (by simp)
  have hPr : DifferentiableAt ℝ P z := hPz.restrictScalars ℝ
  have hlin : fderiv ℝ P z (Complex.I • u) = Complex.I • fderiv ℝ P z u := by
    rw [hPz.fderiv_restrictScalars ℝ]
    exact (fderiv ℂ P z).map_smul Complex.I u
  have hcomp : fderiv ℝ (fun w => χ (P w)) z = (fderiv ℝ χ (P z)).comp (fderiv ℝ P z) :=
    fderiv_comp z hχd hPr
  have hD1 : fderiv ℝ (fun w => χ (P w)) z u = 0 := by
    rw [hcomp, ContinuousLinearMap.comp_apply, hu, map_zero]
  have hD2 : fderiv ℝ (fun w => χ (P w)) z (Complex.I • u) = 0 := by
    rw [hcomp, ContinuousLinearMap.comp_apply, hlin, hu, smul_zero, map_zero]
  rw [hL1, hL2, hD1, hD2]
  ring

/-- The Levi form of a finite sum of `C²` germs is the sum of the Levi forms. -/
theorem leviForm_finset_sum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {ι : Type*} (s : Finset ι) {f : ι → E → ℝ} {z : E}
    (hf : ∀ a ∈ s, ContDiffAt ℝ 2 (f a) z) (u : E) :
    leviForm (fun w => ∑ a ∈ s, f a w) z u = ∑ a ∈ s, leviForm (f a) z u := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    have hs : ContDiffAt ℝ 2 (fun w => ∑ a ∈ s, f a w) z :=
      ContDiffAt.sum fun a ha => hf a (Finset.mem_insert_of_mem ha)
    have hfun : (fun w => ∑ a ∈ insert j s, f a w) = f j + fun w => ∑ a ∈ s, f a w := by
      funext w
      simp [Finset.sum_insert hj]
    rw [hfun, leviForm_add (hf j (Finset.mem_insert_self j s)) hs,
      ih fun a ha => hf a (Finset.mem_insert_of_mem ha), Finset.sum_insert hj]

variable {N n : ℕ} {ι : Type*} {m : ι → ℕ}

/-- The glued local potential `R(z) = χ₀(P z) ‖z‖² + Σ_a χ_a(P z) ‖G_a z‖²`. -/
def potential (s : Finset ι) (P : ComplexModel N → ComplexModel n) (χ₀ : ComplexModel n → ℝ)
    (χ : ι → ComplexModel n → ℝ) (G : (a : ι) → ComplexModel N → ComplexModel (m a)) :
    ComplexModel N → ℝ :=
  fun z => χ₀ (P z) * ‖z‖ ^ 2 + ∑ a ∈ s, χ a (P z) * ‖G a z‖ ^ 2

theorem potential_contDiffOn (s : Finset ι) {T : Set (ComplexModel N)}
    {O : Set (ComplexModel n)} {P : ComplexModel N → ComplexModel n}
    (hP : ContDiffOn ℂ ∞ P T) (hPO : MapsTo P T O) {χ₀ : ComplexModel n → ℝ}
    (hχ₀ : ContDiffOn ℝ ∞ χ₀ O) {χ : ι → ComplexModel n → ℝ}
    (hχ : ∀ a, ContDiffOn ℝ ∞ (χ a) O) {G : (a : ι) → ComplexModel N → ComplexModel (m a)}
    (hG : ∀ a, ContDiffOn ℂ ∞ (G a) T) :
    ContDiffOn ℝ ∞ (potential s P χ₀ χ G) T := by
  have hPr := hP.restrict_scalars ℝ
  refine ((hχ₀.comp hPr hPO).mul (contDiff_norm_sq ℝ).contDiffOn).add ?_
  exact ContDiffOn.sum fun a _ =>
    ((hχ a).comp hPr hPO).mul ((contDiff_norm_sq ℝ).comp_contDiffOn ((hG a).restrict_scalars ℝ))

/-- **Positivity on the fibre directions.** At a point where `dP u = 0`, the Levi form of the glued
potential is at least `χ₀(P z) ‖u‖²`. -/
theorem leviForm_potential_ge_of_fderiv_eq_zero (s : Finset ι) {T : Set (ComplexModel N)}
    (hT : IsOpen T) {O : Set (ComplexModel n)} (hO : IsOpen O)
    {P : ComplexModel N → ComplexModel n} (hP : ContDiffOn ℂ ∞ P T) (hPO : MapsTo P T O)
    {χ₀ : ComplexModel n → ℝ} (hχ₀ : ContDiffOn ℝ ∞ χ₀ O) {χ : ι → ComplexModel n → ℝ}
    (hχ : ∀ a, ContDiffOn ℝ ∞ (χ a) O) (hχnn : ∀ a, ∀ x ∈ O, 0 ≤ χ a x)
    {G : (a : ι) → ComplexModel N → ComplexModel (m a)} (hG : ∀ a, ContDiffOn ℂ ∞ (G a) T)
    {z : ComplexModel N} (hz : z ∈ T) {u : ComplexModel N} (hu : fderiv ℝ P z u = 0) :
    χ₀ (P z) * ‖u‖ ^ 2 ≤ leviForm (potential s P χ₀ χ G) z u := by
  have hPr := hP.restrict_scalars ℝ
  have h0 : ContDiffAt ℝ 2 (fun w => χ₀ (P w) * ‖w‖ ^ 2) z :=
    (((hχ₀.comp hPr hPO).mul (contDiff_norm_sq ℝ).contDiffOn).contDiffAt
      (hT.mem_nhds hz)).of_le two_le_infty
  have ha : ∀ a ∈ s, ContDiffAt ℝ 2 (fun w => χ a (P w) * ‖G a w‖ ^ 2) z := fun a _ =>
    ((((hχ a).comp hPr hPO).mul ((contDiff_norm_sq ℝ).comp_contDiffOn
      ((hG a).restrict_scalars ℝ))).contDiffAt (hT.mem_nhds hz)).of_le two_le_infty
  have hsplit : potential s P χ₀ χ G = (fun w => χ₀ (P w) * ‖w‖ ^ 2) +
      fun w => ∑ a ∈ s, χ a (P w) * ‖G a w‖ ^ 2 := rfl
  rw [hsplit, leviForm_add h0 (ContDiffAt.sum ha),
    leviForm_finset_sum s ha u]
  have hid := leviForm_cutoff_mul_normSq hT hO hP hPO hχ₀
    (G := (id : ComplexModel N → ComplexModel N)) contDiffOn_id hz hu
  simp only [id_eq, fderiv_id, ContinuousLinearMap.coe_id'] at hid
  rw [hid]
  have hsum : 0 ≤ ∑ a ∈ s, leviForm (fun w => χ a (P w) * ‖G a w‖ ^ 2) z u := by
    refine Finset.sum_nonneg fun a _ => ?_
    rw [leviForm_cutoff_mul_normSq hT hO hP hPO (hχ a) (hG a) hz hu]
    exact mul_nonneg (hχnn a _ (hPO hz)) (sq_nonneg _)
  linarith

/-- The `(u, iu)`-value of the pull-back of a semipositive form along a holomorphic map is
nonnegative; it vanishes only in the directions killed by the differential when the form is
strictly positive. -/
theorem quad_pullbackForm_nonneg {T : Set (ComplexModel N)} (hT : IsOpen T)
    {O : Set (ComplexModel n)} {P : ComplexModel N → ComplexModel n}
    (hP : ContDiffOn ℂ ∞ P T) (hPO : MapsTo P T O) {w : AmbientForm n 2}
    (hwpos : ∀ x ∈ O, IsStrictlyPositive (w x)) {z : ComplexModel N} (hz : z ∈ T)
    (u : ComplexModel N) :
    0 ≤ quad (pullbackForm P w z) u ∧
      (quad (pullbackForm P w z) u = 0 → fderiv ℝ P z u = 0) := by
  have hPz : DifferentiableAt ℂ P z :=
    (hP.differentiableOn (by simp)).differentiableAt (hT.mem_nhds hz)
  have hq : quad (pullbackForm P w z) u =
      w (P z) ![fderiv ℝ P z u, Complex.I • fderiv ℝ P z u] :=
    pullbackForm_apply_complexLine hPz w u
  rw [hq]
  by_cases hξ : fderiv ℝ P z u = 0
  · refine ⟨?_, fun _ => hξ⟩
    rw [hξ, (w (P z)).map_coord_zero (0 : Fin 2) rfl]
  · have hpos := hwpos (P z) (hPO hz) _ hξ
    exact ⟨hpos.le, fun h => absurd h hpos.ne'⟩

/-- **The local Varouchas estimate.** For a strictly positive form `w` on `O` and the glued
potential `R` with `χ₀(P b) > 0`, there are `B₀ > 0` and an open `U ∋ b` such that
`ddᶜ R + B · P^*w` is strictly positive on `U` for every `B ≥ B₀`. -/
theorem exists_isStrictlyPositive_near (s : Finset ι) {T : Set (ComplexModel N)}
    (hT : IsOpen T) {O : Set (ComplexModel n)} (hO : IsOpen O)
    {P : ComplexModel N → ComplexModel n} (hP : ContDiffOn ℂ ∞ P T) (hPO : MapsTo P T O)
    {w : AmbientForm n 2} (hw : ContDiffOn ℝ ∞ w O) (hwpos : ∀ x ∈ O, IsStrictlyPositive (w x))
    {χ₀ : ComplexModel n → ℝ} (hχ₀ : ContDiffOn ℝ ∞ χ₀ O) {χ : ι → ComplexModel n → ℝ}
    (hχ : ∀ a, ContDiffOn ℝ ∞ (χ a) O) (hχnn : ∀ a, ∀ x ∈ O, 0 ≤ χ a x)
    {G : (a : ι) → ComplexModel N → ComplexModel (m a)} (hG : ∀ a, ContDiffOn ℂ ∞ (G a) T)
    {b : ComplexModel N} (hb : b ∈ T) (hχ₀b : 0 < χ₀ (P b)) :
    ∃ B₀ : ℝ, 0 < B₀ ∧ ∃ U : Set (ComplexModel N), IsOpen U ∧ b ∈ U ∧ U ⊆ T ∧
      ∀ B : ℝ, B₀ ≤ B → ∀ z ∈ U,
        IsStrictlyPositive (smoothDDC (potential s P χ₀ χ G) z + B • pullbackForm P w z) := by
  have hR := potential_contDiffOn s hP hPO hχ₀ hχ hG
  have hPr := hP.restrict_scalars ℝ
  have hacont : ContinuousOn (smoothDDC (potential s P χ₀ χ G)) T :=
    (Pending.LogWeightFactorization.smoothDDC_contDiffOn hT hR).continuousOn
  have hbcont : ContinuousOn (pullbackForm P w) T :=
    (SmoothRealForm.contDiffOn_compContinuousLinearMap (hw.comp hPr hPO)
      (hPr.fderiv_of_isOpen hT (by simp))).continuousOn
  obtain ⟨B₀, hB₀, U, hU, hbU, hUT, hB⟩ :=
    Pending.UniformTubePositivity.exists_forall_isStrictlyPositive_add_smul_of_pos_on_null_familyOn
      hT hacont hbcont (fun z hz u => (quad_pullbackForm_nonneg hT hP hPO hwpos hz u).1)
      (isCompact_singleton (x := b)) (singleton_subset_iff.mpr hb) (by
        intro x hx u hu hnull
        rw [mem_singleton_iff] at hx
        subst hx
        have hξ := (quad_pullbackForm_nonneg hT hP hPO hwpos hb u).2 hnull
        have hlevi := leviForm_potential_ge_of_fderiv_eq_zero s hT hO hP hPO hχ₀ hχ hχnn hG hb hξ
        have h2 : ContDiffAt ℝ 2 (potential s P χ₀ χ G) x :=
          (hR.contDiffAt (hT.mem_nhds hb)).of_le two_le_infty
        change 0 < smoothDDC (potential s P χ₀ χ G) x ![u, Complex.I • u]
        rw [smoothDDC_complexDiagonal_eq_leviForm h2 u]
        have hu2 : 0 < ‖u‖ ^ 2 := by positivity
        exact div_pos (lt_of_lt_of_le (mul_pos hχ₀b hu2) hlevi) Real.pi_pos)
  exact ⟨B₀, hB₀, U, hU, hbU (mem_singleton b), hUT, hB⟩

/-- `P^*w + ddᶜ R` is closed when `w` is. -/
theorem extDeriv_pullback_add_ddc {T : Set (ComplexModel N)} (hT : IsOpen T)
    {O : Set (ComplexModel n)} (hO : IsOpen O) {P : ComplexModel N → ComplexModel n}
    (hP : ContDiffOn ℂ ∞ P T) (hPO : MapsTo P T O) {w : AmbientForm n 2}
    (hw : ContDiffOn ℝ ∞ w O) (hwcl : ∀ x ∈ O, extDeriv w x = 0) {R : ComplexModel N → ℝ}
    (hR : ContDiffOn ℝ ∞ R T) {z : ComplexModel N} (hz : z ∈ T) :
    extDeriv (pullbackForm P w + smoothDDC R) z = 0 := by
  have hPr := hP.restrict_scalars ℝ
  have h1 : DifferentiableAt ℝ (pullbackForm P w) z :=
    ((SmoothRealForm.contDiffOn_compContinuousLinearMap (hw.comp hPr hPO)
      (hPr.fderiv_of_isOpen hT (by simp))).contDiffAt (hT.mem_nhds hz)).differentiableAt
      (by simp)
  have h2 : DifferentiableAt ℝ (smoothDDC R) z :=
    ((Pending.LogWeightFactorization.smoothDDC_contDiffOn hT hR).contDiffAt
      (hT.mem_nhds hz)).differentiableAt (by simp)
  rw [extDeriv_add h1 h2]
  have hdiff : DifferentiableAt ℝ w (P z) :=
    (hw.contDiffAt (hO.mem_nhds (hPO hz))).differentiableAt (by simp)
  have hnat := extDeriv_pullback hdiff (hPr.contDiffAt (hT.mem_nhds hz))
    (by simpa using ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hpull : extDeriv (pullbackForm P w) z = 0 := by
    change extDeriv (fun x => (w (P x)).compContinuousLinearMap (fderiv ℝ P x)) z = 0
    rw [hnat, hwcl _ (hPO hz)]
    ext v
    rfl
  have hddc : extDeriv (smoothDDC R) z = 0 :=
    extDeriv_extDeriv_apply
      ((smoothDc_contDiffOn hT hR).contDiffAt (hT.mem_nhds hz))
      (by simpa using ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  rw [hpull, hddc, add_zero]

/-- `P^*w + ddᶜ R` is of type `(1,1)` when `w` is (`P` holomorphic). -/
theorem isOneOne_pullback_add_ddc {T : Set (ComplexModel N)} (hT : IsOpen T)
    {O : Set (ComplexModel n)} {P : ComplexModel N → ComplexModel n}
    (hP : ContDiffOn ℂ ∞ P T) (hPO : MapsTo P T O) {w : AmbientForm n 2}
    (hw11 : ∀ x ∈ O, IsOneOne (w x)) {R : ComplexModel N → ℝ}
    (hR : ContDiffOn ℝ ∞ R T) {z : ComplexModel N} (hz : z ∈ T) :
    IsOneOne ((pullbackForm P w + smoothDDC R) z) := by
  intro a b
  have hd : DifferentiableAt ℂ P z :=
    (hP.differentiableOn (by simp)).differentiableAt (hT.mem_nhds hz)
  have hlin (v : ComplexModel N) :
      fderiv ℝ P z (Complex.I • v) = Complex.I • fderiv ℝ P z v := by
    rw [hd.fderiv_restrictScalars ℝ]
    exact (fderiv ℂ P z).map_smul Complex.I v
  have hR2 : ContDiffAt ℝ 2 R z := (hR.contDiffAt (hT.mem_nhds hz)).of_le two_le_infty
  have hddc := MongeAmpere.smoothDDC_isOneOne hR2 a b
  have hpull : pullbackForm P w z ![Complex.I • a, Complex.I • b] =
      pullbackForm P w z ![a, b] := by
    change w (P z) ((fderiv ℝ P z) ∘ ![Complex.I • a, Complex.I • b]) =
      w (P z) ((fderiv ℝ P z) ∘ ![a, b])
    have hvec : ((fderiv ℝ P z) ∘ ![Complex.I • a, Complex.I • b]) =
        ![Complex.I • fderiv ℝ P z a, Complex.I • fderiv ℝ P z b] := by
      funext i
      fin_cases i <;> simp [hlin]
    have hvec' : ((fderiv ℝ P z) ∘ ![a, b]) = ![fderiv ℝ P z a, fderiv ℝ P z b] := by
      funext i
      fin_cases i <;> rfl
    rw [hvec, hvec']
    exact hw11 (P z) (hPO hz) (fderiv ℝ P z a) (fderiv ℝ P z b)
  simp only [Pi.add_apply, ContinuousAlternatingMap.add_apply]
  rw [hpull, hddc]

end SGPT.Unibranch.KS2LeviEstimate

end
