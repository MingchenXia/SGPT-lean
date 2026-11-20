import SGPT.Foundations.Analysis.Pending.BedfordTaylorFibreSlicing
import SGPT.Foundations.Analysis.Pending.BedfordTaylorSlotAdd

set_option autoImplicit false

/-!
# A slot depending on the last coordinate only

On `ℂⁿ⁺¹ = ℂⁿ × ℂ` let `ψ : ℂ → ℝ` be smooth and `ψ̂(q) = ψ(q_last)` (`timeLift`). Its complex Hessian
is `(Δψ/4)(q_last) · E`, with `E` the complex Hessian of `|τ|²` (`complexHessian_timeLift`), where
`Δψ/4 = (ψ_xx + ψ_yy)/4` is `timeLaplacian ψ`. Consequently, in every mixed density, a slot `ψ̂` is
`(Δψ/4)` times the slot `|τ|²` (`mixedDensity_update_timeLift`), and for Bedford--Taylor limits:

* `integral_isBTLimit_timeLift_sub` — **the time-slot defect**: if `p` and `ψ̂ + p` are smooth
  plurisubharmonic on `Ω` (a regularizer), then for continuous `χ` with compact support in `Ω` and a
  weight `w` with decreasing smooth plurisubharmonic approximations,
  \[
    \int \chi w\, d\,\mathrm{BT}(v, \hat\psi + p) - \int \chi w\, d\,\mathrm{BT}(v, p)
      = \int \chi\, w\, (\Delta\psi/4)(\tau)\, d\,\mathrm{BT}(v, |\tau|^2),
  \]
  i.e. `ddᶜψ̂ ∧ T = (Δψ/4) ddᶜ|τ|² ∧ T` for the Bedford--Taylor product `T` of the other slots.

This is the step `ddᶜ_τ ψ = (Δψ/4) ddᶜ|τ|²` of Xia's identities (4.29)--(4.34) (`xia-sgpt:page-0171`).
-/

open Set Filter MeasureTheory TopologicalSpace Metric
open scoped Topology ContDiff ComplexOrder

namespace SGPT.Foundations.Analysis.Pending.BedfordTaylorTimeSlot

open FirstPass FirstPass.MongeAmpere FirstPass.MixedMongeAmpere MixedDensityRankOneSlot
  BedfordTaylor BedfordTaylorFibreSlicing

noncomputable section

variable {n : ℕ}

/-- `(Δψ/4)(τ) = (ψ_xx + ψ_yy)/4`, through the real Hessian. -/
def timeLaplacian (ψ : ℂ → ℝ) (τ : ℂ) : ℝ :=
  (realHessian ψ τ 1 1 + realHessian ψ τ Complex.I Complex.I) / 4

/-- `ψ̂(q) = ψ(q_last)`: a function of the last coordinate only. -/
def timeLift (n : ℕ) (ψ : ℂ → ℝ) : ComplexModel (n + 1) → ℝ := fun q => ψ (q (Fin.last n))

theorem timeLift_eq_comp (ψ : ℂ → ℝ) : timeLift n ψ = ψ ∘ lastCoordinate n := rfl

theorem contDiff_timeLift {ψ : ℂ → ℝ} {k : WithTop ℕ∞} (hψ : ContDiff ℝ k ψ) :
    ContDiff ℝ k (timeLift n ψ) :=
  hψ.comp (lastCoordinate n).contDiff

theorem realHessian_zero_left {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u : E → ℝ) (x w : E) : realHessian u x 0 w = 0 := by
  unfold realHessian
  exact (iteratedFDeriv ℝ 2 u x).map_coord_zero (i := 0) (by simp)

theorem realHessian_zero_right {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u : E → ℝ) (x v : E) : realHessian u x v 0 = 0 := by
  unfold realHessian
  exact (iteratedFDeriv ℝ 2 u x).map_coord_zero (i := 1) (by simp)

theorem realHessian_timeLift {ψ : ℂ → ℝ} (hψ : ContDiff ℝ 2 ψ) (q a b : ComplexModel (n + 1)) :
    realHessian (timeLift n ψ) q a b =
      realHessian ψ (q (Fin.last n)) (a (Fin.last n)) (b (Fin.last n)) := by
  have h := realHessian_comp_affine hψ (lastCoordinate n) 0 q a b
  have hfun : (fun y : ComplexModel (n + 1) => ψ ((0 : ℂ) + lastCoordinate n y)) = timeLift n ψ := by
    funext y; simp [timeLift]
  rw [hfun] at h
  rw [h]
  simp

/-- **The complex Hessian of a function of the last coordinate** is `(Δψ/4)` times that of `|τ|²`. -/
theorem complexHessian_timeLift {ψ : ℂ → ℝ} (hψ : ContDiff ℝ 2 ψ) (q : ComplexModel (n + 1)) :
    complexHessian (timeLift n ψ) q =
      timeLaplacian ψ (q (Fin.last n)) • complexHessian (lastNormSq n) q := by
  have hsym : realHessian ψ (q (Fin.last n)) 1 Complex.I =
      realHessian ψ (q (Fin.last n)) Complex.I 1 := by
    simpa only [realHessian_eq_fderiv] using
      hψ.contDiffAt.isSymmSndFDerivAt (by norm_num) 1 Complex.I
  rw [complexHessian_lastNormSq]
  ext j k
  simp only [complexHessian, realHessian_timeLift hψ, Matrix.smul_apply, lastUnit]
  by_cases hj : j = Fin.last n <;> by_cases hk : k = Fin.last n
  · subst hj hk
    simp only [coordinateVector, PiLp.smul_apply, PiLp.single_apply, if_true,
      smul_eq_mul, mul_one, and_self, hsym, sub_self, Complex.ofReal_zero, zero_div, mul_zero,
      add_zero, timeLaplacian, Complex.real_smul]
    push_cast
    ring
  · simp only [coordinateVector, PiLp.smul_apply, PiLp.single_apply,
      Ne.symm hk, if_false, smul_eq_mul, mul_zero, realHessian_zero_right, hk, and_false]
    simp
  · simp only [coordinateVector, PiLp.smul_apply, PiLp.single_apply,
      Ne.symm hj, if_false, smul_eq_mul, mul_zero, realHessian_zero_left, hj, false_and]
    simp
  · simp only [coordinateVector, PiLp.smul_apply, PiLp.single_apply,
      Ne.symm hj, if_false, smul_eq_mul, mul_zero, realHessian_zero_left, hj, false_and]
    simp

theorem complexHessian_update_apply {m : ℕ} (F : Fin m → ComplexModel m → ℝ) (i₀ : Fin m)
    (g : ComplexModel m → ℝ) (q : ComplexModel m) :
    (fun i => complexHessian (Function.update F i₀ g i) q) =
      Function.update (fun i => complexHessian (F i) q) i₀ (complexHessian g q) := by
  classical
  funext i
  by_cases h : i = i₀
  · subst h; simp
  · simp [Function.update_of_ne h]

/-- A slot whose complex Hessian is a real multiple of another one. -/
theorem mixedDensity_update_of_complexHessian_eq_smul {m : ℕ} (F : Fin m → ComplexModel m → ℝ)
    (i₀ : Fin m) {g h : ComplexModel m → ℝ} {q : ComplexModel m} {c : ℝ}
    (hgh : complexHessian g q = c • complexHessian h q) :
    mixedDensity (Function.update F i₀ g) q = c * mixedDensity (Function.update F i₀ h) q := by
  unfold mixedDensity
  rw [complexHessian_update_apply, complexHessian_update_apply, hgh,
    FirstPass.MongeAmpere.mixedCoefficient_update_smul, Complex.re_ofReal_mul, mul_div_assoc]

/-- **In a mixed density, a slot `ψ̂` is `(Δψ/4)` times the slot `|τ|²`.** -/
theorem mixedDensity_update_timeLift (F : Fin (n + 1) → ComplexModel (n + 1) → ℝ) {ψ : ℂ → ℝ}
    (hψ : ContDiff ℝ 2 ψ) (q : ComplexModel (n + 1)) :
    mixedDensity (Function.update F (Fin.last n) (timeLift n ψ)) q =
      timeLaplacian ψ (q (Fin.last n)) *
        mixedDensity (Function.update F (Fin.last n) (lastNormSq n)) q :=
  mixedDensity_update_of_complexHessian_eq_smul F _ (complexHessian_timeLift hψ q)

theorem continuous_timeLaplacian {ψ : ℂ → ℝ} (hψ : ContDiff ℝ ∞ ψ) :
    Continuous (timeLaplacian ψ) := by
  have h2 : Continuous (iteratedFDeriv ℝ 2 ψ) :=
    hψ.continuous_iteratedFDeriv (WithTop.coe_le_coe.mpr le_top)
  have hc (v w : ℂ) : Continuous fun τ => realHessian ψ τ v w :=
    (continuous_eval_const ![v, w]).comp h2
  exact ((hc 1 1).add (hc Complex.I Complex.I)).div_const 4

/-! ### The time-slot defect of Bedford--Taylor limits -/

/-- A constant sequence of a smooth plurisubharmonic function in the last slot of an admissible
family. -/
theorem isAdmissible_update_last {U : Opens (ComplexModel (n + 1))}
    {v : Fin (n + 1) → ComplexModel (n + 1) → ℝ} {a s : ComplexModel (n + 1) → ℝ}
    {F : Fin (n + 1) → ℕ → ComplexModel (n + 1) → ℝ}
    (hF : IsAdmissible (n + 1) U (Function.update v (Fin.last n) a) F) (hs : IsSmoothPsdOn U s) :
    IsAdmissible (n + 1) U (Function.update v (Fin.last n) s)
      (Function.update F (Fin.last n) fun _ => s) := by
  classical
  refine ⟨fun i => ?_, fun i hi => absurd i.isLt (not_lt.2 hi)⟩
  by_cases h : i = Fin.last n
  · subst h; simpa using isDecApprox_const hs
  · simpa [Function.update_of_ne h] using hF.1 i

theorem update_apply_last_family {m : ℕ} (F : Fin m → ℕ → ComplexModel m → ℝ) (i₀ : Fin m)
    (s : ComplexModel m → ℝ) (k : ℕ) :
    (fun i => Function.update F i₀ (fun _ => s) i k) = Function.update (fun i => F i k) i₀ s := by
  classical
  funext i
  by_cases h : i = i₀
  · subst h; simp
  · simp [Function.update_of_ne h]

/-- **The time-slot defect.** For a regularizer `p` with `p` and `ψ̂ + p` smooth plurisubharmonic on
`Ω`, `ddᶜ(ψ̂ + p) ∧ T - ddᶜp ∧ T = (Δψ/4)(τ) ddᶜ|τ|² ∧ T`, tested against `χ w`. -/
theorem integral_isBTLimit_timeLift_sub {Ω : Opens (ComplexModel (n + 1))}
    {v : Fin (n + 1) → ComplexModel (n + 1) → ℝ} {ψ : ℂ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    {p : ComplexModel (n + 1) → ℝ} (hp : IsSmoothPsdOn Ω p)
    (hψp : IsSmoothPsdOn Ω fun q => timeLift n ψ q + p q)
    {ν₁ ν₂ ν : Measure (ComplexModel (n + 1))}
    (hν₁ : IsBTLimit Ω (Function.update v (Fin.last n) fun q => timeLift n ψ q + p q) ν₁)
    (hν₂ : IsBTLimit Ω (Function.update v (Fin.last n) p) ν₂)
    (hν : IsBTLimit Ω (Function.update v (Fin.last n) (lastNormSq n)) ν)
    {w : ComplexModel (n + 1) → ℝ} (hw : ∀ V, RelativelyCompactIn V Ω → ∃ G, IsDecApprox V w G)
    {χ : ComplexModel (n + 1) → ℝ} (hχ : Continuous χ) (hχc : HasCompactSupport χ)
    (hχΩ : tsupport χ ⊆ Ω) :
    (∫ q, χ q * w q ∂ν₁) - ∫ q, χ q * w q ∂ν₂ =
      ∫ q, (χ q * timeLaplacian ψ (q (Fin.last n))) * w q ∂ν := by
  classical
  have h2 : (2 : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
  set K := tsupport χ with hKdef
  have hK : IsCompact K := hχc
  obtain ⟨U, hUo, hKU, hUΩ, hUc⟩ := exists_open_between_and_isCompact_closure hK Ω.isOpen hχΩ
  set UO : Opens (ComplexModel (n + 1)) := ⟨U, hUo⟩ with hUOdef
  have hUrc : RelativelyCompactIn UO Ω := ⟨hUc, hUΩ⟩
  have hUOΩ : UO ≤ Ω := subset_closure.trans hUΩ
  obtain ⟨F, hF, -⟩ := hν.2.2 UO hUrc
  obtain ⟨G, hG⟩ := hw UO hUrc
  have hpU : IsSmoothPsdOn UO p := IsSmoothPsdOn.mono hp hUOΩ
  have hψpU : IsSmoothPsdOn UO (fun q => timeLift n ψ q + p q) := IsSmoothPsdOn.mono hψp hUOΩ
  have hEU : IsSmoothPsdOn UO (lastNormSq n) := isSmoothPsdOn_lastNormSq UO
  have hF₁ := isAdmissible_update_last hF hψpU
  have hF₂ := isAdmissible_update_last hF hpU
  have hFE := isAdmissible_update_last hF hEU
  -- the three weighted limits
  have hlim (s : ComplexModel (n + 1) → ℝ) (μs : Measure (ComplexModel (n + 1)))
      (hμs : IsBTLimit Ω (Function.update v (Fin.last n) s) μs)
      (hFs : IsAdmissible (n + 1) UO (Function.update v (Fin.last n) s)
        (Function.update F (Fin.last n) fun _ => s))
      (ξ : ComplexModel (n + 1) → ℝ) (hξ : Continuous ξ) (hξc : HasCompactSupport ξ)
      (hξU : tsupport ξ ⊆ UO) :
      Tendsto (fun k => ∫ q, ξ q * G k q *
          mixedDensity (Function.update (fun i => F i k) (Fin.last n) s) q) atTop
        (𝓝 (∫ q, ξ q * w q ∂μs)) := by
    have hc : (μs.restrict UO) (UO : Set (ComplexModel (n + 1)))ᶜ = 0 := by
      rw [Measure.restrict_apply' UO.isOpen.measurableSet]; simp
    have hf : ∀ K', IsCompact K' → K' ⊆ UO → (μs.restrict UO) K' < ⊤ := fun K' hK' hK'U =>
      (Measure.restrict_apply_le _ _).trans_lt (hμs.2.1 K' hK' (hK'U.trans hUOΩ))
    have h := wClaim_of_pClaim (pClaim_all (n := n + 1)) UO _ (μs.restrict UO) hc hf
      (fun F hF => hμs.tendstoMixed_restrict hUrc hF) _ hFs w G hG ξ hξ hξc hξU
    have hr : ∫ q, ξ q * w q ∂(μs.restrict UO) = ∫ q, ξ q * w q ∂μs :=
      setIntegral_eq_integral_of_forall_compl_eq_zero fun q hq => by
        rw [image_eq_zero_of_notMem_tsupport fun h => hq (hξU h), zero_mul]
    rw [hr] at h
    simpa only [update_apply_last_family] using h
  set χ' : ComplexModel (n + 1) → ℝ := fun q => χ q * timeLaplacian ψ (q (Fin.last n)) with hχ'def
  have hχ' : Continuous χ' :=
    hχ.mul ((continuous_timeLaplacian hψ).comp (lastCoordinate n).continuous)
  have hχ'K : tsupport χ' ⊆ K := tsupport_mul_subset_left
  have hχ'c : HasCompactSupport χ' := hχc.mono' (subset_tsupport _ |>.trans hχ'K)
  have h₁ := hlim _ ν₁ hν₁ hF₁ χ hχ hχc hKU
  have h₂ := hlim _ ν₂ hν₂ hF₂ χ hχ hχc hKU
  have hE := hlim _ ν hν hFE χ' hχ' hχ'c (hχ'K.trans hKU)
  -- the pointwise identity at every level
  have hlevel (k : ℕ) :
      (∫ q, χ q * G k q * mixedDensity (Function.update (fun i => F i k) (Fin.last n)
          fun q => timeLift n ψ q + p q) q) -
        ∫ q, χ q * G k q * mixedDensity (Function.update (fun i => F i k) (Fin.last n) p) q =
      ∫ q, χ' q * G k q *
        mixedDensity (Function.update (fun i => F i k) (Fin.last n) (lastNormSq n)) q := by
    have hint (s : ComplexModel (n + 1) → ℝ) (hs : ∀ i, IsSmoothPsdOn UO
        (Function.update (fun i => F i k) (Fin.last n) s i)) :
        Integrable fun q => χ q * G k q *
          mixedDensity (Function.update (fun i => F i k) (Fin.last n) s) q := by
      have h := integrable_mul_of_continuousOn (U := UO)
        (D := fun q => G k q * mixedDensity (Function.update (fun i => F i k) (Fin.last n) s) q)
        (((hG.1 k).1.continuousOn).mul (continuousOn_mixedDensity fun i => (hs i).1)) hχ hχc hKU
      simpa only [mul_assoc] using h
    have hslots (s : ComplexModel (n + 1) → ℝ) (hs : IsSmoothPsdOn UO s) (i : Fin (n + 1)) :
        IsSmoothPsdOn UO (Function.update (fun i => F i k) (Fin.last n) s i) := by
      by_cases h : i = Fin.last n
      · subst h; simpa using hs
      · simpa [Function.update_of_ne h] using (hF.1 i).1 k
    rw [← integral_sub (hint _ (hslots _ hψpU)) (hint _ (hslots _ hpU))]
    refine integral_congr_ae (Eventually.of_forall fun q => ?_)
    by_cases hq : q ∈ UO
    · have hpq : ContDiffAt ℝ 2 p q := (hp.1.contDiffAt (Ω.isOpen.mem_nhds (hUOΩ hq))).of_le h2
      have hψq : ContDiffAt ℝ 2 (timeLift n ψ) q := (contDiff_timeLift hψ).contDiffAt.of_le h2
      have hadd := mixedDensity_update_add (f := fun i => F i k) (Fin.last n) hψq hpq
      have hT := mixedDensity_update_timeLift (fun i => F i k) (hψ.of_le h2) q
      simp only [hχ'def]
      rw [hadd, hT]
      ring
    · have : χ q = 0 := image_eq_zero_of_notMem_tsupport fun h => hq (hKU h)
      simp [hχ'def, this]
  have hlhs := h₁.sub h₂
  simp only [hlevel] at hlhs
  exact tendsto_nhds_unique hlhs hE

end

end SGPT.Foundations.Analysis.Pending.BedfordTaylorTimeSlot
