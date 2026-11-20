import SGPT.Okounkov.TranscendentalSkodaStatement
import SGPT.Foundations.Analysis.Pending.MultiplierIdeals
import SGPT.Foundations.Analysis.Pending.AnalyticSingularities
import SGPT.Foundations.Analysis.FirstPass.ERealChordUSC

/-!
# Skoda's theorem: the algebraic part

Blueprint `claude-tok-skoda`, nodes `skoda:easy-inclusion` and `skoda:main`.

* `multiplierIntegrableAt_of_memPowMulMultiplierAt`: `J^k · 𝓘(cφ)_x ⊆ 𝓘((k + c)φ)_x`
  (`|g^β|² ≤ |g|^{2k}`).
* `skodaStatement_of_division`: the one-step division `𝓘((ℓ + 1)φ)_x ⊆ J · 𝓘(ℓφ)_x` for all
  `ℓ ≥ n` (`SkodaDivisionStatement`) implies `𝓘((k + m)φ)_x = J^k · 𝓘(mφ)_x` for all `m ≥ n`
  (`SkodaStatement`), by induction on `k`.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Okounkov.TranscendentalSkoda

open Filter MeasureTheory Set SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology ENNReal

variable {n r : ℕ}

/-- `φ = log ∑ |gᵢ|²` is plurisubharmonic, hence quasi-plurisubharmonic, near `x`. -/
theorem quasiPlurisubharmonicAt_generatorLog {g : Fin r → ComplexModel n → ℂ}
    {x : ComplexModel n} (hg : HolomorphicGeneratorsAt g x) :
    QuasiPlurisubharmonicAt (generatorLog g) x := by
  have h := SGPT.Foundations.Analysis.Pending.plurisubharmonicAt_scaled_generatorLog hg one_pos
  have heq : (fun y => ((1 : ℝ) : EReal) * generatorLog g y) = generatorLog g := by
    funext y; simp
  rw [heq] at h
  exact h.quasiPlurisubharmonicAt

/-- `log ∑ |gᵢ|²` is continuous (in the order topology of `EReal`) where the `gᵢ` are. -/
theorem continuousOn_generatorLog {g : Fin r → ComplexModel n → ℂ} {U : Set (ComplexModel n)}
    (hg : ∀ i, ContinuousOn (g i) U) : ContinuousOn (generatorLog g) U := by
  have hv : ContinuousOn (generatorVector g) U := by
    have : generatorVector g = fun y => (WithLp.equiv 2 (Fin r → ℂ)).symm (fun j => g j y) := by
      funext y; rfl
    rw [this]
    exact (PiLp.continuous_toLp 2 _).comp_continuousOn (continuousOn_pi.mpr hg)
  exact continuous_logNormSq.comp_continuousOn hv

/-- Measurability of the multiplier density `|F|² e^{-cφ}` on an open set where `g` and `F`
are continuous. -/
theorem aemeasurable_multiplierDensity_generatorLog {g : Fin r → ComplexModel n → ℂ}
    {U : Set (ComplexModel n)} (hU : IsOpen U) (hg : ∀ i, ContinuousOn (g i) U) {c : ℝ}
    (hc : c ≠ 0) {F : ComplexModel n → ℂ} (hF : ContinuousOn F U) :
    AEMeasurable (multiplierDensity (generatorLog g) c F) (volume.restrict U) := by
  have hφ : AEMeasurable (generatorLog g) (volume.restrict U) :=
    (continuousOn_generatorLog hg).aemeasurable hU.measurableSet
  have hcmul : AEMeasurable (fun y => (c : EReal) * generatorLog g y) (volume.restrict U) :=
    (FirstPass.continuous_eReal_const_mul hc).measurable.comp_aemeasurable' hφ
  have hweight : AEMeasurable (fun y => multiplierWeight c (generatorLog g y))
      (volume.restrict U) := by
    have hneg : AEMeasurable (fun y => -((c : EReal) * generatorLog g y)) (volume.restrict U) :=
      continuous_neg.measurable.comp_aemeasurable' hcmul
    simpa only [multiplierWeight] using EReal.measurable_exp.comp_aemeasurable' hneg
  have hFm : AEMeasurable F (volume.restrict U) := hF.aemeasurable hU.measurableSet
  exact ((hFm.norm.pow_const 2).ennreal_ofReal).mul hweight

/-- `|g^β|² ≤ (∑ |gᵢ|²)^k`. -/
theorem norm_sq_prod_le {k : ℕ} (g : Fin r → ComplexModel n → ℂ) (β : Fin k → Fin r)
    (y : ComplexModel n) :
    ‖∏ i, g (β i) y‖ ^ 2 ≤ (∑ j, ‖g j y‖ ^ 2) ^ k := by
  rw [norm_prod, ← Finset.prod_pow]
  calc ∏ i, ‖g (β i) y‖ ^ 2 ≤ ∏ _i : Fin k, ∑ j, ‖g j y‖ ^ 2 :=
        Finset.prod_le_prod (fun i _ => sq_nonneg _) fun i _ =>
          Finset.single_le_sum (f := fun j => ‖g j y‖ ^ 2) (fun j _ => sq_nonneg _)
            (Finset.mem_univ (β i))
    _ = (∑ j, ‖g j y‖ ^ 2) ^ k := by simp

/-- The pointwise inequality `|g^β h|² e^{-(k+c)φ} ≤ |h|² e^{-cφ}`. -/
theorem multiplierDensity_prod_mul_le {k : ℕ} (g : Fin r → ComplexModel n → ℂ)
    (β : Fin k → Fin r) (c : ℝ) (h : ComplexModel n → ℂ) (y : ComplexModel n) :
    multiplierDensity (generatorLog g) ((k : ℝ) + c) (fun z => (∏ i, g (β i) z) * h z) y ≤
      multiplierDensity (generatorLog g) c h y := by
  by_cases hy : ∃ j, g j y ≠ 0
  · have hlog := generatorLog_of_nonzero hy
    set S := generatorNormSq g y with hS
    have hSpos : 0 < S := by
      obtain ⟨j, hj⟩ := hy
      rw [hS, generatorNormSq]
      exact lt_of_lt_of_le (by positivity) (Finset.single_le_sum
        (f := fun j => ‖g j y‖ ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ j))
    simp only [multiplierDensity, hlog, multiplierWeight_coe]
    rw [← ENNReal.ofReal_mul (sq_nonneg _), ← ENNReal.ofReal_mul (sq_nonneg _)]
    apply ENNReal.ofReal_le_ofReal
    have hprod := norm_sq_prod_le g β y
    rw [← generatorNormSq] at hprod
    have hexp : Real.exp (-(((k : ℝ) + c) * Real.log S)) =
        (S ^ k)⁻¹ * Real.exp (-(c * Real.log S)) := by
      rw [show -(((k : ℝ) + c) * Real.log S) = -((k : ℝ) * Real.log S) + -(c * Real.log S) by
        ring, Real.exp_add, ← Real.log_pow, Real.exp_neg, Real.exp_log (pow_pos hSpos k)]
    rw [hexp, norm_mul, mul_pow]
    have hSk : 0 < S ^ k := pow_pos hSpos k
    calc ‖∏ i, g (β i) y‖ ^ 2 * ‖h y‖ ^ 2 * ((S ^ k)⁻¹ * Real.exp (-(c * Real.log S)))
        ≤ S ^ k * ‖h y‖ ^ 2 * ((S ^ k)⁻¹ * Real.exp (-(c * Real.log S))) := by
          gcongr
      _ = ‖h y‖ ^ 2 * Real.exp (-(c * Real.log S)) := by
          field_simp
  · push Not at hy
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      simp
    · have h0 : ∏ i, g (β i) y = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ ⟨0, hk⟩) (hy _)
      simp [multiplierDensity, h0]

/-- One generator monomial times an element of `𝓘(cφ)_x` lies in `𝓘((k + c)φ)_x`. -/
theorem multiplierIntegrableAt_prod_mul {k : ℕ} {g : Fin r → ComplexModel n → ℂ}
    {x : ComplexModel n} (hg : HolomorphicGeneratorsAt g x) (β : Fin k → Fin r) {c : ℝ}
    {h : ComplexModel n → ℂ} (hh : MultiplierIntegrableAt (generatorLog g) c h x volume) :
    MultiplierIntegrableAt (generatorLog g) ((k : ℝ) + c) (fun z => (∏ i, g (β i) z) * h z) x
      volume := by
  obtain ⟨hc, U, hU, hxU, hhol, hint⟩ := hh
  obtain ⟨V, hV, hxV, hgV⟩ := hg
  have hprod : DifferentiableOn ℂ (fun z => ∏ i, g (β i) z) (U ∩ V) := by
    have h := Finset.prod_induction (fun i => g (β i))
      (fun F : ComplexModel n → ℂ => DifferentiableOn ℂ F (U ∩ V))
      (fun a b ha hb => ha.mul hb) (differentiableOn_const 1)
      (fun i _ => (hgV (β i)).mono inter_subset_right) (s := Finset.univ)
    convert h using 1
    funext z
    simp [Finset.prod_apply]
  have hhol' : DifferentiableOn ℂ (fun z => (∏ i, g (β i) z) * h z) (U ∩ V) :=
    hprod.mul (hhol.mono inter_subset_left)
  refine ⟨by positivity, U ∩ V, hU.inter hV, ⟨hxU, hxV⟩, hhol', ?_⟩
  refine ⟨aemeasurable_multiplierDensity_generatorLog (hU.inter hV)
    (fun i => (hgV i).continuousOn.mono inter_subset_right)
    (ne_of_gt (by positivity : (0 : ℝ) < (k : ℝ) + c)) hhol'.continuousOn, ?_⟩
  calc (∫⁻ y in U ∩ V, multiplierDensity (generatorLog g) ((k : ℝ) + c)
        (fun z => (∏ i, g (β i) z) * h z) y)
      ≤ ∫⁻ y in U ∩ V, multiplierDensity (generatorLog g) c h y :=
        lintegral_mono fun y => multiplierDensity_prod_mul_le g β c h y
    _ ≤ ∫⁻ y in U, multiplierDensity (generatorLog g) c h y :=
        lintegral_mono_set inter_subset_left
    _ < ⊤ := hint.2

/-- Finite sums stay in `𝓘(cφ)_x`. -/
theorem multiplierIntegrableAt_finset_sum {g : Fin r → ComplexModel n → ℂ}
    {x : ComplexModel n} (hg : HolomorphicGeneratorsAt g x) {c : ℝ} (hc : 0 < c)
    {ι : Type*} (s : Finset ι) {F : ι → ComplexModel n → ℂ}
    (hF : ∀ i ∈ s, MultiplierIntegrableAt (generatorLog g) c (F i) x volume) :
    MultiplierIntegrableAt (generatorLog g) c (fun z => ∑ i ∈ s, F i z) x volume := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using multiplierIntegrableAt_zero (generatorLog g) hc x volume
  | insert a s has ih =>
    have h1 := hF a (Finset.mem_insert_self a s)
    have h2 := ih fun i hi => hF i (Finset.mem_insert_of_mem hi)
    have := SGPT.Foundations.Analysis.Pending.multiplierIntegrableAt_add
      (quasiPlurisubharmonicAt_generatorLog hg) h1 h2
    simpa [Finset.sum_insert has] using this

/-- **The easy inclusion** (`skoda:easy-inclusion`): `J^k · 𝓘(cφ)_x ⊆ 𝓘((k + c)φ)_x`. -/
theorem multiplierIntegrableAt_of_memPowMulMultiplierAt {g : Fin r → ComplexModel n → ℂ}
    {x : ComplexModel n} (hg : HolomorphicGeneratorsAt g x) {k : ℕ} {c : ℝ} (hc : 0 < c)
    {f : ComplexModel n → ℂ} (hf : MemPowMulMultiplierAt g k c x f) :
    MultiplierIntegrableAt (generatorLog g) ((k : ℝ) + c) f x volume := by
  obtain ⟨h, hh, heq⟩ := hf
  have hsum := multiplierIntegrableAt_finset_sum hg (by positivity : (0 : ℝ) < (k : ℝ) + c)
    Finset.univ (fun β _ => multiplierIntegrableAt_prod_mul hg β (hh β))
  exact hsum.congr (Filter.Eventually.of_forall fun _ => rfl) heq.symm

/-- `J^0 · 𝓘(cφ)_x = 𝓘(cφ)_x`. -/
theorem memPowMulMultiplierAt_zero_iff {g : Fin r → ComplexModel n → ℂ} {x : ComplexModel n}
    {c : ℝ} {f : ComplexModel n → ℂ} :
    MemPowMulMultiplierAt g 0 c x f ↔ MultiplierIntegrableAt (generatorLog g) c f x volume := by
  constructor
  · rintro ⟨h, hh, heq⟩
    refine (hh Fin.elim0).congr (Filter.Eventually.of_forall fun _ => rfl) ?_
    filter_upwards [heq] with z hz
    rw [hz]
    simp [Unique.eq_default (α := Fin 0 → Fin r)]
  · intro hf
    refine ⟨fun _ => f, fun _ => hf, Filter.Eventually.of_forall fun z => ?_⟩
    simp

/-- Multiplying `J^k · 𝓘(cφ)_x` by `J` lands in `J^{k+1} · 𝓘(cφ)_x`. -/
theorem memPowMulMultiplierAt_succ {g : Fin r → ComplexModel n → ℂ} {x : ComplexModel n}
    {k : ℕ} {c : ℝ} {f : ComplexModel n → ℂ} {h : Fin r → ComplexModel n → ℂ}
    (hh : ∀ i, MemPowMulMultiplierAt g k c x (h i))
    (hf : f =ᶠ[𝓝 x] fun z => ∑ i, g i z * h i z) :
    MemPowMulMultiplierAt g (k + 1) c x f := by
  choose H hH hHeq using hh
  refine ⟨fun β => H (β 0) (Fin.tail β), fun β => hH _ _, ?_⟩
  have hall : ∀ᶠ z in 𝓝 x, ∀ i, h i z = ∑ β, (∏ l, g (β l) z) * H i β z :=
    Filter.eventually_all.mpr hHeq
  filter_upwards [hf, hall] with z hz hz'
  rw [hz]
  simp_rw [hz', Finset.mul_sum]
  rw [← (Fin.consEquiv fun _ => Fin r).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun β _ => ?_
  simp only [Fin.consEquiv, Equiv.coe_fn_mk, Fin.prod_univ_succ, Fin.cons_zero, Fin.tail_cons,
    Fin.cons_succ]
  ring

/-- **Skoda's theorem from one division step** (`skoda:main`, induction on `k`). -/
theorem skodaStatement_of_division (hdiv : SkodaDivisionStatement) : SkodaStatement := by
  intro n r hn g x hg m k hm
  induction k with
  | zero =>
    intro f
    rw [memPowMulMultiplierAt_zero_iff]
    simp
  | succ k ih =>
    intro f
    constructor
    · intro hf
      have hf' : MultiplierIntegrableAt (generatorLog g) (((k + m : ℕ) + 1 : ℕ) : ℝ) f x
          volume := by
        convert hf using 2
        ring_nf
      obtain ⟨h, hh, heq⟩ := hdiv n r hn g x hg (k + m) (by omega) f hf'
      exact memPowMulMultiplierAt_succ (fun i => (ih (h i)).mp (hh i)) heq
    · intro hf
      have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
      have := multiplierIntegrableAt_of_memPowMulMultiplierAt hg hm0 hf
      convert this using 2
      push_cast; ring

end SGPT.Okounkov.TranscendentalSkoda
