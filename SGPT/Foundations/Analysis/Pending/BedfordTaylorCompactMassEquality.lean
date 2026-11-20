import SGPT.Foundations.Analysis.Pending.BedfordTaylorIncreasingStepP
import SGPT.Foundations.Analysis.Pending.BedfordTaylorCapacity
import SGPT.Foundations.Analysis.Pending.BedfordTaylorMaxObstacle
import SGPT.Foundations.Analysis.Pending.VaguePortmanteau

set_option autoImplicit false

/-!
# Local Stokes: two potentials agreeing off a compact set carry the same mass

Let `a, b` be locally bounded plurisubharmonic functions on an open `Ω ⊆ ℂⁿ`
which agree outside a compact `K ⊆ Ω`.  Then their Monge--Ampère measures agree
on every open `V` with `K ⊆ V ⋐ Ω`:

  `(ddᶜa)ⁿ(V) = (ddᶜb)ⁿ(V)`.

This is the Stokes step of Błocki's proof of the local domination principle
(*The complex Monge--Ampère operator in pluripotential theory*, lecture notes,
Theorem 2.2.6, p. 46), where it is used for `a = max(u + ε, v)` and `b = u + ε`
on `Ω₀ = {u < v}`: the two agree off the compact `{u + ε ≤ v}`.

The proof is the usual telescoping over the `n` slots.  Fix a smooth cutoff `φ`
which is `1` on a neighbourhood of `V` and compactly supported in `Ω`, and let
`μ_k` be the Bedford--Taylor measure of the tuple carrying `a` in the slots of
index `< k` and `b` in the rest.  Swapping one slot changes the test integral by
the *slot defect* of `Pending.BedfordTaylorSlotStokes*,

  `∫ φ dμ_{k+1} - ∫ φ dμ_k = ∫ χ (a - b) dν₁ - ∫ χ (a - b) dν₂`,

with `ν₁, ν₂` the limits carrying `φ + p` resp. `p` in that slot.  On `V` the
function `φ` is the *constant* `1`, so `ν₁` and `ν₂` agree there
(`IsBTLimit.update_const_add`), while `χ (a - b)` vanishes off `V`; the defect is
therefore zero, and `∫ φ dμ_n = ∫ φ dμ_0`, i.e. `∫ φ (ddᶜa)ⁿ = ∫ φ (ddᶜb)ⁿ`.
Splitting that integral at `K`, where `φ ≡ 1`, and using that the two measures
agree on the open set `Ω \ K` (locality) gives `(ddᶜa)ⁿ(K) = (ddᶜb)ⁿ(K)` and
hence the statement on `V`.

Nothing here assumes a boundary condition: the hypothesis is only that the two
potentials agree off a compact subset of the domain.
-/

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ContDiff ComplexOrder

namespace SGPT.Foundations.Analysis.Pending.BedfordTaylor

open FirstPass FirstPass.MongeAmpere FirstPass.MixedMongeAmpere

variable {n : ℕ}

/-! ## The hybrid tuple -/

/-- The tuple carrying `a` in the slots of index below `k` and `b` in the rest. -/
def hybridTuple (a b : ComplexModel n → ℝ) (k : ℕ) : Fin n → ComplexModel n → ℝ :=
  fun i ↦ if (i : ℕ) < k then a else b

theorem hybridTuple_zero (a b : ComplexModel n → ℝ) :
    hybridTuple a b 0 = fun _ ↦ b := by
  funext i; simp [hybridTuple]

theorem hybridTuple_top (a b : ComplexModel n → ℝ) :
    hybridTuple (n := n) a b n = fun _ ↦ a := by
  funext i; simp [hybridTuple, i.isLt]

theorem hybridTuple_apply_self (a b : ComplexModel n → ℝ) {k : ℕ} (hk : k < n) :
    hybridTuple a b k ⟨k, hk⟩ = b := by
  simp [hybridTuple]

theorem hybridTuple_succ (a b : ComplexModel n → ℝ) {k : ℕ} (hk : k < n) :
    hybridTuple a b (k + 1) = Function.update (hybridTuple a b k) ⟨k, hk⟩ a := by
  classical
  funext i
  by_cases h : i = ⟨k, hk⟩
  · subst h; simp [hybridTuple]
  · have hik : (i : ℕ) ≠ k := fun h' ↦ h (Fin.ext h')
    simp only [hybridTuple, Function.update_of_ne h]
    by_cases hlt : (i : ℕ) < k
    · simp [hlt, show (i : ℕ) < k + 1 by omega]
    · simp [hlt, show ¬ (i : ℕ) < k + 1 by omega]

theorem hybridTuple_update_self (a b : ComplexModel n → ℝ) {k : ℕ} (hk : k < n) :
    Function.update (hybridTuple a b k) ⟨k, hk⟩ b = hybridTuple a b k := by
  classical
  funext i
  by_cases h : i = ⟨k, hk⟩
  · subst h; simp [hybridTuple]
  · simp [Function.update_of_ne h]

theorem isLocallyBoundedPshOn_hybridTuple {Ω : Opens (ComplexModel n)}
    {a b : ComplexModel n → ℝ} (ha : IsLocallyBoundedPshOn Ω a)
    (hb : IsLocallyBoundedPshOn Ω b) (k : ℕ) (i : Fin n) :
    IsLocallyBoundedPshOn Ω (hybridTuple a b k i) := by
  by_cases h : (i : ℕ) < k <;> simp [hybridTuple, h, ha, hb]

/-! ## The slot swap -/

/-- A nonnegative multiple of `‖z‖²` is smooth with positive semidefinite Hessian. -/
theorem isSmoothPsdOn_const_mul_norm_sq {C : ℝ} (hC : 0 ≤ C) :
    IsSmoothPsdOn (⊤ : Opens (ComplexModel n)) fun z ↦ C * ‖z‖ ^ 2 := by
  have h2 : (2 : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
  refine ⟨(contDiff_const.mul (contDiff_norm_sq ℝ)).contDiffOn, fun z _ ↦ ?_⟩
  have hsplit : (fun z : ComplexModel n ↦ C * ‖z‖ ^ 2) =
      C • fun z : ComplexModel n ↦ ‖z‖ ^ 2 := by
    funext y; simp
  rw [hsplit, complexHessian_smul ((contDiff_norm_sq ℝ).contDiffAt.of_le h2),
    complexHessian_norm_sq]
  exact Matrix.PosSemidef.one.smul (by exact_mod_cast hC)

/-- **One slot swapped, no change in the test integral.**  If the test function `φ`
is the constant `1` on an open `V` off which `a` and `b` agree, then replacing `a`
by `b` in one slot does not change `∫ φ`. -/
theorem integral_eq_of_slot_swap {Ω : Opens (ComplexModel n)}
    {v : Fin n → ComplexModel n → ℝ} (i₀ : Fin n)
    {a b φ : ComplexModel n → ℝ} {μa μb : Measure (ComplexModel n)}
    (ha : IsLocallyBoundedPshOn Ω a) (hb : IsLocallyBoundedPshOn Ω b)
    (hμa : IsBTLimit Ω (Function.update v i₀ a) μa)
    (hμb : IsBTLimit Ω (Function.update v i₀ b) μb)
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφΩ : tsupport φ ⊆ (Ω : Set (ComplexModel n)))
    {V : Opens (ComplexModel n)} (hVΩ : V ≤ Ω)
    (hφV : ∀ z ∈ (V : Set (ComplexModel n)), φ z = 1)
    (hab : ∀ z ∈ (Ω : Set (ComplexModel n)), z ∉ (V : Set (ComplexModel n)) → a z = b z) :
    (∫ z, φ z ∂μa) = ∫ z, φ z ∂μb := by
  classical
  obtain ⟨C, hC0, hCpsd⟩ := exists_isSmoothPsdOn_add_norm_sq hφ hφc
  obtain ⟨ν₁, hν₁⟩ := hμa.exists_update_smoothPsd i₀ (hCpsd.mono le_top)
  obtain ⟨ν₂, hν₂⟩ := hμa.exists_update_smoothPsd i₀
    ((isSmoothPsdOn_const_mul_norm_sq hC0).mono le_top)
  obtain ⟨χ, hχ1, hχ01⟩ := exists_testFunction_eq_one_nhds_compact hφc hφΩ
  have hid := integral_sub_eq_slotDefect_of_eventuallyEq_one i₀ ha hb hμa hμb hν₁ hν₂
    hφ hφc hφΩ χ.continuous χ.hasCompactSupport χ.tsupport_subset hχ1
  have hzero : ∀ z ∉ (V : Set (ComplexModel n)), χ z * (a z - b z) = 0 := by
    intro z hz
    by_cases hzΩ : z ∈ (Ω : Set (ComplexModel n))
    · rw [hab z hzΩ hz]; ring
    · rw [image_eq_zero_of_notMem_tsupport fun h ↦ hzΩ (χ.tsupport_subset h)]; ring
  have hres : ν₁.restrict (V : Set (ComplexModel n)) = ν₂.restrict (V : Set (ComplexModel n)) := by
    refine hν₁.restrict_eq_of_eqOn (hν₂.update_const_add i₀ 1) hVΩ ?_
    intro i z hz
    by_cases h : i = i₀
    · subst h; simp only [Function.update_self]; rw [hφV z hz]
    · simp [Function.update_of_ne h]
  have hdef : (∫ z, χ z * (a z - b z) ∂ν₁) = ∫ z, χ z * (a z - b z) ∂ν₂ := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (μ := ν₁) hzero,
      ← setIntegral_eq_integral_of_forall_compl_eq_zero (μ := ν₂) hzero, hres]
  rw [hdef, sub_self] at hid
  exact sub_eq_zero.mp hid

/-! ## Telescoping over the slots -/

theorem integral_hybrid_eq {Ω : Opens (ComplexModel n)}
    {a b φ : ComplexModel n → ℝ}
    (ha : IsLocallyBoundedPshOn Ω a) (hb : IsLocallyBoundedPshOn Ω b)
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφΩ : tsupport φ ⊆ (Ω : Set (ComplexModel n)))
    {V : Opens (ComplexModel n)} (hVΩ : V ≤ Ω)
    (hφV : ∀ z ∈ (V : Set (ComplexModel n)), φ z = 1)
    (hab : ∀ z ∈ (Ω : Set (ComplexModel n)), z ∉ (V : Set (ComplexModel n)) → a z = b z) :
    ∀ k, k ≤ n → ∀ μk μ0 : Measure (ComplexModel n),
      IsBTLimit Ω (hybridTuple a b k) μk → IsBTLimit Ω (hybridTuple a b 0) μ0 →
      (∫ z, φ z ∂μk) = ∫ z, φ z ∂μ0 := by
  intro k
  induction k with
  | zero => intro _ μk μ0 hμk hμ0; rw [hμk.unique hμ0]
  | succ k ih =>
    intro hk μk1 μ0 hμk1 hμ0
    have hkn : k < n := hk
    obtain ⟨μk, hμk⟩ := exists_isBTLimit_of_isLocallyBoundedPshOn
      (u := hybridTuple a b k) (isLocallyBoundedPshOn_hybridTuple ha hb k)
    have hμk1' : IsBTLimit Ω (Function.update (hybridTuple a b k) ⟨k, hkn⟩ a) μk1 := by
      rwa [hybridTuple_succ a b hkn] at hμk1
    have hμk' : IsBTLimit Ω (Function.update (hybridTuple a b k) ⟨k, hkn⟩ b) μk := by
      rwa [hybridTuple_update_self a b hkn]
    rw [integral_eq_of_slot_swap ⟨k, hkn⟩ ha hb hμk1' hμk' hφ hφc hφΩ hVΩ hφV hab]
    exact ih hkn.le μk μ0 hμk hμ0

/-! ## The mass equality -/

/-- **The local Stokes mass equality.**  Two locally bounded plurisubharmonic
functions on `Ω` which agree off a compact `K ⊆ Ω` have the same Monge--Ampère
mass on every open `V` with `K ⊆ V ⋐ Ω`. -/
theorem measure_eq_of_eqOn_compl
    {Ω V : Opens (ComplexModel n)} {a b : ComplexModel n → ℝ}
    (ha : IsLocallyBoundedPshOn Ω a) (hb : IsLocallyBoundedPshOn Ω b)
    (hV : RelativelyCompactIn V Ω) {K : Set (ComplexModel n)} (hK : IsCompact K)
    (hKV : K ⊆ (V : Set (ComplexModel n)))
    (hab : ∀ z ∈ (Ω : Set (ComplexModel n)), z ∉ K → a z = b z)
    {μa μb : Measure (ComplexModel n)}
    (hBTa : IsBTLimit Ω (fun _ ↦ a) μa) (hBTb : IsBTLimit Ω (fun _ ↦ b) μb) :
    μa (V : Set (ComplexModel n)) = μb (V : Set (ComplexModel n)) := by
  classical
  have hVΩ : V ≤ Ω := subset_closure.trans hV.2
  -- an open `W` between `closure V` and `Ω`
  obtain ⟨W, hWo, hVW, hWΩ, hWc⟩ :=
    exists_open_between_and_isCompact_closure hV.1 Ω.isOpen hV.2
  -- the cutoff
  obtain ⟨φ, hφ1, hφ01⟩ :=
    exists_testFunction_eq_one_nhds_compact (Ω := (⟨W, hWo⟩ : Opens (ComplexModel n)))
      hV.1 hVW
  have hφΩ : tsupport ⇑φ ⊆ (Ω : Set (ComplexModel n)) :=
    φ.tsupport_subset.trans (subset_closure.trans hWΩ)
  have hφV : ∀ z ∈ (V : Set (ComplexModel n)), φ z = 1 := fun z hz ↦
    (hφ1.filter_mono (nhds_le_nhdsSet (subset_closure hz))).self_of_nhds
  have habV : ∀ z ∈ (Ω : Set (ComplexModel n)), z ∉ (V : Set (ComplexModel n)) →
      a z = b z := fun z hz hzV ↦ hab z hz fun hzK ↦ hzV (hKV hzK)
  -- the telescoped test-integral identity
  have hint : (∫ z, φ z ∂μa) = ∫ z, φ z ∂μb := by
    have h := integral_hybrid_eq ha hb φ.contDiff φ.hasCompactSupport hφΩ hVΩ hφV habV
      n le_rfl μa μb (by rwa [hybridTuple_top]) (by rwa [hybridTuple_zero])
    exact h
  -- locality off `K`
  have hKclosed : IsClosed K := hK.isClosed
  have hKmeas : MeasurableSet K := hKclosed.measurableSet
  have hΩ'Ω : (⟨(Ω : Set (ComplexModel n)) \ K, Ω.isOpen.sdiff hKclosed⟩ :
      Opens (ComplexModel n)) ≤ Ω := fun z hz ↦ hz.1
  have hloc : μa.restrict ((Ω : Set (ComplexModel n)) \ K) =
      μb.restrict ((Ω : Set (ComplexModel n)) \ K) :=
    hBTa.restrict_eq_of_eqOn hBTb hΩ'Ω fun _ z hz ↦ hab z hz.1 hz.2
  -- off `K` we may as well integrate over `Ω \ K`
  have hcompl : ∀ ρ : Measure (ComplexModel n), ρ ((Ω : Set (ComplexModel n)))ᶜ = 0 →
      ρ.restrict Kᶜ = ρ.restrict ((Ω : Set (ComplexModel n)) \ K) := by
    intro ρ hρ
    refine Measure.restrict_congr_set ?_
    refine (ae_eq_set (μ := ρ)).2 ⟨?_, ?_⟩
    · refine measure_mono_null (fun z hz ↦ ?_) hρ
      obtain ⟨hzK, hz⟩ := hz
      exact fun hzΩ ↦ hz ⟨hzΩ, hzK⟩
    · rw [sdiff_eq_empty.2 fun z hz ↦ hz.2]; simp
  -- integrability of the cutoff
  have hIa : Integrable (⇑φ) μa :=
    VaguePortmanteau.integrable_of_tsupport_subset hBTa.2.1 φ.continuous
      φ.hasCompactSupport hφΩ
  have hIb : Integrable (⇑φ) μb :=
    VaguePortmanteau.integrable_of_tsupport_subset hBTb.2.1 φ.continuous
      φ.hasCompactSupport hφΩ
  -- the integral over `K`, where the cutoff is one
  have hKint : ∀ ρ : Measure (ComplexModel n),
      (∫ z in K, φ z ∂ρ) = (ρ K).toReal := by
    intro ρ
    rw [setIntegral_congr_fun hKmeas (g := fun _ ↦ (1 : ℝ))
      (fun z hz ↦ hφV z (hKV hz)), setIntegral_const]
    simp [Measure.real]
  -- mass of `K`
  have hKfin_a : μa K ≠ ⊤ := (hBTa.2.1 K hK (hKV.trans hVΩ)).ne
  have hKfin_b : μb K ≠ ⊤ := (hBTb.2.1 K hK (hKV.trans hVΩ)).ne
  have hKmass : μa K = μb K := by
    have ha' := MeasureTheory.integral_add_compl hKmeas hIa
    have hb' := MeasureTheory.integral_add_compl hKmeas hIb
    have hoff : (∫ z, φ z ∂(μa.restrict Kᶜ)) = ∫ z, φ z ∂(μb.restrict Kᶜ) := by
      rw [hcompl μa hBTa.1, hcompl μb hBTb.1, hloc]
    have htot := ha'.trans (hint.trans hb'.symm)
    rw [hoff] at htot
    have e : (∫ z in K, φ z ∂μa) = ∫ z in K, φ z ∂μb := add_right_cancel htot
    rw [hKint μa, hKint μb] at e
    exact (ENNReal.toReal_eq_toReal_iff' hKfin_a hKfin_b).mp e
  -- transport from `K` to `V`
  have hVK : (V : Set (ComplexModel n)) \ K ⊆ (Ω : Set (ComplexModel n)) \ K :=
    fun z hz ↦ ⟨hVΩ hz.1, hz.2⟩
  have hVKmeas : MeasurableSet ((V : Set (ComplexModel n)) \ K) :=
    V.isOpen.measurableSet.diff hKmeas
  have hdiff : μa ((V : Set (ComplexModel n)) \ K) = μb ((V : Set (ComplexModel n)) \ K) := by
    have ea := Measure.restrict_apply (μ := μa) (s := (Ω : Set (ComplexModel n)) \ K) hVKmeas
    have eb := Measure.restrict_apply (μ := μb) (s := (Ω : Set (ComplexModel n)) \ K) hVKmeas
    rw [inter_eq_left.2 hVK] at ea eb
    rw [← ea, ← eb, hloc]
  have hVsplit : ∀ ρ : Measure (ComplexModel n),
      ρ ((V : Set (ComplexModel n))) = ρ K + ρ ((V : Set (ComplexModel n)) \ K) := by
    intro ρ
    rw [← measure_inter_add_sdiff (V : Set (ComplexModel n)) hKmeas,
      inter_eq_right.2 hKV]
  rw [hVsplit μa, hVsplit μb, hKmass, hdiff]

/-- The canonical form of the local Stokes mass equality. -/
theorem canonicalBedfordTaylorMeasure_eq_of_eqOn_compl
    {Ω V : Opens (ComplexModel n)} {a b : ComplexModel n → ℝ}
    (ha : IsLocallyBoundedPshOn Ω a) (hb : IsLocallyBoundedPshOn Ω b)
    (hV : RelativelyCompactIn V Ω) {K : Set (ComplexModel n)} (hK : IsCompact K)
    (hKV : K ⊆ (V : Set (ComplexModel n)))
    (hab : ∀ z ∈ (Ω : Set (ComplexModel n)), z ∉ K → a z = b z) :
    Pending.MongeAmpere.canonicalBedfordTaylorMeasure Ω a ha (V : Set (ComplexModel n)) =
      Pending.MongeAmpere.canonicalBedfordTaylorMeasure Ω b hb (V : Set (ComplexModel n)) :=
  measure_eq_of_eqOn_compl ha hb hV hK hKV hab
    (isBTLimit_canonicalBedfordTaylorMeasure ha) (isBTLimit_canonicalBedfordTaylorMeasure hb)

end SGPT.Foundations.Analysis.Pending.BedfordTaylor

end
