import SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorMass

/-!
# A bounded-potential cutoff estimate for actual local currents

The nearby-trace argument for Hermitian extremal functions transfers two
derivatives from the bounded potential difference to a cutoff. This file
performs that step directly on the project's genuine coefficient-current
and trace-measure representation. The differentiated multiplier can be a
signed locally bounded Borel function; it need not be plurisubharmonic.

The constant depends only on the dimension and bidimension. Geometry enters
through the cutoff's second-derivative bound and the trace mass on its
compact support. In particular, a gap of size `κ r²` cancels the `r⁻²`
cutoff bound without requiring synchronized smooth approximations.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianBalayage

open Set Filter MeasureTheory TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open StronglyPositiveForms LocalProductCurrents LocalBedfordTaylorProducts
  LocalBedfordTaylorMass
open scoped Topology Distributions ContDiff

variable {n : ℕ} {Ω : Opens (ComplexModel n)}

private theorem locallyBounded_sub {u v : ComplexModel n → ℝ}
    (hu : IsLocallyBoundedOn u Ω) (hv : IsLocallyBoundedOn v Ω) :
    IsLocallyBoundedOn (u - v) Ω := by
  intro K hK hKΩ
  obtain ⟨A, hA⟩ := hu K hK hKΩ
  obtain ⟨B, hB⟩ := hv K hK hKΩ
  refine ⟨A + B, fun x hx => ?_⟩
  exact (abs_sub_le (u x) 0 (v x)).trans (by simpa using add_le_add (hA x hx) (hB x hx))

/-- The actual recursively differentiated current is linear in a signed
locally bounded Borel multiplier. -/
theorem ddcMul_sub {m : ℕ} {R : LocalProductCurrent n Ω (m + 1)} (hR : IsPositive R)
    {u v : ComplexModel n → ℝ} (hu : Measurable u) (hub : IsLocallyBoundedOn u Ω)
    (hv : Measurable v) (hvb : IsLocallyBoundedOn v Ω) :
    ddcMul R (u - v) = ddcMul R u - ddcMul R v := by
  let a := (Ω : Set (ComplexModel n)).indicator u
  let b := (Ω : Set (ComplexModel n)).indicator v
  have ha : Measurable a := hu.indicator Ω.isOpen.measurableSet
  have hb : Measurable b := hv.indicator Ω.isOpen.measurableSet
  have hab : IsLocallyBoundedOn a Ω := by
    intro K hK hKΩ
    obtain ⟨A, hA⟩ := hub K hK hKΩ
    exact ⟨A, fun x hx => by simpa only [a, Set.indicator_of_mem (hKΩ hx)] using hA x hx⟩
  have hbb : IsLocallyBoundedOn b Ω := by
    intro K hK hKΩ
    obtain ⟨B, hB⟩ := hvb K hK hKΩ
    exact ⟨B, fun x hx => by simpa only [b, Set.indicator_of_mem (hKΩ hx)] using hB x hx⟩
  have hmul : mulBorel R (a - b) = mulBorel R a - mulBorel R b := by
    ext γ φ
    rw [mulBorel_apply hR (ha.sub hb) (locallyBounded_sub hab hbb),
      LinearMap.sub_apply, _root_.sub_apply, mulBorel_apply hR ha hab,
      mulBorel_apply hR hb hbb, ← integral_sub (hR.integrable_mul_density ha hab γ φ)
        (hR.integrable_mul_density hb hbb γ φ)]
    congr 1
    funext x
    simp only [Pi.sub_apply]
    ring
  have hind : (Ω : Set (ComplexModel n)).indicator (u - v) = a - b := by
    funext x
    by_cases hx : x ∈ (Ω : Set (ComplexModel n)) <;> simp [a, b, hx]
  rw [ddcMul, hind, hmul]
  rw [sub_eq_add_neg, ← neg_one_smul ℝ (mulBorel R b), ddc_add, ddc_smul]
  simp only [neg_one_smul, sub_eq_add_neg]
  rfl

/-- A bounded signed potential paired with two derivatives of a cutoff is
controlled by the actual trace measure of the positive current. No positivity
or closedness of the differentiated signed current is assumed. -/
theorem exists_abs_ddcMul_cutoff_le (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Ω : Opens (ComplexModel n)) (R : LocalProductCurrent n Ω (m + 1)) (hR : IsPositive R)
        (u : ComplexModel n → ℝ), Measurable u → IsLocallyBoundedOn u Ω →
        ∀ (χ : 𝓓(Ω, ℝ)) (K : Set (ComplexModel n)),
          IsCompact K → K ⊆ Ω → tsupport χ ⊆ K →
          ∀ B ε : ℝ, 0 ≤ B → 0 ≤ ε →
            (∀ a b x, |dTest (realBasis n b) (dTest (realBasis n a) χ) x| ≤ B) →
            (∀ x ∈ K, |u x| ≤ ε) →
            |(ddcMul R u) (kahlerPower n m) χ| ≤
              C * B * ε * (hR.traceMeasure K).toReal := by
  classical
  let γ : Fin (n * 2) → Fin (n * 2) → formSpan n (m + 1) := fun a b =>
    wedgeLM m (isOneOne_coeffForm a b) (kahlerPower n m)
  have hord : ∀ a b, ∃ C : ℝ, 0 ≤ C ∧
      C • formPower (kahlerForm n) (m + 1) -
          (γ a b : RealForm n (2 * (m + 1))) ∈ spCone (m + 1) ∧
      C • formPower (kahlerForm n) (m + 1) +
          (γ a b : RealForm n (2 * (m + 1))) ∈ spCone (m + 1) :=
    fun a b => exists_orderUnit (γ a b).2
  choose Cγ hCγ0 hCγ1 hCγ2 using hord
  refine ⟨(1 / (4 * Real.pi)) * ∑ a, ∑ b, Cγ a b, ?_, ?_⟩
  · exact mul_nonneg (by positivity)
      (Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => hCγ0 a b)
  intro Ω R hR u hu hub χ K hK hKΩ hχK B ε hB hε hψb huε
  let ψ : Fin (n * 2) → Fin (n * 2) → 𝓓(Ω, ℝ) := fun a b =>
    dTest (realBasis n b) (dTest (realBasis n a) χ)
  have hψK : ∀ a b, tsupport (ψ a b) ⊆ K := fun a b =>
    ((tsupport_dTest_subset _ _).trans (tsupport_dTest_subset _ _)).trans hχK
  have hum : Measurable ((Ω : Set (ComplexModel n)).indicator u) :=
    hu.indicator Ω.isOpen.measurableSet
  have hubi : IsLocallyBoundedOn ((Ω : Set (ComplexModel n)).indicator u) Ω := by
    intro L hL hLΩ
    obtain ⟨M, hM⟩ := hub L hL hLΩ
    exact ⟨M, fun x hx => by simpa only [Set.indicator_of_mem (hLΩ hx)] using hM x hx⟩
  have heq : (ddcMul R u) (kahlerPower n m) χ =
      ∑ a, ∑ b, (-(1 / (4 * Real.pi))) *
        ∫ x, ψ a b x * ((Ω : Set (ComplexModel n)).indicator u x * hR.density (γ a b) x)
          ∂hR.traceMeasure := by
    rw [ddcMul, ddc_apply_apply]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [mulBorel_apply hR hum hubi]
  have hterm : ∀ a b,
      |∫ x, ψ a b x * ((Ω : Set (ComplexModel n)).indicator u x * hR.density (γ a b) x)
          ∂hR.traceMeasure| ≤ B * (ε * Cγ a b) * (hR.traceMeasure K).toReal := by
    intro a b
    have hKfin : hR.traceMeasure K < ⊤ := hR.traceMeasure_lt_top hK hKΩ
    have hbd := abs_density_le_of_orderUnit hR (γ a b) (hCγ1 a b) (hCγ2 a b)
    have hI : ∫ x, K.indicator (fun _ => B * (ε * Cγ a b)) x ∂hR.traceMeasure =
        B * (ε * Cγ a b) * (hR.traceMeasure K).toReal := by
      rw [integral_indicator_const _ hK.measurableSet, smul_eq_mul, Measure.real, mul_comm]
    rw [← Real.norm_eq_abs, ← hI]
    refine norm_integral_le_of_norm_le ((integrable_indicator_iff hK.measurableSet).mpr
      (integrableOn_const hKfin.ne)) ?_
    filter_upwards [hbd] with x hx
    by_cases hxK : x ∈ K
    · rw [Set.indicator_of_mem hxK, Set.indicator_of_mem (hKΩ hxK), norm_mul, norm_mul,
        Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs]
      exact mul_le_mul (hψb a b x)
        (mul_le_mul (huε x hxK) hx (abs_nonneg _) hε)
        (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hB
    · have hψ0 : ψ a b x = 0 :=
        image_eq_zero_of_notMem_tsupport fun h => hxK (hψK a b h)
      simp [hψ0, Set.indicator_of_notMem hxK]
  calc |(ddcMul R u) (kahlerPower n m) χ|
      = |∑ a, ∑ b, (-(1 / (4 * Real.pi))) *
          ∫ x, ψ a b x * ((Ω : Set (ComplexModel n)).indicator u x * hR.density (γ a b) x)
            ∂hR.traceMeasure| := congrArg abs heq
    _ ≤ ∑ a, ∑ b, (1 / (4 * Real.pi)) *
          (B * (ε * Cγ a b) * (hR.traceMeasure K).toReal) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ =>
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b _ => ?_))
      rw [abs_mul, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 1 / (4 * Real.pi))]
      exact mul_le_mul_of_nonneg_left (hterm a b) (by positivity)
    _ = ((1 / (4 * Real.pi)) * ∑ a, ∑ b, Cγ a b) * B * ε *
          (hR.traceMeasure K).toReal := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      ring

/-- Radius cancellation for a bounded signed multiplier and an actual
positive local current. -/
theorem exists_abs_ddcMul_cutoff_le_scaled (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Ω : Opens (ComplexModel n)) (R : LocalProductCurrent n Ω (m + 1)) (hR : IsPositive R)
        (u : ComplexModel n → ℝ), Measurable u → IsLocallyBoundedOn u Ω →
        ∀ (χ : 𝓓(Ω, ℝ)) (K : Set (ComplexModel n)),
          IsCompact K → K ⊆ Ω → tsupport χ ⊆ K →
          ∀ r B κ : ℝ, r ≠ 0 → 0 ≤ B → 0 ≤ κ →
            (∀ a b x, |dTest (realBasis n b) (dTest (realBasis n a) χ) x| ≤ B / r ^ 2) →
            (∀ x ∈ K, |u x| ≤ κ * r ^ 2) →
            |(ddcMul R u) (kahlerPower n m) χ| ≤
              C * B * κ * (hR.traceMeasure K).toReal := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_ddcMul_cutoff_le (n := n) m
  refine ⟨C, hC0, ?_⟩
  intro Ω R hR u hu hub χ K hK hKΩ hχK r B κ hr hB hκ hψ huκ
  have h := hC Ω R hR u hu hub χ K hK hKΩ hχK (B / r ^ 2) (κ * r ^ 2)
    (div_nonneg hB (sq_nonneg r)) (mul_nonneg hκ (sq_nonneg r)) hψ huκ
  have hscale : C * (B / r ^ 2) * (κ * r ^ 2) = C * B * κ := by
    field_simp [hr]
  simpa only [hscale] using h

/-- The actual one-slot nearby-trace recurrence. The two differentiated
currents and every mass in the conclusion are genuine Bedford--Taylor
current traces; no mass comparison is a caller premise. -/
theorem exists_one_slot_trace_mass_le (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Ω : Opens (ComplexModel n)) (R : LocalProductCurrent n Ω (m + 1)) (hR : IsPositive R)
        (hRc : IsClosedCurrent R) (u v : ComplexModel n → ℝ),
        Measurable u → Measurable v →
        IsLocallyBoundedOn u Ω → IsLocallyBoundedOn v Ω →
        ∀ (hu : FirstPass.MongeAmpere.IsLocallyBoundedPshOn Ω u)
          (hv : FirstPass.MongeAmpere.IsLocallyBoundedPshOn Ω v)
          (χ : 𝓓(Ω, ℝ)) (K L : Set (ComplexModel n)),
          IsCompact K → K ⊆ Ω → IsCompact L → L ⊆ K →
          tsupport χ ⊆ K → (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) →
          (∀ x ∈ L, χ x = 1) →
          ∀ B ε : ℝ, 0 ≤ B → 0 ≤ ε →
            (∀ a b x, |dTest (realBasis n b) (dTest (realBasis n a) χ) x| ≤ B) →
            (∀ x ∈ K, |v x - u x| ≤ ε) →
            (((isPositive_ddcMul hR hRc hv).1).traceMeasure L).toReal ≤
              (((isPositive_ddcMul hR hRc hu).1).traceMeasure K).toReal +
                C * B * ε * (hR.traceMeasure K).toReal := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_ddcMul_cutoff_le (n := n) m
  refine ⟨C, hC0, ?_⟩
  intro Ω R hR hRc u v hum hvm hub hvb hu hv χ K L hK hKΩ hL hLK hχK hχ01 hχ1
    B ε hB hε hψ hclose
  let Su := ddcMul R u
  let Sv := ddcMul R v
  have hSu : IsPositive Su := (isPositive_ddcMul hR hRc hu).1
  have hSv : IsPositive Sv := (isPositive_ddcMul hR hRc hv).1
  have hχint (S : LocalProductCurrent n Ω m) (hS : IsPositive S) :
      Integrable (fun x => χ x) hS.traceMeasure := by
    have h := hS.integrable_mul_of_bounded χ.continuous χ.hasCompactSupport χ.tsupport_subset
      (aestronglyMeasurable_const (b := (1 : ℝ))) ⟨1, fun _ _ => by simp⟩
    simpa using h
  have hlower : (hSv.traceMeasure L).toReal ≤ ∫ x, χ x ∂hSv.traceMeasure := by
    have hLf := hSv.traceMeasure_lt_top hL (hLK.trans hKΩ)
    rw [← Measure.real, ← integral_indicator_one hL.measurableSet]
    refine integral_mono ((integrable_indicator_iff hL.measurableSet).mpr
      (integrableOn_const hLf.ne)) (hχint Sv hSv) fun x => ?_
    by_cases hx : x ∈ L
    · simp [hx, hχ1 x hx]
    · simp [hx, (hχ01 x).1]
  have hupper : (∫ x, χ x ∂hSu.traceMeasure) ≤ (hSu.traceMeasure K).toReal := by
    have hKf := hSu.traceMeasure_lt_top hK hKΩ
    rw [← Measure.real, ← integral_indicator_one hK.measurableSet]
    refine integral_mono (hχint Su hSu) ((integrable_indicator_iff hK.measurableSet).mpr
      (integrableOn_const hKf.ne)) fun x => ?_
    by_cases hx : x ∈ K
    · simpa [hx] using (hχ01 x).2
    · have hχ0 : χ x = 0 := image_eq_zero_of_notMem_tsupport fun h => hx (hχK h)
      simp [hx, hχ0]
  have herror := hC Ω R hR (v - u) (hvm.sub hum) (locallyBounded_sub hvb hub)
    χ K hK hKΩ hχK B ε hB hε hψ hclose
  rw [ddcMul_sub hR hvm hvb hum hub, LinearMap.sub_apply, _root_.sub_apply] at herror
  have hpairu : (∫ x, χ x ∂hSu.traceMeasure) = Su (kahlerPower n m) χ :=
    hSu.integral_traceMeasure χ
  have hpairv : (∫ x, χ x ∂hSv.traceMeasure) = Sv (kahlerPower n m) χ :=
    hSv.integral_traceMeasure χ
  change (hSv.traceMeasure L).toReal ≤ (hSu.traceMeasure K).toReal +
    C * B * ε * (hR.traceMeasure K).toReal
  rw [hpairu] at hupper
  rw [hpairv] at hlower
  exact hlower.trans (by linarith [le_abs_self (Sv (kahlerPower n m) χ - Su (kahlerPower n m) χ)])

/-! ## Finite iteration of the one-slot recurrence

The index `i` records the successive nested compact sets; `j` and `m`
record the numbers of old and new potential factors. The terminal array
`J` consists of the old-potential trace masses on the largest set.
-/

/-- The weighted old-potential moments in the nearby-trace estimate. -/
def weightedTraceSum (κ : ℝ) (J : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ l ∈ Finset.range (k + 1), κ ^ (k - l) * J l

theorem weightedTraceSum_nonneg {κ : ℝ} (hκ : 0 ≤ κ) {J : ℕ → ℝ}
    (hJ : ∀ l, 0 ≤ J l) (k : ℕ) : 0 ≤ weightedTraceSum κ J k :=
  Finset.sum_nonneg fun l _ => mul_nonneg (pow_nonneg hκ _) (hJ l)

/-- The top old-potential moment is one of the nonnegative summands. -/
theorem le_weightedTraceSum {κ : ℝ} (hκ : 0 ≤ κ) {J : ℕ → ℝ}
    (hJ : ∀ l, 0 ≤ J l) (k : ℕ) : J k ≤ weightedTraceSum κ J k := by
  have h := Finset.single_le_sum
    (s := Finset.range (k + 1)) (f := fun l => κ ^ (k - l) * J l)
    (fun l _ => mul_nonneg (pow_nonneg hκ _) (hJ l))
    (Finset.mem_range.mpr (Nat.lt_succ_self k))
  simpa only [weightedTraceSum, Nat.sub_self, pow_zero, one_mul] using h

/-- A factor of the potential gap promotes the weighted trace degree by one. -/
theorem mul_weightedTraceSum_le {κ : ℝ} {J : ℕ → ℝ}
    (hJ : ∀ l, 0 ≤ J l) (k : ℕ) :
    κ * weightedTraceSum κ J k ≤ weightedTraceSum κ J (k + 1) := by
  have heq : κ * weightedTraceSum κ J k =
      ∑ l ∈ Finset.range (k + 1), κ ^ (k + 1 - l) * J l := by
    rw [weightedTraceSum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l hl => ?_
    have hlk : l ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hl)
    rw [show k + 1 - l = (k - l) + 1 by omega, pow_succ]
    ring
  rw [heq, weightedTraceSum, Finset.sum_range_succ _ (k + 1)]
  exact le_add_of_nonneg_right (by simpa only [Nat.sub_self, pow_zero, one_mul] using hJ (k + 1))

/-- Iterating the two-branch one-slot trace recurrence keeps every lower
trace moment and its correct power of the potential gap. -/
theorem trace_recursion_le_weighted_sum
    (I : ℕ → ℕ → ℕ → ℝ) (J : ℕ → ℝ) {a κ : ℝ}
    (ha : 0 ≤ a) (hκ : 0 ≤ κ) (hJ : ∀ l, 0 ≤ J l)
    (hbase : ∀ i j, I i j 0 ≤ J j)
    (hstep : ∀ i j m, I i j (m + 1) ≤
      I (i + 1) (j + 1) m + (a * κ) * I (i + 1) j m) :
    ∀ m i j, I i j m ≤ (1 + a) ^ m * weightedTraceSum κ J (j + m) := by
  intro m
  induction m with
  | zero =>
    intro i j
    simpa only [pow_zero, one_mul, Nat.add_zero] using
      (hbase i j).trans (le_weightedTraceSum hκ hJ j)
  | succ m ih =>
    intro i j
    have h1 := ih (i + 1) (j + 1)
    have h2 := ih (i + 1) j
    have hD : 0 ≤ (1 + a) ^ m := pow_nonneg (by linarith) _
    have hpromote := mul_le_mul_of_nonneg_left
      (mul_weightedTraceSum_le (κ := κ) hJ (j + m)) (mul_nonneg ha hD)
    calc I i j (m + 1)
        ≤ I (i + 1) (j + 1) m + (a * κ) * I (i + 1) j m := hstep i j m
      _ ≤ (1 + a) ^ m * weightedTraceSum κ J (j + m + 1) +
            (a * κ) * ((1 + a) ^ m * weightedTraceSum κ J (j + m)) := by
        refine add_le_add ?_ (mul_le_mul_of_nonneg_left h2 (mul_nonneg ha hκ))
        simpa only [show j + 1 + m = j + m + 1 by omega] using h1
      _ = (1 + a) ^ m * weightedTraceSum κ J (j + m + 1) +
            (a * (1 + a) ^ m) * (κ * weightedTraceSum κ J (j + m)) := by ring
      _ ≤ (1 + a) ^ m * weightedTraceSum κ J (j + m + 1) +
            (a * (1 + a) ^ m) * weightedTraceSum κ J (j + m + 1) :=
        add_le_add le_rfl hpromote
      _ = (1 + a) ^ (m + 1) * weightedTraceSum κ J (j + (m + 1)) := by
        rw [pow_succ]
        simp only [Nat.add_assoc]
        ring

/-- The complete finite trace sum has a single dimension-only coefficient.
This form, rather than the individual binomial coefficients, is used by the
frozen-coefficient mass estimate. -/
theorem trace_recursion_sum_le
    (I : ℕ → ℕ → ℕ → ℝ) (J : ℕ → ℝ) {a κ : ℝ}
    (ha : 0 ≤ a) (hκ : 0 ≤ κ) (hJ : ∀ l, 0 ≤ J l)
    (hbase : ∀ i j, I i j 0 ≤ J j)
    (hstep : ∀ i j m, I i j (m + 1) ≤
      I (i + 1) (j + 1) m + (a * κ) * I (i + 1) j m)
    (k i : ℕ) :
    (∑ j ∈ Finset.range (k + 1), I i j (k - j)) ≤
      (k + 1 : ℝ) * (1 + a) ^ k * weightedTraceSum κ J k := by
  calc (∑ j ∈ Finset.range (k + 1), I i j (k - j))
      ≤ ∑ j ∈ Finset.range (k + 1),
          (1 + a) ^ k * weightedTraceSum κ J k := by
        refine Finset.sum_le_sum fun j hj => ?_
        have hjk : j ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
        have h := trace_recursion_le_weighted_sum I J ha hκ hJ hbase hstep (k - j) i j
        rw [Nat.add_sub_of_le hjk] at h
        exact h.trans (mul_le_mul_of_nonneg_right
          (pow_le_pow_right₀ (by linarith) (Nat.sub_le k j))
          (weightedTraceSum_nonneg hκ hJ k))
    _ = (k + 1 : ℝ) * (1 + a) ^ k * weightedTraceSum κ J k := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add,
        Nat.cast_one]
      ring

end SGPT.PSH.HermitianBalayage
