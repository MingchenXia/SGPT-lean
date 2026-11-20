import SGPT.Foundations.Analysis.Pending.PolydiskSecondDifference
import SGPT.Foundations.Analysis.Pending.SemiconcaveSecondDifference

set_option autoImplicit false

/-!
# The `C^{1,1}` estimate: the Perron envelope of smooth data is semiconcave

This module supplies the one input that `Pending.PerronEnvelopeVanishingMass`
still carried as a hypothesis, namely Blocki's Theorem 2.3.2 for the unit
polydisk: the Perron--Bremermann envelope of `C²` boundary data is locally
semiconcave.

`Pending.PolydiskSecondDifference` already proves the pluripotential half —
the balanced average of the two Mobius pullbacks of the envelope is a
competitor, so

  `u(a+h) + u(a-h) - 2 u(a) ≤ 2K`

as soon as the *boundary* data satisfies the same second difference along the
family `T_{a,±h}` with constant `2K`.  What is added here is the estimate on
the data, which involves no pluripotential theory:

1.  The whole family factors through a single two-variable map.  Writing
    `S(c, w)` for the coordinatewise Mobius shift `w ↦ (w + c)/(1 + bar c w)`,
    one has `T_{a,h} = S(a + h, ·) ∘ S(-a, ·)`, and `S(a, ·)` inverts
    `S(-a, ·)` on the closed polydisk.  So with `w := S(-a, ζ)`,

      `v(T_{a,h} ζ) + v(T_{a,-h} ζ) - 2 v(ζ)
         = Ψ(a + h, w) + Ψ(a - h, w) - 2 Ψ(a, w)`,  `Ψ := v ∘ S`,

    an ordinary second difference of a fixed function of the *parameter*.
2.  `Ψ` is real-`C²` wherever the denominators do not vanish, in particular on
    a neighbourhood of `{‖c‖_∞ ≤ ρ} × closedPolydisk` for every `ρ < 1`; that
    set is compact, so `‖D²Ψ‖` is bounded there by some `M`.
3.  A second difference of a `C²` function is at most `2M‖h‖²`
    (`secondDifference_le_of_norm_fderiv_fderiv_le`, proved below on an open
    set rather than globally, since `Ψ` genuinely has poles).

Source: Z. Blocki, *The complex Monge--Ampere operator in pluripotential
theory*, lecture notes, Theorem 2.3.2; Bedford--Taylor, Invent. Math. 37
(1976).
-/

noncomputable section

open Set Filter Metric TopologicalSpace
open scoped Topology ContDiff ComplexConjugate

namespace SGPT.Foundations.Analysis.Pending.BedfordTaylor

open FirstPass FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending.SemiconcaveHessian

/-! ### The Mobius shift as a function of the parameter and the point -/

variable {n : ℕ}

/-- The coordinatewise Mobius shift `S(c, w) = M_{-c}(w)`, i.e.
`w_i ↦ (w_i + c_i)/(1 + conj c_i · w_i)`, read as a function of the *pair*
`(c, w)`.  The whole family `T_{a,h}` factors through it. -/
def polydiskShift (p : ComplexModel n × ComplexModel n) : ComplexModel n :=
  WithLp.toLp 2 fun i => discMobius (-(p.1 i)) (p.2 i)

theorem polydiskShift_apply (p : ComplexModel n × ComplexModel n) (i : Fin n) :
    polydiskShift p i = discMobius (-(p.1 i)) (p.2 i) := rfl

/-- The set where the Mobius denominators do not vanish. -/
def mobiusDomain (n : ℕ) : Set (ComplexModel n × ComplexModel n) :=
  {p | ∀ i, (1 : ℂ) - (starRingEnd ℂ) (-(p.1 i)) * p.2 i ≠ 0}

theorem continuous_denom (i : Fin n) :
    Continuous fun p : ComplexModel n × ComplexModel n =>
      (1 : ℂ) - (starRingEnd ℂ) (-(p.1 i)) * p.2 i := by
  have h1 : Continuous fun p : ComplexModel n × ComplexModel n => p.1 i :=
    ((EuclideanSpace.proj (𝕜 := ℂ) i).continuous).comp continuous_fst
  have h2 : Continuous fun p : ComplexModel n × ComplexModel n => p.2 i :=
    ((EuclideanSpace.proj (𝕜 := ℂ) i).continuous).comp continuous_snd
  exact continuous_const.sub (((Complex.continuous_conj).comp h1.neg).mul h2)

theorem isOpen_mobiusDomain : IsOpen (mobiusDomain n) := by
  have : mobiusDomain n =
      ⋂ i : Fin n, {p : ComplexModel n × ComplexModel n |
        (1 : ℂ) - (starRingEnd ℂ) (-(p.1 i)) * p.2 i ≠ 0} := by
    ext p; simp [mobiusDomain]
  rw [this]
  refine isOpen_iInter_of_finite fun i => ?_
  exact (continuous_denom i).isOpen_preimage {(0 : ℂ)}ᶜ isOpen_compl_singleton

/-- A pair with `‖c i‖ < 1` and `‖w i‖ ≤ 1` lies in the domain. -/
theorem mem_mobiusDomain {p : ComplexModel n × ComplexModel n}
    (hc : ∀ i, ‖p.1 i‖ < 1) (hw : ∀ i, ‖p.2 i‖ ≤ 1) : p ∈ mobiusDomain n :=
  fun i => discMobius_denom_ne_zero (by rw [norm_neg]; exact hc i) (hw i)

theorem contDiffOn_polydiskShift :
    ContDiffOn ℝ 2 (polydiskShift (n := n)) (mobiusDomain n) := by
  have hproj1 : ∀ i : Fin n,
      ContDiff ℝ 2 fun p : ComplexModel n × ComplexModel n => p.1 i := fun i =>
    (((EuclideanSpace.proj (𝕜 := ℂ) i).restrictScalars ℝ).comp
      (ContinuousLinearMap.fst ℝ (ComplexModel n) (ComplexModel n))).contDiff
  have hproj2 : ∀ i : Fin n,
      ContDiff ℝ 2 fun p : ComplexModel n × ComplexModel n => p.2 i := fun i =>
    (((EuclideanSpace.proj (𝕜 := ℂ) i).restrictScalars ℝ).comp
      (ContinuousLinearMap.snd ℝ (ComplexModel n) (ComplexModel n))).contDiff
  have hconj : ContDiff ℝ 2 fun z : ℂ => (starRingEnd ℂ) z :=
    Complex.conjCLE.toContinuousLinearMap.contDiff
  have hcomp : ∀ i : Fin n, ContDiffOn ℝ 2
      (fun p : ComplexModel n × ComplexModel n =>
        discMobius (-(p.1 i)) (p.2 i)) (mobiusDomain n) := by
    intro i
    have hnum : ContDiff ℝ 2 fun p : ComplexModel n × ComplexModel n =>
        p.2 i - -(p.1 i) := (hproj2 i).sub (hproj1 i).neg
    have hden : ContDiff ℝ 2 fun p : ComplexModel n × ComplexModel n =>
        (1 : ℂ) - (starRingEnd ℂ) (-(p.1 i)) * p.2 i :=
      contDiff_const.sub ((hconj.comp (hproj1 i).neg).mul (hproj2 i))
    have hden0 : ∀ p ∈ mobiusDomain n,
        (1 : ℂ) - (starRingEnd ℂ) (-(p.1 i)) * p.2 i ≠ 0 := fun p hp => hp i
    have hinv : ContDiffOn ℝ 2
        (fun p : ComplexModel n × ComplexModel n =>
          ((1 : ℂ) - (starRingEnd ℂ) (-(p.1 i)) * p.2 i)⁻¹) (mobiusDomain n) := by
      simpa only [Pi.inv_def] using hden.contDiffOn.inv hden0
    have hmul := hnum.contDiffOn.mul hinv
    simpa only [discMobius, div_eq_mul_inv] using hmul
  have hpi : ContDiffOn ℝ 2
      (fun p : ComplexModel n × ComplexModel n =>
        (fun i => discMobius (-(p.1 i)) (p.2 i) : Fin n → ℂ))
      (mobiusDomain n) := contDiffOn_pi.mpr hcomp
  have hL : ContDiff ℝ 2 fun x : Fin n → ℂ => (WithLp.toLp 2 x : ComplexModel n) :=
    (((EuclideanSpace.equiv (Fin n) ℂ).symm.toContinuousLinearMap).restrictScalars
      ℝ).contDiff
  exact hL.comp_contDiffOn hpi

/-! ### The family `T_{a,h}` factors through the shift -/

theorem polydiskShift_neg_left (a z : ComplexModel n) (i : Fin n) :
    polydiskShift (-a, z) i = discMobius (a i) (z i) := by
  rw [polydiskShift_apply]
  simp

/-- **The factorization.**  `T_{a,h} = S(a + h, ·) ∘ S(-a, ·)`: the inner map
does not depend on `h`, so the second difference of `v ∘ T_{a,·} ζ` is an
ordinary second difference of `v ∘ S(·, w)` at the parameter `a`. -/
theorem polydiskAut_eq_polydiskShift (a h z : ComplexModel n) :
    polydiskAut a h z = polydiskShift (a + h, polydiskShift (-a, z)) := by
  ext i
  rw [polydiskAut_apply, polydiskShift_apply, polydiskShift_neg_left]
  congr 2

theorem polydiskShift_neg_mem_closedUnitPolydisk {a z : ComplexModel n}
    (ha : ∀ i, ‖a i‖ < 1) (hz : z ∈ closedUnitPolydisk n) :
    polydiskShift (-a, z) ∈ closedUnitPolydisk n := by
  intro i
  rw [polydiskShift_neg_left]
  exact norm_discMobius_le_one (ha i) (hz i)

/-- `S(a, ·)` inverts `S(-a, ·)` on the closed polydisk: the parameter value
`c = a` returns the original point. -/
theorem polydiskShift_polydiskShift_neg {a z : ComplexModel n}
    (ha : ∀ i, ‖a i‖ < 1) (hz : z ∈ closedUnitPolydisk n) :
    polydiskShift (a, polydiskShift (-a, z)) = z := by
  ext i
  rw [polydiskShift_apply, polydiskShift_neg_left]
  exact discMobius_neg_discMobius (ha i) (hz i)

/-! ### The compact parameter box -/

/-- The compact convex box `{‖c‖_∞ ≤ rho} × closedPolydisk` of parameters. -/
def paramBox (n : ℕ) (rho : ℝ) : Set (ComplexModel n × ComplexModel n) :=
  {p | (∀ i, ‖p.1 i‖ ≤ rho) ∧ ∀ i, ‖p.2 i‖ ≤ 1}

theorem convex_paramBox (rho : ℝ) : Convex ℝ (paramBox n rho) := by
  intro p hp q hq s t hs ht hst
  refine ⟨fun i => ?_, fun i => ?_⟩
  · have hpq : (s • p + t • q).1 i = s • p.1 i + t • q.1 i := rfl
    rw [hpq]
    calc ‖s • p.1 i + t • q.1 i‖ ≤ ‖s • p.1 i‖ + ‖t • q.1 i‖ := norm_add_le _ _
      _ = s * ‖p.1 i‖ + t * ‖q.1 i‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_nonneg hs, abs_of_nonneg ht]
      _ ≤ s * rho + t * rho :=
          add_le_add (mul_le_mul_of_nonneg_left (hp.1 i) hs)
            (mul_le_mul_of_nonneg_left (hq.1 i) ht)
      _ = rho := by rw [← add_mul, hst, one_mul]
  · have hpq : (s • p + t • q).2 i = s • p.2 i + t • q.2 i := rfl
    rw [hpq]
    calc ‖s • p.2 i + t • q.2 i‖ ≤ ‖s • p.2 i‖ + ‖t • q.2 i‖ := norm_add_le _ _
      _ = s * ‖p.2 i‖ + t * ‖q.2 i‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_nonneg hs, abs_of_nonneg ht]
      _ ≤ s * 1 + t * 1 :=
          add_le_add (mul_le_mul_of_nonneg_left (hp.2 i) hs)
            (mul_le_mul_of_nonneg_left (hq.2 i) ht)
      _ = 1 := by rw [mul_one, mul_one, hst]

theorem isClosed_paramBox (rho : ℝ) : IsClosed (paramBox n rho) := by
  have h1 : ∀ i : Fin n, Continuous
      fun p : ComplexModel n × ComplexModel n => ‖p.1 i‖ :=
    fun i => continuous_norm.comp
      (((EuclideanSpace.proj (𝕜 := ℂ) i).continuous).comp continuous_fst)
  have h2 : ∀ i : Fin n, Continuous
      fun p : ComplexModel n × ComplexModel n => ‖p.2 i‖ :=
    fun i => continuous_norm.comp
      (((EuclideanSpace.proj (𝕜 := ℂ) i).continuous).comp continuous_snd)
  have : paramBox n rho =
      (⋂ i : Fin n, {p : ComplexModel n × ComplexModel n | ‖p.1 i‖ ≤ rho}) ∩
        ⋂ i : Fin n, {p : ComplexModel n × ComplexModel n | ‖p.2 i‖ ≤ 1} := by
    ext p; simp [paramBox]
  rw [this]
  exact (isClosed_iInter fun i => isClosed_le (h1 i) continuous_const).inter
    (isClosed_iInter fun i => isClosed_le (h2 i) continuous_const)

theorem isBounded_paramBox (rho : ℝ) : Bornology.IsBounded (paramBox n rho) := by
  refine Bornology.IsBounded.subset (Metric.isBounded_closedBall (x := (0 : ComplexModel n × ComplexModel n))
    (r := Real.sqrt ((n : ℝ) * (max rho 1) ^ 2))) ?_
  intro p hp
  rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def]
  refine max_le ?_ ?_
  · rw [EuclideanSpace.norm_eq]
    refine Real.sqrt_le_sqrt ?_
    calc ∑ i, ‖p.1 i‖ ^ 2 ≤ ∑ _i : Fin n, (max rho 1) ^ 2 :=
          Finset.sum_le_sum fun i _ => by
            have := (hp.1 i).trans (le_max_left rho 1)
            have h0 : (0:ℝ) ≤ ‖p.1 i‖ := norm_nonneg _
            nlinarith [le_max_right rho 1]
      _ = (n : ℝ) * (max rho 1) ^ 2 := by simp [Finset.sum_const]
  · rw [EuclideanSpace.norm_eq]
    refine Real.sqrt_le_sqrt ?_
    calc ∑ i, ‖p.2 i‖ ^ 2 ≤ ∑ _i : Fin n, (max rho 1) ^ 2 :=
          Finset.sum_le_sum fun i _ => by
            have := (hp.2 i).trans (le_max_right rho 1)
            have h0 : (0:ℝ) ≤ ‖p.2 i‖ := norm_nonneg _
            nlinarith [le_max_left rho 1]
      _ = (n : ℝ) * (max rho 1) ^ 2 := by simp [Finset.sum_const]

theorem isCompact_paramBox (rho : ℝ) : IsCompact (paramBox n rho) := by
  have : ProperSpace (ComplexModel n × ComplexModel n) :=
    FiniteDimensional.proper ℝ _
  exact Metric.isCompact_of_isClosed_isBounded (isClosed_paramBox rho)
    (isBounded_paramBox rho)

theorem paramBox_subset_mobiusDomain {rho : ℝ} (hrho : rho < 1) :
    paramBox n rho ⊆ mobiusDomain n :=
  fun _ hp => mem_mobiusDomain (fun i => lt_of_le_of_lt (hp.1 i) hrho) hp.2

/-! ### The uniform boundary estimate -/

theorem complexModel_add_apply (a h : ComplexModel n) (i : Fin n) : (a + h) i = a i + h i := rfl

theorem complexModel_sub_apply (a h : ComplexModel n) (i : Fin n) : (a - h) i = a i - h i := rfl

/-- **Blocki's `C^{1,1}` estimate, the half about the data.**  For `v` of
class `C²` and any `rho < 1` there is a single constant `M` bounding the
second difference of `v` along the Mobius family at every parameter `a` with
`‖a‖_∞ ≤ rho` whose translates `a ± h` stay in the same box, uniformly in the
point `z` of the closed polydisk.

No pluripotential theory enters: after the factorization
`T_{a,h} = S(a+h, ·) ∘ S(-a, ·)` this is the second difference, in the
parameter, of the fixed `C²` function `v ∘ S` on a compact convex box on which
`‖D²(v ∘ S)‖` is bounded. -/
theorem exists_secondDifference_bound (v : ComplexModel n → ℝ)
    (hv : ContDiff ℝ 2 v) {rho : ℝ} (hrho : rho < 1) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ a h : ComplexModel n, (∀ i, ‖a i‖ ≤ rho) →
      (∀ i, ‖a i + h i‖ ≤ rho) → (∀ i, ‖a i - h i‖ ≤ rho) →
      ∀ z ∈ closedUnitPolydisk n,
        v (polydiskAut a h z) + v (polydiskAut a (-h) z) - 2 * v z ≤
          M * ‖h‖ ^ 2 := by
  classical
  set Psi : ComplexModel n × ComplexModel n → ℝ := fun p => v (polydiskShift p)
    with hPsidef
  have hU : IsOpen (mobiusDomain n) := isOpen_mobiusDomain
  have hPsiC : ContDiffOn ℝ 2 Psi (mobiusDomain n) :=
    hv.comp_contDiffOn contDiffOn_polydiskShift
  obtain ⟨M₀, hM₀0, hMbound⟩ := exists_bound_fderiv_fderiv_of_isCompact hU hPsiC
    (isCompact_paramBox (n := n) rho) (paramBox_subset_mobiusDomain hrho)
  refine ⟨2 * M₀, by positivity, ?_⟩
  intro a h ha hah hah' z hz
  have haP : ∀ i, ‖a i‖ < 1 := fun i => lt_of_le_of_lt (ha i) hrho
  set w : ComplexModel n := polydiskShift (-a, z) with hwdef
  have hw : ∀ i, ‖w i‖ ≤ 1 := polydiskShift_neg_mem_closedUnitPolydisk haP hz
  have hx : ((a, w) : ComplexModel n × ComplexModel n) ∈ paramBox n rho := ⟨ha, hw⟩
  have hadd : ((a, w) + (h, (0 : ComplexModel n)) :
      ComplexModel n × ComplexModel n) = (a + h, w) := by
    simp
  have hsub : ((a, w) - (h, (0 : ComplexModel n)) :
      ComplexModel n × ComplexModel n) = (a - h, w) := by
    simp
  have hxp : ((a, w) + (h, (0 : ComplexModel n)) :
      ComplexModel n × ComplexModel n) ∈ paramBox n rho := by
    rw [hadd]
    exact ⟨fun i => by rw [complexModel_add_apply]; exact hah i, hw⟩
  have hxm : ((a, w) - (h, (0 : ComplexModel n)) :
      ComplexModel n × ComplexModel n) ∈ paramBox n rho := by
    rw [hsub]
    exact ⟨fun i => by rw [complexModel_sub_apply]; exact hah' i, hw⟩
  have hbound := secondDifference_le_of_norm_fderiv_fderiv_le_on hU hPsiC
    (convex_paramBox rho) (paramBox_subset_mobiusDomain hrho)
    hMbound hx hxp hxm
  have hnorm : ‖((h, (0 : ComplexModel n)) : ComplexModel n × ComplexModel n)‖
      = ‖h‖ := by
    rw [Prod.norm_def]
    simp
  rw [hadd, hsub, hnorm] at hbound
  have e₁ : Psi (a + h, w) = v (polydiskAut a h z) := by
    rw [hPsidef, polydiskAut_eq_polydiskShift, hwdef]
  have e₂ : Psi (a - h, w) = v (polydiskAut a (-h) z) := by
    rw [hPsidef, polydiskAut_eq_polydiskShift, hwdef, ← sub_eq_add_neg]
  have e₃ : Psi (a, w) = v z := by
    rw [hPsidef, hwdef]
    exact congrArg v (polydiskShift_polydiskShift_neg haP hz)
  rw [e₁, e₂, e₃] at hbound
  exact hbound

end SGPT.Foundations.Analysis.Pending.BedfordTaylor




end
