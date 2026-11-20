import SGPT.Bergman.SiuNativeProjectiveEquivalence

/-!
# Ample real classes are the Kähler classes of the Néron--Severi space

Lane BD, blueprint `bd.tex`. Source `rmk:bdiv:L749` (`chapter_bdiv.tex`): "The algebraic nef
b-divisors are introduced by Dang--Favre [DF20] [...] our transcendental intersection theory
coincides with theirs in the algebraic setting."

Dang--Favre's ample classes in `N¹(Y)_ℝ` are the positive real combinations of classes of ample
line bundles. Read through the cycle class map, and with ampleness of a holomorphic line bundle
expressed by a smooth Hermitian metric of positive curvature (Kodaira: such a bundle has a power
giving a projective embedding, `SGPT.Bergman.SiuKodaira.kodairaEmbedding`), this file proves:

* `IsAmpleRealClass α`: `α = ∑_j t_j c₁(L_j)` with `t_j > 0` and `L_j` positive line bundles
  (a nonempty finite family);
* `isAmpleRealClass_iff`: on a compact manifold, **the ample real classes are exactly the Kähler
  classes lying in `NS(X)_ℝ`**.

The nontrivial direction writes the coefficient vector `a` of a Kähler class
`{ω} = ∑ a_i {Θ_{E_i}}` as a convex combination of rational vectors `v_k` so close to `a` that
`η_k = ω + ∑ (v_{k,i} - a_i) Θ_{E_i}` stays Kähler (a simplex with rational vertices around `a`);
each `q_k η_k` is the curvature of a positive integral line bundle, as in
`exists_positive_native_bundle_of_kahler_mem_neronSeveri`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.BDivisor.DFAlg

open Set Filter Bundle
open scoped Topology Manifold ContDiff BigOperators
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open SGPT.Bergman.NativeHermitianMetric SGPT.PSH.GlobalL2
open SGPT.Bergman.QuantizationDraft
open SGPT.Bergman.AnalyticSectionProducts SGPT.Bergman.CompactHolomorphicSectionsDraft
open HermitianHolomorphicLineBundle
open SGPT.BDivisor.NSKodaira

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] [CompactSpace X]

/-- **Ample real classes**: positive real combinations `∑_j t_j c₁(L_j)` (`t_j > 0`, a nonempty
finite family) of first Chern classes of positive holomorphic line bundles `L_j` (smooth
Hermitian metrics with Kähler curvature forms `θ_j`; ample by Kodaira's embedding theorem). -/
def IsAmpleRealClass (α : RealBottChern n X) : Prop :=
  ∃ (k : ℕ) (L : Fin (k + 1) → HermitianHolomorphicLineBundle.{0, 0} n X)
    (θ : Fin (k + 1) → ClosedRealOneOneForm n X) (t : Fin (k + 1) → ℝ),
    (∀ j, IsSourceSmoothHermitianMetric (L j) ∧ IsOwnFirstChernForm (L j) (θ j) ∧
      (θ j).val.IsKahler ∧ 0 < t j) ∧
    α = ∑ j, t j • RealBottChern.ofRepresentative (θ j)

omit [CompactSpace X] in
/-- Positive combinations of Kähler forms (with at least one term) are Kähler. -/
theorem isKahler_sum_smul {k : ℕ} (θ : Fin (k + 1) → ClosedRealOneOneForm n X)
    (t : Fin (k + 1) → ℝ) (hθ : ∀ j, (θ j).val.IsKahler) (ht : ∀ j, 0 < t j) :
    (∑ j, t j • θ j).val.IsKahler := by
  set η := ∑ j, t j • θ j
  refine ⟨fun c z hz => ⟨η.property.2 c z hz, fun v hv => ?_⟩, η.property.1⟩
  have hcoef : η.val.coeff c z ![v, Complex.I • v] =
      ∑ j, t j * (θ j).val.coeff c z ![v, Complex.I • v] := by
    have hsumcoeff : η.val.coeff c z = ∑ j, (t j • θ j).val.coeff c z := by
      apply map_sum (show ClosedRealOneOneForm n X →ₗ[ℝ]
        ((ComplexModel n) [⋀^Fin 2]→L[ℝ] ℝ) from
        { toFun := fun s => s.val.coeff c z
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl })
    rw [hsumcoeff]
    simp only [ContinuousAlternatingMap.sum_apply, ClosedRealOneOneForm.coeff_smul,
      ContinuousAlternatingMap.smul_apply, smul_eq_mul]
  change 0 < η.val.coeff c z ![v, Complex.I • v]
  rw [hcoef, Fin.sum_univ_succ]
  have h0 : 0 < t 0 * (θ 0).val.coeff c z ![v, Complex.I • v] :=
    mul_pos (ht 0) (((hθ 0).1 c z hz).2 v hv)
  have hrest : 0 ≤ ∑ j : Fin k, t j.succ * (θ j.succ).val.coeff c z ![v, Complex.I • v] :=
    Finset.sum_nonneg fun j _ => (mul_pos (ht j.succ) (((hθ j.succ).1 c z hz).2 v hv)).le
  linarith

/-- **Uniform rational perturbation**: for `omega` Kähler and forms `θ_i`, there is `ε > 0` such
that
`omega + ∑ (r_i - a_i) θ_i` is Kähler whenever `|r_i - a_i| < ε` for all `i`. -/
theorem exists_uniform_positive_perturbation {N : ℕ}
    (omega : ClosedRealOneOneForm n X) (homega : omega.val.IsKahler)
    (θ : Fin N → ClosedRealOneOneForm n X) (a : Fin N → ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ r : Fin N → ℝ, (∀ i, |r i - a i| < ε) →
      (omega + ∑ i, (r i - a i) • θ i).val.IsKahler := by
  classical
  choose C hC hbound using fun i => exists_abs_line_domination omega (θ i) homega
  let S : ℝ := ∑ i, C i
  have hS : 0 ≤ S := Finset.sum_nonneg fun i _ => (hC i).le
  let ε : ℝ := 1 / (2 * (S + 1))
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hsmall : ε * S < 1 := by
    dsimp [ε]
    rw [one_div_mul_eq_div, div_lt_one (by positivity)]
    linarith
  refine ⟨ε, hε, fun r hr => ?_⟩
  let η := omega + ∑ i, (r i - a i) • θ i
  refine ⟨fun c z hz => ⟨η.property.2 c z hz, fun v hv => ?_⟩, η.property.1⟩
  have hpos := (homega.1 c z hz).2 v hv
  let w := omega.val.coeff c z ![v, Complex.I • v]
  have hw : 0 < w := hpos
  have hterm : ∀ i : Fin N,
      |(r i - a i) * (θ i).val.coeff c z ![v, Complex.I • v]| ≤ ε * C i * w := by
    intro i
    rw [abs_mul]
    calc
      _ ≤ ε * (C i * w) := mul_le_mul (hr i).le (hbound i c z hz v)
        (abs_nonneg _) (le_of_lt hε)
      _ = _ := by ring
  have hsum : |∑ i, (r i - a i) * (θ i).val.coeff c z ![v, Complex.I • v]| ≤ ε * S * w := by
    calc
      _ ≤ ∑ i, |(r i - a i) * (θ i).val.coeff c z ![v, Complex.I • v]| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ε * C i * w := Finset.sum_le_sum fun i _ => hterm i
      _ = _ := by simp only [S, Finset.sum_mul, Finset.mul_sum]
  have hlow := neg_le_of_abs_le hsum
  have hcoef : η.val.coeff c z ![v, Complex.I • v] =
      w + ∑ i, (r i - a i) * (θ i).val.coeff c z ![v, Complex.I • v] := by
    simp only [η, ClosedRealOneOneForm.coeff_add, ContinuousAlternatingMap.add_apply]
    congr 1
    have hsumcoeff : (∑ i, (r i - a i) • θ i).val.coeff c z =
        ∑ i, ((r i - a i) • θ i).val.coeff c z := by
      apply map_sum (show ClosedRealOneOneForm n X →ₗ[ℝ]
        ((ComplexModel n) [⋀^Fin 2]→L[ℝ] ℝ) from
        { toFun := fun t => t.val.coeff c z
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl })
    rw [hsumcoeff]
    simp only [ContinuousAlternatingMap.sum_apply, ClosedRealOneOneForm.coeff_smul,
      ContinuousAlternatingMap.smul_apply, smul_eq_mul]
  change 0 < η.val.coeff c z ![v, Complex.I • v]
  rw [hcoef]
  nlinarith [mul_lt_mul_of_pos_right hsmall hw]

/-- **A rational simplex around a real vector**: every `a ∈ ℝ^N` is a convex combination, with
positive weights, of `N + 1` rational vectors within distance `ε` of `a` (in every coordinate). -/
theorem exists_rational_simplex {N : ℕ} (a : Fin N → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ (v : Fin (N + 1) → Fin N → ℚ) (μ : Fin (N + 1) → ℝ),
      (∀ k i, |(v k i : ℝ) - a i| < ε) ∧ (∀ k, 0 < μ k) ∧ ∑ k, μ k = 1 ∧
      ∀ i, ∑ k, μ k * (v k i : ℝ) = a i := by
  classical
  set δ : ℝ := ε / (2 * (N + 1)) with hδ
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hδpos : 0 < δ := by rw [hδ]; positivity
  have hδε : δ ≤ ε := by
    rw [hδ, div_le_iff₀ (by positivity)]
    nlinarith
  have hNδ : ((N : ℝ) + 1) * δ = ε / 2 := by
    rw [hδ, mul_div_assoc', div_eq_iff (by positivity)]
    ring
  -- a rational point strictly below `a`, within `δ`
  have hlow : ∀ i, ∃ r : ℚ, a i - δ < r ∧ (r : ℝ) < a i := fun i =>
    exists_rat_btwn (by linarith)
  choose r hr1 hr2 using hlow
  set x : Fin N → ℝ := fun i => a i - r i with hx
  have hxpos : ∀ i, 0 < x i := fun i => by simp only [hx]; linarith [hr2 i]
  have hxlt : ∀ i, x i < δ := fun i => by simp only [hx]; linarith [hr1 i]
  set s : ℝ := ∑ i, x i with hs
  have hslt : s < ε / 2 := by
    have h1 : s ≤ N * δ := by
      calc s ≤ ∑ _i : Fin N, δ := Finset.sum_le_sum fun i _ => (hxlt i).le
        _ = N * δ := by simp
    nlinarith
  obtain ⟨D, hD1, hD2⟩ := exists_rat_btwn (show max s (ε / 4) < ε / 2 from
    max_lt hslt (by linarith))
  have hDs : s < D := lt_of_le_of_lt (le_max_left _ _) hD1
  have hDpos : (0 : ℝ) < D := by
    have := le_max_right s (ε / 4)
    linarith
  -- the vertices `r` and `r + D e_j`, with weights `1 - s / D` and `x_j / D`
  let v : Fin (N + 1) → Fin N → ℚ := Fin.cases r (fun j i => r i + if i = j then D else 0)
  let μ : Fin (N + 1) → ℝ := Fin.cases (1 - s / D) (fun j => x j / D)
  refine ⟨v, μ, ?_, ?_, ?_, ?_⟩
  · intro k i
    refine Fin.cases ?_ (fun j => ?_) k
    · show |((r i : ℚ) : ℝ) - a i| < ε
      rw [abs_lt]
      constructor <;> linarith [hr1 i, hr2 i]
    · show |(((r i + if i = j then D else 0 : ℚ)) : ℝ) - a i| < ε
      split_ifs with hij
      · push_cast
        rw [abs_lt]
        constructor <;> linarith [hr1 i, hr2 i]
      · push_cast
        rw [add_zero, abs_lt]
        constructor <;> linarith [hr1 i, hr2 i]
  · intro k
    refine Fin.cases ?_ (fun j => ?_) k
    · show 0 < 1 - s / D
      rw [sub_pos, div_lt_one hDpos]
      exact hDs
    · show 0 < x j / D
      exact div_pos (hxpos j) hDpos
  · rw [Fin.sum_univ_succ]
    show 1 - s / D + ∑ j : Fin N, x j / D = 1
    rw [← Finset.sum_div, ← hs]
    ring
  · intro i
    rw [Fin.sum_univ_succ]
    show (1 - s / D) * (r i : ℝ) +
      ∑ j : Fin N, x j / D * (((r i + if i = j then D else 0 : ℚ)) : ℝ) = a i
    have hsplit : ∀ j : Fin N, x j / D * (((r i + if i = j then D else 0 : ℚ)) : ℝ) =
        x j / D * (r i : ℝ) + (if i = j then x j else 0) := by
      intro j
      split_ifs with hij
      · push_cast
        rw [mul_add, div_mul_cancel₀ _ hDpos.ne']
      · push_cast
        ring
    rw [Finset.sum_congr rfl fun j _ => hsplit j, Finset.sum_add_distrib, ← Finset.sum_mul,
      ← Finset.sum_div, ← hs, Finset.sum_ite_eq]
    simp only [Finset.mem_univ, if_true, hx]
    field_simp
    ring

/-- **A Kähler form with rational coefficients is (a multiple of) a positive line bundle**: if
`omega = ∑ a_i Θ_{E_i} + ddᶜ f` and `η = omega + ∑ (r_i - a_i) Θ_{E_i}` is Kähler with `r`
rational, then
`q η` is the curvature of a smooth metric on a holomorphic line bundle for some integer `q > 0`. -/
theorem exists_positive_bundle_of_rational {N : ℕ} (omega : ClosedRealOneOneForm n X)
    (D : Fin N → EffectiveDivisor n X) (E : Fin N → MeteredEffectiveQDivisor n X)
    (a : Fin N → ℝ) (hE : ∀ i, DivisorMetric.IsDivisorMetric (D i) (E i))
    (f : X → ℝ) (hf : ChartSmooth (n := n) f)
    (hpotential : ∀ (c : ComplexChart n X) (z : ComplexModel n), z ∈ c.val.target →
      omega.val.coeff c z = (∑ i, a i • (E i).curvature).val.coeff c z +
        smoothDDC (fun w => f (c.val.symm w)) z)
    (r : Fin N → ℚ) (hr : (omega + ∑ i, ((r i : ℝ) - a i) • (E i).curvature).val.IsKahler) :
    ∃ (q : ℕ), 0 < q ∧ ∃ (G : HermitianHolomorphicLineBundle.{0, 0} n X),
      IsSourceSmoothHermitianMetric G ∧
      IsOwnFirstChernForm G ((q : ℝ) • (omega + ∑ i, ((r i : ℝ) - a i) • (E i).curvature)) ∧
      ((q : ℝ) • (omega + ∑ i, ((r i : ℝ) - a i) • (E i).curvature)).val.IsKahler := by
  classical
  obtain ⟨q, hq, b, hb⟩ := exists_positive_common_denominator r
  let η := omega + ∑ i, ((r i : ℝ) - a i) • (E i).curvature
  let θa := ∑ i, a i • (E i).curvature
  let θr := ∑ i, (r i : ℝ) • (E i).curvature
  let θb := ∑ i, (b i : ℝ) • (E i).curvature
  have hlinear : θr = θa + ∑ i, ((r i : ℝ) - a i) • (E i).curvature := by
    dsimp only [θr, θa]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← add_smul]
    congr 1
    ring
  have hη : ∀ (c : ComplexChart n X) (z : ComplexModel n), z ∈ c.val.target →
      η.val.coeff c z = θr.val.coeff c z + smoothDDC (fun w => f (c.val.symm w)) z := by
    intro c z hz
    dsimp only [η]
    rw [ClosedRealOneOneForm.coeff_add, hpotential c z hz, hlinear,
      ClosedRealOneOneForm.coeff_add]
    abel
  have hθb : θb = (q : ℝ) • θr := by
    dsimp only [θb, θr]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [hb i, smul_smul]
  obtain ⟨L, hL, hcurv⟩ := exists_native_integral_divisor_metric D E hE b
  have hqf : ChartSmooth (n := n) (fun p => (q : ℝ) * f p) :=
    fun c => contDiffOn_const.mul (hf c)
  refine ⟨q, hq, rescaleExp L (fun p => (q : ℝ) * f p) hqf,
    rescaleExp_smooth L hL _ hqf, ?_, ?_⟩
  · apply rescale_exp_isOwnFirstChernForm L hL θb ((q : ℝ) • η) hcurv _ hqf
    intro c z hz
    rw [ClosedRealOneOneForm.coeff_smul, hη c z hz, smul_add, hθb,
      ClosedRealOneOneForm.coeff_smul]
    congr 1
    simpa only [smul_eq_mul] using (smoothDDC_smul c.val.open_target (hf c) (q : ℝ) hz).symm
  · refine ⟨fun c z hz => ⟨((q : ℝ) • η).property.2 c z hz, fun v hv => ?_⟩,
      ((q : ℝ) • η).property.1⟩
    simp only [ClosedRealOneOneForm.coeff_smul, ContinuousAlternatingMap.smul_apply, smul_eq_mul]
    exact mul_pos (by exact_mod_cast hq) ((hr.1 c z hz).2 v hv)

/-- **The ample real classes are the Kähler classes of the Néron--Severi space**: on a compact
complex manifold, `α` is a positive real combination of first Chern classes of positive line
bundles iff `α ∈ NS(X)_ℝ` and `α` is represented by a Kähler form. -/
theorem isAmpleRealClass_iff (α : RealBottChern n X) :
    IsAmpleRealClass α ↔ α ∈ neronSeveri n X ∧
      ∃ omega : ClosedRealOneOneForm n X, omega.val.IsKahler ∧
        RealBottChern.ofRepresentative omega = α := by
  classical
  constructor
  · rintro ⟨k, L, θ, t, hLθ, rfl⟩
    refine ⟨Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _
      (positive_native_chern_mem_neronSeveri (L j) (hLθ j).1 (θ j) (hLθ j).2.1 (hLθ j).2.2.1),
      ∑ j, t j • θ j, isKahler_sum_smul θ t (fun j => (hLθ j).2.2.1) (fun j => (hLθ j).2.2.2), ?_⟩
    change RealBottChern.ofRepresentativeLinearMap (∑ j, t j • θ j) = _
    simp only [map_sum, map_smul]
    rfl
  · rintro ⟨hNS, omega, homega, rfl⟩
    obtain ⟨N, D, E, a, hE, f, hf, hpotential⟩ := exists_finite_divisor_potential omega hNS
    obtain ⟨ε, hε, hpert⟩ :=
      exists_uniform_positive_perturbation omega homega (fun i => (E i).curvature) a
    obtain ⟨v, μ, hv, hμ, hμ1, hμa⟩ := exists_rational_simplex a hε
    have hK : ∀ k, (omega + ∑ i, ((v k i : ℝ) - a i) • (E i).curvature).val.IsKahler :=
      fun k => hpert (fun i => (v k i : ℝ)) (hv k)
    choose q hq G hG hown hGK using fun k =>
      exists_positive_bundle_of_rational omega D E a hE f hf hpotential (v k) (hK k)
    refine ⟨N, G, fun k => (q k : ℝ) • (omega + ∑ i, ((v k i : ℝ) - a i) • (E i).curvature),
      fun k => μ k / q k, fun k => ⟨hG k, hown k, hGK k, ?_⟩, ?_⟩
    · exact div_pos (hμ k) (by exact_mod_cast hq k)
    · -- `{omega} = ∑_k μ_k {η_k}` since `∑ μ_k = 1` and `∑_k μ_k v_k = a`
      have hcoef : ∀ i, ∑ k, μ k * ((v k i : ℝ) - a i) = 0 := by
        intro i
        rw [Finset.sum_congr rfl (fun k _ => mul_sub (μ k) _ _), Finset.sum_sub_distrib, hμa i,
          ← Finset.sum_mul, hμ1, one_mul, sub_self]
      have hform : ∑ k, μ k • (omega + ∑ i, ((v k i : ℝ) - a i) • (E i).curvature) = omega := by
        simp only [smul_add, Finset.sum_add_distrib, Finset.smul_sum, smul_smul]
        rw [← Finset.sum_smul, hμ1, one_smul, Finset.sum_comm, Finset.sum_eq_zero, add_zero]
        intro i _
        rw [← Finset.sum_smul, hcoef i, zero_smul]
      conv_lhs => rw [← hform]
      change RealBottChern.ofRepresentativeLinearMap (∑ k, _) = _
      rw [map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      change RealBottChern.ofRepresentative (μ k • _) = _
      rw [RealBottChern.ofRepresentative_smul, RealBottChern.ofRepresentative_smul, smul_smul,
        div_mul_cancel₀ _ (by exact_mod_cast (hq k).ne' : (q k : ℝ) ≠ 0)]

end SGPT.BDivisor.DFAlg
