import SGPT.LineBundle.RiemannRochAmple
import SGPT.Foundations.Schemes.NativeFlagTerminalEulerLength
import SGPT.Foundations.Schemes.NativeRegularProjectiveFlag
import SGPT.Foundations.Schemes.NativeSmoothFunctionFieldDimension
import SGPT.Foundations.Schemes.FiniteTypeDomainDimension

/-!
# Self-intersection numbers of ample line bundles and asymptotic Riemann–Roch

Let `X` be an integral scheme, smooth of relative dimension `n` over `ℂ`, and `L` an ample line
bundle with polarization `L^q ≅ ι^* 𝒪(1)`, `ι : X → ℙ^N_ℂ` a closed immersion
(`SGPT.LineBundle.AmplePolarization`). Write `H = L^q`.

## The intersection number `(L^n)`

The workspace (`SGPT.Foundations.Schemes`) constructs a *regular projective flag*
`X = Z_0 ⊇ Z_1 ⊇ ⋯`, where `Z_{j+1}` is the zero scheme of a section of `𝒪(1)|_{Z_j}` which is
regular (a nonzerodivisor on every coordinate chart), together with the Čech Euler
characteristics `χ(Z_j, 𝒪(m))` on the standard cover and the exact recurrence
`χ(Z_j, 𝒪(m+1)) - χ(Z_j, 𝒪(m)) = χ(Z_{j+1}, 𝒪(m+1))`. Here we show that for `X` of dimension
`n` the `n`-th stage `Z = Z_n = D_1 ∩ ⋯ ∩ D_n` is a zero-dimensional (Artinian) complete
intersection, and define
`(H^n) := length(𝒪_Z)` (`AmplePolarization.flagLength`) and
`(L^n) := (H^n) / q^n` (`AmplePolarization.selfIntersection`).
By the recurrence, `(H^n)` is the eventual value of the `n`-th forward difference
`Δ^n χ(X, H^m)` (`AmplePolarization.fwdDiff_euler_eq_flagLength`), i.e. `n!` times the leading
coefficient of the Snapper polynomial `χ(X, H^m)`: this is the Snapper–Kleiman definition of the
top self-intersection number of `H`.

## Main results

* `affineChart_ringKrullDim_le_of_smooth`: affine opens of `X` have Krull dimension `≤ n`.
* `AmplePolarization.flag_terminal_isArtinian`: the `n`-th stage of the regular flag is Artinian.
* `AmplePolarization.exists_h0_polynomial_flagLength`: `h⁰(X, L^{qm})` is eventually a
  polynomial of degree `≤ n` in `m` whose coefficient of `m^n` is `(H^n)/n!`.
* `AmplePolarization.volume_eq_selfIntersection`: **`vol(L) = (L^n)`**.
* `AmplePolarization.h0_sub_selfIntersection_isBigO`: **asymptotic Riemann–Roch for ample line
  bundles**: `h⁰(X, L^k) = (L^n)/n! · k^n + O(k^{n-1})` (`n ≥ 1`).
* `AmplePolarization.selfIntersection_eq`: `(L^n)` does not depend on the polarization (nor on
  the regular sections chosen).
* `AmplePolarization.isBig_iff_selfIntersection_pos`: `L` is big iff `(L^n) > 0`.

Not formalized: `(L^n) > 0` for ample `L` (nonemptiness of `Z`, a dimension statement),
mixed intersection numbers `(L_1 ⋯ L_n)`, the nef case, and `(L^n) = ∫_X c_1(L, h)^n`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.LineBundle

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry SGPT.Foundations.Schemes Filter Opposite
open TopologicalSpace Polynomial
open scoped ENNReal Nat Topology

attribute [local instance] MvPolynomial.gradedAlgebra

section ChartDimension

variable {X : Scheme} [IsIntegral X] (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f]

/-- A nonempty affine open of an integral scheme smooth of relative dimension `n` over `ℂ` has a
coordinate ring of transcendence degree `n` over `ℂ`. -/
theorem affineChart_trdeg_of_smooth (V : X.Opens) [Nonempty V] (hV : IsAffineOpen V) :
    letI := affineChartAlgebra f V
    Algebra.trdeg ℂ Γ(X, V) = (n : Cardinal) := by
  let := affineChartAlgebra f V
  let := schemeFunctionFieldAlgebra f
  have := schemeFunctionField_affineChartScalarTower f V
  have : IsFractionRing Γ(X, V) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X V hV
  have : Algebra.IsAlgebraic Γ(X, V) X.functionField :=
    IsLocalization.isAlgebraic _ (nonZeroDivisors Γ(X, V))
  have hz : Algebra.trdeg Γ(X, V) X.functionField = 0 :=
    trdeg_eq_zero_iff.mpr inferInstance
  have h := trdeg_add_eq ℂ Γ(X, V) (A := X.functionField)
  simpa only [hz, add_zero, nativeSmoothFunctionField_trdeg f n] using h

/-- Affine opens of a projective integral scheme smooth of relative dimension `n` over `ℂ` have
Krull dimension at most `n` (the empty open has dimension `⊥`). -/
theorem affineChart_ringKrullDim_le_of_smooth (E : ClosedProjectiveEmbedding f) (V : X.Opens)
    (hV : IsAffineOpen V) : ringKrullDim Γ(X, V) ≤ (n : WithBot ℕ∞) := by
  classical
  by_cases h : Nonempty V
  · let := affineChartAlgebra f V
    have := E.locallyOfFiniteType
    have := affineChartAlgebra_finiteType f hV
    exact le_of_eq (finiteTypeDomain_ringKrullDim_of_trdeg ℂ Γ(X, V) n
      (affineChart_trdeg_of_smooth f n V hV))
  · have hV0 : V = ⊥ := by
      apply bot_unique
      intro x hx
      exact (h ⟨⟨x, hx⟩⟩).elim
    have : Subsingleton Γ(X, V) := CommRingCat.subsingleton_of_isTerminal
      (TopCat.Sheaf.isTerminalOfEqEmpty X.sheaf hV0)
    rw [ringKrullDim_eq_bot_of_subsingleton]
    exact bot_le

end ChartDimension

/-- Integer sequences agreeing eventually with a polynomial have the corresponding forward
differences (as in the workspace lemma `SGPT.Foundations.Schemes.integer_eventual_polynomial_fwdDiff`). -/
theorem int_fwdDiff_iter_eq_polynomial (F : ℕ → ℤ) (Q : Polynomial ℚ) (b : ℕ)
    (h : ∀ m : ℕ, b ≤ m → (F m : ℚ) = Q.eval (m : ℚ)) (j m : ℕ) (hm : b ≤ m) :
    (((fwdDiff (1 : ℕ))^[j] F) m : ℚ) = ((fwdDiff (1 : ℚ))^[j] Q.eval) (m : ℚ) := by
  induction j generalizing m with
  | zero => exact h m hm
  | succ j ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    change (((((fwdDiff (1 : ℕ))^[j] F) (m + 1)) - (((fwdDiff (1 : ℕ))^[j] F) m) : ℤ) : ℚ) =
        ((fwdDiff (1 : ℚ))^[j] Q.eval) ((m : ℚ) + 1) - ((fwdDiff (1 : ℚ))^[j] Q.eval) (m : ℚ)
    rw [Int.cast_sub, ih (m + 1) (hm.trans (Nat.le_succ m)), ih m hm]
    simp only [Nat.cast_add, Nat.cast_one]

/-- If a function `ℚ → ℚ` is eventually constant on natural numbers, its forward differences of
positive order eventually vanish there. -/
theorem fwdDiff_iter_eventually_zero (g : ℚ → ℚ) (c : ℚ) (b : ℕ)
    (hg : ∀ m : ℕ, b ≤ m → g m = c) (k : ℕ) (hk : 1 ≤ k) :
    ∀ m : ℕ, b ≤ m → ((fwdDiff (1 : ℚ))^[k] g) m = 0 := by
  have key : ∀ k : ℕ, ∃ v : ℚ, ∀ m : ℕ, b ≤ m → ((fwdDiff (1 : ℚ))^[k] g) m = v ∧
      (1 ≤ k → v = 0) := by
    intro k
    induction k with
    | zero => exact ⟨c, fun m hm => ⟨hg m hm, fun h => absurd h (by omega)⟩⟩
    | succ k ih =>
      obtain ⟨v, hv⟩ := ih
      refine ⟨0, fun m hm => ⟨?_, fun _ => rfl⟩⟩
      rw [Function.iterate_succ_apply']
      change ((fwdDiff (1 : ℚ))^[k] g) ((m : ℚ) + 1) - ((fwdDiff (1 : ℚ))^[k] g) (m : ℚ) = 0
      have h1 := (hv (m + 1) (hm.trans (Nat.le_succ m))).1
      have h2 := (hv m hm).1
      push_cast at h1
      rw [h1, h2, sub_self]
  intro m hm
  obtain ⟨v, hv⟩ := key k
  rw [(hv m hm).1]
  exact (hv m hm).2 hk

/-- A polynomial whose `n`-th forward difference is eventually the constant `c` on natural
numbers has degree `≤ n` and `n!` times its coefficient of `X^n` equals `c`. -/
theorem polynomial_natDegree_le_of_fwdDiff_eventually_const (Q : Polynomial ℚ) (n b : ℕ) (c : ℚ)
    (h : ∀ m : ℕ, b ≤ m → ((fwdDiff (1 : ℚ))^[n] Q.eval) (m : ℚ) = c) :
    Q.natDegree ≤ n ∧ (n ! : ℚ) * Q.coeff n = c := by
  have hdeg : Q.natDegree ≤ n := by
    by_contra hlt
    rw [not_le] at hlt
    have hQ : Q ≠ 0 := by
      intro hz
      rw [hz, natDegree_zero] at hlt
      omega
    have hz := fwdDiff_iter_eventually_zero ((fwdDiff (1 : ℚ))^[n] Q.eval) c b h
      (Q.natDegree - n) (by omega) b le_rfl
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel hlt.le,
      Polynomial.fwdDiff_iter_degree_eq_factorial] at hz
    simp only [Pi.smul_apply, Pi.natCast_apply, smul_eq_mul] at hz
    rcases mul_eq_zero.mp hz with h1 | h1
    · exact hQ (leadingCoeff_eq_zero.mp h1)
    · exact (Nat.factorial_ne_zero _) (by exact_mod_cast h1)
  refine ⟨hdeg, ?_⟩
  rcases hdeg.lt_or_eq with hlt | heq
  · have h0 := h b le_rfl
    rw [Polynomial.fwdDiff_iter_eq_zero_of_degree_lt hlt] at h0
    rw [coeff_eq_zero_of_natDegree_lt hlt, mul_zero]
    simpa using h0
  · have h0 := h b le_rfl
    rw [← heq, Polynomial.fwdDiff_iter_degree_eq_factorial] at h0
    simp only [Pi.smul_apply, Pi.natCast_apply, smul_eq_mul] at h0
    rw [← h0, ← heq, coeff_natDegree, mul_comm]

namespace AmplePolarization

variable {X : Scheme} {f : X ⟶ Spec (.of ℂ)} {L : X.Modules}

/-- The stratum `ι : X → ℙ^N` from which the regular flag starts. -/
def initialStratum (P : AmplePolarization f L) : NativeClosedProjectiveStratum P.ambientDimension :=
  ⟨Over.mk P.map, P.isClosedImmersion⟩

/-- The regular projective flag `Z_j` of iterated zero schemes of regular sections of
`𝒪(1) = L^q` (workspace construction `NativeClosedProjectiveStratum.iterated`). -/
def flag (P : AmplePolarization f L) (j : ℕ) : NativeClosedProjectiveStratum P.ambientDimension :=
  P.initialStratum.iterated j

/-- The regrouping `L^{qm} ≅ (ι^* 𝒪(1))^{⊗ m}`. -/
def initialPowerIso (P : AmplePolarization f L) (a : LineBundleAtlas L) (m : ℕ) :
    bundleTensorPower L (P.power * m) ≅ P.initialStratum.powerSheaf m :=
  nativeLineTensorPowerMulIso a P.power m ≪≫
    nativeLineTensorPowerIso (P.iso ≪≫
      (nativeProjectivePositiveLinePowerOneIso ℂ P.ambientDimension P.map).symm) m

/-- The Euler characteristic `χ(X, H^m)` is eventually `h⁰(X, L^{qm})`. -/
theorem initial_euler_eq_h0 (P : AmplePolarization f L) (a : LineBundleAtlas L) :
    ∃ b : ℕ, ∀ m : ℕ, b ≤ m → P.initialStratum.powerEuler m = (h0 f L (P.power * m) : ℤ) := by
  obtain ⟨b, hb⟩ := P.initialStratum.powerEuler_eventually_eq_global_finrank
  refine ⟨b, fun m hm => (hb m hm).trans ?_⟩
  have hc : schemeGlobalConstants
      (P.initialStratum.val.hom ≫ polynomialProjStructureMap ℂ P.ambientDimension) =
        schemeGlobalConstants f := congrArg schemeGlobalConstants P.over_base
  rw [hc]
  exact congrArg (fun d : ℕ => (d : ℤ))
    ((nativeModuleIsoBaseGlobalSections (P.initialPowerIso a m)
      (schemeGlobalConstants f)).toLinearEquiv.finrank_eq).symm

variable [IsIntegral X] (n : ℕ) [SmoothOfRelativeDimension n f]

/-- Each regular cut lowers the chart dimension: `dim Γ(Z_j ∩ U_S) + j ≤ n`. -/
theorem flag_chart_dimension_bound (P : AmplePolarization f L) (j : ℕ)
    (S : Finset (Fin (P.ambientDimension + 1))) (hS : S.Nonempty) :
    ringKrullDim Γ((P.flag j).val.left, actualSchemeSubsetOpen
        (actualPolynomialProjectivePullbackCoordinateOpens (P.flag j).val.hom) S) +
      (j : WithBot ℕ∞) ≤ (n : WithBot ℕ∞) :=
  (NativeClosedProjectiveStratum.iterated_chart_dimension_bound P.initialStratum j S hS).trans
    (affineChart_ringKrullDim_le_of_smooth f n P.toClosedProjectiveEmbedding _
      (actualPolynomialProjectivePullbackSubsetOpen_isAffine ℂ P.ambientDimension P.map S hS))

/-- The `n`-th stage `Z = D_1 ∩ ⋯ ∩ D_n` of the regular flag is an Artinian scheme
(zero-dimensional; possibly empty). -/
theorem flag_terminal_isArtinian (P : AmplePolarization f L) :
    IsArtinianScheme (P.flag n).val.left := by
  let T := P.flag n
  let U := actualPolynomialProjectivePullbackCoordinateOpens T.val.hom
  have : IsClosedImmersion T.val.hom := T.property
  have : IsNoetherian T.val.left := T.embedding.isNoetherian
  have hAff (i : Fin (P.ambientDimension + 1)) : IsAffineOpen (U i) :=
    (polynomialProjCoordinateOpen_isAffine ℂ P.ambientDimension i).preimage T.val.hom
  have hlocal : IsLocallyArtinian T.val.left := by
    apply (isLocallyArtinian_iff_of_isOpenCover
      (show IsOpenCover U from actualPolynomialProjectivePullbackCoordinateOpens_covers T.val.hom)
      hAff).mpr
    intro i
    have : IsNoetherianRing Γ(T.val.left, U i) := T.embedding.affineSections_isNoetherian (hAff i)
    apply isArtinianRing_iff_krullDimLE_zero.mpr
    apply Ring.krullDimLE_iff.mpr
    have hd := P.flag_chart_dimension_bound n n {i} (by simp)
    apply (ENat.WithBot.add_le_add_natCast_right_iff (c := n)).mp
    have hi : actualSchemeSubsetOpen U {i} = U i := Finset.inf_singleton
    change ringKrullDim Γ(T.val.left, actualSchemeSubsetOpen U {i}) + (n : WithBot ℕ∞) ≤
      (n : WithBot ℕ∞) at hd
    rw [hi] at hd
    simpa only [Nat.cast_zero, zero_add] using hd
  exact { toIsLocallyArtinian := hlocal, toCompactSpace := inferInstance }

/-- The top self-intersection `(H^n)` of the very ample `H = L^q = ι^* 𝒪(1)`: the length
`Σ_{z ∈ Z} length 𝒪_{Z,z}` of the zero-dimensional complete intersection `Z = D_1 ∩ ⋯ ∩ D_n`
cut out by the regular flag. -/
def flagLength (P : AmplePolarization f L) : ℕ :=
  letI := P.flag_terminal_isArtinian n
  (P.flag n).artinianStalkLengthSum.toNat

/-- The top self-intersection number `(L^n) = (H^n) / q^n` of the ample line bundle `L`. -/
def selfIntersection (P : AmplePolarization f L) : ℝ :=
  (P.flagLength n : ℝ) / (P.power : ℝ) ^ n

theorem selfIntersection_nonneg (P : AmplePolarization f L) : 0 ≤ P.selfIntersection n :=
  div_nonneg (Nat.cast_nonneg _) (pow_nonneg (Nat.cast_nonneg _) _)

/-- **Snapper form of `(H^n)`.** The `n`-th forward difference of the Euler characteristic
`m ↦ χ(X, H^m)` (Čech, standard cover) is eventually `(H^n)`. -/
theorem fwdDiff_euler_eq_flagLength (P : AmplePolarization f L) :
    ∃ b : ℕ, ∀ m : ℕ, b ≤ m →
      ((fwdDiff (1 : ℕ))^[n] P.initialStratum.powerEuler) m = (P.flagLength n : ℤ) := by
  have := P.flag_terminal_isArtinian n
  obtain ⟨b, hb⟩ := (P.flag n).artinian_powerEuler_eventually_eq_stalk_length_sum
  refine ⟨b, fun m hm => ?_⟩
  rw [NativeClosedProjectiveStratum.powerEuler_iterated_fwdDiff]
  exact hb (m + n) (hm.trans (Nat.le_add_right m n))

/-- `h⁰(X, L^{qm})` is eventually a polynomial of degree `≤ n` in `m` whose coefficient of `m^n`
is `(H^n) / n!`. -/
theorem exists_h0_polynomial_flagLength (P : AmplePolarization f L) (a : LineBundleAtlas L) :
    ∃ Q : Polynomial ℚ, Q.natDegree ≤ n ∧ (n ! : ℚ) * Q.coeff n = P.flagLength n ∧
      ∃ b : ℕ, ∀ m : ℕ, b ≤ m → (h0 f L (P.power * m) : ℚ) = Q.eval (m : ℚ) := by
  obtain ⟨Q, -, bQ, hQ⟩ := P.exists_h0_residuePolynomial a 0
  obtain ⟨bE, hE⟩ := P.initial_euler_eq_h0 a
  obtain ⟨bT, hT⟩ := P.fwdDiff_euler_eq_flagLength n
  have hQ' : ∀ m : ℕ, max bQ bE ≤ m →
      ((P.initialStratum.powerEuler m : ℤ) : ℚ) = Q.eval (m : ℚ) := by
    intro m hm
    rw [hE m ((le_max_right _ _).trans hm)]
    have := hQ m ((le_max_left _ _).trans hm)
    simpa using this
  have hconst : ∀ m : ℕ, max (max bQ bE) bT ≤ m →
      ((fwdDiff (1 : ℚ))^[n] Q.eval) (m : ℚ) = (P.flagLength n : ℚ) := by
    intro m hm
    rw [← int_fwdDiff_iter_eq_polynomial P.initialStratum.powerEuler Q (max bQ bE) hQ' n m
      ((le_max_left _ _).trans hm), hT m ((le_max_right _ _).trans hm)]
    simp
  obtain ⟨hdeg, hcoeff⟩ := polynomial_natDegree_le_of_fwdDiff_eventually_const Q n
    (max (max bQ bE) bT) _ hconst
  refine ⟨Q, hdeg, hcoeff, bQ, fun m hm => ?_⟩
  simpa using hQ m hm

/-- **The volume of an ample line bundle is its top self-intersection number:**
`vol(L) = (L^n)`. -/
theorem volume_eq_selfIntersection (P : AmplePolarization f L) (a : LineBundleAtlas L) :
    volume f L n = ENNReal.ofReal (P.selfIntersection n) := by
  obtain ⟨Q, hdeg, hcoeff, b, hb⟩ := P.exists_h0_polynomial_flagLength n a
  -- along `k = q m`, `h⁰(L^{qm}) / (qm)^n → coeff_n(Q) / q^n`
  let R : Polynomial ℝ := Q.map (algebraMap ℚ ℝ)
  have hR : Tendsto (fun m : ℕ => R.eval (m : ℝ) / (m : ℝ) ^ n) atTop (𝓝 (R.coeff n)) :=
    SGPT.Foundations.Schemes.polynomial_eval_div_pow_tendsto_coeff R n (by simpa [R] using hdeg)
  have hsub : Tendsto (fun m : ℕ => (h0 f L (P.power * m) : ℝ) / ((P.power * m : ℕ) : ℝ) ^ n)
      atTop (𝓝 (R.coeff n / (P.power : ℝ) ^ n)) := by
    have h2 := hR.div_const ((P.power : ℝ) ^ n)
    refine h2.congr' ?_
    filter_upwards [eventually_ge_atTop b] with m hm
    have he : R.eval (m : ℝ) = (h0 f L (P.power * m) : ℝ) := by
      have := hb m hm
      have h' : R.eval (m : ℝ) = algebraMap ℚ ℝ (Q.eval (m : ℚ)) := by
        simpa only [R, map_natCast] using
          (Polynomial.eval_map_apply (algebraMap ℚ ℝ) (p := Q) (m : ℚ))
      rw [h', ← this]
      simp
    rw [he, Nat.cast_mul, mul_pow]
    ring
  have hE : Tendsto (fun m : ℕ => ((n ! : ℝ≥0∞) * (h0 f L (P.power * m) : ℝ≥0∞)) /
      ((P.power * m : ℕ) : ℝ≥0∞) ^ n) atTop
      (𝓝 (ENNReal.ofReal ((n ! : ℝ) * (R.coeff n / (P.power : ℝ) ^ n)))) := by
    have h := ENNReal.tendsto_ofReal (hsub.const_mul (n ! : ℝ))
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with m hm
    exact (QuasiPolynomial.ennreal_ratio_eq_ofReal (h0 f L) n (P.power * m)
      (Nat.mul_pos P.power_pos hm)).symm
  have hmul : Tendsto (fun m : ℕ => P.power * m) atTop atTop :=
    tendsto_atTop_mono (fun m => Nat.le_mul_of_pos_left m P.power_pos) tendsto_id
  have hfull := (P.tendsto_volume a n).comp hmul
  have huniq := tendsto_nhds_unique hfull hE
  rw [huniq]
  congr 1
  have hc : (n ! : ℝ) * R.coeff n = (P.flagLength n : ℝ) := by
    have := congrArg (fun x : ℚ => (x : ℝ)) hcoeff
    simpa [R] using this
  unfold selfIntersection
  rw [← hc]
  ring

/-- **Asymptotic Riemann–Roch for ample line bundles.** For `n ≥ 1`,
`h⁰(X, L^k) = (L^n)/n! · k^n + O(k^{n-1})`. -/
theorem h0_sub_selfIntersection_isBigO (P : AmplePolarization f L) (a : LineBundleAtlas L)
    (hn : 1 ≤ n) :
    (fun k : ℕ => (h0 f L k : ℝ) - (P.selfIntersection n / (n ! : ℝ)) * (k : ℝ) ^ n)
      =O[atTop] (fun k : ℕ => (k : ℝ) ^ (n - 1)) := by
  have hvol := P.volume_eq_selfIntersection n a
  have hfin : volume f L n ≠ ∞ := by
    rw [hvol]
    exact ENNReal.ofReal_ne_top
  have h := P.h0_sub_isBigO a hn hfin
  rwa [hvol, ENNReal.toReal_ofReal (P.selfIntersection_nonneg n)] at h

/-- **Asymptotic Riemann–Roch, limit form:** `n! h⁰(X, L^k) / k^n → (L^n)`. -/
theorem tendsto_h0_selfIntersection (P : AmplePolarization f L) (a : LineBundleAtlas L) :
    Tendsto (fun k : ℕ => (n ! : ℝ) * (h0 f L k : ℝ) / (k : ℝ) ^ n) atTop
      (𝓝 (P.selfIntersection n)) := by
  have hvol := P.volume_eq_selfIntersection n a
  have hfin : volume f L n ≠ ∞ := by
    rw [hvol]
    exact ENNReal.ofReal_ne_top
  have h := P.tendsto_real_volume a hfin
  rwa [hvol, ENNReal.toReal_ofReal (P.selfIntersection_nonneg n)] at h

/-- `(L^n)` does not depend on the polarization (nor on the regular sections chosen). -/
theorem selfIntersection_eq (P P' : AmplePolarization f L) (a : LineBundleAtlas L) :
    P.selfIntersection n = P'.selfIntersection n := by
  have h1 := P.volume_eq_selfIntersection n a
  have h2 := P'.volume_eq_selfIntersection n a
  rw [h1] at h2
  exact (ENNReal.ofReal_eq_ofReal_iff (P.selfIntersection_nonneg n)
    (P'.selfIntersection_nonneg n)).mp h2

/-- An ample line bundle is big (in the section-growth sense) iff `(L^n) > 0`. -/
theorem isBig_iff_selfIntersection_pos (P : AmplePolarization f L) (a : LineBundleAtlas L) :
    IsBig f L n ↔ 0 < P.selfIntersection n := by
  rw [← ENNReal.ofReal_pos, ← P.volume_eq_selfIntersection n a]
  exact ⟨fun h => h.volume_pos, fun h => P.isBig_of_volume_pos a h⟩

end AmplePolarization

end SGPT.LineBundle
