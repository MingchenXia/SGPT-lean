import SGPT.Foundations.Analysis.Pending.ConvexCombEnvelopeMass
import SGPT.Foundations.Analysis.Pending.ThetaPshTruncatedAffineLimitInterface

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Copy-4 `lem:positive-rooftop`, and Xia's Lemma 2.4.4 (Step 1) for big classes without Boucksom 4.8

Source: Copy-4, `lem:positive-rooftop`
(`references/transcendental-nakamaye-copy4-20260911/source/main-Nulllocus.tex:1539-1585`):

> For every sufficiently large dyadic `m`, there is `h_C ∈ PSH(V, β_m)` with
> `h_C ≤ Cu - (C-1)φ_m` quasi-everywhere and `∫_V (β_m)_{h_C}^k ≥ 2^{-k-1} h`.
> [...] `w := P_{β_m}(2Cu - (2C-1)φ_m) ∈ PSH(V, β_m)_{>0}` [...] `h_C := ½(w + φ_m)` [...]
> `∫(β_m)_{h_C}^k ≥ 2^{-k} ∫(β_m)_{φ_m}^k = 2^{-k} b_m`.

Copy-4 obtains `w` from Xia's Theorem 6.1.1 (`u ≼_P φ_m`).  As recorded in
`scratch/tn23-envelopes-qea-plan-0117.md` §5.2 (valid in both routes), Xia's **Lemma 2.4.4**
suffices once `φ_m` is replaced by a `β_m`-psh `ψ ≥ u` of the same mass (e.g. `P_{β_m}[φ_m]`):
with `a = 2C` it gives `η` with `(2C)⁻¹η + (1 - (2C)⁻¹)ψ ≤ u`, and `h_C := ½ψ + ½η` satisfies
`h_C + (C-1)ψ ≤ C u` **everywhere** and `∫(β_m)_{h_C}^k ≥ 2^{-k}∫(β_m)_ψ^k`.  Only Step 1 of
Lemma 2.4.4 (a competitor exists) is used; the mass of `η` itself is never needed.

The tree's Lemma 2.4.4 (`ConvexCombEnvelopeMass.exists_thetaPsh_convexCombBarrier`) reaches
`sorryAx` through the named input `UniformAmbientVolumeBigness` (Boucksom 4.8), and only through
classes that are NOT big (`NonBigPotentialMass`).  Every class Copy-4 applies it to is big
(`β_m = γ + η_m ω_V` contains the Kähler current `γ_u + η_m ω_V`), so:

* `exists_thetaPsh_convexCombBarrier_of_isBigClass` — Lemma 2.4.4, Step 1, for a big class,
  **axiom-clean**: Step 1.3 through
  `ThetaPshTruncatedAffineLimitMassChain.exists_ne_bot_truncatedAffineLimit_of_isBigClass`, i.e.
  Xia's Theorem 2.4.4 at the affine obstacle for a big class
  (`DominationPrincipleAffineContactProof.xiaTheorem244_affineObstacle_noncontact_eq_zero_of_le_of_isBigClass`);
* `exists_positiveRooftop` — `lem:positive-rooftop` in the form above, on any compact connected
  Kähler manifold;
* `eventually_isAdmissibleWeight` — the admissibility `(2C)^k (b_m - a_m) < b_m` for large `m`
  from `a_m ≥ L > 0` and `b_m → L` (Copy-4: `a_m ≥ ∫γ_u^k = h` by monotonicity in the background,
  `b_m → h`).

Programme `TN.2.3.PCI`, piece C5 of `scratch/tn23-envelopes-qea-plan-0117.md` §5.3.  Sorry-free.
-/

open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace SGPT.Foundations.Analysis.Pending.PositiveCurrentRooftop

noncomputable section

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Foundations.Analysis.Pending.ThetaPshConvexCombination
open SGPT.Foundations.Analysis.Pending.ConvexCombEnvelopeMass

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [Nonempty M]

/-! ### Lemma 2.4.4, Step 1, for a big class -/

/-- Xia's Step 1.3 (`η ≢ -∞`) in the predicate form of the Step-1 assembly, for a big class. -/
theorem hasNondegenerateTruncatedAffineLimit_of_isBigClass [ConnectedSpace M]
    (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative theta)) (a : ℝ) :
    ThetaPshTruncatedAffineLimit.HasNondegenerateTruncatedAffineLimit (n := n) theta a :=
  fun _u _v hu hv hle _hv0 hfix hpos hadm =>
    ThetaPshTruncatedAffineLimitMassChain.exists_ne_bot_truncatedAffineLimit_of_isBigClass
      omega theta hu hv hle hfix hbig hpos hadm

/-- **Xia, SGPT, Lemma 2.4.4, Step 1, for a big class** (`xia-sgpt:page-0083`--`page-0086`):
for `φ ≤ ψ` in `PSH(X, θ)` with `∫θ_φ^n > 0` and an admissible weight `a`, some `η ∈ PSH(X, θ)`
satisfies `a⁻¹η + (1 - a⁻¹)ψ ≤ φ`.  Same statement as
`ConvexCombEnvelopeMass.exists_thetaPsh_convexCombBarrier` plus `IsBigClass {θ}`; unlike that
theorem it does not rest on Boucksom 4.8. -/
theorem exists_thetaPsh_convexCombBarrier_of_isBigClass [ConnectedSpace M]
    (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative theta)) {phi psi : M → EReal}
    (hphi : IsThetaPshPotential theta.val phi)
    (hpsi : IsThetaPshPotential theta.val psi) (hle : phi ≤ psi)
    (hpos : 0 < diagonalPotentialMass theta phi hphi) {a : ℝ}
    (ha : IsAdmissibleWeight n (diagonalPotentialMass theta phi hphi)
      (diagonalPotentialMass theta psi hpsi) a) :
    ∃ eta : M → EReal, IsThetaPshPotential theta.val eta ∧ convexComb a⁻¹ eta psi ≤ phi :=
  RooftopConvexCombBarrierStepOneAssembly.exists_thetaPsh_convexCombBarrier_of_nondegenerateTruncatedAffineLimit
    omega theta hphi hpsi hle hpos ha
    (hasNondegenerateTruncatedAffineLimit_of_isBigClass omega theta hbig a)

/-! ### `lem:positive-rooftop` -/

/-- The pointwise algebra of `lem:positive-rooftop`: if `(2C)⁻¹e + (1 - (2C)⁻¹)p ≤ w` then
`½p + ½e + (C-1)p ≤ C w`, for extended reals `e, p ≠ ⊤` (poles allowed). -/
theorem half_add_le_of_convexCombValue_le {C : ℕ} (hC : 1 ≤ C) {e p w : EReal}
    (he : e ≠ ⊤) (hp : p ≠ ⊤)
    (h : ((((2 * C : ℕ) : ℝ)⁻¹ : ℝ) : EReal) * e + ((1 - ((2 * C : ℕ) : ℝ)⁻¹ : ℝ) : EReal) * p ≤
      w) :
    ((1 / 2 : ℝ) : EReal) * p + ((1 - 1 / 2 : ℝ) : EReal) * e +
        (((C - 1 : ℕ) : ℝ) : EReal) * p ≤ ((C : ℝ) : EReal) * w := by
  have hCpos : (0 : ℝ) < C := by exact_mod_cast hC
  induction p using EReal.rec with
  | bot =>
      rw [EReal.coe_mul_bot_of_pos (by norm_num), EReal.bot_add, EReal.bot_add]
      exact bot_le
  | top => exact absurd rfl hp
  | coe p =>
      induction e using EReal.rec with
      | bot =>
          rw [EReal.coe_mul_bot_of_pos (by norm_num), EReal.add_bot, EReal.bot_add]
          exact bot_le
      | top => exact absurd rfl he
      | coe e =>
          induction w using EReal.rec with
          | bot =>
              rw [← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add] at h
              exact absurd (le_bot_iff.mp h) (EReal.coe_ne_bot _)
          | top =>
              rw [EReal.coe_mul_top_of_pos hCpos]
              exact le_top
          | coe w =>
              rw [← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add,
                EReal.coe_le_coe_iff] at h
              rw [← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_mul,
                ← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff]
              have h2C : ((2 * C : ℕ) : ℝ) = 2 * (C : ℝ) := by push_cast; ring
              rw [h2C] at h
              have hC1 : ((C - 1 : ℕ) : ℝ) = (C : ℝ) - 1 := by
                rw [Nat.cast_sub hC]; simp
              rw [hC1]
              have key : (C : ℝ) * ((2 * (C : ℝ))⁻¹ * e + (1 - (2 * (C : ℝ))⁻¹) * p) ≤
                  (C : ℝ) * w := mul_le_mul_of_nonneg_left h hCpos.le
              have hsimp : (C : ℝ) * ((2 * (C : ℝ))⁻¹ * e + (1 - (2 * (C : ℝ))⁻¹) * p) =
                  1 / 2 * p + (1 - 1 / 2) * e + ((C : ℝ) - 1) * p := by
                field_simp
                ring
              linarith

/-- **Copy-4 `lem:positive-rooftop`** (with Lemma 2.4.4 in place of Xia's Theorem 6.1.1, see
the module docstring).  On a compact connected Kähler manifold, let `β` be a big class, `u ≤ ψ`
two `β`-psh potentials with `∫β_u^n > 0`, and `C ≥ 1` such that `2C` is admissible for the masses
(`(2C)^n (∫β_ψ^n - ∫β_u^n) < ∫β_ψ^n`).  Then there is a `β`-psh potential `h` with
`h + (C-1)ψ ≤ C u` everywhere and `2^{-n} ∫β_ψ^n ≤ ∫β_h^n`. -/
theorem exists_positiveRooftop [ConnectedSpace M] (omega : KahlerBackground n M)
    (β : ClosedRealOneOneForm n M) (hbig : IsBigClass (RealBottChern.ofRepresentative β))
    {u ψ : M → EReal} (hu : IsThetaPshPotential β.val u) (hψ : IsThetaPshPotential β.val ψ)
    (hle : u ≤ ψ) (hpos : 0 < diagonalPotentialMass β u hu) {C : ℕ} (hC : 1 ≤ C)
    (hadm : IsAdmissibleWeight n (diagonalPotentialMass β u hu)
      (diagonalPotentialMass β ψ hψ) ((2 * C : ℕ) : ℝ)) :
    ∃ h : M → EReal, ∃ hh : IsThetaPshPotential β.val h,
      (∀ x, h x + (((C - 1 : ℕ) : ℝ) : EReal) * ψ x ≤ ((C : ℝ) : EReal) * u x) ∧
      ENNReal.ofReal ((1 / 2 : ℝ) ^ n) * diagonalPotentialMass β ψ hψ ≤
        diagonalPotentialMass β h hh := by
  obtain ⟨η, hη, hbar⟩ :=
    exists_thetaPsh_convexCombBarrier_of_isBigClass omega β hbig hu hψ hle hpos hadm
  have hhalf0 : (0 : ℝ) < 1 / 2 := by norm_num
  have hhalf1 : (1 / 2 : ℝ) < 1 := by norm_num
  refine ⟨convexComb (1 / 2) ψ η, isThetaPshPotential_convexComb hψ hη hhalf0 hhalf1,
    fun x => ?_, ?_⟩
  · have hb := hbar x
    simp only [convexComb_apply] at hb ⊢
    exact half_add_le_of_convexCombValue_le hC (hη.1.quasiPlurisubharmonic.ne_top x)
      (hψ.1.quasiPlurisubharmonic.ne_top x) hb
  · exact GlobalDiagonalConvexScaling.globalMixedMeasure_diagonal_convexComb_le hψ hη hhalf0
      hhalf1 univ

/-- **The admissible weight for large levels**: if `a_m ≥ L > 0` for all `m` and `b_m → L < ∞`,
then for every `t > 1` eventually `t^n (b_m - a_m) < b_m` (Copy-4: "In particular
`(2C)^k a_m > ((2C)^k - 1) b_m` for all large `m`"). -/
theorem eventually_isAdmissibleWeight {a b : ℕ → ℝ≥0∞} {L : ℝ≥0∞} (hL : 0 < L) (hLtop : L ≠ ⊤)
    (ha : ∀ m, L ≤ a m) (hb : Tendsto b atTop (𝓝 L)) {t : ℝ} (ht : 1 < t) :
    ∀ᶠ m in atTop, IsAdmissibleWeight n (a m) (b m) t := by
  have hsub : Tendsto (fun m => b m - L) atTop (𝓝 0) := by
    have := ENNReal.Tendsto.sub hb (tendsto_const_nhds (x := L)) (Or.inr hLtop)
    simpa using this
  have hmul : Tendsto (fun m => ENNReal.ofReal (t ^ n) * (b m - L)) atTop (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (t ^ n)) hsub
      (Or.inr ENNReal.ofReal_ne_top)
    simpa using this
  have h1 : ∀ᶠ m in atTop, ENNReal.ofReal (t ^ n) * (b m - L) < L / 2 :=
    hmul.eventually (gt_mem_nhds (ENNReal.half_pos hL.ne'))
  have h2 : ∀ᶠ m in atTop, L / 2 < b m :=
    hb.eventually (lt_mem_nhds (ENNReal.half_lt_self hL.ne' hLtop))
  filter_upwards [h1, h2] with m hm1 hm2
  refine ⟨ht, lt_of_le_of_lt ?_ (hm1.trans hm2)⟩
  gcongr
  exact ha m

end

end SGPT.Foundations.Analysis.Pending.PositiveCurrentRooftop
