import SGPT.TestCurve.TCLinChartRing
import SGPT.Foundations.Schemes.NativePositiveCoordinatePowerCoefficients

/-!
# The chart condition of an ample test configuration

Let `(𝓧, 𝓛)` be an ample test configuration in the sense of lane TC-ENC
(`TCEnc.TestConfiguration.IsAmple`): `𝓛^r ≅ ι^* 𝒪(1)` for `ι : 𝓧 ⟶ ℙᴺ` with
`(ι, π) : 𝓧 ↪ ℙᴺ × 𝔸¹` a closed immersion. The coordinate sections `s_i = ι^* X_i ∈ H⁰(𝓧, 𝓛^r)`
(`coordSec`, SGPT.Foundations.Schemes's `nativePositiveProjectiveCoordinateSection`) have no common zeros
(`noCommonZero_coordSec`) and satisfy the chart condition of `TCLin.ChartCondition`
(`chartCondition_coordSec`): for `σ ∈ H⁰(𝓧, 𝓛^{rk})`, the coefficient of `σ` in the frame
`s_i^k` of `𝓛^{rk}` over the chart `𝓧_i = ι⁻¹(D₊(X_i))` is a regular function on `𝓧_i`, hence a
polynomial `Q(t, s_l / s_i)` (`TCLin.exists_mvPolynomial_chart`); clearing denominators gives
`s_i^{D+1} σ = Σ q · t^a s^β` on `𝓧_i`, and the identity extends to `𝓧` since `𝓧` is integral and
the nonvanishing locus of `s_i` is `𝓧_i`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.TestCurve.TCLin

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry SGPT.Foundations.Schemes SGPT.LineBundle
open Opposite SGPT.TestCurve.TestConfig SGPT.TestCurve.TCEnc SGPT.TestCurve.FGRel

attribute [local instance] MvPolynomial.gradedAlgebra

/-! ### Coordinate sections and their frames -/

section Frames

variable {Y : Scheme.{0}} {M : Y.Modules} (b : LineBundleAtlas M) {N r : ℕ}
  (ι : Y ⟶ polynomialProj ℂ N)
  (e : bundleTensorPower M r ≅ (Scheme.Modules.pullback ι).obj (polynomialProjTwistingLine ℂ N).sheaf)

/-- The line bundle `M` with the atlas `b`. -/
abbrev lineOf : IntrinsicLineBundle Y := ⟨M, b⟩

/-- **The coordinate section `s_i = ι^* X_i ∈ H⁰(Y, M^r)`** (through `e : M^r ≅ ι^* 𝒪(1)`). -/
def coordSec (i : Fin (N + 1)) : bundlePowerGlobalSections M r :=
  nativePositiveProjectiveCoordinateSection ℂ N ι (lineOf b) r e i

/-- The chart `Y_i = ι⁻¹(D₊(X_i))`. -/
abbrev chartOpen (i : Fin (N + 1)) : Y.Opens := ι ⁻¹ᵁ polynomialProjCoordinateOpen ℂ N i

/-- The pulled-back ratio `ι^♯(X_j / X_i)` on `Y_i`. -/
abbrev chartRatio (i j : Fin (N + 1)) : Γ(Y, chartOpen ι i) :=
  ι.app _ (polynomialProjCoordinateRegularRatio ℂ N i j)

/-- The coefficient of a global section of `M^n` in the frame of the chart `c` of `b`, on an open
`V ⊆ U_c`. -/
def locCoeff (n : ℕ) (c : b.I) {V : Y.Opens} (k : V ⟶ b.opens c)
    (s : bundlePowerGlobalSections M n) : Y.sheaf.obj.obj (op V) :=
  ((b.frame c).tensorPower n).coefficients k ((bundleTensorPower M n).val.map (homOfLE le_top).op s)

theorem locCoeff_eq (n : ℕ) (c : b.I) {V : Y.Opens} (k : V ⟶ b.opens c)
    (s : bundlePowerGlobalSections M n) :
    locCoeff b n c k s = Y.sheaf.obj.map k.op (atlasPowerGlobalCoefficients b n c s) :=
  LocalBundleFrame.global_coefficients_restrict (b.frame c) n k s

theorem coordSec_coeff_one (i : Fin (N + 1)) {V : Y.Opens} (h : V ⟶ chartOpen ι i) :
    (nativePositiveProjectiveCoordinateFrame ℂ N ι (lineOf b) r e i).coefficients h
      ((bundleTensorPower M r).val.map (homOfLE le_top).op (coordSec b ι e i)) = 1 :=
  nativePositiveProjectiveCoordinateSection_coefficients ℂ N ι (lineOf b) r e i h

theorem coordSec_coeff_ratio (i j : Fin (N + 1)) {V : Y.Opens} (h : V ⟶ chartOpen ι i) :
    (nativePositiveProjectiveCoordinateFrame ℂ N ι (lineOf b) r e i).coefficients h
      ((bundleTensorPower M r).val.map (homOfLE le_top).op (coordSec b ι e j)) =
      Y.sheaf.obj.map h.op (chartRatio ι i j) :=
  nativePositiveProjectiveCoordinateSection_cross_coefficients_subordinate ℂ N ι (lineOf b) r e
    i j h

/-- On `V ⊆ Y_i ∩ U_c`: `s_j = s_i · ι^♯(X_j / X_i)`. -/
theorem locCoeff_coordSec (i j : Fin (N + 1)) (c : b.I) {V : Y.Opens} (h : V ⟶ chartOpen ι i)
    (k : V ⟶ b.opens c) :
    locCoeff b r c k (coordSec b ι e j) =
      locCoeff b r c k (coordSec b ι e i) * Y.sheaf.obj.map h.op (chartRatio ι i j) := by
  let C := nativePositiveProjectiveCoordinateFrame ℂ N ι (lineOf b) r e i
  have t1 := localBundleFrameTransition_coefficients C ((b.frame c).tensorPower r) h k
    ((bundleTensorPower M r).val.map (homOfLE le_top).op (coordSec b ι e j))
  have t2 := localBundleFrameTransition_coefficients C ((b.frame c).tensorPower r) h k
    ((bundleTensorPower M r).val.map (homOfLE le_top).op (coordSec b ι e i))
  rw [coordSec_coeff_one, mul_one] at t2
  rw [coordSec_coeff_ratio] at t1
  unfold locCoeff
  rw [t1, t2]

/-- On `V ⊆ Y_i ∩ U_c` the coefficient of `s_i` is a unit. -/
theorem isUnit_locCoeff_coordSec (i : Fin (N + 1)) (c : b.I) {V : Y.Opens}
    (h : V ⟶ chartOpen ι i) (k : V ⟶ b.opens c) : IsUnit (locCoeff b r c k (coordSec b ι e i)) := by
  let C := nativePositiveProjectiveCoordinateFrame ℂ N ι (lineOf b) r e i
  have t2 := localBundleFrameTransition_coefficients C ((b.frame c).tensorPower r) h k
    ((bundleTensorPower M r).val.map (homOfLE le_top).op (coordSec b ι e i))
  rw [coordSec_coeff_one, mul_one] at t2
  unfold locCoeff
  rw [t2]
  exact Units.isUnit _

/-- **The chart coefficient `g_σ`** of `σ ∈ H⁰(Y, M^{rk})`: its coefficient in the frame `s_i^k`
over `Y_i`. -/
def chartCoeff (k : ℕ) (i : Fin (N + 1)) (σ : bundlePowerGlobalSections M (r * k)) :
    Γ(Y, chartOpen ι i) :=
  (nativePositiveProjectivePowerFrame ℂ N ι (lineOf b) r e k i).coefficients (𝟙 _)
    ((bundleTensorPower M (r * k)).val.map (homOfLE le_top).op σ)

/-- On `V ⊆ Y_i ∩ U_c`: `σ = g_σ · s_i^k`. -/
theorem locCoeff_eq_chartCoeff (k : ℕ) (i : Fin (N + 1)) (c : b.I) {V : Y.Opens}
    (h : V ⟶ chartOpen ι i) (kk : V ⟶ b.opens c) (σ : bundlePowerGlobalSections M (r * k)) :
    locCoeff b (r * k) c kk σ =
      locCoeff b r c kk (coordSec b ι e i) ^ k * Y.sheaf.obj.map h.op (chartCoeff b ι e k i σ) := by
  let P := nativePositiveProjectivePowerFrame ℂ N ι (lineOf b) r e k i
  let A := (b.frame c).tensorPower (r * k)
  have t := localBundleFrameTransition_coefficients P A h kk
    ((bundleTensorPower M (r * k)).val.map (homOfLE le_top).op σ)
  have t0 := localBundleFrameTransition_coefficients P A h kk ((P.coefficients h).symm 1)
  rw [LinearEquiv.apply_symm_apply, mul_one] at t0
  have hunit := nativePositiveProjectivePowerFrame_unit_originalCoefficients ℂ N ι (lineOf b) r e
    k i c h kk
  rw [t0] at hunit
  have hres := P.coefficients_restrict (𝟙 _) h
    ((bundleTensorPower M (r * k)).val.map (homOfLE le_top).op σ)
  rw [Category.comp_id, ← PresheafOfModules.map_comp_apply] at hres
  unfold locCoeff chartCoeff
  rw [t, hunit]
  congr 1

end Frames

/-! ### Extension from a chart on an integral scheme -/

/-- On an integral scheme, a function vanishing on an open containing the nonvanishing locus of
`u` is killed by `u`. -/
theorem mul_eq_zero_of_restrict {Y : Scheme.{0}} [IsIntegral Y] {U V : Y.Opens} (hVU : V ≤ U)
    (f u : Γ(Y, U)) (hu : Y.basicOpen u ≤ V)
    (hf : Y.presheaf.map (homOfLE hVU).op f = 0) : f * u = 0 := by
  by_cases hne : (Y.basicOpen u : Set Y).Nonempty
  · have : Nonempty (Y.basicOpen u) := ⟨⟨hne.some, hne.some_mem⟩⟩
    have hf' : Y.presheaf.map (homOfLE (Y.basicOpen_le u)).op f = 0 := by
      have : (homOfLE (Y.basicOpen_le u)).op = (homOfLE hVU).op ≫ (homOfLE hu).op := rfl
      rw [this, Functor.map_comp, CommRingCat.comp_apply, hf, map_zero]
    have := map_injective_of_isIntegral Y (homOfLE (Y.basicOpen_le u))
      (hf'.trans (map_zero _).symm)
    rw [this, zero_mul]
  · have hbot : Y.basicOpen u = ⊥ := by
      ext x
      simp only [TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
      exact fun hx => hne ⟨x, hx⟩
    rw [AlgebraicGeometry.basicOpen_eq_bot_iff] at hbot
    rw [hbot, mul_zero]

/-! ### Coefficients of monomials -/

section MonomialCoeff

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} {L : X.Modules} {a : LineBundleAtlas L}
  (T : TestConfiguration f a) {N r : ℕ} (s : Fin (N + 1) → SectionSpace T.structureMap T.line r)

/-- The chart coefficients of the monomial `t^a s^β` are `t^a Π_l (s_l)_c^{β_l}`. -/
theorem exists_monomial_coeff (a' : ℕ) (β : Fin (N + 1) →₀ ℕ) :
    ∃ (M : ℕ) (σ0 : SectionSpace T.structureMap T.line M), M = r * expSum β ∧
      secMonomialξ T s a' β = SecRing.of M σ0 ∧
      ∀ c, atlasPowerGlobalCoefficients T.extAtlas M c σ0 =
        (T.space.sheaf.obj.map (homOfLE le_top).op (tFun T.toLine)) ^ a' *
          β.prod fun l e => atlasPowerGlobalCoefficients T.extAtlas r c (s l) ^ e := by
  classical
  have hβ : ∃ (M : ℕ) (σ0 : SectionSpace T.structureMap T.line M), M = r * expSum β ∧
      (β.prod fun l e => (SecRing.of r (s l) : SecRing T.structureMap T.extAtlas) ^ e) =
        SecRing.of M σ0 ∧ ∀ c, atlasPowerGlobalCoefficients T.extAtlas M c σ0 =
          β.prod fun l e => atlasPowerGlobalCoefficients T.extAtlas r c (s l) ^ e := by
    induction β using Finsupp.induction with
    | zero =>
      refine ⟨0, secOne T.structureMap T.line, by simp [expSum], rfl, fun c => ?_⟩
      rw [Finsupp.prod_zero_index]
      exact atlasPowerGlobalCoefficients_one T.extAtlas c
    | single_add i e β hi he ih =>
      obtain ⟨M, σ0, hM, hprod, hc⟩ := ih
      refine ⟨r * e + M, SectionSpace.mul T.structureMap T.extAtlas (r * e) M
        (secPow T.extAtlas (s i) e) σ0, ?_, ?_, fun c => ?_⟩
      · rw [hM, expSum, expSum, Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
          Finsupp.sum_single_index rfl, mul_add]
      · rw [Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _),
          Finsupp.prod_single_index (by rw [pow_zero]), hprod]
        have hpow : ∀ e : ℕ, (SecRing.of r (s i) : SecRing T.structureMap T.extAtlas) ^ e =
            SecRing.of (r * e) (secPow T.extAtlas (s i) e) := by
          intro e
          induction e with
          | zero => rfl
          | succ e ihe => rw [pow_succ, ihe, SecRing.of_mul_of]; rfl
        rw [hpow, SecRing.of_mul_of]
      · rw [Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _),
          Finsupp.prod_single_index (by rw [pow_zero]), SectionSpace.coefficients_mul,
          coeff_secPow, hc c]
  obtain ⟨M, σ0, hM, hprod, hc⟩ := hβ
  have htpow : ∀ n : ℕ, ∃ τ : SectionSpace T.structureMap T.line 0,
      tSecRing T ^ n = SecRing.of 0 τ ∧ ∀ c, atlasPowerGlobalCoefficients T.extAtlas 0 c τ =
        (T.space.sheaf.obj.map (homOfLE le_top).op (tFun T.toLine)) ^ n := by
    intro n
    induction n with
    | zero =>
      refine ⟨secOne T.structureMap T.line, rfl, fun c => ?_⟩
      rw [pow_zero]
      exact atlasPowerGlobalCoefficients_one T.extAtlas c
    | succ n ih =>
      obtain ⟨τ, hτ, hτc⟩ := ih
      refine ⟨SectionSpace.mul T.structureMap T.extAtlas 0 0 τ
        (show SectionSpace T.structureMap T.line 0 from tFun T.toLine), ?_, fun c => ?_⟩
      · rw [pow_succ, hτ, tSecRing, SecRing.of_mul_of]
      · dsimp only
        refine (SectionSpace.coefficients_mul T.structureMap T.extAtlas 0 0 c τ
          (tFun T.toLine)).trans ?_
        rw [hτc c, pow_succ]
        congr 1
  obtain ⟨τ, hτ, hτc⟩ := htpow a'
  refine ⟨0 + M, SectionSpace.mul T.structureMap T.extAtlas 0 M τ σ0, by rw [zero_add, hM],
    ?_, fun c => ?_⟩
  · rw [secMonomialξ, hτ, hprod, SecRing.of_mul_of]
  · rw [SectionSpace.coefficients_mul, hτc c, hc c]

end MonomialCoeff

end SGPT.TestCurve.TCLin
