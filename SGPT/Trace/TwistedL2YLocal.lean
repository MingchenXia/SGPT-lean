import SGPT.Trace.TwistedL2DDensity
import SGPT.Trace.TwistedL2XDefect

/-!
# Friedrichs' lemma for `W ↦ (ϑ_p W, ∂̄(σ^♭ W))` with general coefficients

Blueprint `claude-tl2-man2.tex` (lane TL2-MAN2, `claude-tl2-man2:local`).  This is the
chart-local step of the density argument (`claude-tl2-dens:local`) written for arbitrary smooth
coefficients on an open set `D₀ ⊆ ℂⁿ`: a weight `p` and a matrix `S = (σ_{lk})`.  On a manifold it
is applied in every chart-frame `(c, e)` with `D₀ = dom(c, e)`, `p = p_{ce}` and `S = σ_c`; on `ℂⁿ`
it is `TwistedDatum.exists_approx`.

For a locally `L²` field `W` on `D₀` satisfying the two weak equations

* `∫ (conj ∂_kψ (σ^♭W)_j - conj ∂_jψ (σ^♭W)_k) = 0` for test functions `ψ` on `D₀`
  (`∂̄(σ^♭ W) = 0` weakly), and
* `∫ e^{-p} ∑_l ∂_{l̄} u conj W_l = ∫ u conj Θ e^{-p}` for test functions `u` on `D₀`
  (`ϑ_p W = Θ` weakly),

and a real test function `ζ` on `D₀`, the localized field `ζ W` satisfies `P(ζW) = f` weakly, with
`f_ϑ = ζ Θ - ∑_l ∂_l ζ W_l` and `f_{jk} = ∂_{j̄}ζ (σ^♭W)_k - ∂_{k̄}ζ (σ^♭W)_j` (`weak_eqG`), and
Friedrichs' lemma gives smooth approximations (`exists_approxG`).
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Trace.TwistedL2

open Set Filter MeasureTheory Matrix Bundle Metric
open scoped Topology ContDiff ComplexConjugate ComplexOrder Manifold InnerProductSpace ENNReal NNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.Pending.CauchyGreen SGPT.Foundations.Analysis.Pending.Hormander
  SGPT.Foundations.Analysis.Pending.OTChen
open SGPT.Bergman.TensorDictionaryDraft
open HermitianHolomorphicLineBundle

variable {n : ℕ}

/-! ### The system with general coefficients -/

section System

variable (S : ComplexModel n → Matrix (Fin n) (Fin n) ℂ) (p : ComplexModel n → ℝ)

/-- The `∂̄`-coefficients of the `∂̄σ^♭`-rows: `δ_{mj} S_{ik} - δ_{mk} S_{ij}`. -/
def sysA'G (m : Fin n) (z : ComplexModel n) : Matrix (Fin (n * n + 1)) (Fin n) ℂ :=
  Matrix.of fun i' i => Fin.lastCases 0 (fun q =>
    (if m = (rowJK q).1 then S z i (rowJK q).2 else 0) -
    (if m = (rowJK q).2 then S z i (rowJK q).1 else 0)) i'

/-- The zero order coefficients: `∂_i p` in the `ϑ`-row, `∂_{j̄}S_{ik} - ∂_{k̄}S_{ij}` in the
`∂̄σ^♭`-rows. -/
def sysBG (z : ComplexModel n) : Matrix (Fin (n * n + 1)) (Fin n) ℂ :=
  Matrix.of fun i' i => Fin.lastCases (dDir (coordVec i) (fun y => (p y : ℂ)) z) (fun q =>
    dbarDir (coordVec (rowJK q).1) (fun y => S y i (rowJK q).2) z -
    dbarDir (coordVec (rowJK q).2) (fun y => S y i (rowJK q).1) z) i'

/-- The lowering `(S^♭ W)_k = ∑_l S_{lk} W_l`. -/
def lowS (W : ComplexModel n → ComplexModel n) (y : ComplexModel n) (k : Fin n) : ℂ :=
  ∑ l, S y l k * W y l

/-- The coefficient matrix `∂_{j̄}(S^♭W)_k - ∂_{k̄}(S^♭W)_j` of `∂̄(S^♭ W)`. -/
def sigmaDbarG (W : ComplexModel n → ComplexModel n) (z : ComplexModel n) :
    Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun j k => dbarDir (coordVec j) (fun y => lowS S W y k) z -
    dbarDir (coordVec k) (fun y => lowS S W y j) z

end System

theorem firstOrderApply_lastG (S : ComplexModel n → Matrix (Fin n) (Fin n) ℂ)
    (p : ComplexModel n → ℝ) (w : Fin n → ComplexModel n → ℂ) (z : ComplexModel n) :
    firstOrderApply (sysA (n := n)) (sysA'G S) (sysBG S p) w (Fin.last _) z =
      chartTheta p (ofComps w) z := by
  simp only [firstOrderApply, sysA, sysA'G, sysBG, of_apply, Fin.lastCases_last, zero_mul,
    add_zero, chartTheta, deltaDir, ofComps]
  have h : ∀ x : Fin n, ∑ x_1 : Fin n, (if x_1 = x then (-1 : ℂ) else 0) *
      dDir (coordVec x) (w x_1) z = -dDir (coordVec x) (w x) z := by
    intro x; simp [ite_mul, Finset.sum_ite_eq']
  rw [Finset.sum_congr rfl fun x _ => h x, Finset.sum_sub_distrib, neg_sub]
  simp only [Finset.sum_neg_distrib]
  ring

theorem firstOrderApply_SG (S : ComplexModel n → Matrix (Fin n) (Fin n) ℂ)
    (p : ComplexModel n → ℝ) (w : Fin n → ComplexModel n → ℂ)
    {z : ComplexModel n} (hσ : ∀ l k, DifferentiableAt ℝ (fun y => S y l k) z)
    (hw : ∀ i, DifferentiableAt ℝ (w i) z) (q : Fin (n * n)) :
    firstOrderApply (sysA (n := n)) (sysA'G S) (sysBG S p) w (Fin.castSucc q) z =
      sigmaDbarG S (ofComps w) z (rowJK q).1 (rowJK q).2 := by
  set j := (rowJK q).1
  set k := (rowJK q).2
  have hD : ∀ a b : Fin n, dbarDir (coordVec a) (fun y => lowS S (ofComps w) y b) z =
      ∑ l, (dbarDir (coordVec a) (fun y => S y l b) z * w l z +
        S z l b * dbarDir (coordVec a) (w l) z) := by
    intro a b
    have hfun : (fun y => lowS S (ofComps w) y b) = fun y => ∑ l, S y l b * w l y := by
      funext y; simp [lowS, ofComps]
    rw [hfun, dbarDir_finset_sum_fun Finset.univ fun l _ =>
      (show DifferentiableAt ℝ (fun y => S y l b * w l y) z from (hσ l b).mul (hw l))]
    exact Finset.sum_congr rfl fun l _ => dbarDir_mul (hσ l b) (hw l)
  simp only [sigmaDbarG, of_apply, hD]
  simp only [firstOrderApply, sysA, sysA'G, sysBG, of_apply, Fin.lastCases_castSucc, zero_mul,
    zero_add]
  have h1 : ∀ (a b : Fin n), ∑ m : Fin n, ∑ i : Fin n,
      (if m = a then S z i b else 0) * dbarDir (coordVec m) (w i) z =
      ∑ i, S z i b * dbarDir (coordVec a) (w i) z := by
    intro a b
    simp [ite_mul, Finset.sum_ite_eq']
  simp only [sub_mul, Finset.sum_sub_distrib, h1, Finset.sum_add_distrib]
  ring

/-! ### The formal adjoint -/

section Adjoint

variable (S : ComplexModel n → Matrix (Fin n) (Fin n) ℂ) (p : ComplexModel n → ℝ)

theorem adj_row_lastG (g : ComplexModel n → ℂ) (hg : ContDiff ℝ ∞ g) (i : Fin n)
    (z : ComplexModel n) :
    (∑ j, (-dbarDir (coordVec j) (fun y => conj (sysA j y (Fin.last (n * n)) i) * g y) z -
      dDir (coordVec j) (fun y => conj (sysA'G S j y (Fin.last (n * n)) i) * g y) z)) +
      conj (sysBG S p z (Fin.last (n * n)) i) * g z =
    dbarDir (coordVec i) g z + conj (dDir (coordVec i) (fun y => (p y : ℂ)) z) * g z := by
  have hgd : DifferentiableAt ℝ g z := hg.differentiable (by simp) z
  simp only [sysA, sysA'G, sysBG, of_apply, Fin.lastCases_last, map_zero, zero_mul]
  have h0 : ∀ j : Fin n, dDir (coordVec j) (fun _ : ComplexModel n => (0 : ℂ)) z = 0 := fun j => by
    simp [dDir]
  have h1 : ∀ j : Fin n, dbarDir (coordVec j)
      (fun y => conj (if i = j then (-1 : ℂ) else 0) * g y) z =
      (if i = j then -dbarDir (coordVec j) g z else 0) := fun j => by
    rw [dbarDir_const_mul_fun _ hgd]
    split_ifs <;> simp
  simp only [h0, h1, sub_zero]
  simp [Finset.sum_ite_eq]

theorem adj_row_SG {g : ComplexModel n → ℂ} (hg : ContDiff ℝ ∞ g) {z : ComplexModel n}
    (hσ : ∀ l k, DifferentiableAt ℝ (fun y => S y l k) z) (q : Fin (n * n))
    (i : Fin n) :
    (∑ j, (-dbarDir (coordVec j) (fun y => conj (sysA j y (Fin.castSucc q) i) * g y) z -
      dDir (coordVec j) (fun y => conj (sysA'G S j y (Fin.castSucc q) i) * g y) z)) +
      conj (sysBG S p z (Fin.castSucc q) i) * g z =
    -conj (S z i (rowJK q).2) * dDir (coordVec (rowJK q).1) g z +
      conj (S z i (rowJK q).1) * dDir (coordVec (rowJK q).2) g z := by
  have hgd : DifferentiableAt ℝ g z := hg.differentiable (by simp) z
  simp only [sysA, sysA'G, sysBG, of_apply, Fin.lastCases_castSucc, map_zero, zero_mul]
  set a := (rowJK q).1
  set b := (rowJK q).2
  have h0 : ∀ j : Fin n, dbarDir (coordVec j) (fun _ : ComplexModel n => (0 : ℂ)) z = 0 :=
    fun j => by simp [dbarDir]
  have hfun : ∀ j : Fin n, (fun y => conj ((if j = a then S y i b else 0) -
      (if j = b then S y i a else 0)) * g y) =
      fun y => (if j = a then conj (S y i b) * g y else 0) -
        (if j = b then conj (S y i a) * g y else 0) := fun j => by
    funext y; split_ifs <;> simp [sub_mul]
  have hd1 : ∀ (j c d : Fin n), DifferentiableAt ℝ
      (fun y => if j = c then conj (S y i d) * g y else 0) z := fun j c d => by
    split_ifs
    · exact ((Complex.conjCLE.toContinuousLinearMap.differentiableAt).comp z (hσ i d)).mul hgd
    · exact differentiableAt_const _
  have hD : ∀ j : Fin n, dDir (coordVec j) (fun y => conj ((if j = a then
      S y i b else 0) - (if j = b then S y i a else 0)) * g y) z =
      (if j = a then dDir (coordVec j) (fun y => conj (S y i b) * g y) z else 0) -
      (if j = b then dDir (coordVec j) (fun y => conj (S y i a) * g y) z else 0) :=
    fun j => by
      rw [hfun j, dDir_sub (hd1 j a b) (hd1 j b a), dDir_ite_fun, dDir_ite_fun]
  simp only [h0, hD, neg_zero, zero_sub, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [dDir_conj_mul (hσ i b) hgd, dDir_conj_mul (hσ i a) hgd]
  simp only [map_sub]
  ring

end Adjoint

theorem adj_eqG (S : ComplexModel n → Matrix (Fin n) (Fin n) ℂ) (p : ComplexModel n → ℝ)
    {D : Set (ComplexModel n)}
    (hσD : ∀ z ∈ D, ∀ l k, DifferentiableAt ℝ (fun y => S y l k) z)
    (h : Fin (n * n + 1) → ComplexModel n → ℂ) (hh : ∀ i', IsTestFunctionOn D (h i'))
    (i : Fin n) (z : ComplexModel n) :
    firstOrderAdjointApply (sysA (n := n)) (sysA'G S) (sysBG S p) h i z =
      (dbarDir (coordVec i) (h (Fin.last _)) z +
        conj (dDir (coordVec i) (fun y => (p y : ℂ)) z) * h (Fin.last _) z) +
      ∑ q : Fin (n * n), (-conj (S z i (rowJK q).2) *
          dDir (coordVec (rowJK q).1) (h q.castSucc) z +
        conj (S z i (rowJK q).1) * dDir (coordVec (rowJK q).2) (h q.castSucc) z) := by
  by_cases hz : z ∈ D
  · rw [firstOrderAdjointApply_eq_sum, Fin.sum_univ_castSucc, adj_row_lastG S p _ (hh _).1,
      Finset.sum_congr rfl fun q _ => adj_row_SG S p (hh _).1 (hσD z hz) q i, add_comm]
  · have hz' : ∀ i', z ∉ tsupport (h i') := fun i' h' => hz ((hh i').2.2 h')
    rw [FriedrichsProof.firstOrderAdjointApply_eq_zero_of_notMem _ _ _ _ _ hz']
    simp [dbarDir_eq_zero_of_notMem (hz' _), dDir_eq_zero_of_notMem (hz' _),
      image_eq_zero_of_notMem_tsupport (hz' _)]

/-! ### Locally `L²` fields -/

/-- `W` is locally `L²` on `D₀`: its restriction to every compact subset of `D₀` is in `L²`. -/
def IsLocL2 (D₀ : Set (ComplexModel n)) (W : ComplexModel n → ComplexModel n) : Prop :=
  ∀ K : Set (ComplexModel n), IsCompact K → K ⊆ D₀ → MemLp (K.indicator W) 2 volume

theorem memLp_W_mul {D₀ : Set (ComplexModel n)} {W : ComplexModel n → ComplexModel n}
    (hW : IsLocL2 D₀ W) {c : ComplexModel n → ℂ} (hc : Continuous c) (hcs : HasCompactSupport c)
    (hcd : tsupport c ⊆ D₀) (i : Fin n) : MemLp (fun z => W z i * c z) 2 volume := by
  set K := tsupport c
  have hK := hW K hcs hcd
  obtain ⟨M, hM⟩ := hcs.exists_bound_of_continuousOn hc.continuousOn
  have heq : (fun z => W z i * c z) = fun z => K.indicator W z i * c z := by
    funext z
    by_cases hz : z ∈ K
    · rw [indicator_of_mem hz]
    · rw [image_eq_zero_of_notMem_tsupport hz, mul_zero, mul_zero]
  rw [heq]
  have hm : AEStronglyMeasurable (fun z => K.indicator W z i * c z) volume :=
    (((EuclideanSpace.proj i : ComplexModel n →L[ℂ] ℂ).continuous).comp_aestronglyMeasurable
      hK.1).mul hc.aestronglyMeasurable
  refine hK.of_le_mul (c := max M 0) hm (Eventually.of_forall fun z => ?_)
  rw [norm_mul]
  by_cases hz : z ∈ K
  · calc ‖K.indicator W z i‖ * ‖c z‖ ≤ ‖K.indicator W z‖ * max M 0 :=
          mul_le_mul (norm_coord_le _ i) ((hM z hz).trans (le_max_left _ _)) (norm_nonneg _)
            (norm_nonneg _)
      _ = max M 0 * ‖K.indicator W z‖ := mul_comm _ _
  · rw [image_eq_zero_of_notMem_tsupport hz, norm_zero, mul_zero]
    exact mul_nonneg (le_max_right _ _) (norm_nonneg _)

theorem integrable_W_mul {D₀ : Set (ComplexModel n)} {W : ComplexModel n → ComplexModel n}
    (hW : IsLocL2 D₀ W) {c : ComplexModel n → ℂ} (hc : Continuous c) (hcs : HasCompactSupport c)
    (hcd : tsupport c ⊆ D₀) (i : Fin n) : Integrable (fun z => W z i * c z) := by
  have hL := memLp_W_mul hW hc hcs hcd i
  set K := tsupport c
  have hfin : IsFiniteMeasure (volume.restrict K) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hcs.isCompact.measure_lt_top⟩
  have hI : IntegrableOn (fun z => W z i * c z) K := (hL.restrict K).integrable (by norm_num)
  refine (integrableOn_iff_integrable_of_support_subset fun z hz => ?_).mp hI
  by_contra h
  exact hz (by simp [image_eq_zero_of_notMem_tsupport h])

/-! ### The weak equations -/

/-- The localized field `w = ζ W`, componentwise. -/
def wsysG (ζ : ComplexModel n → ℝ) (W : ComplexModel n → ComplexModel n) :
    Fin n → ComplexModel n → ℂ := fun i z => (ζ z : ℂ) * W z i

/-- The `ϑ`-row of the weak equation: `f_ϑ = ζ Θ - ∑_l ∂_l ζ W_l`. -/
def f0G (ζ : ComplexModel n → ℝ) (W : ComplexModel n → ComplexModel n)
    (Θ : ComplexModel n → ℂ) (z : ComplexModel n) : ℂ :=
  (ζ z : ℂ) * Θ z - ∑ l, dDir (coordVec l) (fun y => (ζ y : ℂ)) z * W z l

/-- The `∂̄σ^♭`-rows of the weak equation: `f_{jk} = ∂_{j̄}ζ (S^♭W)_k - ∂_{k̄}ζ (S^♭W)_j`. -/
def fSG (S : ComplexModel n → Matrix (Fin n) (Fin n) ℂ) (ζ : ComplexModel n → ℝ)
    (W : ComplexModel n → ComplexModel n) (j k : Fin n) (z : ComplexModel n) : ℂ :=
  dbarDir (coordVec j) (fun y => (ζ y : ℂ)) z * lowS S W z k -
    dbarDir (coordVec k) (fun y => (ζ y : ℂ)) z * lowS S W z j

/-- The right-hand side `f` of the weak equation `P w = f`. -/
def fsysG (S : ComplexModel n → Matrix (Fin n) (Fin n) ℂ) (ζ : ComplexModel n → ℝ)
    (W : ComplexModel n → ComplexModel n) (Θ : ComplexModel n → ℂ) :
    Fin (n * n + 1) → ComplexModel n → ℂ := fun i' =>
  Fin.lastCases (f0G ζ W Θ) (fun q => fSG S ζ W (rowJK q).1 (rowJK q).2) i'

section Weak

variable {D₀ : Set (ComplexModel n)} {p : ComplexModel n → ℝ}
  {S : ComplexModel n → Matrix (Fin n) (Fin n) ℂ} {W : ComplexModel n → ComplexModel n}
  {Θ : ComplexModel n → ℂ}

/-- **The `ϑ`-row of the weak equation**, from `ϑ_p W = Θ` weakly. -/
theorem row_lastG (hD₀ : IsOpen D₀) (hp : ContDiffOn ℝ ∞ p D₀) (hW : IsLocL2 D₀ W)
    (hΘ : ContinuousOn Θ D₀)
    (hW2 : ∀ u : ComplexModel n → ℂ, IsTestFunctionOn D₀ u →
      ∫ z, D₀.indicator (fun z => cweight p z *
        ∑ l, dbarDir (coordVec l) u z * conj (W z l)) z =
      ∫ z, u z * conj (Θ z) * cweight p z)
    {ζ : ComplexModel n → ℝ} (hζ : ContDiff ℝ ∞ ζ) {D : Set (ComplexModel n)}
    (hDd : D ⊆ D₀) {g : ComplexModel n → ℂ} (hg : IsTestFunctionOn D g) :
    ∑ i, ∫ z, wsysG ζ W i z * conj (dbarDir (coordVec i) g z +
      conj (dDir (coordVec i) (fun y => (p y : ℂ)) z) * g z) =
      ∫ z, f0G ζ W Θ z * conj (g z) := by
  set E : ComplexModel n → ℂ := fun y => ((Real.exp (p y) : ℝ) : ℂ) with hE
  have hO := hD₀
  have hpD : ContDiffOn ℝ ∞ p D₀ := hp
  have hED : ContDiffOn ℝ ∞ E D₀ :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn (Real.contDiff_exp.comp_contDiffOn hpD)
  have hgd : tsupport g ⊆ D₀ := hg.2.2.trans hDd
  have hEg : ContDiff ℝ ∞ (fun y => E y * g y) := contDiff_mul_of_tsupport_subset hO hED hg.1 hgd
  have hζc : ContDiff ℝ ∞ (fun y => (ζ y : ℂ)) := Complex.ofRealCLM.contDiff.comp hζ
  set u : ComplexModel n → ℂ := fun y => (ζ y : ℂ) * (E y * g y) with hu_def
  have hEgs : tsupport (fun y => E y * g y) ⊆ tsupport g := tsupport_mul_subset_right
  have hus : tsupport u ⊆ tsupport g := tsupport_mul_subset_right.trans hEgs
  have hu : IsTestFunctionOn D₀ u :=
    ⟨hζc.mul hEg, hg.2.1.mono' (subset_closure.trans hus), hus.trans hgd⟩
  have hWe := hW2 u hu
  have hWc := congrArg conj hWe
  rw [← integral_conj, ← integral_conj] at hWc
  -- the pointwise identities
  have hcw : ∀ z, cweight p z * E z = 1 := fun z => by
    rw [cweight, hE, ← Complex.ofReal_mul, ← Real.exp_add, neg_add_cancel, Real.exp_zero,
      Complex.ofReal_one]
  have hcwc : ∀ z, conj (cweight p z) = cweight p z := fun z => by
    rw [cweight, Complex.conj_ofReal]
  have hEc : ∀ z, conj (E z) = E z := fun z => Complex.conj_ofReal _
  have hpt : ∀ z, conj (D₀.indicator (fun z => cweight p z *
      ∑ l, dbarDir (coordVec l) u z * conj (W z l)) z) =
      ∑ i, (wsysG ζ W i z * conj (dbarDir (coordVec i) g z +
        conj (dDir (coordVec i) (fun y => (p y : ℂ)) z) * g z) +
        W z i * (dDir (coordVec i) (fun y => (ζ y : ℂ)) z * conj (g z))) := by
    intro z
    by_cases hz : z ∈ D₀
    · rw [indicator_of_mem hz]
      have hpz : DifferentiableAt ℝ p z :=
        (hpD.contDiffAt (hO.mem_nhds hz)).differentiableAt (by simp)
      have hζz : DifferentiableAt ℝ ζ z := hζ.differentiable (by simp) z
      have hζz' : DifferentiableAt ℝ (fun y => (ζ y : ℂ)) z := hζc.differentiable (by simp) z
      have hgz : DifferentiableAt ℝ g z := hg.1.differentiable (by simp) z
      have hEz : DifferentiableAt ℝ E z :=
        (hED.contDiffAt (hO.mem_nhds hz)).differentiableAt (by simp)
      have hdu : ∀ l, dbarDir (coordVec l) u z =
          dbarDir (coordVec l) (fun y => (ζ y : ℂ)) z * (E z * g z) +
            (ζ z : ℂ) * (E z * (dbarDir (coordVec l) (fun y => (p y : ℂ)) z * g z +
              dbarDir (coordVec l) g z)) := by
        intro l
        have hEgz : DifferentiableAt ℝ (fun y => E y * g y) z := hEz.mul hgz
        rw [hu_def, dbarDir_mul hζz' hEgz, dbarDir_mul hEz hgz, hE, dbarDir_exp_ofReal hpz]
        ring
      simp only [hdu, map_mul, map_sum, map_add, hcwc, hEc, Complex.conj_ofReal, Complex.conj_conj,
        conj_dbarDir_ofReal hζz, conj_dbarDir_ofReal hpz, Finset.mul_sum, wsysG]
      refine Finset.sum_congr rfl fun l _ => ?_
      linear_combination (conj (g z) * (dDir (coordVec l) (fun y => (ζ y : ℂ)) z +
          (ζ z : ℂ) * dDir (coordVec l) (fun y => (p y : ℂ)) z) * W z l +
        (ζ z : ℂ) * conj (dbarDir (coordVec l) g z) * W z l) * hcw z
    · have hzg : z ∉ tsupport g := fun h => hz (hgd h)
      rw [indicator_of_notMem hz, map_zero]
      simp [image_eq_zero_of_notMem_tsupport hzg, dbarDir_eq_zero_of_notMem hzg, wsysG]
  -- integrability
  have hgc : Continuous g := hg.1.continuous
  have hconj_g : Continuous fun z => conj (g z) := Complex.continuous_conj.comp hgc
  have hgcs : HasCompactSupport g := hg.2.1
  have hcomp : ∀ c : ComplexModel n → ℂ, (∀ z, z ∉ tsupport g → c z = 0) →
      HasCompactSupport c ∧ tsupport c ⊆ D₀ := fun c hc => by
    have hsub : tsupport c ⊆ tsupport g :=
      closure_minimal (fun z hz => by by_contra h; exact hz (hc z h)) (isClosed_tsupport g)
    exact ⟨hgcs.mono' (subset_closure.trans hsub), hsub.trans hgd⟩
  have hdp : ∀ i, ContinuousOn (dDir (coordVec i) (fun y => (p y : ℂ))) D₀ := fun i =>
    (contDiffOn_dDir hO (contDiffOn_ofReal' hpD) _).continuousOn
  have hA : ∀ i, Integrable (fun z => wsysG ζ W i z * conj (dbarDir (coordVec i) g z +
      conj (dDir (coordVec i) (fun y => (p y : ℂ)) z) * g z)) := by
    intro i
    set c : ComplexModel n → ℂ := fun z => (ζ z : ℂ) * conj (dbarDir (coordVec i) g z +
      conj (dDir (coordVec i) (fun y => (p y : ℂ)) z) * g z)
    have hc : Continuous c := by
      have h1 : Continuous fun z => conj (dDir (coordVec i) (fun y => (p y : ℂ)) z) * g z :=
        continuous_mul_of_continuousOn hO (Complex.continuous_conj.comp_continuousOn (hdp i)) hgc
          hgd
      exact (Complex.continuous_ofReal.comp hζ.continuous).mul (Complex.continuous_conj.comp
        ((continuous_dbarDir' (hg.1.of_le (by simp))).add h1))
    obtain ⟨hcs, hcd⟩ := hcomp c fun z hz => by
      simp [c, image_eq_zero_of_notMem_tsupport hz, dbarDir_eq_zero_of_notMem hz]
    refine (integrable_W_mul hW hc hcs hcd i).congr (Eventually.of_forall fun z => ?_)
    simp only [wsysG, c]; ring
  have hB : ∀ i, Integrable (fun z => W z i *
      (dDir (coordVec i) (fun y => (ζ y : ℂ)) z * conj (g z))) := by
    intro i
    have hc : Continuous fun z => dDir (coordVec i) (fun y => (ζ y : ℂ)) z * conj (g z) :=
      (contDiff_dDir (k := 0) (hζc.of_le (by norm_num))).continuous.mul hconj_g
    obtain ⟨hcs, hcd⟩ := hcomp (fun z => dDir (coordVec i) (fun y => (ζ y : ℂ)) z * conj (g z))
      fun z hz => by simp [image_eq_zero_of_notMem_tsupport hz]
    exact integrable_W_mul hW hc hcs hcd i
  have hC : Integrable (fun z => (ζ z : ℂ) * conj (g z) * Θ z) := by
    have h1 : Continuous fun z => (ζ z : ℂ) * conj (g z) :=
      (Complex.continuous_ofReal.comp hζ.continuous).mul hconj_g
    obtain ⟨hcs, hcd⟩ := hcomp (fun z => (ζ z : ℂ) * conj (g z))
      fun z hz => by simp [image_eq_zero_of_notMem_tsupport hz]
    have h2 : Continuous fun z => (ζ z : ℂ) * conj (g z) * Θ z := by
      have := continuous_mul_of_continuousOn hO hΘ h1 hcd
      exact this.congr fun z => mul_comm _ _
    exact h2.integrable_of_hasCompactSupport hcs.mul_right
  have hrhs : ∀ z, conj (u z * conj (Θ z) * cweight p z) =
      (ζ z : ℂ) * conj (g z) * Θ z := by
    intro z
    simp only [hu_def, map_mul, Complex.conj_conj, hcwc, hEc, Complex.conj_ofReal]
    linear_combination ((ζ z : ℂ) * conj (g z) * Θ z) * hcw z
  simp only [hpt, hrhs] at hWc
  have hsum := integral_finsetSum Finset.univ fun i _ => (hA i).add (hB i)
  simp only [Pi.add_apply] at hsum
  rw [hsum] at hWc
  simp only [integral_add (hA _) (hB _), Finset.sum_add_distrib] at hWc
  rw [← integral_finsetSum _ fun i _ => hB i] at hWc
  have hf0 : ∀ z, f0G ζ W Θ z * conj (g z) = (ζ z : ℂ) * conj (g z) * Θ z -
      ∑ i, W z i * (dDir (coordVec i) (fun y => (ζ y : ℂ)) z * conj (g z)) := by
    intro z
    simp only [f0G, sub_mul, Finset.sum_mul]
    congr 1
    · ring
    · exact Finset.sum_congr rfl fun i _ => by ring
  simp only [hf0]
  rw [integral_sub hC (integrable_finsetSum _ fun i _ => hB i), ← hWc]
  ring

/-- **The `∂̄σ^♭`-rows of the weak equation**, from `∂̄(S^♭ W) = 0` weakly. -/
theorem row_SG (hD₀ : IsOpen D₀) (hS : ∀ l k, ContDiffOn ℝ ∞ (fun z => S z l k) D₀)
    (hW : IsLocL2 D₀ W)
    (hW1 : ∀ ψ : ComplexModel n → ℂ, IsTestFunctionOn D₀ ψ →
      ∀ j k : Fin n, ∫ z, D₀.indicator (fun z =>
        conj (dDir (coordVec k) ψ z) * lowS S W z j -
        conj (dDir (coordVec j) ψ z) * lowS S W z k) z = 0)
    {ζ : ComplexModel n → ℝ} (hζ : ContDiff ℝ ∞ ζ) {D : Set (ComplexModel n)}
    (hDd : D ⊆ D₀) {g : ComplexModel n → ℂ} (hg : IsTestFunctionOn D g) (j k : Fin n) :
    ∑ i, ∫ z, wsysG ζ W i z * conj (-conj (S z i k) *
      dDir (coordVec j) g z + conj (S z i j) * dDir (coordVec k) g z) =
      ∫ z, fSG S ζ W j k z * conj (g z) := by
  have hO := hD₀
  have hgd : tsupport g ⊆ D₀ := hg.2.2.trans hDd
  have hζc : ContDiff ℝ ∞ (fun y => (ζ y : ℂ)) := Complex.ofRealCLM.contDiff.comp hζ
  set ψ : ComplexModel n → ℂ := fun y => (ζ y : ℂ) * g y with hψ_def
  have hψs : tsupport ψ ⊆ tsupport g := tsupport_mul_subset_right
  have hψ : IsTestFunctionOn D₀ ψ :=
    ⟨hζc.mul hg.1, hg.2.1.mono' (subset_closure.trans hψs), hψs.trans hgd⟩
  have hWe := hW1 ψ hψ j k
  have hgc : Continuous g := hg.1.continuous
  have hgcs : HasCompactSupport g := hg.2.1
  have hcomp : ∀ c : ComplexModel n → ℂ, (∀ z, z ∉ tsupport g → c z = 0) →
      HasCompactSupport c ∧ tsupport c ⊆ D₀ := fun c hc => by
    have hsub : tsupport c ⊆ tsupport g :=
      closure_minimal (fun z hz => by by_contra h; exact hz (hc z h)) (isClosed_tsupport g)
    exact ⟨hgcs.mono' (subset_closure.trans hsub), hsub.trans hgd⟩
  have hσc : ∀ a b, ContinuousOn (fun z => S z a b) D₀ := fun a b => (hS a b).continuousOn
  have hdg : ∀ a, Continuous (dDir (coordVec a) g) := fun a =>
    (contDiff_dDir (k := 0) (hg.1.of_le (by norm_num))).continuous
  -- the pointwise identity
  have hpt : ∀ z, D₀.indicator (fun z =>
      conj (dDir (coordVec k) ψ z) * lowS S W z j -
      conj (dDir (coordVec j) ψ z) * lowS S W z k) z =
      ∑ i, wsysG ζ W i z * conj (-conj (S z i k) *
        dDir (coordVec j) g z + conj (S z i j) * dDir (coordVec k) g z) -
      fSG S ζ W j k z * conj (g z) := by
    intro z
    by_cases hz : z ∈ D₀
    · rw [indicator_of_mem hz]
      have hζz : DifferentiableAt ℝ ζ z := hζ.differentiable (by simp) z
      have hζz' : DifferentiableAt ℝ (fun y => (ζ y : ℂ)) z := hζc.differentiable (by simp) z
      have hgz : DifferentiableAt ℝ g z := hg.1.differentiable (by simp) z
      have hdψ : ∀ a, dDir (coordVec a) ψ z =
          dDir (coordVec a) (fun y => (ζ y : ℂ)) z * g z + (ζ z : ℂ) * dDir (coordVec a) g z :=
        fun a => by rw [hψ_def, dDir_mul hζz' hgz]
      simp only [hdψ, map_add, map_mul, Complex.conj_ofReal, dDir_ofReal_eq_conj hζz,
        Complex.conj_conj, fSG, lowS, wsysG, Finset.mul_sum, Finset.sum_mul,
        ← Finset.sum_sub_distrib, map_neg, neg_mul]
      exact Finset.sum_congr rfl fun i _ => by ring
    · have hzg : z ∉ tsupport g := fun h => hz (hgd h)
      rw [indicator_of_notMem hz]
      simp [image_eq_zero_of_notMem_tsupport hzg, dDir_eq_zero_of_notMem hzg]
  -- integrability
  have hA : ∀ i, Integrable (fun z => wsysG ζ W i z * conj (-conj (S z i k) *
      dDir (coordVec j) g z + conj (S z i j) * dDir (coordVec k) g z)) := by
    intro i
    set c : ComplexModel n → ℂ := fun z => (ζ z : ℂ) * conj (-conj (S z i k) *
      dDir (coordVec j) g z + conj (S z i j) * dDir (coordVec k) g z)
    have hc : Continuous c := by
      have h1 : ∀ a b, Continuous fun z => conj (S z i a) * dDir (coordVec b) g z :=
        fun a b => continuous_mul_of_continuousOn hO
          (Complex.continuous_conj.comp_continuousOn (hσc i a)) (hdg b)
          ((tsupport_dDir_subset' _ _).trans hgd)
      have h2 : Continuous fun z => -conj (S z i k) *
          dDir (coordVec j) g z + conj (S z i j) * dDir (coordVec k) g z := by
        have := ((h1 k j).neg).add (h1 j k)
        refine this.congr fun z => ?_
        simp only [Pi.add_apply, Pi.neg_apply]; ring
      exact (Complex.continuous_ofReal.comp hζ.continuous).mul (Complex.continuous_conj.comp h2)
    obtain ⟨hcs, hcd⟩ := hcomp c fun z hz => by
      simp [c, dDir_eq_zero_of_notMem hz]
    refine (integrable_W_mul hW hc hcs hcd i).congr (Eventually.of_forall fun z => ?_)
    simp only [wsysG, c]; ring
  have hF : Integrable (fun z => fSG S ζ W j k z * conj (g z)) := by
    have h1 : ∀ i (a b : Fin n), Integrable (fun z => W z i *
        (dbarDir (coordVec a) (fun y => (ζ y : ℂ)) z * S z i b * conj (g z))) := by
      intro i a b
      have hc : Continuous fun z => dbarDir (coordVec a) (fun y => (ζ y : ℂ)) z *
          S z i b * conj (g z) := by
        have h2 : Continuous fun z => S z i b * conj (g z) :=
          continuous_mul_of_continuousOn hO (hσc i b) (Complex.continuous_conj.comp hgc)
            ((tsupport_comp_subset (map_zero _) _).trans hgd)
        refine ((continuous_dbarDir' (hζc.of_le (by simp)) (v := coordVec a)).mul h2).congr
          fun z => ?_
        simp only [Pi.mul_apply]; ring
      obtain ⟨hcs, hcd⟩ := hcomp (fun z => dbarDir (coordVec a) (fun y => (ζ y : ℂ)) z *
          S z i b * conj (g z)) fun z hz => by
        simp [image_eq_zero_of_notMem_tsupport hz]
      exact integrable_W_mul hW hc hcs hcd i
    have h3 : (fun z => fSG S ζ W j k z * conj (g z)) = fun z => ∑ i, (W z i *
        (dbarDir (coordVec j) (fun y => (ζ y : ℂ)) z * S z i k * conj (g z)) -
        W z i * (dbarDir (coordVec k) (fun y => (ζ y : ℂ)) z *
          S z i j * conj (g z))) := by
      funext z
      simp only [fSG, lowS, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [h3]
    exact integrable_finsetSum _ fun i _ => (h1 i j k).sub (h1 i k j)
  simp only [hpt] at hWe
  rw [integral_sub (integrable_finsetSum _ fun i _ => hA i) hF,
    integral_finsetSum _ fun i _ => hA i] at hWe
  exact sub_eq_zero.mp hWe

theorem integrable_wsysG_mul (hW : IsLocL2 D₀ W) {ζ : ComplexModel n → ℝ}
    (hζ : Continuous ζ) {c : ComplexModel n → ℂ} (hc : Continuous c) (hcs : HasCompactSupport c)
    (hcd : tsupport c ⊆ D₀) (i : Fin n) :
    Integrable (fun z => wsysG ζ W i z * c z) := by
  have hc' : Continuous fun z => (ζ z : ℂ) * c z := (Complex.continuous_ofReal.comp hζ).mul hc
  have hsub : tsupport (fun z => (ζ z : ℂ) * c z) ⊆ tsupport c := tsupport_mul_subset_right
  refine (integrable_W_mul hW hc' (hcs.mono' (subset_closure.trans hsub)) (hsub.trans hcd)
    i).congr (Eventually.of_forall fun z => ?_)
  simp only [wsysG]; ring

/-- **The weak equation `P(ζ W) = f`** (`claude-tl2-man2:local`). -/
theorem weak_eqG (hD₀ : IsOpen D₀) (hp : ContDiffOn ℝ ∞ p D₀)
    (hS : ∀ l k, ContDiffOn ℝ ∞ (fun z => S z l k) D₀) (hW : IsLocL2 D₀ W)
    (hΘ : ContinuousOn Θ D₀)
    (hW1 : ∀ ψ : ComplexModel n → ℂ, IsTestFunctionOn D₀ ψ →
      ∀ j k : Fin n, ∫ z, D₀.indicator (fun z =>
        conj (dDir (coordVec k) ψ z) * lowS S W z j -
        conj (dDir (coordVec j) ψ z) * lowS S W z k) z = 0)
    (hW2 : ∀ u : ComplexModel n → ℂ, IsTestFunctionOn D₀ u →
      ∫ z, D₀.indicator (fun z => cweight p z *
        ∑ l, dbarDir (coordVec l) u z * conj (W z l)) z =
      ∫ z, u z * conj (Θ z) * cweight p z)
    {ζ : ComplexModel n → ℝ} (hζ : ContDiff ℝ ∞ ζ) {D : Set (ComplexModel n)}
    (hDd : D ⊆ D₀) (h : Fin (n * n + 1) → ComplexModel n → ℂ)
    (hh : ∀ i', IsTestFunctionOn D (h i')) :
    ∑ i', ∫ z, fsysG S ζ W Θ i' z * conj (h i' z) =
      ∑ i, ∫ z, wsysG ζ W i z * conj (firstOrderAdjointApply (sysA (n := n))
        (sysA'G S) (sysBG S p) h i z) := by
  have hO := hD₀
  have hσD : ∀ z ∈ D, ∀ l k, DifferentiableAt ℝ (fun y => S y l k) z :=
    fun z hz l k => ((hS l k).contDiffAt (hO.mem_nhds (hDd hz))).differentiableAt (by simp)
  simp only [adj_eqG S p hσD h hh]
  have hpD : ContDiffOn ℝ ∞ p D₀ := hp
  -- continuity of the adjoint pieces
  have hX : ∀ i, Continuous fun z => conj (dbarDir (coordVec i) (h (Fin.last _)) z +
      conj (dDir (coordVec i) (fun y => (p y : ℂ)) z) * h (Fin.last _) z) := by
    intro i
    have hg := hh (Fin.last _)
    have h1 : Continuous fun z => conj (dDir (coordVec i) (fun y => (p y : ℂ)) z) *
        h (Fin.last _) z :=
      continuous_mul_of_continuousOn hO (Complex.continuous_conj.comp_continuousOn
        (contDiffOn_dDir hO (contDiffOn_ofReal' hpD) _).continuousOn) hg.1.continuous
        (hg.2.2.trans hDd)
    exact Complex.continuous_conj.comp ((continuous_dbarDir' (hg.1.of_le (by simp))).add h1)
  have hY : ∀ (q : Fin (n * n)) (i : Fin n), Continuous fun z => conj (-conj (S z
      i (rowJK q).2) * dDir (coordVec (rowJK q).1) (h q.castSucc) z + conj (S z i
        (rowJK q).1) * dDir (coordVec (rowJK q).2) (h q.castSucc) z) := by
    intro q i
    have hg := hh q.castSucc
    have h1 : ∀ a b, Continuous fun z => conj (S z i a) *
        dDir (coordVec b) (h q.castSucc) z := fun a b =>
      continuous_mul_of_continuousOn hO (Complex.continuous_conj.comp_continuousOn
        (hS i a).continuousOn)
        (contDiff_dDir (k := 0) (hg.1.of_le (by norm_num))).continuous
        ((tsupport_dDir_subset' _ _).trans (hg.2.2.trans hDd))
    have h2 : Continuous fun z => -conj (S z i (rowJK q).2) *
        dDir (coordVec (rowJK q).1) (h q.castSucc) z + conj (S z i
          (rowJK q).1) * dDir (coordVec (rowJK q).2) (h q.castSucc) z := by
      refine (((h1 (rowJK q).2 (rowJK q).1).neg).add (h1 (rowJK q).1 (rowJK q).2)).congr
        fun z => ?_
      simp only [Pi.add_apply, Pi.neg_apply]; ring
    exact Complex.continuous_conj.comp h2
  have hsupp : ∀ (c : ComplexModel n → ℂ) (g : ComplexModel n → ℂ), IsTestFunctionOn D g →
      (∀ z, z ∉ tsupport g → c z = 0) → HasCompactSupport c ∧ tsupport c ⊆ D₀ :=
    fun c g hg hc => by
      have hsub : tsupport c ⊆ tsupport g :=
        closure_minimal (fun z hz => by by_contra hn; exact hz (hc z hn)) (isClosed_tsupport g)
      exact ⟨hg.2.1.mono' (subset_closure.trans hsub), hsub.trans (hg.2.2.trans hDd)⟩
  have hIX : ∀ i, Integrable fun z => wsysG ζ W i z * conj (dbarDir (coordVec i)
      (h (Fin.last _)) z + conj (dDir (coordVec i) (fun y => (p y : ℂ)) z) *
        h (Fin.last _) z) := by
    intro i
    obtain ⟨hcs, hcd⟩ := hsupp (fun z => conj (dbarDir (coordVec i) (h (Fin.last _)) z +
      conj (dDir (coordVec i) (fun y => (p y : ℂ)) z) * h (Fin.last _) z))
      (h (Fin.last _)) (hh (Fin.last _)) fun z hz => by
        simp [image_eq_zero_of_notMem_tsupport hz, dbarDir_eq_zero_of_notMem hz]
    exact integrable_wsysG_mul hW hζ.continuous (hX i) hcs hcd i
  have hIY : ∀ q i, Integrable fun z => wsysG ζ W i z * conj (-conj (S z
      i (rowJK q).2) * dDir (coordVec (rowJK q).1) (h q.castSucc) z + conj (S z i
        (rowJK q).1) * dDir (coordVec (rowJK q).2) (h q.castSucc) z) := by
    intro q i
    obtain ⟨hcs, hcd⟩ := hsupp (fun z => conj (-conj (S z
      i (rowJK q).2) * dDir (coordVec (rowJK q).1) (h q.castSucc) z + conj (S z i
        (rowJK q).1) * dDir (coordVec (rowJK q).2) (h q.castSucc) z)) (h q.castSucc)
      (hh q.castSucc) fun z hz => by simp [dDir_eq_zero_of_notMem hz]
    exact integrable_wsysG_mul hW hζ.continuous (hY q i) hcs hcd i
  have hsplit : ∀ i, ∫ z, wsysG ζ W i z * conj ((dbarDir (coordVec i) (h (Fin.last _)) z +
      conj (dDir (coordVec i) (fun y => (p y : ℂ)) z) * h (Fin.last _) z) +
      ∑ q : Fin (n * n), (-conj (S z i (rowJK q).2) *
          dDir (coordVec (rowJK q).1) (h q.castSucc) z + conj (S z i
            (rowJK q).1) * dDir (coordVec (rowJK q).2) (h q.castSucc) z)) =
      (∫ z, wsysG ζ W i z * conj (dbarDir (coordVec i) (h (Fin.last _)) z +
        conj (dDir (coordVec i) (fun y => (p y : ℂ)) z) * h (Fin.last _) z)) +
      ∑ q : Fin (n * n), ∫ z, wsysG ζ W i z * conj (-conj (S z i
        (rowJK q).2) * dDir (coordVec (rowJK q).1) (h q.castSucc) z + conj (S z
          i (rowJK q).1) * dDir (coordVec (rowJK q).2) (h q.castSucc) z) := by
    intro i
    have := integral_add (hIX i) (integrable_finsetSum Finset.univ fun q _ => hIY q i)
    rw [integral_finsetSum _ fun q _ => hIY q i] at this
    refine (integral_congr_ae (Eventually.of_forall fun z => ?_)).trans this
    simp only [map_add, map_sum, mul_add, Finset.mul_sum]
  rw [Finset.sum_congr rfl fun i _ => hsplit i]
  simp only [Finset.sum_add_distrib]
  rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin n))), Fin.sum_univ_castSucc, add_comm]
  congr 1
  · simp only [fsysG, Fin.lastCases_last]
    exact (row_lastG hD₀ hp hW hΘ hW2 hζ hDd (hh _)).symm
  · refine Finset.sum_congr rfl fun q _ => ?_
    simp only [fsysG, Fin.lastCases_castSucc]
    exact (row_SG hD₀ hS hW hW1 hζ hDd (hh _) _ _).symm

/-- **Friedrichs approximation of a localized weak solution** (`claude-tl2-man2:local`): smooth
fields `h_m`, supported in `D`, with `h_m → ζ W`, `ϑ_p h_m → f_ϑ` and `∂̄(S^♭h_m) → f_S` in `L²`. -/
theorem exists_approxG (hD₀ : IsOpen D₀) (hp : ContDiffOn ℝ ∞ p D₀)
    (hS : ∀ l k, ContDiffOn ℝ ∞ (fun z => S z l k) D₀) (hW : IsLocL2 D₀ W)
    (hΘ : ContinuousOn Θ D₀)
    (hW1 : ∀ ψ : ComplexModel n → ℂ, IsTestFunctionOn D₀ ψ →
      ∀ j k : Fin n, ∫ z, D₀.indicator (fun z =>
        conj (dDir (coordVec k) ψ z) * lowS S W z j -
        conj (dDir (coordVec j) ψ z) * lowS S W z k) z = 0)
    (hW2 : ∀ u : ComplexModel n → ℂ, IsTestFunctionOn D₀ u →
      ∫ z, D₀.indicator (fun z => cweight p z *
        ∑ l, dbarDir (coordVec l) u z * conj (W z l)) z =
      ∫ z, u z * conj (Θ z) * cweight p z)
    {ζ : ComplexModel n → ℝ} (hζ : ContDiff ℝ ∞ ζ) (hζc : HasCompactSupport ζ)
    {D : Set (ComplexModel n)} (hD : IsOpen D) (hζD : tsupport ζ ⊆ D) (hDd : D ⊆ D₀) :
    ∃ hs : ℕ → ComplexModel n → ComplexModel n,
      (∀ m, ContDiff ℝ ∞ (hs m) ∧ HasCompactSupport (hs m)) ∧ (∀ m, tsupport (hs m) ⊆ D) ∧
      Tendsto (fun m => eLpNorm (fun z => hs m z - ofComps (wsysG ζ W) z) 2 volume)
        atTop (𝓝 0) ∧
      Tendsto (fun m => eLpNorm (fun z => chartTheta p (hs m) z - f0G ζ W Θ z) 2
        (volume.restrict D)) atTop (𝓝 0) ∧
      (∀ j k : Fin n, Tendsto (fun m => eLpNorm (fun z => sigmaDbarG S (hs m) z j k -
        fSG S ζ W j k z) 2 (volume.restrict D)) atTop (𝓝 0)) ∧
      MemLp (f0G ζ W Θ) 2 volume ∧ ∀ j k : Fin n, MemLp (fSG S ζ W j k) 2 volume := by
  have hO := hD₀
  have hζd : tsupport ζ ⊆ D₀ := hζD.trans hDd
  have hσ : ∀ l k, ContDiffOn ℝ ∞ (fun z => S z l k) D := fun l k => (hS l k).mono hDd
  have hp' : ContDiffOn ℝ ∞ p D := hp.mono hDd
  have hA : ∀ j i' i, ContDiffOn ℝ ∞ (fun z => sysA (n := n) j z i' i) D := by
    intro j i' i; simp only [sysA, of_apply]; exact contDiffOn_const
  have hA' : ∀ j i' i, ContDiffOn ℝ ∞ (fun z => sysA'G S j z i' i) D := by
    intro j i' i
    induction i' using Fin.lastCases with
    | last => simp only [sysA'G, of_apply, Fin.lastCases_last]; exact contDiffOn_const
    | cast q =>
      simp only [sysA'G, of_apply, Fin.lastCases_castSucc]
      refine ContDiffOn.sub ?_ ?_
      · split_ifs
        · exact hσ _ _
        · exact contDiffOn_const
      · split_ifs
        · exact hσ _ _
        · exact contDiffOn_const
  have hB : ∀ i' i, ContDiffOn ℝ ∞ (fun z => sysBG S p z i' i) D := by
    intro i' i
    induction i' using Fin.lastCases with
    | last =>
      simp only [sysBG, of_apply, Fin.lastCases_last]
      exact contDiffOn_dDir hD (contDiffOn_ofReal' hp') _
    | cast q =>
      simp only [sysBG, of_apply, Fin.lastCases_castSucc]
      exact (contDiffOn_dbarDir hD (hσ _ _) _).sub (contDiffOn_dbarDir hD (hσ _ _) _)
  -- the data of the weak equation
  have hζC : Continuous fun z => (ζ z : ℂ) := Complex.continuous_ofReal.comp hζ.continuous
  have hζcs : HasCompactSupport fun z => (ζ z : ℂ) := hζc.comp_left Complex.ofReal_zero
  have hζts : tsupport (fun z => (ζ z : ℂ)) ⊆ D₀ :=
    (tsupport_comp_subset Complex.ofReal_zero ζ).trans hζd
  have hζc' : ContDiff ℝ ∞ (fun y => (ζ y : ℂ)) := Complex.ofRealCLM.contDiff.comp hζ
  have hwL : ∀ i, MemLp (wsysG ζ W i) 2 volume := by
    intro i
    have h1 : wsysG ζ W i = fun z => W z i * (ζ z : ℂ) := by
      funext z; simp only [wsysG]; ring
    rw [h1]
    exact memLp_W_mul hW hζC hζcs hζts i
  have hw0 : ∀ i, ∀ z ∉ tsupport ζ, wsysG ζ W i z = 0 := fun i z hz => by
    simp [wsysG, image_eq_zero_of_notMem_tsupport hz]
  have hdζ : ∀ l, Continuous (dDir (coordVec l) fun y => (ζ y : ℂ)) := fun l =>
    (contDiff_dDir (k := 0) (hζc'.of_le (by norm_num))).continuous
  have hdζs : ∀ l, HasCompactSupport (dDir (coordVec l) fun y => (ζ y : ℂ)) ∧
      tsupport (dDir (coordVec l) fun y => (ζ y : ℂ)) ⊆ D₀ := fun l =>
    ⟨hζcs.mono' (subset_closure.trans (tsupport_dDir_subset' _ _)),
      (tsupport_dDir_subset' _ _).trans hζts⟩
  have hdbζ : ∀ l, Continuous (dbarDir (coordVec l) fun y => (ζ y : ℂ)) := fun l =>
    continuous_dbarDir' (hζc'.of_le (by simp))
  have hcS : ∀ (a i b : Fin n), Continuous fun z => dbarDir (coordVec a) (fun y => (ζ y : ℂ)) z *
      S z i b := fun a i b => by
    have := continuous_mul_of_continuousOn hO (hS i b).continuousOn (hdbζ a)
      ((tsupport_dbarDir_subset _ _).trans hζts)
    exact this.congr fun z => mul_comm _ _
  have hcSs : ∀ (a i b : Fin n), HasCompactSupport (fun z => dbarDir (coordVec a)
      (fun y => (ζ y : ℂ)) z * S z i b) ∧ tsupport (fun z => dbarDir (coordVec a)
        (fun y => (ζ y : ℂ)) z * S z i b) ⊆ D₀ := fun a i b =>
    ⟨(hasCompactSupport_dbarDir hζcs).mul_right,
      (tsupport_mul_subset_left.trans (tsupport_dbarDir_subset _ _)).trans hζts⟩
  have hfL : ∀ i', MemLp (fsysG S ζ W Θ i') 2 volume := by
    intro i'
    induction i' using Fin.lastCases with
    | last =>
      simp only [fsysG, Fin.lastCases_last]
      refine MemLp.sub ?_ (memLp_finsetSum _ fun l _ => ?_)
      · have hc := continuous_mul_of_continuousOn hO hΘ hζC hζts
        have h1 : (fun z => (ζ z : ℂ) * Θ z) = fun z => Θ z * (ζ z : ℂ) :=
          funext fun z => mul_comm _ _
        rw [h1]
        exact hc.memLp_of_hasCompactSupport hζcs.mul_left
      · have h1 : (fun z => dDir (coordVec l) (fun y => (ζ y : ℂ)) z * W z l) =
            fun z => W z l * dDir (coordVec l) (fun y => (ζ y : ℂ)) z := by
          funext z; ring
        rw [h1]
        exact memLp_W_mul hW (hdζ l) (hdζs l).1 (hdζs l).2 l
    | cast q =>
      simp only [fsysG, Fin.lastCases_castSucc]
      have h3 : fSG S ζ W (rowJK q).1 (rowJK q).2 = fun z => ∑ i, (W z i *
          (dbarDir (coordVec (rowJK q).1) (fun y => (ζ y : ℂ)) z * S z i
            (rowJK q).2) - W z i * (dbarDir (coordVec (rowJK q).2) (fun y => (ζ y : ℂ)) z *
              S z i (rowJK q).1)) := by
        funext z
        simp only [fSG, lowS, Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
      rw [h3]
      exact memLp_finsetSum _ fun i _ =>
        (memLp_W_mul hW (hcS (rowJK q).1 i (rowJK q).2) (hcSs (rowJK q).1 i (rowJK q).2).1
          (hcSs (rowJK q).1 i (rowJK q).2).2 i).sub
          (memLp_W_mul hW (hcS (rowJK q).2 i (rowJK q).1) (hcSs (rowJK q).2 i (rowJK q).1).1
            (hcSs (rowJK q).2 i (rowJK q).1).2 i)
  have hweak : ∀ h : Fin (n * n + 1) → ComplexModel n → ℂ, (∀ i', IsTestFunctionOn D (h i')) →
      ∑ i', ∫ z, fsysG S ζ W Θ i' z * conj (h i' z) =
        ∑ i, ∫ z, wsysG ζ W i z * conj (firstOrderAdjointApply (sysA (n := n))
          (sysA'G S) (sysBG S p) h i z) :=
    fun h hh => weak_eqG hD₀ hp hS hW hΘ hW1 hW2 hζ hDd h hh
  obtain ⟨ws, hws, hc1, hc2⟩ := friedrichsStatement n n (n * n + 1) D hD (sysA (n := n))
    (sysA'G S) (sysBG S p) hA hA' hB (tsupport ζ) hζc hζD
    (wsysG ζ W) (fsysG S ζ W Θ) hwL hw0 hfL hweak
  have hsub : ∀ m, tsupport (ofComps (ws m)) ⊆ ⋃ i, tsupport (ws m i) := fun m =>
    closure_minimal (fun z hz => by
      by_contra h
      simp only [mem_iUnion, not_exists] at h
      apply hz
      ext i
      simp [ofComps, image_eq_zero_of_notMem_tsupport (h i)])
      (isClosed_iUnion_of_finite fun i => isClosed_tsupport _)
  have hsD : ∀ m, tsupport (ofComps (ws m)) ⊆ D := fun m =>
    (hsub m).trans (iUnion_subset fun i => (hws m i).2.2)
  refine ⟨fun m => ofComps (ws m), fun m => ⟨?_, ?_⟩, hsD, ?_, ?_, ?_,
    by simpa [fsysG] using hfL (Fin.last _), fun j k => ?_⟩
  rotate_right
  · have hq : rowJK (finProdFinEquiv (j, k)) = (j, k) := by simp [rowJK]
    have := hfL (Fin.castSucc (finProdFinEquiv (j, k)))
    simp only [fsysG, Fin.lastCases_castSucc, hq] at this
    exact this
  · have h1 : ContDiff ℝ ∞ (fun z => fun i => ws m i z) := contDiff_pi.mpr fun i => (hws m i).1
    exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℂ)).symm.contDiff.comp h1
  · exact IsCompact.of_isClosed_subset (isCompact_iUnion fun i => (hws m i).2.1)
      (isClosed_tsupport _) (hsub m)
  · refine tendsto_eLpNorm_sum Finset.univ (G := fun i m z => ws m i z - wsysG ζ W i z)
      (fun i m => (hws m i).1.continuous.aestronglyMeasurable.sub (hwL i).1)
      (fun m z => ?_) fun i _ => hc1 i
    refine (norm_le_sum_norm_coord _).trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
    simp [ofComps]
  · refine (hc2 (Fin.last _)).congr fun m => ?_
    congr 1
    funext z
    rw [firstOrderApply_lastG]
    simp [fsysG]
  · intro j k
    set q : Fin (n * n) := finProdFinEquiv (j, k)
    have hq : rowJK q = (j, k) := by simp [rowJK, q]
    refine (hc2 q.castSucc).congr fun m => ?_
    refine eLpNorm_congr_ae ((ae_restrict_iff' hD.measurableSet).mpr
      (Eventually.of_forall fun z hz => ?_))
    simp only [fsysG, Fin.lastCases_castSucc]
    rw [firstOrderApply_SG S p (ws m)
      (fun l k => ((hσ l k).contDiffAt (hD.mem_nhds hz)).differentiableAt (by simp))
      (fun i => (hws m i).1.differentiable (by simp) z) q, hq]

end Weak

end SGPT.Trace.TwistedL2
