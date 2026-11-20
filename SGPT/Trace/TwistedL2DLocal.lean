import SGPT.Trace.TwistedL2DCutoff
import SGPT.Trace.TwistedL2Friedrichs

/-!
# Friedrichs' lemma for the system `W ↦ (ϑ_p W, ∂̄(σ^♭ W))` in a frame

Blueprint `claude-tl2-dens.tex` (`claude-tl2-dens:local`).  In a frame `e` of `L` (local weight
`p = p_e`), the first order system

`P W = (ϑ_p W, (∂̄(σ^♭W))_{jk})`,     rows `Fin (n·n + 1)` (`last` is the `ϑ`-row),

has coefficients smooth on the frame domain (`sysA`, `sysA'`, `sysB`).  `firstOrderApply_last`
and `firstOrderApply_S` identify `P` with `chartTheta` and `sigmaDbar`; `adj_eq` computes the
formal adjoint `P†`.  For the projected field `v` (`exists_v`) localized by a real test function
`ζ` in the frame domain, `w = ζ W_e(v)` satisfies `P w = f` weakly, with
`f_ϑ = ζ ϑ_p τ - ∑_l ∂_l ζ W_l` and `f_{jk} = ∂_{j̄}ζ (σ^♭W)_k - ∂_{k̄}ζ (σ^♭W)_j`
(`weak_eq`); Friedrichs' lemma (`friedrichsStatement`) gives smooth approximations
(`exists_approx`).
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

/-! ### The system -/

/-- Decoding of the `∂̄σ^♭`-rows. -/
def rowJK (q : Fin (n * n)) : Fin n × Fin n := finProdFinEquiv.symm q

section System

variable (omega : SGPT.Foundations.Analysis.FirstPass.PositiveClasses.KahlerBackground n
  (ComplexModel n)) (r : ComplexModel n → ℝ) (p : ComplexModel n → ℝ)

/-- The `∂`-coefficients: `-1` on the diagonal of the `ϑ`-row. -/
def sysA (m : Fin n) (_z : ComplexModel n) : Matrix (Fin (n * n + 1)) (Fin n) ℂ :=
  Matrix.of fun i' i => Fin.lastCases (if i = m then -1 else 0) (fun _ => 0) i'

/-- The `∂̄`-coefficients of the `∂̄σ^♭`-rows: `δ_{mj} σ_{ik} - δ_{mk} σ_{ij}`. -/
def sysA' (m : Fin n) (z : ComplexModel n) : Matrix (Fin (n * n + 1)) (Fin n) ℂ :=
  Matrix.of fun i' i => Fin.lastCases 0 (fun q =>
    (if m = (rowJK q).1 then sigmaMat omega r z i (rowJK q).2 else 0) -
    (if m = (rowJK q).2 then sigmaMat omega r z i (rowJK q).1 else 0)) i'

/-- The zero order coefficients: `∂_i p` in the `ϑ`-row, `∂_{j̄}σ_{ik} - ∂_{k̄}σ_{ij}` in the
`∂̄σ^♭`-rows. -/
def sysB (z : ComplexModel n) : Matrix (Fin (n * n + 1)) (Fin n) ℂ :=
  Matrix.of fun i' i => Fin.lastCases (dDir (coordVec i) (fun y => (p y : ℂ)) z) (fun q =>
    dbarDir (coordVec (rowJK q).1) (fun y => sigmaMat omega r y i (rowJK q).2) z -
    dbarDir (coordVec (rowJK q).2) (fun y => sigmaMat omega r y i (rowJK q).1) z) i'

end System

/-- The components of a vector field. -/
def comps (W : ComplexModel n → ComplexModel n) : Fin n → ComplexModel n → ℂ := fun i z => W z i

/-- The vector field of a family of components. -/
def ofComps (w : Fin n → ComplexModel n → ℂ) : ComplexModel n → ComplexModel n :=
  fun z => WithLp.toLp 2 fun i => w i z

theorem firstOrderApply_last (omega : SGPT.Foundations.Analysis.FirstPass.PositiveClasses.KahlerBackground n
    (ComplexModel n)) (r p : ComplexModel n → ℝ) (w : Fin n → ComplexModel n → ℂ)
    (z : ComplexModel n) :
    firstOrderApply (sysA (n := n)) (sysA' omega r) (sysB omega r p) w (Fin.last _) z =
      chartTheta p (ofComps w) z := by
  simp only [firstOrderApply, sysA, sysA', sysB, of_apply, Fin.lastCases_last, zero_mul,
    add_zero, chartTheta, deltaDir, ofComps]
  have h : ∀ x : Fin n, ∑ x_1 : Fin n, (if x_1 = x then (-1 : ℂ) else 0) *
      dDir (coordVec x) (w x_1) z = -dDir (coordVec x) (w x) z := by
    intro x; simp [ite_mul, Finset.sum_ite_eq']
  rw [Finset.sum_congr rfl fun x _ => h x, Finset.sum_sub_distrib, neg_sub]
  simp only [Finset.sum_neg_distrib]
  ring

theorem firstOrderApply_S (omega : SGPT.Foundations.Analysis.FirstPass.PositiveClasses.KahlerBackground n
    (ComplexModel n)) (r p : ComplexModel n → ℝ) (w : Fin n → ComplexModel n → ℂ)
    {z : ComplexModel n} (hσ : ∀ l k, DifferentiableAt ℝ (fun y => sigmaMat omega r y l k) z)
    (hw : ∀ i, DifferentiableAt ℝ (w i) z) (q : Fin (n * n)) :
    firstOrderApply (sysA (n := n)) (sysA' omega r) (sysB omega r p) w (Fin.castSucc q) z =
      sigmaDbar omega r (ofComps w) z (rowJK q).1 (rowJK q).2 := by
  set j := (rowJK q).1
  set k := (rowJK q).2
  have hD : ∀ a b : Fin n, dbarDir (coordVec a) (fun y => lowerSigma omega r (ofComps w) y b) z =
      ∑ l, (dbarDir (coordVec a) (fun y => sigmaMat omega r y l b) z * w l z +
        sigmaMat omega r z l b * dbarDir (coordVec a) (w l) z) := by
    intro a b
    have hfun : (fun y => lowerSigma omega r (ofComps w) y b) =
        fun y => ∑ l, sigmaMat omega r y l b * w l y := by
      funext y; simp [lowerSigma, ofComps]
    rw [hfun, dbarDir_finset_sum_fun Finset.univ fun l _ =>
      (show DifferentiableAt ℝ (fun y => sigmaMat omega r y l b * w l y) z from
        (hσ l b).mul (hw l))]
    exact Finset.sum_congr rfl fun l _ => dbarDir_mul (hσ l b) (hw l)
  simp only [sigmaDbar, of_apply, hD]
  simp only [firstOrderApply, sysA, sysA', sysB, of_apply, Fin.lastCases_castSucc, zero_mul,
    zero_add]
  have h1 : ∀ (a b : Fin n), ∑ m : Fin n, ∑ i : Fin n,
      (if m = a then sigmaMat omega r z i b else 0) * dbarDir (coordVec m) (w i) z =
      ∑ i, sigmaMat omega r z i b * dbarDir (coordVec a) (w i) z := by
    intro a b
    simp [ite_mul, Finset.sum_ite_eq']
  simp only [sub_mul, Finset.sum_sub_distrib, h1, Finset.sum_add_distrib]
  ring

/-! ### The formal adjoint -/

theorem dDir_ite_fun (P : Prop) [Decidable P] (F : ComplexModel n → ℂ) (v z : ComplexModel n) :
    dDir v (fun y => if P then F y else 0) z = if P then dDir v F z else 0 := by
  split_ifs <;> simp [dDir]

theorem dbarDir_ite_fun (P : Prop) [Decidable P] (F : ComplexModel n → ℂ) (v z : ComplexModel n) :
    dbarDir v (fun y => if P then F y else 0) z = if P then dbarDir v F z else 0 := by
  split_ifs <;> simp [dbarDir]

theorem tsupport_dDir_subset' (v : ComplexModel n) (h : ComplexModel n → ℂ) :
    tsupport (dDir v h) ⊆ tsupport h :=
  closure_minimal (fun z hz => by
    by_contra hn
    exact hz (dDir_eq_zero_of_notMem hn v)) (isClosed_tsupport h)

theorem dDir_conj_mul {c h : ComplexModel n → ℂ} {z : ComplexModel n} (hc : DifferentiableAt ℝ c z)
    (hh : DifferentiableAt ℝ h z) (v : ComplexModel n) :
    dDir v (fun y => conj (c y) * h y) z = conj (dbarDir v c z) * h z + conj (c z) * dDir v h z := by
  have hcc : DifferentiableAt ℝ (fun y => conj (c y)) z :=
    (Complex.conjCLE.toContinuousLinearMap.differentiableAt).comp z hc
  rw [dDir_mul hcc hh, dDir_conj hc]

/-- The formal adjoint as a sum over the rows. -/
theorem firstOrderAdjointApply_eq_sum {N N' : ℕ}
    (A A' : Fin n → ComplexModel n → Matrix (Fin N') (Fin N) ℂ)
    (B : ComplexModel n → Matrix (Fin N') (Fin N) ℂ) (h : Fin N' → ComplexModel n → ℂ) (i : Fin N)
    (z : ComplexModel n) :
    firstOrderAdjointApply A A' B h i z = ∑ i', ((∑ j, (-dbarDir (coordVec j)
      (fun y => conj (A j y i' i) * h i' y) z - dDir (coordVec j)
        (fun y => conj (A' j y i' i) * h i' y) z)) + conj (B z i' i) * h i' z) := by
  rw [firstOrderAdjointApply, Finset.sum_comm, ← Finset.sum_add_distrib]

section Adjoint

variable (omega : SGPT.Foundations.Analysis.FirstPass.PositiveClasses.KahlerBackground n
  (ComplexModel n)) (r p : ComplexModel n → ℝ)

theorem adj_row_last (g : ComplexModel n → ℂ) (hg : ContDiff ℝ ∞ g) (i : Fin n)
    (z : ComplexModel n) :
    (∑ j, (-dbarDir (coordVec j) (fun y => conj (sysA j y (Fin.last (n * n)) i) * g y) z -
      dDir (coordVec j) (fun y => conj (sysA' omega r j y (Fin.last (n * n)) i) * g y) z)) +
      conj (sysB omega r p z (Fin.last (n * n)) i) * g z =
    dbarDir (coordVec i) g z + conj (dDir (coordVec i) (fun y => (p y : ℂ)) z) * g z := by
  have hgd : DifferentiableAt ℝ g z := hg.differentiable (by simp) z
  simp only [sysA, sysA', sysB, of_apply, Fin.lastCases_last, map_zero, zero_mul]
  have h0 : ∀ j : Fin n, dDir (coordVec j) (fun _ : ComplexModel n => (0 : ℂ)) z = 0 := fun j => by
    simp [dDir]
  have h1 : ∀ j : Fin n, dbarDir (coordVec j)
      (fun y => conj (if i = j then (-1 : ℂ) else 0) * g y) z =
      (if i = j then -dbarDir (coordVec j) g z else 0) := fun j => by
    rw [dbarDir_const_mul_fun _ hgd]
    split_ifs <;> simp
  simp only [h0, h1, sub_zero]
  simp [Finset.sum_ite_eq]

theorem adj_row_S {g : ComplexModel n → ℂ} (hg : ContDiff ℝ ∞ g) {z : ComplexModel n}
    (hσ : ∀ l k, DifferentiableAt ℝ (fun y => sigmaMat omega r y l k) z) (q : Fin (n * n))
    (i : Fin n) :
    (∑ j, (-dbarDir (coordVec j) (fun y => conj (sysA j y (Fin.castSucc q) i) * g y) z -
      dDir (coordVec j) (fun y => conj (sysA' omega r j y (Fin.castSucc q) i) * g y) z)) +
      conj (sysB omega r p z (Fin.castSucc q) i) * g z =
    -conj (sigmaMat omega r z i (rowJK q).2) * dDir (coordVec (rowJK q).1) g z +
      conj (sigmaMat omega r z i (rowJK q).1) * dDir (coordVec (rowJK q).2) g z := by
  have hgd : DifferentiableAt ℝ g z := hg.differentiable (by simp) z
  simp only [sysA, sysA', sysB, of_apply, Fin.lastCases_castSucc, map_zero, zero_mul]
  set a := (rowJK q).1
  set b := (rowJK q).2
  have h0 : ∀ j : Fin n, dbarDir (coordVec j) (fun _ : ComplexModel n => (0 : ℂ)) z = 0 :=
    fun j => by simp [dbarDir]
  have hfun : ∀ j : Fin n, (fun y => conj ((if j = a then sigmaMat omega r y i b else 0) -
      (if j = b then sigmaMat omega r y i a else 0)) * g y) =
      fun y => (if j = a then conj (sigmaMat omega r y i b) * g y else 0) -
        (if j = b then conj (sigmaMat omega r y i a) * g y else 0) := fun j => by
    funext y; split_ifs <;> simp [sub_mul]
  have hd1 : ∀ (j c d : Fin n), DifferentiableAt ℝ
      (fun y => if j = c then conj (sigmaMat omega r y i d) * g y else 0) z := fun j c d => by
    split_ifs
    · exact ((Complex.conjCLE.toContinuousLinearMap.differentiableAt).comp z (hσ i d)).mul hgd
    · exact differentiableAt_const _
  have hD : ∀ j : Fin n, dDir (coordVec j) (fun y => conj ((if j = a then
      sigmaMat omega r y i b else 0) - (if j = b then sigmaMat omega r y i a else 0)) * g y) z =
      (if j = a then dDir (coordVec j) (fun y => conj (sigmaMat omega r y i b) * g y) z else 0) -
      (if j = b then dDir (coordVec j) (fun y => conj (sigmaMat omega r y i a) * g y) z else 0) :=
    fun j => by
      rw [hfun j, dDir_sub (hd1 j a b) (hd1 j b a), dDir_ite_fun, dDir_ite_fun]
  simp only [h0, hD, neg_zero, zero_sub, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [dDir_conj_mul (hσ i b) hgd, dDir_conj_mul (hσ i a) hgd]
  simp only [map_sub]
  ring

end Adjoint

theorem adj_eq (omega : SGPT.Foundations.Analysis.FirstPass.PositiveClasses.KahlerBackground n
    (ComplexModel n)) (r p : ComplexModel n → ℝ) {D : Set (ComplexModel n)}
    (hσD : ∀ z ∈ D, ∀ l k, DifferentiableAt ℝ (fun y => sigmaMat omega r y l k) z)
    (h : Fin (n * n + 1) → ComplexModel n → ℂ) (hh : ∀ i', IsTestFunctionOn D (h i'))
    (i : Fin n) (z : ComplexModel n) :
    firstOrderAdjointApply (sysA (n := n)) (sysA' omega r) (sysB omega r p) h i z =
      (dbarDir (coordVec i) (h (Fin.last _)) z +
        conj (dDir (coordVec i) (fun y => (p y : ℂ)) z) * h (Fin.last _) z) +
      ∑ q : Fin (n * n), (-conj (sigmaMat omega r z i (rowJK q).2) *
          dDir (coordVec (rowJK q).1) (h q.castSucc) z +
        conj (sigmaMat omega r z i (rowJK q).1) * dDir (coordVec (rowJK q).2) (h q.castSucc) z) := by
  by_cases hz : z ∈ D
  · rw [firstOrderAdjointApply_eq_sum, Fin.sum_univ_castSucc, adj_row_last omega r p _ (hh _).1,
      Finset.sum_congr rfl fun q _ => adj_row_S omega r p (hh _).1 (hσD z hz) q i, add_comm]
  · have hz' : ∀ i', z ∉ tsupport (h i') := fun i' h' => hz ((hh i').2.2 h')
    rw [FriedrichsProof.firstOrderAdjointApply_eq_zero_of_notMem _ _ _ _ _ hz']
    simp [dbarDir_eq_zero_of_notMem (hz' _), dDir_eq_zero_of_notMem (hz' _),
      image_eq_zero_of_notMem_tsupport (hz' _)]

/-! ### `L²` bookkeeping on compact sets -/

theorem memLp_of_le_on_compact {E : Type*} [NormedAddCommGroup E] {f : ComplexModel n → E}
    (x : H2 n) {K : Set (ComplexModel n)} (hf : AEStronglyMeasurable f volume) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ z ∈ K, ‖f z‖ ≤ C * ‖x z‖) (h0 : ∀ z ∉ K, f z = 0) : MemLp f 2 volume := by
  refine (Lp.memLp x).of_le_mul (c := C) hf (Eventually.of_forall fun z => ?_)
  by_cases hz : z ∈ K
  · exact hb z hz
  · rw [h0 z hz, norm_zero]; positivity

theorem integrable_of_le_on_compact {E : Type*} [NormedAddCommGroup E] {f : ComplexModel n → E}
    (x : H2 n) {K : Set (ComplexModel n)} (hK : IsCompact K) (hf : AEStronglyMeasurable f volume)
    {C : ℝ} (hb : ∀ z ∈ K, ‖f z‖ ≤ C * ‖x z‖) (h0 : ∀ z ∉ K, f z = 0) : Integrable f volume := by
  have : IsFiniteMeasure (volume.restrict K) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hK.measure_lt_top⟩
  have hx : Integrable (fun z => C * ‖x z‖) (volume.restrict K) :=
    (((Lp.memLp x).restrict K).integrable (by norm_num)).norm.const_mul C
  refine Integrable.mono' (IntegrableOn.integrable_indicator (μ := volume) hx hK.measurableSet) hf (Eventually.of_forall fun z => ?_)
  by_cases hz : z ∈ K
  · rw [indicator_of_mem hz]; exact hb z hz
  · rw [indicator_of_notMem hz, h0 z hz, norm_zero]

theorem dbarDir_exp_ofReal {p : ComplexModel n → ℝ} {x : ComplexModel n}
    (hp : DifferentiableAt ℝ p x) (v : ComplexModel n) :
    dbarDir v (fun y => ((Real.exp (p y) : ℝ) : ℂ)) x =
      ((Real.exp (p x) : ℝ) : ℂ) * dbarDir v (fun y => (p y : ℂ)) x := by
  have h1 : HasFDerivAt (fun y => Real.exp (p y)) (Real.exp (p x) • fderiv ℝ p x) x :=
    hp.hasFDerivAt.exp
  have h2 : fderiv ℝ (fun y => ((Real.exp (p y) : ℝ) : ℂ)) x =
      Complex.ofRealCLM.comp (Real.exp (p x) • fderiv ℝ p x) :=
    ((Complex.ofRealCLM.hasFDerivAt).comp x h1).fderiv
  have h3 : fderiv ℝ (fun y => (p y : ℂ)) x = Complex.ofRealCLM.comp (fderiv ℝ p x) :=
    ((Complex.ofRealCLM.hasFDerivAt).comp x hp.hasFDerivAt).fderiv
  simp only [dbarDir, h2, h3, ContinuousLinearMap.comp_apply, _root_.smul_apply,
    smul_eq_mul, Complex.ofRealCLM_apply, Complex.ofReal_mul]
  ring

/-- Componentwise `L²` convergence of a sum bound. -/
theorem tendsto_eLpNorm_sum {ι : Type*} (s : Finset ι) {E : Type*} [NormedAddCommGroup E]
    {μ : Measure (ComplexModel n)} {F : ℕ → ComplexModel n → E} {G : ι → ℕ → ComplexModel n → ℂ}
    (hG : ∀ i m, AEStronglyMeasurable (G i m) μ) (hb : ∀ m z, ‖F m z‖ ≤ ∑ i ∈ s, ‖G i m z‖)
    (h : ∀ i ∈ s, Tendsto (fun m => eLpNorm (G i m) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun m => eLpNorm (F m) 2 μ) atTop (𝓝 0) := by
  have hle : ∀ m, eLpNorm (F m) 2 μ ≤ ∑ i ∈ s, eLpNorm (G i m) 2 μ := by
    intro m
    refine (eLpNorm_mono_real (g := fun z => ∑ i ∈ s, ‖G i m z‖) (hb m)).trans ?_
    have h1 := eLpNorm_sum_le (f := fun i z => ‖G i m z‖) (s := s) (p := 2) (μ := μ)
      (fun i _ => (hG i m).norm) (by norm_num)
    have h2 : (∑ i ∈ s, fun z => ‖G i m z‖) = fun z => ∑ i ∈ s, ‖G i m z‖ := by
      funext z; simp [Finset.sum_apply]
    rw [h2] at h1
    refine h1.trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
    exact eLpNorm_norm _
  have hsum : Tendsto (fun m => ∑ i ∈ s, eLpNorm (G i m) 2 μ) atTop (𝓝 0) := by
    have := tendsto_finsetSum s h
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun _ => by positivity)
    hle

theorem conj_dbarDir_ofReal {χ : ComplexModel n → ℝ} {z : ComplexModel n}
    (hχ : DifferentiableAt ℝ χ z) (v : ComplexModel n) :
    conj (dbarDir v (fun y => (χ y : ℂ)) z) = dDir v (fun y => (χ y : ℂ)) z := by
  rw [dDir_ofReal_eq_conj hχ]

namespace TwistedDatum

variable {T : TwistedDatum n (ComplexModel n)} {ρ : ComplexModel n → ℝ}

variable (T ρ) in
/-- The frame coefficient `uc e · Weps x` of a field `x ∈ H₂`. -/
def We (e : AtlasFrame T.L) (x : ComplexModel n → ComplexModel n) (z : ComplexModel n) :
    ComplexModel n :=
  uc e z • T.Weps ρ x z

theorem We_eq_zero {e : AtlasFrame T.L} {x : ComplexModel n → ComplexModel n} {z : ComplexModel n}
    (hz : z ∉ T.U) : T.We ρ e x z = 0 := by
  simp [We, Weps, indicator_of_notMem hz]

variable (hρ : IsChartDensity T.μ chart0 ρ)
include hρ

theorem aestronglyMeasurable_We (e : AtlasFrame T.L) (x : H2 n) :
    AEStronglyMeasurable (T.We ρ e x) volume :=
  (measurable_uc e).aestronglyMeasurable.smul (aestronglyMeasurable_Weps hρ (Lp.aestronglyMeasurable x))

theorem exists_We_bound {e : AtlasFrame T.L} {K : Set (ComplexModel n)} (hK : IsCompact K)
    (hKd : K ⊆ T.dom e) : ∃ C, 0 ≤ C ∧ ∀ (x : ComplexModel n → ComplexModel n), ∀ z ∈ K,
      ‖T.We ρ e x z‖ ≤ C * ‖x z‖ := by
  set κ : ComplexModel n → ℝ := fun z =>
    (Real.sqrt (frameNormSq T.L e z))⁻¹ * (T.sw ρ z)⁻¹ * mnorm (Bi T.omega T.r z)
  have hκ : ContinuousOn κ (T.dom e) := by
    have h1 : ContinuousOn (fun z => Real.sqrt (frameNormSq T.L e z)) (T.dom e) :=
      ((continuousOn_frameNormSq e).mono fun z hz => ((T.mem_dom).mp hz).1).sqrt
    have h2 := (continuousOn_sw hρ).mono (dom_subset_U e)
    have h3 := (continuous_mnorm.comp_continuousOn
      (continuousOn_Bi T.isOpen_U T.kahler)).mono (dom_subset_U e)
    refine ((h1.inv₀ fun z hz => ?_).mul (h2.inv₀ fun z _ => (sw_pos hρ z).ne')).mul h3
    exact (Real.sqrt_pos.mpr (frameNormSq_pos e ((T.mem_dom).mp hz).1)).ne'
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hκ.mono hKd)
  refine ⟨max C 0, le_max_right _ _, fun x z hz => ?_⟩
  have hzd := hKd hz
  have hzU := dom_subset_U e hzd
  have hzb := ((T.mem_dom).mp hzd).1
  have hb : ‖T.We ρ e x z‖ ≤ κ z * ‖x z‖ := by
    rw [We, Weps, indicator_of_mem hzU, norm_smul, norm_smul, Complex.norm_real, norm_inv,
      Real.norm_of_nonneg (sw_pos hρ z).le]
    have hu : ‖uc e z‖ = (Real.sqrt (frameNormSq T.L e z))⁻¹ := by
      rw [← norm_inv_uc hzb, norm_inv, inv_inv]
    rw [hu]
    have h1 := norm_mv_le (Bi T.omega T.r z) (x z)
    have hp : 0 ≤ (Real.sqrt (frameNormSq T.L e z))⁻¹ * (T.sw ρ z)⁻¹ :=
      mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) (inv_nonneg.mpr (sw_pos hρ z).le)
    calc (Real.sqrt (frameNormSq T.L e z))⁻¹ * ((T.sw ρ z)⁻¹ * ‖mv (Bi T.omega T.r z) (x z)‖)
        = ((Real.sqrt (frameNormSq T.L e z))⁻¹ * (T.sw ρ z)⁻¹) *
          ‖mv (Bi T.omega T.r z) (x z)‖ := by ring
      _ ≤ ((Real.sqrt (frameNormSq T.L e z))⁻¹ * (T.sw ρ z)⁻¹) *
          (mnorm (Bi T.omega T.r z) * ‖x z‖) := mul_le_mul_of_nonneg_left h1 hp
      _ = κ z * ‖x z‖ := by simp only [κ]; ring
  refine hb.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  exact (le_abs_self _).trans ((Real.norm_eq_abs _ ▸ hC z hz).trans (le_max_left _ _))

theorem integrable_We_mul (v : H2 n) {e : AtlasFrame T.L} {c : ComplexModel n → ℂ}
    (hc : Continuous c) (hcs : HasCompactSupport c) (hcd : tsupport c ⊆ T.dom e) (i : Fin n) :
    Integrable (fun z => T.We ρ e v z i * c z) := by
  obtain ⟨C, hC0, hC⟩ := exists_We_bound hρ hcs hcd
  obtain ⟨M, hM⟩ := hcs.exists_bound_of_continuousOn hc.continuousOn
  have hm : AEStronglyMeasurable (fun z => T.We ρ e v z i * c z) volume :=
    (((EuclideanSpace.proj i : ComplexModel n →L[ℂ] ℂ).continuous).comp_aestronglyMeasurable
      (aestronglyMeasurable_We hρ e v)).mul hc.aestronglyMeasurable
  refine integrable_of_le_on_compact v hcs hm (C := C * M) (fun z hz => ?_)
    fun z hz => by simp [image_eq_zero_of_notMem_tsupport hz]
  rw [norm_mul]
  have h1 := (norm_coord_le (T.We ρ e v z) i).trans (hC v z hz)
  have h2 := hM z hz
  have h3 : 0 ≤ ‖c z‖ := norm_nonneg _
  calc ‖T.We ρ e v z i‖ * ‖c z‖ ≤ (C * ‖v z‖) * M :=
        mul_le_mul h1 h2 h3 (by positivity)
    _ = C * M * ‖v z‖ := by ring

variable (T ρ) in
/-- The `ϑ`-row of the weak equation: `f_ϑ = ζ ϑ_p τ - ∑_l ∂_l ζ W_l`. -/
def f0 (F : T.FrameFamily) (e : AtlasFrame T.L) (ζ : ComplexModel n → ℝ)
    (x : ComplexModel n → ComplexModel n) (z : ComplexModel n) : ℂ :=
  (ζ z : ℂ) * chartTheta (T.pW ρ e) (T.tot F.s F.e F.h e) z -
    ∑ l, dDir (coordVec l) (fun y => (ζ y : ℂ)) z * T.We ρ e x z l

variable (T ρ) in
/-- The `∂̄σ^♭`-rows of the weak equation: `f_{jk} = ∂_{j̄}ζ (σ^♭W)_k - ∂_{k̄}ζ (σ^♭W)_j`. -/
def fS (e : AtlasFrame T.L) (ζ : ComplexModel n → ℝ) (x : ComplexModel n → ComplexModel n)
    (j k : Fin n) (z : ComplexModel n) : ℂ :=
  dbarDir (coordVec j) (fun y => (ζ y : ℂ)) z * mv (sT T.omega T.r z) (T.We ρ e x z) k -
    dbarDir (coordVec k) (fun y => (ζ y : ℂ)) z * mv (sT T.omega T.r z) (T.We ρ e x z) j

variable (T ρ) in
/-- The localized field `w = ζ W_e(x)`, componentwise. -/
def wsys (e : AtlasFrame T.L) (ζ : ComplexModel n → ℝ) (x : ComplexModel n → ComplexModel n) :
    Fin n → ComplexModel n → ℂ := fun i z => (ζ z : ℂ) * T.We ρ e x z i

/-- **The `ϑ`-row of the weak equation**, from `T* v = T* τ`. -/
theorem row_last (F : T.FrameFamily) (v : H2 n)
    (hW2 : ∀ (e : AtlasFrame T.L) (u : ComplexModel n → ℂ), IsTestFunctionOn (T.dom e) u →
      ∫ z, (T.dom e).indicator (fun z => cweight (T.pW ρ e) z *
        ∑ l, dbarDir (coordVec l) u z * conj ((uc e z • T.Weps ρ v z) l)) z =
      ∫ z, u z * conj (chartTheta (T.pW ρ e) (T.tot F.s F.e F.h e) z) * cweight (T.pW ρ e) z)
    {e : AtlasFrame T.L} {ζ : ComplexModel n → ℝ} (hζ : ContDiff ℝ ∞ ζ) {D : Set (ComplexModel n)}
    (hDd : D ⊆ T.dom e) {g : ComplexModel n → ℂ} (hg : IsTestFunctionOn D g) :
    ∑ i, ∫ z, T.wsys ρ e ζ v i z * conj (dbarDir (coordVec i) g z +
      conj (dDir (coordVec i) (fun y => (T.pW ρ e y : ℂ)) z) * g z) =
      ∫ z, T.f0 ρ F e ζ v z * conj (g z) := by
  set p := T.pW ρ e with hp
  set E : ComplexModel n → ℂ := fun y => ((Real.exp (p y) : ℝ) : ℂ) with hE
  have hO := T.isOpen_dom e
  have hpD : ContDiffOn ℝ ∞ p (T.dom e) := T.contDiffOn_pW hρ e
  have hED : ContDiffOn ℝ ∞ E (T.dom e) :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn (Real.contDiff_exp.comp_contDiffOn hpD)
  have hgd : tsupport g ⊆ T.dom e := hg.2.2.trans hDd
  have hEg : ContDiff ℝ ∞ (fun y => E y * g y) := contDiff_mul_of_tsupport_subset hO hED hg.1 hgd
  have hζc : ContDiff ℝ ∞ (fun y => (ζ y : ℂ)) := Complex.ofRealCLM.contDiff.comp hζ
  set u : ComplexModel n → ℂ := fun y => (ζ y : ℂ) * (E y * g y) with hu_def
  have hEgs : tsupport (fun y => E y * g y) ⊆ tsupport g := tsupport_mul_subset_right
  have hus : tsupport u ⊆ tsupport g := tsupport_mul_subset_right.trans hEgs
  have hu : IsTestFunctionOn (T.dom e) u :=
    ⟨hζc.mul hEg, hg.2.1.mono' (subset_closure.trans hus), hus.trans hgd⟩
  have hW := hW2 e u hu
  have hWc := congrArg conj hW
  rw [← integral_conj, ← integral_conj] at hWc
  -- the pointwise identities
  have hcw : ∀ z, cweight p z * E z = 1 := fun z => by
    rw [cweight, hE, ← Complex.ofReal_mul, ← Real.exp_add, neg_add_cancel, Real.exp_zero,
      Complex.ofReal_one]
  have hcwc : ∀ z, conj (cweight p z) = cweight p z := fun z => by
    rw [cweight, Complex.conj_ofReal]
  have hEc : ∀ z, conj (E z) = E z := fun z => Complex.conj_ofReal _
  have hpt : ∀ z, conj ((T.dom e).indicator (fun z => cweight p z *
      ∑ l, dbarDir (coordVec l) u z * conj ((uc e z • T.Weps ρ v z) l)) z) =
      ∑ i, (T.wsys ρ e ζ v i z * conj (dbarDir (coordVec i) g z +
        conj (dDir (coordVec i) (fun y => (p y : ℂ)) z) * g z) +
        T.We ρ e v z i * (dDir (coordVec i) (fun y => (ζ y : ℂ)) z * conj (g z))) := by
    intro z
    by_cases hz : z ∈ T.dom e
    · rw [indicator_of_mem hz]
      have hpz : DifferentiableAt ℝ p z :=
        (hpD.contDiffAt (hO.mem_nhds hz)).differentiableAt (by simp)
      have hζz : DifferentiableAt ℝ ζ z := hζ.differentiable (by simp) z
      have hζz' : DifferentiableAt ℝ (fun y => (ζ y : ℂ)) z := hζc.differentiable (by simp) z
      have hgz : DifferentiableAt ℝ g z := hg.1.differentiable (by simp) z
      have hEz : DifferentiableAt ℝ E z := (hED.contDiffAt (hO.mem_nhds hz)).differentiableAt (by simp)
      have hdu : ∀ l, dbarDir (coordVec l) u z =
          dbarDir (coordVec l) (fun y => (ζ y : ℂ)) z * (E z * g z) +
            (ζ z : ℂ) * (E z * (dbarDir (coordVec l) (fun y => (p y : ℂ)) z * g z +
              dbarDir (coordVec l) g z)) := by
        intro l
        have hEgz : DifferentiableAt ℝ (fun y => E y * g y) z := hEz.mul hgz
        rw [hu_def, dbarDir_mul hζz' hEgz, dbarDir_mul hEz hgz, hE, dbarDir_exp_ofReal hpz]
        ring
      simp only [hdu, map_mul, map_sum, map_add, hcwc, hEc, Complex.conj_ofReal, Complex.conj_conj,
        conj_dbarDir_ofReal hζz, conj_dbarDir_ofReal hpz, Finset.mul_sum, wsys, We]
      refine Finset.sum_congr rfl fun l _ => ?_
      linear_combination (conj (g z) * (dDir (coordVec l) (fun y => (ζ y : ℂ)) z +
          (ζ z : ℂ) * dDir (coordVec l) (fun y => (p y : ℂ)) z) * (uc e z • T.Weps ρ v z) l +
        (ζ z : ℂ) * conj (dbarDir (coordVec l) g z) * (uc e z • T.Weps ρ v z) l) * hcw z
    · have hzg : z ∉ tsupport g := fun h => hz (hgd h)
      rw [indicator_of_notMem hz, map_zero]
      simp [image_eq_zero_of_notMem_tsupport hzg, dbarDir_eq_zero_of_notMem hzg, wsys]
  -- integrability
  have hgc : Continuous g := hg.1.continuous
  have hconj_g : Continuous fun z => conj (g z) := Complex.continuous_conj.comp hgc
  have hgcs : HasCompactSupport g := hg.2.1
  have hcomp : ∀ c : ComplexModel n → ℂ, (∀ z, z ∉ tsupport g → c z = 0) →
      HasCompactSupport c ∧ tsupport c ⊆ T.dom e := fun c hc => by
    have hsub : tsupport c ⊆ tsupport g :=
      closure_minimal (fun z hz => by by_contra h; exact hz (hc z h)) (isClosed_tsupport g)
    exact ⟨hgcs.mono' (subset_closure.trans hsub), hsub.trans hgd⟩
  have hdp : ∀ i, ContinuousOn (dDir (coordVec i) (fun y => (p y : ℂ))) (T.dom e) := fun i =>
    (contDiffOn_dDir hO (contDiffOn_ofReal' hpD) _).continuousOn
  have hA : ∀ i, Integrable (fun z => T.wsys ρ e ζ v i z * conj (dbarDir (coordVec i) g z +
      conj (dDir (coordVec i) (fun y => (p y : ℂ)) z) * g z)) := by
    intro i
    set c : ComplexModel n → ℂ := fun z => (ζ z : ℂ) * conj (dbarDir (coordVec i) g z +
      conj (dDir (coordVec i) (fun y => (p y : ℂ)) z) * g z)
    have hc : Continuous c := by
      have h1 : Continuous fun z => conj (dDir (coordVec i) (fun y => (p y : ℂ)) z) * g z :=
        continuous_mul_of_continuousOn hO (Complex.continuous_conj.comp_continuousOn (hdp i)) hgc hgd
      exact (Complex.continuous_ofReal.comp hζ.continuous).mul (Complex.continuous_conj.comp
        ((continuous_dbarDir' (hg.1.of_le (by simp))).add h1))
    obtain ⟨hcs, hcd⟩ := hcomp c fun z hz => by
      simp [c, image_eq_zero_of_notMem_tsupport hz, dbarDir_eq_zero_of_notMem hz]
    refine (integrable_We_mul hρ v hc hcs hcd i).congr (Eventually.of_forall fun z => ?_)
    simp only [wsys, c]; ring
  have hB : ∀ i, Integrable (fun z => T.We ρ e v z i *
      (dDir (coordVec i) (fun y => (ζ y : ℂ)) z * conj (g z))) := by
    intro i
    have hc : Continuous fun z => dDir (coordVec i) (fun y => (ζ y : ℂ)) z * conj (g z) :=
      (contDiff_dDir (k := 0) (hζc.of_le (by norm_num))).continuous.mul hconj_g
    obtain ⟨hcs, hcd⟩ := hcomp (fun z => dDir (coordVec i) (fun y => (ζ y : ℂ)) z * conj (g z))
      fun z hz => by simp [image_eq_zero_of_notMem_tsupport hz]
    exact integrable_We_mul hρ v hc hcs hcd i
  have hθc : ContinuousOn (chartTheta p (T.tot F.s F.e F.h e)) (T.dom e) :=
    continuousOn_chartTheta' hO hpD
      ((T.contDiffOn_tot F.spec e).mono fun z hz => ((T.mem_dom).mp hz).1)
  have hC : Integrable (fun z => (ζ z : ℂ) * conj (g z) * chartTheta p (T.tot F.s F.e F.h e) z) := by
    have h1 : Continuous fun z => (ζ z : ℂ) * conj (g z) :=
      (Complex.continuous_ofReal.comp hζ.continuous).mul hconj_g
    obtain ⟨hcs, hcd⟩ := hcomp (fun z => (ζ z : ℂ) * conj (g z))
      fun z hz => by simp [image_eq_zero_of_notMem_tsupport hz]
    have h2 : Continuous fun z => (ζ z : ℂ) * conj (g z) * chartTheta p (T.tot F.s F.e F.h e) z := by
      have := continuous_mul_of_continuousOn hO hθc h1 hcd
      exact this.congr fun z => mul_comm _ _
    exact h2.integrable_of_hasCompactSupport hcs.mul_right
  have hrhs : ∀ z, conj (u z * conj (chartTheta p (T.tot F.s F.e F.h e) z) * cweight p z) =
      (ζ z : ℂ) * conj (g z) * chartTheta p (T.tot F.s F.e F.h e) z := by
    intro z
    simp only [hu_def, map_mul, Complex.conj_conj, hcwc, hEc, Complex.conj_ofReal]
    linear_combination ((ζ z : ℂ) * conj (g z) * chartTheta p (T.tot F.s F.e F.h e) z) * hcw z
  rw [← hp] at hWc
  simp only [hpt, hrhs] at hWc
  have hsum := integral_finsetSum Finset.univ fun i _ => (hA i).add (hB i)
  simp only [Pi.add_apply] at hsum
  rw [hsum] at hWc
  simp only [integral_add (hA _) (hB _), Finset.sum_add_distrib] at hWc
  rw [← integral_finsetSum _ fun i _ => hB i] at hWc
  have hf0 : ∀ z, T.f0 ρ F e ζ v z * conj (g z) = (ζ z : ℂ) * conj (g z) *
      chartTheta p (T.tot F.s F.e F.h e) z - ∑ i, T.We ρ e v z i *
        (dDir (coordVec i) (fun y => (ζ y : ℂ)) z * conj (g z)) := by
    intro z
    simp only [f0, sub_mul, Finset.sum_mul]
    congr 1
    · ring
    · exact Finset.sum_congr rfl fun i _ => by ring
  simp only [hf0]
  rw [integral_sub hC (integrable_finsetSum _ fun i _ => hB i), ← hWc]
  ring

omit hρ in
theorem mv_sT_apply (z : ComplexModel n) (x : ComplexModel n) (j : Fin n) :
    mv (sT T.omega T.r z) x j = ∑ i, sigmaMat T.omega T.r z i j * x i := by
  simp [mv_apply, sT, transpose_apply]

/-- **The `∂̄σ^♭`-rows of the weak equation**, from `∂̄(σ^♭ v) = 0`. -/
theorem row_S (v : H2 n)
    (hW1 : ∀ (e : AtlasFrame T.L) (ψ : ComplexModel n → ℂ), IsTestFunctionOn (T.dom e) ψ →
      ∀ j k : Fin n, ∫ z, (T.dom e).indicator (fun z =>
        conj (dDir (coordVec k) ψ z) * mv (sT T.omega T.r z) (uc e z • T.Weps ρ v z) j -
        conj (dDir (coordVec j) ψ z) * mv (sT T.omega T.r z) (uc e z • T.Weps ρ v z) k) z = 0)
    {e : AtlasFrame T.L} {ζ : ComplexModel n → ℝ} (hζ : ContDiff ℝ ∞ ζ) {D : Set (ComplexModel n)}
    (hDd : D ⊆ T.dom e) {g : ComplexModel n → ℂ} (hg : IsTestFunctionOn D g) (j k : Fin n) :
    ∑ i, ∫ z, T.wsys ρ e ζ v i z * conj (-conj (sigmaMat T.omega T.r z i k) *
      dDir (coordVec j) g z + conj (sigmaMat T.omega T.r z i j) * dDir (coordVec k) g z) =
      ∫ z, T.fS ρ e ζ v j k z * conj (g z) := by
  have hO := T.isOpen_dom e
  have hgd : tsupport g ⊆ T.dom e := hg.2.2.trans hDd
  have hζc : ContDiff ℝ ∞ (fun y => (ζ y : ℂ)) := Complex.ofRealCLM.contDiff.comp hζ
  set ψ : ComplexModel n → ℂ := fun y => (ζ y : ℂ) * g y with hψ_def
  have hψs : tsupport ψ ⊆ tsupport g := tsupport_mul_subset_right
  have hψ : IsTestFunctionOn (T.dom e) ψ :=
    ⟨hζc.mul hg.1, hg.2.1.mono' (subset_closure.trans hψs), hψs.trans hgd⟩
  have hW := hW1 e ψ hψ j k
  have hgc : Continuous g := hg.1.continuous
  have hgcs : HasCompactSupport g := hg.2.1
  have hcomp : ∀ c : ComplexModel n → ℂ, (∀ z, z ∉ tsupport g → c z = 0) →
      HasCompactSupport c ∧ tsupport c ⊆ T.dom e := fun c hc => by
    have hsub : tsupport c ⊆ tsupport g :=
      closure_minimal (fun z hz => by by_contra h; exact hz (hc z h)) (isClosed_tsupport g)
    exact ⟨hgcs.mono' (subset_closure.trans hsub), hsub.trans hgd⟩
  have hσc : ∀ a b, ContinuousOn (fun z => sigmaMat T.omega T.r z a b) (T.dom e) := fun a b =>
    (contDiffOn_sigmaMat T.isOpen_U T.kahler a b).continuousOn.mono (dom_subset_U e)
  have hdg : ∀ a, Continuous (dDir (coordVec a) g) := fun a =>
    (contDiff_dDir (k := 0) (hg.1.of_le (by norm_num))).continuous
  -- the pointwise identity
  have hpt : ∀ z, (T.dom e).indicator (fun z =>
      conj (dDir (coordVec k) ψ z) * mv (sT T.omega T.r z) (uc e z • T.Weps ρ v z) j -
      conj (dDir (coordVec j) ψ z) * mv (sT T.omega T.r z) (uc e z • T.Weps ρ v z) k) z =
      ∑ i, T.wsys ρ e ζ v i z * conj (-conj (sigmaMat T.omega T.r z i k) *
        dDir (coordVec j) g z + conj (sigmaMat T.omega T.r z i j) * dDir (coordVec k) g z) -
      T.fS ρ e ζ v j k z * conj (g z) := by
    intro z
    by_cases hz : z ∈ T.dom e
    · rw [indicator_of_mem hz]
      have hζz : DifferentiableAt ℝ ζ z := hζ.differentiable (by simp) z
      have hζz' : DifferentiableAt ℝ (fun y => (ζ y : ℂ)) z := hζc.differentiable (by simp) z
      have hgz : DifferentiableAt ℝ g z := hg.1.differentiable (by simp) z
      have hdψ : ∀ a, dDir (coordVec a) ψ z =
          dDir (coordVec a) (fun y => (ζ y : ℂ)) z * g z + (ζ z : ℂ) * dDir (coordVec a) g z :=
        fun a => by rw [hψ_def, dDir_mul hζz' hgz]
      simp only [hdψ, map_add, map_mul, Complex.conj_ofReal, dDir_ofReal_eq_conj hζz,
        Complex.conj_conj, fS, mv_sT_apply, wsys, We, Finset.mul_sum, Finset.sum_mul,
        ← Finset.sum_sub_distrib, map_neg, neg_mul]
      exact Finset.sum_congr rfl fun i _ => by ring
    · have hzg : z ∉ tsupport g := fun h => hz (hgd h)
      rw [indicator_of_notMem hz]
      simp [image_eq_zero_of_notMem_tsupport hzg, dDir_eq_zero_of_notMem hzg]
  -- integrability
  have hA : ∀ i, Integrable (fun z => T.wsys ρ e ζ v i z * conj (-conj (sigmaMat T.omega T.r z i k) *
      dDir (coordVec j) g z + conj (sigmaMat T.omega T.r z i j) * dDir (coordVec k) g z)) := by
    intro i
    set c : ComplexModel n → ℂ := fun z => (ζ z : ℂ) * conj (-conj (sigmaMat T.omega T.r z i k) *
      dDir (coordVec j) g z + conj (sigmaMat T.omega T.r z i j) * dDir (coordVec k) g z)
    have hc : Continuous c := by
      have h1 : ∀ a b, Continuous fun z => conj (sigmaMat T.omega T.r z i a) * dDir (coordVec b) g z :=
        fun a b => continuous_mul_of_continuousOn hO
          (Complex.continuous_conj.comp_continuousOn (hσc i a)) (hdg b)
          ((tsupport_dDir_subset' _ _).trans hgd)
      have h2 : Continuous fun z => -conj (sigmaMat T.omega T.r z i k) * dDir (coordVec j) g z +
          conj (sigmaMat T.omega T.r z i j) * dDir (coordVec k) g z := by
        have := ((h1 k j).neg).add (h1 j k)
        refine this.congr fun z => ?_
        simp only [Pi.add_apply, Pi.neg_apply]; ring
      exact (Complex.continuous_ofReal.comp hζ.continuous).mul (Complex.continuous_conj.comp h2)
    obtain ⟨hcs, hcd⟩ := hcomp c fun z hz => by
      simp [c, dDir_eq_zero_of_notMem hz]
    refine (integrable_We_mul hρ v hc hcs hcd i).congr (Eventually.of_forall fun z => ?_)
    simp only [wsys, c]; ring
  have hF : Integrable (fun z => T.fS ρ e ζ v j k z * conj (g z)) := by
    have h1 : ∀ i (a b : Fin n), Integrable (fun z => T.We ρ e v z i *
        (dbarDir (coordVec a) (fun y => (ζ y : ℂ)) z * sigmaMat T.omega T.r z i b * conj (g z))) := by
      intro i a b
      have hc : Continuous fun z => dbarDir (coordVec a) (fun y => (ζ y : ℂ)) z *
          sigmaMat T.omega T.r z i b * conj (g z) := by
        have h2 : Continuous fun z => sigmaMat T.omega T.r z i b * conj (g z) :=
          continuous_mul_of_continuousOn hO (hσc i b) (Complex.continuous_conj.comp hgc)
            ((tsupport_comp_subset (map_zero _) _).trans hgd)
        refine ((continuous_dbarDir' (hζc.of_le (by simp)) (v := coordVec a)).mul h2).congr
          fun z => ?_
        simp only [Pi.mul_apply]; ring
      obtain ⟨hcs, hcd⟩ := hcomp (fun z => dbarDir (coordVec a) (fun y => (ζ y : ℂ)) z *
          sigmaMat T.omega T.r z i b * conj (g z)) fun z hz => by
        simp [image_eq_zero_of_notMem_tsupport hz]
      exact integrable_We_mul hρ v hc hcs hcd i
    have h3 : (fun z => T.fS ρ e ζ v j k z * conj (g z)) = fun z => ∑ i, (T.We ρ e v z i *
        (dbarDir (coordVec j) (fun y => (ζ y : ℂ)) z * sigmaMat T.omega T.r z i k * conj (g z)) -
        T.We ρ e v z i * (dbarDir (coordVec k) (fun y => (ζ y : ℂ)) z *
          sigmaMat T.omega T.r z i j * conj (g z))) := by
      funext z
      simp only [fS, mv_sT_apply, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [h3]
    exact integrable_finsetSum _ fun i _ => (h1 i j k).sub (h1 i k j)
  simp only [hpt] at hW
  rw [integral_sub (integrable_finsetSum _ fun i _ => hA i) hF,
    integral_finsetSum _ fun i _ => hA i] at hW
  exact sub_eq_zero.mp hW

theorem memLp_We_mul (v : H2 n) {e : AtlasFrame T.L} {c : ComplexModel n → ℂ}
    (hc : Continuous c) (hcs : HasCompactSupport c) (hcd : tsupport c ⊆ T.dom e) (i : Fin n) :
    MemLp (fun z => T.We ρ e v z i * c z) 2 volume := by
  obtain ⟨C, hC0, hC⟩ := exists_We_bound hρ hcs hcd
  obtain ⟨M, hM⟩ := hcs.exists_bound_of_continuousOn hc.continuousOn
  have hm : AEStronglyMeasurable (fun z => T.We ρ e v z i * c z) volume :=
    (((EuclideanSpace.proj i : ComplexModel n →L[ℂ] ℂ).continuous).comp_aestronglyMeasurable
      (aestronglyMeasurable_We hρ e v)).mul hc.aestronglyMeasurable
  refine memLp_of_le_on_compact v (K := tsupport c) hm (C := C * max M 0) (by positivity)
    (fun z hz => ?_) fun z hz => by simp [image_eq_zero_of_notMem_tsupport hz]
  rw [norm_mul]
  have h1 := (norm_coord_le (T.We ρ e v z) i).trans (hC v z hz)
  calc ‖T.We ρ e v z i‖ * ‖c z‖ ≤ (C * ‖v z‖) * max M 0 :=
        mul_le_mul h1 ((hM z hz).trans (le_max_left _ _)) (norm_nonneg _) (by positivity)
    _ = C * max M 0 * ‖v z‖ := by ring

theorem integrable_wsys_mul (v : H2 n) {e : AtlasFrame T.L} {ζ : ComplexModel n → ℝ}
    (hζ : Continuous ζ) {c : ComplexModel n → ℂ} (hc : Continuous c) (hcs : HasCompactSupport c)
    (hcd : tsupport c ⊆ T.dom e) (i : Fin n) :
    Integrable (fun z => T.wsys ρ e ζ v i z * c z) := by
  have hc' : Continuous fun z => (ζ z : ℂ) * c z := (Complex.continuous_ofReal.comp hζ).mul hc
  have hsub : tsupport (fun z => (ζ z : ℂ) * c z) ⊆ tsupport c := tsupport_mul_subset_right
  refine (integrable_We_mul hρ v hc' (hcs.mono' (subset_closure.trans hsub)) (hsub.trans hcd)
    i).congr (Eventually.of_forall fun z => ?_)
  simp only [wsys]; ring

variable (T ρ) in
/-- The right-hand side `f` of the weak equation `P w = f`. -/
def fsys (F : T.FrameFamily) (e : AtlasFrame T.L) (ζ : ComplexModel n → ℝ)
    (x : ComplexModel n → ComplexModel n) : Fin (n * n + 1) → ComplexModel n → ℂ := fun i' =>
  Fin.lastCases (T.f0 ρ F e ζ x) (fun q => T.fS ρ e ζ x (rowJK q).1 (rowJK q).2) i'

omit hρ in
theorem differentiableAt_sigmaMat {z : ComplexModel n} (hz : z ∈ T.U) (l k : Fin n) :
    DifferentiableAt ℝ (fun y => sigmaMat T.omega T.r y l k) z :=
  ((contDiffOn_sigmaMat T.isOpen_U T.kahler l k).contDiffAt
    (T.isOpen_U.mem_nhds hz)).differentiableAt (by simp)

/-- **The weak equation `P(ζ W_e(v)) = f`** (`claude-tl2-dens:local`). -/
theorem weak_eq (F : T.FrameFamily) (v : H2 n)
    (hW1 : ∀ (e : AtlasFrame T.L) (ψ : ComplexModel n → ℂ), IsTestFunctionOn (T.dom e) ψ →
      ∀ j k : Fin n, ∫ z, (T.dom e).indicator (fun z =>
        conj (dDir (coordVec k) ψ z) * mv (sT T.omega T.r z) (uc e z • T.Weps ρ v z) j -
        conj (dDir (coordVec j) ψ z) * mv (sT T.omega T.r z) (uc e z • T.Weps ρ v z) k) z = 0)
    (hW2 : ∀ (e : AtlasFrame T.L) (u : ComplexModel n → ℂ), IsTestFunctionOn (T.dom e) u →
      ∫ z, (T.dom e).indicator (fun z => cweight (T.pW ρ e) z *
        ∑ l, dbarDir (coordVec l) u z * conj ((uc e z • T.Weps ρ v z) l)) z =
      ∫ z, u z * conj (chartTheta (T.pW ρ e) (T.tot F.s F.e F.h e) z) * cweight (T.pW ρ e) z)
    {e : AtlasFrame T.L} {ζ : ComplexModel n → ℝ} (hζ : ContDiff ℝ ∞ ζ) {D : Set (ComplexModel n)}
    (hDd : D ⊆ T.dom e) (h : Fin (n * n + 1) → ComplexModel n → ℂ)
    (hh : ∀ i', IsTestFunctionOn D (h i')) :
    ∑ i', ∫ z, T.fsys ρ F e ζ v i' z * conj (h i' z) =
      ∑ i, ∫ z, T.wsys ρ e ζ v i z * conj (firstOrderAdjointApply (sysA (n := n))
        (sysA' T.omega T.r) (sysB T.omega T.r (T.pW ρ e)) h i z) := by
  have hO := T.isOpen_dom e
  have hσD : ∀ z ∈ D, ∀ l k, DifferentiableAt ℝ (fun y => sigmaMat T.omega T.r y l k) z :=
    fun z hz l k => differentiableAt_sigmaMat (dom_subset_U e (hDd hz)) l k
  simp only [adj_eq T.omega T.r (T.pW ρ e) hσD h hh]
  have hpD : ContDiffOn ℝ ∞ (T.pW ρ e) (T.dom e) := T.contDiffOn_pW hρ e
  -- continuity of the adjoint pieces
  have hX : ∀ i, Continuous fun z => conj (dbarDir (coordVec i) (h (Fin.last _)) z +
      conj (dDir (coordVec i) (fun y => (T.pW ρ e y : ℂ)) z) * h (Fin.last _) z) := by
    intro i
    have hg := hh (Fin.last _)
    have h1 : Continuous fun z => conj (dDir (coordVec i) (fun y => (T.pW ρ e y : ℂ)) z) *
        h (Fin.last _) z :=
      continuous_mul_of_continuousOn hO (Complex.continuous_conj.comp_continuousOn
        (contDiffOn_dDir hO (contDiffOn_ofReal' hpD) _).continuousOn) hg.1.continuous
        (hg.2.2.trans hDd)
    exact Complex.continuous_conj.comp ((continuous_dbarDir' (hg.1.of_le (by simp))).add h1)
  have hY : ∀ (q : Fin (n * n)) (i : Fin n), Continuous fun z => conj (-conj (sigmaMat T.omega T.r z
      i (rowJK q).2) * dDir (coordVec (rowJK q).1) (h q.castSucc) z + conj (sigmaMat T.omega T.r z i
        (rowJK q).1) * dDir (coordVec (rowJK q).2) (h q.castSucc) z) := by
    intro q i
    have hg := hh q.castSucc
    have h1 : ∀ a b, Continuous fun z => conj (sigmaMat T.omega T.r z i a) *
        dDir (coordVec b) (h q.castSucc) z := fun a b =>
      continuous_mul_of_continuousOn hO (Complex.continuous_conj.comp_continuousOn
        ((contDiffOn_sigmaMat T.isOpen_U T.kahler i a).continuousOn.mono (dom_subset_U e)))
        (contDiff_dDir (k := 0) (hg.1.of_le (by norm_num))).continuous
        ((tsupport_dDir_subset' _ _).trans (hg.2.2.trans hDd))
    have h2 : Continuous fun z => -conj (sigmaMat T.omega T.r z i (rowJK q).2) *
        dDir (coordVec (rowJK q).1) (h q.castSucc) z + conj (sigmaMat T.omega T.r z i
          (rowJK q).1) * dDir (coordVec (rowJK q).2) (h q.castSucc) z := by
      refine (((h1 (rowJK q).2 (rowJK q).1).neg).add (h1 (rowJK q).1 (rowJK q).2)).congr
        fun z => ?_
      simp only [Pi.add_apply, Pi.neg_apply]; ring
    exact Complex.continuous_conj.comp h2
  have hsupp : ∀ (c : ComplexModel n → ℂ) (g : ComplexModel n → ℂ), IsTestFunctionOn D g →
      (∀ z, z ∉ tsupport g → c z = 0) → HasCompactSupport c ∧ tsupport c ⊆ T.dom e :=
    fun c g hg hc => by
      have hsub : tsupport c ⊆ tsupport g :=
        closure_minimal (fun z hz => by by_contra hn; exact hz (hc z hn)) (isClosed_tsupport g)
      exact ⟨hg.2.1.mono' (subset_closure.trans hsub), hsub.trans (hg.2.2.trans hDd)⟩
  have hIX : ∀ i, Integrable fun z => T.wsys ρ e ζ v i z * conj (dbarDir (coordVec i)
      (h (Fin.last _)) z + conj (dDir (coordVec i) (fun y => (T.pW ρ e y : ℂ)) z) *
        h (Fin.last _) z) := by
    intro i
    obtain ⟨hcs, hcd⟩ := hsupp (fun z => conj (dbarDir (coordVec i) (h (Fin.last _)) z +
      conj (dDir (coordVec i) (fun y => (T.pW ρ e y : ℂ)) z) * h (Fin.last _) z))
      (h (Fin.last _)) (hh (Fin.last _)) fun z hz => by
        simp [image_eq_zero_of_notMem_tsupport hz, dbarDir_eq_zero_of_notMem hz]
    exact integrable_wsys_mul hρ v hζ.continuous (hX i) hcs hcd i
  have hIY : ∀ q i, Integrable fun z => T.wsys ρ e ζ v i z * conj (-conj (sigmaMat T.omega T.r z
      i (rowJK q).2) * dDir (coordVec (rowJK q).1) (h q.castSucc) z + conj (sigmaMat T.omega T.r z i
        (rowJK q).1) * dDir (coordVec (rowJK q).2) (h q.castSucc) z) := by
    intro q i
    obtain ⟨hcs, hcd⟩ := hsupp (fun z => conj (-conj (sigmaMat T.omega T.r z
      i (rowJK q).2) * dDir (coordVec (rowJK q).1) (h q.castSucc) z + conj (sigmaMat T.omega T.r z i
        (rowJK q).1) * dDir (coordVec (rowJK q).2) (h q.castSucc) z)) (h q.castSucc)
      (hh q.castSucc) fun z hz => by simp [dDir_eq_zero_of_notMem hz]
    exact integrable_wsys_mul hρ v hζ.continuous (hY q i) hcs hcd i
  have hsplit : ∀ i, ∫ z, T.wsys ρ e ζ v i z * conj ((dbarDir (coordVec i) (h (Fin.last _)) z +
      conj (dDir (coordVec i) (fun y => (T.pW ρ e y : ℂ)) z) * h (Fin.last _) z) +
      ∑ q : Fin (n * n), (-conj (sigmaMat T.omega T.r z i (rowJK q).2) *
          dDir (coordVec (rowJK q).1) (h q.castSucc) z + conj (sigmaMat T.omega T.r z i
            (rowJK q).1) * dDir (coordVec (rowJK q).2) (h q.castSucc) z)) =
      (∫ z, T.wsys ρ e ζ v i z * conj (dbarDir (coordVec i) (h (Fin.last _)) z +
        conj (dDir (coordVec i) (fun y => (T.pW ρ e y : ℂ)) z) * h (Fin.last _) z)) +
      ∑ q : Fin (n * n), ∫ z, T.wsys ρ e ζ v i z * conj (-conj (sigmaMat T.omega T.r z i
        (rowJK q).2) * dDir (coordVec (rowJK q).1) (h q.castSucc) z + conj (sigmaMat T.omega T.r z
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
  · simp only [fsys, Fin.lastCases_last]
    exact (row_last hρ F v hW2 hζ hDd (hh _)).symm
  · refine Finset.sum_congr rfl fun q _ => ?_
    simp only [fsys, Fin.lastCases_castSucc]
    exact (row_S hρ v hW1 hζ hDd (hh _) _ _).symm

/-- **Friedrichs approximation of the localized projected field** (`claude-tl2-dens:local`). -/
theorem exists_approx (F : T.FrameFamily) (v : H2 n)
    (hW1 : ∀ (e : AtlasFrame T.L) (ψ : ComplexModel n → ℂ), IsTestFunctionOn (T.dom e) ψ →
      ∀ j k : Fin n, ∫ z, (T.dom e).indicator (fun z =>
        conj (dDir (coordVec k) ψ z) * mv (sT T.omega T.r z) (uc e z • T.Weps ρ v z) j -
        conj (dDir (coordVec j) ψ z) * mv (sT T.omega T.r z) (uc e z • T.Weps ρ v z) k) z = 0)
    (hW2 : ∀ (e : AtlasFrame T.L) (u : ComplexModel n → ℂ), IsTestFunctionOn (T.dom e) u →
      ∫ z, (T.dom e).indicator (fun z => cweight (T.pW ρ e) z *
        ∑ l, dbarDir (coordVec l) u z * conj ((uc e z • T.Weps ρ v z) l)) z =
      ∫ z, u z * conj (chartTheta (T.pW ρ e) (T.tot F.s F.e F.h e) z) * cweight (T.pW ρ e) z)
    {e : AtlasFrame T.L} {ζ : ComplexModel n → ℝ} (hζ : ContDiff ℝ ∞ ζ) (hζc : HasCompactSupport ζ)
    {D : Set (ComplexModel n)} (hD : IsOpen D) (hζD : tsupport ζ ⊆ D) (hDd : D ⊆ T.dom e) :
    ∃ hs : ℕ → ComplexModel n → ComplexModel n,
      (∀ m, IsLocalTestField T.L T.U chart0 e (hs m)) ∧ (∀ m, tsupport (hs m) ⊆ D) ∧
      Tendsto (fun m => eLpNorm (fun z => hs m z - ofComps (T.wsys ρ e ζ v) z) 2 volume)
        atTop (𝓝 0) ∧
      Tendsto (fun m => eLpNorm (fun z => chartTheta (T.pW ρ e) (hs m) z - T.f0 ρ F e ζ v z) 2
        (volume.restrict D)) atTop (𝓝 0) ∧
      (∀ j k : Fin n, Tendsto (fun m => eLpNorm (fun z => sigmaDbar T.omega T.r (hs m) z j k -
        T.fS ρ e ζ v j k z) 2 (volume.restrict D)) atTop (𝓝 0)) ∧
      MemLp (T.f0 ρ F e ζ v) 2 volume ∧ ∀ j k : Fin n, MemLp (T.fS ρ e ζ v j k) 2 volume := by
  have hO := T.isOpen_dom e
  have hDU : D ⊆ T.U := hDd.trans (dom_subset_U e)
  have hζd : tsupport ζ ⊆ T.dom e := hζD.trans hDd
  have hσ : ∀ l k, ContDiffOn ℝ ∞ (fun z => sigmaMat T.omega T.r z l k) D := fun l k =>
    (contDiffOn_sigmaMat T.isOpen_U T.kahler l k).mono hDU
  have hp : ContDiffOn ℝ ∞ (T.pW ρ e) D := (T.contDiffOn_pW hρ e).mono hDd
  have hA : ∀ j i' i, ContDiffOn ℝ ∞ (fun z => sysA (n := n) j z i' i) D := by
    intro j i' i; simp only [sysA, of_apply]; exact contDiffOn_const
  have hA' : ∀ j i' i, ContDiffOn ℝ ∞ (fun z => sysA' T.omega T.r j z i' i) D := by
    intro j i' i
    induction i' using Fin.lastCases with
    | last => simp only [sysA', of_apply, Fin.lastCases_last]; exact contDiffOn_const
    | cast q =>
      simp only [sysA', of_apply, Fin.lastCases_castSucc]
      refine ContDiffOn.sub ?_ ?_
      · split_ifs
        · exact hσ _ _
        · exact contDiffOn_const
      · split_ifs
        · exact hσ _ _
        · exact contDiffOn_const
  have hB : ∀ i' i, ContDiffOn ℝ ∞ (fun z => sysB T.omega T.r (T.pW ρ e) z i' i) D := by
    intro i' i
    induction i' using Fin.lastCases with
    | last =>
      simp only [sysB, of_apply, Fin.lastCases_last]
      exact contDiffOn_dDir hD (contDiffOn_ofReal' hp) _
    | cast q =>
      simp only [sysB, of_apply, Fin.lastCases_castSucc]
      exact (contDiffOn_dbarDir hD (hσ _ _) _).sub (contDiffOn_dbarDir hD (hσ _ _) _)
  -- the data of the weak equation
  have hζC : Continuous fun z => (ζ z : ℂ) := Complex.continuous_ofReal.comp hζ.continuous
  have hζcs : HasCompactSupport fun z => (ζ z : ℂ) := hζc.comp_left Complex.ofReal_zero
  have hζts : tsupport (fun z => (ζ z : ℂ)) ⊆ T.dom e :=
    (tsupport_comp_subset Complex.ofReal_zero ζ).trans hζd
  have hζc' : ContDiff ℝ ∞ (fun y => (ζ y : ℂ)) := Complex.ofRealCLM.contDiff.comp hζ
  have hwL : ∀ i, MemLp (T.wsys ρ e ζ v i) 2 volume := by
    intro i
    have h1 : T.wsys ρ e ζ v i = fun z => T.We ρ e v z i * (ζ z : ℂ) := by
      funext z; simp only [wsys]; ring
    rw [h1]
    exact memLp_We_mul hρ v hζC hζcs hζts i
  have hw0 : ∀ i, ∀ z ∉ tsupport ζ, T.wsys ρ e ζ v i z = 0 := fun i z hz => by
    simp [wsys, image_eq_zero_of_notMem_tsupport hz]
  have hdζ : ∀ l, Continuous (dDir (coordVec l) fun y => (ζ y : ℂ)) := fun l =>
    (contDiff_dDir (k := 0) (hζc'.of_le (by norm_num))).continuous
  have hdζs : ∀ l, HasCompactSupport (dDir (coordVec l) fun y => (ζ y : ℂ)) ∧
      tsupport (dDir (coordVec l) fun y => (ζ y : ℂ)) ⊆ T.dom e := fun l =>
    ⟨hζcs.mono' (subset_closure.trans (tsupport_dDir_subset' _ _)),
      (tsupport_dDir_subset' _ _).trans hζts⟩
  have hdbζ : ∀ l, Continuous (dbarDir (coordVec l) fun y => (ζ y : ℂ)) := fun l =>
    continuous_dbarDir' (hζc'.of_le (by simp))
  have hcS : ∀ (a i b : Fin n), Continuous fun z => dbarDir (coordVec a) (fun y => (ζ y : ℂ)) z *
      sigmaMat T.omega T.r z i b := fun a i b => by
    have := continuous_mul_of_continuousOn hO
      ((contDiffOn_sigmaMat T.isOpen_U T.kahler i b).continuousOn.mono (dom_subset_U e)) (hdbζ a)
      ((tsupport_dbarDir_subset _ _).trans hζts)
    exact this.congr fun z => mul_comm _ _
  have hcSs : ∀ (a i b : Fin n), HasCompactSupport (fun z => dbarDir (coordVec a)
      (fun y => (ζ y : ℂ)) z * sigmaMat T.omega T.r z i b) ∧ tsupport (fun z => dbarDir (coordVec a)
        (fun y => (ζ y : ℂ)) z * sigmaMat T.omega T.r z i b) ⊆ T.dom e := fun a i b =>
    ⟨(hasCompactSupport_dbarDir hζcs).mul_right,
      (tsupport_mul_subset_left.trans (tsupport_dbarDir_subset _ _)).trans hζts⟩
  have hfL : ∀ i', MemLp (T.fsys ρ F e ζ v i') 2 volume := by
    intro i'
    induction i' using Fin.lastCases with
    | last =>
      simp only [fsys, Fin.lastCases_last]
      refine MemLp.sub ?_ (memLp_finsetSum _ fun l _ => ?_)
      · have hθ : ContinuousOn (chartTheta (T.pW ρ e) (T.tot F.s F.e F.h e)) (T.dom e) :=
          continuousOn_chartTheta' hO (T.contDiffOn_pW hρ e)
            ((T.contDiffOn_tot F.spec e).mono fun z hz => ((T.mem_dom).mp hz).1)
        have hc := continuous_mul_of_continuousOn hO hθ hζC hζts
        have h1 : (fun z => (ζ z : ℂ) * chartTheta (T.pW ρ e) (T.tot F.s F.e F.h e) z) =
            fun z => chartTheta (T.pW ρ e) (T.tot F.s F.e F.h e) z * (ζ z : ℂ) :=
          funext fun z => mul_comm _ _
        rw [h1]
        exact hc.memLp_of_hasCompactSupport hζcs.mul_left
      · have h1 : (fun z => dDir (coordVec l) (fun y => (ζ y : ℂ)) z * T.We ρ e v z l) =
            fun z => T.We ρ e v z l * dDir (coordVec l) (fun y => (ζ y : ℂ)) z := by
          funext z; ring
        rw [h1]
        exact memLp_We_mul hρ v (hdζ l) (hdζs l).1 (hdζs l).2 l
    | cast q =>
      simp only [fsys, Fin.lastCases_castSucc]
      have h3 : T.fS ρ e ζ v (rowJK q).1 (rowJK q).2 = fun z => ∑ i, (T.We ρ e v z i *
          (dbarDir (coordVec (rowJK q).1) (fun y => (ζ y : ℂ)) z * sigmaMat T.omega T.r z i
            (rowJK q).2) - T.We ρ e v z i * (dbarDir (coordVec (rowJK q).2) (fun y => (ζ y : ℂ)) z *
              sigmaMat T.omega T.r z i (rowJK q).1)) := by
        funext z
        simp only [fS, mv_sT_apply, Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
      rw [h3]
      exact memLp_finsetSum _ fun i _ =>
        (memLp_We_mul hρ v (hcS (rowJK q).1 i (rowJK q).2) (hcSs (rowJK q).1 i (rowJK q).2).1
          (hcSs (rowJK q).1 i (rowJK q).2).2 i).sub
          (memLp_We_mul hρ v (hcS (rowJK q).2 i (rowJK q).1) (hcSs (rowJK q).2 i (rowJK q).1).1
            (hcSs (rowJK q).2 i (rowJK q).1).2 i)
  have hweak : ∀ h : Fin (n * n + 1) → ComplexModel n → ℂ, (∀ i', IsTestFunctionOn D (h i')) →
      ∑ i', ∫ z, T.fsys ρ F e ζ v i' z * conj (h i' z) =
        ∑ i, ∫ z, T.wsys ρ e ζ v i z * conj (firstOrderAdjointApply (sysA (n := n))
          (sysA' T.omega T.r) (sysB T.omega T.r (T.pW ρ e)) h i z) :=
    fun h hh => weak_eq hρ F v hW1 hW2 hζ hDd h hh
  obtain ⟨ws, hws, hc1, hc2⟩ := friedrichsStatement n n (n * n + 1) D hD (sysA (n := n))
    (sysA' T.omega T.r) (sysB T.omega T.r (T.pW ρ e)) hA hA' hB (tsupport ζ) hζc hζD
    (T.wsys ρ e ζ v) (T.fsys ρ F e ζ v) hwL hw0 hfL hweak
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
  refine ⟨fun m => ofComps (ws m), fun m => ⟨?_, ?_, (hsD m).trans hDd⟩, hsD, ?_, ?_, ?_,
    by simpa [fsys] using hfL (Fin.last _), fun j k => ?_⟩
  rotate_right
  · have hq : rowJK (finProdFinEquiv (j, k)) = (j, k) := by simp [rowJK]
    have := hfL (Fin.castSucc (finProdFinEquiv (j, k)))
    simp only [fsys, Fin.lastCases_castSucc, hq] at this
    exact this
  · have h1 : ContDiff ℝ ∞ (fun z => fun i => ws m i z) := contDiff_pi.mpr fun i => (hws m i).1
    exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℂ)).symm.contDiff.comp h1
  · exact IsCompact.of_isClosed_subset (isCompact_iUnion fun i => (hws m i).2.1)
      (isClosed_tsupport _) (hsub m)
  · refine tendsto_eLpNorm_sum Finset.univ (G := fun i m z => ws m i z - T.wsys ρ e ζ v i z)
      (fun i m => (hws m i).1.continuous.aestronglyMeasurable.sub (hwL i).1)
      (fun m z => ?_) fun i _ => hc1 i
    refine (norm_le_sum_norm_coord _).trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
    simp [ofComps]
  · refine (hc2 (Fin.last _)).congr fun m => ?_
    congr 1
    funext z
    rw [firstOrderApply_last]
    simp [fsys]
  · intro j k
    set q : Fin (n * n) := finProdFinEquiv (j, k)
    have hq : rowJK q = (j, k) := by simp [rowJK, q]
    refine (hc2 q.castSucc).congr fun m => ?_
    refine eLpNorm_congr_ae ((ae_restrict_iff' hD.measurableSet).mpr
      (Eventually.of_forall fun z hz => ?_))
    simp only [fsys, Fin.lastCases_castSucc]
    rw [firstOrderApply_S T.omega T.r (T.pW ρ e) (ws m)
      (fun l k => differentiableAt_sigmaMat (hDU hz) l k)
      (fun i => (hws m i).1.differentiable (by simp) z) q, hq]


end TwistedDatum






end SGPT.Trace.TwistedL2
