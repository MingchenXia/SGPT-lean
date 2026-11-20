import SGPT.Okounkov.TranscendentalSkodaProjection
import SGPT.Foundations.Analysis.Pending.HormanderL2Theorem

/-!
# Skoda's theorem: the Hilbert spaces of the kernel-bundle estimate

Blueprint `claude-tok-skoda`, node `skoda:twisted-hormander` (setting of Steps 3--4).

On an open set `L` with Hörmander's three weights `w₃ = Φ + χ`, `w₂ = w₃ - ψ₀`, `w₁ = w₃ - 2ψ₀`
(`KernelL2Data`), the `ℂ^R`-valued `L²` spaces are the products
`H₂ = L²_{(0,1)}(L, e^{-w₂})^R` and `H₁ = L²(L, e^{-w₁})^R` (`PiLp 2` of TN's scalar spaces,
row by row). The test space is `V = (test forms)^R`, with the linear maps

* `aMap : V → H₂`, `α ↦ α`;
* `tMap : V → H₁`, `α ↦ T* α` (row by row, TN's `tstarToL2`);
* `AMap : V → H₁`, `α ↦ P_S T* α` (`sTstar`).

`kernelSubmodule G μ` is the closed subspace of kernel-valued elements (`∑ᵢ Gᵢ βᵢ = 0` a.e.),
closed because `L²` convergence has an a.e. convergent subsequence
(`isClosed_kernelSubmodule`). `W ⊆ H₂` is the closed subspace of kernel-valued forms with weakly
`∂̄`-closed rows.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Okounkov.TranscendentalSkoda

open Filter MeasureTheory Set SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.CauchyGreen SGPT.Foundations.Analysis.Pending.Hormander
open SGPT.Foundations.Analysis.Pending.Hormander.Density
open scoped Topology ComplexConjugate ContDiff ENNReal InnerProductSpace

variable {n R : ℕ}

/-! ### Convergence and integrability helpers -/

/-- Convergence in `L²` from a pointwise bound by finitely many functions converging to `0`. -/
theorem tendsto_eLpNorm_of_le_sum {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {V W : Type*} [NormedAddCommGroup V] [NormedAddCommGroup W] {ι : Type*} [Fintype ι]
    {F : ℕ → α → V} {f : ℕ → ι → α → W} {C : ℝ}
    (hf : ∀ m q, AEStronglyMeasurable (f m q) μ)
    (hle : ∀ m, ∀ᵐ x ∂μ, ‖F m x‖ ≤ C * ∑ q, ‖f m q x‖)
    (hf0 : ∀ q, Tendsto (fun m => eLpNorm (f m q) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun m => eLpNorm (F m) 2 μ) atTop (𝓝 0) := by
  have hsum : Tendsto (fun m => eLpNorm (fun x => ∑ q, ‖f m q x‖) 2 μ) atTop (𝓝 0) :=
    tendsto_eLpNorm_sum (f := fun m q x => ‖f m q x‖) (fun m q => (hf m q).norm) fun q => by
      simpa only [eLpNorm_norm] using hf0 q
  have hb : ∀ m, eLpNorm (F m) 2 μ ≤
      ENNReal.ofReal C * eLpNorm (fun x => ∑ q, ‖f m q x‖) 2 μ := fun m =>
    eLpNorm_le_mul_eLpNorm_of_ae_le_mul (by
      filter_upwards [hle m] with x hx
      rwa [Real.norm_of_nonneg (Finset.sum_nonneg fun q _ => norm_nonneg _)]) 2
  have hlim : Tendsto (fun m => ENNReal.ofReal C * eLpNorm (fun x => ∑ q, ‖f m q x‖) 2 μ)
      atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul hsum (Or.inr ENNReal.ofReal_ne_top)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => zero_le) hb

theorem integrable_sq_mul_exp_of_memLp' {V : Type*} [NormedAddCommGroup V]
    {D : Set (ComplexModel n)} (hD : IsOpen D) {w : ComplexModel n → ℝ} (hw : ContinuousOn w D)
    {u : ComplexModel n → V} (hu : MemLp u 2 (weightedVolume D w)) :
    Integrable (fun x => ‖u x‖ ^ 2 * Real.exp (-w x)) (volume.restrict D) := by
  have h1 : Integrable (fun x => ‖u x‖ ^ 2) (weightedVolume D w) :=
    (memLp_two_iff_integrable_sq_norm hu.1).mp hu
  rw [weightedVolume_eq_withDensity_weightDensity hD, integrable_withDensity_iff
    (measurable_weightDensity hD hw) (Eventually.of_forall fun x => weightDensity_lt_top x)] at h1
  refine h1.congr ?_
  filter_upwards [ae_restrict_mem hD.measurableSet] with x hx
  simp [weightDensity, hx, (Real.exp_pos _).le]

/-- `f ∈ L²(e^{-w})` from `|f|² e^{-w} ≤ |b|² e^{-w'}` with `b ∈ L²(e^{-w'})`. -/
theorem memLp_weightedVolume_of_sq_le {D : Set (ComplexModel n)} (hD : IsOpen D)
    {w w' : ComplexModel n → ℝ} (hw : ContinuousOn w D) (hw' : ContinuousOn w' D)
    {V : Type*} [NormedAddCommGroup V] {f : ComplexModel n → ℂ} {b : ComplexModel n → V}
    (hf : AEStronglyMeasurable f (volume.restrict D)) (hb : MemLp b 2 (weightedVolume D w'))
    (hle : ∀ x ∈ D, ‖f x‖ ^ 2 * Real.exp (-w x) ≤ ‖b x‖ ^ 2 * Real.exp (-w' x)) :
    MemLp f 2 (weightedVolume D w) := by
  have hfm : AEStronglyMeasurable f (weightedVolume D w) :=
    (aestronglyMeasurable_weightedVolume_iff hD hw).mpr hf
  rw [memLp_two_iff_integrable_sq_norm hfm]
  have hbi := integrable_sq_mul_exp_of_memLp' hD hw' hb
  have h1 : Integrable (fun x => ‖f x‖ ^ 2 * Real.exp (-w x)) (volume.restrict D) := by
    refine hbi.mono' ((hf.norm.pow 2).mul
      ((Real.continuous_exp.comp_continuousOn hw.neg).aestronglyMeasurable hD.measurableSet)) ?_
    filter_upwards [ae_restrict_mem hD.measurableSet] with x hx
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)]
    exact hle x hx
  rw [weightedVolume_eq_withDensity_weightDensity hD, integrable_withDensity_iff
    (measurable_weightDensity hD hw) (Eventually.of_forall fun x => weightDensity_lt_top x)]
  refine h1.congr ?_
  filter_upwards [ae_restrict_mem hD.measurableSet] with x hx
  simp [weightDensity, hx, (Real.exp_pos _).le]

theorem memLp_conj' {μ : Measure (ComplexModel n)} {f : ComplexModel n → ℂ} (hf : MemLp f 2 μ) :
    MemLp (fun x => conj (f x)) 2 μ :=
  (Complex.conjCLE.toContinuousLinearMap).comp_memLp' hf

theorem integrable_conj_mul {μ : Measure (ComplexModel n)} {f g : ComplexModel n → ℂ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) : Integrable (fun x => conj (f x) * g x) μ :=
  integrable_mul_of_memLp_two (memLp_conj' hf) hg

/-! ### Kernel-valued elements -/

section KernelSubmodule

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The kernel-valued elements of `L²(μ; E)^R`: `∑ᵢ Gᵢ βᵢ = 0` almost everywhere. -/
def kernelSubmodule (G : Fin R → ComplexModel n → ℂ) (μ : Measure (ComplexModel n)) :
    Submodule ℂ (PiLp 2 fun _ : Fin R => Lp E 2 μ) where
  carrier := {β | ∀ᵐ x ∂μ, ∑ i, G i x • (β i : ComplexModel n → E) x = 0}
  add_mem' {β β'} hβ hβ' := by
    have h := ae_all_iff.mpr fun i => Lp.coeFn_add (β i) (β' i)
    filter_upwards [hβ, hβ', h] with x h1 h2 h3
    simp only [PiLp.add_apply, h3, Pi.add_apply, smul_add, Finset.sum_add_distrib, h1, h2,
      add_zero]
  zero_mem' := by
    filter_upwards [Lp.coeFn_zero E 2 μ] with x hx
    simp only [WithLp.ofLp_zero, Pi.zero_apply, hx, smul_zero, Finset.sum_const_zero]
  smul_mem' c β hβ := by
    have h := ae_all_iff.mpr fun i => Lp.coeFn_smul c (β i)
    filter_upwards [hβ, h] with x h1 h2
    simp only [PiLp.smul_apply, h2, Pi.smul_apply]
    rw [show ∑ i, G i x • c • (β i : ComplexModel n → E) x = c • ∑ i, G i x • (β i) x by
      rw [Finset.smul_sum]; exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _, h1, smul_zero]

theorem mem_kernelSubmodule_iff (G : Fin R → ComplexModel n → ℂ) {μ : Measure (ComplexModel n)}
    (β : PiLp 2 fun _ : Fin R => Lp E 2 μ) :
    β ∈ kernelSubmodule G μ ↔ ∀ᵐ x ∂μ, ∑ i, G i x • (β i : ComplexModel n → E) x = 0 :=
  Iff.rfl

/-- The kernel-valued elements form a closed subspace. -/
theorem isClosed_kernelSubmodule (G : Fin R → ComplexModel n → ℂ) (μ : Measure (ComplexModel n)) :
    IsClosed (kernelSubmodule (E := E) G μ : Set (PiLp 2 fun _ : Fin R => Lp E 2 μ)) := by
  refine isClosed_of_closure_subset fun β hβ => ?_
  obtain ⟨b, hb, hlim⟩ := mem_closure_iff_seq_limit.mp hβ
  have hcomp : ∀ i, Tendsto (fun m => eLpNorm (⇑(b m i) - ⇑(β i)) 2 μ) atTop (𝓝 0) := fun i =>
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).mp
      (((PiLp.proj 2 (𝕜 := ℂ) (fun _ : Fin R => Lp E 2 μ) i).continuous.tendsto β).comp hlim)
  set F : ℕ → ComplexModel n → ℝ := fun m x => ∑ i, ‖(b m i : ComplexModel n → E) x - β i x‖
    with hF
  have hFm : ∀ m, AEStronglyMeasurable (F m) μ := fun m =>
    Finset.aestronglyMeasurable_fun_sum _ fun i _ =>
      ((Lp.aestronglyMeasurable _).sub (Lp.aestronglyMeasurable _)).norm
  have hF0 : Tendsto (fun m => eLpNorm (F m - 0) 2 μ) atTop (𝓝 0) := by
    simp only [sub_zero]
    refine tendsto_eLpNorm_of_le_sum (C := 1)
      (f := fun m i x => (b m i : ComplexModel n → E) x - β i x)
      (fun m i => (Lp.aestronglyMeasurable _).sub (Lp.aestronglyMeasurable _))
      (fun m => Eventually.of_forall fun x => ?_) fun i => ?_
    · rw [one_mul, hF, Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)]
    · simpa only [Pi.sub_def] using hcomp i
  obtain ⟨ns, -, hae⟩ := (tendstoInMeasure_of_tendsto_eLpNorm two_ne_zero hFm
    aestronglyMeasurable_const hF0).exists_seq_tendsto_ae
  have hall : ∀ᵐ x ∂μ, ∀ m, ∑ i, G i x • (b m i : ComplexModel n → E) x = 0 :=
    ae_all_iff.mpr fun m => hb m
  change ∀ᵐ x ∂μ, ∑ i, G i x • (β i : ComplexModel n → E) x = 0
  filter_upwards [hae, hall] with x hx hxm
  have hi : ∀ i, Tendsto (fun k => (b (ns k) i : ComplexModel n → E) x) atTop (𝓝 (β i x)) := by
    intro i
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hx' : Tendsto (fun k => F (ns k) x) atTop (𝓝 0) := hx
    refine squeeze_zero (fun k => norm_nonneg _) (fun k => ?_) hx'
    exact Finset.single_le_sum (f := fun i => ‖(b (ns k) i : ComplexModel n → E) x - β i x‖)
      (fun i _ => norm_nonneg _) (Finset.mem_univ i)
  have hconv := tendsto_finsetSum Finset.univ fun i _ => (hi i).const_smul (G i x)
  simp only [hxm] at hconv
  exact (tendsto_nhds_unique tendsto_const_nhds hconv).symm

end KernelSubmodule

/-! ### The data of the estimate -/

/-- The data of the kernel-bundle `L²` estimate on an open set `L`: Hörmander's weights
`Φ, χ, ψ₀` and cutoffs `η` (as produced by TN's `exists_hormanderCutoffData`), and a tuple `G`
holomorphic without common zeros on `L`, with bounds on `L` for `G`, `∂G`, `ρ = Ḡ/|G|²` and
`∂̄ρ`. -/
structure KernelL2Data (n R : ℕ) where
  L : Set (ComplexModel n)
  Φ : ComplexModel n → ℝ
  χ : ComplexModel n → ℝ
  ψ₀ : ComplexModel n → ℝ
  η : ℕ → ComplexModel n → ℝ
  G : Fin R → ComplexModel n → ℂ
  isOpen : IsOpen L
  Φ_smooth : ContDiffOn ℝ ∞ Φ L
  χ_smooth : ContDiffOn ℝ ∞ χ L
  ψ_smooth : ContDiffOn ℝ ∞ ψ₀ L
  ψ_nonneg : ∀ x, 0 ≤ ψ₀ x
  η_test : ∀ k, ContDiff ℝ ∞ (η k) ∧ HasCompactSupport (η k) ∧ tsupport (η k) ⊆ L ∧
    ∀ x, 0 ≤ η k x ∧ η k x ≤ 1
  η_ev : ∀ x ∈ L, ∀ᶠ k in atTop, η k =ᶠ[𝓝 x] fun _ => 1
  η_grad : ∀ k, ∀ x ∈ L, ‖fderiv ℝ (η k) x‖ ^ 2 ≤ Real.exp (ψ₀ x)
  G_holo : ∀ i, DifferentiableOn ℂ (G i) L
  pos : ∀ z ∈ L, 0 < generatorNormSq G z
  CG : ℝ
  G_bound : ∀ x ∈ L, ∀ i, ‖G i x‖ ≤ CG
  CdG : ℝ
  dG_bound : ∀ x ∈ L, ∀ i j, ‖dDir (coordVec j) (G i) x‖ ≤ CdG
  Cρ : ℝ
  ρ_bound : ∀ x ∈ L, ∀ i, ‖normalDir G i x‖ ≤ Cρ
  Cdρ : ℝ
  dρ_bound : ∀ x ∈ L, ∀ i j, ‖dbarDir (coordVec j) (normalDir G i) x‖ ≤ Cdρ

namespace KernelL2Data

variable (d : KernelL2Data n R)

/-- `w₃ = Φ + χ`. -/
abbrev w₃ : ComplexModel n → ℝ := fun x => d.Φ x + d.χ x
/-- `w₂ = w₃ - ψ₀`. -/
abbrev w₂ : ComplexModel n → ℝ := fun x => d.w₃ x - d.ψ₀ x
/-- `w₁ = w₃ - 2ψ₀`. -/
abbrev w₁ : ComplexModel n → ℝ := fun x => d.w₃ x - 2 * d.ψ₀ x
/-- `e^{-w₃} dλ|_L`. -/
abbrev μ₃ : Measure (ComplexModel n) := weightedVolume d.L d.w₃
/-- `e^{-w₂} dλ|_L`. -/
abbrev μ₂ : Measure (ComplexModel n) := weightedVolume d.L d.w₂
/-- `e^{-w₁} dλ|_L`. -/
abbrev μ₁ : Measure (ComplexModel n) := weightedVolume d.L d.w₁
/-- `H₂ = L²_{(0,1)}(L, e^{-w₂})^R`. -/
abbrev H₂ : Type := PiLp 2 fun _ : Fin R => Lp (EuclideanSpace ℂ (Fin n)) 2 d.μ₂
/-- `H₁ = L²(L, e^{-w₁})^R`. -/
abbrev H₁ : Type := PiLp 2 fun _ : Fin R => Lp ℂ 2 d.μ₁

theorem w₃_smooth : ContDiffOn ℝ ∞ d.w₃ d.L := d.Φ_smooth.add d.χ_smooth
theorem w₂_smooth : ContDiffOn ℝ ∞ d.w₂ d.L := d.w₃_smooth.sub d.ψ_smooth
theorem w₃_cont : ContinuousOn d.w₃ d.L := d.w₃_smooth.continuousOn
theorem w₂_cont : ContinuousOn d.w₂ d.L := d.w₂_smooth.continuousOn
theorem w₁_cont : ContinuousOn d.w₁ d.L :=
  d.w₃_cont.sub (continuousOn_const.mul d.ψ_smooth.continuousOn)
theorem h12 : ∀ x ∈ d.L, d.w₂ x = d.w₁ x + d.ψ₀ x := fun x _ => by simp only [w₂, w₁]; ring

theorem μ₃_le_μ₂ : d.μ₃ ≤ d.μ₂ := by
  refine withDensity_mono (Eventually.of_forall fun x => ?_)
  refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
  simp only [w₂]
  linarith [d.ψ_nonneg x]

theorem aesm_of_continuousOn {w : ComplexModel n → ℝ} {V : Type*} [TopologicalSpace V]
    [TopologicalSpace.PseudoMetrizableSpace V] {f : ComplexModel n → V}
    (hf : ContinuousOn f d.L) : AEStronglyMeasurable f (weightedVolume d.L w) :=
  (hf.aestronglyMeasurable d.isOpen.measurableSet).mono_ac (withDensity_absolutelyContinuous _ _)

theorem aesm_kernelProj {w : ComplexModel n → ℝ} {b : Fin R → ComplexModel n → ℂ}
    (hb : ∀ k, AEStronglyMeasurable (b k) (weightedVolume d.L w)) (i : Fin R) :
    AEStronglyMeasurable (fun x => kernelProj d.G x (fun k => b k x) i)
      (weightedVolume d.L w) := by
  have e : (fun x => kernelProj d.G x (fun k => b k x) i) =
      fun x => b i x - normalDir d.G i x * ∑ k, d.G k x * b k x :=
    funext fun x => kernelProj_eq _ _ _ _
  rw [e]
  exact (hb i).sub ((d.aesm_of_continuousOn
    (contDiffOn_normalDir d.isOpen d.G_holo d.pos i).continuousOn).mul
      (Finset.aestronglyMeasurable_fun_sum _ fun k _ =>
        (d.aesm_of_continuousOn (d.G_holo k).continuousOn).mul (hb k)))

/-! ### The linear maps -/

/-- `α ↦ α ∈ H₂`. -/
def aMap : (Fin R → testForms d.L) →ₗ[ℂ] d.H₂ where
  toFun α := WithLp.toLp 2 fun i => formToL2 d.isOpen d.w₂_cont (α i)
  map_add' α β := PiLp.ext fun i => by simp
  map_smul' c α := PiLp.ext fun i => by simp

theorem aMap_apply (α : Fin R → testForms d.L) (i : Fin R) :
    d.aMap α i = formToL2 d.isOpen d.w₂_cont (α i) := rfl

/-- `α ↦ T* α ∈ H₁`, row by row. -/
def tMap : (Fin R → testForms d.L) →ₗ[ℂ] d.H₁ where
  toFun α := WithLp.toLp 2 fun i =>
    tstarToL2 d.isOpen d.w₁_cont d.w₂_smooth d.ψ_smooth.continuousOn (α i)
  map_add' α β := PiLp.ext fun i => by simp
  map_smul' c α := PiLp.ext fun i => by simp

theorem tMap_apply (α : Fin R → testForms d.L) (i : Fin R) :
    d.tMap α i = tstarToL2 d.isOpen d.w₁_cont d.w₂_smooth d.ψ_smooth.continuousOn (α i) := rfl

/-- `P_S T* α`, row `i`. -/
def sTstar (α : Fin R → testForms d.L) (i : Fin R) (x : ComplexModel n) : ℂ :=
  kernelProj d.G x (fun k => tstarForm d.w₂ d.ψ₀ (α k : Fin n → ComplexModel n → ℂ) x) i

theorem memLp_tstar (α : Fin R → testForms d.L) (k : Fin R) :
    MemLp (tstarForm d.w₂ d.ψ₀ (α k : Fin n → ComplexModel n → ℂ)) 2 d.μ₁ :=
  memLp_tstarForm d.isOpen d.w₁_cont d.w₂_smooth d.ψ_smooth.continuousOn (α k).2

theorem memLp_sTstar (α : Fin R → testForms d.L) (i : Fin R) : MemLp (d.sTstar α i) 2 d.μ₁ := by
  have hsum : MemLp (fun x => ∑ k, ‖tstarForm d.w₂ d.ψ₀ (α k : Fin n → ComplexModel n → ℂ) x‖)
      2 d.μ₁ := memLp_finsetSum _ fun k _ => (d.memLp_tstar α k).norm
  refine hsum.of_le_mul (c := 2) (d.aesm_kernelProj (fun k => (d.memLp_tstar α k).1) i)
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)]
  exact norm_kernelProj_le _ _ _ _

/-- `α ↦ P_S T* α ∈ H₁`. -/
def AMap : (Fin R → testForms d.L) →ₗ[ℂ] d.H₁ where
  toFun α := WithLp.toLp 2 fun i => (d.memLp_sTstar α i).toLp _
  map_add' α β := PiLp.ext fun i => by
    simp only [PiLp.add_apply]
    rw [← MemLp.toLp_add]
    refine MemLp.toLp_congr _ _ (Eventually.of_forall fun x => ?_)
    simp only [sTstar, Pi.add_apply, Submodule.coe_add]
    rw [← kernelProj_add]
    congr 1
    funext k
    exact tstarForm_add (α k).2 (β k).2 x
  map_smul' c α := PiLp.ext fun i => by
    simp only [PiLp.smul_apply, RingHom.id_apply]
    rw [← MemLp.toLp_const_smul]
    refine MemLp.toLp_congr _ _ (Eventually.of_forall fun x => ?_)
    simp only [sTstar, Pi.smul_apply, Submodule.coe_smul, smul_eq_mul]
    rw [← kernelProj_smul]
    congr 1
    funext k
    exact tstarForm_smul (α k).2 c x

theorem AMap_apply (α : Fin R → testForms d.L) (i : Fin R) :
    d.AMap α i = (d.memLp_sTstar α i).toLp _ := rfl

/-! ### The closed subspace `W` -/

/-- Forms in `H₂` whose rows are weakly `∂̄`-closed. -/
def Wcl : Submodule ℂ d.H₂ where
  carrier := {β | ∀ i, β i ∈ closedForms d.isOpen d.w₂_smooth}
  add_mem' hβ hβ' i := by rw [PiLp.add_apply]; exact add_mem (hβ i) (hβ' i)
  zero_mem' i := by rw [WithLp.ofLp_zero, Pi.zero_apply]; exact zero_mem _
  smul_mem' c β hβ i := by rw [PiLp.smul_apply]; exact Submodule.smul_mem _ c (hβ i)

theorem isClosed_Wcl : IsClosed (d.Wcl : Set d.H₂) := by
  have e : (d.Wcl : Set d.H₂) =
      ⋂ i, (PiLp.proj 2 (𝕜 := ℂ) (fun _ : Fin R => Lp (EuclideanSpace ℂ (Fin n)) 2 d.μ₂) i) ⁻¹'
        (closedForms d.isOpen d.w₂_smooth : Set _) := by
    ext β; simp [Wcl]
  rw [e]
  exact isClosed_iInter fun i => (Submodule.isClosed_orthogonal _).preimage
    (PiLp.proj 2 (𝕜 := ℂ) _ i).continuous

/-- `W`: kernel-valued forms in `H₂` with weakly `∂̄`-closed rows. -/
def W : Submodule ℂ d.H₂ := kernelSubmodule d.G d.μ₂ ⊓ d.Wcl

theorem isClosed_W : IsClosed (d.W : Set d.H₂) :=
  (isClosed_kernelSubmodule d.G d.μ₂).inter d.isClosed_Wcl

instance completeSpace_W : CompleteSpace d.W := d.isClosed_W.completeSpace_coe

instance hasOrthogonalProjection_W : d.W.HasOrthogonalProjection :=
  Submodule.HasOrthogonalProjection.ofCompleteSpace d.W

end KernelL2Data

end SGPT.Okounkov.TranscendentalSkoda
