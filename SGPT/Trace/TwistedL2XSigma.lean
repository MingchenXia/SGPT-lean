import SGPT.Trace.TwistedL2XApriori

/-!
# The complete Kähler form `σ` on a manifold and the `∂̄`-defect

Blueprint `claude-tl2-man.tex` (lane TL2-MAN, `claude-tl2-man:sigma`, `claude-tl2-man:defect`).

* `sigmaQX`, `sigmaSX`, `sigmaMatX`, `gX`: the quadratic form, the sesquilinear form and the matrix of
  `σ = ω + ddᶜ r` in an atlas chart `c`; near every point of `U` it is the Levi form of a local
  potential (`exists_sigma_potentialX`), `gX = σᵀ` is positive definite (`posDef_gX`).
* Chart invariance: `sigmaQX_chg` (from the transformation law of `ω` and `leviForm_comp`), hence
  `gX c z = Dψᴴ gX c' (ψ z) Dψ` (`gX_chg`).
* `kahlerAntisym_zeroTwoPair_transport`: the `σ`-norm of the `(0,2)`-form `(gA)ᵀ - gA` is invariant
  (no second derivatives of the coordinate change are needed: `A` transforms tensorially by
  `Amat_transport`).
* `FSX`: the `S`-form `|(gA_W)ᵀ - gA_W|²_σ |e|² e^{-φ}` (which equals `|∂̄(σ^♭W)|²_σ |e|² e^{-φ}` by Kähler
  lowering) is a gauge form; the defect bound `Q(τ) ≤ (sup a) · ‖S τ‖²`
  (`XFam.defect_le`) and the reduction `twistedL2CorrectionStatement_of_sigmaGraphDensityX`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.Trace.TwistedL2

open Set Filter MeasureTheory Matrix
open scoped Topology ContDiff ComplexConjugate Manifold ComplexOrder
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.Pending.CauchyGreen SGPT.Foundations.Analysis.Pending.Hormander
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.CompactHolomorphicSectionsDraft
open HermitianHolomorphicLineBundle

variable {n : ℕ}

/-! ### The matrix identity -/

theorem map_conj_eq_conjTranspose_transpose (M : Matrix (Fin n) (Fin n) ℂ) :
    M.map conj = Mᴴᵀ := by
  ext i j; simp

/-- **Invariance of the `σ`-norm of `(gA)ᵀ - gA`** under `g = Mᴴ g' M`, `A' M̄ = t M A`. -/
theorem kahlerAntisym_zeroTwoPair_transport {M g g' Au Au' Aw Aw' : Matrix (Fin n) (Fin n) ℂ}
    {t : ℂ} (hM : IsUnit M.det) (hg : IsUnit g.det) (hgg : g = Mᴴ * g' * M)
    (hu : Au' * M.map conj = t • (M * Au)) (hw : Aw' * M.map conj = t • (M * Aw)) :
    zeroTwoPair g'⁻¹ (kahlerAntisym g' Au') (kahlerAntisym g' Aw') =
      (t * conj t) * zeroTwoPair g⁻¹ (kahlerAntisym g Au) (kahlerAntisym g Aw) := by
  set C := M.map conj with hC
  have hCdet : IsUnit C.det := by
    have h := RingHom.map_det (starRingEnd ℂ) M
    rw [RingHom.mapMatrix_apply] at h
    rw [hC, ← h]
    exact hM.map _
  set U := C⁻¹ with hU
  have hUC : U * C = 1 := nonsing_inv_mul C hCdet
  have hCU : C * U = 1 := mul_nonsing_inv C hCdet
  have hCt : C = Mᴴᵀ := map_conj_eq_conjTranspose_transpose M
  -- `Uᵀ Mᴴ = 1` and `Mᴴ Uᵀ = 1`
  have h1 : Uᵀ * Mᴴ = 1 := by
    have := congrArg transpose hCU
    rwa [transpose_mul, hCt, transpose_transpose, transpose_one] at this
  have h1' : Mᴴ * Uᵀ = 1 := by
    have := congrArg transpose hUC
    rwa [transpose_mul, hCt, transpose_transpose, transpose_one] at this
  -- `conj U · M = 1` and `M · conj U = 1`, written with `Uᴴ`
  have h2 : Uᴴ * Mᵀ = 1 := by
    have := congrArg conjTranspose hCU
    rwa [conjTranspose_mul, hCt, conjTranspose_one, show (Mᴴᵀ)ᴴ = Mᵀ by ext; simp] at this
  have h2' : Mᵀ * Uᴴ = 1 := by
    have := congrArg conjTranspose hUC
    rwa [conjTranspose_mul, hCt, conjTranspose_one, show (Mᴴᵀ)ᴴ = Mᵀ by ext; simp] at this
  -- the transformed matrices
  have hAu : Au' = t • (M * Au * U) := by
    have := congrArg (· * U) hu
    simp only [Matrix.mul_assoc, hCU, Matrix.mul_one, Matrix.smul_mul] at this
    rw [this, Matrix.mul_assoc]
  have hAw : Aw' = t • (M * Aw * U) := by
    have := congrArg (· * U) hw
    simp only [Matrix.mul_assoc, hCU, Matrix.mul_one, Matrix.smul_mul] at this
    rw [this, Matrix.mul_assoc]
  have hg'M : g' * M = Uᵀ * g := by
    rw [hgg, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  have hK : ∀ A A' : Matrix (Fin n) (Fin n) ℂ, A' = t • (M * A * U) →
      kahlerAntisym g' A' = t • (Uᵀ * kahlerAntisym g A * U) := by
    intro A A' hA
    have hX : g' * A' = t • (Uᵀ * (g * A) * U) := by
      rw [hA, Matrix.mul_smul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hg'M, Matrix.mul_assoc Uᵀ g A]
    simp only [kahlerAntisym, hX, transpose_smul, transpose_mul, transpose_transpose,
      Matrix.mul_sub, Matrix.sub_mul, smul_sub, Matrix.mul_assoc]
  -- the inverse metric
  have hN : g'⁻¹ = M * g⁻¹ * Mᴴ := by
    refine inv_eq_left_inv ?_
    have hMinv : M * M⁻¹ = 1 := mul_nonsing_inv M hM
    calc M * g⁻¹ * Mᴴ * g' = M * g⁻¹ * Mᴴ * g' * (M * M⁻¹) := by rw [hMinv, Matrix.mul_one]
      _ = M * (g⁻¹ * (Mᴴ * g' * M)) * M⁻¹ := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [← hgg, nonsing_inv_mul g hg, Matrix.mul_one, hMinv]
  rw [hK Au Au' hAu, hK Aw Aw' hAw, hN]
  set β := kahlerAntisym g Au
  set γ := kahlerAntisym g Aw
  set N := g⁻¹
  have hUTC : (Uᵀ)ᴴ = Uᴴᵀ := by ext; simp
  have hP : (Uᵀ)ᴴ * M = 1 := by
    have := congrArg transpose h2'
    rwa [transpose_mul, transpose_transpose, transpose_one, ← hUTC] at this
  have hPM : ∀ X : Matrix (Fin n) (Fin n) ℂ, (Uᵀ)ᴴ * (M * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hP, Matrix.one_mul]
  have hMP : ∀ X : Matrix (Fin n) (Fin n) ℂ, Mᴴ * (Uᵀ * X) = X := fun X => by
    rw [← Matrix.mul_assoc, h1', Matrix.one_mul]
  have hUT : U * (M * (N * Mᴴ))ᵀ = Nᵀ * Mᵀ := by
    rw [transpose_mul, transpose_mul, ← hCt, ← Matrix.mul_assoc, ← Matrix.mul_assoc U C,
      hUC, Matrix.one_mul]
  have hprod : (t • (Uᵀ * β * U))ᴴ * (M * N * Mᴴ) * (t • (Uᵀ * γ * U)) * (M * N * Mᴴ)ᵀ =
      (star t * t) • (Uᴴ * (βᴴ * (N * (γ * (Nᵀ * Mᵀ))))) := by
    rw [conjTranspose_smul, conjTranspose_mul, conjTranspose_mul]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc, hPM, hMP, hUT]
    rw [mul_comm]
  have htr : trace (Uᴴ * (βᴴ * (N * (γ * (Nᵀ * Mᵀ))))) = trace (βᴴ * N * γ * Nᵀ) := by
    rw [trace_mul_comm]
    simp only [Matrix.mul_assoc, h2', Matrix.mul_one]
  simp only [zeroTwoPair]
  rw [hprod, trace_smul, htr, smul_eq_mul]
  simp only [RCLike.star_def]
  ring

/-! ### `σ` in a chart -/

theorem leviForm_congr_ev {F G : ComplexModel n → ℝ} {x : ComplexModel n} (h : F =ᶠ[𝓝 x] G)
    (v : ComplexModel n) : leviForm F x v = leviForm G x v := by
  simp only [leviForm, realHessian_eq_fderiv, h.fderiv.fderiv_eq]

variable {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

section Defs

variable (omega : KahlerBackground n X) (r : X → ℝ)

/-- The quadratic form of `σ = ω + ddᶜr` in the chart `c`. -/
def sigmaQX (c : ComplexChart n X) (z v : ComplexModel n) : ℝ := modifiedKahlerQuad omega r c z v

/-- The polarized sesquilinear form of `σ` in the chart `c`. -/
def sigmaSX (c : ComplexChart n X) (z u w : ComplexModel n) : ℂ :=
  ((sigmaQX omega r c z (u + w) : ℂ) - sigmaQX omega r c z (u - w) +
    Complex.I * sigmaQX omega r c z (u + Complex.I • w) -
    Complex.I * sigmaQX omega r c z (u - Complex.I • w)) / 4

/-- The Hermitian matrix `σ_{lk}` of `σ` in the chart `c`. -/
def sigmaMatX (c : ComplexChart n X) (z : ComplexModel n) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun l k => sigmaSX omega r c z (coordVec l) (coordVec k)

/-- `g = σᵀ` in the chart `c`. -/
def gX (c : ComplexChart n X) (z : ComplexModel n) : Matrix (Fin n) (Fin n) ℂ :=
  (sigmaMatX omega r c z)ᵀ

end Defs

variable {omega : KahlerBackground n X} {r : X → ℝ} {U : Set X}

/-- **Local potentials of `σ` in a chart.** -/
theorem exists_sigma_potentialX (hU : IsOpen U) (hr : IsKahlerModificationOn omega r U)
    (c : ComplexChart n X) {z : ComplexModel n} (hz : z ∈ c.val.target)
    (hzU : c.val.symm z ∈ U) :
    ∃ V : Set (ComplexModel n), ∃ R : ComplexModel n → ℝ, IsOpen V ∧ z ∈ V ∧
      V ⊆ c.val.target ∩ c.val.symm ⁻¹' U ∧ ContDiffOn ℝ ∞ R V ∧
      ∀ y ∈ V, ∀ v, sigmaQX omega r c y v = leviForm R y v := by
  obtain ⟨W, ρω, hzW, hW, -, hρ, heq⟩ :=
    SGPT.Foundations.Analysis.Pending.LocalPotentials.closedRealOneOne_hasLocalPotentials
      omega.form c z hz
  have hO : IsOpen (c.val.target ∩ c.val.symm ⁻¹' U) := c.val.isOpen_inter_preimage_symm hU
  have hrU : ContDiffOn ℝ ∞ (fun y => r (c.val.symm y)) (c.val.target ∩ c.val.symm ⁻¹' U) :=
    hr.1 c
  refine ⟨W ∩ (c.val.target ∩ c.val.symm ⁻¹' U),
    (1 / Real.pi) • (ρω + fun y => r (c.val.symm y)), hW.inter hO, ⟨hzW, hz, hzU⟩,
    inter_subset_right,
    ((hρ.mono inter_subset_left).add (hrU.mono inter_subset_right)).const_smul (1 / Real.pi), ?_⟩
  intro y hy v
  have h2 : (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := WithTop.coe_le_coe.mpr le_top
  have hρy : ContDiffAt ℝ 2 ρω y := ((hρ.contDiffAt (hW.mem_nhds hy.1))).of_le h2
  have hry : ContDiffAt ℝ 2 (fun y => r (c.val.symm y)) y :=
    ((hrU.contDiffAt (hO.mem_nhds hy.2))).of_le h2
  have hsum : ContDiffAt ℝ 2 (ρω + fun y => r (c.val.symm y)) y := hρy.add hry
  rw [leviForm_smul hsum, leviForm_add hρy hry]
  simp only [sigmaQX, modifiedKahlerQuad, kahlerQuad]
  rw [← heq hy.1, smoothDDC_complexDiagonal_eq_leviForm hρy]
  ring

theorem sigmaSX_eq_leviS {c : ComplexChart n X} {V : Set (ComplexModel n)}
    {R : ComplexModel n → ℝ} (hV : IsOpen V) (hR : ContDiffOn ℝ ∞ R V)
    (hσ : ∀ y ∈ V, ∀ v, sigmaQX omega r c y v = leviForm R y v) {y : ComplexModel n}
    (hy : y ∈ V) (u w : ComplexModel n) : sigmaSX omega r c y u w = leviS R y u w := by
  have hRy : ContDiffAt ℝ 2 R y :=
    (hR.contDiffAt (hV.mem_nhds hy)).of_le (WithTop.coe_le_coe.mpr le_top)
  rw [leviS_polar R y u w, sigmaSX]
  simp only [hσ y hy, leviS_self hRy]

theorem sigmaMatX_eq_hessian {c : ComplexChart n X} {V : Set (ComplexModel n)}
    {R : ComplexModel n → ℝ} (hV : IsOpen V) (hR : ContDiffOn ℝ ∞ R V)
    (hσ : ∀ y ∈ V, ∀ v, sigmaQX omega r c y v = leviForm R y v) {y : ComplexModel n}
    (hy : y ∈ V) (l k : Fin n) :
    sigmaMatX omega r c y l k = dbarDir (coordVec k) (dDir (coordVec l) fun x => (R x : ℂ)) y := by
  rw [sigmaMatX, of_apply, sigmaSX_eq_leviS hV hR hσ hy, leviS]
  simp [coordVec, Finset.sum_ite_eq']

theorem sum_sigmaMatX_mul {c : ComplexChart n X} {V : Set (ComplexModel n)}
    {R : ComplexModel n → ℝ} (hV : IsOpen V) (hR : ContDiffOn ℝ ∞ R V)
    (hσ : ∀ y ∈ V, ∀ v, sigmaQX omega r c y v = leviForm R y v) {y : ComplexModel n}
    (hy : y ∈ V) (u w : ComplexModel n) :
    ∑ l, ∑ k, sigmaMatX omega r c y l k * u l * conj (w k) = leviS R y u w := by
  simp only [sigmaMatX_eq_hessian hV hR hσ hy, leviS]

/-- **`gX = σᵀ` is positive definite** at the points of `U`. -/
theorem posDef_gX (hU : IsOpen U) (hr : IsKahlerModificationOn omega r U)
    {c : ComplexChart n X} {z : ComplexModel n} (hz : z ∈ c.val.target)
    (hzU : c.val.symm z ∈ U) : (gX omega r c z).PosDef := by
  obtain ⟨V, R, hV, hzV, -, hR, hσ⟩ := exists_sigma_potentialX hU hr c hz hzU
  have hRz : ContDiffAt ℝ 2 R z :=
    (hR.contDiffAt (hV.mem_nhds hzV)).of_le (WithTop.coe_le_coe.mpr le_top)
  have hquad : ∀ x : Fin n → ℂ, star x ⬝ᵥ (gX omega r c z *ᵥ x) =
      leviS R z (WithLp.toLp 2 x) (WithLp.toLp 2 x) := by
    intro x
    rw [← sum_sigmaMatX_mul hV hR hσ hzV]
    simp only [gX, dotProduct, mulVec, transpose_apply, Pi.star_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
    simp only [RCLike.star_def]
    ring
  refine PosDef.of_dotProduct_mulVec_pos ?_ fun x hx => ?_
  · ext l k
    simp only [gX, conjTranspose_apply, transpose_apply, RCLike.star_def]
    rw [sigmaMatX_eq_hessian hV hR hσ hzV, sigmaMatX_eq_hessian hV hR hσ hzV]
    have := conj_leviS_symm hRz (coordVec l) (coordVec k)
    simp only [leviS] at this
    simp [coordVec, Finset.sum_ite_eq'] at this
    exact this
  · rw [hquad, leviS_self hRz, ← hσ z hzV]
    have hv : (WithLp.toLp 2 x : ComplexModel n) ≠ 0 := by
      intro h0
      exact hx (by simpa using congrArg WithLp.ofLp h0)
    exact_mod_cast hr.2 c z hz hzU _ hv

theorem continuousOn_gX (hU : IsOpen U) (hr : IsKahlerModificationOn omega r U)
    (c : ComplexChart n X) :
    ContinuousOn (gX omega r c) (c.val.target ∩ c.val.symm ⁻¹' U) := by
  intro z hz
  obtain ⟨V, R, hV, hzV, -, hR, hσ⟩ := exists_sigma_potentialX hU hr c hz.1 hz.2
  have hRc : ContDiffOn ℝ ∞ (fun y => (R y : ℂ)) V := contDiffOn_ofReal' hR
  have hH : ContinuousOn (fun y => (Matrix.of fun l k : Fin n =>
      dbarDir (coordVec k) (dDir (coordVec l) fun x => (R x : ℂ)) y)ᵀ) V := by
    refine continuousOn_pi.mpr fun k => continuousOn_pi.mpr fun l => ?_
    exact (contDiffOn_dbarDir hV (contDiffOn_dDir hV hRc _) _).continuousOn
  refine ((hH.continuousAt (hV.mem_nhds hzV)).congr ?_).continuousWithinAt
  filter_upwards [hV.mem_nhds hzV] with y hy
  ext k l
  simp only [gX, transpose_apply, of_apply, sigmaMatX_eq_hessian hV hR hσ hy]

/-! ### Chart invariance of `σ` -/

theorem kahlerQuad_chg (omega : KahlerBackground n X) {c c' : ComplexChart n X}
    {z : ComplexModel n} (hz : z ∈ ovl c c') (v : ComplexModel n) :
    kahlerQuad omega c' (chg c c' z) (fderiv ℂ (chg c c') z v) = kahlerQuad omega c z v := by
  have h := omega.form.val.compatible c c' z (by rw [← ovl_eq_source]; exact hz)
    ![v, Complex.I • v]
  have hd : chartTransitionDerivative c c' z = (fderiv ℂ (chg c c') z).restrictScalars ℝ := by
    rw [chartTransitionDerivative, ← chg_eq]
    exact (differentiableAt_chg hz).fderiv_restrictScalars ℝ
  have hvec : (fun i => chartTransitionDerivative c c' z (![v, Complex.I • v] i)) =
      ![fderiv ℂ (chg c c') z v, Complex.I • fderiv ℂ (chg c c') z v] := by
    ext i : 1
    fin_cases i <;> simp [hd]
  have hpt : chartTransition c c' z = chg c c' z := (congrFun (chg_eq c c') z).symm
  simp only [kahlerQuad]
  rw [h, hvec, hpt]

theorem leviForm_r_chg (hU : IsOpen U) (hr : IsKahlerModificationOn omega r U)
    {c c' : ComplexChart n X} {z : ComplexModel n} (hz : z ∈ ovl c c')
    (hzU : c.val.symm z ∈ U) (v : ComplexModel n) :
    leviForm (fun y => r (c'.val.symm y)) (chg c c' z) (fderiv ℂ (chg c c') z v) =
      leviForm (fun y => r (c.val.symm y)) z v := by
  set S := ovl c c' ∩ c.val.symm ⁻¹' U
  have hS : IsOpen S := (c.val.continuousOn_symm.mono fun _ hy => hy.1).isOpen_inter_preimage
    (isOpen_ovl c c') hU
  have hV : IsOpen (c'.val.target ∩ c'.val.symm ⁻¹' U) := c'.val.isOpen_inter_preimage_symm hU
  have hF : ContDiffOn ℂ ∞ (chg c c') S :=
    contDiffOn_of_differentiableOn_complex ((differentiableOn_chg c c').mono fun _ hy => hy.1) hS
  have hmaps : MapsTo (chg c c') S (c'.val.target ∩ c'.val.symm ⁻¹' U) := fun y hy =>
    ⟨c'.val.map_source hy.1.2, by simp only [mem_preimage]; rw [symm_chg hy.1]; exact hy.2⟩
  have hcomp := SGPT.Foundations.Analysis.Pending.LeviFormHolomorphicComp.leviForm_comp hS hV hF
    (hr.1 c') hmaps ⟨hz, hzU⟩ v
  rw [(differentiableAt_chg hz).fderiv_restrictScalars ℝ] at hcomp
  change _ = leviForm (fun y => r (c'.val.symm y)) (chg c c' z) (fderiv ℂ (chg c c') z v) at hcomp
  rw [← hcomp]
  refine leviForm_congr_ev ?_ v
  filter_upwards [(isOpen_ovl c c').mem_nhds hz] with y hy
  simp only [symm_chg hy]

theorem sigmaQX_chg (hU : IsOpen U) (hr : IsKahlerModificationOn omega r U)
    {c c' : ComplexChart n X} {z : ComplexModel n} (hz : z ∈ ovl c c')
    (hzU : c.val.symm z ∈ U) (v : ComplexModel n) :
    sigmaQX omega r c' (chg c c' z) (fderiv ℂ (chg c c') z v) = sigmaQX omega r c z v := by
  simp only [sigmaQX, modifiedKahlerQuad, kahlerQuad_chg omega hz, leviForm_r_chg hU hr hz hzU]

theorem sigmaSX_chg (hU : IsOpen U) (hr : IsKahlerModificationOn omega r U)
    {c c' : ComplexChart n X} {z : ComplexModel n} (hz : z ∈ ovl c c')
    (hzU : c.val.symm z ∈ U) (u w : ComplexModel n) :
    sigmaSX omega r c' (chg c c' z) (fderiv ℂ (chg c c') z u) (fderiv ℂ (chg c c') z w) =
      sigmaSX omega r c z u w := by
  simp only [sigmaSX, ← map_add, ← map_sub, ← map_smul, sigmaQX_chg hU hr hz hzU]

/-- **The transformation of the matrix of `σ`**: `g_c = Dψᴴ g_{c'} Dψ`. -/
theorem gX_chg (hU : IsOpen U) (hr : IsKahlerModificationOn omega r U)
    {c c' : ComplexChart n X} {z : ComplexModel n} (hz : z ∈ ovl c c')
    (hzU : c.val.symm z ∈ U) :
    gX omega r c z = (linMat (fderiv ℂ (chg c c') z))ᴴ * gX omega r c' (chg c c' z) *
      linMat (fderiv ℂ (chg c c') z) := by
  have hzU' : c'.val.symm (chg c c' z) ∈ U := by rw [symm_chg hz]; exact hzU
  obtain ⟨V, R, hV, hzV, -, hR, hσ⟩ :=
    exists_sigma_potentialX hU hr c' (z := chg c c' z) (c'.val.map_source hz.2) hzU'
  ext l k
  simp only [gX, transpose_apply, sigmaMatX, of_apply]
  rw [← sigmaSX_chg hU hr hz hzU, sigmaSX_eq_leviS hV hR hσ hzV,
    ← sum_sigmaMatX_mul hV hR hσ hzV]
  simp only [mul_apply, conjTranspose_apply, transpose_apply, RCLike.star_def, linMat, of_apply,
    sigmaMatX, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

end SGPT.Trace.TwistedL2
