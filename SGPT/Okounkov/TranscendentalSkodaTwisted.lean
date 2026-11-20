import SGPT.Okounkov.TranscendentalSkodaApprox

/-!
# Skoda's theorem: the `L²` estimate in the kernel bundle

Blueprint `claude-tok-skoda`, node `skoda:twisted-hormander` (Step 4 and assembly):
`twistedHormanderStatement : TwistedHormanderStatement`.

For every test form `α`, `(α, v)_{w₂} = (P_S α, v)_{w₂}` (`v` is kernel-valued) and
`P_S T* α = P_S T*(P_S α)` (projection calculus), so the pairing bound for the kernel-valued test
form `P_S α` (`kernel_norm_sq_pairing_le`) gives
`|(α, v)|² ≤ (1 + t) I_g (‖P_S T* α‖² + ‖∂̄ (P_S α)‖²)` (`norm_sq_inner_le`). The approximation of
Step 3 (`exists_approx`) removes the `∂̄` term through TN's `norm_inner_le_of_approx'`, and
Hahn--Banach/Riesz (TN's `exists_solution_of_bound`) gives `u` in the closure of
`{P_S T* α}` with `‖u‖² ≤ (1 + t) I_g`. The closure is kernel-valued, so
`(P_S T* α, u) = (T* α, u)`, and testing with forms supported in one row gives `∂̄ uᵢ = vᵢ`.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Okounkov.TranscendentalSkoda

open Filter MeasureTheory Set SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.CauchyGreen SGPT.Foundations.Analysis.Pending.Hormander
open SGPT.Foundations.Analysis.Pending.Hormander.Density
open scoped Topology ComplexConjugate ContDiff ENNReal InnerProductSpace

variable {n R : ℕ}

namespace KernelL2Data

variable (d : KernelL2Data n R)

/-- The datum `v ∈ H₂`. -/
def vVec {v : Fin R → Fin n → ComplexModel n → ℂ} (hv : ∀ i j, MemLp (v i j) 2 d.μ₂) : d.H₂ :=
  WithLp.toLp 2 fun i => (memLp_formVec_of_components (hv i)).toLp (formVec (v i))

theorem inner_aMap_vVec {v : Fin R → Fin n → ComplexModel n → ℂ}
    (hv : ∀ i j, MemLp (v i j) 2 d.μ₂) (α : Fin R → testForms d.L) :
    ⟪d.aMap α, d.vVec hv⟫_ℂ =
      ∑ i, ∑ j, ∫ x, conj ((α i : Fin n → ComplexModel n → ℂ) j x) * v i j x ∂d.μ₂ := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show (d.aMap α).ofLp i = formToL2 d.isOpen d.w₂_cont (α i) from rfl, inner_formToL2]
  refine Finset.sum_congr rfl fun j _ => integral_congr_ae ?_
  filter_upwards [(memLp_formVec_of_components (hv i)).coeFn_toLp] with x hx
  rw [show (d.vVec hv).ofLp i = (memLp_formVec_of_components (hv i)).toLp (formVec (v i)) from
    rfl, hx, formVec_apply]

/-- The projection `P_S α` of a test form, as a test form. -/
def projV (α : Fin R → testForms d.L) : Fin R → testForms d.L := fun i =>
  ⟨kernelProjForm d.G (fun k => (α k : Fin n → ComplexModel n → ℂ)) i,
    kernelProjForm_mem d.isOpen d.G_holo d.pos (fun k => (α k).2) i⟩

theorem inner_aMap_projV {v : Fin R → Fin n → ComplexModel n → ℂ}
    (hv : ∀ i j, MemLp (v i j) 2 d.μ₂) (hvker : ∀ z ∈ d.L, InKernel d.G z fun i j => v i j z)
    (α : Fin R → testForms d.L) :
    ⟪d.aMap (d.projV α), d.vVec hv⟫_ℂ = ⟪d.aMap α, d.vVec hv⟫_ℂ := by
  rw [d.inner_aMap_vVec hv, d.inner_aMap_vVec hv]
  have hint : ∀ (β : Fin R → testForms d.L) i j,
      Integrable (fun x => conj ((β i : Fin n → ComplexModel n → ℂ) j x) * v i j x) d.μ₂ :=
    fun β i j => integrable_conj_mul (memLp_test d.isOpen d.w₂_cont ((β i).2 j)) (hv i j)
  rw [Finset.sum_comm, Finset.sum_comm (f := fun i j =>
    ∫ x, conj ((α i : Fin n → ComplexModel n → ℂ) j x) * v i j x ∂d.μ₂)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← integral_finsetSum _ fun i _ => hint _ i j, ← integral_finsetSum _ fun i _ => hint _ i j]
  refine integral_congr_ae ?_
  filter_upwards [d.ae_mem d.w₂] with x hx
  exact sum_conj_kernelProj_mul d.G x (hvker x hx j) _

theorem norm_sq_AMap (α : Fin R → testForms d.L) :
    ‖d.AMap α‖ ^ 2 = ∫ x, ∑ i, ‖d.sTstar α i x‖ ^ 2 ∂d.μ₁ := by
  rw [PiLp.norm_sq_eq_of_L2, integral_finsetSum _ fun i _ =>
    (memLp_two_iff_integrable_sq_norm (d.memLp_sTstar α i).1).mp (d.memLp_sTstar α i)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show (d.AMap α).ofLp i = (d.memLp_sTstar α i).toLp _ from rfl, norm_sq_toLp_eq_integral]

/-- `P_S T*(P_S α) = P_S T* α` (projection calculus). -/
theorem AMap_projV (α : Fin R → testForms d.L) : d.AMap (d.projV α) = d.AMap α := by
  refine PiLp.ext fun i => ?_
  refine MemLp.toLp_congr (d.memLp_sTstar _ i) (d.memLp_sTstar α i) ?_
  filter_upwards [d.ae_mem d.w₁] with x hx
  exact congrFun (kernelProj_tstarForm_kernelProjForm d.isOpen d.G_holo d.pos d.w₂ d.ψ₀
    (fun i j => isTestFunctionOn_contDiff_one ((α i).2 j)) hx) i

/-- **The a priori bound for every test form** (Steps 1--2 for `P_S α`). -/
theorem norm_sq_inner_le {t : ℝ} (ht : 0 < t)
    (hLevi : ∀ x ∈ d.L, ∀ ξ, (1 + 1 / t) * n * ‖fderiv ℝ d.ψ₀ x‖ ^ 2 * ‖ξ‖ ^ 2 ≤
      leviForm d.χ x ξ)
    (hcurv : ∀ z ∈ d.L, ∀ α : Fin R → Fin n → ℂ, InKernel d.G z α →
      (1 + t) * secondFundamental d.G z α ≤ vectorLevi d.Φ z α)
    {v : Fin R → Fin n → ComplexModel n → ℂ} (hv : ∀ i j, MemLp (v i j) 2 d.μ₂)
    (hvker : ∀ z ∈ d.L, InKernel d.G z fun i j => v i j z)
    {g : ComplexModel n → ℝ} (hg0 : ∀ x ∈ d.L, 0 ≤ g x)
    (hvg : ∀ z ∈ d.L, ∀ α : Fin R → Fin n → ℂ, InKernel d.G z α →
      ‖∑ i, ∑ j, conj (α i j) * v i j z‖ ^ 2 ≤
        g z * (vectorLevi d.Φ z α - (1 + t) * secondFundamental d.G z α))
    (hgi : Integrable (fun x => g x * Real.exp (-d.w₁ x)) (volume.restrict d.L))
    (α : Fin R → testForms d.L) :
    ‖⟪d.aMap α, d.vVec hv⟫_ℂ‖ ^ 2 ≤
      (1 + t) * (∫ x in d.L, g x * Real.exp (-d.w₁ x)) * (‖d.AMap α‖ ^ 2 + d.Qfun α) := by
  have key := kernel_norm_sq_pairing_le d.isOpen d.Φ_smooth d.χ_smooth d.ψ_smooth ht hLevi
    d.G_holo d.pos hcurv hv hg0 hvg hgi
    (α := fun i => kernelProjForm d.G (fun k => (α k : Fin n → ComplexModel n → ℂ)) i)
    (fun i => (d.projV α i).2) (fun x hx => inKernel_kernelProjForm d.G (d.pos x hx) _)
  rw [← d.inner_aMap_projV hv hvker, d.inner_aMap_vVec hv, ← d.AMap_projV α, d.norm_sq_AMap]
  exact key

theorem vVec_mem_W {v : Fin R → Fin n → ComplexModel n → ℂ} (hv : ∀ i j, MemLp (v i j) 2 d.μ₂)
    (hvker : ∀ z ∈ d.L, InKernel d.G z fun i j => v i j z)
    (hvc : ∀ i, WeakDbarClosed d.L (v i)) : d.vVec hv ∈ d.W := by
  refine ⟨?_, fun i => ?_⟩
  · rw [SetLike.mem_coe, mem_kernelSubmodule_iff]
    have hae := ae_all_iff.mpr fun i => (memLp_formVec_of_components (hv i)).coeFn_toLp
    filter_upwards [hae, d.ae_mem d.w₂] with x hx hxL
    have hx' : ∀ i, (d.vVec hv i : ComplexModel n → EuclideanSpace ℂ (Fin n)) x =
        formVec (v i) x := hx
    simp only [hx']
    refine PiLp.ext fun j => ?_
    simpa [formVec] using hvker x hxL j
  · rw [mem_closedForms_iff]
    intro h hh j k
    rw [← hvc i h hh j k]
    refine integral_congr_of_ae_weightedVolume d.isOpen d.w₂_cont (fun x hx => ?_)
      (fun x hx => ?_) ?_
    · have hxs : x ∉ tsupport h := fun h' => hx (hh.2.2 h')
      simp [dbarDir_eq_zero_of_notMem_tsupport hxs]
    · have hxs : x ∉ tsupport h := fun h' => hx (hh.2.2 h')
      simp [dbarDir_eq_zero_of_notMem_tsupport hxs]
    · filter_upwards [(memLp_formVec_of_components (hv i)).coeFn_toLp] with x hx
      rw [show (d.vVec hv).ofLp i = (memLp_formVec_of_components (hv i)).toLp (formVec (v i))
        from rfl, hx, formVec_apply, formVec_apply]

/-- `P_S T* α` is kernel-valued: `range AMap ⊆ kernelSubmodule`. -/
theorem range_AMap_le : LinearMap.range d.AMap ≤ kernelSubmodule d.G d.μ₁ := by
  rintro _ ⟨α, rfl⟩
  rw [mem_kernelSubmodule_iff]
  have hae := ae_all_iff.mpr fun i => (d.memLp_sTstar α i).coeFn_toLp
  filter_upwards [hae, d.ae_mem d.w₁] with x hx hxL
  have hx' : ∀ i, (d.AMap α i : ComplexModel n → ℂ) x = d.sTstar α i x := hx
  simp only [hx', smul_eq_mul]
  exact sum_mul_kernelProj d.G (d.pos x hxL) _

/-- For kernel-valued `U`, `(P_S T* α, U) = (T* α, U)`. -/
theorem inner_AMap_eq {U : d.H₁} (hU : U ∈ kernelSubmodule d.G d.μ₁)
    (α : Fin R → testForms d.L) : ⟪d.AMap α, U⟫_ℂ = ⟪d.tMap α, U⟫_ℂ := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  have hL : ∀ i, ⟪(d.AMap α).ofLp i, U i⟫_ℂ = ∫ x, conj (d.sTstar α i x) * U i x ∂d.μ₁ := by
    intro i
    rw [show (d.AMap α).ofLp i = (d.memLp_sTstar α i).toLp _ from rfl, inner_toLp_eq_integral]
    simp_rw [RCLike.inner_apply, mul_comm (U i _)]
  have hR : ∀ i, ⟪(d.tMap α).ofLp i, U i⟫_ℂ =
      ∫ x, conj (tstarForm d.w₂ d.ψ₀ (α i : Fin n → ComplexModel n → ℂ) x) * U i x ∂d.μ₁ :=
    fun i => inner_tstarToL2 d.isOpen d.w₁_cont d.w₂_smooth d.ψ_smooth.continuousOn (α i) (U i)
  simp only [hL, hR]
  rw [← integral_finsetSum _ fun i _ => integrable_conj_mul (d.memLp_sTstar α i) (Lp.memLp _),
    ← integral_finsetSum _ fun i _ => integrable_conj_mul (d.memLp_tstar α i) (Lp.memLp _)]
  refine integral_congr_ae ?_
  filter_upwards [hU] with x hx
  have hx' : ∑ k, d.G k x * (U k : ComplexModel n → ℂ) x = 0 := by simpa using hx
  exact sum_conj_kernelProj_mul d.G x hx' _

theorem inner_aMap_single (i : Fin R) (α₀ : testForms d.L) (F : d.H₂) :
    ⟪d.aMap (Pi.single i α₀), F⟫_ℂ = ⟪formToL2 d.isOpen d.w₂_cont α₀, F i⟫_ℂ := by
  rw [PiLp.inner_apply, Finset.sum_eq_single i]
  · rw [show (d.aMap (Pi.single i α₀)).ofLp i = formToL2 d.isOpen d.w₂_cont
      (Pi.single (M := fun _ => testForms d.L) i α₀ i) from rfl, Pi.single_eq_same]
  · intro k _ hk
    rw [show (d.aMap (Pi.single i α₀)).ofLp k = formToL2 d.isOpen d.w₂_cont
      (Pi.single (M := fun _ => testForms d.L) i α₀ k) from rfl, Pi.single_eq_of_ne hk,
      map_zero, inner_zero_left]
  · simp

theorem inner_tMap_single (i : Fin R) (α₀ : testForms d.L) (U : d.H₁) :
    ⟪d.tMap (Pi.single i α₀), U⟫_ℂ =
      ⟪tstarToL2 d.isOpen d.w₁_cont d.w₂_smooth d.ψ_smooth.continuousOn α₀, U i⟫_ℂ := by
  rw [PiLp.inner_apply, Finset.sum_eq_single i]
  · rw [show (d.tMap (Pi.single i α₀)).ofLp i = tstarToL2 d.isOpen d.w₁_cont d.w₂_smooth
      d.ψ_smooth.continuousOn (Pi.single (M := fun _ => testForms d.L) i α₀ i) from rfl,
      Pi.single_eq_same]
  · intro k _ hk
    rw [show (d.tMap (Pi.single i α₀)).ofLp k = tstarToL2 d.isOpen d.w₁_cont d.w₂_smooth
      d.ψ_smooth.continuousOn (Pi.single (M := fun _ => testForms d.L) i α₀ k) from rfl,
      Pi.single_eq_of_ne hk, map_zero, inner_zero_left]
  · simp

/-- **The kernel-bundle `L²` estimate on `L`** (`skoda:twisted-hormander`, Steps 3--4). -/
theorem exists_kernel_solution {t : ℝ} (ht : 0 < t)
    (hLevi : ∀ x ∈ d.L, ∀ ξ, (1 + 1 / t) * n * ‖fderiv ℝ d.ψ₀ x‖ ^ 2 * ‖ξ‖ ^ 2 ≤
      leviForm d.χ x ξ)
    (hcurv : ∀ z ∈ d.L, ∀ α : Fin R → Fin n → ℂ, InKernel d.G z α →
      (1 + t) * secondFundamental d.G z α ≤ vectorLevi d.Φ z α)
    {v : Fin R → Fin n → ComplexModel n → ℂ} (hv : ∀ i j, MemLp (v i j) 2 d.μ₂)
    (hvker : ∀ z ∈ d.L, InKernel d.G z fun i j => v i j z)
    (hvc : ∀ i, WeakDbarClosed d.L (v i))
    {g : ComplexModel n → ℝ} (hg0 : ∀ x ∈ d.L, 0 ≤ g x)
    (hvg : ∀ z ∈ d.L, ∀ α : Fin R → Fin n → ℂ, InKernel d.G z α →
      ‖∑ i, ∑ j, conj (α i j) * v i j z‖ ^ 2 ≤
        g z * (vectorLevi d.Φ z α - (1 + t) * secondFundamental d.G z α))
    (hgi : Integrable (fun x => g x * Real.exp (-d.w₁ x)) (volume.restrict d.L)) :
    ∃ u : Fin R → ComplexModel n → ℂ, (∀ i, MemLp (u i) 2 d.μ₁) ∧
      (∀ᵐ x ∂(volume.restrict d.L), ∑ i, d.G i x * u i x = 0) ∧
      (∀ i, WeakDbarEq d.L (u i) (v i)) ∧
      ∫ x in d.L, (∑ i, ‖u i x‖ ^ 2) * Real.exp (-d.w₁ x) ≤
        (1 + t) * ∫ x in d.L, g x * Real.exp (-d.w₁ x) := by
  set M := (1 + t) * ∫ x in d.L, g x * Real.exp (-d.w₁ x) with hMdef
  have hG0 : 0 ≤ ∫ x in d.L, g x * Real.exp (-d.w₁ x) :=
    setIntegral_nonneg d.isOpen.measurableSet fun x hx => mul_nonneg (hg0 x hx) (Real.exp_pos _).le
  have hM : 0 ≤ M := mul_nonneg (by linarith) hG0
  have hbound : ∀ α, ‖⟪d.aMap α, d.vVec hv⟫_ℂ‖ ≤ Real.sqrt M * ‖d.AMap α‖ :=
    norm_inner_le_of_approx' d.aMap d.AMap d.Qfun d.W (d.vVec_mem_W hv hvker hvc) hM
      (fun α => d.norm_sq_inner_le ht hLevi hcurv hv hvker hg0 hvg hgi α) d.exists_approx
  obtain ⟨U, hUcl, hUn, hUsol⟩ :=
    exists_solution_of_bound d.aMap d.AMap (d.vVec hv) (Real.sqrt_nonneg M) hbound
  have hUS : U ∈ kernelSubmodule d.G d.μ₁ :=
    Submodule.topologicalClosure_minimal _ d.range_AMap_le (isClosed_kernelSubmodule d.G d.μ₁)
      hUcl
  refine ⟨fun i => U i, fun i => Lp.memLp _, ?_, fun i => ?_, ?_⟩
  · have h := ae_restrict_of_ae_weightedVolume d.isOpen d.w₁_cont hUS
    simpa only [smul_eq_mul] using h
  · refine (weakDbarEq_iff_inner d.isOpen d.w₁_cont d.w₂_smooth d.ψ_smooth.continuousOn d.h12
      (Lp.memLp (U i)) (hv i)).mpr fun α₀ => ?_
    rw [Lp.toLp_coeFn]
    have h := hUsol (Pi.single i α₀)
    rw [d.inner_AMap_eq hUS, d.inner_tMap_single, d.inner_aMap_single] at h
    exact h
  · have hsq : ‖U‖ ^ 2 ≤ M :=
      calc ‖U‖ ^ 2 ≤ Real.sqrt M ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hUn 2
        _ = M := Real.sq_sqrt hM
    have hrow : ∀ i, ‖U.ofLp i‖ ^ 2 = ∫ x, ‖(U i : ComplexModel n → ℂ) x‖ ^ 2 ∂d.μ₁ := by
      intro i
      have h := norm_sq_toLp_eq_integral (Lp.memLp (U i))
      rwa [Lp.toLp_coeFn] at h
    have hnorm : ‖U‖ ^ 2 = ∫ x in d.L, (∑ i, ‖(U i : ComplexModel n → ℂ) x‖ ^ 2) *
        Real.exp (-d.w₁ x) := by
      rw [PiLp.norm_sq_eq_of_L2]
      simp only [hrow]
      rw [← integral_finsetSum _ fun i _ => (memLp_two_iff_integrable_sq_norm
        (Lp.memLp (U i)).1).mp (Lp.memLp (U i)), integral_weightedVolume d.isOpen d.w₁_cont]
      refine setIntegral_congr_fun d.isOpen.measurableSet fun x _ => ?_
      simp only [smul_eq_mul]
      ring
    rw [← hnorm]
    exact hsq

end KernelL2Data

/-! ### Assembly -/

theorem exists_bound_of_isCompact {K : Set (ComplexModel n)} (hK : IsCompact K) {ι : Type*}
    [Fintype ι] {f : ι → ComplexModel n → ℂ} (hf : ∀ i, ContinuousOn (f i) K) :
    ∃ C, ∀ x ∈ K, ∀ i, ‖f i x‖ ≤ C := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
    (continuousOn_finsetSum Finset.univ fun i _ => (hf i).norm)
  refine ⟨C, fun x hx i => ?_⟩
  have h1 := hC x hx
  rw [Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)] at h1
  exact (Finset.single_le_sum (f := fun i => ‖f i x‖) (fun _ _ => norm_nonneg _)
    (Finset.mem_univ i)).trans h1

/-- **Hörmander's `L²` estimate in the kernel bundle** (`skoda:twisted-hormander`). -/
theorem twistedHormanderStatement : TwistedHormanderStatement := by
  intro n D hDo hDc hDb K hK hKD t ht
  obtain ⟨L', U₀, η, ψ₀, χ, hL'o, hL'c, hL'D, hU₀o, hKU₀, hU₀L', hη, hηev, hψs, hχs, hηgrad,
    hψ0, hU₀z, h2ψ, hLevi, -⟩ := SGPT.Foundations.Analysis.Pending.exists_hormanderCutoffData
      hDo hDc hDb hK hKD ((1 + 1 / t) * n)
  refine ⟨L', U₀, fun x => χ x - 2 * ψ₀ x, fun x => χ x - ψ₀ x, hL'o, hL'c, hL'D, hU₀o, hKU₀,
    hU₀L', hχs.continuousOn.sub (continuousOn_const.mul hψs.continuousOn),
    hχs.continuousOn.sub hψs.continuousOn,
    fun x hx => ⟨by linarith [h2ψ x hx], by linarith [hψ0 x]⟩,
    fun x hx => by simp [(hU₀z x hx).1, (hU₀z x hx).2], ?_⟩
  intro R G hG hpos Φ hΦ hcurv v hv hvker hvc g hg0 hvg hgi
  simp only [← add_sub_assoc] at hv hgi ⊢
  have hKc : IsCompact (closure L') :=
    Metric.isCompact_of_isClosed_isBounded isClosed_closure (hDb.subset hL'D)
  have hL'sub : L' ⊆ D := subset_closure.trans hL'D
  have hbd : ∀ {ι : Type} [Fintype ι] {f : ι → ComplexModel n → ℂ},
      (∀ i, ContinuousOn (f i) D) → ∃ C, ∀ x ∈ L', ∀ i, ‖f i x‖ ≤ C := by
    intro ι _ f hf
    obtain ⟨C, hC⟩ := exists_bound_of_isCompact hKc fun i => (hf i).mono hL'D
    exact ⟨C, fun x hx i => hC x (subset_closure hx) i⟩
  obtain ⟨CG, hCG⟩ := hbd (f := G) fun i => (hG i).continuousOn
  obtain ⟨CdG, hCdG⟩ := hbd (f := fun p : Fin R × Fin n => dDir (coordVec p.2) (G p.1))
    fun p => (contDiffOn_dDir hDo (contDiffOn_real_of_holo hDo (hG p.1)) _).continuousOn
  obtain ⟨Cρ, hCρ⟩ := hbd (f := normalDir G) fun i =>
    (contDiffOn_normalDir hDo hG hpos i).continuousOn
  obtain ⟨Cdρ, hCdρ⟩ := hbd
    (f := fun p : Fin R × Fin n => dbarDir (coordVec p.2) (normalDir G p.1))
    fun p => (contDiffOn_dbarDir hDo (contDiffOn_normalDir hDo hG hpos p.1) _).continuousOn
  let d : KernelL2Data n R :=
    { L := L', Φ := Φ, χ := χ, ψ₀ := ψ₀, η := η, G := G, isOpen := hL'o
      Φ_smooth := hΦ.mono hL'sub, χ_smooth := hχs, ψ_smooth := hψs, ψ_nonneg := hψ0
      η_test := hη, η_ev := hηev, η_grad := hηgrad
      G_holo := fun i => (hG i).mono hL'sub, pos := fun z hz => hpos z (hL'sub hz)
      CG := CG, G_bound := hCG, CdG := CdG, dG_bound := fun x hx i j => hCdG x hx (i, j)
      Cρ := Cρ, ρ_bound := hCρ, Cdρ := Cdρ, dρ_bound := fun x hx i j => hCdρ x hx (i, j) }
  exact d.exists_kernel_solution ht hLevi (fun z hz => hcurv z (hL'sub hz)) hv hvker hvc hg0
    hvg hgi

end SGPT.Okounkov.TranscendentalSkoda
