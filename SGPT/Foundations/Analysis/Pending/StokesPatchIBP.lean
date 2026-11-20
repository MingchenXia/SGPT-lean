import SGPT.Foundations.Analysis.Pending.StokesRegularDecomposition
import SGPT.Foundations.Analysis.Pending.StokesWeightedPairing
import SGPT.Foundations.Analysis.Pending.PatchDensityTelescope
import SGPT.Foundations.Analysis.Pending.PatchDensityLocalPotential
import SGPT.Foundations.Analysis.Pending.BedfordTaylorSlots
import SGPT.Foundations.Analysis.Pending.MixedCoordinateDensity
import SGPT.Foundations.Analysis.Pending.ChartPartition
import SGPT.Foundations.Analysis.Pending.SmoothDDCForm

set_option autoImplicit false

/-!
# Integration by parts on `V_reg` against a cutoff vanishing near `V_sing`

Blueprint `ana:stokes-patch-ibp` (TN.4 #4, Stokes against `[V]`, part B of
Stokes' theorem on the regular locus).

For smooth functions `χ`, `w` on a compact complex manifold `X`, `χ` with `tsupport χ ∩ V ⊆ V_reg`,
and smooth two-forms `a_i` (`i ≠ i₀`) with local potentials in the parameters of every regular
patch (`HasPatchPotentials`: closed real `(1,1)`-forms, `ddᶜ` of smooth functions, sums), the
integrals over the decomposition measure of `StokesRegularDecomposition` satisfy

`∫ (χ ∘ γ) D_γ(a[i₀ ↦ ddᶜw]) dμ = ∫ (w ∘ γ) D_γ(a[i₀ ↦ ddᶜχ]) dμ`

(`integral_measure_ibp`).  Proof: a finite chart partition of unity `ρ_b` subordinate to
`{X \ K} ∪ {U_x : x ∈ K}`, `K = tsupport χ ∩ V`, where `U_x` traps a parameter ball of a patch
centred at `x` carrying potentials of the slots; in each patch the slot swap of
`BedfordTaylor.integral_mul_mixedDensity_update_swap` (`setIntegral_patch_ibp`), and the transfer
`RegularDecomposition.integrable_measure_and_integral_eq` on both sides.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff

namespace SGPT.Foundations.Analysis.Pending.StokesPatchIBP

open FirstPass FirstPass.NumericalRestrictedVolume FirstPass.RegularPatchNeighborhood
open FirstPass.MongeAmpere FirstPass.MixedMongeAmpere
open RegularPatchTransition StokesRegularDecomposition SmoothDDCForm

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {V : ClosedIrreducibleAnalyticSubvariety n M}

/-! ### Slots with local potentials in patch parameters -/

/-- A smooth two-form has, near every parameter of every regular patch, a smooth potential
of its pull-back. -/
def HasPatchPotentials (V : ClosedIrreducibleAnalyticSubvariety n M) (a : SmoothRealForm n M 2) :
    Prop :=
  ∀ (P : RegularPatch V) (w : ComplexModel V.dim), w ∈ P.parameterDomain →
    ∃ (Ω : Set (ComplexModel V.dim)) (φ : ComplexModel V.dim → ℝ), w ∈ Ω ∧ IsOpen Ω ∧
      Ω ⊆ P.parameterDomain ∧ ContDiffOn ℝ ∞ φ Ω ∧
        ∀ w' ∈ Ω, patchCoordinateForm a P w' = smoothDDC φ w'

theorem isOpen_parameterDomain (P : RegularPatch V) : IsOpen P.parameterDomain :=
  AdmissibleCurrentFormPositivity.RegularPatchDerivative.isOpen_parameterDomain P

/-- A smooth function read through a regular patch is smooth on the parameter domain. -/
theorem contDiffOn_comp_toManifold {v : M → ℝ} (hv : ChartSmooth (n := n) v)
    (P : RegularPatch V) :
    ContDiffOn ℝ ∞ (fun y => v (P.toManifold y)) P.parameterDomain := by
  have hmaps : MapsTo P.coordinateParametrization P.parameterDomain
      (complexChartAt (n := n) P.center).val.target :=
    fun w hw => P.source_subset (P.flattening.mapsTo_invFun hw)
  exact (hv (complexChartAt (n := n) P.center)).comp
    ((PatchDensityTelescope.contDiffOn_complex_coordinateParametrization P).restrict_scalars ℝ)
    hmaps

theorem hasPatchPotentials_closed (θ : ClosedRealOneOneForm n M) :
    HasPatchPotentials V θ.val := fun P _ hw =>
  PatchDensityLocalPotential.exists_localPotential_patchCoordinateForm θ P hw

theorem hasPatchPotentials_ddcForm {v : M → ℝ} (hv : ChartSmooth (n := n) v) :
    HasPatchPotentials V (ddcForm v hv) := fun P _ hw =>
  ⟨P.parameterDomain, fun y => v (P.toManifold y), hw, isOpen_parameterDomain P, subset_rfl,
    contDiffOn_comp_toManifold hv P, fun _ hw' =>
      PatchDensityTelescope.patchCoordinateForm_ddcForm P hv hw'⟩

/-- Potentials add. -/
theorem HasPatchPotentials.add {a b c : SmoothRealForm n M 2} (ha : HasPatchPotentials V a)
    (hb : HasPatchPotentials V b)
    (hc : ∀ (e : ComplexChart n M) (z : ComplexModel n), c.coeff e z = a.coeff e z + b.coeff e z) :
    HasPatchPotentials V c := fun P w hw => by
  obtain ⟨Ωa, φa, hwa, hΩa, hΩas, hφa, hpa⟩ := ha P w hw
  obtain ⟨Ωb, φb, hwb, hΩb, hΩbs, hφb, hpb⟩ := hb P w hw
  refine ⟨Ωa ∩ Ωb, fun y => φa y + φb y, ⟨hwa, hwb⟩, hΩa.inter hΩb, inter_subset_left.trans hΩas,
    (hφa.mono inter_subset_left).add (hφb.mono inter_subset_right), fun w' hw' => ?_⟩
  rw [PatchDensityTelescope.patchCoordinateForm_add a b c hc, hpa w' hw'.1, hpb w' hw'.2,
    smoothDDC_add (hΩa.inter hΩb) (hφa.mono inter_subset_left) (hφb.mono inter_subset_right) hw']

/-! ### Densities in a patch through potentials -/

/-- The pulled-back family with one slot replaced. -/
theorem patchCoordinateForm_update (a : Fin V.dim → SmoothRealForm n M 2) (i₀ : Fin V.dim)
    (b : SmoothRealForm n M 2) (P : RegularPatch V) (u : ComplexModel V.dim) :
    (fun i => patchCoordinateForm (Function.update a i₀ b i) P u) =
      Function.update (fun i => patchCoordinateForm (a i) P u) i₀ (patchCoordinateForm b P u) := by
  funext i
  by_cases h : i = i₀
  · subst h; simp
  · simp [Function.update_of_ne h]

/-- In a patch region carrying potentials `φᵢ` of the slots `i ≠ i₀`, the mixed density with
`ddᶜ g` in slot `i₀` is the mixed density of the complex Hessians of `φ[i₀ ↦ g ∘ γ]`. -/
theorem patchMixedDensity_update_ddcForm_eq (P : RegularPatch V) {Ω : Set (ComplexModel V.dim)}
    (hΩ : IsOpen Ω) (hΩsub : Ω ⊆ P.parameterDomain) {a : Fin V.dim → SmoothRealForm n M 2}
    (i₀ : Fin V.dim) {φ : Fin V.dim → ComplexModel V.dim → ℝ} (hφ : ∀ i, ContDiffOn ℝ ∞ (φ i) Ω)
    (hpot : ∀ i, i ≠ i₀ → ∀ u ∈ Ω, patchCoordinateForm (a i) P u = smoothDDC (φ i) u)
    {g : M → ℝ} (hg : ChartSmooth (n := n) g) {G : ComplexModel V.dim → ℝ}
    (hG : ∀ u ∈ Ω, G u = g (P.toManifold u)) {u : ComplexModel V.dim} (hu : u ∈ Ω) :
    patchMixedDensity (Function.update a i₀ (ddcForm g hg)) P u =
      mixedDensity (Function.update φ i₀ G) u := by
  have hGs : ContDiffOn ℝ ∞ G Ω :=
    ((contDiffOn_comp_toManifold hg P).mono hΩsub).congr hG
  have hsmooth : ∀ i, ContDiffOn ℝ ∞ (Function.update φ i₀ G i) Ω := fun i => by
    by_cases h : i = i₀
    · subst h; simpa using hGs
    · simpa [Function.update_of_ne h] using hφ i
  rw [patchMixedDensity, patchCoordinateForm_update,
    ← actualMixedTopDensity_smoothDDC (fun i =>
      ((hsmooth i).contDiffAt (hΩ.mem_nhds hu)).of_le (WithTop.coe_le_coe.mpr le_top))]
  congr 1
  funext i
  by_cases h : i = i₀
  · subst h
    simp only [Function.update_self]
    rw [PatchDensityTelescope.patchCoordinateForm_ddcForm P hg (hΩsub hu)]
    exact smoothDDC_congr (Filter.eventuallyEq_of_mem (hΩ.mem_nhds hu) fun y hy => (hG y hy).symm)
  · simp only [Function.update_of_ne h]
    exact hpot i h u hu

/-- A mixed density with a slot vanishing near `z` vanishes at `z`. -/
theorem mixedDensity_update_eq_zero {k : ℕ} (f : Fin k → ComplexModel k → ℝ) (i₀ : Fin k)
    {A : ComplexModel k → ℝ} {z : ComplexModel k} (hA : A =ᶠ[𝓝 z] 0) :
    mixedDensity (Function.update f i₀ A) z = 0 := by
  rw [BedfordTaylor.mixedDensity_congr (g := Function.update f i₀ (fun _ => (0 : ℝ))) fun i => by
    by_cases h : i = i₀
    · subst h; simp only [Function.update_self]; exact hA
    · simp [Function.update_of_ne h]]
  have h := BedfordTaylor.mixedDensity_update_add_smul (f := f) i₀ (a := fun _ => (0 : ℝ))
    (b := fun _ => (0 : ℝ)) (z := z) contDiffAt_const contDiffAt_const 1
  simp only [mul_zero, add_zero, one_mul] at h
  linarith

/-- **Integration by parts in one patch.**  If `g ∘ γ` vanishes on `Ω` off a compact subset of
`Ω`, and the slots `i ≠ i₀` have potentials `φᵢ` on the open `Ω`, then
`∫_Ω (g∘γ) D(a[i₀ ↦ ddᶜw]) = ∫_Ω (w∘γ) D(a[i₀ ↦ ddᶜg])`. -/
theorem setIntegral_patch_ibp (P : RegularPatch V) {Ω : Set (ComplexModel V.dim)}
    (hΩ : IsOpen Ω) (hΩsub : Ω ⊆ P.parameterDomain) {a : Fin V.dim → SmoothRealForm n M 2}
    (i₀ : Fin V.dim) {φ : Fin V.dim → ComplexModel V.dim → ℝ} (hφ : ∀ i, ContDiffOn ℝ ∞ (φ i) Ω)
    (hpot : ∀ i, i ≠ i₀ → ∀ u ∈ Ω, patchCoordinateForm (a i) P u = smoothDDC (φ i) u)
    {g w : M → ℝ} (hg : ChartSmooth (n := n) g) (hw : ChartSmooth (n := n) w)
    {K : Set (ComplexModel V.dim)} (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (hgK : ∀ u ∈ Ω, u ∉ K → g (P.toManifold u) = 0) :
    ∫ u in Ω, g (P.toManifold u) * patchMixedDensity (Function.update a i₀ (ddcForm w hw)) P u =
      ∫ u in Ω, w (P.toManifold u) * patchMixedDensity (Function.update a i₀ (ddcForm g hg)) P u := by
  classical
  set A : ComplexModel V.dim → ℝ := Ω.indicator fun u => g (P.toManifold u) with hAdef
  set B : ComplexModel V.dim → ℝ := fun u => w (P.toManifold u) with hBdef
  have hAΩ : ∀ u ∈ Ω, A u = g (P.toManifold u) := fun u hu => indicator_of_mem hu _
  have hAK : ∀ u, u ∉ K → A u = 0 := fun u hu => by
    by_cases hΩu : u ∈ Ω
    · rw [hAΩ u hΩu, hgK u hΩu hu]
    · exact indicator_of_notMem hΩu _
  have htsA : tsupport A ⊆ K := closure_minimal (fun u hu => by
    by_contra h; exact hu (hAK u h)) hK.isClosed
  have hAs : ContDiffOn ℝ ∞ A Ω :=
    ((contDiffOn_comp_toManifold hg P).mono hΩsub).congr fun u hu => hAΩ u hu
  have hBs : ContDiffOn ℝ ∞ B Ω := (contDiffOn_comp_toManifold hw P).mono hΩsub
  have hswap := BedfordTaylor.integral_mul_mixedDensity_update_swap (U := ⟨Ω, hΩ⟩) (f := φ) hφ
    i₀ hAs hBs (hK.of_isClosed_subset (isClosed_tsupport A) htsA) (htsA.trans hKΩ)
  -- the left side
  have hL : ∫ u in Ω, g (P.toManifold u) * patchMixedDensity (Function.update a i₀ (ddcForm w hw))
      P u = ∫ u, A u * mixedDensity (Function.update φ i₀ B) u := by
    rw [← integral_indicator hΩ.measurableSet]
    congr 1
    funext u
    by_cases hu : u ∈ Ω
    · rw [indicator_of_mem hu, hAΩ u hu,
        patchMixedDensity_update_ddcForm_eq P hΩ hΩsub i₀ hφ hpot hw (fun _ _ => rfl) hu]
    · rw [indicator_of_notMem hu, show A u = 0 from indicator_of_notMem hu _, zero_mul]
  -- the right side
  have hR : ∫ u in Ω, w (P.toManifold u) * patchMixedDensity (Function.update a i₀ (ddcForm g hg))
      P u = ∫ u, B u * mixedDensity (Function.update φ i₀ A) u := by
    rw [← integral_indicator hΩ.measurableSet]
    congr 1
    funext u
    by_cases hu : u ∈ Ω
    · rw [indicator_of_mem hu,
        patchMixedDensity_update_ddcForm_eq P hΩ hΩsub i₀ hφ hpot hg (fun v hv => hAΩ v hv) hu]
    · rw [indicator_of_notMem hu, mixedDensity_update_eq_zero φ i₀
        (Filter.eventuallyEq_of_mem ((hK.isClosed.isOpen_compl).mem_nhds fun h => hu (hKΩ h))
          fun v hv => hAK v hv), mul_zero]
  rw [hL, hR]
  exact hswap

/-! ### Vanishing and linearity of the swapped slot -/

/-- `ddᶜ` of a finite sum of smooth functions on an open set. -/
theorem smoothDDC_finsetSum {k : ℕ} {ι : Type*} (s : Finset ι) {h : ι → ComplexModel k → ℝ}
    {U : Set (ComplexModel k)} (hU : IsOpen U) (hh : ∀ i ∈ s, ContDiffOn ℝ ∞ (h i) U)
    {z : ComplexModel k} (hz : z ∈ U) :
    smoothDDC (fun y => ∑ i ∈ s, h i y) z = ∑ i ∈ s, smoothDDC (h i) z := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [smoothDDC_add hU (hh a (Finset.mem_insert_self a s))
      (ContDiffOn.sum fun i hi => hh i (Finset.mem_insert_of_mem hi)) hz,
      ih fun i hi => hh i (Finset.mem_insert_of_mem hi)]

/-- If `g` vanishes near `γ(u)`, the mixed density with `ddᶜg` in one slot vanishes at `u`. -/
theorem patchMixedDensity_update_ddcForm_eq_zero (P : RegularPatch V)
    (a : Fin V.dim → SmoothRealForm n M 2) (i₀ : Fin V.dim) {g : M → ℝ}
    (hg : ChartSmooth (n := n) g) {u : ComplexModel V.dim} (hu : u ∈ P.parameterDomain)
    (hg0 : g =ᶠ[𝓝 (P.toManifold u)] 0) :
    patchMixedDensity (Function.update a i₀ (ddcForm g hg)) P u = 0 := by
  have hcont : ContinuousAt P.toManifold u :=
    (RegularPatch.continuousOn_toManifold P).continuousAt ((isOpen_parameterDomain P).mem_nhds hu)
  have hzero : patchCoordinateForm (ddcForm g hg) P u = 0 := by
    rw [PatchDensityTelescope.patchCoordinateForm_ddcForm P hg hu]
    rw [smoothDDC_congr (g := fun _ => (0 : ℝ)) ((hcont.eventually hg0).mono fun y hy => hy)]
    exact smoothDDC_zero u
  rw [patchMixedDensity, patchCoordinateForm_update, hzero]
  exact (MongeAmpere.actualMixedTopDensityMultilinear).map_update_zero _ i₀

/-- **Linearity in the swapped slot.**  If `χ = ∑_b g_b`, the mixed density with `ddᶜχ` in slot
`i₀` is the sum of those with `ddᶜg_b`. -/
theorem patchMixedDensity_update_ddcForm_sum (P : RegularPatch V)
    (a : Fin V.dim → SmoothRealForm n M 2) (i₀ : Fin V.dim) {m : ℕ} {g : Fin m → M → ℝ}
    (hg : ∀ b, ChartSmooth (n := n) (g b)) {χ : M → ℝ} (hχ : ChartSmooth (n := n) χ)
    (hsum : ∀ y, ∑ b, g b y = χ y) {u : ComplexModel V.dim} (hu : u ∈ P.parameterDomain) :
    patchMixedDensity (Function.update a i₀ (ddcForm χ hχ)) P u =
      ∑ b, patchMixedDensity (Function.update a i₀ (ddcForm (g b) (hg b))) P u := by
  have hform : patchCoordinateForm (ddcForm χ hχ) P u =
      ∑ b, patchCoordinateForm (ddcForm (g b) (hg b)) P u := by
    rw [PatchDensityTelescope.patchCoordinateForm_ddcForm P hχ hu]
    rw [show (fun y => χ (P.toManifold y)) = fun y => ∑ b, g b (P.toManifold y) from
      funext fun y => (hsum _).symm]
    rw [smoothDDC_finsetSum Finset.univ (isOpen_parameterDomain P)
      (fun b _ => contDiffOn_comp_toManifold (hg b) P) hu]
    exact Finset.sum_congr rfl fun b _ =>
      (PatchDensityTelescope.patchCoordinateForm_ddcForm P (hg b) hu).symm
  simp only [patchMixedDensity, patchCoordinateForm_update]
  rw [hform]
  have hlin := map_sum ((MongeAmpere.actualMixedTopDensityMultilinear).toLinearMap
    (fun i => patchCoordinateForm (a i) P u) i₀)
    (fun b => patchCoordinateForm (ddcForm (g b) (hg b)) P u) Finset.univ
  simpa only [MultilinearMap.toLinearMap_apply,
    MongeAmpere.actualMixedTopDensityMultilinear_apply] using hlin

/-- The integrands are continuous on the parameter domain. -/
theorem continuousOn_mul_patchMixedDensity (P : RegularPatch V)
    (b : Fin V.dim → SmoothRealForm n M 2) {g : M → ℝ} (hg : ChartSmooth (n := n) g) :
    ContinuousOn (fun u => g (P.toManifold u) * patchMixedDensity b P u) P.parameterDomain :=
  (contDiffOn_comp_toManifold hg P).continuousOn.mul (continuousOn_patchMixedDensity b P)

/-! ### Local data at a regular point -/

/-- **A patch at a regular point carrying potentials of the slots `i ≠ i₀`**, a parameter ball
with closure in the potential domain, and an ambient open set trapping the ball's image. -/
theorem exists_ibpChart {a : Fin V.dim → SmoothRealForm n M 2} (i₀ : Fin V.dim)
    (ha : ∀ i, i ≠ i₀ → HasPatchPotentials V (a i)) {x : M}
    (hx : x ∈ regularLocus (n := n) V.carrier V.dim) :
    ∃ (P : RegularPatch V) (Ω : Set (ComplexModel V.dim)) (φ : Fin V.dim → ComplexModel V.dim → ℝ)
      (r : ℝ) (U : Set M), IsOpen Ω ∧ Ω ⊆ P.parameterDomain ∧ (∀ i, ContDiffOn ℝ ∞ (φ i) Ω) ∧
        (∀ i, i ≠ i₀ → ∀ u ∈ Ω, patchCoordinateForm (a i) P u = smoothDDC (φ i) u) ∧ 0 < r ∧
          Metric.closedBall (0 : ComplexModel V.dim) r ⊆ Ω ∧ IsOpen U ∧ x ∈ U ∧
            V.carrier ∩ U ⊆ P.toManifold '' Metric.ball (0 : ComplexModel V.dim) r := by
  classical
  set P : RegularPatch V := SubvarietyStokesMassInterfaces.patchOfMemRegularLocus hx with hP
  have h0 : (0 : ComplexModel V.dim) ∈ P.parameterDomain := RegularPatch.zero_mem_parameterDomain P
  have hslot : ∀ i, ∃ (Ω : Set (ComplexModel V.dim)) (φ : ComplexModel V.dim → ℝ),
      (0 : ComplexModel V.dim) ∈ Ω ∧ IsOpen Ω ∧ ContDiffOn ℝ ∞ φ Ω ∧
        (i ≠ i₀ → ∀ u ∈ Ω, patchCoordinateForm (a i) P u = smoothDDC φ u) := fun i => by
    by_cases h : i = i₀
    · exact ⟨univ, fun _ => 0, mem_univ _, isOpen_univ, contDiffOn_const, fun h' => (h' h).elim⟩
    · obtain ⟨Ω, φ, h0Ω, hΩ, -, hφ, hpot⟩ := ha i h P 0 h0
      exact ⟨Ω, φ, h0Ω, hΩ, hφ, fun _ => hpot⟩
  choose Ωi φ h0i hΩi hφi hpoti using hslot
  set Ω : Set (ComplexModel V.dim) := P.parameterDomain ∩ ⋂ i, Ωi i with hΩdef
  have hΩo : IsOpen Ω := (isOpen_parameterDomain P).inter (isOpen_iInter_of_finite hΩi)
  have h0Ω : (0 : ComplexModel V.dim) ∈ Ω := ⟨h0, mem_iInter.2 h0i⟩
  obtain ⟨ε, hε, hεΩ⟩ := Metric.isOpen_iff.mp hΩo 0 h0Ω
  set r := ε / 2 with hr
  have hr0 : 0 < r := half_pos hε
  have hcb : Metric.closedBall (0 : ComplexModel V.dim) r ⊆ Ω :=
    (Metric.closedBall_subset_ball (half_lt_self hε)).trans hεΩ
  have hballdom : Metric.ball (0 : ComplexModel V.dim) r ⊆ P.parameterDomain :=
    Metric.ball_subset_closedBall.trans (hcb.trans inter_subset_left)
  obtain ⟨U, hUo, himU, hUV⟩ := PatchParameterNull.exists_isOpen_carrier_inter_subset_image P
    Metric.isOpen_ball hballdom
  refine ⟨P, Ω, φ, r, U, hΩo, inter_subset_left, fun i => (hφi i).mono fun u hu =>
    mem_iInter.1 hu.2 i, fun i hi u hu => hpoti i hi u (mem_iInter.1 hu.2 i), hr0, hcb, hUo, ?_, hUV⟩
  exact himU ⟨0, Metric.mem_ball_self hr0, by rw [RegularPatch.toManifold_zero]; rfl⟩

/-- The decomposition measure lives on the pieces. -/
theorem ae_mem_piece (D : RegularDecomposition V) :
    ∀ᵐ x ∂D.measure, x.2 ∈ D.piece x.1 := by
  have hmeas : MeasurableSet {x : ℕ × ComplexModel V.dim | x.2 ∈ D.piece x.1} := by
    have : {x : ℕ × ComplexModel V.dim | x.2 ∈ D.piece x.1} =
        ⋃ j, ({j} : Set ℕ) ×ˢ D.piece j := by
      ext ⟨j, u⟩
      simp
    rw [this]
    exact MeasurableSet.iUnion fun j => (measurableSet_singleton j).prod (D.measurableSet_piece j)
  rw [ae_iff]
  change D.measure {x : ℕ × ComplexModel V.dim | x.2 ∈ D.piece x.1}ᶜ = 0
  rw [RegularDecomposition.measure, Measure.sum_apply _ hmeas.compl]
  refine ENNReal.tsum_eq_zero.mpr fun j => ?_
  rw [Measure.map_apply measurable_prodMk_left hmeas.compl,
    Measure.restrict_apply (measurable_prodMk_left hmeas.compl)]
  convert measure_empty (μ := volume)
  ext u
  simp

/-! ### Integration by parts on the decomposition measure -/

/-- The parametrization of a regular patch is injective on its parameter domain. -/
theorem toManifold_injOn (P : RegularPatch V) : InjOn P.toManifold P.parameterDomain :=
  fun u hu u' hu' h => by
    rw [← StokesWeightedPairing.parameterOf_toManifold P hu,
      ← StokesWeightedPairing.parameterOf_toManifold P hu', h]

/-- **Integration by parts on `V_reg`** (blueprint `ana:stokes-patch-ibp`).  Let `χ`, `w` be
smooth on the compact `X` with `tsupport χ ∩ V ⊆ V_reg`, and let the slots `aᵢ`, `i ≠ i₀`, have
local potentials in patch parameters.  On the decomposition measure `μ`, the functions
`(j, u) ↦ χ(γⱼ u) D_{γⱼ}(a[i₀ ↦ ddᶜw])(u)` and `(j, u) ↦ w(γⱼ u) D_{γⱼ}(a[i₀ ↦ ddᶜχ])(u)` are
integrable with the same integral. -/
theorem integral_measure_ibp [CompactSpace M] (D : RegularDecomposition V)
    {a : Fin V.dim → SmoothRealForm n M 2} (i₀ : Fin V.dim)
    (ha : ∀ i, i ≠ i₀ → HasPatchPotentials V (a i))
    {χ w : M → ℝ} (hχ : ChartSmooth (n := n) χ) (hw : ChartSmooth (n := n) w)
    (hχreg : ∀ x ∈ tsupport χ, x ∈ V.carrier → x ∈ regularLocus (n := n) V.carrier V.dim) :
    Integrable (fun x : ℕ × ComplexModel V.dim => χ ((D.patch x.1).toManifold x.2) *
        patchMixedDensity (Function.update a i₀ (ddcForm w hw)) (D.patch x.1) x.2) D.measure ∧
      Integrable (fun x : ℕ × ComplexModel V.dim => w ((D.patch x.1).toManifold x.2) *
        patchMixedDensity (Function.update a i₀ (ddcForm χ hχ)) (D.patch x.1) x.2) D.measure ∧
      ∫ x, χ ((D.patch x.1).toManifold x.2) *
          patchMixedDensity (Function.update a i₀ (ddcForm w hw)) (D.patch x.1) x.2 ∂D.measure =
        ∫ x, w ((D.patch x.1).toManifold x.2) *
          patchMixedDensity (Function.update a i₀ (ddcForm χ hχ)) (D.patch x.1) x.2 ∂D.measure := by
  classical
  set K : Set M := tsupport χ ∩ V.carrier with hKdef
  have hKc : IsCompact K := ((isClosed_tsupport χ).inter V.isClosed_carrier).isCompact
  have hloc : ∀ x : K, ∃ (P : RegularPatch V) (Ω : Set (ComplexModel V.dim))
      (φ : Fin V.dim → ComplexModel V.dim → ℝ) (r : ℝ) (U : Set M), IsOpen Ω ∧
        Ω ⊆ P.parameterDomain ∧ (∀ i, ContDiffOn ℝ ∞ (φ i) Ω) ∧
        (∀ i, i ≠ i₀ → ∀ u ∈ Ω, patchCoordinateForm (a i) P u = smoothDDC (φ i) u) ∧ 0 < r ∧
          Metric.closedBall (0 : ComplexModel V.dim) r ⊆ Ω ∧ IsOpen U ∧ (x : M) ∈ U ∧
            V.carrier ∩ U ⊆ P.toManifold '' Metric.ball (0 : ComplexModel V.dim) r := fun x =>
    exists_ibpChart i₀ ha (hχreg x x.2.1 x.2.2)
  choose P Ω φ r U hΩo hΩd hφ hpot hr hrΩ hUo hxU hUV using hloc
  -- the cover and the partition of unity
  let S : Option K → TopologicalSpace.Opens M := fun o => match o with
    | none => ⟨Kᶜ, hKc.isClosed.isOpen_compl⟩
    | some x => ⟨U x, hUo x⟩
  have hcover : ∀ y : M, ∃ o, y ∈ S o := fun y => by
    by_cases hy : y ∈ K
    · exact ⟨some ⟨y, hy⟩, hxU _⟩
    · exact ⟨none, hy⟩
  obtain ⟨m, ρ, idx, hρs, -, hρsupp, -, hρsum⟩ :=
    ChartPartition.exists_chartSmooth_partitionOfUnity (n := n) S hcover
  set g : Fin m → M → ℝ := fun b y => ρ b y * χ y with hgdef
  have hgs : ∀ b, ChartSmooth (n := n) (g b) := fun b e => (hρs b e).mul (hχ e)
  have hsumg : ∀ y, ∑ b, g b y = χ y := fun y => by
    simp only [hgdef, ← Finset.sum_mul, hρsum, one_mul]
  -- `g b` vanishes near every point of `V` outside `tsupport (ρ b)`
  have hgvan : ∀ b (y : M), y ∈ V.carrier → y ∉ tsupport (ρ b) → g b =ᶠ[𝓝 y] 0 := by
    intro b y _ hy
    exact ((notMem_tsupport_iff_eventuallyEq.mp hy).mono fun z hz => by
      simp only [hgdef, Pi.zero_apply] at hz ⊢; rw [hz, zero_mul])
  -- notation for the four families of integrands
  set FL : Fin m → ℕ × ComplexModel V.dim → ℝ := fun b x =>
    g b ((D.patch x.1).toManifold x.2) *
      patchMixedDensity (Function.update a i₀ (ddcForm w hw)) (D.patch x.1) x.2 with hFL
  set FR : Fin m → ℕ × ComplexModel V.dim → ℝ := fun b x =>
    w ((D.patch x.1).toManifold x.2) *
      patchMixedDensity (Function.update a i₀ (ddcForm (g b) (hgs b))) (D.patch x.1) x.2 with hFR
  have hmem : ∀ x : ℕ × ComplexModel V.dim, x.2 ∈ D.piece x.1 →
      (D.patch x.1).toManifold x.2 ∈ V.carrier := fun x hx =>
    RegularPatch.toManifold_mem_carrier _ (D.piece_subset x.1 hx)
  -- each term
  have hterm : ∀ b, Integrable (FL b) D.measure ∧ Integrable (FR b) D.measure ∧
      ∫ x, FL b x ∂D.measure = ∫ x, FR b x ∂D.measure := by
    intro b
    rcases hidx : idx b with _ | x
    · -- the term subordinate to `X \ K`: `g b` vanishes near every point of `V`
      have hsupp : tsupport (ρ b) ⊆ Kᶜ := by simpa [S, hidx] using hρsupp b
      have hvanV : ∀ y ∈ V.carrier, g b =ᶠ[𝓝 y] 0 := fun y hy => by
        by_cases hyK : y ∈ K
        · exact hgvan b y hy fun h => hsupp h hyK
        · have hyχ : y ∉ tsupport χ := fun h => hyK ⟨h, hy⟩
          exact (notMem_tsupport_iff_eventuallyEq.mp hyχ).mono fun z hz => by
            simp only [hgdef, Pi.zero_apply] at hz ⊢; rw [hz, mul_zero]
      have hL0 : FL b =ᵐ[D.measure] 0 := (ae_mem_piece D).mono fun x hx => by
        simp only [hFL, Pi.zero_apply]
        rw [(hvanV _ (hmem x hx)).eq_of_nhds, Pi.zero_apply, zero_mul]
      have hR0 : FR b =ᵐ[D.measure] 0 := (ae_mem_piece D).mono fun x hx => by
        simp only [hFR, Pi.zero_apply]
        rw [patchMixedDensity_update_ddcForm_eq_zero _ a i₀ (hgs b) (D.piece_subset x.1 hx)
          (hvanV _ (hmem x hx)), mul_zero]
      exact ⟨(integrable_zero _ _ _).congr hL0.symm, (integrable_zero _ _ _).congr hR0.symm,
        by rw [integral_congr_ae hL0, integral_congr_ae hR0]⟩
    · -- the term subordinate to `U x`: transfer to the patch `P x` and swap there
      have hsupp : tsupport (ρ b) ⊆ U x := by simpa [S, hidx] using hρsupp b
      set Q := P x with hQ
      have hball : ∀ u ∈ Q.parameterDomain, Q.toManifold u ∈ tsupport (ρ b) →
          u ∈ Metric.ball (0 : ComplexModel V.dim) (r x) := fun u hu h => by
        obtain ⟨u', hu', hu'u⟩ := hUV x ⟨RegularPatch.toManifold_mem_carrier Q hu, hsupp h⟩
        have hball' : Metric.ball (0 : ComplexModel V.dim) (r x) ⊆ Q.parameterDomain :=
          Metric.ball_subset_closedBall.trans ((hrΩ x).trans (hΩd x))
        rw [← toManifold_injOn Q (hball' hu') hu hu'u]
        exact hu'
      -- off `Q(Ω x)`, a point of `V` is off `tsupport (ρ b)`
      have hoff : ∀ y ∈ V.carrier, y ∉ Q.toManifold '' Ω x → y ∉ tsupport (ρ b) := fun y hy hyQ h => by
        obtain ⟨u', hu', hu'y⟩ := hUV x ⟨hy, hsupp h⟩
        exact hyQ ⟨u', (Metric.ball_subset_closedBall.trans (hrΩ x)) hu', hu'y⟩
      have hfarL : ∀ u ∈ Ω x, u ∉ Metric.closedBall (0 : ComplexModel V.dim) (r x) →
          g b (Q.toManifold u) = 0 := fun u hu hub => by
        have hnot : Q.toManifold u ∉ tsupport (ρ b) := fun h =>
          hub (Metric.ball_subset_closedBall (hball u (hΩd x hu) h))
        simp only [hgdef, image_eq_zero_of_notMem_tsupport hnot, zero_mul]
      -- the two density fields
      set YL : RegularPatch V → ComplexModel V.dim → ℝ := fun P' u =>
        g b (P'.toManifold u) * patchMixedDensity (Function.update a i₀ (ddcForm w hw)) P' u with hYL
      set YR : RegularPatch V → ComplexModel V.dim → ℝ := fun P' u =>
        w (P'.toManifold u) * patchMixedDensity (Function.update a i₀ (ddcForm (g b) (hgs b))) P' u
        with hYR
      have hYLf : IsDensityField YL := (isDensityField_patchMixedDensity _).mul_comp (g b)
      have hYRf : IsDensityField YR := (isDensityField_patchMixedDensity _).mul_comp w
      have hvanL : ∀ j w', w' ∈ D.piece j → (D.patch j).toManifold w' ∉ Q.toManifold '' Ω x →
          YL (D.patch j) w' = 0 := fun j w' hw' hnot => by
        have h := hoff _ (RegularPatch.toManifold_mem_carrier _ (D.piece_subset j hw')) hnot
        simp only [hYL, hgdef, image_eq_zero_of_notMem_tsupport h, zero_mul]
      have hvanR : ∀ j w', w' ∈ D.piece j → (D.patch j).toManifold w' ∉ Q.toManifold '' Ω x →
          YR (D.patch j) w' = 0 := fun j w' hw' hnot => by
        have hV := RegularPatch.toManifold_mem_carrier _ (D.piece_subset j hw')
        simp only [hYR]
        rw [patchMixedDensity_update_ddcForm_eq_zero _ a i₀ (hgs b) (D.piece_subset j hw')
          (hgvan b _ hV (hoff _ hV hnot)), mul_zero]
      have hmeasL : ∀ j, AEStronglyMeasurable (YL (D.patch j)) (volume.restrict (D.piece j)) :=
        fun j => ((continuousOn_mul_patchMixedDensity _ _ (hgs b)).mono
          (D.piece_subset j)).aestronglyMeasurable (D.measurableSet_piece j)
      have hmeasR : ∀ j, AEStronglyMeasurable (YR (D.patch j)) (volume.restrict (D.piece j)) :=
        fun j => ((continuousOn_mul_patchMixedDensity _ _ hw).mono
          (D.piece_subset j)).aestronglyMeasurable (D.measurableSet_piece j)
      have hcb : Metric.closedBall (0 : ComplexModel V.dim) (r x) ⊆ Q.parameterDomain :=
        (hrΩ x).trans (hΩd x)
      have hintL : IntegrableOn (YL Q) (Ω x) := by
        refine IntegrableOn.of_forall_sdiff_eq_zero (s := Metric.closedBall (0 : ComplexModel V.dim) (r x)) ?_
          (hΩo x).measurableSet fun u hu => ?_
        · exact ((continuousOn_mul_patchMixedDensity _ _ (hgs b)).mono hcb).integrableOn_compact
            (isCompact_closedBall _ _)
        · simp only [hYL, hfarL u hu.1 hu.2, zero_mul]
      have hintR : IntegrableOn (YR Q) (Ω x) := by
        refine IntegrableOn.of_forall_sdiff_eq_zero (s := Metric.closedBall (0 : ComplexModel V.dim) (r x)) ?_
          (hΩo x).measurableSet fun u hu => ?_
        · exact ((continuousOn_mul_patchMixedDensity _ _ hw).mono hcb).integrableOn_compact
            (isCompact_closedBall _ _)
        · have hnot : Q.toManifold u ∉ tsupport (ρ b) := fun h =>
            hu.2 (Metric.ball_subset_closedBall (hball u (hΩd x hu.1) h))
          simp only [hYR]
          rw [patchMixedDensity_update_ddcForm_eq_zero _ a i₀ (hgs b) (hΩd x hu.1)
            (hgvan b _ (RegularPatch.toManifold_mem_carrier Q (hΩd x hu.1)) hnot), mul_zero]
      obtain ⟨hIL, hEL⟩ := D.integrable_measure_and_integral_eq hYLf Q (hΩo x).measurableSet
        (hΩd x) hvanL hmeasL hintL
      obtain ⟨hIR, hER⟩ := D.integrable_measure_and_integral_eq hYRf Q (hΩo x).measurableSet
        (hΩd x) hvanR hmeasR hintR
      refine ⟨hIL, hIR, ?_⟩
      change ∫ x, YL (D.patch x.1) x.2 ∂D.measure = ∫ x, YR (D.patch x.1) x.2 ∂D.measure
      rw [hEL, hER]
      exact setIntegral_patch_ibp Q (hΩo x) (hΩd x) i₀ (hφ x) (hpot x) (hgs b) hw
        (isCompact_closedBall _ _) (hrΩ x) hfarL
  -- assemble
  have hLsum : (fun x : ℕ × ComplexModel V.dim => χ ((D.patch x.1).toManifold x.2) *
      patchMixedDensity (Function.update a i₀ (ddcForm w hw)) (D.patch x.1) x.2) =
      fun x => ∑ b, FL b x := by
    funext x
    simp only [hFL, ← Finset.sum_mul, hsumg]
  have hRsum : (fun x : ℕ × ComplexModel V.dim => w ((D.patch x.1).toManifold x.2) *
      patchMixedDensity (Function.update a i₀ (ddcForm χ hχ)) (D.patch x.1) x.2) =ᵐ[D.measure]
      fun x => ∑ b, FR b x := (ae_mem_piece D).mono fun x hx => by
    simp only [hFR, ← Finset.mul_sum]
    rw [patchMixedDensity_update_ddcForm_sum _ a i₀ hgs hχ hsumg (D.piece_subset x.1 hx)]
  have hIL : Integrable (fun x => ∑ b, FL b x) D.measure :=
    integrable_finsetSum _ fun b _ => (hterm b).1
  have hIR : Integrable (fun x => ∑ b, FR b x) D.measure :=
    integrable_finsetSum _ fun b _ => (hterm b).2.1
  refine ⟨hLsum ▸ hIL, hIR.congr hRsum.symm, ?_⟩
  rw [hLsum, integral_congr_ae hRsum, integral_finsetSum _ fun b _ => (hterm b).1,
    integral_finsetSum _ fun b _ => (hterm b).2.1]
  exact Finset.sum_congr rfl fun b _ => (hterm b).2.2

end

end SGPT.Foundations.Analysis.Pending.StokesPatchIBP
