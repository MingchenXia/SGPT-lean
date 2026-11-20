import SGPT.Foundations.Analysis.Pending.ConstantRankSubmanifold
import SGPT.Foundations.Analysis.Pending.RegularAtDimChart
import SGPT.Foundations.Analysis.Pending.CodimOneSupport
import SGPT.Foundations.Analysis.FirstPass.LocalHolomorphicInverse

/-!
# The image of a holomorphic immersion is a submanifold


Let `F : N → M` be holomorphic near `x`, from a complex manifold of dimension `d`, with injective
differential at `x`, and let `A ⊆ M` contain `F(y)` for `y` near `x` and be covered near `F x` by
the images of the neighbourhoods of `x` (`F` is open onto `A` at `x`).  Then `A` is a regular point
of dimension `d` at `F x` (`regularAtDim_of_immersion`).  In charts, a linear left inverse `Q` of
`dF_x` makes `Q ∘ F` a local biholomorphism, and `A` is the graph of `F ∘ (Q ∘ F)⁻¹` over the
linear projection `Q` (`ConstantRankSubmanifold.regularAtDim_graph`).

Two cases: holomorphic sections (`regularAtDim_of_section`: the image of a holomorphic section
of a holomorphic map over an open set is a submanifold of the dimension of the base), and
local parametrizations of an analytic set by a smooth model.
-/

set_option autoImplicit false

open Set Filter
open scoped Topology Manifold ContDiff

noncomputable section

namespace SGPT.GAGA.AlgPrimes3

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending

variable {d K : ℕ} {N M : Type*} [TopologicalSpace N] [ChartedSpace (ComplexModel d) N]
  [IsComplexManifold d N] [TopologicalSpace M] [ChartedSpace (ComplexModel K) M]
  [IsComplexManifold K M]

/-- **The image of a holomorphic immersion is a submanifold.**  If `F : N → M` is holomorphic
near `x` with injective differential at `x`, `F y ∈ A` for `y` near `x`, and every neighbourhood
of `x` is mapped onto a neighbourhood of `F x` in `A`, then `A` is regular of dimension `dim N` at
`F x`. -/
theorem regularAtDim_of_immersion {F : N → M} {x : N}
    (hF : ∀ᶠ y in 𝓝 x, ContMDiffAt 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel K) ∞ F y)
    (hinj : Function.Injective (mfderiv 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel K) F x))
    {A : Set M} (hA : ∀ᶠ y in 𝓝 x, F y ∈ A)
    (hloc : ∀ U ∈ 𝓝 x, ∃ V ∈ 𝓝 (F x), A ∩ V ⊆ F '' U) :
    RegularAtDim (n := K) A (F x) d := by
  classical
  obtain ⟨O, hOsub, hOo, hxO⟩ := mem_nhds_iff.mp (hF.and hA)
  have hFO : ContMDiffOn 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel K) ∞ F O :=
    fun y hy => (hOsub hy).1.contMDiffWithinAt
  set e := chartAt (ComplexModel d) x with he
  set e' := chartAt (ComplexModel K) (F x) with he'
  have hxe : x ∈ e.source := mem_chart_source _ x
  have hFxe' : F x ∈ e'.source := mem_chart_source _ (F x)
  set G : ComplexModel d → ComplexModel K := fun u => e' (F (e.symm u)) with hG
  set U0 : Set (ComplexModel d) := e.target ∩ e.symm ⁻¹' (O ∩ F ⁻¹' e'.source) with hU0
  have hU0o : IsOpen U0 :=
    e.continuousOn_symm.isOpen_inter_preimage e.open_target
      (hFO.continuousOn.isOpen_inter_preimage hOo e'.open_source)
  have hpU0 : e x ∈ U0 := ⟨e.map_source hxe, by
    rw [mem_preimage, e.left_inv hxe]
    exact ⟨hxO, hFxe'⟩⟩
  have hGd : DifferentiableOn ℂ G U0 := by
    have h := (contMDiffOn_iff.mp hFO).2 x (F x)
    refine (h.differentiableOn (by simp)).mono ?_
    intro u hu
    simp only [mfld_simps]
    exact ⟨hu.1, hu.2.1, hu.2.2⟩
  -- the derivative of `G` at `e x` is the differential of `F`
  have hmd : MDifferentiableAt 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel K) F x :=
    ((hOsub hxO).1).mdifferentiableAt (by simp)
  have hderiv : mfderiv 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel K) F x = fderiv ℂ G (e x) := by
    rw [hmd.mfderiv]
    simp only [mfld_simps, fderivWithin_univ]
    rfl
  set L := fderiv ℂ G (e x) with hL
  have hLinj : Function.Injective L := by
    rw [← hderiv]
    exact hinj
  -- a linear left inverse `Q` of `L`
  obtain ⟨Q₀, hQ₀⟩ := LinearMap.exists_leftInverse_of_injective
    (L : ComplexModel d →ₗ[ℂ] ComplexModel K) (LinearMap.ker_eq_bot.mpr hLinj)
  set Q : ComplexModel K →L[ℂ] ComplexModel d := LinearMap.toContinuousLinearMap Q₀ with hQ
  have hQL : ∀ v, Q (L v) = v := fun v => by
    change Q₀ (L v) = v
    exact congrArg (fun φ : ComplexModel d →ₗ[ℂ] ComplexModel d => φ v) hQ₀
  -- `H = Q ∘ G` is a local biholomorphism at `e x`
  set H : ComplexModel d → ComplexModel d := fun u => Q (G u) with hH
  have hHd : DifferentiableOn ℂ H U0 := Q.differentiable.comp_differentiableOn hGd
  have hGda : DifferentiableAt ℂ G (e x) := hGd.differentiableAt (hU0o.mem_nhds hpU0)
  have hHderiv : fderiv ℂ H (e x) = Q.comp L :=
    (Q.hasFDerivAt.comp (e x) hGda.hasFDerivAt).fderiv
  have hHinj : Function.Injective (fderiv ℂ H (e x)) := by
    rw [hHderiv]
    intro v w hvw
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply] at hvw
    rw [← hQL v, ← hQL w]
    exact hvw
  obtain ⟨Ξ, hΞsub, hΞeq, -⟩ := FirstPass.exists_localHolomorphicEquivAt hU0o hpU0 hHd hHinj
  -- the graph parametrization
  set k : ComplexModel d → ComplexModel K := fun w => G (Ξ.invFun w) with hk
  have hkd : DifferentiableOn ℂ k Ξ.target :=
    hGd.comp Ξ.invFun_holomorphic fun w hw => hΞsub (Ξ.mapsTo_invFun hw)
  have hQk : ∀ w ∈ Ξ.target, Q (k w) = w := by
    intro w hw
    change H (Ξ.invFun w) = w
    rw [← hΞeq]
    exact Ξ.right_inv w hw
  have hpΞ : e x ∈ Ξ.source := Ξ.center_mem_source
  have hQGp : Q (G (e x)) ∈ Ξ.target := by
    change H (e x) ∈ Ξ.target
    rw [← hΞeq]
    exact Ξ.mapsTo_toFun hpΞ
  have hkGp : k (Q (G (e x))) = G (e x) := by
    change G (Ξ.invFun (H (e x))) = G (e x)
    rw [← hΞeq, Ξ.left_inv _ hpΞ]
  set S : Set (ComplexModel K) := {z | Q z ∈ Ξ.target ∧ k (Q z) = z} with hS
  have hSreg : RegularAtDim (n := K) (M := ComplexModel K) S (G (e x)) d := by
    have h := ConstantRankSubmanifold.regularAtDim_graph Q Ξ.isOpen_target hkd hQk hQGp hkGp
    rwa [finrank_euclideanSpace_fin] at h
  have hGx : G (e x) = e' (F x) := by
    simp only [hG, e.left_inv hxe]
  -- `S` is the image `G(Ξ.source)`
  have hSimage : ∀ z, z ∈ S ↔ ∃ u ∈ Ξ.source, G u = z := by
    intro z
    constructor
    · rintro ⟨hz1, hz2⟩
      exact ⟨Ξ.invFun (Q z), Ξ.mapsTo_invFun hz1, hz2⟩
    · rintro ⟨u, hu, rfl⟩
      have hHu : Q (G u) = Ξ.toFun u := by rw [hΞeq]
      refine ⟨?_, ?_⟩
      · rw [hHu]
        exact Ξ.mapsTo_toFun hu
      · change G (Ξ.invFun (Q (G u))) = G u
        rw [hHu, Ξ.left_inv u hu]
  -- the neighbourhood of `x` corresponding to `Ξ.source`
  set U : Set N := e.source ∩ e ⁻¹' Ξ.source with hUdef
  have hUo : IsOpen U := e.isOpen_inter_preimage Ξ.isOpen_source
  have hxU : x ∈ U := ⟨hxe, hpΞ⟩
  obtain ⟨V, hV, hAV⟩ := hloc U (hUo.mem_nhds hxU)
  -- `A` and `e'⁻¹ S` agree near `F x`
  have hUO : ∀ y ∈ U, y ∈ O ∧ F y ∈ e'.source := by
    intro y hy
    have h1 : e y ∈ U0 := hΞsub hy.2
    have h2 := h1.2
    rw [mem_preimage, e.left_inv hy.1] at h2
    exact h2
  have hGy : ∀ y ∈ U, G (e y) = e' (F y) := fun y hy => by
    simp only [hG, e.left_inv hy.1]
  have hset : ∀ z ∈ V ∩ e'.source, z ∈ A ↔ e' z ∈ S := by
    rintro z ⟨hzV, hze'⟩
    constructor
    · intro hzA
      obtain ⟨y, hyU, rfl⟩ := hAV ⟨hzA, hzV⟩
      exact (hSimage _).mpr ⟨e y, hyU.2, hGy y hyU⟩
    · intro hzS
      obtain ⟨u, hu, hGu⟩ := (hSimage _).mp hzS
      have hu0 : u ∈ U0 := hΞsub hu
      have hy : e.symm u ∈ O ∧ F (e.symm u) ∈ e'.source := hu0.2
      have hzeq : F (e.symm u) = z := by
        rw [← e'.left_inv hy.2, ← e'.left_inv hze']
        exact congrArg e'.symm hGu
      rw [← hzeq]
      exact (hOsub hy.1).2
  -- transfer to `M` through the chart `e'`
  have hreg1 : RegularAtDim (n := K) (M := ComplexModel K) (S ∩ e'.target) (e' (F x)) d := by
    rw [← hGx]
    refine RegularPointDimension.regularAtDim_of_inter_eq (W := e'.target) e'.open_target
      (by rw [hGx]; exact e'.map_source hFxe') ?_ hSreg
    rw [inter_assoc, inter_self]
  have hreg2 : RegularAtDim (n := K) (e'.source ∩ e' ⁻¹' S) (F x) d :=
    (RegularAtDimChart.regularAtDim_chart_iff (complexChartAt (n := K) (F x)) S hFxe').mpr hreg1
  have hVo : V ∩ e'.source ∈ 𝓝 (F x) := inter_mem hV (e'.open_source.mem_nhds hFxe')
  refine CodimOneSupport.regularAtDim_of_eventually_mem_iff ?_ hreg2
  filter_upwards [hVo] with z hz
  constructor
  · rintro ⟨-, hzS⟩
    exact (hset z hz).mpr hzS
  · intro hzA
    exact ⟨hz.2, (hset z hz).mp hzA⟩

/-- **The image of a holomorphic section is a submanifold.**  Let `π : M → N` be holomorphic and
`s` a holomorphic section of `π` over the open set `W ⊆ N`.  If `A ∩ π⁻¹ W = s(W)`, then `A` is
regular of dimension `dim N` at every point `s x`, `x ∈ W`. -/
theorem regularAtDim_of_section {π : M → N}
    (hπ : ContMDiff 𝓘(ℂ, ComplexModel K) 𝓘(ℂ, ComplexModel d) ∞ π) {W : Set N} (hW : IsOpen W)
    {s : N → M} (hs : ContMDiffOn 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel K) ∞ s W)
    (hπs : ∀ x ∈ W, π (s x) = x) {A : Set M} (hsA : ∀ x ∈ W, s x ∈ A)
    (hAs : ∀ z ∈ A, π z ∈ W → s (π z) = z) {x : N} (hx : x ∈ W) :
    RegularAtDim (n := K) A (s x) d := by
  have hsx : ContMDiffAt 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel K) ∞ s x :=
    hs.contMDiffAt (hW.mem_nhds hx)
  refine regularAtDim_of_immersion ?_ ?_ ?_ ?_
  · filter_upwards [hW.mem_nhds hx] with y hy
    exact hs.contMDiffAt (hW.mem_nhds hy)
  · -- `dπ ∘ ds = id`
    have hπd : MDifferentiableAt 𝓘(ℂ, ComplexModel K) 𝓘(ℂ, ComplexModel d) π (s x) :=
      (hπ (s x)).mdifferentiableAt (by simp)
    have hsd : MDifferentiableAt 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel K) s x :=
      hsx.mdifferentiableAt (by simp)
    have heq : (π ∘ s) =ᶠ[𝓝 x] id := by
      filter_upwards [hW.mem_nhds hx] with y hy
      exact hπs y hy
    have h1 := mfderiv_comp x hπd hsd
    rw [heq.mfderiv_eq, mfderiv_id] at h1
    intro v w hvw
    have hv : (mfderiv 𝓘(ℂ, ComplexModel K) 𝓘(ℂ, ComplexModel d) π (s x))
        ((mfderiv 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel K) s x) v) = v :=
      (congrArg (fun L => L v) h1).symm
    have hw : (mfderiv 𝓘(ℂ, ComplexModel K) 𝓘(ℂ, ComplexModel d) π (s x))
        ((mfderiv 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel K) s x) w) = w :=
      (congrArg (fun L => L w) h1).symm
    rw [← hv, ← hw, hvw]
  · filter_upwards [hW.mem_nhds hx] with y hy
    exact hsA y hy
  · intro U hU
    refine ⟨π ⁻¹' (interior U ∩ W), ?_, ?_⟩
    · refine (hπ.continuous.isOpen_preimage _ (isOpen_interior.inter hW)).mem_nhds ?_
      rw [mem_preimage, hπs x hx]
      exact ⟨mem_interior_iff_mem_nhds.mpr hU, hx⟩
    · rintro z ⟨hzA, hzU, hzW⟩
      exact ⟨π z, interior_subset hzU, hAs z hzA hzW⟩

end SGPT.GAGA.AlgPrimes3

end
