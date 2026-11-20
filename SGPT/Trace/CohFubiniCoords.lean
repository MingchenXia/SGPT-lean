import SGPT.Trace.CohFibIeq
import SGPT.Foundations.Analysis.Pending.BlowupSNCTransform

/-!
# Coordinates adapted to a submersion onto `Δ*`

Infrastructure of lane COHERENT (source `lma:fibIeq`; blueprint `claude-coherent.tex`, node
`claude-coherent:ae-reverse`).

Let `f : X → Δ*` be holomorphic on a complex manifold of dimension `b + 1` with surjective
differential at `x`. Then (`exists_fibre_theta`) there is a local biholomorphism `Θ` of `ℂ^{b+1}`
at `e(x)` (`e` the preferred chart at `x`), with `Θ(e x) = 0`, whose **last coordinate is the
coordinate of `f`**: `Θ(e u)_b = t(u) - t(x)`. Thus near `x` every fibre `X_z` is the slice
`{Θ_b = z - t(x)}`. The construction is that of `SGPT.Trace.DirectImg.exists_fibre_coords`
(`W = (L(e u - e x), t(u) - t(x))`, `L` injective on `ker dt`), recentred by
`BlowupSNCTransform.exists_recentred_coords`, keeping track of the last coordinate.

`IsSmoothMorphism`-type input: `surjective_chartDeriv_of_generator` shows that a
rotation-equivariant `f` (for a `C¹` circle action) has surjective differential everywhere.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open Set Filter
open scoped Topology Manifold ContDiff

namespace SGPT.Trace.CohFib

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.RankDegeneracy SGPT.GAGA.Coherent SGPT.Trace.DirectImg

variable {b : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel (b + 1)) X]
  [IsComplexManifold (b + 1) X] {f : X → puncturedDisc}

/-- **Coordinates adapted to `f`.** -/
theorem exists_fibre_theta
    (hf : ContMDiff 𝓘(ℂ, ComplexModel (b + 1)) 𝓘(ℂ, ComplexModel 1) ∞ f) {x : X}
    (hD : Function.Surjective (chartDeriv (complexChartAt (n := b + 1) x)
      (complexChartAt (n := 1) (f x)) f x)) :
    ∃ Θ : LocalHolomorphicEquivAt (n := b + 1) ((complexChartAt (n := b + 1) x).val x),
      Θ.source ⊆ (complexChartAt (n := b + 1) x).val.target ∧
      Θ.toFun ((complexChartAt (n := b + 1) x).val x) = 0 ∧
      ∀ {u : X}, u ∈ (complexChartAt (n := b + 1) x).val.source →
        (complexChartAt (n := b + 1) x).val u ∈ Θ.source →
          Θ.toFun ((complexChartAt (n := b + 1) x).val u) (Fin.last b) =
            coord f u - coord f x := by
  classical
  set e := complexChartAt (n := b + 1) x with he
  set e' := complexChartAt (n := 1) (f x) with he'
  set z₀ := e.val x with hz₀
  set c := e'.val (f x) with hc
  have hxe : x ∈ e.val.source := mem_complexChartAt_source x
  have hfxe' : f x ∈ e'.val.source := mem_complexChartAt_source (f x)
  set F : ComplexModel (b + 1) → ComplexModel 1 := fun ζ => e'.val (f (e.val.symm ζ)) with hF
  set D := chartDeriv e e' f x with hD'
  have hFd : DifferentiableAt ℂ F z₀ :=
    differentiableAt_chartReading e e' hxe hfxe' (hf.mdifferentiableAt (by simp))
  have hDF : fderiv ℂ F z₀ = D := rfl
  set K := LinearMap.ker (D : ComplexModel (b + 1) →ₗ[ℂ] ComplexModel 1) with hK
  have hKdim : Module.finrank ℂ K = b := by
    have h1 : Module.finrank ℂ (LinearMap.range (D : ComplexModel (b + 1) →ₗ[ℂ] ComplexModel 1)) +
        Module.finrank ℂ K = Module.finrank ℂ (ComplexModel (b + 1)) :=
      LinearMap.finrank_range_add_finrank_ker _
    have h2 : LinearMap.range (D : ComplexModel (b + 1) →ₗ[ℂ] ComplexModel 1) = ⊤ :=
      LinearMap.range_eq_top.mpr hD
    rw [h2, finrank_top] at h1
    simp only [finrank_euclideanSpace_fin] at h1
    omega
  obtain ⟨g₀, hg₀⟩ := LinearMap.exists_leftInverse_of_injective K.subtype K.ker_subtype
  set eK : K ≃ₗ[ℂ] ComplexModel b := LinearEquiv.ofFinrankEq K (ComplexModel b)
    (by rw [hKdim, finrank_euclideanSpace_fin])
  set L : ComplexModel (b + 1) →L[ℂ] ComplexModel b :=
    LinearMap.toContinuousLinearMap (eK.toLinearMap ∘ₗ g₀) with hL
  set P := EuclideanSpace.finAddEquivProd (𝕜 := ℂ) (n := b) (m := 1) with hP
  set W : X → ComplexModel (b + 1) := fun z => P.symm (L (e.val z - z₀), e'.val (f z) - c)
    with hW
  set O : Set X := e.val.source ∩ f ⁻¹' e'.val.source with hO
  have hOopen : IsOpen O := e.val.open_source.inter (e'.val.open_source.preimage hf.continuous)
  have hxO : x ∈ O := ⟨hxe, hfxe'⟩
  have hWs : ∀ z ∈ O, ContMDiffAt 𝓘(ℂ, ComplexModel (b + 1)) 𝓘(ℂ, ComplexModel (b + 1)) ∞ W z := by
    intro z hz
    have h1 : ContMDiffAt 𝓘(ℂ, ComplexModel (b + 1)) 𝓘(ℂ, ComplexModel b) ∞
        (fun z => L (e.val z - z₀)) z :=
      (L.contMDiff.contMDiffAt).comp z
        (((contMDiffOn_chart (n := ∞)).contMDiffAt (e.val.open_source.mem_nhds hz.1)).sub
          contMDiffAt_const)
    have h2 : ContMDiffAt 𝓘(ℂ, ComplexModel (b + 1)) 𝓘(ℂ, ComplexModel 1) ∞
        (fun z => e'.val (f z) - c) z :=
      (((contMDiffOn_chart (n := ∞)).contMDiffAt (e'.val.open_source.mem_nhds hz.2)).comp z
        (hf z)).sub contMDiffAt_const
    exact (P.symm.contDiff.contMDiff.contMDiffAt).comp z (h1.prodMk_space h2)
  have hWinj : Function.Injective (fderiv ℂ (fun ζ => W ((chartAt (ComplexModel (b + 1)) x).symm ζ))
      (chartAt (ComplexModel (b + 1)) x x)) := by
    have hloc : (fun ζ => W (e.val.symm ζ)) =ᶠ[𝓝 z₀]
        fun ζ => P.symm (L (ζ - z₀), F ζ - c) := by
      filter_upwards [e.val.open_target.mem_nhds (e.val.map_source hxe)] with ζ hζ
      simp only [hW, hF, e.val.right_inv hζ]
    have hder : HasFDerivAt (fun ζ => W (e.val.symm ζ))
        ((P.symm : ComplexModel b × ComplexModel 1 →L[ℂ] ComplexModel (b + 1)).comp
          (L.prod D)) z₀ := by
      refine HasFDerivAt.congr_of_eventuallyEq ?_ hloc
      have hL' : HasFDerivAt (fun ζ => L (ζ - z₀)) L z₀ := by
        have := L.hasFDerivAt.comp z₀ ((hasFDerivAt_id z₀).sub_const z₀)
        rw [ContinuousLinearMap.comp_id] at this
        exact this
      have hF' : HasFDerivAt (fun ζ => F ζ - c) D z₀ := by
        rw [← hDF]
        exact hFd.hasFDerivAt.sub_const c
      exact P.symm.hasFDerivAt.comp z₀ (hL'.prodMk hF')
    show Function.Injective (fderiv ℂ (fun ζ => W (e.val.symm ζ)) z₀)
    rw [hder.fderiv]
    refine (injective_iff_map_eq_zero _).mpr fun v hv => ?_
    have hv' : (L.prod D) v = 0 := by
      have h := congrArg P hv
      simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
        ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply, map_zero] at h
      exact h
    have hDv : D v = 0 := congrArg Prod.snd hv'
    have hLv : L v = 0 := congrArg Prod.fst hv'
    have hvK : v ∈ K := hDv
    have h1 : g₀ v = ⟨v, hvK⟩ := by
      have := congrArg (fun ψ => ψ ⟨v, hvK⟩) hg₀
      simpa using this
    have h2 : eK (g₀ v) = 0 := hLv
    rw [h1, LinearEquiv.map_eq_zero_iff] at h2
    exact congrArg Subtype.val h2
  obtain ⟨Θ, hΘt, hΘ0, hΘ⟩ := BlowupSNCTransform.exists_recentred_coords hOopen hWs hxO hWinj
  refine ⟨Θ, hΘt, hΘ0, fun {u} hu huΘ => ?_⟩
  obtain ⟨-, hΘu⟩ := hΘ hu huΘ
  rw [hΘu]
  have hlast : (Fin.last b : Fin (b + 1)) = Fin.natAdd b (0 : Fin 1) := by
    ext; simp
  rw [PiLp.sub_apply, hlast, hW]
  simp only
  rw [DirectImg.finAddEquivProd_symm_natAdd, DirectImg.finAddEquivProd_symm_natAdd, hc, sub_self,
    PiLp.sub_apply, he', complexChartAt, chartAt_puncturedDisc_apply]
  simp only [coord]
  rw [chartAt_puncturedDisc_apply]
  simp

/-- **A rotation-equivariant map is a submersion.** If `f : X → Δ*` is holomorphic and
`f(σ_θ x) = e^{iθ} f(x)` for a `C¹` circle action, then the differential of `f` is surjective at
every point: `θ ↦ t(σ_θ x)` has derivative `i t(x) ≠ 0`, which by the chain rule is `dt_x` applied
to the velocity of the action. -/
theorem surjective_chartDeriv_of_equivariant (σ : CircleAction (b + 1) X)
    (hf : ContMDiff 𝓘(ℂ, ComplexModel (b + 1)) 𝓘(ℂ, ComplexModel 1) ∞ f)
    (hequiv : IsRotationEquivariant σ f) (x : X) :
    Function.Surjective (chartDeriv (complexChartAt (n := b + 1) x)
      (complexChartAt (n := 1) (f x)) f x) := by
  set e := complexChartAt (n := b + 1) x with he
  set e' := complexChartAt (n := 1) (f x) with he'
  have hxe : x ∈ e.val.source := mem_complexChartAt_source x
  have hfxe' : f x ∈ e'.val.source := mem_complexChartAt_source (f x)
  set F : ComplexModel (b + 1) → ComplexModel 1 := fun ζ => e'.val (f (e.val.symm ζ)) with hF
  set D := chartDeriv e e' f x with hD
  have hFd : HasFDerivAt F D (e.val x) :=
    (differentiableAt_chartReading e e' hxe hfxe' (hf.mdifferentiableAt (by simp))).hasFDerivAt
  -- the velocity of the action at `x`, read in the chart
  set Fl : ℝ → ComplexModel (b + 1) := fun θ => σ.chartFlow x (θ, e.val x) with hFl
  have hFl0 : Fl 0 = e.val x := by
    simp only [hFl, CircleAction.chartFlow, σ.act_zero]
    exact (chartAt (ComplexModel (b + 1)) x).right_inv
      ((chartAt (ComplexModel (b + 1)) x).map_source (mem_chart_source _ x))
  have hFld : HasDerivAt Fl (fderiv ℝ (σ.chartFlow x) ((0 : ℝ), e.val x) ((1 : ℝ), 0)) 0 := by
    have h1 : HasFDerivAt (σ.chartFlow x) (fderiv ℝ (σ.chartFlow x) ((0 : ℝ), e.val x))
        ((0 : ℝ), e.val x) :=
      ((σ.contDiffAt_chartFlow x).differentiableAt one_ne_zero).hasFDerivAt
    exact h1.comp_hasDerivAt (0 : ℝ) (hasDerivAt_pair (0 : ℝ) (e.val x))
  have hcomp : HasDerivAt (fun θ => F (Fl θ))
      (D (fderiv ℝ (σ.chartFlow x) ((0 : ℝ), e.val x) ((1 : ℝ), 0))) 0 := by
    have h := (hFd.restrictScalars ℝ)
    rw [← hFl0] at h
    exact h.comp_hasDerivAt 0 hFld
  have hproj := ((EuclideanSpace.proj (0 : Fin 1) : ComplexModel 1 →L[ℂ] ℂ).restrictScalars
    ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hcomp
  -- the same function is `θ ↦ e^{iθ} t(x)` near `0`
  have hT : Tendsto (fun θ : ℝ => σ.act θ x) (𝓝 0) (𝓝 x) := σ.tendsto_act_zero x
  have heq : (fun θ => (EuclideanSpace.proj (0 : Fin 1) : ComplexModel 1 →L[ℂ] ℂ) (F (Fl θ)))
      =ᶠ[𝓝 0] fun θ : ℝ => Complex.exp (θ * Complex.I) * coord f x := by
    filter_upwards [hT.eventually (e.val.open_source.mem_nhds hxe)] with θ hθ
    have h1 : Fl θ = chartAt (ComplexModel (b + 1)) x (σ.act θ x) := by
      show chartAt (ComplexModel (b + 1)) x (σ.act θ ((chartAt (ComplexModel (b + 1)) x).symm
        (chartAt (ComplexModel (b + 1)) x x))) = _
      rw [(chartAt (ComplexModel (b + 1)) x).left_inv hxe]
    have h2 : F (Fl θ) = (f (σ.act θ x) : ComplexModel 1) := by
      rw [h1]
      show chartAt (ComplexModel 1) (f x) (f ((chartAt (ComplexModel (b + 1)) x).symm
        (chartAt (ComplexModel (b + 1)) x (σ.act θ x)))) = _
      rw [(chartAt (ComplexModel (b + 1)) x).left_inv hθ]
      exact chartAt_puncturedDisc_apply _ _
    show (EuclideanSpace.proj (0 : Fin 1) : ComplexModel 1 →L[ℂ] ℂ) (F (Fl θ)) = _
    rw [h2]
    exact coord_act hequiv θ x
  have hexp : HasDerivAt (fun θ : ℝ => Complex.exp (θ * Complex.I) * coord f x)
      (Complex.I * coord f x) 0 := by
    have h := (((hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const Complex.I).cexp).mul_const
      (coord f x)
    simpa using h
  have hunique := (hproj.congr_of_eventuallyEq heq.symm).unique hexp
  -- hence `D ≠ 0`, and a nonzero functional onto `ℂ¹` is surjective
  have hDv : D (fderiv ℝ (σ.chartFlow x) ((0 : ℝ), e.val x) ((1 : ℝ), 0)) ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hunique
    exact mul_ne_zero Complex.I_ne_zero (coord_ne_zero f x) hunique.symm
  set v := fderiv ℝ (σ.chartFlow x) ((0 : ℝ), e.val x) ((1 : ℝ), 0) with hv
  have hDv0 : (D v) 0 ≠ 0 := by
    intro h0
    apply hDv
    ext i
    fin_cases i
    simpa using h0
  intro w
  refine ⟨(w 0 / (D v) 0) • v, ?_⟩
  rw [map_smul]
  ext i
  have hi : i = 0 := Subsingleton.elim _ _
  subst hi
  simp only [PiLp.smul_apply, smul_eq_mul]
  field_simp

end SGPT.Trace.CohFib
