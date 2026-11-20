import SGPT.GAGA.ChowBlPoint
import SGPT.Foundations.Analysis.Pending.BlowupIsomorphismOff
import SGPT.Foundations.Analysis.Pending.BlowupCompact
import SGPT.Foundations.Analysis.Pending.BlowupConnected
import SGPT.GAGA.SmoothFlagsScheme

/-!
# The blow-up of a projective manifold along a smooth centre is projective


Setting `BlData`: `Ψ : M → ℙᴺ` a holomorphic embedding of a compact complex manifold, `π : Y → M`
the blow-up along `C`, `P_0, …, P_r` homogeneous of degree `m` generating the ideal of the cone
over `Ψ(C)`.  The map

  `blowupEmbedding = Segre ∘ (Ψ ∘ π, blowupMap) : Y → ℙᴺ × ℙʳ → ℙ^{(N+1)(r+1)-1}`

is a holomorphic embedding (`isHolomorphicEmbedding_blowupEmbedding`):

* lifts: near `p`, `[F₁ ⊗ w]` with `F₁` the affine lift of `Ψ ∘ π` and `w` a representation of
  `blowupMap` (`lift_of_rep`);
* immersion off `π⁻¹(C)`: `π` is a local biholomorphism there (`joint_of_not_mem`);
* immersion on `π⁻¹(C)` (`joint_of_mem`): if `dF₁ v ∈ ℂ F₁` then `dπ v = 0`; writing
  `π = γⱼ ∘ W` (`exists_monomialInverse`) this gives `dσⱼ(ξ) = 0` for `ξ = dW v`; then
  `w = αⱼ · ũ ∘ W` and `dũ ξ = B(x₀) ξ'` (`fderiv_tildeU_apply`) together with
  `c(x₀) b(x₀) = 1` force `ξ = 0`, and `ℓⱼ ∘ W = id` gives `v = 0`;
* injectivity (`blowupEmbedding_injective`): off `π⁻¹(C)` `π` is injective; over `x₀ ∈ C` the
  value `[b(x₀) α]` of `blowupMap` determines `[α]`, hence `W`, hence the point `ℓⱼ(W)`.

Consequently (`exists_isHolomorphicEmbedding_of_isBlowupAlong`, with Chow's theorem
`chow_image`) every blow-up of a projective manifold along a smooth centre is projective, and so
is every finite tower of such blow-ups (`exists_isHolomorphicEmbedding_of_isBlowupSequence`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Filter Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.Pending.BlowupFlatCoordinates
open SGPT.Foundations.Analysis.Pending.BlowupMonomialCharts
open SGPT.Foundations.Analysis.Pending.BlowupLocalSurjectivity
open SGPT.GAGA.H0S
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open scoped Manifold ContDiff

noncomputable section

namespace SGPT.GAGA.ChowBl

universe u

variable {n N r m : ℕ} {M Y : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] [CompactSpace M] [TopologicalSpace Y]
  [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  {Ψ : M → ComplexProjectiveSpace N} {C : Set M} {π : Y → M}
  {P : Fin (r + 1) → MvPolynomial (Fin (N + 1)) ℂ}

variable (Ψ π P) in
/-- **The projective embedding of the blow-up**: `y ↦ Segre(Ψ(π y), blowupMap y)`. -/
def blowupEmbedding (y : Y) : ComplexProjectiveSpace (segreDim N r) :=
  segreMap (Ψ (π y)) (blowupMap Ψ π P y)

variable (Ψ π) in
/-- The affine lift of `Ψ ∘ π`, read in the chart of `Y` at `p`. -/
def baseLift (p : Y) (z : ComplexModel n) : Fin (N + 1) → ℂ :=
  affineLift (chartIndex (Ψ (π p)))
    (affineChart (chartIndex (Ψ (π p))) (Ψ (π ((chartAt (ComplexModel n) p).symm z))))

variable (π) in
/-- The chart expression of `π` at `p`. -/
def chartExpr (p : Y) (z : ComplexModel n) : ComplexModel n :=
  chartAt (ComplexModel n) (π p) (π ((chartAt (ComplexModel n) p).symm z))

theorem tendsto_chart_symm (p : Y) :
    Tendsto (chartAt (ComplexModel n) p).symm (𝓝 (chartAt (ComplexModel n) p p)) (𝓝 p) := by
  have h := (chartAt (ComplexModel n) p).continuousAt_symm
    ((chartAt (ComplexModel n) p).map_source (mem_chart_source _ p))
  have := h.tendsto
  rwa [(chartAt (ComplexModel n) p).left_inv (mem_chart_source _ p)] at this

/-- **The base lift.**  `Ψ ∘ π = [F₁]` near `p`, and `dF₁ v ∈ ℂ F₁` forces `dπ v = 0`. -/
theorem baseLift_props (hd : BlData n m Ψ C π P) (p : Y) :
    (∀ᶠ z in 𝓝 (chartAt (ComplexModel n) p p), DifferentiableAt ℂ (baseLift Ψ π p) z ∧
      Ψ (π ((chartAt (ComplexModel n) p).symm z)) = pmk (baseLift Ψ π p z)) ∧
    DifferentiableAt ℂ (chartExpr π p) (chartAt (ComplexModel n) p p) ∧
    ∀ v, (∃ c : ℂ, fderiv ℂ (baseLift Ψ π p) (chartAt (ComplexModel n) p p) v =
      c • baseLift Ψ π p (chartAt (ComplexModel n) p p)) →
      fderiv ℂ (chartExpr π p) (chartAt (ComplexModel n) p p) v = 0 := by
  set i := chartIndex (Ψ (π p))
  have hi : Ψ (π p) ∈ (affineChart i).source := mem_affineChart_chartIndex _
  have hπs : ∀ y, ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ π y :=
    fun y => hd.blowup.contMDiff y
  have hps : p ∈ (chartAt (ComplexModel n) p).source := mem_chart_source _ p
  have hT := tendsto_chart_symm (n := n) p
  -- differentiability of the base lift
  have hcomp : ∀ α : Fin (N + 1), HolomorphicAt n (fun y => (coneLift Ψ i (π y)) α) p := by
    intro α
    exact HolomorphicAt.comp_contMDiff (b := fun x => coneLift Ψ i x α)
      (holomorphicAt_comp_coneLift hd.emb hi (c := fun Z => Z α)
        (Eventually.of_forall fun _ => (EuclideanSpace.proj (𝕜 := ℂ) α).differentiableAt))
      (Eventually.of_forall hπs)
  have hd1 := eventually_differentiableAt_chart (n := n) (f := fun y α => (coneLift Ψ i (π y)) α)
    hcomp
  have hsrc : ∀ᶠ z in 𝓝 (chartAt (ComplexModel n) p p),
      Ψ (π ((chartAt (ComplexModel n) p).symm z)) ∈ (affineChart i).source :=
    hT.eventually ((hd.emb.continuous.comp hd.blowup.contMDiff.continuous).continuousAt.eventually
      ((affineChart i).open_source.mem_nhds hi))
  have hτd : DifferentiableAt ℂ (chartExpr π p) (chartAt (ComplexModel n) p p) :=
    differentiableAt_chart_of_mdifferentiableAt ((hπs p).mdifferentiableAt (by simp))
  refine ⟨?_, hτd, ?_⟩
  · filter_upwards [hd1, hsrc] with z hz hzs
    refine ⟨hz, ?_⟩
    rw [baseLift, pmk_eq_mk (affineLift_ne_zero _ _)]
    exact ((affineChart i).left_inv hzs).symm
  · rintro v ⟨c, hc⟩
    obtain ⟨hev, himm⟩ := exists_lift_of_isHolomorphicEmbedding hd.emb (π p) hi
    have hsrcM : ∀ᶠ z in 𝓝 (chartAt (ComplexModel n) p p),
        π ((chartAt (ComplexModel n) p).symm z) ∈ (chartAt (ComplexModel n) (π p)).source :=
      hT.eventually (hd.blowup.contMDiff.continuous.continuousAt.eventually
        ((chartAt (ComplexModel n) (π p)).open_source.mem_nhds (mem_chart_source _ _)))
    have hFeq : baseLift Ψ π p =ᶠ[𝓝 (chartAt (ComplexModel n) p p)]
        fun z => affineLift i (chartMap (n := n) Ψ (π p) i (chartExpr π p z)) := by
      filter_upwards [hsrcM] with z hz
      simp only [baseLift, chartMap, chartExpr]
      rw [show (complexChartAt (n := n) (π p)).val = chartAt (ComplexModel n) (π p) from rfl,
        (chartAt (ComplexModel n) (π p)).left_inv hz]
    have hτ0 : chartExpr π p (chartAt (ComplexModel n) p p) =
        (complexChartAt (n := n) (π p)).val (π p) := by
      simp only [chartExpr, (chartAt (ComplexModel n) p).left_inv hps]
      rfl
    have hFMd : DifferentiableAt ℂ (fun z => affineLift i (chartMap (n := n) Ψ (π p) i z))
        (chartExpr π p (chartAt (ComplexModel n) p p)) := by
      rw [hτ0]; exact hev.self_of_nhds.1
    rw [hFeq.fderiv_eq, fderiv_fun_comp (chartAt (ComplexModel n) p p) hFMd hτd,
      ContinuousLinearMap.comp_apply, hFeq.self_of_nhds] at hc
    have := himm (fderiv ℂ (chartExpr π p) (chartAt (ComplexModel n) p p) v) ⟨c, ?_⟩
    · exact this
    · rw [← hτ0]; exact hc

/-- **Lifts of the blow-up embedding from a representation of `blowupMap`.** -/
theorem lift_of_rep (hd : BlData n m Ψ C π P) (p : Y) {U : Set Y} {h : Y → ℂ}
    {w : Y → Fin (r + 1) → ℂ} (hrep : IsBlRep Ψ π P p (chartIndex (Ψ (π p))) U h w)
    (hw : ∀ q, HolomorphicAt n (fun y => w y q) p)
    (hjoint : ∀ v, (∃ c : ℂ, fderiv ℂ (baseLift Ψ π p) (chartAt (ComplexModel n) p p) v =
        c • baseLift Ψ π p (chartAt (ComplexModel n) p p)) →
      (∃ c : ℂ, fderiv ℂ (fun z => w ((chartAt (ComplexModel n) p).symm z))
        (chartAt (ComplexModel n) p p) v = c • w p) → v = 0) :
    ∃ F : ComplexModel n → Fin (segreDim N r + 1) → ℂ,
      (∀ᶠ z in 𝓝 ((complexChartAt (n := n) p).val p),
        DifferentiableAt ℂ F z ∧ F z ≠ 0 ∧
        blowupEmbedding Ψ π P ((complexChartAt (n := n) p).val.symm z) = pmk (F z)) ∧
      IsProjImmersionAt F ((complexChartAt (n := n) p).val p) := by
  have hps : p ∈ (chartAt (ComplexModel n) p).source := mem_chart_source _ p
  have hT := tendsto_chart_symm (n := n) p
  obtain ⟨hF1, -, -⟩ := baseLift_props hd p
  have hG := eventually_differentiableAt_chart (n := n) hw
  have hw0 : ∀ᶠ z in 𝓝 (chartAt (ComplexModel n) p p),
      w ((chartAt (ComplexModel n) p).symm z) ≠ 0 :=
    hT.eventually (hrep.2.2.2.2.2.1.self_of_nhds.eventually_ne hrep.2.2.2.2.2.2.2)
  have hmap : ∀ᶠ z in 𝓝 (chartAt (ComplexModel n) p p),
      blowupMap Ψ π P ((chartAt (ComplexModel n) p).symm z) =
        pmk (w ((chartAt (ComplexModel n) p).symm z)) := by
    have hmapY : ∀ᶠ y in 𝓝 p, blowupMap Ψ π P y = pmk (w y) := by
      filter_upwards [hrep.eventually hd.emb hd.blowup.contMDiff.continuous] with y hy
      exact blowupMap_eq hd.emb hd.blowup.contMDiff.continuous hd.hom hy
    exact hT.eventually hmapY
  refine ⟨fun z => segreVec (baseLift Ψ π p z) (w ((chartAt (ComplexModel n) p).symm z)), ?_, ?_⟩
  · filter_upwards [hF1, hG, hw0, hmap] with z h1 h2 h3 h4
    refine ⟨?_, segreVec_ne_zero (affineLift_ne_zero _ _) h3, ?_⟩
    · have hd1 := h1.1
      have hd2 := h2
      exact differentiableAt_pi.mpr fun k => (differentiableAt_pi.mp hd1 _).mul
        (differentiableAt_pi.mp hd2 _)
    · show segreMap (Ψ (π ((chartAt (ComplexModel n) p).symm z)))
        (blowupMap Ψ π P ((chartAt (ComplexModel n) p).symm z)) = _
      rw [h1.2, h4]
      exact segreMap_pmk (affineLift_ne_zero _ _) h3
  · refine isProjImmersionAt_segreVec hF1.self_of_nhds.1 hG.self_of_nhds
      (affineLift_ne_zero _ _) ?_ ?_
    · have := hw0.self_of_nhds
      exact this
    · intro v h1 h2
      refine hjoint v h1 ?_
      obtain ⟨c, hc⟩ := h2
      refine ⟨c, ?_⟩
      change fderiv ℂ (fun z => w ((chartAt (ComplexModel n) p).symm z))
        (chartAt (ComplexModel n) p p) v =
          c • w ((chartAt (ComplexModel n) p).symm (chartAt (ComplexModel n) p p)) at hc
      rw [hc, (chartAt (ComplexModel n) p).left_inv hps]

/-- **Immersion off the exceptional divisor.** -/
theorem joint_of_not_mem (hd : BlData n m Ψ C π P) {p : Y} (hp : π p ∉ C) (v : ComplexModel n)
    (h1 : ∃ c : ℂ, fderiv ℂ (baseLift Ψ π p) (chartAt (ComplexModel n) p p) v =
      c • baseLift Ψ π p (chartAt (ComplexModel n) p p)) :
    v = 0 := by
  have hτv := (baseLift_props hd p).2.2 v h1
  have hiso := BlowupIsomorphismOff.isIsomorphismOver_compl_of_isBlowupAlong hd.blowup
  have hnex : p ∉ exceptionalLocus n π := fun hex =>
    Set.disjoint_left.mp hiso.2 (show p ∈ π ⁻¹' Cᶜ from hp) hex
  have hbij : Function.Bijective (mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) π p) := by
    by_contra h; exact hnex h
  have hmd : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) π p :=
    (hd.blowup.contMDiff p).mdifferentiableAt (by simp)
  rw [mfderiv_eq_fderiv_chart hmd] at hbij
  have h0 : (fderiv ℂ (chartExpr π p) (chartAt (ComplexModel n) p p)) v =
      (fderiv ℂ (chartExpr π p) (chartAt (ComplexModel n) p p)) 0 := by
    rw [map_zero]; exact hτv
  exact hbij.1 h0

/-- `σⱼ(W) = Φ(e(π ·))` gives `γⱼ(W) = π`. -/
theorem monoBase_monoInverse {x₀ : M} {k : ℕ}
    {Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x₀ x₀)}
    {α : Y → NormalIdx n k → ℂ} {j : NormalIdx n k} {y : Y} (hy : π y ∈ flatDomain Φ)
    (hkey : monomial k j.1 (monoInverse Φ π α j y) =
      Φ.toFun (chartAt (ComplexModel n) x₀ (π y))) :
    monoBase Φ k j (monoInverse Φ π α j y) = π y := by
  rw [monoBase, hkey]
  exact flatInverse_flat Φ hy

/-- `w = αⱼ · ũ ∘ W` where `w = b(π ·) α`. -/
theorem eq_smul_tildeU {x₀ : M} {k : ℕ}
    {Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x₀ x₀)}
    {b : Fin (r + 1) → NormalIdx n k → M → ℂ} {w : Y → Fin (r + 1) → ℂ}
    {α : Y → NormalIdx n k → ℂ} {j : NormalIdx n k} {y : Y} (hy : π y ∈ flatDomain Φ)
    (hkey : monomial k j.1 (monoInverse Φ π α j y) =
      Φ.toFun (chartAt (ComplexModel n) x₀ (π y)))
    (hyj : α y j ≠ 0) (hwb : ∀ q, w y q = ∑ l, b q l (π y) * α y l) :
    w y = α y j • tildeU Φ k j b (monoInverse Φ π α j y) := by
  classical
  funext q
  simp only [Pi.smul_apply, smul_eq_mul, tildeU, monoBase_monoInverse hy hkey, hwb q,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  by_cases hl : l = j
  · subst hl; simp [hatW]; ring
  · have hne : l.1 ≠ j.1 := fun h => hl (Subtype.ext h)
    have hW : monoInverse Φ π α j y l.1 = α y l / α y j := by
      show (if h : k ≤ l.1.1 ∧ l.1 ≠ j.1 then α y ⟨l.1, h.1⟩ / α y j
        else flatCoord Φ l.1 (π y)) = _
      rw [dif_pos ⟨l.2, hne⟩]
    simp only [hatW, hl, if_false, hW]
    field_simp

/-- **Immersion along the exceptional divisor.** -/
theorem joint_of_mem (hd : BlData n m Ψ C π P) {x₀ : M} {k : ℕ}
    {Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x₀ x₀)}
    {b : Fin (r + 1) → NormalIdx n k → M → ℂ} {c : NormalIdx n k → Fin (r + 1) → M → ℂ}
    (hF : FlatData Ψ C P x₀ k Φ b c) {p : Y} (hp : π p = x₀) {h : Y → ℂ}
    {w : Y → Fin (r + 1) → ℂ} {α : Y → NormalIdx n k → ℂ}
    (hα : ∀ l, HolomorphicAt n (fun y => α y l) p)
    (hα0 : α p ≠ 0) (hαeq : ∀ᶠ y in 𝓝 p, ∀ l, flatCoord Φ l.1 (π y) = h y * α y l)
    (hwb : ∀ᶠ y in 𝓝 p, ∀ q, w y q = ∑ l, b q l (π y) * α y l) (v : ComplexModel n)
    (h1 : ∃ c : ℂ, fderiv ℂ (baseLift Ψ π p) (chartAt (ComplexModel n) p p) v =
      c • baseLift Ψ π p (chartAt (ComplexModel n) p p))
    (h2 : ∃ c : ℂ, fderiv ℂ (fun z => w ((chartAt (ComplexModel n) p).symm z))
      (chartAt (ComplexModel n) p p) v = c • w p) :
    v = 0 := by
  classical
  subst hp
  have hps : p ∈ (chartAt (ComplexModel n) p).source := mem_chart_source _ p
  have hT := tendsto_chart_symm (n := n) p
  have hτv := (baseLift_props hd p).2.2 v h1
  have hτd := (baseLift_props hd p).2.1
  obtain ⟨j, hj⟩ : ∃ j, α p j ≠ 0 := Function.ne_iff.mp hα0
  obtain ⟨ℓ, ⟨hℓs, hℓπ⟩, -⟩ := existsUnique_monomialLift hd.blowup hF.src hF.flat j.2
  obtain ⟨hWkey, hWhol, hWℓ⟩ := exists_monomialInverse hd hF rfl hα hαeq hj hℓs hℓπ
  have hWtd' := eventually_differentiableAt_chart (n := n)
    (f := fun y i => monoInverse Φ π α j y i) hWhol
  have hWtd : ∀ᶠ z in 𝓝 (chartAt (ComplexModel n) p p), DifferentiableAt ℂ
      (fun z => monoInverse Φ π α j ((chartAt (ComplexModel n) p).symm z)) z := by
    filter_upwards [hWtd'] with z hz
    exact (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => ℂ)).symm.differentiableAt.comp z hz
  have hWt0 : monoInverse Φ π α j ((chartAt (ComplexModel n) p).symm
      (chartAt (ComplexModel n) p p)) = monoInverse Φ π α j p := by
    rw [(chartAt (ComplexModel n) p).left_inv hps]
  have hkey0 := hWkey.self_of_nhds
  have hw₀ : monomial k j.1 (monoInverse Φ π α j p) = 0 := by rw [hkey0.2]; exact hF.zero
  have hbase0 : monoBase Φ k j (monoInverse Φ π α j p) = π p :=
    monoBase_monoInverse hkey0.1 hkey0.2
  -- Step 2: `dσⱼ(ξ) = 0`
  have hkeyz : (fun z => Φ.toFun (chartExpr π p z)) =ᶠ[𝓝 (chartAt (ComplexModel n) p p)]
      fun z => monomial k j.1 (monoInverse Φ π α j ((chartAt (ComplexModel n) p).symm z)) := by
    filter_upwards [hT.eventually hWkey] with z hz
    exact hz.2.symm
  have hτ0 : chartExpr π p (chartAt (ComplexModel n) p p) =
      chartAt (ComplexModel n) (π p) (π p) := by
    simp only [chartExpr, (chartAt (ComplexModel n) p).left_inv hps]
  have hΦd : DifferentiableAt ℂ Φ.toFun (chartExpr π p (chartAt (ComplexModel n) p p)) := by
    rw [hτ0]
    exact Φ.toFun_holomorphic.differentiableAt (Φ.isOpen_source.mem_nhds Φ.center_mem_source)
  have hmonod : ∀ w', DifferentiableAt ℂ (monomial k j.1) w' := fun w' =>
    (contDiff_monomial k j.1).differentiable (by simp) w'
  set ξ := fderiv ℂ (fun z => monoInverse Φ π α j ((chartAt (ComplexModel n) p).symm z))
    (chartAt (ComplexModel n) p p) v with hξdef
  have hξ : fderiv ℂ (monomial k j.1) (monoInverse Φ π α j p) ξ = 0 := by
    have e2 : fderiv ℂ (fun z => Φ.toFun (chartExpr π p z)) (chartAt (ComplexModel n) p p) v
        = 0 := by
      rw [fderiv_fun_comp _ hΦd hτd, ContinuousLinearMap.comp_apply, hτv, map_zero]
    rw [hkeyz.fderiv_eq, fderiv_fun_comp _ (hmonod _) hWtd.self_of_nhds,
      ContinuousLinearMap.comp_apply, hWt0] at e2
    exact e2
  -- Step 3: the non-normal and `j`-th coordinates of `ξ` vanish
  have hξ3 := fderiv_monomial_eq_zero hξ
  -- Step 4: `w = αⱼ ũ(W)` near `p`
  have hrel : ∀ᶠ y in 𝓝 p, w y = α y j • tildeU Φ k j b (monoInverse Φ π α j y) := by
    filter_upwards [hWkey, hwb, (hα j).continuousAt.eventually_ne hj] with y hy hyw hyj
    exact eq_smul_tildeU hy.1 hy.2 hyj hyw
  have hrelz : (fun z => w ((chartAt (ComplexModel n) p).symm z)) =ᶠ[𝓝 (chartAt (ComplexModel n) p p)]
      fun z => α ((chartAt (ComplexModel n) p).symm z) j •
        tildeU Φ k j b (monoInverse Φ π α j ((chartAt (ComplexModel n) p).symm z)) :=
    hT.eventually hrel
  have hlamd : DifferentiableAt ℂ (fun z => α ((chartAt (ComplexModel n) p).symm z) j)
      (chartAt (ComplexModel n) p p) :=
    (CartanLocalReduction.holAt_comp_chart_symm hps (hα j)).self_of_nhds
  have hT3 := fun q => fderiv_tildeU_apply hF.zero hF.hb j hw₀ hξ q
  have hũd : DifferentiableAt ℂ (tildeU Φ k j b) (monoInverse Φ π α j p) :=
    differentiableAt_pi.mpr fun q => (hT3 q).1.differentiableAt
  have hũd' : DifferentiableAt ℂ (tildeU Φ k j b)
      (monoInverse Φ π α j ((chartAt (ComplexModel n) p).symm (chartAt (ComplexModel n) p p))) := by
    rw [hWt0]; exact hũd
  have hũWd : DifferentiableAt ℂ
      (fun z => tildeU Φ k j b (monoInverse Φ π α j ((chartAt (ComplexModel n) p).symm z)))
      (chartAt (ComplexModel n) p p) :=
    DifferentiableAt.comp (g := tildeU Φ k j b)
      (f := fun z => monoInverse Φ π α j ((chartAt (ComplexModel n) p).symm z)) _ hũd'
      hWtd.self_of_nhds
  obtain ⟨c', hc'⟩ := h2
  have hsm : HasFDerivAt (fun z => α ((chartAt (ComplexModel n) p).symm z) j •
      tildeU Φ k j b (monoInverse Φ π α j ((chartAt (ComplexModel n) p).symm z))) _
      (chartAt (ComplexModel n) p p) := hlamd.hasFDerivAt.smul hũWd.hasFDerivAt
  rw [hrelz.fderiv_eq, hsm.fderiv] at hc'
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply] at hc'
  rw [fderiv_fun_comp (g := tildeU Φ k j b)
      (f := fun z => monoInverse Φ π α j ((chartAt (ComplexModel n) p).symm z)) _ hũd'
      hWtd.self_of_nhds, ContinuousLinearMap.comp_apply, hWt0,
    (chartAt (ComplexModel n) p).left_inv hps, ← hξdef] at hc'
  have hwp : w p = α p j • tildeU Φ k j b (monoInverse Φ π α j p) := hrel.self_of_nhds
  rw [hwp] at hc'
  -- `dũ ξ = ν ũ₀`
  set lam0 := α p j
  set dlam := fderiv ℂ (fun z => α ((chartAt (ComplexModel n) p).symm z) j)
    (chartAt (ComplexModel n) p p) v
  set ν := (c' * lam0 - dlam) / lam0 with hν
  have hdu : fderiv ℂ (tildeU Φ k j b) (monoInverse Φ π α j p) ξ =
      ν • tildeU Φ k j b (monoInverse Φ π α j p) := by
    funext q
    have := congrFun hc' q
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
    simp only [Pi.smul_apply, smul_eq_mul, hν]
    field_simp
    linear_combination this
  -- Step 5: componentwise
  have hcoord : ∀ q, ∑ l, b q l (π p) *
      ((if l = j then 0 else ξ l.1) - ν * hatW j (monoInverse Φ π α j p) l) = 0 := by
    intro q
    have e1 := fderiv_apply_coord hũd q ξ
    rw [hdu, (hT3 q).2] at e1
    simp only [Pi.smul_apply, smul_eq_mul, tildeU, hbase0] at e1
    have e2 : ∑ l, b q l (π p) * ((if l = j then 0 else ξ l.1) -
        ν * hatW j (monoInverse Φ π α j p) l) =
        (∑ l, b q l (π p) * (if l = j then 0 else ξ l.1)) -
          ν * ∑ l, b q l (π p) * hatW j (monoInverse Φ π α j p) l := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun l _ => by ring
    rw [e2]
    linear_combination -e1
  -- Step 6: apply `c(x₀)`
  have hd0 : ∀ l', (if l' = j then 0 else ξ l'.1) - ν * hatW j (monoInverse Φ π α j p) l' = 0 := by
    intro l'
    have := Finset.sum_eq_zero (s := Finset.univ) fun q (_ : q ∈ Finset.univ) =>
      show c l' q (π p) * ∑ l, b q l (π p) *
        ((if l = j then 0 else ξ l.1) - ν * hatW j (monoInverse Φ π α j p) l) = 0 by
        rw [hcoord q, mul_zero]
    simp only [Finset.mul_sum] at this
    rw [Finset.sum_comm] at this
    simp only [← mul_assoc, ← Finset.sum_mul, hF.delta, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true] at this
    exact this
  have hν0 : ν = 0 := by
    have := hd0 j
    simp only [if_true, hatW, mul_one, zero_sub, neg_eq_zero] at this
    exact this
  -- Step 7: `ξ = 0`
  have hξ0 : ξ = 0 := by
    ext i
    by_cases hi : k ≤ i.1 ∧ i ≠ j.1
    · have hl : (⟨i, hi.1⟩ : NormalIdx n k) ≠ j := fun h => hi.2 (congrArg Subtype.val h)
      have := hd0 ⟨i, hi.1⟩
      simp only [hl, if_false, hν0, zero_mul, sub_zero] at this
      simpa using this
    · simpa using hξ3 i hi
  -- Step 8: `ℓⱼ ∘ W = id` makes `dW` injective
  have hdom : ∀ y, π y ∈ flatDomain Φ → monomial k j.1 (monoInverse Φ π α j y) =
      Φ.toFun (chartAt (ComplexModel n) (π p) (π y)) →
      monoInverse Φ π α j y ∈ monomialDomain Φ k j.1 := by
    intro y hy hk
    show monomial k j.1 (monoInverse Φ π α j y) ∈ Φ.target
    rw [hk]; exact Φ.mapsTo_toFun hy.2
  set D : ComplexModel n → ComplexModel n := fun w' => chartAt (ComplexModel n) p
    (if hw' : w' ∈ monomialDomain Φ k j.1 then ℓ (LiftedOpen.mk _ w' hw') else p) with hD
  have hDW : (fun z => D (monoInverse Φ π α j ((chartAt (ComplexModel n) p).symm z)))
      =ᶠ[𝓝 (chartAt (ComplexModel n) p p)] id := by
    filter_upwards [hT.eventually (hWℓ.and hWkey),
      (chartAt (ComplexModel n) p).open_target.mem_nhds
        ((chartAt (ComplexModel n) p).map_source hps)] with z hz hzt
    have hm := hdom _ hz.2.1 hz.2.2
    simp only [hD, dif_pos hm, hz.1 hm, id]
    exact (chartAt (ComplexModel n) p).right_inv hzt
  have hw₀mem : monoInverse Φ π α j p ∈ monomialDomain Φ k j.1 := hdom p hkey0.1 hkey0.2
  have hℓq₀ : ℓ (LiftedOpen.mk _ (monoInverse Φ π α j p) hw₀mem) = p :=
    hWℓ.self_of_nhds hw₀mem
  have hDd : DifferentiableAt ℂ D (monoInverse Φ π α j p) := by
    set q₀ := LiftedOpen.mk.{u} (monomialDomain Φ k j.1) (monoInverse Φ π α j p) hw₀mem
    have hmd : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ℓ q₀ :=
      (hℓs q₀).mdifferentiableAt (by simp)
    have hdiff := differentiableAt_chart_of_mdifferentiableAt hmd
    rw [hℓq₀] at hdiff
    have hq₀ : chartAt (ComplexModel n) q₀ q₀ = monoInverse Φ π α j p := rfl
    rw [hq₀] at hdiff
    refine hdiff.congr_of_eventuallyEq ?_
    filter_upwards [(monomialDomain Φ k j.1).isOpen.mem_nhds hw₀mem] with w' hw'
    have e3 : D w' = chartAt (ComplexModel n) p (ℓ (LiftedOpen.mk _ w' hw')) := by
      simp only [hD]
      split_ifs with hcase
      · rfl
      · exact absurd hw' hcase
    rw [e3]
    congr 2
    exact (liftedOpen_extChartAt_symm q₀ w' hw').symm
  have hid : fderiv ℂ (fun z => D (monoInverse Φ π α j ((chartAt (ComplexModel n) p).symm z)))
      (chartAt (ComplexModel n) p p) = fderiv ℂ id (chartAt (ComplexModel n) p p) :=
    hDW.fderiv_eq
  rw [fderiv_fun_comp (g := D)
      (f := fun z => monoInverse Φ π α j ((chartAt (ComplexModel n) p).symm z)) _
      (by rw [hWt0]; exact hDd) hWtd.self_of_nhds, fderiv_id] at hid
  have := congrArg (fun L : ComplexModel n →L[ℂ] ComplexModel n => L v) hid
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at this
  rw [← this, ← hξdef, hξ0, map_zero]

/-- **Local lifts with projective immersion at every point of the blow-up.** -/
theorem exists_lift_blowupEmbedding (hd : BlData n m Ψ C π P) (p : Y) :
    ∃ F : ComplexModel n → Fin (segreDim N r + 1) → ℂ,
      (∀ᶠ z in 𝓝 ((complexChartAt (n := n) p).val p),
        DifferentiableAt ℂ F z ∧ F z ≠ 0 ∧
        blowupEmbedding Ψ π P ((complexChartAt (n := n) p).val.symm z) = pmk (F z)) ∧
      IsProjImmersionAt F ((complexChartAt (n := n) p).val p) := by
  by_cases hx : π p ∈ C
  · obtain ⟨k, Φ, b, c, hF⟩ := exists_flatData hd hx
    obtain ⟨U, h, w, α, hrep, -, hw, hα, hα0, hαeq, hwb⟩ := exists_pointData hd hF rfl
    exact lift_of_rep hd p hrep hw fun v h1 h2 => joint_of_mem hd hF rfl hα hα0 hαeq hwb v h1 h2
  · obtain ⟨U, h, w, hrep, hw⟩ := exists_isBlRep hd.emb hd.blowup hd.gen p
    exact lift_of_rep hd p hrep hw fun v h1 _ => joint_of_not_mem hd hx v h1

/-- **The blow-up embedding is injective.** -/
theorem blowupEmbedding_injective (hd : BlData n m Ψ C π P) :
    Function.Injective (blowupEmbedding Ψ π P) := by
  classical
  intro y₁ y₂ heq
  have hpair : (Ψ (π y₁), blowupMap Ψ π P y₁) = (Ψ (π y₂), blowupMap Ψ π P y₂) :=
    segreMap_injective heq
  have hπ12 : π y₁ = π y₂ := hd.emb.injective (congrArg Prod.fst hpair)
  have hΦ12 : blowupMap Ψ π P y₁ = blowupMap Ψ π P y₂ := congrArg Prod.snd hpair
  by_cases hx : π y₁ ∈ C
  · obtain ⟨k, Φ, b, c, hF⟩ := exists_flatData hd hx
    obtain ⟨U₁, h₁, w₁, α₁, hrep₁, -, -, hα₁, hα₁0, hα₁eq, hwb₁⟩ := exists_pointData hd hF rfl
    obtain ⟨U₂, h₂, w₂, α₂, hrep₂, -, -, hα₂, -, hα₂eq, hwb₂⟩ :=
      exists_pointData hd hF hπ12.symm
    have hm₁ := blowupMap_eq hd.emb hd.blowup.contMDiff.continuous hd.hom hrep₁
    have hm₂ := blowupMap_eq hd.emb hd.blowup.contMDiff.continuous hd.hom hrep₂
    have hw₁ : w₁ y₁ = fun q => ∑ l, b q l (π y₁) * α₁ y₁ l := funext hwb₁.self_of_nhds
    have hw₂ : w₂ y₂ = fun q => ∑ l, b q l (π y₁) * α₂ y₂ l := by
      funext q; rw [hwb₂.self_of_nhds q, hπ12]
    have hpm : pmk (w₁ y₁) = pmk (w₂ y₂) := by rw [← hm₁, ← hm₂, hΦ12]
    obtain ⟨t, ht, ht12⟩ := (pmk_eq_pmk_iff hrep₁.2.2.2.2.2.2.2 hrep₂.2.2.2.2.2.2.2).mp hpm
    have key : ∀ (a : NormalIdx n k → ℂ) (l' : NormalIdx n k),
        (∑ q, c l' q (π y₁) * ∑ l, b q l (π y₁) * a l) = a l' := by
      intro a l'
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      simp only [← mul_assoc, ← Finset.sum_mul, hF.delta, ite_mul, one_mul, zero_mul,
        Finset.sum_ite_eq, Finset.mem_univ, if_true]
    have hα12 : ∀ l', α₁ y₁ l' = t * α₂ y₂ l' := by
      intro l'
      rw [← key (α₁ y₁) l', ← key (fun l => t * α₂ y₂ l) l']
      refine Finset.sum_congr rfl fun q _ => ?_
      have := congrFun ht12 q
      rw [hw₁, hw₂] at this
      simp only [Pi.smul_apply, smul_eq_mul] at this
      rw [this, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun l _ => by ring
    obtain ⟨j, hj⟩ : ∃ j, α₁ y₁ j ≠ 0 := Function.ne_iff.mp hα₁0
    have hj2 : α₂ y₂ j ≠ 0 := fun h0 => hj (by rw [hα12 j, h0, mul_zero])
    obtain ⟨ℓ, ⟨hℓs, hℓπ⟩, -⟩ := existsUnique_monomialLift hd.blowup hF.src hF.flat j.2
    obtain ⟨hk₁, -, hℓ₁⟩ := exists_monomialInverse hd hF rfl hα₁ hα₁eq hj hℓs hℓπ
    obtain ⟨-, -, hℓ₂⟩ := exists_monomialInverse hd hF hπ12.symm hα₂ hα₂eq hj2 hℓs hℓπ
    have hW : monoInverse Φ π α₁ j y₁ = monoInverse Φ π α₂ j y₂ := by
      ext i
      show (if h : k ≤ i.1 ∧ i ≠ j.1 then α₁ y₁ ⟨i, h.1⟩ / α₁ y₁ j
        else flatCoord Φ i (π y₁)) = (if h : k ≤ i.1 ∧ i ≠ j.1 then α₂ y₂ ⟨i, h.1⟩ / α₂ y₂ j
        else flatCoord Φ i (π y₂))
      split_ifs with hi
      · rw [hα12, hα12 j, mul_div_mul_left _ _ ht]
      · exact congrArg _ hπ12
    have hmem : monoInverse Φ π α₁ j y₁ ∈ monomialDomain Φ k j.1 := by
      show monomial k j.1 _ ∈ Φ.target
      rw [hk₁.self_of_nhds.2]
      exact Φ.mapsTo_toFun hk₁.self_of_nhds.1.2
    have hmem₂ : monoInverse Φ π α₂ j y₂ ∈ monomialDomain Φ k j.1 := hW ▸ hmem
    calc y₁ = ℓ (LiftedOpen.mk _ _ hmem) := (hℓ₁.self_of_nhds hmem).symm
      _ = ℓ (LiftedOpen.mk _ _ hmem₂) := congrArg ℓ (Subtype.ext (congrArg ULift.up hW))
      _ = y₂ := hℓ₂.self_of_nhds hmem₂
  · have hiso := BlowupIsomorphismOff.isIsomorphismOver_compl_of_isBlowupAlong hd.blowup
    exact hiso.1.injOn (show π y₁ ∈ Cᶜ from hx) (show π y₂ ∈ Cᶜ by rw [← hπ12]; exact hx) hπ12

/-- **The blow-up embedding is a holomorphic embedding.** -/
theorem isHolomorphicEmbedding_blowupEmbedding (hd : BlData n m Ψ C π P) :
    IsHolomorphicEmbedding (n := n) (blowupEmbedding Ψ π P) :=
  isHolomorphicEmbedding_of_lifts (blowupEmbedding_injective hd) (exists_lift_blowupEmbedding hd)

/-- The generator data of Chow's theorem exist for every blow-up of a projective manifold. -/
theorem exists_blData (hΨ : IsHolomorphicEmbedding (n := n) Ψ) (hπ : IsBlowupAlong n C π) :
    ∃ (r m : ℕ) (P : Fin (r + 1) → MvPolynomial (Fin (N + 1)) ℂ), BlData n m Ψ C π P := by
  classical
  obtain ⟨m₀, hm₀⟩ := chow_image hΨ
    (AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold hπ.1)
  obtain ⟨μ, hμ, P, hP, hgen, -⟩ := hm₀ m₀ le_rfl
  set e := Fintype.equivFin μ
  set P' : Fin (Fintype.card μ + 1) → MvPolynomial (Fin (N + 1)) ℂ :=
    Fin.cons 0 fun q => P (e.symm q) with hP'
  refine ⟨Fintype.card μ, m₀, P', hΨ, hπ, fun q => ?_, ?_⟩
  · refine Fin.cases ?_ (fun q => ?_) q
    · simp only [hP', Fin.cons_zero]
      exact MvPolynomial.isHomogeneous_zero _ _ _
    · simp only [hP', Fin.cons_succ]
      exact hP _
  · refine hgen.of_generators (fun q _ => (SGPT.GAGA.PN.differentiable_eval_poly _).differentiableOn)
      (fun y hy q => ?_) (fun y _ k' => ?_)
    · refine Fin.cases ?_ (fun q => ?_) q
      · refine ⟨Eventually.of_forall fun _ => (SGPT.GAGA.PN.differentiable_eval_poly _).differentiableAt,
          Eventually.of_forall fun z _ => ?_⟩
        simp [hP', SGPT.GAGA.PN.polyTuple]
      · have := hgen.gen_mem hy (e.symm q)
        simpa [hP'] using this
    · have h := Core.isCombinationAt_gen (fun q => SGPT.GAGA.PN.polyTuple (P' q)) y (Fin.succ (e k'))
      simpa [hP'] using h

/-- **Projectivity of blow-ups along smooth centres**: the blow-up of a compact complex
manifold with a holomorphic embedding into `ℙᴺ`, along a nowhere dense closed complex
submanifold, is compact and has a holomorphic embedding into some `ℙ^{N'}`. -/
theorem exists_isHolomorphicEmbedding_of_isBlowupAlong (hΨ : IsHolomorphicEmbedding (n := n) Ψ)
    (hπ : IsBlowupAlong n C π) :
    CompactSpace Y ∧ ∃ (N' : ℕ) (Ψ' : Y → ComplexProjectiveSpace N'),
      IsHolomorphicEmbedding (n := n) Ψ' := by
  obtain ⟨r, m, P, hd⟩ := exists_blData hΨ hπ
  exact ⟨BlowupCompact.compactSpace_of_isBlowupAlong hπ, _, _,
    isHolomorphicEmbedding_blowupEmbedding hd⟩

end SGPT.GAGA.ChowBl

namespace SGPT.GAGA.ChowBl

universe u

/-- **Projectivity of blow-up towers**: every finite sequence of blow-ups with smooth centres of
a compact complex manifold with a holomorphic embedding into projective space is compact and
admits a holomorphic embedding into projective space. -/
theorem exists_isHolomorphicEmbedding_of_isBlowupSequence {n N : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    [CompactSpace X] {Ψ : X → ComplexProjectiveSpace N} (hΨ : IsHolomorphicEmbedding (n := n) Ψ)
    {Z : Type u} [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z]
    {f : Z → X} (h : IsBlowupSequence n X Z f) :
    CompactSpace Z ∧ ∃ (N' : ℕ) (Ψ' : Z → ComplexProjectiveSpace N'),
      IsHolomorphicEmbedding (n := n) Ψ' := by
  induction h with
  | refl => exact ⟨inferInstance, N, Ψ, hΨ⟩
  | step f C g _ hg ih =>
    obtain ⟨hc, N', Ψ', hΨ'⟩ := ih
    have := hc
    exact exists_isHolomorphicEmbedding_of_isBlowupAlong hΨ' hg

/-- **Smooth flags through every smooth hypersurface of a blow-up tower** of a compact
connected projective manifold: every closed connected complex submanifold `W` of dimension
`n - 1` of a finite sequence of blow-ups with smooth centres is the first member `W = Y₁` of a
smooth flag (`def:Okounkov:L170`). -/
theorem exists_isSmoothFlag_one_eq_of_isBlowupSequence {n N : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    [CompactSpace X] [ConnectedSpace X] {Ψ : X → ComplexProjectiveSpace N}
    (hΨ : IsHolomorphicEmbedding (n := n) Ψ)
    {Z : Type u} [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z]
    {f : Z → X} (h : IsBlowupSequence n X Z f) (hn : 1 ≤ n) {W : Set Z}
    (hW : IsClosedConnectedSubmanifold n W (n - 1)) :
    ∃ Yfl : Fin (n + 1) → Set Z, SGPT.Okounkov.IsSmoothFlag Yfl ∧ Yfl ⟨1, by omega⟩ = W := by
  obtain ⟨hc, N', Ψ', hΨ'⟩ := exists_isHolomorphicEmbedding_of_isBlowupSequence hΨ h
  have := hc
  have := BlowupConnected.connectedSpace_of_isBlowupSequence f h
  exact SGPT.GAGA.SmoothFlags.exists_isSmoothFlag_one_eq Ψ'
    (SGPT.GAGA.SmoothFlags.contMDiff_of_isHolomorphicEmbedding hΨ') hΨ'.injective hn hW

end SGPT.GAGA.ChowBl

namespace SGPT.GAGA.ChowBl

universe u

/-- **Blow-up towers are projective algebraic**: a finite sequence of blow-ups with smooth centres
of a compact complex manifold with a holomorphic embedding into projective space has a holomorphic
embedding `Ψ'` into some `ℙ^{N'}` whose image is cut out by homogeneous polynomials of degree `m`
(every large `m`) generating the ideal sheaf of its cone (Chow's theorem): the tower is
biholomorphic to the analytification of a reduced closed subscheme of `ℙ^{N'}`. -/
theorem exists_chow_presentation_of_isBlowupSequence {n N : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    [CompactSpace X] {Ψ : X → ComplexProjectiveSpace N} (hΨ : IsHolomorphicEmbedding (n := n) Ψ)
    {Z : Type u} [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z]
    {f : Z → X} (h : IsBlowupSequence n X Z f) :
    ∃ (N' : ℕ) (Ψ' : Z → ComplexProjectiveSpace N'), IsHolomorphicEmbedding (n := n) Ψ' ∧
      ∃ m₀ : ℕ, ∀ m ≥ m₀, ∃ (μ : Type) (_ : Fintype μ)
        (P : μ → MvPolynomial (Fin (N' + 1)) ℂ), (∀ k, (P k).IsHomogeneous m) ∧
        (coneIdeal (Set.range Ψ')).GeneratedOn
          (SGPT.GAGA.PN.puncture (SGPT.GAGA.PN.ConeSpace N'))
          (fun k => SGPT.GAGA.PN.polyTuple (P k)) ∧
        Set.range Ψ' = {x | ∀ k, MvPolynomial.eval x.rep (P k) = 0} := by
  obtain ⟨hc, N', Ψ', hΨ'⟩ := exists_isHolomorphicEmbedding_of_isBlowupSequence hΨ h
  have := hc
  refine ⟨N', Ψ', hΨ', ?_⟩
  have h := chow_image hΨ' (isComplexAnalyticSubset_univ (n := n) (M := Z))
  rw [Set.image_univ] at h
  exact h

end SGPT.GAGA.ChowBl
