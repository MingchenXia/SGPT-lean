import SGPT.Okounkov.TranscendentalExtensionThetaOn
import SGPT.Foundations.Analysis.Pending.SubmanifoldKahlerRestriction
import SGPT.Foundations.Analysis.Pending.HolomorphicPullback
import SGPT.Foundations.Analysis.FirstPass.RegularPatchNeighborhood
import SGPT.Foundations.Analysis.FirstPass.LocalPotentialPullback

/-!
# Local extensions of potentials from a submanifold (DRWNXZ Theorem 6.1, Step 2)

Blueprint `tok:ext-nwz` and `tok:ct-extension` (package EXT). Let `Y ⊆ X` be a closed complex
submanifold of dimension `k` and `G` a flattening datum of `Y` (`SubmanifoldChartedSpace.FlatData`:
an atlas chart `e = G.amb` of `X` and a biholomorphism `Φ = G.flat` of open subsets of `ℂⁿ` with
`Y = {Φ ∘ e ∈ ℂᵏ × 0}`). In these coordinates the coordinate projection `(z', w) ↦ (z', 0)` is a
holomorphic retraction `retr G` of a neighbourhood of `Y ∩ dom G` onto `Y`.

## Adaptation of the source

DRWNXZ (following Ning--Wang--Zhou, §2) and FPT extend `φ` near `Y` by
`φ ∘ π + A dist(·, Y)²`, and prove positivity by a block-matrix (Schur complement) estimate. We use
instead the exact local correction given by a local potential `ρ` of the Kähler form
(`dd^c ρ = ω` on the chart):
`u = φ ∘ π + c (ρ ∘ π - ρ)` (`localExt`). Then `c ω + dd^c u = π^*(c ω|_Y + dd^c φ) ≥ 0`, so
`u ∈ PSH(·, c ω)` exactly when `φ ∈ PSH(Y, c ω|_Y)` (`thetaOn_localExt`), with no estimate and no
shrinking; `u = φ` on `Y`. The correction `c (ρ ∘ π - ρ)` is smooth and vanishes on `Y`, and it
is itself `c ω`-psh (`thetaOn_localCorrection`, the case `φ = 0`), which is what the
comparison of local extensions and the gluing need. This replaces `tok:ext-nwz`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

universe u

open Set Filter
open scoped Topology Manifold ContDiff

namespace SGPT.Okounkov.TranscendentalExtension

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.FirstPass.RegularLocusDense
open SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.SubmanifoldChartedSpace

variable {n k : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {Y : Set X}

/-! ### The retraction of a flattening chart -/

/-- The flattened coordinates `Φ (e x)` of a point. -/
def flatCoord (G : FlatData n k X Y) (x : X) : ComplexModel n := G.flat (G.amb.val x)

/-- The tangential coordinates `z' = pr (Φ (e x))`. -/
def flatProj (G : FlatData n k X Y) (x : X) : ComplexModel k :=
  coordinateProjection n k (flatCoord G x)

/-- The holomorphic retraction `(z', w) ↦ (z', 0)` onto `Y`, in the flattening chart `G`. -/
def retr (G : FlatData n k X Y) (x : X) : Y := G.invPoint (flatProj G x)

/-- The open set on which the retraction is defined. -/
def retrDomain (G : FlatData n k X Y) : Set X :=
  {x | x ∈ G.ambSource ∧ flatProj G x ∈ G.coordTarget}

theorem continuousOn_flatCoord (G : FlatData n k X Y) :
    ContinuousOn (flatCoord G) G.ambSource :=
  G.flat.continuousOn.comp (G.amb.val.continuousOn.mono fun _ hx => hx.1) fun _ hx => hx.2

theorem continuousOn_flatProj (G : FlatData n k X Y) :
    ContinuousOn (flatProj G) G.ambSource :=
  (coordinateProjection n k).continuous.comp_continuousOn (continuousOn_flatCoord G)

theorem isOpen_retrDomain (G : FlatData n k X Y) : IsOpen (retrDomain G) :=
  (continuousOn_flatProj G).isOpen_inter_preimage G.isOpen_ambSource G.isOpen_coordTarget

theorem retrDomain_subset (G : FlatData n k X Y) : retrDomain G ⊆ G.ambSource :=
  fun _ hx => hx.1

theorem retr_val {G : FlatData n k X Y} {x : X} (hx : x ∈ retrDomain G) :
    (retr G x : X) = G.ofCoord (flatProj G x) :=
  G.invPoint_val hx.2

theorem retr_mem_ambSource {G : FlatData n k X Y} {x : X} (hx : x ∈ retrDomain G) :
    (retr G x : X) ∈ G.ambSource := by
  rw [retr_val hx]
  exact G.ofCoord_mem_ambSource hx.2

theorem amb_retr {G : FlatData n k X Y} {x : X} (hx : x ∈ retrDomain G) :
    G.amb.val (retr G x : X) = G.flat.symm (coordinateInclusion n k (flatProj G x)) := by
  rw [retr_val hx]
  exact amb_ofCoord G hx.2

theorem flatCoord_retr {G : FlatData n k X Y} {x : X} (hx : x ∈ retrDomain G) :
    flatCoord G (retr G x : X) = coordinateInclusion n k (flatProj G x) := by
  rw [flatCoord, retr_val hx]
  exact G.flat_amb_ofCoord hx.2

theorem continuousOn_retr (G : FlatData n k X Y) : ContinuousOn (retr G) (retrDomain G) :=
  G.continuousOn_invPoint.comp ((continuousOn_flatProj G).mono (retrDomain_subset G))
    fun _ hx => hx.2

theorem mem_retrDomain_of_mem (G : FlatData n k X Y) {y : X} (hyY : y ∈ Y)
    (hy : y ∈ G.ambSource) : y ∈ retrDomain G :=
  ⟨hy, G.toCoord_mem_coordTarget ⟨y, hyY⟩ hy⟩

/-- The retraction fixes the points of `Y`. -/
theorem retr_of_mem (hk : k ≤ n) (G : FlatData n k X Y) {y : X} (hyY : y ∈ Y)
    (hy : y ∈ G.ambSource) : retr G y = ⟨y, hyY⟩ :=
  (G.chart hk).left_inv (show (⟨y, hyY⟩ : Y) ∈ (G.chart hk).source from hy)

/-! ### The local extension -/

/-- The correction `c (ρ ∘ π - ρ)`, read in the ambient chart `e = G.amb`. -/
def localCorrection (G : FlatData n k X Y) (ρ : ComplexModel n → ℝ) (c : ℝ) (x : X) : ℝ :=
  c * ρ (G.amb.val (retr G x : X)) - c * ρ (G.amb.val x)

/-- **The local extension** `u = φ ∘ π + c (ρ ∘ π - ρ)` of `φ` in the flattening chart `G`, for a
local potential `ρ` of `ω` in the chart `G.amb`. -/
def localExt (G : FlatData n k X Y) (ρ : ComplexModel n → ℝ) (c : ℝ) (φ : Y → EReal)
    (x : X) : EReal :=
  φ (retr G x) + (localCorrection G ρ c x : EReal)

/-- The domain of the local extension: the retraction is defined and both `x` and `π x` lie in
the domain `Wρ` of the local potential. -/
def localDomain (G : FlatData n k X Y) (Wρ : Set (ComplexModel n)) : Set X :=
  {x | x ∈ retrDomain G ∧ G.amb.val x ∈ Wρ ∧ G.amb.val (retr G x : X) ∈ Wρ}

theorem localDomain_subset_retrDomain (G : FlatData n k X Y) (Wρ : Set (ComplexModel n)) :
    localDomain G Wρ ⊆ retrDomain G := fun _ hx => hx.1

theorem isOpen_localDomain (G : FlatData n k X Y) {Wρ : Set (ComplexModel n)}
    (hW : IsOpen Wρ) : IsOpen (localDomain G Wρ) := by
  have h1 : ContinuousOn (fun x => G.amb.val x) (retrDomain G) :=
    G.amb.val.continuousOn.mono fun _ hx => hx.1.1
  have h2 : ContinuousOn (fun x => G.amb.val (retr G x : X)) (retrDomain G) :=
    G.amb.val.continuousOn.comp (continuous_subtype_val.comp_continuousOn (continuousOn_retr G))
      fun _ hx => (retr_mem_ambSource hx).1
  have h3 := h1.isOpen_inter_preimage (isOpen_retrDomain G) hW
  have h4 := h2.isOpen_inter_preimage (isOpen_retrDomain G) hW
  have : localDomain G Wρ = (retrDomain G ∩ (fun x => G.amb.val x) ⁻¹' Wρ) ∩
      (retrDomain G ∩ (fun x => G.amb.val (retr G x : X)) ⁻¹' Wρ) := by
    ext x
    simp only [localDomain, mem_ofPred_eq, mem_inter_iff, mem_preimage]
    tauto
  rw [this]
  exact h3.inter h4

theorem mem_localDomain_of_mem (hk : k ≤ n) (G : FlatData n k X Y) {Wρ : Set (ComplexModel n)}
    {y : X} (hyY : y ∈ Y) (hy : y ∈ G.ambSource) (hyW : G.amb.val y ∈ Wρ) :
    y ∈ localDomain G Wρ := by
  refine ⟨mem_retrDomain_of_mem G hyY hy, hyW, ?_⟩
  rw [retr_of_mem hk G hyY hy]
  exact hyW

theorem localCorrection_of_mem (hk : k ≤ n) (G : FlatData n k X Y) (ρ : ComplexModel n → ℝ)
    (c : ℝ) {y : X} (hyY : y ∈ Y) (hy : y ∈ G.ambSource) : localCorrection G ρ c y = 0 := by
  rw [localCorrection, retr_of_mem hk G hyY hy, sub_self]

/-- The local extension restricts to `φ` on `Y`. -/
theorem localExt_of_mem (hk : k ≤ n) (G : FlatData n k X Y) (ρ : ComplexModel n → ℝ) (c : ℝ)
    (φ : Y → EReal) {y : X} (hyY : y ∈ Y) (hy : y ∈ G.ambSource) :
    localExt G ρ c φ y = φ ⟨y, hyY⟩ := by
  rw [localExt, localCorrection_of_mem hk G ρ c hyY hy, retr_of_mem hk G hyY hy, EReal.coe_zero,
    add_zero]

theorem continuousOn_localCorrection (G : FlatData n k X Y) {Wρ : Set (ComplexModel n)}
    {ρ : ComplexModel n → ℝ} (hρ : ContinuousOn ρ Wρ) (c : ℝ) :
    ContinuousOn (localCorrection G ρ c) (localDomain G Wρ) := by
  have h1 : ContinuousOn (fun x => G.amb.val x) (localDomain G Wρ) :=
    G.amb.val.continuousOn.mono fun _ hx => hx.1.1.1
  have h2 : ContinuousOn (fun x => G.amb.val (retr G x : X)) (localDomain G Wρ) :=
    G.amb.val.continuousOn.comp
      (continuous_subtype_val.comp_continuousOn ((continuousOn_retr G).mono
        (localDomain_subset_retrDomain G Wρ)))
      fun _ hx => (retr_mem_ambSource hx.1).1
  exact ((continuousOn_const.mul (hρ.comp h2 fun _ hx => hx.2.2)).sub
    (continuousOn_const.mul (hρ.comp h1 fun _ hx => hx.2.1)))

/-- **The local extension is psh** (replacing `tok:ext-nwz`): if `φ` is `(c • ω|_Y)`-psh on `Y`
and `ρ` is a local potential of `ω` in the chart `G.amb`, then `localExt G ρ c φ` is
`(c • ω)`-psh on `localDomain G Wρ`. -/
theorem thetaOn_localExt (hk : k ≤ n) (hY : ∀ x ∈ Y, RegularAtDim (n := n) Y x k)
    (a : ClosedRealOneOneForm n X) (G : FlatData n k X Y) {Wρ : Set (ComplexModel n)}
    {ρ : ComplexModel n → ℝ} (hρ : IsSmoothLocalPotential a.val G.amb Wρ ρ) (c : ℝ)
    {φ : Y → EReal}
    (hφ : letI := chartedSpace hk hY
      haveI := isComplexManifold_chartedSpace hk hY
      ThetaPlurisubharmonic (c • ClosedRealOneOneForm.pullback (contMDiff_val hk hY) a).val φ) :
    ThetaPlurisubharmonicOn (c • a).val (localExt G ρ c φ) (localDomain G Wρ) := by
  let _ := chartedSpace hk hY
  have _ := isComplexManifold_chartedSpace hk hY
  have hval := contMDiff_val hk hY
  let e := G.amb
  let eY : ComplexChart k Y := ⟨G.chart hk, chart_mem_atlas hk hY G⟩
  -- the holomorphic map `z ↦ pr (Φ z)` and the potential domain of the pulled back potential
  let Pr : ComplexModel n → ComplexModel k := fun z => coordinateProjection n k (G.flat z)
  let V : Set (ComplexModel k) := LocalPotentialPullback.potentialDomain Subtype.val eY e Wρ
  have hV : IsOpen V := LocalPotentialPullback.potentialDomain_isOpen hval eY e hρ.1
  have hσ : IsSmoothLocalPotential (c • ClosedRealOneOneForm.pullback hval a).val eY V
      (fun ζ => c • (ρ ∘ coordinateMap Subtype.val eY e) ζ) :=
    LocalPotentials.localPotential_smul
      (a := ClosedRealOneOneForm.pullback hval a)
      (LocalPotentialPullback.isSmoothLocalPotential_pullback hval eY hρ) c
  have hPsh : PlurisubharmonicOn
      (fun ζ => chartFunction φ eY ζ + ((c • (ρ ∘ coordinateMap Subtype.val eY e) ζ : ℝ) : EReal))
      V := fun ζ hζ =>
    IdealFunctionMaxGluing.ThetaPlurisubharmonicOn.plurisubharmonicAt_add_potential
      (thetaOn_of_global hφ univ) eY hσ hζ (mem_univ _)
  -- the chart domain
  let W : Set (ComplexModel n) :=
    {z | z ∈ e.val.target ∧ z ∈ Wρ ∧ z ∈ G.flat.source ∧ Pr z ∈ G.coordTarget ∧
      G.flat.symm (coordinateInclusion n k (Pr z)) ∈ Wρ}
  have hPrc : ContinuousOn Pr G.flat.source :=
    (coordinateProjection n k).continuous.comp_continuousOn G.flat.continuousOn
  have hW : IsOpen W := by
    let S : Set (ComplexModel n) := G.flat.source ∩ Pr ⁻¹' G.coordTarget
    have hS : IsOpen S := hPrc.isOpen_inter_preimage G.flat.open_source G.isOpen_coordTarget
    have hR : ContinuousOn (fun z => G.flat.symm (coordinateInclusion n k (Pr z))) S :=
      G.flat.continuousOn_symm.comp
        ((coordinateInclusion n k).continuous.comp_continuousOn (hPrc.mono inter_subset_left))
        fun z hz => hz.2
    have hS' := hR.isOpen_inter_preimage hS hρ.1
    have : W = (e.val.target ∩ Wρ) ∩
        (S ∩ (fun z => G.flat.symm (coordinateInclusion n k (Pr z))) ⁻¹' Wρ) := by
      ext z
      simp only [W, S, mem_ofPred_eq, mem_inter_iff, mem_preimage]
      tauto
    rw [this]
    exact (e.val.open_target.inter hρ.1).inter hS'
  have hPrd : DifferentiableOn ℂ Pr W :=
    ((coordinateProjection n k).differentiable.comp_differentiableOn
      G.differentiableOn_flat).mono fun z hz => hz.2.2.1
  -- `Pr` maps `W` into the potential domain
  have hmaps : MapsTo Pr W V := by
    intro z hz
    have hzT : Pr z ∈ G.coordTarget := hz.2.2.2.1
    have hsymm : ((eY.val.symm (Pr z) : Y) : X) = G.ofCoord (Pr z) := G.invPoint_val hzT
    refine ⟨⟨hzT, ?_⟩, ?_⟩
    · show ((eY.val.symm (Pr z) : Y) : X) ∈ e.val.source
      rw [hsymm]
      exact (G.ofCoord_mem_ambSource hzT).1
    · show e.val ((eY.val.symm (Pr z) : Y) : X) ∈ Wρ
      rw [hsymm, amb_ofCoord G hzT]
      exact hz.2.2.2.2
  have hcomp := HolomorphicPullback.plurisubharmonicOn_comp_holomorphic hW hPrd hmaps hPsh
  refine thetaPlurisubharmonicOn_of_chart e (fun x hx => hx.1.1.1) fun x hx => ?_
  have hxS : x ∈ G.ambSource := hx.1.1
  refine ⟨W, fun z => c • ρ z, ⟨e.val.map_source hxS.1, hx.2.1, hxS.2, hx.1.2, ?_⟩,
    (LocalPotentials.localPotential_smul hρ c).mono hW fun z hz => hz.2.1, ?_⟩
  · have := amb_retr hx.1
    show G.flat.symm (coordinateInclusion n k (flatProj G x)) ∈ Wρ
    rw [← this]
    exact hx.2.2
  intro z hz
  refine (hcomp z hz).congr ?_
  filter_upwards [hW.mem_nhds hz] with w hw
  have hwT : Pr w ∈ G.coordTarget := hw.2.2.2.1
  have hew : e.val (e.val.symm w) = w := e.val.right_inv hw.1
  have hretr : retr G (e.val.symm w) = eY.val.symm (Pr w) := by
    show G.invPoint (coordinateProjection n k (G.flat (e.val (e.val.symm w)))) = G.invPoint (Pr w)
    rw [hew]
  have hcm : coordinateMap Subtype.val eY e (Pr w) = e.val ((retr G (e.val.symm w) : Y) : X) := by
    rw [hretr]; rfl
  simp only [chartFunction, localExt, localCorrection, Function.comp_apply, smul_eq_mul]
  rw [hcm, hretr, hew, add_assoc, ← EReal.coe_add]
  congr 2
  ring

/-- **The local correction is psh**: for `c ≥ 0`, `c (ρ ∘ π - ρ)` is `(c • ω)`-psh on
`localDomain G Wρ` (the case `φ = 0` of `thetaOn_localExt`; `ω|_Y` is semipositive). -/
theorem thetaOn_localCorrection (hk : k ≤ n) (hY : ∀ x ∈ Y, RegularAtDim (n := n) Y x k)
    (a : ClosedRealOneOneForm n X) (ha : a.val.IsSemipositive) (G : FlatData n k X Y)
    {Wρ : Set (ComplexModel n)} {ρ : ComplexModel n → ℝ}
    (hρ : IsSmoothLocalPotential a.val G.amb Wρ ρ) {c : ℝ} (hc : 0 ≤ c) :
    ThetaPlurisubharmonicOn (c • a).val (fun x => (localCorrection G ρ c x : EReal))
      (localDomain G Wρ) := by
  let _ := chartedSpace hk hY
  have _ := isComplexManifold_chartedSpace hk hY
  have hval := contMDiff_val hk hY
  have hsemi : (c • ClosedRealOneOneForm.pullback hval a).val.IsSemipositive := by
    intro e z hz v
    have h := ClosedRealOneOneForm.pullback_isSemipositive hval ha e z hz v
    simp only [ClosedRealOneOneForm.coeff_smul, ContinuousAlternatingMap.smul_apply,
      smul_eq_mul] at h ⊢
    exact mul_nonneg hc h
  have h0 := (LocalPotentials.thetaPlurisubharmonic_zero_iff _).mpr hsemi
  have h := thetaOn_localExt hk hY a G hρ c (φ := fun _ => 0) h0
  refine thetaOn_congr (isOpen_localDomain G hρ.1) h fun x _ => ?_
  simp only [localExt, zero_add]

end SGPT.Okounkov.TranscendentalExtension
