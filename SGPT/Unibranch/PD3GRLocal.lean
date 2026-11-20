import SGPT.Unibranch.MiscMFornaessNarasimhanManifold
import SGPT.Unibranch.FNRAnalyticHull
import SGPT.PSH.GrauertRemmertBounded
import SGPT.Foundations.Analysis.Pending.PshAnalyticRemovable
import SGPT.Foundations.Analysis.FirstPass.UscRegularizationContinuous

/-!
# Grauert--Remmert extension along domain charts

Source `thm:GRexten2` (Appendix B, `appendix_unibranch.tex`), proof of item (2): "By the smooth
version of the extension theorem `thm:GRexten`, `π^*φ` admits a unique extension to a psh function
on `Y`". This file proves the local statement behind it, for an arbitrary morphism `ρ : T → X` from
a complex space `T` with domain charts (e.g. a complex manifold, the source of a resolution) to a
complex space `X`:

Let `Z ⊆ X` be analytic and `φ : X → [-∞, ∞)` satisfy condition 2 of `def:unibranch:L105` at every
point of `X \ Z`, be locally bounded above off `Z` near every point of `X`, and be finite at a dense
set of points `ρ(t) ∉ Z`. Then the upper-regularized extension
`η_T = (ρ^*φ)^* = limsup_{T \ ρ⁻¹Z ∋ s → t} φ(ρ(s))` across `ρ⁻¹(Z)` satisfies condition 2 of
`def:unibranch:L105` at every point of `T` (`isLocallyAmbientPSHAt_analyticExtension_comp`).

Proof: in a connected domain chart `F : U → T`, `ρ ∘ F` factors near each point through a local
embedding of `X` in which `Z` is the trace of an analytic set, so `A = (ρ ∘ F)⁻¹(Z)` has local
holomorphic equations in `U`; off `A` the pull-back `φ ∘ ρ ∘ F` is psh (pointwise independence of
the embedding); it is locally bounded above; so the removable-singularity theorem on domains of
`ℂ^d` (`PshAnalyticRemovable.plurisubharmonicOn_extension_of_zeroLocus`, the chart form of
`thm:GRexten` (2)) makes its upper-regularized extension psh on `U`. Upper regularization commutes
with the open embeddings `U ← F⁻¹(T) → T`, so this is `η_T ∘ F`.

Also: local embeddings of an open subspace are local embeddings of the ambient space
(`LocalEmbedding.compOpenImmersion`), and condition 2 at a single point gives ambient disc-psh
representatives along every morphism from a model (`exists_ambient_of_morphism_at`).

Lane PD3, blueprint `pd3.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.HironakaReducedComplexAnalyticSpaces

namespace SGPT.Unibranch.PD3

open SourceReducedComplexSpace

noncomputable section

/-! ### Local embeddings through open immersions -/

/-- A local embedding of `V` composed with an open immersion `j : V → X` is a local embedding of
`X`. -/
def LocalEmbedding.compOpenImmersion {X V : SourceReducedComplexSpace} (e : LocalEmbedding V)
    (j : V ⟶ X) (hj : LocallyRingedSpace.IsOpenImmersion j.hom.left) : LocalEmbedding X where
  dim := e.dim
  ambient := e.ambient
  carrier := e.carrier
  analytic := e.analytic
  map := e.map ≫ j.hom.left
  isOpenImmersion := by
    let _ := e.isOpenImmersion
    let _ := hj
    infer_instance
  overPoint := by
    rw [Category.assoc, Over.w j.hom]
    exact e.overPoint

theorem LocalEmbedding.compOpenImmersion_toPoint {X V : SourceReducedComplexSpace}
    (e : LocalEmbedding V) (j : V ⟶ X) (hj : LocallyRingedSpace.IsOpenImmersion j.hom.left)
    (c : e.carrier) :
    (LocalEmbedding.compOpenImmersion e j hj).toPoint c = j.hom.left.base (e.toPoint c) := rfl

/-- Condition 2 of `def:unibranch:L105` transfers from an open subspace `j : V → X` to `X`. -/
theorem isLocallyAmbientPSHAt_of_openImmersion {X V : SourceReducedComplexSpace} (j : V ⟶ X)
    (hj : LocallyRingedSpace.IsOpenImmersion j.hom.left) {φ : X.obj.left → EReal}
    {v : V.obj.left} (h : V.IsLocallyAmbientPSHAt (fun w => φ (j.hom.left.base w)) v) :
    X.IsLocallyAmbientPSHAt φ (j.hom.left.base v) := by
  obtain ⟨e, ⟨c, rfl⟩, hconn, ψ, hψ, hφ⟩ := h
  exact ⟨LocalEmbedding.compOpenImmersion e j hj, ⟨c, rfl⟩, hconn, ψ, hψ, fun c' => hφ c'⟩

/-! ### Pointwise independence of the embedding -/

/-- If `φ` satisfies condition 2 of `def:unibranch:L105` at `F(c)`, then near `c` the pull-back of
`φ` along a morphism `F` from an embedded model is the restriction of an ambient function satisfying
the disc criterion. -/
theorem exists_ambient_of_morphism_at {X : SourceReducedComplexSpace} {φ : X.obj.left → EReal}
    {n : ℕ} {U : Opens (ComplexModel n)} {C : Set U}
    (F : (modelOver U C).left ⟶ X.obj.left) (hF : F ≫ X.obj.hom = (modelOver U C).hom)
    (c : C) (hφ : X.IsLocallyAmbientPSHAt φ (F.base c)) :
    ∃ W : Set (ComplexModel n), IsOpen W ∧ c.val.val ∈ W ∧ W ⊆ U ∧
      ∃ ψ : ComplexModel n → EReal, SGPT.Foundations.Analysis.DiscPshOn ψ W ∧
        ∀ y : C, y.val.val ∈ W → φ (F.base y) = ψ y.val.val := by
  obtain ⟨e₂, hc, -, ψ, hψ, hφ₂⟩ := hφ
  obtain ⟨W, hW, hcW, hWU, G, hG, hGmaps, hfac⟩ :=
    LocalEmbedding.exists_differentiableOn_factor F hF e₂ c hc
  refine ⟨W, hW, hcW, hWU, fun z => ψ (G z),
    SGPT.PSH.discPshOn_comp_holomorphic hW e₂.ambient.isOpen hG hGmaps hψ, ?_⟩
  intro y hy
  obtain ⟨z, hz, hzy⟩ := hfac y hy
  rw [← hzy, hφ₂ z, hz]

/-! ### Upper regularization at points where the function is upper semicontinuous -/

/-- If `f ≤ g` with `g` upper semicontinuous at `x` and `f x = g x`, then the upper regularization
of `f` at `x` is `f x`. -/
theorem uscRegularization_eq_of_le {Y : Type*} [TopologicalSpace Y] {f g : Y → EReal} {x : Y}
    (hfg : f ≤ g) (hg : UpperSemicontinuousAt g x) (hx : f x = g x) :
    uscRegularization f x = f x :=
  le_antisymm ((uscRegularization_le_of_eventually_le hg (Eventually.of_forall hfg)).trans
    hx.ge) (le_uscRegularization f x)

/-- The regularized extension `analyticExtension Z φ` agrees with `φ` at points off `Z` where `φ`
satisfies condition 2 of `def:unibranch:L105`. -/
theorem analyticExtension_eq_of_isLocallyAmbientPSHAt {X : SourceReducedComplexSpace}
    {Z : Set X.obj.left} {φ : X.obj.left → EReal} {x : X.obj.left} (hx : x ∉ Z)
    (hφ : X.IsLocallyAmbientPSHAt φ x) :
    SGPT.PSH.VariableComplexAtlas.analyticExtension Z φ x = φ x := by
  classical
  have h := uscRegularization_eq_of_le (f := fun y => if y ∈ Z then ⊥ else φ y) (g := φ) (x := x)
    (fun y => by
      by_cases hy : y ∈ Z
      · simp only [hy, if_true, bot_le]
      · simp only [hy, if_false, le_refl])
    hφ.upperSemicontinuousAt (by simp only [hx, if_false])
  unfold SGPT.PSH.VariableComplexAtlas.analyticExtension
  convert h using 1
  simp only [hx, if_false]

/-- The regularized extension dominates the function off `Z`. -/
theorem le_analyticExtension {Y : Type*} [TopologicalSpace Y] {Z : Set Y} {φ : Y → EReal}
    {x : Y} (hx : x ∉ Z) : φ x ≤ SGPT.PSH.VariableComplexAtlas.analyticExtension Z φ x := by
  classical
  have h := le_uscRegularization (fun y => if y ∈ Z then ⊥ else φ y) x
  simp only [hx, if_false] at h
  unfold SGPT.PSH.VariableComplexAtlas.analyticExtension
  convert h using 2

/-! ### The extension along a domain chart -/

section DomainChart

variable {X : SourceReducedComplexSpace} {d : ℕ} {U : Opens (ComplexModel d)}

/-- The set of points of `U` mapped into `Z` by a morphism `G` from the domain model. -/
def chartPreimage (G : (modelOver U (univ : Set U)).left ⟶ X.obj.left) (Z : Set X.obj.left) :
    Set (ComplexModel d) :=
  {z | ∃ h : z ∈ U, G.base (⟨⟨z, h⟩, trivial⟩ : (univ : Set U)) ∈ Z}

theorem mem_chartPreimage_point (G : (modelOver U (univ : Set U)).left ⟶ X.obj.left)
    (Z : Set X.obj.left) (p : (univ : Set U)) :
    p.val.val ∈ chartPreimage G Z ↔ G.base p ∈ Z :=
  ⟨fun ⟨_, h⟩ => h, fun h => ⟨p.val.property, h⟩⟩

/-- **Grauert--Remmert extension in a domain chart.** For a morphism `G : U → X` from a domain,
`Z ⊆ X` analytic and `φ` satisfying condition 2 of `def:unibranch:L105` off `Z` and locally bounded
above off `Z`, the upper-regularized extension of `φ ∘ G` across `G⁻¹(Z)` is psh on `U`. -/
theorem plurisubharmonicOn_extension_chart (G : (modelOver U (univ : Set U)).left ⟶ X.obj.left)
    (hG : G ≫ X.obj.hom = (modelOver U (univ : Set U)).hom) {Z : Set X.obj.left}
    (hZ : X.IsAnalyticSubset Z) {φ : X.obj.left → EReal}
    (hφ : ∀ x, x ∉ Z → X.IsLocallyAmbientPSHAt φ x)
    (hb : ∀ x, ∃ N ∈ 𝓝 x, ∃ C : ℝ, ∀ y ∈ N, y ∉ Z → φ y ≤ C) :
    SGPT.Foundations.Analysis.PlurisubharmonicOn
      (SGPT.Foundations.Analysis.Pending.PshCodimTwoExtension.extension (chartPreimage G Z)
        (domainPullback G φ)) U := by
  intro z hz
  set p : (univ : Set U) := ⟨⟨z, hz⟩, trivial⟩ with hp
  obtain ⟨e₂, hx₂, A', hA', hrep⟩ := hZ (G.base p)
  obtain ⟨W, hW, hzW, hWU, G', hG', hmaps, hfac⟩ :=
    LocalEmbedding.exists_differentiableOn_factor G hG e₂ p hx₂
  obtain ⟨W₂, hW₂, hzW₂, m, h, hh, hhA⟩ :=
    FNR.hasLocalEquationsOn_of_isComplexAnalyticSubset hA' (G' z) (hmaps hzW)
  set Ω : Set (ComplexModel d) := W ∩ G' ⁻¹' W₂ with hΩdef
  have hΩ : IsOpen Ω := hG'.continuousOn.isOpen_inter_preimage hW hW₂
  have hzΩ : z ∈ Ω := ⟨hzW, hzW₂⟩
  have hΩU : Ω ⊆ U := fun y hy => hWU hy.1
  -- local equations of `G⁻¹(Z)` on `Ω`
  have hg : ∀ i, DifferentiableOn ℂ (fun w => h i (G' w)) Ω := fun i =>
    (hh i).comp (hG'.mono inter_subset_left) (fun w hw => hw.2)
  have hgA : ∀ y ∈ Ω, y ∈ chartPreimage G Z ↔ ∀ i, (fun w => h i (G' w)) y = 0 := by
    intro y hy
    set py : (univ : Set U) := ⟨⟨y, hΩU hy⟩, trivial⟩
    obtain ⟨q, hq, hqe⟩ := hfac py hy.1
    rw [show y = py.val.val from rfl, mem_chartPreimage_point, ← hqe]
    have h1 : e₂.toPoint q ∈ Z ↔ q.val ∈ A' := Set.ext_iff.mp hrep q
    rw [h1, ← hhA (G' y) hy.2]
    constructor
    · intro hqA
      exact ⟨q.val, hqA, hq⟩
    · rintro ⟨a, ha, hav⟩
      have : a = q.val := Subtype.ext (hav.trans hq.symm)
      rw [← this]
      exact ha
  -- the pull-back is psh off `G⁻¹(Z)`
  have hpsh : SGPT.Foundations.Analysis.PlurisubharmonicOn (domainPullback G φ)
      (Ω \ chartPreimage G Z) := by
    intro y hy
    set py : (univ : Set U) := ⟨⟨y, hΩU hy.1⟩, trivial⟩
    have hpyZ : G.base py ∉ Z := fun hZ' => hy.2 ((mem_chartPreimage_point G Z py).mpr hZ')
    obtain ⟨W₃, hW₃, hyW₃, hW₃U, ψ, hψ, hφψ⟩ :=
      exists_ambient_of_morphism_at G hG py (hφ _ hpyZ)
    refine ⟨W₃, hW₃, hyW₃, hψ.congr ?_⟩
    intro w hw
    have hwU : w ∈ U := hW₃U hw
    simp only [domainPullback, dif_pos hwU]
    exact (hφψ ⟨⟨w, hwU⟩, trivial⟩ hw).symm
  -- local upper bound
  have hbound : SGPT.Foundations.Analysis.Pending.PshHypersurfaceRemovable.LocallyBoundedAboveOff
      (chartPreimage G Z) Ω (domainPullback G φ) := by
    intro y hy
    set py : (univ : Set U) := ⟨⟨y, hΩU hy⟩, trivial⟩
    obtain ⟨N, hN, C, hC⟩ := hb (G.base py)
    have hι := isOpenEmbedding_domainPoint U
    have hpre : G.base ⁻¹' N ∈ 𝓝 py := G.base.hom.continuous.continuousAt.preimage_mem_nhds hN
    refine ⟨(fun q : (univ : Set U) => (q.val.val : ComplexModel d)) '' (G.base ⁻¹' N),
      hι.isOpenMap.image_mem_nhds hpre, C, ?_⟩
    rintro _ ⟨q, hqN, rfl⟩ hqA
    rw [domainPullback_apply]
    exact hC _ hqN fun hZ' => hqA ((mem_chartPreimage_point G Z q).mpr hZ')
  exact SGPT.Foundations.Analysis.Pending.PshAnalyticRemovable.plurisubharmonicOn_extension_of_zeroLocus
    hΩ hpsh hbound hg hgA z hzΩ

/-- On the points of a domain chart `G : U → X`, the chart extension (on `ℂ^d`) is the regularized
extension of `φ ∘ G` across `G⁻¹(Z)` on the domain model (upper regularization commutes with the
open embedding `U → ℂ^d`). -/
theorem extension_chart_apply (G : (modelOver U (univ : Set U)).left ⟶ X.obj.left)
    (Z : Set X.obj.left) (φ : X.obj.left → EReal) (p : (univ : Set U)) :
    SGPT.Foundations.Analysis.Pending.PshCodimTwoExtension.extension (chartPreimage G Z)
        (domainPullback G φ) p.val.val =
      SGPT.PSH.VariableComplexAtlas.analyticExtension (G.base ⁻¹' Z)
        (fun q => φ (G.base q)) p := by
  classical
  have hι := isOpenEmbedding_domainPoint U
  have hfun : ((fun z => if z ∈ chartPreimage G Z then (⊥ : EReal) else domainPullback G φ z) ∘
      fun q : (univ : Set U) => (q.val.val : ComplexModel d)) =
      fun q => if q ∈ G.base ⁻¹' Z then ⊥ else φ (G.base q) := by
    funext q
    simp only [Function.comp_apply, mem_chartPreimage_point, mem_preimage, domainPullback_apply]
  have h := uscRegularization_comp_isOpenEmbedding_apply
    (fun z => if z ∈ chartPreimage G Z then (⊥ : EReal) else domainPullback G φ z) hι p
  rw [hfun] at h
  rw [SGPT.Foundations.Analysis.Pending.PshCodimTwoExtension.extension_eq_uscRegularization]
  unfold SGPT.PSH.VariableComplexAtlas.analyticExtension
  convert h.symm using 2

end DomainChart

/-- **Source `thm:GRexten2` (2), the extension upstairs.** Let `T` be a complex space with domain
charts (e.g. a complex manifold), `ρ : T → X` a morphism, `Z ⊆ X` analytic, and `φ` satisfy condition
2 of `def:unibranch:L105` at every point off `Z`, be locally bounded above off `Z`, with
`{t | ρ(t) ∉ Z, φ(ρ(t)) ≠ -∞}` dense in `T`. Then the regularized extension
`limsup_{T \ ρ⁻¹Z ∋ s → t} φ(ρ(s))` of `ρ^*φ` satisfies condition 2 of `def:unibranch:L105` at every
point of `T`. -/
theorem isLocallyAmbientPSHAt_analyticExtension_comp {T X : SourceReducedComplexSpace}
    (hT : T.HasDomainCharts) (ρ : T ⟶ X) {Z : Set X.obj.left} (hZ : X.IsAnalyticSubset Z)
    {φ : X.obj.left → EReal} (hφ : ∀ x, x ∉ Z → X.IsLocallyAmbientPSHAt φ x)
    (hb : ∀ x, ∃ N ∈ 𝓝 x, ∃ C : ℝ, ∀ y ∈ N, y ∉ Z → φ y ≤ C)
    (hd : Dense {t | ρ.hom.left.base t ∉ Z ∧ φ (ρ.hom.left.base t) ≠ ⊥}) (t : T.obj.left) :
    T.IsLocallyAmbientPSHAt (SGPT.PSH.VariableComplexAtlas.analyticExtension
      (ρ.hom.left.base ⁻¹' Z) (fun s => φ (ρ.hom.left.base s))) t := by
  obtain ⟨d, U, F, hFo, hF, hUc, htF, -⟩ := hT t univ isOpen_univ trivial
  let G : (modelOver U (univ : Set U)).left ⟶ X.obj.left := F ≫ ρ.hom.left
  have hG : G ≫ X.obj.hom = (modelOver U (univ : Set U)).hom := by
    change (F ≫ ρ.hom.left) ≫ X.obj.hom = _
    rw [Category.assoc, Over.w ρ.hom]
    exact hF
  have hGp : ∀ p, G.base p = ρ.hom.left.base (F.base p) := fun _ => rfl
  have hpsh := plurisubharmonicOn_extension_chart G hG hZ hφ hb
  set ψ := SGPT.Foundations.Analysis.Pending.PshCodimTwoExtension.extension (chartPreimage G Z)
    (domainPullback G φ) with hψ
  have hval : ∀ p : (univ : Set U), ψ p.val.val =
      SGPT.PSH.VariableComplexAtlas.analyticExtension (ρ.hom.left.base ⁻¹' Z)
        (fun s => φ (ρ.hom.left.base s)) (F.base p) := by
    intro p
    rw [hψ, extension_chart_apply]
    have hFe : Topology.IsOpenEmbedding F.base := hFo.base_open
    classical
    have h := uscRegularization_comp_isOpenEmbedding_apply
      (fun s => if s ∈ ρ.hom.left.base ⁻¹' Z then (⊥ : EReal) else φ (ρ.hom.left.base s)) hFe p
    unfold SGPT.PSH.VariableComplexAtlas.analyticExtension
    convert h using 2
    funext q
    by_cases hq : ρ.hom.left.base (F.base q) ∈ Z <;> simp [hq, hGp]
  refine ⟨domainEmbedding U F hFo hF, htF, hUc, ψ, ⟨hpsh.discPshOn, ?_⟩, ?_⟩
  · -- nontriviality from the dense finite locus
    obtain ⟨_, ⟨p, rfl⟩, hpZ, hpfin⟩ := hd.inter_open_nonempty _
      (isOpen_range_domainChart hFo) ⟨t, htF⟩
    refine ⟨p.val.val, p.val.property, ?_⟩
    rw [hval]
    exact ne_bot_of_le_ne_bot hpfin (le_analyticExtension (Z := ρ.hom.left.base ⁻¹' Z)
      (φ := fun s => φ (ρ.hom.left.base s)) hpZ)
  · intro c
    exact (hval c).symm

end

end SGPT.Unibranch.PD3
