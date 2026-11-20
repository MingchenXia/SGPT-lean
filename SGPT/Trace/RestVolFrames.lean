import SGPT.Trace.RestVolIdeal
import SGPT.IGood.DXLow2Shift
import SGPT.Bergman.SourceMultiplierSectionDensity
import SGPT.Trace.OTExtAlongOpenness

/-!
# Restricting holomorphic sections to a submanifold

Lane TRACE-RV, blueprint `claude-rest-vol.tex`, nodes `claude-rest-vol:frames`,
`claude-rest-vol:restrict-section`.  Used in `thm:rest_volume_2` (`chapter_trace.tex`), where the
book compares `{s|_Y : s ∈ H⁰(X, T ⊗ L^k ⊗ 𝓘(kφ))}` with `H⁰(Y, T|_Y ⊗ L|_Y^k ⊗ Res_Y 𝓘(kφ))`.

For a holomorphic map `f : V → X` and holomorphic line bundles `L`, `T` on `X`, the bundle
`(L^k ⊗ T)|_V` of the book is `twistedPower (f^*L) (f^*T) k`, whose fibres are literally those of
`L^k ⊗ T`.

* `pullFrame`: the pullback of an atlas frame; `twistedPowerAtlasFrame_pull_symm`: the product
  frames of `(f^*L)^k ⊗ f^*T` built from pulled-back frames are the product frames of `L^k ⊗ T`
  at `f(y)`; `twistedPowerAtlasFrame_pull_coord`: hence the coordinates agree.
* `restrictSection s = s|_V`: the restriction of a holomorphic section of `L^k ⊗ T` is a
  holomorphic section of `(f^*L)^k ⊗ f^*T` (`restrictSectionLinear`, `ℂ`-linear).
* `mem_fullHolomorphicIdealSections_of_frame`, `coefficient_mem_of_mem_full`: membership in
  `H⁰(V, E ⊗ 𝓐)` read on one atlas frame at each point.
* `restrictSection_mem_restrictIdeal`: for `W ⊆ X` a closed submanifold,
  `s ∈ H⁰(X, L^k ⊗ T ⊗ 𝓘(kφ)) ⇒ s|_W ∈ H⁰(W, (L^k ⊗ T)|_W ⊗ Res_W 𝓘(kφ))`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.Trace.RestVol

open Set Filter Bundle TopologicalSpace
open scoped Topology ContDiff Manifold TensorProduct
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.SubmanifoldChartedSpace
open SGPT.Foundations.Analysis.Pending.SubmanifoldIdealRestriction
open SGPT.Foundations.Analysis.Pending.HironakaSmoothCentreRealDomainActualSheafStalk
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.QuantizationDraft
  SGPT.Bergman.MultiplierSectionsDraft SGPT.Bergman.CompactHolomorphicSectionsDraft
open SGPT.IGood.DXLow2
open HermitianHolomorphicLineBundle

/-! ### Membership in `H⁰(V, E ⊗ 𝓐)` read on one frame -/

section Membership

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]
  (V : X → Type) [∀ x, NormedAddCommGroup (V x)] [∀ x, NormedSpace ℂ (V x)]
  [TopologicalSpace (TotalSpace ℂ V)] [FiberBundle ℂ V] [VectorBundle ℂ ℂ V]
  [ContMDiffVectorBundle ∞ ℂ V 𝓘(ℂ, ComplexModel n)]

/-- A section whose coefficient at each point, in some atlas frame, lies in `𝓐` belongs to
`H⁰(X, V ⊗ 𝓐)` (no coherence needed). -/
theorem mem_fullHolomorphicIdealSections_of_frame (A : GermIdeal n X)
    (s : HolomorphicSections (n := n) V)
    (h : ∀ x : X, ∃ e : OriginalFrame V, x ∈ e.val.baseSet ∧
      A.mem x (sectionCoefficient V e.val s)) :
    s ∈ fullHolomorphicIdealSections (n := n) V A := by
  change globalSectionSheafEquiv (n := n) V s ∈ idealOpenSectionSubmodule (n := n) V A ⊤
  rw [mem_idealOpenSectionSubmodule_iff_preferred]
  intro x
  obtain ⟨e, hx, hmem⟩ := h x.val
  apply (localFrameCoefficientGerm_mem_iff (n := n) V A ⊤ (preferredOriginalFrame V x.val) e _ x
    (mem_baseSet_trivializationAt ℂ V x.val) hx).mpr
  have hg := actualOriginalFunctionGerm_eq_section
    (frameOpen V (⊤ : Opens X) e) x.val ⟨Set.mem_univ x.val, hx⟩
    (localFrameCoefficient (n := n) V ⊤ e (globalSectionSheafEquiv (n := n) V s))
    (sectionCoefficient V e.val s) (originalSectionCoefficient_holomorphicAt (n := n) V e s hx)
    (localFrameCoefficient_extension_eventually (n := n) V e s hx)
  change (actualComplexStructureSheaf (n := n) X).presheaf.germ
    (frameOpen V (⊤ : Opens X) e) x.val ⟨Set.mem_univ x.val, hx⟩ _ ∈ _
  rw [← hg]
  exact Ideal.subset_span ⟨_, _, hmem, rfl⟩

/-- For a coherent `𝓐`, the coefficients of a section of `H⁰(X, V ⊗ 𝓐)` in every atlas frame lie
in `𝓐`. -/
theorem coefficient_mem_of_mem_full (A : GermIdeal n X) (hA : A.IsCoherent)
    {s : HolomorphicSections (n := n) V} (hs : s ∈ fullHolomorphicIdealSections (n := n) V A)
    (e : OriginalFrame V) {x : X} (hx : x ∈ e.val.baseSet) :
    A.mem x (sectionCoefficient V e.val s) :=
  (localFrameCoefficientGerm_mem_iff_originalCoefficient (n := n) V A hA e s hx).mp
    (hs e ⟨x, Set.mem_univ x⟩ hx)

end Membership

/-! ### Pulled-back frames -/

section Frames

variable {n m : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]
  {V : Type} [TopologicalSpace V] [ChartedSpace (ComplexModel m) V] [IsComplexManifold m V]
  (f : ContMDiffMap 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) V X ∞)

/-- The pullback `f^*e` of an atlas frame `e` of `L`, an atlas frame of `f^*L`. -/
def pullFrame {L : HermitianHolomorphicLineBundle.{0, 0} n X} (e : AtlasFrame L) :
    AtlasFrame (restrictBundle L f) :=
  ⟨e.val.pullback f, ⟨e.val, e.property, rfl⟩⟩

theorem mem_pullFrame_baseSet {L : HermitianHolomorphicLineBundle.{0, 0} n X} (e : AtlasFrame L)
    {y : V} (hy : f y ∈ e.val.baseSet) : y ∈ (pullFrame f e).val.baseSet := hy

theorem pullFrame_symm_one {L : HermitianHolomorphicLineBundle.{0, 0} n X} (e : AtlasFrame L)
    {y : V} (hy : f y ∈ e.val.baseSet) :
    (pullFrame f e).val.symm y 1 = e.val.symm (f y) 1 :=
  SGPT.Toric.F1IntersectionDraft.nativeHolomorphicPullbackFrame_symm L f e.val hy 1

/-- The fibres of `(f^*L)^{⊗(k+1)}` at `y` are those of `L^{⊗(k+1)}` at `f(y)`. -/
def posPowFiberEquiv (L : HermitianHolomorphicLineBundle.{0, 0} n X) (y : V) :
    ∀ k : ℕ, (positivePower (restrictBundle L f) k).Fiber y ≃ₗ[ℂ] (positivePower L k).Fiber (f y)
  | 0 => LinearEquiv.refl ℂ (L.Fiber (f y))
  | k + 1 => TensorProduct.congr (posPowFiberEquiv L y k) (LinearEquiv.refl ℂ (L.Fiber (f y)))

/-- The fibres of `(f^*L)^k ⊗ f^*T` at `y` are those of `L^k ⊗ T` at `f(y)`. -/
def twistedFiberEquiv (L T : HermitianHolomorphicLineBundle.{0, 0} n X) (y : V) :
    ∀ k : ℕ, (twistedPower (restrictBundle L f) (restrictBundle T f) k).Fiber y ≃ₗ[ℂ]
      (twistedPower L T k).Fiber (f y)
  | 0 => TensorProduct.congr (LinearEquiv.refl ℂ ℂ) (LinearEquiv.refl ℂ (T.Fiber (f y)))
  | k + 1 => TensorProduct.congr (posPowFiberEquiv f L y k) (LinearEquiv.refl ℂ (T.Fiber (f y)))

theorem posPowFiberEquiv_frame {L : HermitianHolomorphicLineBundle.{0, 0} n X}
    (e : AtlasFrame L) {y : V} (hy : f y ∈ e.val.baseSet) :
    ∀ k : ℕ, posPowFiberEquiv f L y k ((positivePowerAtlasFrame (pullFrame f e) k).val.symm y 1) =
      (positivePowerAtlasFrame e k).val.symm (f y) 1
  | 0 => pullFrame_symm_one f e hy
  | k + 1 => by
    have hW := positivePowerAtlasFrame_mem (pullFrame f e) (mem_pullFrame_baseSet f e hy) k
    have hX := positivePowerAtlasFrame_mem e hy k
    change posPowFiberEquiv f L y (k + 1)
        ((tensorAtlasFrame (positivePowerAtlasFrame (pullFrame f e) k) (pullFrame f e)).val.symm
          y 1) = (tensorAtlasFrame (positivePowerAtlasFrame e k) e).val.symm (f y) 1
    rw [tensorAtlasFrame_symm _ _ ⟨hW, mem_pullFrame_baseSet f e hy⟩,
      tensorAtlasFrame_symm _ _ ⟨hX, hy⟩]
    change TensorProduct.congr (posPowFiberEquiv f L y k) (LinearEquiv.refl ℂ (L.Fiber (f y)))
      ((1 : ℂ) • _) = _
    rw [map_smul, TensorProduct.congr_tmul, posPowFiberEquiv_frame e hy k,
      LinearEquiv.refl_apply, pullFrame_symm_one f e hy]

theorem twistedFiberEquiv_frame {L T : HermitianHolomorphicLineBundle.{0, 0} n X}
    (e : AtlasFrame L) (g : AtlasFrame T) {y : V} (he : f y ∈ e.val.baseSet)
    (hg : f y ∈ g.val.baseSet) (k : ℕ) :
    twistedFiberEquiv f L T y k
        ((twistedPowerAtlasFrame (pullFrame f e) (pullFrame f g) k).val.symm y 1) =
      (twistedPowerAtlasFrame e g k).val.symm (f y) 1 := by
  cases k with
  | zero =>
    change twistedFiberEquiv f L T y 0
        ((tensorAtlasFrame unitAtlasFrame (pullFrame f g)).val.symm y 1) =
      (tensorAtlasFrame unitAtlasFrame g).val.symm (f y) 1
    rw [tensorAtlasFrame_symm _ _ ⟨Set.mem_univ y, mem_pullFrame_baseSet f g hg⟩,
      tensorAtlasFrame_symm _ _ ⟨Set.mem_univ (f y), hg⟩]
    change TensorProduct.congr (LinearEquiv.refl ℂ ℂ) (LinearEquiv.refl ℂ (T.Fiber (f y)))
      ((1 : ℂ) • _) = _
    rw [map_smul, TensorProduct.congr_tmul, LinearEquiv.refl_apply, LinearEquiv.refl_apply,
      pullFrame_symm_one f g hg]
    rfl
  | succ k =>
    have hW := positivePowerAtlasFrame_mem (pullFrame f e) (mem_pullFrame_baseSet f e he) k
    have hX := positivePowerAtlasFrame_mem e he k
    change twistedFiberEquiv f L T y (k + 1)
        ((tensorAtlasFrame (positivePowerAtlasFrame (pullFrame f e) k) (pullFrame f g)).val.symm
          y 1) = (tensorAtlasFrame (positivePowerAtlasFrame e k) g).val.symm (f y) 1
    rw [tensorAtlasFrame_symm _ _ ⟨hW, mem_pullFrame_baseSet f g hg⟩,
      tensorAtlasFrame_symm _ _ ⟨hX, hg⟩]
    change TensorProduct.congr (posPowFiberEquiv f L y k) (LinearEquiv.refl ℂ (T.Fiber (f y)))
      ((1 : ℂ) • _) = _
    rw [map_smul, TensorProduct.congr_tmul, posPowFiberEquiv_frame f e he k,
      LinearEquiv.refl_apply, pullFrame_symm_one f g hg]

/-- In an atlas frame of a line bundle every vector is its coordinate times the frame. -/
theorem eq_frameCoord_smul_frame {W' : HermitianHolomorphicLineBundle.{0, 0} m V}
    (H : AtlasFrame W') {y : V} (hy : y ∈ H.val.baseSet) (v : W'.Fiber y) :
    v = frameCoord H y v • H.val.symm y 1 := by
  let := H.property
  have h1 : H.val.symm y (frameCoord H y v) = v := by
    rw [frameCoord_apply H hy]
    exact H.val.symm_apply_apply_mk hy v
  have h2 : H.val.symm y (frameCoord H y v) = frameCoord H y v • H.val.symm y 1 := by
    have := (H.val.symmₗ ℂ y).map_smul (frameCoord H y v) 1
    rwa [Trivialization.symmₗ_apply _ hy, Trivialization.symmₗ_apply _ hy, smul_eq_mul,
      mul_one] at this
  rw [← h2, h1]

/-- **The coordinates of `(L^k ⊗ T)|_V` in pulled-back product frames are those of `L^k ⊗ T`.** -/
theorem twistedPowerAtlasFrame_pull_coord {L T : HermitianHolomorphicLineBundle.{0, 0} n X}
    (e : AtlasFrame L) (g : AtlasFrame T) {y : V} (he : f y ∈ e.val.baseSet)
    (hg : f y ∈ g.val.baseSet) (k : ℕ)
    (v : (twistedPower (restrictBundle L f) (restrictBundle T f) k).Fiber y) :
    frameCoord (twistedPowerAtlasFrame (pullFrame f e) (pullFrame f g) k) y v =
      frameCoord (twistedPowerAtlasFrame e g k) (f y) (twistedFiberEquiv f L T y k v) := by
  set H := twistedPowerAtlasFrame (pullFrame f e) (pullFrame f g) k
  set G := twistedPowerAtlasFrame e g k
  have hH : y ∈ H.val.baseSet :=
    twistedPowerAtlasFrame_mem _ _ (mem_pullFrame_baseSet f e he) (mem_pullFrame_baseSet f g hg) k
  have hG : f y ∈ G.val.baseSet := twistedPowerAtlasFrame_mem e g he hg k
  conv_rhs => rw [eq_frameCoord_smul_frame H hH v]
  rw [map_smul, map_smul, twistedFiberEquiv_frame f e g he hg k, frameCoord_symm_one G hG,
    smul_eq_mul, mul_one]

end Frames

/-! ### Restriction of sections -/

section Restriction

variable {n m : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]
  {V : Type} [TopologicalSpace V] [ChartedSpace (ComplexModel m) V] [IsComplexManifold m V]
  (f : ContMDiffMap 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) V X ∞)
  {L T : HermitianHolomorphicLineBundle.{0, 0} n X}

/-- The coordinate of `v` in the product frame of `L^k ⊗ T` built from the frames at `x₀`. -/
theorem coord_restrict_eq (k : ℕ) (y₀ y : V)
    (hy : f y ∈ (trivializationAt ℂ L.Fiber (f y₀)).baseSet ∩
      (trivializationAt ℂ T.Fiber (f y₀)).baseSet)
    (w : (twistedPower L T k).Fiber (f y)) :
    ((twistedPowerAtlasFrame (pullFrame f (⟨trivializationAt ℂ L.Fiber (f y₀), inferInstance⟩ :
        AtlasFrame L)) (pullFrame f (⟨trivializationAt ℂ T.Fiber (f y₀), inferInstance⟩ :
        AtlasFrame T)) k).val ⟨y, (twistedFiberEquiv f L T y k).symm w⟩).2 =
      ((twistedPowerAtlasFrame (⟨trivializationAt ℂ L.Fiber (f y₀), inferInstance⟩ : AtlasFrame L)
        (⟨trivializationAt ℂ T.Fiber (f y₀), inferInstance⟩ : AtlasFrame T) k).val ⟨f y, w⟩).2 := by
  set e : AtlasFrame L := ⟨trivializationAt ℂ L.Fiber (f y₀), inferInstance⟩
  set g : AtlasFrame T := ⟨trivializationAt ℂ T.Fiber (f y₀), inferInstance⟩
  have hH : y ∈ (twistedPowerAtlasFrame (pullFrame f e) (pullFrame f g) k).val.baseSet :=
    twistedPowerAtlasFrame_mem _ _ (mem_pullFrame_baseSet f e hy.1)
      (mem_pullFrame_baseSet f g hy.2) k
  have hG : f y ∈ (twistedPowerAtlasFrame e g k).val.baseSet :=
    twistedPowerAtlasFrame_mem e g hy.1 hy.2 k
  rw [← frameCoord_apply _ hH, ← frameCoord_apply _ hG,
    twistedPowerAtlasFrame_pull_coord f e g hy.1 hy.2 k, LinearEquiv.apply_symm_apply]

/-- **The restriction `s|_V`** of a holomorphic section of `L^k ⊗ T`: a holomorphic section of
`(f^*L)^k ⊗ f^*T`, `y ↦ s(f(y))`. -/
def restrictSection {k : ℕ} (s : twistedSections L T k) :
    twistedSections (restrictBundle L f) (restrictBundle T f) k where
  toFun y := (twistedFiberEquiv f L T y k).symm (s (f y))
  contMDiff_toFun := by
    intro y₀
    let e : AtlasFrame L := ⟨trivializationAt ℂ L.Fiber (f y₀), inferInstance⟩
    let g : AtlasFrame T := ⟨trivializationAt ℂ T.Fiber (f y₀), inferInstance⟩
    have he : f y₀ ∈ e.val.baseSet := mem_baseSet_trivializationAt ℂ L.Fiber (f y₀)
    have hg : f y₀ ∈ g.val.baseSet := mem_baseSet_trivializationAt ℂ T.Fiber (f y₀)
    let G := twistedPowerAtlasFrame e g k
    let H := twistedPowerAtlasFrame (pullFrame f e) (pullFrame f g) k
    let := G.property
    let := H.property
    have hG : f y₀ ∈ G.val.baseSet := twistedPowerAtlasFrame_mem e g he hg k
    have hH : y₀ ∈ H.val.baseSet :=
      twistedPowerAtlasFrame_mem _ _ (mem_pullFrame_baseSet f e he) (mem_pullFrame_baseSet f g hg) k
    apply (H.val.contMDiffAt_section_iff hH).mpr
    have hs := (G.val.contMDiffAt_section_iff hG).mp (s.contMDiff (f y₀))
    have hcomp := hs.comp y₀ (f.contMDiff y₀)
    apply hcomp.congr_of_eventuallyEq
    have hopen : IsOpen (f ⁻¹' (e.val.baseSet ∩ g.val.baseSet)) :=
      (e.val.open_baseSet.inter g.val.open_baseSet).preimage f.contMDiff.continuous
    filter_upwards [hopen.mem_nhds ⟨he, hg⟩] with y hy
    exact coord_restrict_eq f k y₀ y hy (s (f y))

theorem restrictSection_apply {k : ℕ} (s : twistedSections L T k) (y : V) :
    restrictSection f s y = (twistedFiberEquiv f L T y k).symm (s (f y)) := rfl

/-- Restriction is `ℂ`-linear. -/
def restrictSectionLinear (k : ℕ) :
    twistedSections L T k →ₗ[ℂ] twistedSections (restrictBundle L f) (restrictBundle T f) k where
  toFun := restrictSection f
  map_add' s t := by
    ext y
    simp [restrictSection_apply]
  map_smul' c s := by
    ext y
    simp [restrictSection_apply]

theorem restrictSectionLinear_apply (k : ℕ) (s : twistedSections L T k) :
    restrictSectionLinear f k s = restrictSection f s := rfl

end Restriction

/-! ### Submanifolds -/

section Submanifold

variable {n m : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {W : Set X} [ChartedSpace (ComplexModel m) W] [IsComplexManifold m W]
  (hval : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ (Subtype.val : W → X))
  {L T : HermitianHolomorphicLineBundle.{0, 0} n X}

/-- **`s ∈ H⁰(X, L^k ⊗ T ⊗ 𝓘(kφ)) ⇒ s|_W ∈ H⁰(W, (L^k ⊗ T)|_W ⊗ Res_W 𝓘(kφ))`.** -/
theorem restrictSection_mem_restrictIdeal {k : ℕ} {φ : X → EReal}
    (hφ : IsGlobalQuasiPshPotential (n := n) φ) {s : twistedSections L T k}
    (hs : s ∈ fullHolomorphicIdealSections (n := n) (twistedPower L T k).Fiber
      (sourceDegreeMultiplierIdeal (n := n) k φ)) :
    restrictSection ⟨Subtype.val, hval⟩ s ∈ fullHolomorphicIdealSections (n := m)
      (twistedPower (restrictBundle L ⟨Subtype.val, hval⟩)
        (restrictBundle T ⟨Subtype.val, hval⟩) k).Fiber
      (restrictIdeal (k := m) (W := W) (sourceDegreeMultiplierIdeal (n := n) k φ)) := by
  set f : ContMDiffMap 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) W X ∞ := ⟨Subtype.val, hval⟩
  apply mem_fullHolomorphicIdealSections_of_frame
  intro y
  let e : AtlasFrame L := ⟨trivializationAt ℂ L.Fiber (f y), inferInstance⟩
  let g : AtlasFrame T := ⟨trivializationAt ℂ T.Fiber (f y), inferInstance⟩
  have he : f y ∈ e.val.baseSet := mem_baseSet_trivializationAt ℂ L.Fiber (f y)
  have hg : f y ∈ g.val.baseSet := mem_baseSet_trivializationAt ℂ T.Fiber (f y)
  let G := twistedPowerAtlasFrame e g k
  let H := twistedPowerAtlasFrame (pullFrame f e) (pullFrame f g) k
  have hG : f y ∈ G.val.baseSet := twistedPowerAtlasFrame_mem e g he hg k
  have hH : y ∈ H.val.baseSet :=
    twistedPowerAtlasFrame_mem _ _ (mem_pullFrame_baseSet f e he) (mem_pullFrame_baseSet f g hg) k
  refine ⟨⟨H.val, H.property⟩, hH, ?_⟩
  have hX := coefficient_mem_of_mem_full (twistedPower L T k).Fiber _
    (sourceDegreeMultiplierIdeal_isCoherent k hφ) hs ⟨G.val, G.property⟩ hG
  rw [mem_restrictIdeal_iff]
  refine ⟨originalSectionCoefficient_holomorphicAt (n := m) _ ⟨H.val, H.property⟩ _ hH, 1,
    fun _ => sectionCoefficient (twistedPower L T k).Fiber G.val s ∘ Subtype.val,
    fun _ _ => 1, fun _ => ⟨_, hX, rfl⟩, fun _ => holomorphicAt_const 1, ?_⟩
  have hopen : IsOpen (f ⁻¹' (e.val.baseSet ∩ g.val.baseSet)) :=
    (e.val.open_baseSet.inter g.val.open_baseSet).preimage f.contMDiff.continuous
  filter_upwards [hopen.mem_nhds ⟨he, hg⟩] with y' hy'
  simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton, one_mul,
    Function.comp_apply]
  exact coord_restrict_eq f k y y' hy' (s (f y'))

include hval in
/-- **Frame change along `W`**: the coefficient of a section of `V|_W` in the preferred frame at
`y` is a holomorphic multiple of its coefficient in any atlas frame `G` defined at `y`. -/
theorem alongCoefficient_eventuallyEq_mul_of_frame
    (V : X → Type) [∀ x, NormedAddCommGroup (V x)] [∀ x, NormedSpace ℂ (V x)]
    [TopologicalSpace (TotalSpace ℂ V)] [FiberBundle ℂ V] [VectorBundle ℂ ℂ V]
    [ContMDiffVectorBundle ∞ ℂ V 𝓘(ℂ, ComplexModel n)]
    (G : Trivialization ℂ (TotalSpace.proj : TotalSpace ℂ V → X)) [MemTrivializationAtlas G]
    (s : (y : W) → V y) (y : W) (hy : y.val ∈ G.baseSet) :
    ∃ h : W → ℂ, HolomorphicAt m h y ∧
      SGPT.Trace.TwistedL2.alongCoefficient V (trivializationAt ℂ V y.val) s =ᶠ[𝓝 y]
        fun w => h w * SGPT.Trace.TwistedL2.alongCoefficient V G s w := by
  set e' := trivializationAt ℂ V y.val with he'
  set O : Set W := Subtype.val ⁻¹' (G.baseSet ∩ e'.baseSet) with hO
  have hOopen : IsOpen O := (G.open_baseSet.inter e'.open_baseSet).preimage hval.continuous
  have hyO : y ∈ O := ⟨hy, mem_baseSet_trivializationAt ℂ V y.val⟩
  set h : W → ℂ := fun w => (G.coordChangeL ℂ e' w.val) 1 with hh
  refine ⟨h, ?_, ?_⟩
  · have hcc : ContMDiffOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ →L[ℂ] ℂ) ∞
        (fun b : X => (G.coordChangeL ℂ e' b : ℂ →L[ℂ] ℂ)) (G.baseSet ∩ e'.baseSet) :=
      ContMDiffVectorBundle.contMDiffOn_coordChangeL G e'
    have hcc1 : ContMDiffOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) ∞
        (fun b : X => (G.coordChangeL ℂ e' b : ℂ →L[ℂ] ℂ) 1) (G.baseSet ∩ e'.baseSet) :=
      hcc.clm_apply contMDiffOn_const
    have hW : ContMDiffOn 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ℂ) ∞ h O :=
      hcc1.comp hval.contMDiffOn (fun w hw => hw)
    filter_upwards [hOopen.mem_nhds hyO] with w hw
    exact (hW.contMDiffAt (hOopen.mem_nhds hw)).mdifferentiableAt (by simp)
  · filter_upwards [hOopen.mem_nhds hyO] with w hw
    have hlin : ∀ z : ℂ, G.coordChangeL ℂ e' w.val z = G.coordChangeL ℂ e' w.val 1 * z := by
      intro z
      have := (G.coordChangeL ℂ e' w.val).map_smul z 1
      rw [smul_eq_mul, mul_one, smul_eq_mul] at this
      rw [this, mul_comm]
    simp only [SGPT.Trace.TwistedL2.alongCoefficient, hh]
    rw [← hlin, G.coordChangeL_apply e' hw, G.symm_apply_apply_mk hw.1]

/-- **A section of `(L^k ⊗ T)|_W ⊗ 𝓘(ku)` on `W` is a section along `W` in the sense of
`thm:OT_ext`** (`IsAlongMultiplierSection`, coefficients in the ambient frames). -/
theorem isAlongMultiplierSection_of_mem {k : ℕ} {u : W → EReal}
    (hu : IsGlobalQuasiPshPotential (n := m) u)
    {t : twistedSections (restrictBundle L ⟨Subtype.val, hval⟩)
      (restrictBundle T ⟨Subtype.val, hval⟩) k}
    (ht : t ∈ fullHolomorphicIdealSections (n := m)
      (twistedPower (restrictBundle L ⟨Subtype.val, hval⟩)
        (restrictBundle T ⟨Subtype.val, hval⟩) k).Fiber (sourceDegreeMultiplierIdeal (n := m) k u)) :
    SGPT.Trace.TwistedL2.IsAlongMultiplierSection (twistedPower L T k).Fiber (m := m) (k : ℝ) u
      (fun y => twistedFiberEquiv ⟨Subtype.val, hval⟩ L T y k (t y)) := by
  let f : ContMDiffMap 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) W X ∞ := ⟨Subtype.val, hval⟩
  intro y
  let e : AtlasFrame L := ⟨trivializationAt ℂ L.Fiber (f y), inferInstance⟩
  let g : AtlasFrame T := ⟨trivializationAt ℂ T.Fiber (f y), inferInstance⟩
  have he : f y ∈ e.val.baseSet := mem_baseSet_trivializationAt ℂ L.Fiber (f y)
  have hg : f y ∈ g.val.baseSet := mem_baseSet_trivializationAt ℂ T.Fiber (f y)
  let G := twistedPowerAtlasFrame e g k
  let H := twistedPowerAtlasFrame (pullFrame f e) (pullFrame f g) k
  let := G.property
  have hG : f y ∈ G.val.baseSet := twistedPowerAtlasFrame_mem e g he hg k
  have hH : y ∈ H.val.baseSet :=
    twistedPowerAtlasFrame_mem _ _ (mem_pullFrame_baseSet f e he) (mem_pullFrame_baseSet f g hg) k
  have hW := coefficient_mem_of_mem_full _ _ (sourceDegreeMultiplierIdeal_isCoherent k hu) ht
    ⟨H.val, H.property⟩ hH
  have hopen : IsOpen (f ⁻¹' (e.val.baseSet ∩ g.val.baseSet)) :=
    (e.val.open_baseSet.inter g.val.open_baseSet).preimage f.contMDiff.continuous
  have hGcoef : sectionCoefficient _ H.val t =ᶠ[𝓝 y]
      SGPT.Trace.TwistedL2.alongCoefficient (twistedPower L T k).Fiber G.val
        (fun y => twistedFiberEquiv f L T y k (t y)) := by
    filter_upwards [hopen.mem_nhds ⟨he, hg⟩] with y' hy'
    have := coord_restrict_eq f k y y' hy' (twistedFiberEquiv f L T y' k (t y'))
    rw [LinearEquiv.symm_apply_apply] at this
    exact this
  obtain ⟨h, hh, hfr⟩ := alongCoefficient_eventuallyEq_mul_of_frame hval (twistedPower L T k).Fiber
    G.val (fun y => twistedFiberEquiv f L T y k (t y)) y hG
  have h1 := SGPT.Trace.OTExt.mem_multiplierIdeal_congr hW hGcoef
  have h2 := SGPT.Trace.OTExt.mem_multiplierIdeal_mul h1 hh
  exact SGPT.Trace.OTExt.mem_multiplierIdeal_congr h2 hfr.symm

end Submanifold

end SGPT.Trace.RestVol
