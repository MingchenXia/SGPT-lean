import SGPT.LineBundle.TMetricRescale
import SGPT.Bergman.SourceTwistedMultiplierSections
import SGPT.Bergman.Quant2SmoothWeakConv

/-!
# `H⁰(X, T ⊗ L^k ⊗ 𝓘(kφ))` depends only on the holomorphic line bundle `T`

Lane T-METRIC, blueprint `claude-t-metric`, node `claude-t-metric:sections`. Source
`thm:DXmain1` (chapter *`𝓘`-good singularities*): the twist `T` is an arbitrary holomorphic line
bundle, and `h⁰(X, T ⊗ L^k ⊗ 𝓘(kφ))` involves no metric on `T`.

* `FrameIdentityEquiv V W`: a fibrewise linear equivalence `V_x ≃ W_x` of holomorphic line bundles
  that reads as the identity of `ℂ` in suitable atlas frames around every point (a holomorphic
  bundle isomorphism, normalized to be the identity in the chosen frames).
* `FrameIdentityEquiv.sectionEquiv`: it induces a linear equivalence of the spaces of ALL
  holomorphic sections, which maps `H⁰(X, V ⊗ 𝓐)` onto `H⁰(X, W ⊗ 𝓐)` for EVERY ideal sheaf `𝓐`
  (`FrameIdentityEquiv.idealSectionEquiv`; no coherence needed: the coefficient germs agree).
* `FrameIdentityEquiv.refl`, `FrameIdentityEquiv.symm`, `FrameIdentityEquiv.tensorCongr`
  (`A ≅ A'`, `T ≅ T'` give `A ⊗ T ≅ A' ⊗ T'`), `FrameIdentityEquiv.positivePowerCongr`,
  `FrameIdentityEquiv.twistedPowerCongr`: compatibility with the literal tensor powers `L^k ⊗ T`
  (`twistedPower`).
* `literalSectionsCongr`: `H⁰(X, L^k ⊗ T ⊗ 𝓘(kφ)) ≃ H⁰(X, L'^k ⊗ T' ⊗ 𝓘(kφ))` for `L ≅ L'`,
  `T ≅ T'`, and `normalizedH0_congr`: the normalized dimensions agree.
* `rescaleEquiv`: the identity `T ≅ rescale T ρ` (same holomorphic bundle, metric `ρ h_T`), hence
  `normalizedH0_rescale`, `normalizedH0_rescale_rescale`: `h⁰(X, L^k ⊗ T ⊗ 𝓘(kφ))` does not
  depend on the metrics of `L` and `T`.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.LineBundle.TMetric

open Bundle Set Filter TopologicalSpace TensorProduct
open scoped Topology Manifold ContDiff TensorProduct
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending.HironakaSmoothCentreRealDomainActualSheafStalk
open SGPT.Bergman.TensorDictionaryDraft HermitianHolomorphicLineBundle
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.CompactHolomorphicSectionsDraft
open SGPT.Bergman.MultiplierSectionsDraft

/-! ### Germs of frame coefficients -/

section Germs

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

/-- The germ of an original holomorphic function depends only on its germ. -/
theorem actualOriginalFunctionGerm_congr {x : X} {f g : X → ℂ} (hf : HolomorphicAt n f x)
    (hg : HolomorphicAt n g x) (hfg : f =ᶠ[𝓝 x] g) :
    actualOriginalFunctionGerm x f hf = actualOriginalFunctionGerm x g hg := by
  apply (actualStalkChartEquiv (n := n) x).injective
  rw [actualOriginalFunctionGerm_chart, actualOriginalFunctionGerm_chart]
  exact chartTranslatedGerm_congr_original x f g hf hg hfg

variable (V : X → Type) [∀ x, NormedAddCommGroup (V x)] [∀ x, NormedSpace ℂ (V x)]
  [TopologicalSpace (TotalSpace ℂ V)] [FiberBundle ℂ V] [VectorBundle ℂ ℂ V]
  [ContMDiffVectorBundle ∞ ℂ V (𝓘(ℂ, ComplexModel n))]

/-- The structure-sheaf germ of the coefficient of a global section in an atlas frame is the germ
of the coefficient function. -/
theorem localFrameCoefficientGerm_top_eq (e : OriginalFrame V) (s : HolomorphicSections (n := n) V)
    {x : X} (hx : x ∈ e.val.baseSet) :
    localFrameCoefficientGerm (n := n) V ⊤ e (globalSectionSheafEquiv (n := n) V s)
        ⟨x, Set.mem_univ x⟩ hx =
      actualOriginalFunctionGerm x (sectionCoefficient V e.val s)
        (originalSectionCoefficient_holomorphicAt (n := n) V e s hx) :=
  (actualOriginalFunctionGerm_eq_section (frameOpen V (⊤ : Opens X) e) x ⟨Set.mem_univ x, hx⟩
    (localFrameCoefficient (n := n) V ⊤ e (globalSectionSheafEquiv (n := n) V s))
    (sectionCoefficient V e.val s) (originalSectionCoefficient_holomorphicAt (n := n) V e s hx)
    (localFrameCoefficient_extension_eventually (n := n) V e s hx)).symm

end Germs

/-! ### Frame-identity isomorphisms of line bundles -/

section Transport

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]
  (V W : X → Type)
  [∀ x, NormedAddCommGroup (V x)] [∀ x, NormedSpace ℂ (V x)]
  [TopologicalSpace (TotalSpace ℂ V)] [FiberBundle ℂ V] [VectorBundle ℂ ℂ V]
  [ContMDiffVectorBundle ∞ ℂ V (𝓘(ℂ, ComplexModel n))]
  [∀ x, NormedAddCommGroup (W x)] [∀ x, NormedSpace ℂ (W x)]
  [TopologicalSpace (TotalSpace ℂ W)] [FiberBundle ℂ W] [VectorBundle ℂ ℂ W]
  [ContMDiffVectorBundle ∞ ℂ W (𝓘(ℂ, ComplexModel n))]

/-- A fibrewise linear equivalence of holomorphic line bundles which, around every point, reads
as the identity of `ℂ` in some pair of atlas frames. In particular it is a holomorphic bundle
isomorphism; no compatibility with the metrics is required. -/
structure FrameIdentityEquiv where
  /-- The fibrewise linear equivalence. -/
  equiv : ∀ x, V x ≃ₗ[ℂ] W x
  /-- Around each point, the equivalence is the identity in some pair of atlas frames. -/
  exists_frames : ∀ x, ∃ (e : OriginalFrame V) (f : OriginalFrame W),
    x ∈ e.val.baseSet ∧ x ∈ f.val.baseSet ∧
      ∀ y ∈ e.val.baseSet ∩ f.val.baseSet, ∀ w : V y, (f.val ⟨y, equiv y w⟩).2 = (e.val ⟨y, w⟩).2

namespace FrameIdentityEquiv

variable {V W}

/-- The inverse isomorphism. -/
def symm (Φ : FrameIdentityEquiv V W) : FrameIdentityEquiv W V where
  equiv x := (Φ.equiv x).symm
  exists_frames x := by
    obtain ⟨e, f, hx, hy, h⟩ := Φ.exists_frames x
    refine ⟨f, e, hy, hx, fun y hy' w => ?_⟩
    rw [← h y ⟨hy'.2, hy'.1⟩ ((Φ.equiv y).symm w), LinearEquiv.apply_symm_apply]

variable (V) in
/-- The identity isomorphism. -/
def refl : FrameIdentityEquiv V V where
  equiv x := LinearEquiv.refl ℂ (V x)
  exists_frames x := ⟨⟨trivializationAt ℂ V x, inferInstance⟩, ⟨trivializationAt ℂ V x, inferInstance⟩,
    mem_baseSet_trivializationAt ℂ V x, mem_baseSet_trivializationAt ℂ V x, fun _ _ _ => rfl⟩

/-- The image of a holomorphic section is holomorphic. -/
def sectionMap (Φ : FrameIdentityEquiv V W) (s : HolomorphicSections (n := n) V) :
    HolomorphicSections (n := n) W where
  toFun x := Φ.equiv x (s x)
  contMDiff_toFun := by
    intro x
    obtain ⟨e, f, hx, hy, h⟩ := Φ.exists_frames x
    apply (f.val.contMDiffAt_section_iff hy).mpr
    have hs := (e.val.contMDiffAt_section_iff hx).mp (s.contMDiff x)
    apply hs.congr_of_eventuallyEq
    filter_upwards [(e.val.open_baseSet.inter f.val.open_baseSet).mem_nhds ⟨hx, hy⟩] with y hy'
    exact h y hy' (s y)

omit [IsComplexManifold n X] in
theorem sectionMap_apply (Φ : FrameIdentityEquiv V W) (s : HolomorphicSections (n := n) V)
    (x : X) : Φ.sectionMap s x = Φ.equiv x (s x) :=
  rfl

/-- The induced linear equivalence of the spaces of ALL holomorphic sections. -/
def sectionEquiv (Φ : FrameIdentityEquiv V W) :
    HolomorphicSections (n := n) V ≃ₗ[ℂ] HolomorphicSections (n := n) W where
  toFun := Φ.sectionMap
  invFun := Φ.symm.sectionMap
  left_inv s := by ext x; exact (Φ.equiv x).symm_apply_apply (s x)
  right_inv s := by ext x; exact (Φ.equiv x).apply_symm_apply (s x)
  map_add' s t := by ext x; exact map_add (Φ.equiv x) (s x) (t x)
  map_smul' a s := by ext x; exact map_smul (Φ.equiv x) a (s x)

/-- Membership in `H⁰(X, V ⊗ 𝓐)` is transported, for every ideal sheaf `𝓐`. -/
theorem sectionMap_mem (Φ : FrameIdentityEquiv V W) (A : GermIdeal n X)
    {s : HolomorphicSections (n := n) V} (hs : s ∈ fullHolomorphicIdealSections (n := n) V A) :
    Φ.sectionMap s ∈ fullHolomorphicIdealSections (n := n) W A := by
  change globalSectionSheafEquiv (n := n) W (Φ.sectionMap s) ∈
    idealOpenSectionSubmodule (n := n) W A ⊤
  rw [mem_idealOpenSectionSubmodule_iff_preferred]
  intro x
  obtain ⟨e, f, hx, hy, h⟩ := Φ.exists_frames x.val
  apply (localFrameCoefficientGerm_mem_iff (n := n) W A ⊤ (preferredOriginalFrame W x.val) f _ x
    (mem_baseSet_trivializationAt ℂ W x.val) hy).mpr
  have hW := localFrameCoefficientGerm_top_eq W f (Φ.sectionMap s) hy
  have hV := localFrameCoefficientGerm_top_eq V e s hx
  have hcoef : sectionCoefficient W f.val (Φ.sectionMap s) =ᶠ[𝓝 x.val]
      sectionCoefficient V e.val s := by
    filter_upwards [(e.val.open_baseSet.inter f.val.open_baseSet).mem_nhds ⟨hx, hy⟩] with y hy'
    exact h y hy' (s y)
  have hmem : localFrameCoefficientGerm (n := n) V ⊤ e (globalSectionSheafEquiv (n := n) V s)
      ⟨x.val, Set.mem_univ x.val⟩ hx ∈ actualWholeSheafStalkIdeal A x.val :=
    hs e ⟨x.val, Set.mem_univ x.val⟩ hx
  rw [hV, ← actualOriginalFunctionGerm_congr
    (originalSectionCoefficient_holomorphicAt (n := n) W f (Φ.sectionMap s) hy)
    (originalSectionCoefficient_holomorphicAt (n := n) V e s hx) hcoef, ← hW] at hmem
  exact hmem

/-- The induced linear equivalence `H⁰(X, V ⊗ 𝓐) ≃ H⁰(X, W ⊗ 𝓐)`, for every ideal sheaf `𝓐`. -/
def idealSectionEquiv (Φ : FrameIdentityEquiv V W) (A : GermIdeal n X) :
    fullHolomorphicIdealSections (n := n) V A ≃ₗ[ℂ] fullHolomorphicIdealSections (n := n) W A where
  toFun s := ⟨Φ.sectionMap s.1, Φ.sectionMap_mem A s.2⟩
  invFun s := ⟨Φ.symm.sectionMap s.1, Φ.symm.sectionMap_mem A s.2⟩
  left_inv s := Subtype.ext (Φ.sectionEquiv.left_inv s.1)
  right_inv s := Subtype.ext (Φ.sectionEquiv.right_inv s.1)
  map_add' s t := Subtype.ext (Φ.sectionEquiv.map_add s.1 t.1)
  map_smul' a s := Subtype.ext (Φ.sectionEquiv.map_smul a s.1)

end FrameIdentityEquiv

end Transport

/-! ### Tensor powers -/

section Tensor

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

namespace FrameIdentityEquiv

/-- `A ≅ A'` and `T ≅ T'` induce `A ⊗ T ≅ A' ⊗ T'` on the literal tensor bundles. -/
def tensorCongr {A A' T T' : HermitianHolomorphicLineBundle.{0, 0} n X}
    (ΦA : FrameIdentityEquiv A.Fiber A'.Fiber) (ΦT : FrameIdentityEquiv T.Fiber T'.Fiber) :
    FrameIdentityEquiv (tensor A T).Fiber (tensor A' T').Fiber where
  equiv x := TensorProduct.congr (ΦA.equiv x) (ΦT.equiv x)
  exists_frames x := by
    obtain ⟨e, e', hx, hx', he⟩ := ΦA.exists_frames x
    obtain ⟨f, f', hy, hy', hf⟩ := ΦT.exists_frames x
    refine ⟨tensorAtlasFrame e f, tensorAtlasFrame e' f', ⟨hx, hy⟩, ⟨hx', hy'⟩, ?_⟩
    intro y hyy t
    let := e.property
    let := e'.property
    let := f.property
    let := f'.property
    have hye : y ∈ e.val.baseSet := hyy.1.1
    have hyf : y ∈ f.val.baseSet := hyy.1.2
    have hye' : y ∈ e'.val.baseSet := hyy.2.1
    have hyf' : y ∈ f'.val.baseSet := hyy.2.2
    change tensorCoordinate A'.Fiber T'.Fiber e'.val f'.val y
        (TensorProduct.congr (ΦA.equiv y) (ΦT.equiv y) t) =
      tensorCoordinate A.Fiber T.Fiber e.val f.val y t
    have hlin : (tensorCoordinate A'.Fiber T'.Fiber e'.val f'.val y).comp
        (TensorProduct.congr (ΦA.equiv y) (ΦT.equiv y)).toLinearMap =
        tensorCoordinate A.Fiber T.Fiber e.val f.val y := by
      apply TensorProduct.ext'
      intro a b
      rw [LinearMap.comp_apply, LinearEquiv.coe_coe, TensorProduct.congr_tmul,
        tensorCoordinate_tmul, tensorCoordinate_tmul]
      congr 1
      · rw [Trivialization.coe_linearMapAt_of_mem e'.val hye',
          Trivialization.coe_linearMapAt_of_mem e.val hye]
        exact he y ⟨hye, hye'⟩ a
      · rw [Trivialization.coe_linearMapAt_of_mem f'.val hyf',
          Trivialization.coe_linearMapAt_of_mem f.val hyf]
        exact hf y ⟨hyf, hyf'⟩ b
    exact LinearMap.congr_fun hlin t

/-- `T ≅ T'` induces `A ⊗ T ≅ A ⊗ T'` on the literal tensor bundles. -/
def tensorLeft (A : HermitianHolomorphicLineBundle.{0, 0} n X)
    {T T' : HermitianHolomorphicLineBundle.{0, 0} n X} (Φ : FrameIdentityEquiv T.Fiber T'.Fiber) :
    FrameIdentityEquiv (tensor A T).Fiber (tensor A T').Fiber :=
  tensorCongr (refl A.Fiber) Φ

/-- `L ≅ L'` induces `L^{k+1} ≅ L'^{k+1}` on the literal positive tensor powers. -/
def positivePowerCongr {L L' : HermitianHolomorphicLineBundle.{0, 0} n X}
    (ΦL : FrameIdentityEquiv L.Fiber L'.Fiber) :
    ∀ k : ℕ, FrameIdentityEquiv (positivePower L k).Fiber (positivePower L' k).Fiber
  | 0 => ΦL
  | k + 1 => tensorCongr (positivePowerCongr ΦL k) ΦL

/-- `L ≅ L'` and `T ≅ T'` induce `L^k ⊗ T ≅ L'^k ⊗ T'` on the literal twisted powers, in every
degree. -/
def twistedPowerCongr {L L' T T' : HermitianHolomorphicLineBundle.{0, 0} n X}
    (ΦL : FrameIdentityEquiv L.Fiber L'.Fiber) (ΦT : FrameIdentityEquiv T.Fiber T'.Fiber) :
    ∀ k : ℕ, FrameIdentityEquiv (HermitianHolomorphicLineBundle.twistedPower L T k).Fiber
      (HermitianHolomorphicLineBundle.twistedPower L' T' k).Fiber
  | 0 => tensorCongr (refl (unit (n := n) (M := X)).Fiber) ΦT
  | k + 1 => tensorCongr (positivePowerCongr ΦL k) ΦT

/-- `T ≅ T'` induces `L^k ⊗ T ≅ L^k ⊗ T'` on the literal twisted powers, in every degree. -/
def twistedPower (L : HermitianHolomorphicLineBundle.{0, 0} n X)
    {T T' : HermitianHolomorphicLineBundle.{0, 0} n X} (Φ : FrameIdentityEquiv T.Fiber T'.Fiber) :
    ∀ k : ℕ, FrameIdentityEquiv (HermitianHolomorphicLineBundle.twistedPower L T k).Fiber
      (HermitianHolomorphicLineBundle.twistedPower L T' k).Fiber :=
  twistedPowerCongr (refl L.Fiber) Φ

end FrameIdentityEquiv

/-- `H⁰(X, L^k ⊗ T ⊗ 𝓘(kφ)) ≃ H⁰(X, L'^k ⊗ T' ⊗ 𝓘(kφ))` for isomorphic `L ≅ L'`, `T ≅ T'`. -/
def literalSectionsCongr {L L' T T' : HermitianHolomorphicLineBundle.{0, 0} n X}
    (ΦL : FrameIdentityEquiv L.Fiber L'.Fiber) (ΦT : FrameIdentityEquiv T.Fiber T'.Fiber)
    (k : ℕ) (φ : X → EReal) :
    LiteralTwistedMultiplierSections L T k φ ≃ₗ[ℂ] LiteralTwistedMultiplierSections L' T' k φ :=
  (literalTwistedMultiplierSectionEquiv L T k φ).trans
    (((FrameIdentityEquiv.twistedPowerCongr ΦL ΦT k).idealSectionEquiv
      (sourceDegreeMultiplierIdeal (n := n) k φ)).trans
      (literalTwistedMultiplierSectionEquiv L' T' k φ).symm)

/-- `H⁰(X, L^k ⊗ T ⊗ 𝓘(kφ)) ≃ H⁰(X, L^k ⊗ T' ⊗ 𝓘(kφ))` for isomorphic `T ≅ T'`. -/
def literalSectionsEquiv (L : HermitianHolomorphicLineBundle.{0, 0} n X)
    {T T' : HermitianHolomorphicLineBundle.{0, 0} n X} (Φ : FrameIdentityEquiv T.Fiber T'.Fiber)
    (k : ℕ) (φ : X → EReal) :
    LiteralTwistedMultiplierSections L T k φ ≃ₗ[ℂ] LiteralTwistedMultiplierSections L T' k φ :=
  literalSectionsCongr (FrameIdentityEquiv.refl L.Fiber) Φ k φ

theorem finrank_literalSections_congr {L L' T T' : HermitianHolomorphicLineBundle.{0, 0} n X}
    (ΦL : FrameIdentityEquiv L.Fiber L'.Fiber) (ΦT : FrameIdentityEquiv T.Fiber T'.Fiber)
    (k : ℕ) (φ : X → EReal) :
    Module.finrank ℂ (LiteralTwistedMultiplierSections L T k φ) =
      Module.finrank ℂ (LiteralTwistedMultiplierSections L' T' k φ) :=
  (literalSectionsCongr ΦL ΦT k φ).finrank_eq

/-- The normalized dimensions `n!/kⁿ h⁰(X, L^k ⊗ T ⊗ 𝓘(kφ))` agree for isomorphic `L ≅ L'`,
`T ≅ T'`. -/
theorem normalizedH0_congr {L L' T T' : HermitianHolomorphicLineBundle.{0, 0} n X}
    (ΦL : FrameIdentityEquiv L.Fiber L'.Fiber) (ΦT : FrameIdentityEquiv T.Fiber T'.Fiber)
    (φ : X → EReal) (k : ℕ) :
    SGPT.Bergman.Quant2.normalizedH0 L T φ k = SGPT.Bergman.Quant2.normalizedH0 L' T' φ k := by
  rw [SGPT.Bergman.Quant2.normalizedH0, SGPT.Bergman.Quant2.normalizedH0,
    finrank_literalSections_congr ΦL ΦT k φ]

/-! ### Rescaling the metric of `T` -/

/-- The identity `T ≅ rescale T ρ`: same holomorphic bundle, metric `ρ h_T`. -/
def rescaleEquiv (T : HermitianHolomorphicLineBundle.{0, 0} n X) (ρ : X → ℝ)
    (hρc : Continuous ρ) (hρ : ∀ x, 0 < ρ x) :
    FrameIdentityEquiv T.Fiber (rescale T ρ hρc hρ).Fiber where
  equiv := toRescale T ρ hρc hρ
  exists_frames x :=
    ⟨⟨trivializationAt ℂ T.Fiber x, inferInstance⟩,
      toAtlasFrame T ρ hρc hρ ⟨trivializationAt ℂ T.Fiber x, inferInstance⟩,
      mem_baseSet_trivializationAt ℂ T.Fiber x, mem_baseSet_trivializationAt ℂ T.Fiber x,
      fun y _ w => toAtlasFrame_apply T ρ hρc hρ _ y w⟩

/-- **`h⁰(X, L^k ⊗ T ⊗ 𝓘(kφ))` does not depend on the metric of `T`.** -/
theorem normalizedH0_rescale (L T : HermitianHolomorphicLineBundle.{0, 0} n X) (ρ : X → ℝ)
    (hρc : Continuous ρ) (hρ : ∀ x, 0 < ρ x) (φ : X → EReal) (k : ℕ) :
    SGPT.Bergman.Quant2.normalizedH0 L (rescale T ρ hρc hρ) φ k =
      SGPT.Bergman.Quant2.normalizedH0 L T φ k :=
  (normalizedH0_congr (FrameIdentityEquiv.refl L.Fiber) (rescaleEquiv T ρ hρc hρ) φ k).symm

/-- **`h⁰(X, L^k ⊗ T ⊗ 𝓘(kφ))` does not depend on the metrics of `L` and `T`.** -/
theorem normalizedH0_rescale_rescale (L T : HermitianHolomorphicLineBundle.{0, 0} n X)
    (σ : X → ℝ) (hσc : Continuous σ) (hσ : ∀ x, 0 < σ x) (ρ : X → ℝ)
    (hρc : Continuous ρ) (hρ : ∀ x, 0 < ρ x) (φ : X → EReal) (k : ℕ) :
    SGPT.Bergman.Quant2.normalizedH0 (rescale L σ hσc hσ) (rescale T ρ hρc hρ) φ k =
      SGPT.Bergman.Quant2.normalizedH0 L T φ k :=
  (normalizedH0_congr (rescaleEquiv L σ hσc hσ) (rescaleEquiv T ρ hρc hρ) φ k).symm

end Tensor

end SGPT.LineBundle.TMetric
