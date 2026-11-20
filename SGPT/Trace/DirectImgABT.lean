import SGPT.Trace.DirectImgFibre
import SGPT.PSH.BookCurrentMetrics

/-!
# The relative analytic Bertini theorem (`rmk:generalABT`): statement and proved clauses

Source: `chapter_trace.tex`, `rmk:generalABT`: *Let `f : X → Y` be a projective morphism between
complex manifolds and `(L, h)` be a Hermitian pseudo-effective line bundle on `X`. Then for
quasi-every `y ∈ Y` (outside a pluripolar subset of `Y`), the fiber `X_y` is smooth and
`𝓘(λ h|_{X_y}) = Rest_{X_y}(𝓘(λ h))`.* Blueprint `claude-direct-img.tex`.

## Conventions

* `IsProjectiveMorphism f`: `f` is holomorphic and factors as a closed embedding
  `(f, ι) : X ↪ Y × ℙᴹ` (`ι` holomorphic, `(f, ι)` a topological closed embedding with injective
  differential) followed by the projection. Such an `f` is proper
  (`IsProjectiveMorphism.isProperMap`); only properness is used below.
* The multiplier ideal of a psh metric `h = h₀ e^{-φ}` (`def:pshfunctions:L1836`) is `𝓘(h) = 𝓘(φ)`
  and `𝓘(λ h) = 𝓘(λφ)` (in a local frame `e`, `|e|²_h = |e|²_{h₀} e^{-φ}` with `-log |e|²_{h₀}`
  smooth); on a smooth fibre `X_y`, `h|_{X_y} = h₀|_{X_y} e^{-φ|_{X_y}}`, so
  `𝓘(λ h|_{X_y}) = 𝓘(λ φ|_{X_y})` on the manifold `X_y`. The statement quantifies over **every**
  presentation `(h₀, φ)` of `h`.
* `λ` is not quantified in the source; the formal statement asks the equality for **all** `λ > 0`
  simultaneously on the same co-pluripolar set (this implies the reading with a fixed `λ`).
* `Rest_{X_y}` is the book's restriction ideal (`def:restidealsheaf`, `restStalk`), and the two
  germ rings `𝒪_{X_y,q}` and `𝒪_{X,q}/𝓘_{X_y,q}` are identified by `structureStalkEquiv`, exactly
  as in `SGPT.Trace.Bertini.bertiniGoodSet`.

## Main results

* `GeneralABTStatement`: the statement of `rmk:generalABT` (not proved).
* `coPluripolar_isSmoothFibreOfDim` (in `DirectImgFibre`): **the smoothness clause**, for every
  proper holomorphic map.
* `fibre_multiplier_le_restStalk`: **the inclusion `𝓘(λφ|_{X_y}) ⊆ Rest_{X_y} 𝓘(λφ)`** on every
  smooth fibre (Ohsawa–Takegoshi, `thm:OT`), at every level.
* `coPluripolar_generalABT_proved`: both proved clauses quasi-everywhere, for a projective
  morphism and a Hermitian pseudo-effective line bundle.
* `coPluripolar_generalABTGoodSet_of_reverse`, `coPluripolar_reverse_of_generalABTGoodSet`,
  `generalABTStatement_of_reverse`: `rmk:generalABT` is equivalent to the reverse inclusion
  `Rest_{X_y} 𝓘(λφ) ⊆ 𝓘(λφ|_{X_y})` for quasi-every `y` (the open analytic input: positivity of
  the Hodge metric on the direct images `f_*(K_{X/Y} ⊗ L ⊗ 𝓘(h))`, [HPS18, PT18]).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open Set Filter Bundle
open scoped Topology Manifold ContDiff ENNReal

namespace SGPT.Trace.DirectImg

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
  SGPT.Foundations.Analysis.FirstPass.BlowupSequences SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.SubmanifoldChartedSpace
  SGPT.PSH.IdealRestriction SGPT.PSH.OhsawaTakegoshi

/-! ### The multiplier clause on a smooth fibre -/

section Multiplier

variable {n m : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel m) Y]
  [IsComplexManifold m Y] {f : X → Y}

/-- The multiplier clause of `rmk:generalABT` at level `c` on a smooth fibre `X_y` of dimension
`k`: at every `q ∈ X_y`, the stalk `𝓘(c φ|_{X_y})_q ⊆ 𝒪_{X_y,q}`, transported to
`𝒪_{X,q}/𝓘_{X_y,q}`, equals `(Rest_{X_y} 𝓘(c φ))_q`. -/
def FibreMultiplierEq (hf : Continuous f) {y : Y} {k : ℕ} (hk : k ≤ n)
    (hsm : IsSmoothFibreOfDim n m f y k) (φ : X → EReal) (c : ℝ) : Prop :=
  letI := chartedSpace hk hsm.1
  ∀ q : fibre f y,
    Ideal.comap (structureStalkEquiv hk hsm.1 (hsm.isClosedSubmanifold f hf) q)
        (stalkIdeal (multiplierIdeal (n := k) c (fun z : fibre f y => φ z.1)) q) =
      restStalk (multiplierIdeal (n := n) c φ) (submanifoldSubspace (hsm.isClosedSubmanifold f hf))
        q.1

/-- The reverse inclusion `Rest_{X_y} 𝓘(c φ) ⊆ 𝓘(c φ|_{X_y})` on a smooth fibre (the half of the
multiplier clause that is not Ohsawa–Takegoshi). -/
def FibreReverseInclusion (hf : Continuous f) {y : Y} {k : ℕ} (hk : k ≤ n)
    (hsm : IsSmoothFibreOfDim n m f y k) (φ : X → EReal) (c : ℝ) : Prop :=
  letI := chartedSpace hk hsm.1
  ∀ q : fibre f y,
    restStalk (multiplierIdeal (n := n) c φ) (submanifoldSubspace (hsm.isClosedSubmanifold f hf))
        q.1 ≤
      Ideal.comap (structureStalkEquiv hk hsm.1 (hsm.isClosedSubmanifold f hf) q)
        (stalkIdeal (multiplierIdeal (n := k) c (fun z : fibre f y => φ z.1)) q)

/-- **The Ohsawa–Takegoshi half of the multiplier clause, on every smooth fibre**: for `φ`
quasi-psh, every real `c` and every `q ∈ X_y`, `𝓘(c φ|_{X_y})_q ⊆ (Rest_{X_y} 𝓘(c φ))_q`
(`thm:OT` on a closed submanifold of pure dimension, not necessarily connected:
`Trace2Bertini.multiplierIdeal_restrict_le_restStalk_of_regular`). -/
theorem fibre_multiplier_le_restStalk (hf : Continuous f) {y : Y} {k : ℕ} (hk : k ≤ n)
    (hsm : IsSmoothFibreOfDim n m f y k) {φ : X → EReal}
    (hφ : ManifoldQuasiPlurisubharmonic (n := n) φ) (c : ℝ) :
    letI := chartedSpace hk hsm.1
    ∀ q : fibre f y,
      Ideal.comap (structureStalkEquiv hk hsm.1 (hsm.isClosedSubmanifold f hf) q)
          (stalkIdeal (multiplierIdeal (n := k) c (fun z : fibre f y => φ z.1)) q) ≤
        restStalk (multiplierIdeal (n := n) c φ)
          (submanifoldSubspace (hsm.isClosedSubmanifold f hf)) q.1 :=
  Trace2Bertini.multiplierIdeal_restrict_le_restStalk_of_regular hk hsm.1
    (hsm.isClosedSubmanifold f hf) hφ c

/-- On a smooth fibre, the multiplier clause is equivalent to the reverse inclusion. -/
theorem fibreMultiplierEq_iff (hf : Continuous f) {y : Y} {k : ℕ} (hk : k ≤ n)
    (hsm : IsSmoothFibreOfDim n m f y k) {φ : X → EReal}
    (hφ : ManifoldQuasiPlurisubharmonic (n := n) φ) (c : ℝ) :
    FibreMultiplierEq hf hk hsm φ c ↔ FibreReverseInclusion hf hk hsm φ c :=
  ⟨fun h q => (h q).symm.le,
    fun h q => le_antisymm (fibre_multiplier_le_restStalk hf hk hsm hφ c q) (h q)⟩

variable (n m f) in
/-- The set of `y ∈ Y` of the conclusion of `rmk:generalABT` for the weight `φ`: `X_y` is smooth
and `𝓘(λ φ|_{X_y}) = Rest_{X_y}(𝓘(λ φ))` for every `λ > 0`. -/
def generalABTGoodSet (hf : Continuous f) (φ : X → EReal) : Set Y :=
  {y | ∃ (k : ℕ) (hk : k ≤ n) (hsm : IsSmoothFibreOfDim n m f y k),
    ∀ c : ℝ, 0 < c → FibreMultiplierEq hf hk hsm φ c}

/-- **The proved clauses of `rmk:generalABT`, potential form**: for a proper holomorphic map
`f : X → Y` and a quasi-psh `φ` on `X`, for quasi-every `y ∈ Y` the fibre `X_y` is smooth (of
dimension `dim X - dim Y`) and `𝓘(c φ|_{X_y}) ⊆ Rest_{X_y} 𝓘(c φ)` at every point and every
level `c`. -/
theorem coPluripolar_smooth_multiplier_le
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m) ∞ f) (hprop : IsProperMap f)
    {φ : X → EReal} (hφ : ManifoldQuasiPlurisubharmonic (n := n) φ) :
    (SGPT.PSH.VariableComplexAtlas.ofFixedModel m Y).CoPluripolar
      {y | ∃ (hsm : IsSmoothFibreOfDim n m f y (n - m)),
        letI := chartedSpace (Nat.sub_le n m) hsm.1
        ∀ (c : ℝ) (q : fibre f y),
          Ideal.comap (structureStalkEquiv (Nat.sub_le n m) hsm.1
              (hsm.isClosedSubmanifold f hf.continuous) q)
              (stalkIdeal (multiplierIdeal (n := n - m) c (fun z : fibre f y => φ z.1)) q) ≤
            restStalk (multiplierIdeal (n := n) c φ)
              (submanifoldSubspace (hsm.isClosedSubmanifold f hf.continuous)) q.1} :=
  SGPT.Trace.BertiniGeneral.coPluripolar_mono (coPluripolar_isSmoothFibreOfDim hf hprop)
    fun _ hsm => ⟨hsm, fun c => fibre_multiplier_le_restStalk hf.continuous (Nat.sub_le n m) hsm
      hφ c⟩

/-- **`rmk:generalABT` from the reverse inclusion.** For a proper holomorphic `f` and quasi-psh
`φ`: if for quasi-every `y` the reverse inclusion `Rest_{X_y} 𝓘(λφ) ⊆ 𝓘(λφ|_{X_y})` holds for
every `λ > 0` whenever `X_y` is smooth, then the set of `rmk:generalABT` is co-pluripolar. -/
theorem coPluripolar_generalABTGoodSet_of_reverse
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m) ∞ f) (hprop : IsProperMap f)
    {φ : X → EReal} (hφ : ManifoldQuasiPlurisubharmonic (n := n) φ)
    (hrev : (SGPT.PSH.VariableComplexAtlas.ofFixedModel m Y).CoPluripolar
      {y | ∀ (k : ℕ) (hk : k ≤ n) (hsm : IsSmoothFibreOfDim n m f y k),
        ∀ c : ℝ, 0 < c → FibreReverseInclusion hf.continuous hk hsm φ c}) :
    (SGPT.PSH.VariableComplexAtlas.ofFixedModel m Y).CoPluripolar
      (generalABTGoodSet n m f hf.continuous φ) := by
  refine SGPT.Trace.BertiniGeneral.coPluripolar_mono
    (SGPT.Trace.BertiniGeneral.coPluripolar_inter (coPluripolar_isSmoothFibreOfDim hf hprop)
      hrev) fun y hy => ?_
  obtain ⟨hsm, hr⟩ := hy
  exact ⟨n - m, Nat.sub_le n m, hsm, fun c hc =>
    (fibreMultiplierEq_iff hf.continuous (Nat.sub_le n m) hsm hφ c).mpr (hr _ _ hsm c hc)⟩

/-- Conversely, the conclusion of `rmk:generalABT` gives the reverse inclusion for quasi-every
`y`. -/
theorem coPluripolar_reverse_of_generalABTGoodSet
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m) ∞ f)
    {φ : X → EReal} (hφ : ManifoldQuasiPlurisubharmonic (n := n) φ)
    (hG : (SGPT.PSH.VariableComplexAtlas.ofFixedModel m Y).CoPluripolar
      (generalABTGoodSet n m f hf.continuous φ)) :
    (SGPT.PSH.VariableComplexAtlas.ofFixedModel m Y).CoPluripolar
      {y | ∃ (k : ℕ) (hk : k ≤ n) (hsm : IsSmoothFibreOfDim n m f y k),
        ∀ c : ℝ, 0 < c → FibreReverseInclusion hf.continuous hk hsm φ c} :=
  SGPT.Trace.BertiniGeneral.coPluripolar_mono hG fun _ ⟨k, hk, hsm, h⟩ =>
    ⟨k, hk, hsm, fun c hc => (fibreMultiplierEq_iff hf.continuous hk hsm hφ c).mp (h c hc)⟩

end Multiplier

/-! ### Projective morphisms -/

section Projective

open SGPT.Projective

variable {n m : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel m) Y]
  [IsComplexManifold m Y]

variable (n m) in
/-- A **projective morphism** of complex manifolds: `f` is holomorphic and there is a holomorphic
`ι : X → ℙᴹ` such that `(f, ι) : X → Y × ℙᴹ` is a closed embedding (a homeomorphism onto a closed
subset whose differential is injective: `df(v) = 0` and `dι(v) = 0` force `v = 0`); i.e. `f` is
the composite of a closed embedding `X ↪ Y × ℙᴹ` and the projection. -/
def IsProjectiveMorphism (f : X → Y) : Prop :=
  ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m) ∞ f ∧
    ∃ (M : ℕ) (ι : X → ComplexProjectiveSpace M),
      ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel M) ∞ ι ∧
        Topology.IsClosedEmbedding (fun x => (f x, ι x)) ∧
        ∀ (x : X) (v : TangentSpace 𝓘(ℂ, ComplexModel n) x),
          mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m) f x v = 0 →
            mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel M) ι x v = 0 → v = 0

/-- A projective morphism is proper: it is a closed embedding into `Y × ℙᴹ` followed by the
projection, which is proper because `ℙᴹ` is compact. -/
theorem IsProjectiveMorphism.isProperMap {f : X → Y} (hf : IsProjectiveMorphism n m f) :
    IsProperMap f := by
  obtain ⟨-, M, ι, -, hemb, -⟩ := hf
  exact (isProperMap_fst_of_compactSpace (Y := ComplexProjectiveSpace M)).comp hemb.isProperMap

end Projective

/-! ### The statement of `rmk:generalABT` -/

section Statement

open SGPT.PSH.LineBundleMetric

/-- **Source `rmk:generalABT`** (statement only): let `f : X → Y` be a projective morphism between
complex manifolds and `(L, h)` a Hermitian pseudo-effective line bundle on `X`. Then for every
presentation `h = h₀ e^{-φ}` (so `𝓘(λ h) = 𝓘(λ φ)` and `𝓘(λ h|_{X_y}) = 𝓘(λ φ|_{X_y})`), for
quasi-every `y ∈ Y` the fibre `X_y` is smooth and `𝓘(λ h|_{X_y}) = Rest_{X_y}(𝓘(λ h))` for
every `λ > 0`. -/
def GeneralABTStatement : Prop :=
  ∀ (n m : ℕ) (X Y : Type) [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
    [IsComplexManifold n X] [TopologicalSpace Y] [ChartedSpace (ComplexModel m) Y]
    [IsComplexManifold m Y] (f : X → Y) (hf : IsProjectiveMorphism n m f)
    (L : X → Type) [∀ x, AddCommGroup (L x)] [∀ x, Module ℂ (L x)]
    [∀ x, TopologicalSpace (L x)] [TopologicalSpace (TotalSpace ℂ L)] [FiberBundle ℂ L]
    [VectorBundle ℂ ℂ L] [ContMDiffVectorBundle ∞ ℂ L 𝓘(ℂ, ComplexModel n)]
    (h : HermitianPseudoeffective n L) (h₀ : HermitianMetric (n := n) L) (φ : X → EReal),
    IsPSHMetricWith h.metric h₀ φ →
      (SGPT.PSH.VariableComplexAtlas.ofFixedModel m Y).CoPluripolar
        (generalABTGoodSet n m f hf.1.continuous φ)

variable {n m : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel m) Y]
  [IsComplexManifold m Y]
  {L : X → Type*} [∀ x, AddCommGroup (L x)] [∀ x, Module ℂ (L x)] [∀ x, TopologicalSpace (L x)]
  [TopologicalSpace (TotalSpace ℂ L)] [FiberBundle ℂ L] [VectorBundle ℂ ℂ L]
  [ContMDiffVectorBundle ∞ ℂ L 𝓘(ℂ, ComplexModel n)]

/-- The potential of a presentation `h = h₀ e^{-φ}` of a psh metric is quasi-psh. -/
theorem manifoldQuasiPlurisubharmonic_of_isPSHMetricWith {q : (x : X) → L x → ℝ≥0∞}
    {h₀ : HermitianMetric (n := n) L} {φ : X → EReal} (hq : IsPSHMetricWith q h₀ φ) :
    ManifoldQuasiPlurisubharmonic (n := n) φ :=
  hq.thetaPsh.1.quasiPlurisubharmonic

/-- **The proved clauses of `rmk:generalABT`**: for a projective morphism `f : X → Y` of complex
manifolds and a Hermitian pseudo-effective line bundle `(L, h)` on `X` presented as
`h = h₀ e^{-φ}`, for quasi-every `y ∈ Y` the fibre `X_y` is smooth (of dimension
`dim X - dim Y`) and `𝓘(λ h|_{X_y}) ⊆ Rest_{X_y}(𝓘(λ h))` for every `λ` (Ohsawa–Takegoshi). -/
theorem coPluripolar_generalABT_proved {f : X → Y} (hf : IsProjectiveMorphism n m f)
    (h : HermitianPseudoeffective n L) {h₀ : HermitianMetric (n := n) L} {φ : X → EReal}
    (hpres : IsPSHMetricWith h.metric h₀ φ) :
    (SGPT.PSH.VariableComplexAtlas.ofFixedModel m Y).CoPluripolar
      {y | ∃ (hsm : IsSmoothFibreOfDim n m f y (n - m)),
        letI := chartedSpace (Nat.sub_le n m) hsm.1
        ∀ (c : ℝ) (q : fibre f y),
          Ideal.comap (structureStalkEquiv (Nat.sub_le n m) hsm.1
              (hsm.isClosedSubmanifold f hf.1.continuous) q)
              (stalkIdeal (multiplierIdeal (n := n - m) c (fun z : fibre f y => φ z.1)) q) ≤
            restStalk (multiplierIdeal (n := n) c φ)
              (submanifoldSubspace (hsm.isClosedSubmanifold f hf.1.continuous)) q.1} :=
  coPluripolar_smooth_multiplier_le hf.1 hf.isProperMap (manifoldQuasiPlurisubharmonic_of_isPSHMetricWith hpres)

/-- **`rmk:generalABT` is equivalent to the reverse inclusion quasi-everywhere**: if for every
projective morphism `f`, every Hermitian pseudo-effective `(L, h = h₀ e^{-φ})` and quasi-every
`y`, the reverse inclusion `Rest_{X_y} 𝓘(λφ) ⊆ 𝓘(λφ|_{X_y})` holds for every `λ > 0` whenever
`X_y` is smooth, then `GeneralABTStatement` holds. -/
theorem generalABTStatement_of_reverse
    (hrev : ∀ (n m : ℕ) (X Y : Type) [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
      [IsComplexManifold n X] [TopologicalSpace Y] [ChartedSpace (ComplexModel m) Y]
      [IsComplexManifold m Y] (f : X → Y) (hf : IsProjectiveMorphism n m f)
      (L : X → Type) [∀ x, AddCommGroup (L x)] [∀ x, Module ℂ (L x)]
      [∀ x, TopologicalSpace (L x)] [TopologicalSpace (TotalSpace ℂ L)] [FiberBundle ℂ L]
      [VectorBundle ℂ ℂ L] [ContMDiffVectorBundle ∞ ℂ L 𝓘(ℂ, ComplexModel n)]
      (h : HermitianPseudoeffective n L) (h₀ : HermitianMetric (n := n) L) (φ : X → EReal),
      IsPSHMetricWith h.metric h₀ φ →
        (SGPT.PSH.VariableComplexAtlas.ofFixedModel m Y).CoPluripolar
          {y | ∀ (k : ℕ) (hk : k ≤ n) (hsm : IsSmoothFibreOfDim n m f y k),
            ∀ c : ℝ, 0 < c → FibreReverseInclusion hf.1.continuous hk hsm φ c}) :
    GeneralABTStatement := by
  unfold GeneralABTStatement
  intro n m X Y _ _ _ _ _ _ f hf L _ _ _ _ _ _ _ h h₀ φ hpres
  exact coPluripolar_generalABTGoodSet_of_reverse hf.1 hf.isProperMap
    (manifoldQuasiPlurisubharmonic_of_isPSHMetricWith hpres) (hrev n m X Y f hf L h h₀ φ hpres)

end Statement

end SGPT.Trace.DirectImg
