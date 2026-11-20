import SGPT.Trace.RestVolTensor
import SGPT.Bergman.SourceBergmanNorms
import SGPT.PSH.GlobalL2BergmanUpper
import SGPT.Foundations.Analysis.Pending.GermIdealPullbackCalculus
import SGPT.Foundations.Analysis.Pending.RelativePrincipalizationSpan
import SGPT.Foundations.Analysis.Pending.PshAnalyticSetExtension

/-!
# Multiplication by `ϕ^q` on `Y` (Step 2 of `thm:rest_volume`)

Source: `chapter_trace.tex`, proof of `thm:rest_volume`, Step 2: for `ϕ ∈ H⁰(X, A)` not
vanishing identically on `Y`, `t ↦ t ⊗ ϕ^q` is an injective linear map

`H⁰(Y, T|_Y ⊗ L|_Y^{qk₀+r} ⊗ Res_Y 𝓘((qk₀+r)φ)) → H⁰(Y, (T ⊗ L^r)|_Y ⊗ (L^{k₀} ⊗ A)|_Y^q ⊗
Res_Y 𝓘(q k₀ φ))`.

* `pullSection`: the restriction `ϕ|_Y` of a holomorphic section of `A`;
* `transferFiber`, `frameCoord_transferFiber`: the fibre map and its coordinates (multiplication
  by `(coordinate of ϕ)^q`);
* `transferSection`, `transferSectionLinear`, `transferSection_injective`,
  `transferSection_mem`;
* `restrictIdeal_degree_le`: `Res_Y 𝓘(kφ) ⊆ Res_Y 𝓘(k'φ)` for `k' ≤ k`;
* `idealH0_le_transfer`: the resulting inequality of dimensions.
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
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.SubmanifoldIdealRestriction
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.QuantizationDraft
  SGPT.Bergman.MultiplierSectionsDraft SGPT.Bergman.CompactHolomorphicSectionsDraft
  SGPT.Bergman.NativeHermitianMetric SGPT.Bergman.PolynomialH0Growth
open SGPT.IGood.DXLow2
open HermitianHolomorphicLineBundle

/-! ### Restricted multiplier ideals in different degrees -/

section Degree

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [CompactSpace X]

/-- `𝓘(kφ) ⊆ 𝓘(k'φ)` for `k' ≤ k` and quasi-psh `φ`. -/
theorem sourceDegreeMultiplierIdeal_le_of_le {φ : X → EReal}
    (hφ : IsGlobalQuasiPshPotential (n := n) φ) {k k' : ℕ} (hk : k' ≤ k) :
    (sourceDegreeMultiplierIdeal (n := n) k φ).Le (sourceDegreeMultiplierIdeal (n := n) k' φ) := by
  let _ : MeasurableSpace X := borel X
  have _ : BorelSpace X := ⟨rfl⟩
  obtain ⟨M, hM0, hφM⟩ := SGPT.PSH.GlobalL2.exists_nonneg_upper_bound hφ
  have hq : ManifoldQuasiPlurisubharmonic (n := n) (fun x => ((k' : ℝ) : EReal) * φ x) := by
    rcases Nat.eq_zero_or_pos k' with h | h
    · subst h
      intro e z hz
      simp only [Nat.cast_zero, EReal.coe_zero, zero_mul]
      exact (manifoldQuasiPlurisubharmonic_const (n := n) (M := X) 0 e z hz)
    · exact SGPT.NAPotential.BJPrep.manifoldQuasiPlurisubharmonic_const_mul hφ.1
        (Nat.cast_pos.mpr h)
  have hle : ∀ x, ((k : ℝ) : EReal) * φ x ≤
      ((k' : ℝ) : EReal) * φ x + (((k - k' : ℕ) : ℝ) * M : ℝ) := by
    intro x
    have hne := hφ.1.ne_top x
    induction hx : φ x using EReal.rec with
    | bot =>
      rcases Nat.eq_zero_or_pos k with h | h
      · have : k' = 0 := by omega
        subst h; subst this; simp
      · rw [EReal.coe_mul_bot_of_pos (Nat.cast_pos.mpr h)]
        exact bot_le
    | coe t =>
      have ht : t ≤ M := by
        have := hφM x
        rw [hx] at this
        exact_mod_cast this
      rw [← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
      apply EReal.coe_le_coe_iff.mpr
      have hkk : ((k - k' : ℕ) : ℝ) = (k : ℝ) - k' := by push_cast [Nat.cast_sub hk]; ring
      rw [hkk]
      have h0 : (0 : ℝ) ≤ (k : ℝ) - k' := by
        have : (k' : ℝ) ≤ k := by exact_mod_cast hk
        linarith
      nlinarith
    | top => exact absurd hx hne
  have horder := iOrderOnManifold_of_le_add hq hle
  intro x g hg
  exact PositiveCurrentTraceMultiplier.multiplierIdeal_le_of_iOrderOnManifold horder one_pos x g hg

end Degree

/-! ### The fibre map and the transfer of sections -/

section Transfer

variable {n m : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]
  {V : Type} [TopologicalSpace V] [ChartedSpace (ComplexModel m) V] [IsComplexManifold m V]
  (f : ContMDiffMap 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) V X ∞)
  {L A T : HermitianHolomorphicLineBundle.{0, 0} n X} {K r q : ℕ}

/-- The restriction `ϕ|_V` of a holomorphic section of `A`. -/
def pullSection (s : HolomorphicSections (n := n) A.Fiber) :
    HolomorphicSections (n := m) (restrictBundle A f).Fiber where
  toFun y := s (f y)
  contMDiff_toFun := by
    intro y₀
    let e : AtlasFrame A := ⟨trivializationAt ℂ A.Fiber (f y₀), inferInstance⟩
    have he : f y₀ ∈ e.val.baseSet := mem_baseSet_trivializationAt ℂ A.Fiber (f y₀)
    let H := pullFrame f e
    let := H.property
    apply (H.val.contMDiffAt_section_iff (mem_pullFrame_baseSet f e he)).mpr
    have hs := (e.val.contMDiffAt_section_iff he).mp (s.contMDiff (f y₀))
    exact hs.comp y₀ (f.contMDiff y₀)

theorem pullSection_apply (s : HolomorphicSections (n := n) A.Fiber) (y : V) :
    pullSection f s y = s (f y) := rfl

variable (L A T K r q) in
/-- **The fibre map of Step 2**: `v ↦ v ⊗ σ^{⊗q}` from `(L^{r+(K+1)q} ⊗ T)|_V` to
`((L^{K+1} ⊗ A)^q ⊗ (L^r ⊗ T))|_V`. -/
def transferFiber {y : V} (σ : A.Fiber (f y)) :
    (twistedPower (restrictBundle L f) (restrictBundle T f) (r + (K + 1) * q)).Fiber y →ₗ[ℂ]
      (twistedPower (restrictBundle (perturbedBundle L A K) f)
        (restrictBundle (twistedPower L T r) f) q).Fiber y :=
  (twistedFiberEquiv f (perturbedBundle L A K) (twistedPower L T r) y q).symm.toLinearMap ∘ₗ
    mulAFiber L A T K r σ q ∘ₗ
    (castTwistedFiber L T (f y) (stepIndex_eq K r q).symm).toLinearMap ∘ₗ
    (twistedFiberEquiv f L T y (r + (K + 1) * q)).toLinearMap

/-- In pulled-back product frames, `transferFiber σ` multiplies coordinates by
`(coordinate of σ)^q`. -/
theorem frameCoord_transferFiber (eL : AtlasFrame L) (eA : AtlasFrame A) (eT : AtlasFrame T)
    {y : V} (hL : f y ∈ eL.val.baseSet) (hA : f y ∈ eA.val.baseSet) (hT : f y ∈ eT.val.baseSet)
    (σ : A.Fiber (f y))
    (v : (twistedPower (restrictBundle L f) (restrictBundle T f) (r + (K + 1) * q)).Fiber y) :
    frameCoord (twistedPowerAtlasFrame
        (pullFrame f (tensorAtlasFrame (positivePowerAtlasFrame eL K) eA))
        (pullFrame f (twistedPowerAtlasFrame eL eT r)) q) y (transferFiber f L A T K r q σ v) =
      frameCoord eA (f y) σ ^ q *
        frameCoord (twistedPowerAtlasFrame (pullFrame f eL) (pullFrame f eT) (r + (K + 1) * q)) y v := by
  have hK := positivePowerAtlasFrame_mem eL hL K
  have hL' : f y ∈ (tensorAtlasFrame (positivePowerAtlasFrame eL K) eA).val.baseSet := ⟨hK, hA⟩
  have hr : f y ∈ (twistedPowerAtlasFrame eL eT r).val.baseSet :=
    twistedPowerAtlasFrame_mem eL eT hL hT r
  rw [twistedPowerAtlasFrame_pull_coord f _ _ hL' hr q,
    twistedPowerAtlasFrame_pull_coord f eL eT hL hT (r + (K + 1) * q)]
  simp only [transferFiber, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearEquiv.apply_symm_apply]
  rw [frameCoord_mulAFiber eL eA eT hL hA hT σ q, frameCoord_castTwistedFiber]

variable (L A T K r q) in
/-- **The transfer `t ↦ t ⊗ ϕ^q`** of holomorphic sections over `V`. -/
def transferSection (sA : HolomorphicSections (n := n) A.Fiber)
    (t : twistedSections (restrictBundle L f) (restrictBundle T f) (r + (K + 1) * q)) :
    twistedSections (restrictBundle (perturbedBundle L A K) f)
      (restrictBundle (twistedPower L T r) f) q where
  toFun y := transferFiber f L A T K r q (sA (f y)) (t y)
  contMDiff_toFun := by
    intro y₀
    let eL : AtlasFrame L := ⟨trivializationAt ℂ L.Fiber (f y₀), inferInstance⟩
    let eA : AtlasFrame A := ⟨trivializationAt ℂ A.Fiber (f y₀), inferInstance⟩
    let eT : AtlasFrame T := ⟨trivializationAt ℂ T.Fiber (f y₀), inferInstance⟩
    have hL : f y₀ ∈ eL.val.baseSet := mem_baseSet_trivializationAt ℂ L.Fiber (f y₀)
    have hA : f y₀ ∈ eA.val.baseSet := mem_baseSet_trivializationAt ℂ A.Fiber (f y₀)
    have hT : f y₀ ∈ eT.val.baseSet := mem_baseSet_trivializationAt ℂ T.Fiber (f y₀)
    let HF := twistedPowerAtlasFrame
      (pullFrame f (tensorAtlasFrame (positivePowerAtlasFrame eL K) eA))
      (pullFrame f (twistedPowerAtlasFrame eL eT r)) q
    let HE := twistedPowerAtlasFrame (pullFrame f eL) (pullFrame f eT) (r + (K + 1) * q)
    let GA := pullFrame f eA
    let := HF.property
    let := HE.property
    let := GA.property
    have hKm := positivePowerAtlasFrame_mem eL hL K
    have hHF : y₀ ∈ HF.val.baseSet := twistedPowerAtlasFrame_mem _ _
      (mem_pullFrame_baseSet f _ (show f y₀ ∈ (tensorAtlasFrame (positivePowerAtlasFrame eL K)
        eA).val.baseSet from ⟨hKm, hA⟩))
      (mem_pullFrame_baseSet f _ (twistedPowerAtlasFrame_mem eL eT hL hT r)) q
    have hHE : y₀ ∈ HE.val.baseSet := twistedPowerAtlasFrame_mem _ _
      (mem_pullFrame_baseSet f eL hL) (mem_pullFrame_baseSet f eT hT) _
    have hGA : y₀ ∈ GA.val.baseSet := mem_pullFrame_baseSet f eA hA
    apply (HF.val.contMDiffAt_section_iff hHF).mpr
    have ht := (HE.val.contMDiffAt_section_iff hHE).mp (t.contMDiff y₀)
    have hs := (GA.val.contMDiffAt_section_iff hGA).mp ((pullSection f sA).contMDiff y₀)
    apply ((hs.pow q).mul ht).congr_of_eventuallyEq
    have hopen : IsOpen (f ⁻¹' (eL.val.baseSet ∩ eA.val.baseSet ∩ eT.val.baseSet)) :=
      ((eL.val.open_baseSet.inter eA.val.open_baseSet).inter eT.val.open_baseSet).preimage
        f.contMDiff.continuous
    filter_upwards [hopen.mem_nhds ⟨⟨hL, hA⟩, hT⟩] with y hy
    have hyHF : y ∈ HF.val.baseSet := twistedPowerAtlasFrame_mem _ _
      (mem_pullFrame_baseSet f _ (show f y ∈ (tensorAtlasFrame (positivePowerAtlasFrame eL K)
        eA).val.baseSet from ⟨positivePowerAtlasFrame_mem eL hy.1.1 K, hy.1.2⟩))
      (mem_pullFrame_baseSet f _ (twistedPowerAtlasFrame_mem eL eT hy.1.1 hy.2 r)) q
    have hyHE : y ∈ HE.val.baseSet := twistedPowerAtlasFrame_mem _ _
      (mem_pullFrame_baseSet f eL hy.1.1) (mem_pullFrame_baseSet f eT hy.2) _
    rw [← frameCoord_apply HF hyHF, frameCoord_transferFiber f eL eA eT hy.1.1 hy.1.2 hy.2,
      frameCoord_apply HE hyHE, frameCoord_apply eA hy.1.2]
    rfl

theorem transferSection_apply (sA : HolomorphicSections (n := n) A.Fiber)
    (t : twistedSections (restrictBundle L f) (restrictBundle T f) (r + (K + 1) * q)) (y : V) :
    transferSection f L A T K r q sA t y = transferFiber f L A T K r q (sA (f y)) (t y) := rfl

variable (L A T K r q) in
/-- The transfer is `ℂ`-linear. -/
def transferSectionLinear (sA : HolomorphicSections (n := n) A.Fiber) :
    twistedSections (restrictBundle L f) (restrictBundle T f) (r + (K + 1) * q) →ₗ[ℂ]
      twistedSections (restrictBundle (perturbedBundle L A K) f)
        (restrictBundle (twistedPower L T r) f) q where
  toFun := transferSection f L A T K r q sA
  map_add' s t := by
    ext y
    simp [transferSection_apply]
  map_smul' c s := by
    ext y
    simp [transferSection_apply]

/-- `transferFiber σ v = 0` only if `σ = 0` or `v = 0`. -/
theorem transferFiber_eq_zero {y : V} (σ : A.Fiber (f y))
    (v : (twistedPower (restrictBundle L f) (restrictBundle T f) (r + (K + 1) * q)).Fiber y)
    (h : transferFiber f L A T K r q σ v = 0) : σ = 0 ∨ v = 0 := by
  let eL : AtlasFrame L := ⟨trivializationAt ℂ L.Fiber (f y), inferInstance⟩
  let eA : AtlasFrame A := ⟨trivializationAt ℂ A.Fiber (f y), inferInstance⟩
  let eT : AtlasFrame T := ⟨trivializationAt ℂ T.Fiber (f y), inferInstance⟩
  have hL : f y ∈ eL.val.baseSet := mem_baseSet_trivializationAt ℂ L.Fiber (f y)
  have hA : f y ∈ eA.val.baseSet := mem_baseSet_trivializationAt ℂ A.Fiber (f y)
  have hT : f y ∈ eT.val.baseSet := mem_baseSet_trivializationAt ℂ T.Fiber (f y)
  have hc := frameCoord_transferFiber f eL eA eT hL hA hT σ v
  rw [h, map_zero] at hc
  rcases mul_eq_zero.mp hc.symm with ha | hv
  · exact Or.inl ((frameCoord_eq_zero_iff eA hA σ).mp (pow_eq_zero_iff'.mp ha).1)
  · exact Or.inr ((frameCoord_eq_zero_iff _ (twistedPowerAtlasFrame_mem _ _
      (mem_pullFrame_baseSet f eL hL) (mem_pullFrame_baseSet f eT hT) _) v).mp hv)

/-- **The transfer is injective** if `ϕ|_V ≠ 0` (`V` connected; identity theorem). -/
theorem transferSectionLinear_injective [ConnectedSpace V]
    {sA : HolomorphicSections (n := n) A.Fiber} (hsA : pullSection f sA ≠ 0) :
    Function.Injective (transferSectionLinear f L A T K r q sA) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro t ht
  by_contra hne
  have hZA := sectionZeroSet_isComplexAnalytic (n := m) (restrictBundle A f).Fiber (pullSection f sA)
  have hZt := sectionZeroSet_isComplexAnalytic (n := m)
    (twistedPower (restrictBundle L f) (restrictBundle T f) (r + (K + 1) * q)).Fiber t
  have hiA := Pending.PshAnalyticSetExtension.IsComplexAnalyticSubset.interior_eq_empty_of_ne_univ
    hZA (sectionZeroSet_ne_univ _ _ hsA)
  have hit := Pending.PshAnalyticSetExtension.IsComplexAnalyticSubset.interior_eq_empty_of_ne_univ
    hZt (sectionZeroSet_ne_univ _ t hne)
  have hunion : sectionZeroSet (n := m) (restrictBundle A f).Fiber (pullSection f sA) ∪
      sectionZeroSet (n := m)
        (twistedPower (restrictBundle L f) (restrictBundle T f) (r + (K + 1) * q)).Fiber t =
        Set.univ := by
    apply Set.eq_univ_of_forall
    intro y
    have h0 : transferFiber f L A T K r q (sA (f y)) (t y) = 0 := by
      have := congrArg (fun u => u y) ht
      simpa [transferSectionLinear, transferSection_apply] using this
    exact transferFiber_eq_zero f (sA (f y)) (t y) h0
  have hint := interior_union_isClosed_of_interior_empty hZA.isClosed hit
  rw [hunion, interior_univ, hiA] at hint
  obtain ⟨y⟩ := (inferInstance : Nonempty V)
  exact (Set.eq_empty_iff_forall_notMem.mp hint) y (Set.mem_univ y)

theorem holomorphicAt_pow' {h : V → ℂ} {y : V} (hh : HolomorphicAt m h y) :
    ∀ j : ℕ, HolomorphicAt m (fun z => h z ^ j) y
  | 0 => by simpa using holomorphicAt_const (n := m) (x := y) (1 : ℂ)
  | j + 1 => by simpa [pow_succ] using (holomorphicAt_pow' hh j).mul hh

end Transfer

/-! ### Membership and dimensions on a submanifold -/

section Submanifold

variable {n m : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [CompactSpace X] {W : Set X}
  [ChartedSpace (ComplexModel m) W] [IsComplexManifold m W]
  (hval : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ (Subtype.val : W → X))
  {L A T : HermitianHolomorphicLineBundle.{0, 0} n X} {K r q : ℕ}

/-- `𝓘(q · (K+1)φ) = 𝓘((K+1)q · φ)`. -/
theorem sourceDegreeMultiplierIdeal_scaled (φ : X → EReal) (K q : ℕ) :
    sourceDegreeMultiplierIdeal (n := n) q (fun x => (((K + 1 : ℕ) : ℝ) : EReal) * φ x) =
      sourceDegreeMultiplierIdeal (n := n) ((K + 1) * q) φ := by
  unfold sourceDegreeMultiplierIdeal
  congr 1
  funext x
  rw [← mul_assoc, ← EReal.coe_mul]
  congr 2
  push_cast
  ring

/-- **The transfer preserves the restricted multiplier ideals**:
`t ∈ H⁰(W, (L^k ⊗ T)|_W ⊗ Res_W 𝓘(kφ))`, `k = r + (K+1)q`, gives
`t ⊗ ϕ^q ∈ H⁰(W, ((L^{K+1} ⊗ A)^q ⊗ L^r ⊗ T)|_W ⊗ Res_W 𝓘(q (K+1) φ))`. -/
theorem transferSection_mem {φ : X → EReal} (hφ : IsGlobalQuasiPshPotential (n := n) φ)
    (sA : HolomorphicSections (n := n) A.Fiber)
    {t : twistedSections (restrictBundle L ⟨Subtype.val, hval⟩)
      (restrictBundle T ⟨Subtype.val, hval⟩) (r + (K + 1) * q)}
    (ht : t ∈ fullHolomorphicIdealSections (n := m)
      (twistedPower (restrictBundle L ⟨Subtype.val, hval⟩) (restrictBundle T ⟨Subtype.val, hval⟩)
        (r + (K + 1) * q)).Fiber
      (restrictIdeal (k := m) (W := W) (sourceDegreeMultiplierIdeal (n := n) (r + (K + 1) * q) φ))) :
    transferSection ⟨Subtype.val, hval⟩ L A T K r q sA t ∈ fullHolomorphicIdealSections (n := m)
      (twistedPower (restrictBundle (perturbedBundle L A K) ⟨Subtype.val, hval⟩)
        (restrictBundle (twistedPower L T r) ⟨Subtype.val, hval⟩) q).Fiber
      (restrictIdeal (k := m) (W := W) (sourceDegreeMultiplierIdeal (n := n) q
        (fun x => (((K + 1 : ℕ) : ℝ) : EReal) * φ x))) := by
  let f : ContMDiffMap 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) W X ∞ := ⟨Subtype.val, hval⟩
  have hR : (restrictIdeal (k := m) (W := W)
      (sourceDegreeMultiplierIdeal (n := n) (r + (K + 1) * q) φ)).IsCoherent :=
    GermIdealPullbackCalculus.isCoherent_pullback hval (sourceDegreeMultiplierIdeal_isCoherent _ hφ)
  have hRR : (restrictIdeal (k := m) (W := W)
      (sourceDegreeMultiplierIdeal (n := n) (r + (K + 1) * q) φ)).Le
      (restrictIdeal (k := m) (W := W) (sourceDegreeMultiplierIdeal (n := n) q
        (fun x => (((K + 1 : ℕ) : ℝ) : EReal) * φ x))) := by
    rw [sourceDegreeMultiplierIdeal_scaled]
    exact restrictIdeal_mono (sourceDegreeMultiplierIdeal_le_of_le hφ (by omega))
  apply mem_fullHolomorphicIdealSections_of_frame
  intro y
  let eL : AtlasFrame L := ⟨trivializationAt ℂ L.Fiber (f y), inferInstance⟩
  let eA : AtlasFrame A := ⟨trivializationAt ℂ A.Fiber (f y), inferInstance⟩
  let eT : AtlasFrame T := ⟨trivializationAt ℂ T.Fiber (f y), inferInstance⟩
  have hL : f y ∈ eL.val.baseSet := mem_baseSet_trivializationAt ℂ L.Fiber (f y)
  have hA : f y ∈ eA.val.baseSet := mem_baseSet_trivializationAt ℂ A.Fiber (f y)
  have hT : f y ∈ eT.val.baseSet := mem_baseSet_trivializationAt ℂ T.Fiber (f y)
  let HF := twistedPowerAtlasFrame
    (pullFrame f (tensorAtlasFrame (positivePowerAtlasFrame eL K) eA))
    (pullFrame f (twistedPowerAtlasFrame eL eT r)) q
  let HE := twistedPowerAtlasFrame (pullFrame f eL) (pullFrame f eT) (r + (K + 1) * q)
  let GA := pullFrame f eA
  have hKm := positivePowerAtlasFrame_mem eL hL K
  have hHF : y ∈ HF.val.baseSet := twistedPowerAtlasFrame_mem _ _
    (mem_pullFrame_baseSet f _ (show f y ∈ (tensorAtlasFrame (positivePowerAtlasFrame eL K)
      eA).val.baseSet from ⟨hKm, hA⟩))
    (mem_pullFrame_baseSet f _ (twistedPowerAtlasFrame_mem eL eT hL hT r)) q
  have hHE : y ∈ HE.val.baseSet := twistedPowerAtlasFrame_mem _ _
    (mem_pullFrame_baseSet f eL hL) (mem_pullFrame_baseSet f eT hT) _
  have hGA : y ∈ GA.val.baseSet := mem_pullFrame_baseSet f eA hA
  refine ⟨⟨HF.val, HF.property⟩, hHF, ?_⟩
  have hE := hRR y _ (coefficient_mem_of_mem_full _ _ hR ht ⟨HE.val, HE.property⟩ hHE)
  have hh : HolomorphicAt m (fun z => sectionCoefficient (restrictBundle A f).Fiber GA.val
      (pullSection f sA) z ^ q) y :=
    holomorphicAt_pow' (originalSectionCoefficient_holomorphicAt (n := m) _ ⟨GA.val, GA.property⟩
      (pullSection f sA) hGA) q
  rw [mem_restrictIdeal_iff] at hE ⊢
  have hmul := RelativePrincipalizationSpan.IsInSpanAt.mul_left hh hE
  have hopen : IsOpen (f ⁻¹' (eL.val.baseSet ∩ eA.val.baseSet ∩ eT.val.baseSet)) :=
    ((eL.val.open_baseSet.inter eA.val.open_baseSet).inter eT.val.open_baseSet).preimage
      f.contMDiff.continuous
  have heq : (fun z => sectionCoefficient (restrictBundle A f).Fiber GA.val (pullSection f sA) z ^ q *
      sectionCoefficient _ HE.val t z) =ᶠ[𝓝 y]
      sectionCoefficient _ HF.val (transferSection f L A T K r q sA t) := by
    filter_upwards [hopen.mem_nhds ⟨⟨hL, hA⟩, hT⟩] with z hz
    have hzHF : z ∈ HF.val.baseSet := twistedPowerAtlasFrame_mem _ _
      (mem_pullFrame_baseSet f _ (show f z ∈ (tensorAtlasFrame (positivePowerAtlasFrame eL K)
        eA).val.baseSet from ⟨positivePowerAtlasFrame_mem eL hz.1.1 K, hz.1.2⟩))
      (mem_pullFrame_baseSet f _ (twistedPowerAtlasFrame_mem eL eT hz.1.1 hz.2 r)) q
    have hzHE : z ∈ HE.val.baseSet := twistedPowerAtlasFrame_mem _ _
      (mem_pullFrame_baseSet f eL hz.1.1) (mem_pullFrame_baseSet f eT hz.2) _
    change (GA.val ⟨z, sA (f z)⟩).2 ^ q * (HE.val ⟨z, t z⟩).2 =
      (HF.val ⟨z, transferFiber f L A T K r q (sA (f z)) (t z)⟩).2
    rw [← frameCoord_apply HF hzHF, frameCoord_transferFiber f eL eA eT hz.1.1 hz.1.2 hz.2,
      frameCoord_apply HE hzHE, frameCoord_apply eA hz.1.2]
    rfl
  obtain ⟨hhol, N, s, a, hs, ha, hsum⟩ := hmul
  exact ⟨hhol.congr heq, N, s, a, hs, ha, heq.symm.trans hsum⟩

/-- **`h⁰(Y, T|_Y ⊗ L|_Y^{r+(K+1)q} ⊗ Res_Y 𝓘((r+(K+1)q)φ)) ≤
h⁰(Y, (L^r ⊗ T)|_Y ⊗ (L^{K+1} ⊗ A)|_Y^q ⊗ Res_Y 𝓘(q (K+1)φ))`** when `ϕ|_Y ≠ 0`. -/
theorem idealH0_le_transfer [CompactSpace W] [ConnectedSpace W] {φ : X → EReal}
    (hφ : IsGlobalQuasiPshPotential (n := n) φ) {sA : HolomorphicSections (n := n) A.Fiber}
    (hsA : pullSection ⟨Subtype.val, hval⟩ sA ≠ 0) :
    idealH0 (restrictBundle L ⟨Subtype.val, hval⟩) (restrictBundle T ⟨Subtype.val, hval⟩)
        (r + (K + 1) * q)
        (restrictIdeal (k := m) (W := W) (sourceDegreeMultiplierIdeal (n := n) (r + (K + 1) * q) φ)) ≤
      idealH0 (restrictBundle (perturbedBundle L A K) ⟨Subtype.val, hval⟩)
        (restrictBundle (twistedPower L T r) ⟨Subtype.val, hval⟩) q
        (restrictIdeal (k := m) (W := W) (sourceDegreeMultiplierIdeal (n := n) q
          (fun x => (((K + 1 : ℕ) : ℝ) : EReal) * φ x))) := by
  rw [idealH0_eq_finrank, idealH0_eq_finrank]
  have := twistedSections_finiteDimensional (restrictBundle (perturbedBundle L A K) ⟨Subtype.val, hval⟩)
    (restrictBundle (twistedPower L T r) ⟨Subtype.val, hval⟩) q
  let Φ := ((transferSectionLinear ⟨Subtype.val, hval⟩ L A T K r q sA).domRestrict
    (fullHolomorphicIdealSections (n := m)
      (twistedPower (restrictBundle L ⟨Subtype.val, hval⟩) (restrictBundle T ⟨Subtype.val, hval⟩)
        (r + (K + 1) * q)).Fiber
      (restrictIdeal (k := m) (W := W)
        (sourceDegreeMultiplierIdeal (n := n) (r + (K + 1) * q) φ)))).codRestrict _
    (fun t => transferSection_mem hval hφ sA t.2)
  refine LinearMap.finrank_le_finrank_of_injective (f := Φ) fun s t hst => ?_
  apply Subtype.ext
  apply transferSectionLinear_injective ⟨Subtype.val, hval⟩ hsA
  exact congrArg Subtype.val hst

end Submanifold

end SGPT.Trace.RestVol
