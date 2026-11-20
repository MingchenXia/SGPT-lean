import SGPT.Bergman.SourceTwistedMultiplierSections
import SGPT.Bergman.SourceBergmanNorms

/-!
# Multiplication of holomorphic sections of tensor powers

Blueprint `claude-dx-low2`, node `claude-dx-low2:mul`. Used in the book's Step 1 of the proof of
`thm:DXmain1` (chapter *`𝓘`-good singularities*): multiplication by a fixed non-zero section
`s ∈ H⁰(X, L^b)` maps `H⁰(X, L^m ⊗ T)` injectively into `H⁰(X, L^{m+b} ⊗ T)`.

For the literal tensor powers of the Bergman chapter (`positivePower L p = L^{⊗(p+1)}`,
`twistedPower L T m = L^{⊗m} ⊗ T`) we construct

* `mulOneFiber`: the fiberwise bilinear map `L ⊗ (L^{⊗m} ⊗ T) → L^{⊗(m+1)} ⊗ T`;
* `mulFiber`: the fiberwise bilinear map `L^{⊗(p+1)} ⊗ (L^{⊗m} ⊗ T) → L^{⊗(m+p+1)} ⊗ T`;
* `coord_mulFiber`: in product frames, the coordinate of a product is the product of the
  coordinates;
* `mulSection s t`: the product of holomorphic sections `s ∈ H⁰(L^{⊗(p+1)} ⊗ 𝒪)` and
  `t ∈ H⁰(L^{⊗m} ⊗ T)`, a holomorphic section of `L^{⊗(m+p+1)} ⊗ T`, with
  `|s t| = |s| |t|` for the tensor metrics (`norm_mulSection`);
* `mulSection_injective`: on a connected manifold, multiplication by `s ≠ 0` is injective
  (identity theorem).
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.IGood.DXLow2

open Bundle Set Filter TensorProduct
open scoped Manifold ContDiff Topology TensorProduct
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.QuantizationDraft
open HermitianHolomorphicLineBundle

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

/-! ### Coordinates of tensors -/

section Coordinates

/-- The coordinate of a fiber element in an atlas frame (the linear map of the trivialization). -/
def frameCoord {V : HermitianHolomorphicLineBundle.{0, 0} n X} (g : AtlasFrame V) (x : X) :
    V.Fiber x →ₗ[ℂ] ℂ :=
  letI := g.property
  g.val.linearMapAt ℂ x

theorem frameCoord_apply {V : HermitianHolomorphicLineBundle.{0, 0} n X} (g : AtlasFrame V)
    {x : X} (hx : x ∈ g.val.baseSet) (v : V.Fiber x) :
    frameCoord g x v = (g.val ⟨x, v⟩).2 := by
  let := g.property
  change g.val.linearMapAt ℂ x v = _
  rw [Trivialization.coe_linearMapAt_of_mem _ hx]

/-- On its base set, the coordinate of an atlas frame is injective. -/
theorem frameCoord_eq_zero_iff {V : HermitianHolomorphicLineBundle.{0, 0} n X} (g : AtlasFrame V)
    {x : X} (hx : x ∈ g.val.baseSet) (v : V.Fiber x) : frameCoord g x v = 0 ↔ v = 0 := by
  let := g.property
  change g.val.linearMapAt ℂ x v = 0 ↔ v = 0
  rw [Trivialization.linearMapAt_def_of_mem _ hx]
  exact (g.val.linearEquivAt ℂ x hx).map_eq_zero_iff

variable {L T : HermitianHolomorphicLineBundle.{0, 0} n X}

/-- The coordinate of a pure tensor in a product frame is the product of the coordinates. -/
theorem frameCoord_tensor_tmul (e : AtlasFrame L) (f : AtlasFrame T) {x : X}
    (hx : x ∈ e.val.baseSet) (hy : x ∈ f.val.baseSet) (a : L.Fiber x) (b : T.Fiber x) :
    frameCoord (tensorAtlasFrame e f) x (a ⊗ₜ[ℂ] b) = frameCoord e x a * frameCoord f x b := by
  let := e.property; let := f.property
  exact (frameCoord_apply (tensorAtlasFrame e f) (show x ∈ (tensorAtlasFrame e f).val.baseSet from
    ⟨hx, hy⟩) (a ⊗ₜ[ℂ] b)).trans (tensorCoordinate_tmul L.Fiber T.Fiber e.val f.val x a b)

/-- The coordinate of the unit frame is the identity. -/
theorem frameCoord_unit (x : X) (c : (unit (n := n) (M := X)).Fiber x) :
    frameCoord (unitAtlasFrame (n := n) (M := X)) x c = c := by
  exact (frameCoord_apply _ (Set.mem_univ x) c).trans rfl

/-- The coordinate in the degree-zero frame `𝒪 ⊗ T` is the `T`-coordinate of the unit image. -/
theorem frameCoord_zeroTwist (f : AtlasFrame T) {x : X} (hy : x ∈ f.val.baseSet)
    (w : (tensor unit T).Fiber x) :
    frameCoord (tensorAtlasFrame unitAtlasFrame f) x w =
      frameCoord f x (zeroTwistFiberIsometry T x w) := by
  exact (frameCoord_apply (tensorAtlasFrame unitAtlasFrame f)
    (show x ∈ (tensorAtlasFrame unitAtlasFrame f).val.baseSet from ⟨Set.mem_univ x, hy⟩) w).trans
    ((zeroTwist_coordinate f hy w).trans (frameCoord_apply f hy _).symm)

end Coordinates

/-! ### The fiberwise product -/

section Fiber

variable (L T : HermitianHolomorphicLineBundle.{0, 0} n X) (x : X)

/-- Multiplication by one factor of `L`: `l ⊗ w ↦ l · w`, `L ⊗ (L^{⊗m} ⊗ T) → L^{⊗(m+1)} ⊗ T`. -/
def mulOneFiber : ∀ m : ℕ,
    L.Fiber x →ₗ[ℂ] (twistedPower L T m).Fiber x →ₗ[ℂ] (twistedPower L T (m + 1)).Fiber x
  | 0 => (TensorProduct.mk ℂ (L.Fiber x) (T.Fiber x)).compl₂
      (zeroTwistFiberIsometry T x).toLinearEquiv.toLinearMap
  | m + 1 => LinearMap.rTensorHom (T.Fiber x) ∘ₗ
      (TensorProduct.mk ℂ ((positivePower L m).Fiber x) (L.Fiber x)).flip

/-- Multiplication `L^{⊗(p+1)} ⊗ (L^{⊗m} ⊗ T) → L^{⊗(m+p+1)} ⊗ T`. -/
def mulFiber (m : ℕ) : ∀ p : ℕ,
    (positivePower L p).Fiber x →ₗ[ℂ] (twistedPower L T m).Fiber x →ₗ[ℂ]
      (twistedPower L T (m + p + 1)).Fiber x
  | 0 => mulOneFiber L T x m
  | p + 1 => TensorProduct.lift
      ((LinearMap.llcomp ℂ ((twistedPower L T m).Fiber x)
        ((twistedPower L T (m + p + 1)).Fiber x)
        ((twistedPower L T (m + p + 1 + 1)).Fiber x) ∘ₗ mulOneFiber L T x (m + p + 1)).flip ∘ₗ
        mulFiber m p)

theorem mulFiber_succ_tmul (m p : ℕ) (a : (positivePower L p).Fiber x) (l : L.Fiber x)
    (w : (twistedPower L T m).Fiber x) :
    mulFiber L T x m (p + 1) (a ⊗ₜ[ℂ] l) w =
      mulOneFiber L T x (m + p + 1) l (mulFiber L T x m p a w) := by
  rfl

variable {L T x}

/-- **Coordinates of a product by one factor of `L`.** -/
theorem frameCoord_mulOneFiber (e : AtlasFrame L) (f : AtlasFrame T)
    (hx : x ∈ e.val.baseSet) (hy : x ∈ f.val.baseSet) :
    ∀ (m : ℕ) (l : L.Fiber x) (w : (twistedPower L T m).Fiber x),
      frameCoord (twistedPowerAtlasFrame e f (m + 1)) x (mulOneFiber L T x m l w) =
        frameCoord e x l * frameCoord (twistedPowerAtlasFrame e f m) x w
  | 0, l, w => by
    have h1 := frameCoord_tensor_tmul e f hx hy l (zeroTwistFiberIsometry T x w)
    have h2 := frameCoord_zeroTwist f hy w
    exact h1.trans (congrArg (frameCoord e x l * ·) h2.symm)
  | m + 1, l, w => by
    have hm := positivePowerAtlasFrame_mem e hx m
    have key : (frameCoord (twistedPowerAtlasFrame e f (m + 1 + 1)) x).comp
        (mulOneFiber L T x (m + 1) l) =
        frameCoord e x l • frameCoord (twistedPowerAtlasFrame e f (m + 1)) x := by
      apply TensorProduct.ext'
      intro a t
      have h1 := frameCoord_tensor_tmul (tensorAtlasFrame (positivePowerAtlasFrame e m) e) f
        (show x ∈ (tensorAtlasFrame (positivePowerAtlasFrame e m) e).val.baseSet from ⟨hm, hx⟩)
        hy (a ⊗ₜ[ℂ] l) t
      have h2 := frameCoord_tensor_tmul (positivePowerAtlasFrame e m) e hm hx a l
      have h3 := frameCoord_tensor_tmul (positivePowerAtlasFrame e m) f hm hy a t
      change frameCoord (tensorAtlasFrame (tensorAtlasFrame (positivePowerAtlasFrame e m) e) f) x
          ((a ⊗ₜ[ℂ] l) ⊗ₜ[ℂ] t) =
        frameCoord e x l * frameCoord (tensorAtlasFrame (positivePowerAtlasFrame e m) f) x
          (a ⊗ₜ[ℂ] t)
      rw [h1, h2, h3]
      ring
    exact LinearMap.congr_fun key w

/-- **Coordinates of a product**: in product frames, the coordinate of `a · w` is the product of
the coordinates of `a ∈ L^{⊗(p+1)}` and `w ∈ L^{⊗m} ⊗ T`. -/
theorem frameCoord_mulFiber (e : AtlasFrame L) (f : AtlasFrame T)
    (hx : x ∈ e.val.baseSet) (hy : x ∈ f.val.baseSet) (m : ℕ) :
    ∀ (p : ℕ) (a : (positivePower L p).Fiber x) (w : (twistedPower L T m).Fiber x),
      frameCoord (twistedPowerAtlasFrame e f (m + p + 1)) x (mulFiber L T x m p a w) =
        frameCoord (positivePowerAtlasFrame e p) x a * frameCoord (twistedPowerAtlasFrame e f m) x w
  | 0, a, w => frameCoord_mulOneFiber e f hx hy m a w
  | p + 1, a, w => by
    have hp := positivePowerAtlasFrame_mem e hx p
    have key : (frameCoord (twistedPowerAtlasFrame e f (m + (p + 1) + 1)) x).comp
        ((mulFiber L T x m (p + 1)).flip w) =
        frameCoord (twistedPowerAtlasFrame e f m) x w •
          frameCoord (positivePowerAtlasFrame e (p + 1)) x := by
      apply TensorProduct.ext'
      intro b l
      have h1 := mulFiber_succ_tmul L T x m p b l w
      have h2 := frameCoord_mulOneFiber e f hx hy (m + p + 1) l (mulFiber L T x m p b w)
      have h3 := frameCoord_mulFiber e f hx hy m p b w
      have h4 := frameCoord_tensor_tmul (positivePowerAtlasFrame e p) e hp hx b l
      change frameCoord (twistedPowerAtlasFrame e f (m + p + 1 + 1)) x
          (mulFiber L T x m (p + 1) (b ⊗ₜ[ℂ] l) w) =
        frameCoord (twistedPowerAtlasFrame e f m) x w *
          frameCoord (tensorAtlasFrame (positivePowerAtlasFrame e p) e) x (b ⊗ₜ[ℂ] l)
      rw [h1, h2, h3, h4]
      ring
    have := LinearMap.congr_fun key a
    simp only [LinearMap.comp_apply, LinearMap.flip_apply, LinearMap.smul_apply,
      smul_eq_mul] at this
    rw [this, mul_comm]

end Fiber

/-! ### Products of holomorphic sections -/

section Sections

variable {L T : HermitianHolomorphicLineBundle.{0, 0} n X}

/-- The unit isomorphism `L^{⊗(p+1)} ⊗ 𝒪 → L^{⊗(p+1)}`. -/
def unitTwistFiber (p : ℕ) (x : X) :
    (twistedPower L unit (p + 1)).Fiber x →ₗ[ℂ] (positivePower L p).Fiber x :=
  (TensorProduct.rid ℂ ((positivePower L p).Fiber x)).toLinearMap

theorem frameCoord_unitTwistFiber (e : AtlasFrame L) {x : X} (hx : x ∈ e.val.baseSet) (p : ℕ)
    (v : (twistedPower L unit (p + 1)).Fiber x) :
    frameCoord (positivePowerAtlasFrame e p) x (unitTwistFiber p x v) =
      frameCoord (twistedPowerAtlasFrame e unitAtlasFrame (p + 1)) x v := by
  have hp := positivePowerAtlasFrame_mem e hx p
  have key : (frameCoord (positivePowerAtlasFrame e p) x).comp (unitTwistFiber (L := L) p x) =
      frameCoord (twistedPowerAtlasFrame e unitAtlasFrame (p + 1)) x := by
    apply TensorProduct.ext'
    intro a c
    have h1 := frameCoord_tensor_tmul (positivePowerAtlasFrame e p)
      (unitAtlasFrame (n := n) (M := X)) hp (Set.mem_univ x) a c
    change frameCoord (positivePowerAtlasFrame e p) x (TensorProduct.rid ℂ _ (a ⊗ₜ[ℂ] c)) =
      frameCoord (tensorAtlasFrame (positivePowerAtlasFrame e p) unitAtlasFrame) x (a ⊗ₜ[ℂ] c)
    rw [h1]
    have h2 : TensorProduct.rid ℂ ((positivePower L p).Fiber x) (a ⊗ₜ[ℂ] (show ℂ from c)) =
        (show ℂ from c) • a :=
      TensorProduct.rid_tmul a _
    erw [h2]
    rw [map_smul, frameCoord_unit, smul_eq_mul, mul_comm]
  exact LinearMap.congr_fun key v

/-- The product of holomorphic sections `s ∈ H⁰(X, L^{⊗(p+1)} ⊗ 𝒪)` and
`t ∈ H⁰(X, L^{⊗m} ⊗ T)`, a holomorphic section of `L^{⊗(m+p+1)} ⊗ T`. -/
def mulSection {p m : ℕ} (s : twistedSections L unit (p + 1)) (t : twistedSections L T m) :
    twistedSections L T (m + p + 1) where
  toFun x := mulFiber L T x m p (unitTwistFiber p x (s x)) (t x)
  contMDiff_toFun := by
    intro x₀
    let e : AtlasFrame L := ⟨trivializationAt ℂ L.Fiber x₀, inferInstance⟩
    let f : AtlasFrame T := ⟨trivializationAt ℂ T.Fiber x₀, inferInstance⟩
    have he : x₀ ∈ e.val.baseSet := mem_baseSet_trivializationAt ℂ L.Fiber x₀
    have hf : x₀ ∈ f.val.baseSet := mem_baseSet_trivializationAt ℂ T.Fiber x₀
    let G := twistedPowerAtlasFrame e f (m + p + 1)
    let S := twistedPowerAtlasFrame e (unitAtlasFrame (n := n) (M := X)) (p + 1)
    let F := twistedPowerAtlasFrame e f m
    let := G.property
    let := S.property
    let := F.property
    have hG : ∀ y ∈ e.val.baseSet ∩ f.val.baseSet, y ∈ G.val.baseSet := fun y hy =>
      twistedPowerAtlasFrame_mem e f hy.1 hy.2 _
    have hS : ∀ y ∈ e.val.baseSet, y ∈ S.val.baseSet := fun y hy =>
      twistedPowerAtlasFrame_mem e unitAtlasFrame hy (Set.mem_univ y) _
    have hF : ∀ y ∈ e.val.baseSet ∩ f.val.baseSet, y ∈ F.val.baseSet := fun y hy =>
      twistedPowerAtlasFrame_mem e f hy.1 hy.2 _
    apply (G.val.contMDiffAt_section_iff (hG x₀ ⟨he, hf⟩)).mpr
    have hs := (S.val.contMDiffAt_section_iff (hS x₀ he)).mp (s.contMDiff x₀)
    have ht := (F.val.contMDiffAt_section_iff (hF x₀ ⟨he, hf⟩)).mp (t.contMDiff x₀)
    apply (hs.mul ht).congr_of_eventuallyEq
    filter_upwards [(e.val.open_baseSet.inter f.val.open_baseSet).mem_nhds ⟨he, hf⟩] with y hy
    calc (G.val ⟨y, mulFiber L T y m p (unitTwistFiber p y (s y)) (t y)⟩).2
        = frameCoord G y (mulFiber L T y m p (unitTwistFiber p y (s y)) (t y)) :=
          (frameCoord_apply G (hG y hy) _).symm
      _ = frameCoord (positivePowerAtlasFrame e p) y (unitTwistFiber p y (s y)) *
            frameCoord F y (t y) := frameCoord_mulFiber e f hy.1 hy.2 m p _ _
      _ = frameCoord S y (s y) * frameCoord F y (t y) := by
            rw [frameCoord_unitTwistFiber e hy.1]
      _ = (S.val ⟨y, s y⟩).2 * (F.val ⟨y, t y⟩).2 := by
            rw [frameCoord_apply S (hS y hy.1), frameCoord_apply F (hF y hy)]

theorem mulSection_apply {p m : ℕ} (s : twistedSections L unit (p + 1))
    (t : twistedSections L T m) (x : X) :
    mulSection s t x = mulFiber L T x m p (unitTwistFiber p x (s x)) (t x) := rfl

/-- Multiplication by `s` as a `ℂ`-linear map `H⁰(L^{⊗m} ⊗ T) → H⁰(L^{⊗(m+p+1)} ⊗ T)`. -/
def mulSectionLinear {p : ℕ} (s : twistedSections L unit (p + 1)) (m : ℕ) :
    twistedSections L T m →ₗ[ℂ] twistedSections L T (m + p + 1) where
  toFun := mulSection s
  map_add' t₁ t₂ := by
    ext x
    exact map_add (mulFiber L T x m p (unitTwistFiber p x (s x))) (t₁ x) (t₂ x)
  map_smul' c t := by
    ext x
    exact map_smul (mulFiber L T x m p (unitTwistFiber p x (s x))) c (t x)

theorem mulSectionLinear_apply {p : ℕ} (s : twistedSections L unit (p + 1)) (m : ℕ)
    (t : twistedSections L T m) : mulSectionLinear s m t = mulSection s t := rfl

/-- The frame of the unit bundle has norm one. -/
theorem norm_unitAtlasFrame_symm (x : X) :
    ‖(unitAtlasFrame (n := n) (M := X)).val.symm x 1‖ = 1 := by
  change ‖(Bundle.Trivial.trivialization X ℂ).symm x 1‖ = 1
  rw [Bundle.Trivial.trivialization_symm_apply, norm_one]

/-- **The tensor metric is multiplicative**: `|s t|_{h^{m+p+1} h_T} = |s|_{h^{p+1}} |t|_{h^m h_T}`. -/
theorem norm_mulSection {p m : ℕ} (s : twistedSections L unit (p + 1))
    (t : twistedSections L T m) (y : X) : ‖mulSection s t y‖ = ‖s y‖ * ‖t y‖ := by
  let e : AtlasFrame L := ⟨trivializationAt ℂ L.Fiber y, inferInstance⟩
  let f : AtlasFrame T := ⟨trivializationAt ℂ T.Fiber y, inferInstance⟩
  have he : y ∈ e.val.baseSet := mem_baseSet_trivializationAt ℂ L.Fiber y
  have hf : y ∈ f.val.baseSet := mem_baseSet_trivializationAt ℂ T.Fiber y
  let G := twistedPowerAtlasFrame e f (m + p + 1)
  let S := twistedPowerAtlasFrame e (unitAtlasFrame (n := n) (M := X)) (p + 1)
  let F := twistedPowerAtlasFrame e f m
  let := G.property
  let := S.property
  let := F.property
  have hG : y ∈ G.val.baseSet := twistedPowerAtlasFrame_mem e f he hf _
  have hS : y ∈ S.val.baseSet := twistedPowerAtlasFrame_mem e unitAtlasFrame he (Set.mem_univ y) _
  have hF : y ∈ F.val.baseSet := twistedPowerAtlasFrame_mem e f he hf _
  have nG := SGPT.Bergman.CompactHolomorphicSectionsDraft.norm_eq_coefficient_mul_frameNorm
    (twistedPower L T (m + p + 1)).Fiber G.val (mulSection s t) hG
  have nS := SGPT.Bergman.CompactHolomorphicSectionsDraft.norm_eq_coefficient_mul_frameNorm
    (twistedPower L unit (p + 1)).Fiber S.val s hS
  have nF := SGPT.Bergman.CompactHolomorphicSectionsDraft.norm_eq_coefficient_mul_frameNorm
    (twistedPower L T m).Fiber F.val t hF
  have fG := twistedPower_frame_norm e f he hf (m + p + 1)
  have fS := twistedPower_frame_norm e (unitAtlasFrame (n := n) (M := X)) he (Set.mem_univ y) (p + 1)
  have fF := twistedPower_frame_norm e f he hf m
  rw [norm_unitAtlasFrame_symm, mul_one] at fS
  have hc : SGPT.Bergman.CompactHolomorphicSectionsDraft.sectionCoefficient
      (twistedPower L T (m + p + 1)).Fiber G.val (mulSection s t) y =
      SGPT.Bergman.CompactHolomorphicSectionsDraft.sectionCoefficient
        (twistedPower L unit (p + 1)).Fiber S.val s y *
      SGPT.Bergman.CompactHolomorphicSectionsDraft.sectionCoefficient
        (twistedPower L T m).Fiber F.val t y := by
    change (G.val ⟨y, mulSection s t y⟩).2 = (S.val ⟨y, s y⟩).2 * (F.val ⟨y, t y⟩).2
    rw [← frameCoord_apply G hG, ← frameCoord_apply S hS, ← frameCoord_apply F hF,
      mulSection_apply, frameCoord_mulFiber e f he hf m p, frameCoord_unitTwistFiber e he]
  rw [nG, nS, nF, hc, norm_mul]
  simp only [SGPT.Bergman.CompactHolomorphicSectionsDraft.frameNorm]
  rw [fG, fS, fF]
  ring

/-- **Multiplication by a non-zero section is injective** (identity theorem: on a connected
manifold the zero sets of non-zero holomorphic sections are closed with empty interior). -/
theorem mulSection_eq_zero [ConnectedSpace X] {p m : ℕ} {s : twistedSections L unit (p + 1)}
    (hs : s ≠ 0) {t : twistedSections L T m} (hst : mulSection s t = 0) : t = 0 := by
  by_contra ht
  have hZs := sectionZeroSet_isComplexAnalytic (twistedPower L unit (p + 1)).Fiber s
  have hZt := sectionZeroSet_isComplexAnalytic (twistedPower L T m).Fiber t
  have hit := Pending.PshAnalyticSetExtension.IsComplexAnalyticSubset.interior_eq_empty_of_ne_univ
    hZt (sectionZeroSet_ne_univ _ t ht)
  have his := Pending.PshAnalyticSetExtension.IsComplexAnalyticSubset.interior_eq_empty_of_ne_univ
    hZs (sectionZeroSet_ne_univ _ s hs)
  have hunion : sectionZeroSet (twistedPower L unit (p + 1)).Fiber s ∪
      sectionZeroSet (twistedPower L T m).Fiber t = Set.univ := by
    apply Set.eq_univ_of_forall
    intro y
    have h0 : ‖mulSection s t y‖ = 0 := by rw [hst]; simp
    rw [norm_mulSection, mul_eq_zero, norm_eq_zero, norm_eq_zero] at h0
    exact h0
  have hint := interior_union_isClosed_of_interior_empty hZs.isClosed hit
  rw [hunion, interior_univ, his] at hint
  obtain ⟨y, -⟩ : ∃ y, s y ≠ 0 := by
    by_contra h
    exact hs (ContMDiffSection.ext fun y => not_not.mp fun hy => h ⟨y, hy⟩)
  exact (Set.eq_empty_iff_forall_notMem.mp hint) y (Set.mem_univ y)

theorem mulSectionLinear_injective [ConnectedSpace X] {p : ℕ}
    {s : twistedSections L unit (p + 1)} (hs : s ≠ 0) (m : ℕ) :
    Function.Injective (mulSectionLinear (T := T) s m) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  exact fun t ht => mulSection_eq_zero hs ht

end Sections

end SGPT.IGood.DXLow2
