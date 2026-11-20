import SGPT.Okounkov.ValGen2Hausdorff
import SGPT.Foundations.Schemes.BundleDualSheaf

/-!
# Dual line bundles and products of sections across twists

Lane POB-VALGEN2, blueprint `claude-val-gen2.tex`. Source: chapter *The theory of Okounkov
bodies*, proof of `prop:Deltaconvtwisted`, which multiplies sections of `T ⊗ L^k` by a fixed
section `s₀` of `T⁻¹ ⊗ L^{k₀}` and sections of `L^{k-k₀}` by a fixed section `s₁` of `T ⊗ L^{k₀}`.

The dual `T⁻¹ = T^∨` is `SGPT.Foundations.Schemes.bundleDual T` (the internal Hom into `𝒪_X`), with the dual
frames `LocalBundleFrame.dual`. This file adds:

* `dualAtlas`: the dual atlas of `T^∨`, and `localBundleFrameTransition_dual`: the transition of
  dual frames is the inverse transition.
* `coverProduct`: for line bundles `P, Q, R` with frames `p i, q i, r i` on a common cover such that
  `p i ⊗ q i` and `r i` have the same transitions, the product `H⁰(P) × H⁰(Q) → H⁰(R)` (through the
  isomorphism `P ⊗ Q ≅ R` descended from the matching frames,
  `SGPT.Foundations.Schemes.nativeMatchingBundleFrameIso`); in the frames it multiplies coefficients
  (`coverProduct_coefficients`), hence for a valuation `ν` it adds values
  (`plainSectionValue_coverProduct`).
* The two products of the source: `lowerProduct : H⁰(L^j) × H⁰(T ⊗ L^{k₁}) → H⁰(T ⊗ L^{j+k₁})` and
  `upperProduct : H⁰(T ⊗ L^k) × H⁰(T^∨ ⊗ L^{k₀}) → H⁰(L^{k+k₀})`, with additivity of values.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.Okounkov.ValGen2

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Opposite
open SGPT.Okounkov.AlgebraicValuation

universe u

/-! ### The dual atlas -/

section Dual

variable {X : Scheme.{u}}

/-- The atlas of the dual line bundle `T^∨` with the dual frames. -/
def dualAtlas {T : X.Modules} (a : LineBundleAtlas T) : LineBundleAtlas (bundleDual T) where
  I := a.I
  opens := a.opens
  covers := a.covers
  frame i := (a.frame i).dual

/-- **The transition of dual frames is the inverse transition.** -/
theorem localBundleFrameTransition_dual {T : X.Modules} {U V W : X.Opens}
    (e : LocalBundleFrame T U) (f : LocalBundleFrame T V) (i : W ⟶ U) (j : W ⟶ V) :
    localBundleFrameTransition e.dual f.dual i j = (localBundleFrameTransition e f i j)⁻¹ := by
  set τ := localBundleFrameTransition e f i j with hτ
  have key : ∀ α : bundleSections (bundleDual T) W,
      f.dual.coefficients j α = ((τ⁻¹ : (X.sheaf.obj.obj (op W))ˣ) : X.sheaf.obj.obj (op W)) *
        e.dual.coefficients i α := by
    intro α
    have h1 : f.dual.coefficients j α = bundleDualValue T W α ((f.coefficients j).symm 1) := rfl
    have h2 : e.dual.coefficients i α = bundleDualFrameCoefficient e i α := rfl
    rw [h1, h2, bundleDualValue_frame e i α]
    have h3 : e.coefficients i ((f.coefficients j).symm 1) =
        ((τ⁻¹ : (X.sheaf.obj.obj (op W))ˣ) : X.sheaf.obj.obj (op W)) := by
      have h := localBundleFrameTransition_coefficients e f i j ((f.coefficients j).symm 1)
      rw [LinearEquiv.apply_symm_apply] at h
      calc e.coefficients i ((f.coefficients j).symm 1)
          = ((τ⁻¹ : (X.sheaf.obj.obj (op W))ˣ) : X.sheaf.obj.obj (op W)) *
              ((τ : X.sheaf.obj.obj (op W)) * e.coefficients i ((f.coefficients j).symm 1)) := by
            rw [← mul_assoc, Units.inv_mul, one_mul]
        _ = ((τ⁻¹ : (X.sheaf.obj.obj (op W))ˣ) : X.sheaf.obj.obj (op W)) := by
            rw [← h, mul_one]
    rw [h3, mul_comm]
  apply Units.ext
  have h := localBundleFrameTransition_coefficients e.dual f.dual i j
    ((e.dual.coefficients i).symm 1)
  rw [LinearEquiv.apply_symm_apply, mul_one, key, LinearEquiv.apply_symm_apply, mul_one] at h
  exact h.symm

end Dual

/-! ### Products of sections through matching frames -/

section CoverProduct

variable {X : Scheme.{u}} {P Q R : X.Modules} {ι : Type u} (U : ι → X.Opens)
  (hc : ∀ x : X, ∃ i, x ∈ U i) (p : ∀ i, LocalBundleFrame P (U i))
  (q : ∀ i, LocalBundleFrame Q (U i)) (r : ∀ i, LocalBundleFrame R (U i))
  (hu : ∀ i j (W : X.Opens) (h : W ⟶ U i) (k : W ⟶ U j),
    localBundleFrameTransition ((p i).tensor (q i)) ((p j).tensor (q j)) h k =
      localBundleFrameTransition (r i) (r j) h k)

/-- The product `H⁰(P) × H⁰(Q) → H⁰(R)` through the isomorphism `P ⊗ Q ≅ R` descended from frames
`p i ⊗ q i` and `r i` with the same transitions. -/
def coverProduct (s : bundleSections P ⊤) (t : bundleSections Q ⊤) : bundleSections R ⊤ :=
  (nativeMatchingBundleFrameIso (bundleTensor P Q) R U hc (fun i => (p i).tensor (q i)) r
    hu).hom.val.app (op ⊤) (tensorSection P Q ⊤ s t)

/-- In the frames `r i`, `p i`, `q i`, the coefficient of a product is the product of the
coefficients. -/
theorem coverProduct_coefficients (i : ι) (s : bundleSections P ⊤) (t : bundleSections Q ⊤) :
    (r i).coefficients (𝟙 (U i)) (R.val.map (homOfLE le_top).op (coverProduct U hc p q r hu s t)) =
      (p i).coefficients (𝟙 (U i)) (P.val.map (homOfLE le_top).op s) *
        (q i).coefficients (𝟙 (U i)) (Q.val.map (homOfLE le_top).op t) := by
  let Φ := nativeMatchingBundleFrameIso (bundleTensor P Q) R U hc (fun i => (p i).tensor (q i)) r hu
  have hn := PresheafOfModules.naturality_apply Φ.hom.val (homOfLE (le_top : U i ≤ ⊤)).op
    (tensorSection P Q ⊤ s t)
  change Φ.hom.val.app (op (U i))
      ((bundleTensor P Q).val.map (homOfLE le_top).op (tensorSection P Q ⊤ s t)) =
    R.val.map (homOfLE le_top).op (Φ.hom.val.app (op ⊤) (tensorSection P Q ⊤ s t)) at hn
  change (r i).coefficients (𝟙 (U i)) (R.val.map (homOfLE le_top).op
    (Φ.hom.val.app (op ⊤) (tensorSection P Q ⊤ s t))) = _
  rw [← hn, tensorSection_restrict, nativeMatchingBundleFrameIso_coefficients]
  exact LocalBundleFrame.tensor_coefficients _ _ _ _ _

variable [IsIntegral X]

/-- The function-field coefficient of a product is the product of the function-field
coefficients. -/
theorem globalSectionToFunctionField_coverProduct (i : ι) [Nonempty (U i)]
    (s : bundleSections P ⊤) (t : bundleSections Q ⊤) :
    globalSectionToFunctionField (r i) (coverProduct U hc p q r hu s t) =
      globalSectionToFunctionField (p i) s * globalSectionToFunctionField (q i) t := by
  change X.germToFunctionField (U i) ((r i).coefficients (𝟙 _)
      (R.val.map (homOfLE le_top).op (coverProduct U hc p q r hu s t))) =
    X.germToFunctionField (U i) ((p i).coefficients (𝟙 _) (P.val.map (homOfLE le_top).op s)) *
      X.germToFunctionField (U i) ((q i).coefficients (𝟙 _) (Q.val.map (homOfLE le_top).op t))
  rw [← map_mul, coverProduct_coefficients]

end CoverProduct

section Values

variable {X : Scheme.{0}} [IsIntegral X] {P Q R : X.Modules} {ι : Type} (U : ι → X.Opens)
  (hc : ∀ x : X, ∃ i, x ∈ U i) (p : ∀ i, LocalBundleFrame P (U i))
  (q : ∀ i, LocalBundleFrame Q (U i)) (r : ∀ i, LocalBundleFrame R (U i))
  (hu : ∀ i j (W : X.Opens) (h : W ⟶ U i) (k : W ⟶ U j),
    localBundleFrameTransition ((p i).tensor (q i)) ((p j).tensor (q j)) h k =
      localBundleFrameTransition (r i) (r j) h k)
  {n : ℕ} (v : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ)))) {c : X}

/-- **Products add values**: `ν(s t) = ν(s) + ν(t)`, for all atlases of `P, Q, R`. -/
theorem plainSectionValue_coverProduct (hcv : IsNonnegAt v c) (bP : LineBundleAtlas P)
    (bQ : LineBundleAtlas Q) (bR : LineBundleAtlas R) (s : bundleSections P ⊤)
    (t : bundleSections Q ⊤) :
    plainSectionValue v c bR (coverProduct U hc p q r hu s t) =
      plainSectionValue v c bP s + plainSectionValue v c bQ t := by
  obtain ⟨i, hi⟩ := hc c
  have : Nonempty (U i) := ⟨⟨c, hi⟩⟩
  rw [plainSectionValue_eq_frame hcv bR (r i) hi, plainSectionValue_eq_frame hcv bP (p i) hi,
    plainSectionValue_eq_frame hcv bQ (q i) hi, globalSectionToFunctionField_coverProduct,
    v.map_mul]

/-- Products of nonzero sections are nonzero, and their value vectors add. -/
theorem plainSectionVector_coverProduct (hcv : IsNonnegAt v c) (bP : LineBundleAtlas P)
    (bQ : LineBundleAtlas Q) (bR : LineBundleAtlas R) {s : bundleSections P ⊤}
    {t : bundleSections Q ⊤} (hs : s ≠ 0) (ht : t ≠ 0) :
    ∃ hst : coverProduct U hc p q r hu s t ≠ 0,
      plainSectionVector v c bR _ hst = plainSectionVector v c bP s hs +
        plainSectionVector v c bQ t ht := by
  have hv := plainSectionValue_coverProduct U hc p q r hu v hcv bP bQ bR s t
  have hst : coverProduct U hc p q r hu s t ≠ 0 := by
    intro h0
    rw [h0, (plainSectionValue_eq_top_iff c bR 0).mpr rfl] at hv
    exact WithTop.add_ne_top.mpr ⟨(plainSectionValue_eq_top_iff c bP s).not.mpr hs,
      (plainSectionValue_eq_top_iff c bQ t).not.mpr ht⟩ hv.symm
  refine ⟨hst, ?_⟩
  rw [plainSectionValue_eq_vector c bR _ hst, plainSectionValue_eq_vector c bP s hs,
    plainSectionValue_eq_vector c bQ t ht, ← WithTop.coe_add, ← toLex_add] at hv
  exact toLex.injective (WithTop.coe_injective hv)

end Values

/-! ### The two products of the proof of `prop:Deltaconvtwisted` -/

section Twist

variable {X : Scheme.{0}} [IsIntegral X] {L T : X.Modules} (a : LineBundleAtlas L)
  (aT : LineBundleAtlas T)

/-- The common cover `U_i ∩ V_j` of atlases of `L` and `T`. -/
abbrev twistCover : a.I × aT.I → X.Opens := fun ij => a.opens ij.1 ⊓ aT.opens ij.2

theorem twistCover_covers : ∀ x : X, ∃ ij, x ∈ twistCover a aT ij := fun x => by
  obtain ⟨i, hi⟩ := a.covers x
  obtain ⟨j, hj⟩ := aT.covers x
  exact ⟨(i, j), hi, hj⟩

/-- Matching transitions for `L^j ⊗ (T ⊗ L^{k₁}) ≅ T ⊗ L^{j + k₁}`. -/
theorem lower_transitions (j k₁ : ℕ) :
    ∀ i i' (W : X.Opens) (h : W ⟶ twistCover a aT i) (k : W ⟶ twistCover a aT i'),
      localBundleFrameTransition
          (((leftRestrictedFrame a aT i).tensorPower j).tensor
            ((rightRestrictedFrame a aT i).tensor ((leftRestrictedFrame a aT i).tensorPower k₁)))
          (((leftRestrictedFrame a aT i').tensorPower j).tensor
            ((rightRestrictedFrame a aT i').tensor ((leftRestrictedFrame a aT i').tensorPower k₁)))
          h k =
        localBundleFrameTransition
          ((rightRestrictedFrame a aT i).tensor ((leftRestrictedFrame a aT i).tensorPower (j + k₁)))
          ((rightRestrictedFrame a aT i').tensor
            ((leftRestrictedFrame a aT i').tensorPower (j + k₁))) h k := by
  intro i i' W h k
  simp only [localBundleFrameTransition_tensor, localBundleFrameTransition_tensorPower, pow_add]
  exact mul_left_comm _ _ _

/-- The product `H⁰(X, L^j) × H⁰(X, T ⊗ L^{k₁}) → H⁰(X, T ⊗ L^{j + k₁})`. -/
def lowerProduct (j k₁ : ℕ) (t : bundlePowerGlobalSections L j)
    (s : bundleSections (bundleTensor T (bundleTensorPower L k₁)) ⊤) :
    bundleSections (bundleTensor T (bundleTensorPower L (j + k₁))) ⊤ :=
  coverProduct (twistCover a aT) (twistCover_covers a aT)
    (fun i => (leftRestrictedFrame a aT i).tensorPower j)
    (fun i => (rightRestrictedFrame a aT i).tensor ((leftRestrictedFrame a aT i).tensorPower k₁))
    (fun i => (rightRestrictedFrame a aT i).tensor
      ((leftRestrictedFrame a aT i).tensorPower (j + k₁)))
    (lower_transitions a aT j k₁) t s

/-- Matching transitions for `(T ⊗ L^k) ⊗ (T^∨ ⊗ L^{k₀}) ≅ L^{k + k₀}`. -/
theorem upper_transitions (k k₀ : ℕ) :
    ∀ i i' (W : X.Opens) (h : W ⟶ twistCover a aT i) (l : W ⟶ twistCover a aT i'),
      localBundleFrameTransition
          (((rightRestrictedFrame a aT i).tensor ((leftRestrictedFrame a aT i).tensorPower k)).tensor
            ((rightRestrictedFrame a aT i).dual.tensor
              ((leftRestrictedFrame a aT i).tensorPower k₀)))
          (((rightRestrictedFrame a aT i').tensor
              ((leftRestrictedFrame a aT i').tensorPower k)).tensor
            ((rightRestrictedFrame a aT i').dual.tensor
              ((leftRestrictedFrame a aT i').tensorPower k₀))) h l =
        localBundleFrameTransition ((leftRestrictedFrame a aT i).tensorPower (k + k₀))
          ((leftRestrictedFrame a aT i').tensorPower (k + k₀)) h l := by
  intro i i' W h l
  simp only [localBundleFrameTransition_tensor, localBundleFrameTransition_tensorPower,
    localBundleFrameTransition_dual, pow_add]
  rw [mul_mul_mul_comm, mul_inv_cancel, one_mul]

/-- The product `H⁰(X, T ⊗ L^k) × H⁰(X, T^∨ ⊗ L^{k₀}) → H⁰(X, L^{k + k₀})`. -/
def upperProduct (k k₀ : ℕ) (s : bundleSections (bundleTensor T (bundleTensorPower L k)) ⊤)
    (t : bundleSections (bundleTensor (bundleDual T) (bundleTensorPower L k₀)) ⊤) :
    bundlePowerGlobalSections L (k + k₀) :=
  coverProduct (twistCover a aT) (twistCover_covers a aT)
    (fun i => (rightRestrictedFrame a aT i).tensor ((leftRestrictedFrame a aT i).tensorPower k))
    (fun i => (rightRestrictedFrame a aT i).dual.tensor
      ((leftRestrictedFrame a aT i).tensorPower k₀))
    (fun i => (leftRestrictedFrame a aT i).tensorPower (k + k₀))
    (upper_transitions a aT k k₀) s t

variable {n : ℕ} (v : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ)))) {c : X}

/-- The value of a section of `L^k` is its value as a section of the line bundle `L^k`. -/
theorem sectionValue_eq_plainSectionValue (hcv : IsNonnegAt v c) (k : ℕ)
    (s : bundlePowerGlobalSections L k) :
    sectionValue v c a k s = plainSectionValue v c (a.tensorPower k) s := by
  have : Nonempty (a.opens (a.centerIndex c)) := ⟨⟨c, a.centerIndex_mem c⟩⟩
  rw [plainSectionValue_eq_frame hcv (a.tensorPower k) ((a.frame (a.centerIndex c)).tensorPower k)
    (a.centerIndex_mem c)]
  rfl

/-- **The lower product shifts values**: for nonzero `t ∈ H⁰(L^j)` and `s ∈ H⁰(T ⊗ L^{k₁})`,
`t s ≠ 0` and `ν(t s) = ν(t) + ν(s)`, for all atlases `b, b'` of `T ⊗ L^{k₁}`, `T ⊗ L^{j+k₁}`. -/
theorem lowerProduct_vector (hcv : IsNonnegAt v c) (j k₁ : ℕ)
    (b : LineBundleAtlas (bundleTensor T (bundleTensorPower L k₁)))
    (b' : LineBundleAtlas (bundleTensor T (bundleTensorPower L (j + k₁))))
    {t : bundlePowerGlobalSections L j} (ht : t ≠ 0)
    {s : bundleSections (bundleTensor T (bundleTensorPower L k₁)) ⊤} (hs : s ≠ 0) :
    ∃ hts : lowerProduct a aT j k₁ t s ≠ 0,
      plainSectionVector v c b' _ hts = sectionVector v c a j t ht + plainSectionVector v c b s hs := by
  obtain ⟨hts, h⟩ := plainSectionVector_coverProduct (twistCover a aT) (twistCover_covers a aT)
    _ _ _ (lower_transitions a aT j k₁) v hcv (a.tensorPower j) b b' ht hs
  exact ⟨hts, h.trans rfl⟩

/-- **The upper product shifts values**: for nonzero `s ∈ H⁰(T ⊗ L^k)` and
`t ∈ H⁰(T^∨ ⊗ L^{k₀})`, `s t ≠ 0` and `ν(s t) = ν(s) + ν(t)`. -/
theorem upperProduct_vector (hcv : IsNonnegAt v c) (k k₀ : ℕ)
    (b : LineBundleAtlas (bundleTensor T (bundleTensorPower L k)))
    (b' : LineBundleAtlas (bundleTensor (bundleDual T) (bundleTensorPower L k₀)))
    {s : bundleSections (bundleTensor T (bundleTensorPower L k)) ⊤} (hs : s ≠ 0)
    {t : bundleSections (bundleTensor (bundleDual T) (bundleTensorPower L k₀)) ⊤} (ht : t ≠ 0) :
    ∃ hst : upperProduct a aT k k₀ s t ≠ 0,
      sectionVector v c a (k + k₀) _ hst = plainSectionVector v c b s hs +
        plainSectionVector v c b' t ht := by
  obtain ⟨hst, h⟩ := plainSectionVector_coverProduct (twistCover a aT) (twistCover_covers a aT)
    _ _ _ (upper_transitions a aT k k₀) v hcv b b' (a.tensorPower (k + k₀)) hs ht
  exact ⟨hst, Eq.trans rfl h⟩

end Twist

end SGPT.Okounkov.ValGen2
