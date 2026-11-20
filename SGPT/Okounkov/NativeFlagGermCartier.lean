import SGPT.Okounkov.NativeFlagGermScalars
import SGPT.Okounkov.NativeFlagGermRange
import SGPT.Okounkov.EffectiveDivisorCurrentCompatibility

/-!
# Actual original native germs and genuine Cartier flag recursion

Literal original ideal generators, the SAME original restriction kernel and
actual Cartier local-section steps link the two genuine recursive constructions.
No vector, order, tail or current comparison certificate is supplied.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov

open Set Filter
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending

/-- Actual native principal membership is the literal original one-generator
holomorphic span, retaining the actual function representatives. -/
theorem NativeHolGerm.mem_span_singleton_mk_iff {n : ℕ} {M : Type u}
    [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] {x : M}
    (f h : M → ℂ) (hf : HolomorphicAt n f x) (hh : HolomorphicAt n h x) :
    NativeHolGerm.mk f hf ∈ Ideal.span {NativeHolGerm.mk h hh} ↔
      IsInSpanAt (n := n) (· = h) x f := by
  rw [Ideal.mem_span_singleton, isInSpanAt_eq_iff]
  constructor
  · rintro ⟨q, hq⟩
    obtain ⟨c, hc, rfl⟩ := NativeHolGerm.exists_eq_mk q
    refine ⟨hf, c, hc, ?_⟩
    have heq : NativeHolGerm.mk f hf = NativeHolGerm.mk
        (fun y => c y * h y) (hc.mul hh) := by
      change NativeHolGerm.mk f hf = NativeHolGerm.mk c hc * NativeHolGerm.mk h hh
      exact hq.trans (mul_comm _ _)
    exact NativeHolGerm.mk_eq_mk_iff.mp heq
  · rintro ⟨_, c, hc, heq⟩
    refine ⟨NativeHolGerm.mk c hc, ?_⟩
    apply Subtype.ext
    apply Germ.coe_eq.mpr
    filter_upwards [heq] with y hy
    simpa only [mul_comm] using hy

/-- Genuine equality of actual native principal ideals gives equality of the
WHOLE original vector by actual unit association and the full unit-zero theorem. -/
theorem originalFlagGermVector_eq_of_span_eq {n : ℕ} (F : OriginalFlagGeometry.{u} n)
    (x : OriginalFlagGermPoint F) (f g : NativeHolGerm n F.carrier x.1)
    (hf : f ≠ 0) (hg : g ≠ 0) (hspan : Ideal.span {f} = Ideal.span {g}) :
    originalFlagGermVector F x f hf = originalFlagGermVector F x g hg := by
  obtain ⟨v, hv⟩ := Ideal.span_singleton_eq_span_singleton.mp hspan
  subst g
  have hp := originalFlagGermVector_mul F x f v hf v.ne_zero
  rw [originalFlagGermVector_eq_zero_of_isUnit F x v v.ne_zero v.isUnit, add_zero] at hp
  exact hp.symm

private theorem vector_congr {n : ℕ} (F : OriginalFlagGeometry.{u} n)
    (x : OriginalFlagGermPoint F) (f g : NativeHolGerm n F.carrier x.1)
    (hf : f ≠ 0) (hg : g ≠ 0) (h : f = g) :
    originalFlagGermVector F x f hf = originalFlagGermVector F x g hg := by
  subst g
  rfl

/-- The actual whole-vector power law is repeated genuine multiplication. -/
theorem originalFlagGermVector_pow {n : ℕ} (F : OriginalFlagGeometry.{u} n)
    (x : OriginalFlagGermPoint F) (f : NativeHolGerm n F.carrier x.1)
    (hf : f ≠ 0) (a : ℕ) :
    originalFlagGermVector F x (f ^ a) (pow_ne_zero a hf) =
      a • originalFlagGermVector F x f hf := by
  induction a with
  | zero =>
    rw [zero_nsmul]
    exact (vector_congr F x (f ^ 0) 1 (pow_ne_zero 0 hf) one_ne_zero (pow_zero f)).trans
      (originalFlagGermVector_one F x)
  | succ a ih =>
    calc
      _ = originalFlagGermVector F x (f ^ a * f) (mul_ne_zero (pow_ne_zero a hf) hf) :=
        vector_congr F x _ _ _ _ (pow_succ f a)
      _ = originalFlagGermVector F x (f ^ a) (pow_ne_zero a hf) + originalFlagGermVector F x f hf :=
        originalFlagGermVector_mul F x (f ^ a) f (pow_ne_zero a hf) hf
      _ = _ := by rw [ih, succ_nsmul]

/-- Literal original tail restriction is zero exactly when the original
function vanishes on the SAME first flag member near the actual point. -/
theorem originalFirstFlagGermRestriction_mk_eq_zero_iff {m : ℕ}
    (F : OriginalFlagGeometry.{u} (m + 1)) (x : F.tail.carrier)
    (f : F.carrier → ℂ) (hf : HolomorphicAt (m + 1) f x.1) :
    originalFirstFlagGermRestriction F x (NativeHolGerm.mk f hf) = 0 ↔
      (vanishingIdeal (n := m + 1) (F.flag (1 : Fin (m + 2)))).mem x.1 f := by
  have hres : originalFirstFlagGermRestriction F x (NativeHolGerm.mk f hf) = 0 ↔
      (f ∘ (Subtype.val : F.tail.carrier → F.carrier)) =ᶠ[𝓝 x] 0 := by
    rw [Subtype.ext_iff]
    change ((fun y : F.tail.carrier => f y.1) : Germ (𝓝 x) ℂ) =
      ((0 : F.tail.carrier → ℂ) : Germ (𝓝 x) ℂ) ↔ _
    exact Germ.coe_eq
  rw [hres]
  constructor
  · intro hzero
    obtain ⟨V, hV, hsub⟩ := (mem_nhds_subtype (F.flag (1 : Fin (m + 2))) x _).mp hzero
    refine ⟨hf, ?_⟩
    filter_upwards [hV] with y hy
    intro hyF
    exact hsub (show (⟨y, hyF⟩ : F.tail.carrier) ∈ Subtype.val ⁻¹' V from hy)
  · intro hmem
    filter_upwards [continuous_subtype_val.continuousAt.eventually hmem.2] with y hy
    exact hy y.property

private theorem restriction_ker_eq_span_mk {m : ℕ}
    (F : OriginalFlagGeometry.{u} (m + 1)) (x : F.tail.carrier)
    (t : F.carrier → ℂ) (ht : HolomorphicAt (m + 1) t x.1)
    (hgen : ∀ f, (vanishingIdeal (n := m + 1) (F.flag (1 : Fin (m + 2)))).mem x.1 f ↔
      IsInSpanAt (n := m + 1) (· = t) x.1 f) :
    RingHom.ker (originalFirstFlagGermRestriction F x) = Ideal.span {NativeHolGerm.mk t ht} := by
  ext g
  obtain ⟨f, hf, rfl⟩ := NativeHolGerm.exists_eq_mk g
  rw [RingHom.mem_ker, originalFirstFlagGermRestriction_mk_eq_zero_iff, hgen]
  exact (NativeHolGerm.mem_span_singleton_mk_iff f t hf ht).symm

/-- A genuine nonzero LITERAL tail restriction makes the actual full vector
exactly zero followed by its SAME original-tail vector. -/
theorem originalFlagGermVector_cons_zero_of_restriction_ne_zero {m : ℕ}
    (F : OriginalFlagGeometry.{u} (m + 1)) (x : OriginalFlagGermPoint F)
    (f : NativeHolGerm (m + 1) F.carrier x.1) (hf : f ≠ 0)
    (hres : originalFirstFlagGermRestriction F (OriginalFlagGermPoint.first F x) f ≠ 0) :
    originalFlagGermVector F x f hf = Fin.cons 0
      (originalFlagGermVector F.tail (OriginalFlagGermPoint.tail F x)
        (originalFirstFlagGermRestriction F (OriginalFlagGermPoint.first F x) f) hres) := by
  let y := OriginalFlagGermPoint.first F x
  have hval := (originalFirstFlagGermOrder_eq_zero_iff F y f).mpr hres
  have ha : originalFirstFlagGermOrderNat F y f = 0 :=
    ENat.natCast_inj.mp ((originalFirstFlagGermOrderNat_spec F y f hf).symm.trans hval)
  have hq : originalFirstFlagGermQuotient F y f hf = f := by
    apply originalFirstFlagGermQuotient_unique
    rw [ha, pow_zero]
    exact (one_mul f).symm
  have hr : originalFirstFlagGermResidual F y f hf = originalFirstFlagGermRestriction F y f := by
    change originalFirstFlagGermRestriction F y (originalFirstFlagGermQuotient F y f hf) = _
    rw [hq]
  funext i
  refine Fin.cases ha (fun j => ?_) i
  change originalFlagGermVector F.tail (OriginalFlagGermPoint.tail F x)
    (originalFirstFlagGermResidual F y f hf) (originalFirstFlagGermResidual_ne_zero F y f hf) j =
      originalFlagGermVector F.tail (OriginalFlagGermPoint.tail F x) (originalFirstFlagGermRestriction F y f) hres j
  exact congrFun (vector_congr F.tail (OriginalFlagGermPoint.tail F x) _ _ _ _ hr) j

private theorem span_eq_of_original_generators {n : ℕ} {M : Type u}
    [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] (I : GermIdeal n M) (x : M)
    (g : NativeHolGerm n M x) (s : M → ℂ) (hs : HolomorphicAt n s x)
    (hg : ∀ h, I.mem x h ↔ ∃ hh : HolomorphicAt n h x,
      NativeHolGerm.mk h hh ∈ Ideal.span {g})
    (hsg : ∀ h, I.mem x h ↔ IsInSpanAt (n := n) (· = s) x h) :
    Ideal.span {g} = Ideal.span {NativeHolGerm.mk s hs} := by
  ext v
  obtain ⟨h, hh, rfl⟩ := NativeHolGerm.exists_eq_mk v
  have hleft : NativeHolGerm.mk h hh ∈ Ideal.span {g} ↔ I.mem x h := by
    constructor
    · intro hv
      exact (hg h).mpr ⟨hh, hv⟩
    · intro hv
      obtain ⟨_, hm⟩ := (hg h).mp hv
      exact hm
  exact hleft.trans ((hsg h).trans (NativeHolGerm.mem_span_singleton_mk_iff h s hh hs).symm)

private theorem restriction_mk_ne_zero_of_relative_nonzero {m : ℕ}
    (F : OriginalFlagGeometry.{u} (m + 1)) (x : F.tail.carrier)
    (U : Set F.carrier) (hU : IsOpen U) (hxU : x.1 ∈ U)
    (r : F.carrier → ℂ) (hr : HolomorphicAt (m + 1) r x.1)
    (hn : ∀ V : Set F.carrier, IsOpen V → V ⊆ U →
      (V ∩ F.flag (1 : Fin (m + 2))).Nonempty →
        ∃ y ∈ V ∩ F.flag (1 : Fin (m + 2)), r y ≠ 0) :
    originalFirstFlagGermRestriction F x (NativeHolGerm.mk r hr) ≠ 0 := by
  intro hz
  have hzero : (r ∘ (Subtype.val : F.tail.carrier → F.carrier)) =ᶠ[𝓝 x] 0 := by
    apply Germ.coe_eq.mp
    exact congrArg Subtype.val hz
  obtain ⟨V, hV, hsub⟩ := (mem_nhds_subtype (F.flag (1 : Fin (m + 2))) x _).mp hzero
  obtain ⟨W, hWsub, hWopen, hxW⟩ := mem_nhds_iff.mp (inter_mem hV (hU.mem_nhds hxU))
  obtain ⟨y, hy, hyne⟩ := hn W hWopen (fun y hy => (hWsub hy).2) ⟨x.1, hxW, x.property⟩
  exact hyne (hsub (show (⟨y, hy.2⟩ : F.tail.carrier) ∈ Subtype.val ⁻¹' V from (hWsub hy.1).1))

private theorem cartier_step_native_vector {m : ℕ}
    (F : OriginalFlagGeometry.{u} (m + 1)) (x : OriginalFlagGermPoint F)
    (D : EffectiveDivisor (m + 1) F.carrier) (a : ℕ)
    (Dtail : EffectiveDivisor m F.tail.carrier) (hstep : OriginalCartierFlagStep F D a Dtail)
    (g : NativeHolGerm (m + 1) F.carrier x.1) (hg : g ≠ 0)
    (hgen : ∀ f, D.ideal.mem x.1 f ↔ ∃ hf : HolomorphicAt (m + 1) f x.1,
      NativeHolGerm.mk f hf ∈ Ideal.span {g}) :
    ∃ (r : NativeHolGerm m F.tail.carrier (OriginalFlagGermPoint.tail F x).1) (hr : r ≠ 0),
      (∀ f, Dtail.ideal.mem (OriginalFlagGermPoint.tail F x).1 f ↔
        ∃ hf : HolomorphicAt m f (OriginalFlagGermPoint.tail F x).1,
          NativeHolGerm.mk f hf ∈ Ideal.span {r}) ∧
      originalFlagGermVector F x g hg =
        Fin.cons a (originalFlagGermVector F.tail (OriginalFlagGermPoint.tail F x) r hr) := by
  let : ChartedSpace (ComplexModel m) (F.flag (1 : Fin (m + 2))) := F.tail.charts
  let : IsComplexManifold m (F.flag (1 : Fin (m + 2))) := F.tail.complex
  let y := OriginalFlagGermPoint.first F x
  obtain ⟨U, t, r, s, hU, hxU, htU, hrU, htgen, _htzero, hsgen, hseq, _hdiv, htailgen, hrnv⟩ :=
    originalCartierSectionStep_of_ideal_step F D a Dtail hstep x.1 y.property
  have ht : HolomorphicAt (m + 1) t x.1 :=
    InvertibleIdealQuotient.holomorphicAt_of_mdifferentiableOn hU htU hxU
  have hr : HolomorphicAt (m + 1) r x.1 :=
    InvertibleIdealQuotient.holomorphicAt_of_mdifferentiableOn hU hrU hxU
  have hs : HolomorphicAt (m + 1) s x.1 := by
    apply ((BlowupDerivativeIdeal.holomorphicAt_pow ht a).mul hr).congr
    filter_upwards [hU.mem_nhds hxU] with z hz
    exact (hseq z hz).symm
  let gt := NativeHolGerm.mk t ht
  let gr := NativeHolGerm.mk r hr
  let gs := NativeHolGerm.mk s hs
  let rt := originalFirstFlagGermRestriction F y gr
  have hrt : rt ≠ 0 := restriction_mk_ne_zero_of_relative_nonzero F y U hU hxU r hr hrnv
  have hgr : gr ≠ 0 := by
    intro hz
    exact hrt ((congrArg (originalFirstFlagGermRestriction F y) hz).trans (map_zero _))
  have hgtspan : Ideal.span {gt} = Ideal.span {originalFirstFlagGermParameter F y} :=
    (restriction_ker_eq_span_mk F y t ht (htgen x.1 hxU)).symm.trans
      (originalFirstFlagGermParameter_spec F y).2.2
  have hgt : gt ≠ 0 := (Ideal.span_singleton_eq_span_singleton.mp hgtspan).ne_zero_iff.mpr
    (originalFirstFlagGermParameter_spec F y).1.ne_zero
  have hgspan : Ideal.span {g} = Ideal.span {gs} :=
    span_eq_of_original_generators D.ideal x.1 g s hs hgen (hsgen x.1 hxU)
  have hgs : gs ≠ 0 := (Ideal.span_singleton_eq_span_singleton.mp hgspan).ne_zero_iff.mp hg
  have hprod : gs = gt ^ a * gr := by
    apply Subtype.ext
    apply Germ.coe_eq.mpr
    filter_upwards [hU.mem_nhds hxU] with z hz
    exact hseq z hz
  have hgtvec : originalFlagGermVector F x gt hgt = Fin.cons 1 0 :=
    (originalFlagGermVector_eq_of_span_eq F x gt _ hgt
      (originalFirstFlagGermParameter_spec F y).1.ne_zero hgtspan).trans
        (originalFlagGermVector_parameter F x)
  have hgrvec : originalFlagGermVector F x gr hgr =
      Fin.cons 0 (originalFlagGermVector F.tail (OriginalFlagGermPoint.tail F x) rt hrt) :=
    originalFlagGermVector_cons_zero_of_restriction_ne_zero F x gr hgr hrt
  have hrtHol : HolomorphicAt m (fun z : F.tail.carrier => r z.1) y := by
    obtain ⟨R, hR, hReq⟩ := NativeHolGerm.exists_eq_mk rt
    apply hR.congr
    apply Germ.coe_eq.mp
    exact (congrArg Subtype.val hReq).symm
  have hrtmk : rt = NativeHolGerm.mk (fun z : F.tail.carrier => r z.1) hrtHol := by
    apply Subtype.ext
    rfl
  refine ⟨rt, hrt, ?_, ?_⟩
  · intro f
    change Dtail.ideal.mem y f ↔ ∃ hf : HolomorphicAt m f y, NativeHolGerm.mk f hf ∈ Ideal.span {rt}
    rw [htailgen y hxU f, hrtmk]
    constructor
    · intro hf
      exact ⟨hf.holomorphicAt, (NativeHolGerm.mem_span_singleton_mk_iff _ _ hf.holomorphicAt hrtHol).mpr hf⟩
    · rintro ⟨hf, hmem⟩
      exact (NativeHolGerm.mem_span_singleton_mk_iff _ _ hf hrtHol).mp hmem
  · calc
      originalFlagGermVector F x g hg = originalFlagGermVector F x gs hgs :=
        originalFlagGermVector_eq_of_span_eq F x g gs hg hgs hgspan
      _ = originalFlagGermVector F x (gt ^ a * gr) (mul_ne_zero (pow_ne_zero a hgt) hgr) :=
        vector_congr F x _ _ _ _ hprod
      _ = originalFlagGermVector F x (gt ^ a) (pow_ne_zero a hgt) + originalFlagGermVector F x gr hgr :=
        originalFlagGermVector_mul F x _ _ _ _
      _ = a • originalFlagGermVector F x gt hgt + originalFlagGermVector F x gr hgr := by
        rw [originalFlagGermVector_pow]
      _ = _ := by
        rw [hgtvec, hgrvec]
        funext i
        refine Fin.cases ?_ (fun j => ?_) i <;> simp

/-- Genuine actual local generators give the ENTIRE independent original
Cartier recursion. The SAME original-tail generator is manufactured at each step. -/
theorem originalCartierFlagValuation_of_native_generator :
    ∀ (n : ℕ) (F : OriginalFlagGeometry.{u} n) (x : OriginalFlagGermPoint F)
      (D : EffectiveDivisor n F.carrier) (g : NativeHolGerm n F.carrier x.1) (hg : g ≠ 0),
      (∀ f, D.ideal.mem x.1 f ↔ ∃ hf : HolomorphicAt n f x.1,
        NativeHolGerm.mk f hf ∈ Ideal.span {g}) →
      OriginalCartierFlagValuation n F D (originalFlagGermVector F x g hg) := by
  intro n
  induction n with
  | zero =>
    intro F x D g hg hgen
    trivial
  | succ m ih =>
    intro F x D g hg hgen
    obtain ⟨a, Dtail, hstep⟩ := exists_originalCartierFlagStep F D
    obtain ⟨r, hr, hrtgen, hvec⟩ := cartier_step_native_vector F x D a Dtail hstep g hg hgen
    rw [hvec]
    exact ⟨Dtail, hstep, ih F.tail (OriginalFlagGermPoint.tail F x) Dtail r hr hrtgen⟩

/-- The COMPLETE actual effective-divisor current has the SAME whole native
local-generator tuple, by genuine Cartier recursion and its proved uniqueness. -/
theorem currentFlagValuation_effectiveDivisor_eq_native_vector {m : ℕ}
    (F : OriginalFlagGeometry.{u} (m + 1)) (x : OriginalFlagGermPoint F)
    (D : EffectiveDivisor (m + 1) F.carrier)
    (g : NativeHolGerm (m + 1) F.carrier x.1) (hg : g ≠ 0)
    (hgen : ∀ f, D.ideal.mem x.1 f ↔ ∃ hf : HolomorphicAt (m + 1) f x.1,
      NativeHolGerm.mk f hf ∈ Ideal.span {g}) :
    currentFlagValuation F (effectiveDivisorIntegrationCurrent F D)
      (effectiveDivisorIntegrationCurrent_closed_type_positive F D).1
      (effectiveDivisorIntegrationCurrent_closed_type_positive F D).2.1
      (effectiveDivisorIntegrationCurrent_closed_type_positive F D).2.2 =
        (fun i => (originalFlagGermVector F x g hg i : NNReal)) := by
  obtain ⟨ν, hν, hcurrent⟩ := exists_currentFlagValuation_effectiveDivisor_eq_integer_vector F D
  have hnative := originalCartierFlagValuation_of_native_generator (m + 1) F x D g hg hgen
  have hνeq := originalCartierFlagValuation_unique F D hν hnative
  exact hcurrent.trans (congrArg (fun v : Fin (m + 1) → ℕ => fun i => (v i : NNReal)) hνeq)

end SGPT.Okounkov
