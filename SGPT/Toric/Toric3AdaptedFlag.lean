import SGPT.Okounkov.NativeFlagGermValuation
import SGPT.Okounkov.NativeFlagGermResidue
import SGPT.Foundations.Analysis.Pending.HolomorphicGermAlgebra

/-!
# Flag valuations in coordinates adapted to a smooth flag

Source `chapter_Okounkov.tex`, Section *Flags and valuations*: the valuation `ν_{Y•}` of a
holomorphic germ along a smooth flag `Y•` is computed by successive orders of vanishing along
`Y_i ⊆ Y_{i-1}` and restrictions (`originalFlagGermVector`).  In the proof of
`prop:toricusualOko` the source uses that, in local coordinates `z_1, …, z_n` adapted to the
flag (`Y_i = {z_1 = ⋯ = z_i = 0}` near the point `Y_n`), the coordinate `z_j` has valuation the
`j`-th unit vector, so a monomial `z^α` has valuation `α`.

This file proves that statement for an arbitrary smooth flag of an `OriginalFlagGeometry`:

* `IsAdaptedFlagCoordinates F x G`: the holomorphic functions `G_0, …, G_{n-1}` near the flag
  point `x` are adapted to the flag: `G_k` vanishes on `Y_{k+1}` near `x`, and every
  holomorphic function vanishing on `Y_{i+1}` near `x` is, near `x`, a holomorphic combination
  of `G_0, …, G_i`;
* `originalFlagGermVector_adapted`: then `ν_{Y•}(G_j) = e_j`;
* `originalFlagGermVector_prod_pow_adapted`: `ν_{Y•}(∏_j G_j^{α_j}) = α`.
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

/-- The recursive algebraic form of adaptedness: the first germ generates the kernel of the
restriction to `Y_1`, and the restrictions of the remaining germs are adapted to the tail flag. -/
def IsAdaptedFlagGermFamily : {n : ℕ} → (F : OriginalFlagGeometry.{u} n) →
    (x : OriginalFlagGermPoint F) → (Fin n → NativeHolGerm n F.carrier x.1) → Prop
  | 0, _, _, _ => True
  | _m + 1, F, x, g =>
    RingHom.ker (originalFirstFlagGermRestriction F (OriginalFlagGermPoint.first F x)) =
        Ideal.span {g 0} ∧
      IsAdaptedFlagGermFamily F.tail (OriginalFlagGermPoint.tail F x)
        (fun j => originalFirstFlagGermRestriction F (OriginalFlagGermPoint.first F x)
          (g j.succ))

private theorem vector_congr' {n : ℕ} (F : OriginalFlagGeometry.{u} n)
    (x : OriginalFlagGermPoint F) (f g : NativeHolGerm n F.carrier x.1)
    (hf : f ≠ 0) (hg : g ≠ 0) (heq : f = g) :
    originalFlagGermVector F x f hf = originalFlagGermVector F x g hg := by
  subst g
  rfl

/-- Units have flag valuation `0`. -/
theorem originalFlagGermVector_of_isUnit {n : ℕ} (F : OriginalFlagGeometry.{u} n)
    (x : OriginalFlagGermPoint F) (w : NativeHolGerm n F.carrier x.1) (hw : IsUnit w) :
    originalFlagGermVector F x w hw.ne_zero = 0 := by
  obtain ⟨w', hw'⟩ := hw.exists_right_inv
  have hw'0 : w' ≠ 0 := by
    rintro rfl
    simp at hw'
  have h := originalFlagGermVector_mul F x w w' hw.ne_zero hw'0
  rw [vector_congr' F x (w * w') 1 (mul_ne_zero hw.ne_zero hw'0) one_ne_zero hw',
    originalFlagGermVector_one] at h
  funext i
  have hi := congrFun h i
  simp only [Pi.zero_apply, Pi.add_apply] at hi ⊢
  omega

/-- Source `prop:toricusualOko` (proof, the computation in adapted coordinates): for a germ
family adapted to the flag, `ν_{Y•}(g_j) = e_j`. -/
theorem originalFlagGermVector_adapted : ∀ {n : ℕ} (F : OriginalFlagGeometry.{u} n)
    (x : OriginalFlagGermPoint F) (g : Fin n → NativeHolGerm n F.carrier x.1),
    IsAdaptedFlagGermFamily F x g → ∀ j, ∃ hj : g j ≠ 0,
      originalFlagGermVector F x (g j) hj = Pi.single j 1
  | 0, _, _, _, _, j => Fin.elim0 j
  | m + 1, F, x, g, hg, j => by
    obtain ⟨hker, htail⟩ := hg
    let R := NativeHolGerm (m + 1) F.carrier x.1
    let y := OriginalFlagGermPoint.first F x
    let t : R := originalFirstFlagGermParameter F y
    have ht : Prime t ∧ RingHom.ker (originalFirstFlagGermRestriction F y) = Ideal.span {t} :=
      ⟨(originalFirstFlagGermParameter_spec F y).1, (originalFirstFlagGermParameter_spec F y).2.2⟩
    have hspan : Ideal.span {g 0} = Ideal.span {t} := hker.symm.trans ht.2
    have hassoc : Associated t (g 0) :=
      (Ideal.span_singleton_eq_span_singleton.mp hspan).symm
    obtain ⟨u, hu⟩ := hassoc
    have hg0 : g 0 ≠ 0 := by
      rw [← hu]
      exact mul_ne_zero ht.1.ne_zero u.ne_zero
    have htailne := originalFlagGermVector_adapted F.tail (OriginalFlagGermPoint.tail F x) _ htail
    refine Fin.cases ?_ (fun k => ?_) j
    · refine ⟨hg0, ?_⟩
      let u' : R := u
      have hunit : IsUnit (originalFirstFlagGermRestriction F y u') := (u.isUnit).map _
      have hres : originalFirstFlagGermRestriction F y u' ≠ 0 := hunit.ne_zero
      have hord0 := (originalFirstFlagGermOrder_eq_zero_iff F y u').mpr hres
      have htval : originalFirstFlagGermOrder F y (g 0) = (1 : ℕ∞) := by
        rw [← hu]
        refine ((originalFirstFlagGermOrder F y).map_mul t u').trans ?_
        rw [hord0, add_zero]
        change emultiplicity t t = 1
        simpa using emultiplicity_pow_self_of_prime ht.1 1
      have ha : originalFirstFlagGermOrderNat F y (g 0) = 1 :=
        ENat.natCast_inj.mp ((originalFirstFlagGermOrderNat_spec F y (g 0) hg0).symm.trans htval)
      have hq : originalFirstFlagGermQuotient F y (g 0) hg0 = u' := by
        apply originalFirstFlagGermQuotient_unique
        rw [ha, pow_one]
        exact hu.symm
      have hr : originalFirstFlagGermResidual F y (g 0) hg0 =
          originalFirstFlagGermRestriction F y u' := by
        change originalFirstFlagGermRestriction F y (originalFirstFlagGermQuotient F y _ hg0) = _
        rw [hq]
      funext i
      refine Fin.cases ?_ (fun l => ?_) i
      · change originalFirstFlagGermOrderNat F y (g 0) = _
        rw [ha]
        simp
      · change originalFlagGermVector F.tail (OriginalFlagGermPoint.tail F x)
          (originalFirstFlagGermResidual F y (g 0) hg0)
          (originalFirstFlagGermResidual_ne_zero F y (g 0) hg0) l = _
        rw [vector_congr' F.tail (OriginalFlagGermPoint.tail F x) _ _
          (originalFirstFlagGermResidual_ne_zero F y (g 0) hg0) hunit.ne_zero hr,
          originalFlagGermVector_of_isUnit F.tail (OriginalFlagGermPoint.tail F x) _ hunit]
        simp [Fin.succ_ne_zero]
    · obtain ⟨hk, hvk⟩ := htailne k
      have hgk : g k.succ ≠ 0 := by
        intro h0
        apply hk
        change originalFirstFlagGermRestriction F y (g k.succ) = 0
        rw [h0]
        exact map_zero _
      refine ⟨hgk, ?_⟩
      have hord0 := (originalFirstFlagGermOrder_eq_zero_iff F y (g k.succ)).mpr hk
      have ha : originalFirstFlagGermOrderNat F y (g k.succ) = 0 :=
        ENat.natCast_inj.mp ((originalFirstFlagGermOrderNat_spec F y _ hgk).symm.trans hord0)
      have hq : originalFirstFlagGermQuotient F y (g k.succ) hgk = g k.succ := by
        apply originalFirstFlagGermQuotient_unique
        rw [ha, pow_zero]
        exact (one_mul _).symm
      have hr : originalFirstFlagGermResidual F y (g k.succ) hgk =
          originalFirstFlagGermRestriction F y (g k.succ) := by
        change originalFirstFlagGermRestriction F y (originalFirstFlagGermQuotient F y _ hgk) = _
        rw [hq]
      funext i
      refine Fin.cases ?_ (fun l => ?_) i
      · change originalFirstFlagGermOrderNat F y (g k.succ) = _
        rw [ha]
        simp [(Fin.succ_ne_zero k).symm]
      · change originalFlagGermVector F.tail (OriginalFlagGermPoint.tail F x)
          (originalFirstFlagGermResidual F y (g k.succ) hgk)
          (originalFirstFlagGermResidual_ne_zero F y (g k.succ) hgk) l = _
        rw [vector_congr' F.tail (OriginalFlagGermPoint.tail F x) _ _
          (originalFirstFlagGermResidual_ne_zero F y (g k.succ) hgk) hk hr]
        have := congrFun hvk l
        rw [this]
        simp [Pi.single_apply, Fin.succ_inj]

/-- The flag vector of a power. -/
theorem originalFlagGermVector_pow {n : ℕ} (F : OriginalFlagGeometry.{u} n)
    (x : OriginalFlagGermPoint F) (f : NativeHolGerm n F.carrier x.1) (hf : f ≠ 0) (k : ℕ) :
    originalFlagGermVector F x (f ^ k) (pow_ne_zero k hf) = k • originalFlagGermVector F x f hf := by
  induction k with
  | zero =>
    rw [vector_congr' F x (f ^ 0) 1 (pow_ne_zero 0 hf) one_ne_zero (pow_zero f),
      originalFlagGermVector_one, zero_smul]
  | succ k ih =>
    rw [vector_congr' F x (f ^ (k + 1)) (f ^ k * f) (pow_ne_zero _ hf)
      (mul_ne_zero (pow_ne_zero k hf) hf) (pow_succ f k),
      originalFlagGermVector_mul F x _ _ (pow_ne_zero k hf) hf, ih, succ_nsmul]

/-- The flag vector of a finite product of nonzero germs is the sum of the vectors. -/
theorem originalFlagGermVector_prod {n : ℕ} (F : OriginalFlagGeometry.{u} n)
    (x : OriginalFlagGermPoint F) {ι : Type*} (s : Finset ι) (f : ι → NativeHolGerm n F.carrier x.1)
    (hf : ∀ i, f i ≠ 0) :
    originalFlagGermVector F x (∏ i ∈ s, f i) (Finset.prod_ne_zero_iff.mpr fun i _ => hf i) =
      ∑ i ∈ s, originalFlagGermVector F x (f i) (hf i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [vector_congr' F x _ 1 _ one_ne_zero Finset.prod_empty, originalFlagGermVector_one,
      Finset.sum_empty]
  | insert a s ha ih =>
    rw [vector_congr' F x _ (f a * ∏ i ∈ s, f i) _
      (mul_ne_zero (hf a) (Finset.prod_ne_zero_iff.mpr fun i _ => hf i)) (Finset.prod_insert ha),
      originalFlagGermVector_mul F x _ _ (hf a) (Finset.prod_ne_zero_iff.mpr fun i _ => hf i),
      ih, Finset.sum_insert ha]

/-- `ν_{Y•}(∏_j g_j^{α_j}) = α` for a germ family adapted to the flag. -/
theorem originalFlagGermVector_prod_pow_adapted {n : ℕ} (F : OriginalFlagGeometry.{u} n)
    (x : OriginalFlagGermPoint F) (g : Fin n → NativeHolGerm n F.carrier x.1)
    (hg : IsAdaptedFlagGermFamily F x g) (α : Fin n → ℕ) :
    ∃ h : ∏ j, g j ^ α j ≠ 0, originalFlagGermVector F x (∏ j, g j ^ α j) h = α := by
  have hne : ∀ j, g j ≠ 0 := fun j => (originalFlagGermVector_adapted F x g hg j).1
  have hpow : ∀ j, g j ^ α j ≠ 0 := fun j => pow_ne_zero _ (hne j)
  refine ⟨Finset.prod_ne_zero_iff.mpr fun j _ => hpow j, ?_⟩
  rw [originalFlagGermVector_prod F x Finset.univ (fun j => g j ^ α j) hpow]
  have hj : ∀ j, originalFlagGermVector F x (g j ^ α j) (hpow j) = α j • Pi.single j 1 := by
    intro j
    rw [originalFlagGermVector_pow F x (g j) (hne j)]
    obtain ⟨h1, h2⟩ := originalFlagGermVector_adapted F x g hg j
    rw [h2]
  simp only [hj]
  funext i
  simp [Finset.sum_apply, Pi.single_apply]

/-! ### Adapted holomorphic coordinates -/

/-- Holomorphic functions `G_0, …, G_{n-1}` near the point `x` adapted to the flag of `F`:
`G_k` vanishes on `Y_{k+1}` near `x`, and every function holomorphic near `x` vanishing on
`Y_{i+1}` near `x` is, near `x`, a holomorphic combination of `G_0, …, G_i`.  (In local
coordinates with `Y_i = {z_1 = ⋯ = z_i = 0}`, the coordinates `G_k = z_{k+1}` are adapted.) -/
structure IsAdaptedFlagCoordinates {n : ℕ} (F : OriginalFlagGeometry.{u} n) (x : F.carrier)
    (G : Fin n → F.carrier → ℂ) : Prop where
  holo : ∀ k, HolomorphicAt n (G k) x
  vanish : ∀ k : Fin n, ∀ᶠ y in 𝓝 x, y ∈ F.flag k.succ → G k y = 0
  div : ∀ (i : Fin n) (h : F.carrier → ℂ), HolomorphicAt n h x →
    (∀ᶠ y in 𝓝 x, y ∈ F.flag i.succ → h y = 0) →
    ∃ a : Fin n → F.carrier → ℂ, (∀ k, HolomorphicAt n (a k) x) ∧
      h =ᶠ[𝓝 x] fun y => ∑ k, if k ≤ i then G k y * a k y else 0

theorem nativeHolGerm_mk_mul {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] {x : M} (f g : M → ℂ) (hf : HolomorphicAt n f x)
    (hg : HolomorphicAt n g x) :
    NativeHolGerm.mk f hf * NativeHolGerm.mk g hg =
      NativeHolGerm.mk (fun y => f y * g y) (hf.mul hg) := rfl

/-- Neighbourhoods in the first flag member `Y_1` (with its subspace topology). -/
theorem eventually_nhds_tail_iff {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))
    (y : F.tail.carrier) (P : F.carrier → Prop) :
    (∀ᶠ z : F.tail.carrier in 𝓝 y, P z.1) ↔ ∀ᶠ z in 𝓝 y.1, z ∈ F.flag 1 → P z := by
  have hind : Topology.IsInducing (fun z : F.tail.carrier => (z.1 : F.carrier)) :=
    Topology.IsInducing.subtypeVal
  rw [hind.nhds_eq_comap, Filter.eventually_comap]
  constructor
  · intro h
    filter_upwards [h] with b hb hbmem
    exact hb ⟨b, hbmem⟩ rfl
  · intro h
    filter_upwards [h] with b hb a hab
    subst hab
    exact hb a.2

/-- The restriction of a germ to `Y_1` vanishes iff the function vanishes on `Y_1` near the
point. -/
theorem originalFirstFlagGermRestriction_mk_eq_zero_iff_eventually {m : ℕ}
    (F : OriginalFlagGeometry.{u} (m + 1)) (y : F.tail.carrier) (H : F.carrier → ℂ)
    (hH : HolomorphicAt (m + 1) H y.1) :
    originalFirstFlagGermRestriction F y (NativeHolGerm.mk H hH) = 0 ↔
      ∀ᶠ z in 𝓝 y.1, z ∈ F.flag 1 → H z = 0 := by
  rw [← Subtype.coe_inj, originalFirstFlagGermRestriction_mk]
  change ((fun z : F.tail.carrier => H z.1 : F.tail.carrier → ℂ) : Germ (𝓝 y) ℂ) =
    ((fun _ => (0 : ℂ) : F.tail.carrier → ℂ) : Germ (𝓝 y) ℂ) ↔ _
  rw [Germ.coe_eq, Filter.EventuallyEq]
  exact eventually_nhds_tail_iff F y (fun z => H z = 0)

/-- The holomorphic restriction of a function to the first flag member. -/
theorem holomorphicAt_comp_val {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))
    (y : F.tail.carrier) {H : F.carrier → ℂ} (hH : HolomorphicAt (m + 1) H y.1) :
    HolomorphicAt m (fun z : F.tail.carrier => H z.1) y :=
  hH.comp_contMDiff (f := fun z : F.tail.carrier => z.1) (Eventually.of_forall fun z =>
    (SubmanifoldChartedSpace.contMDiff_val (Nat.le_succ m) F.firstDivisor.2.2) z)

theorem originalFirstFlagGermRestriction_mk_eq {m : ℕ}
    (F : OriginalFlagGeometry.{u} (m + 1)) (y : F.tail.carrier) (H : F.carrier → ℂ)
    (hH : HolomorphicAt (m + 1) H y.1) :
    originalFirstFlagGermRestriction F y (NativeHolGerm.mk H hH) =
      NativeHolGerm.mk (fun z : F.tail.carrier => H z.1) (holomorphicAt_comp_val F y hH) := by
  apply Subtype.ext
  exact originalFirstFlagGermRestriction_mk F y H hH

/-- Adapted holomorphic coordinates give an adapted germ family. -/
theorem isAdaptedFlagGermFamily_of_coordinates : ∀ {n : ℕ} (F : OriginalFlagGeometry.{u} n)
    (x : OriginalFlagGermPoint F) (G : Fin n → F.carrier → ℂ)
    (hG : IsAdaptedFlagCoordinates F x.1 G),
    IsAdaptedFlagGermFamily F x (fun k => NativeHolGerm.mk (G k) (hG.holo k))
  | 0, _, _, _, _ => trivial
  | m + 1, F, x, G, hG => by
    let y := OriginalFlagGermPoint.first F x
    have h01 : (0 : Fin (m + 1)).succ = 1 := Fin.succ_zero_eq_one
    refine ⟨?_, ?_⟩
    · apply le_antisymm
      · intro h hh
        obtain ⟨H, hH, rfl⟩ := NativeHolGerm.exists_eq_mk h
        have h0 : originalFirstFlagGermRestriction F y (NativeHolGerm.mk H hH) = 0 := hh
        have hvan1 := (originalFirstFlagGermRestriction_mk_eq_zero_iff_eventually F y H hH).mp h0
        have hvan : ∀ᶠ z in 𝓝 x.1, z ∈ F.flag (Fin.succ (0 : Fin (m + 1))) → H z = 0 := by
          filter_upwards [hvan1] with z hz hz1
          rw [h01] at hz1
          exact hz hz1
        obtain ⟨a, ha, heq⟩ := hG.div 0 H hH hvan
        refine Ideal.mem_span_singleton'.mpr ⟨NativeHolGerm.mk (a 0) (ha 0), ?_⟩
        refine (nativeHolGerm_mk_mul _ _ _ _).trans ((NativeHolGerm.mk_eq_mk_iff).mpr ?_)
        filter_upwards [heq] with z hz
        rw [hz, Fin.sum_univ_succ]
        simp [Fin.succ_ne_zero, mul_comm]
      · intro h hh
        obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hh
        have hv := hG.vanish 0
        rw [h01] at hv
        have h0 : originalFirstFlagGermRestriction F y (NativeHolGerm.mk (G 0) (hG.holo 0)) = 0 :=
          (originalFirstFlagGermRestriction_mk_eq_zero_iff_eventually F y (G 0) (hG.holo 0)).mpr hv
        change originalFirstFlagGermRestriction F y
          (c * (NativeHolGerm.mk (G 0) (hG.holo 0) : NativeHolGerm (m + 1) F.carrier y.1)) = 0
        rw [map_mul, h0, mul_zero]
    · let G' : Fin m → F.tail.carrier → ℂ := fun k z => G k.succ z.1
      have hG' : IsAdaptedFlagCoordinates F.tail (OriginalFlagGermPoint.tail F x).1 G' := by
        refine ⟨fun k => holomorphicAt_comp_val F y (hG.holo k.succ), fun k => ?_, ?_⟩
        · exact (continuous_subtype_val.tendsto y).eventually (hG.vanish k.succ)
        · intro i h' hh' hvan'
          obtain ⟨H0, hH0⟩ := originalFirstFlagGermRestriction_surjective F y
            (NativeHolGerm.mk h' hh')
          obtain ⟨H, hH, rfl⟩ := NativeHolGerm.exists_eq_mk H0
          rw [originalFirstFlagGermRestriction_mk_eq] at hH0
          have geq : (fun z : F.tail.carrier => H z.1) =ᶠ[𝓝 y] h' :=
            NativeHolGerm.mk_eq_mk_iff.mp hH0
          have hvanH : ∀ᶠ z in 𝓝 x.1, z ∈ F.flag i.succ.succ → H z = 0 := by
            have h1 : ∀ᶠ z : F.tail.carrier in 𝓝 y, z.1 ∈ F.flag i.succ.succ → H z.1 = 0 :=
              (geq.and hvan').mono fun z hz hz2 => hz.1.trans (hz.2 hz2)
            have h2 := (eventually_nhds_tail_iff F y
              (fun z => z ∈ F.flag i.succ.succ → H z = 0)).mp h1
            refine h2.mono fun z hz hz2 => hz ?_ hz2
            exact F.smooth.2.1 (show (1 : Fin (m + 2)) ≤ i.succ.succ from by
              rw [Fin.le_def]; simp) hz2
          obtain ⟨a, ha, heq⟩ := hG.div i.succ H hH hvanH
          refine ⟨fun k z => a k.succ z.1, fun k => holomorphicAt_comp_val F y (ha k.succ), ?_⟩
          have hv0 := hG.vanish 0
          rw [h01] at hv0
          have e1 := (continuous_subtype_val.tendsto y).eventually heq
          have e2 := (continuous_subtype_val.tendsto y).eventually hv0
          filter_upwards [geq, e1, e2] with z hz1 hz2 hz3
          rw [← hz1, hz2, Fin.sum_univ_succ, hz3 z.2]
          simp [G', Fin.succ_le_succ_iff]
      have h := isAdaptedFlagGermFamily_of_coordinates F.tail (OriginalFlagGermPoint.tail F x) G' hG'
      have hfun : (fun j : Fin m => originalFirstFlagGermRestriction F y
          (NativeHolGerm.mk (G j.succ) (hG.holo j.succ))) =
          fun k => NativeHolGerm.mk (G' k) (hG'.holo k) := by
        funext j
        exact originalFirstFlagGermRestriction_mk_eq F y (G j.succ) (hG.holo j.succ)
      change IsAdaptedFlagGermFamily F.tail (OriginalFlagGermPoint.tail F x)
        (fun j : Fin m => originalFirstFlagGermRestriction F y
          (NativeHolGerm.mk (G j.succ) (hG.holo j.succ)))
      rw [hfun]
      exact h

/-- Source `prop:toricusualOko` (proof): in coordinates adapted to the flag, the flag
valuation of the monomial `∏_j G_j^{α_j}` is `α`. -/
theorem originalFlagGermVector_monomial {n : ℕ} (F : OriginalFlagGeometry.{u} n)
    (x : OriginalFlagGermPoint F) (G : Fin n → F.carrier → ℂ)
    (hG : IsAdaptedFlagCoordinates F x.1 G) (α : Fin n → ℕ) :
    ∃ h : ∏ j, NativeHolGerm.mk (G j) (hG.holo j) ^ α j ≠ 0,
      originalFlagGermVector F x (∏ j, NativeHolGerm.mk (G j) (hG.holo j) ^ α j) h = α :=
  originalFlagGermVector_prod_pow_adapted F x _ (isAdaptedFlagGermFamily_of_coordinates F x G hG) α

end SGPT.Okounkov
