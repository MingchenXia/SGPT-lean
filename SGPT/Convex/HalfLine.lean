import SGPT.Convex.FamilyOperations
import SGPT.Convex.RelativeInterior
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Topology.Instances.Rat

/-!
# Actual positive-half-line Legendre inversion

An input is read only on positive real arguments. Its actual extension is top
elsewhere, so convexity is exactly convexity of the source half-line epigraph.
The negative-infinite case is handled by actual epigraph interpolation.
-/

namespace SGPT.Convex

open Set Filter Topology

/-- Extend the actual positive-half-line obstacle by top, including at zero. -/
noncomputable def positiveExtension (F : ℝ → EReal) (t : ℝ) : EReal :=
  if 0 < t then F t else ⊤

/-- The actual extension epigraph is exactly the source half-line epigraph. -/
theorem epigraph_positiveExtension (F : ℝ → EReal) :
    epigraph (positiveExtension F) = {p : ℝ × ℝ | 0 < p.1 ∧ F p.1 ≤ (p.2 : EReal)} := by
  ext p
  by_cases hp : 0 < p.1 <;> simp [epigraph, positiveExtension, hp]

/-- Source half-line epigraph convexity produces actual extension convexity. -/
theorem isConvex_positiveExtension {F : ℝ → EReal}
    (hF : Convex ℝ {p : ℝ × ℝ | 0 < p.1 ∧ F p.1 ≤ (p.2 : EReal)}) :
    IsConvex (positiveExtension F) := by
  unfold IsConvex
  rw [epigraph_positiveExtension]
  exact hF

/-- The source non-top codomain gives precisely the actual open half-line domain. -/
theorem effectiveDomain_positiveExtension {F : ℝ → EReal}
    (hF : ∀ t, 0 < t → F t < ⊤) :
    effectiveDomain (positiveExtension F) = Ioi 0 := by
  ext t
  by_cases ht : 0 < t
  · simp [effectiveDomain, positiveExtension, ht, hF t ht]
  · simp [effectiveDomain, positiveExtension, ht]

/-- Actual scalar multiplication pairing for the source one-dimensional dual. -/
def scalarPairing : ℝ →ₗ[ℝ] ℝ →ₗ[ℝ] ℝ := LinearMap.mul ℝ ℝ

/-- The scalar pairing is genuinely perfect: every real functional is determined at one. -/
instance scalarPairing_isContPerfPair : scalarPairing.IsContPerfPair where
  continuous_uncurry := continuous_mul
  bijective_left := by
    constructor
    · intro x y h
      have h' := congrArg (fun m : StrongDual ℝ ℝ ↦ m 1) h
      simpa [scalarPairing] using h'
    · intro m
      refine ⟨m 1, ?_⟩
      apply ContinuousLinearMap.ext
      intro t
      change m 1 * t = m t
      simpa [smul_eq_mul, mul_comm] using (m.map_smul t 1).symm
  bijective_right := by
    constructor
    · intro x y h
      have h' := congrArg (fun m : StrongDual ℝ ℝ ↦ m 1) h
      simpa [scalarPairing] using h'
    · intro m
      refine ⟨m 1, ?_⟩
      apply ContinuousLinearMap.ext
      intro t
      change t * m 1 = m t
      simpa [smul_eq_mul] using (m.map_smul t 1).symm

/-- Reversal of the actual scalar pairing is multiplication itself. -/
theorem scalarPairing_flip : scalarPairing.flip = scalarPairing := by
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  exact mul_comm y x

/-- Bottom at an actual endpoint propagates along every actual open segment
whose other endpoint has a real upper height. -/
theorem eq_bot_of_eq_bot_of_mem_openSegment {E : Type*} [AddCommGroup E] [Module ℝ E]
    {f : E → EReal} (hf : IsConvex f) {x z y : E}
    (hx : f x = ⊥) (hz : f z < ⊤) (hy : y ∈ openSegment ℝ x z) : f y = ⊥ := by
  obtain ⟨s, hs, _⟩ := EReal.exists_between_coe_real hz
  rcases hy with ⟨a, b, ha, hb, hab, rfl⟩
  apply le_bot_iff.mp
  apply EReal.le_of_forall_lt_iff_le.mp
  intro r _
  have hp : (x, (r - b * s) / a) ∈ epigraph f := by
    change f x ≤ ((r - b * s) / a : ℝ)
    rw [hx]
    exact bot_le
  have hq : (z, s) ∈ epigraph f := hs.le
  have h := hf hp hq ha.le hb.le hab
  change f (a • x + b • z) ≤ ((a * ((r - b * s) / a) + b * s : ℝ) : EReal) at h
  have heq : a * ((r - b * s) / a) + b * s = r := by
    field_simp
    ring
  simpa only [heq] using h

/-- A source bottom value propagates through the whole actual open half-line. -/
theorem positive_eq_bot_of_exists_bot {F : ℝ → EReal}
    (hconv : Convex ℝ {p : ℝ × ℝ | 0 < p.1 ∧ F p.1 ≤ (p.2 : EReal)})
    (hfinite : ∀ t, 0 < t → F t < ⊤)
    (hbot : ∃ x, 0 < x ∧ F x = ⊥) : ∀ t, 0 < t → F t = ⊥ := by
  obtain ⟨x, hx, hxbot⟩ := hbot
  have hc := isConvex_positiveExtension hconv
  have hx' : positiveExtension F x = ⊥ := by simp [positiveExtension, hx, hxbot]
  intro t ht
  by_cases heq : x = t
  · simpa only [heq] using hxbot
  rcases lt_or_gt_of_ne heq with hxt | htx
  · have hz : 0 < 2 * t := by linarith
    have hz' : positiveExtension F (2 * t) < ⊤ := by
      simpa only [positiveExtension, if_pos hz] using hfinite (2 * t) hz
    have hs : t ∈ openSegment ℝ x (2 * t) :=
      Ioo_subset_openSegment ⟨hxt, by linarith⟩
    simpa only [positiveExtension, if_pos ht] using
      eq_bot_of_eq_bot_of_mem_openSegment hc hx' hz' hs
  · have hz : 0 < t / 2 := by linarith
    have hz' : positiveExtension F (t / 2) < ⊤ := by
      simpa only [positiveExtension, if_pos hz] using hfinite (t / 2) hz
    have hs : t ∈ openSegment ℝ x (t / 2) := by
      rw [openSegment_symm]
      exact Ioo_subset_openSegment ⟨by linarith, htx⟩
    simpa only [positiveExtension, if_pos ht] using
      eq_bot_of_eq_bot_of_mem_openSegment hc hx' hz' hs

/-- The actual source supremum over strictly positive real arguments. -/
noncomputable def halfLineConjugate (F : ℝ → EReal) (τ : ℝ) : EReal :=
  ⨆ (t : ℝ) (_ : 0 < t), ((t * τ : ℝ) : EReal) - F t

/-- The actual half-line supremum is the full conjugate of its top extension. -/
theorem halfLineConjugate_eq_conjugate (F : ℝ → EReal) :
    halfLineConjugate F = conjugate scalarPairing (positiveExtension F) := by
  funext τ
  apply le_antisymm
  · apply iSup_le
    intro t
    apply iSup_le
    intro ht
    simpa only [scalarPairing, LinearMap.mul_apply', positiveExtension, if_pos ht,
      halfLineConjugate, conjugate] using
      (le_iSup (fun x ↦ (scalarPairing x τ : EReal) - positiveExtension F x) t)
  · apply iSup_le
    intro t
    by_cases ht : 0 < t
    · simpa only [scalarPairing, LinearMap.mul_apply', positiveExtension, if_pos ht,
        halfLineConjugate, conjugate] using
        (le_iSup_of_le t (le_iSup_of_le ht le_rfl) :
          ((t * τ : ℝ) : EReal) - F t ≤ halfLineConjugate F τ)
    · simp [positiveExtension, ht]

/-- The actual half-line conjugate is convex, even before source convexity is imposed. -/
theorem isConvex_halfLineConjugate (F : ℝ → EReal) : IsConvex (halfLineConjugate F) := by
  rw [halfLineConjugate_eq_conjugate]
  exact isConvex_conjugate _ _

/-- Actual source upper finiteness ensures the half-line conjugate never equals bottom. -/
theorem halfLineConjugate_ne_bot {F : ℝ → EReal}
    (hfinite : ∀ t, 0 < t → F t < ⊤) : ∀ τ, halfLineConjugate F τ ≠ ⊥ := by
  rw [halfLineConjugate_eq_conjugate]
  apply conjugate_ne_bot_of_exists_ne_top
  refine ⟨1, ?_⟩
  simpa [positiveExtension] using ne_of_lt (hfinite 1 zero_lt_one)

/-- The actual extension is proper when the source positive values are finite. -/
theorem isProper_positiveExtension {F : ℝ → EReal}
    (hconv : Convex ℝ {p : ℝ × ℝ | 0 < p.1 ∧ F p.1 ≤ (p.2 : EReal)})
    (hfinite : ∀ t, 0 < t → F t < ⊤) (hnobot : ∀ t, 0 < t → F t ≠ ⊥) :
    IsProper (positiveExtension F) := by
  refine ⟨isConvex_positiveExtension hconv, ?_, ?_⟩
  · rw [effectiveDomain_positiveExtension hfinite]
    exact ⟨1, by simp⟩
  · intro t
    by_cases ht : 0 < t
    · simpa only [positiveExtension, if_pos ht] using hnobot t ht
    · simp [positiveExtension, ht]

/-- A genuine positive bottom witness makes the actual half-line conjugate top. -/
theorem halfLineConjugate_eq_top_of_exists_bot {F : ℝ → EReal}
    (hbot : ∃ x, 0 < x ∧ F x = ⊥) : halfLineConjugate F = (fun _ ↦ ⊤) := by
  obtain ⟨x, hx, hxb⟩ := hbot
  rw [halfLineConjugate_eq_conjugate]
  apply conjugate_eq_top_of_exists_bot
  exact ⟨x, by simp [positiveExtension, hx, hxb]⟩

/-- Exact source inversion at every strictly positive point, with the actual
bottom propagation branch and genuine scalar-perfect-pairing biconjugation. -/
theorem halfLineConjugate_inversion {F : ℝ → EReal}
    (hconv : Convex ℝ {p : ℝ × ℝ | 0 < p.1 ∧ F p.1 ≤ (p.2 : EReal)})
    (hfinite : ∀ t, 0 < t → F t < ⊤) {t : ℝ} (ht : 0 < t) :
    conjugate scalarPairing (halfLineConjugate F) t = F t := by
  classical
  by_cases hbot : ∃ x, 0 < x ∧ F x = ⊥
  · rw [halfLineConjugate_eq_top_of_exists_bot hbot,
      positive_eq_bot_of_exists_bot hconv hfinite hbot t ht]
    simp [conjugate]
  have hnobot : ∀ x, 0 < x → F x ≠ ⊥ := by
    intro x hx hxb
    exact hbot ⟨x, hx, hxb⟩
  have hf := isProper_positiveExtension hconv hfinite hnobot
  have hb : conjugate scalarPairing (halfLineConjugate F) =
      convexClosure (positiveExtension F) := by
    rw [halfLineConjugate_eq_conjugate]
    have h := biconjugate_eq_convexClosure_of_isContPerfPair scalarPairing hf.1
    rwa [scalarPairing_flip] at h
  have hri : t ∈ intrinsicInterior ℝ (effectiveDomain (positiveExtension F)) := by
    apply interior_subset_intrinsicInterior
    rw [effectiveDomain_positiveExtension hfinite, isOpen_Ioi.interior_eq]
    exact ht
  rw [hb, convexClosure_of_forall_ne_bot hf.2.2,
    regularization_eq_of_mem_intrinsicInterior hf hri]
  simp [positiveExtension, ht]

/-- Exact positive rational supremum, derived from actual rational density
and genuine convex continuity on the open half-line. -/
theorem halfLineConjugate_eq_iSup_rat {F : ℝ → EReal}
    (hconv : Convex ℝ {p : ℝ × ℝ | 0 < p.1 ∧ F p.1 ≤ (p.2 : EReal)})
    (hfinite : ∀ t, 0 < t → F t < ⊤) (τ : ℝ) :
    halfLineConjugate F τ =
      ⨆ (q : ℚ) (_ : 0 < q), (((q : ℝ) * τ : ℝ) : EReal) - F (q : ℝ) := by
  classical
  by_cases hbot : ∃ x, 0 < x ∧ F x = ⊥
  · rw [halfLineConjugate_eq_top_of_exists_bot hbot]
    symm
    apply top_le_iff.mp
    have hb : F 1 = ⊥ := positive_eq_bot_of_exists_bot hconv hfinite hbot 1 zero_lt_one
    apply le_iSup_of_le (1 : ℚ)
    apply le_iSup_of_le (show (0 : ℚ) < 1 from zero_lt_one)
    simp [hb]
  have hnobot : ∀ x, 0 < x → F x ≠ ⊥ := by
    intro x hx hxb
    exact hbot ⟨x, hx, hxb⟩
  have hf := isProper_positiveExtension hconv hfinite hnobot
  let R : Set ℝ := ((↑) : ℚ → ℝ) '' Ioi 0
  let S : EReal := ⨆ (q : ℚ) (_ : 0 < q),
    (((q : ℝ) * τ : ℝ) : EReal) - F (q : ℝ)
  let H : ℝ → EReal := fun x ↦ ((x * τ - (positiveExtension F x).toReal : ℝ) : EReal)
  have hdense (t : ℝ) (ht : 0 < t) : t ∈ _root_.closure R := by
    apply mem_closure_iff.mpr
    intro o ho hto
    obtain ⟨q, hq⟩ := (Rat.denseRange_cast : DenseRange ((↑) : ℚ → ℝ)).exists_mem_open
      (ho.inter isOpen_Ioi) ⟨t, hto, ht⟩
    have hqpos : (0 : ℚ) < q := by
      exact_mod_cast (show (0 : ℝ) < (q : ℝ) from hq.2)
    exact ⟨(q : ℝ), hq.1, q, hqpos, rfl⟩
  have hcont : ContinuousOn (fun x ↦ (positiveExtension F x).toReal) (Ioi 0) := by
    simpa only [effectiveDomain_positiveExtension hfinite, isOpen_Ioi.interior_eq] using
      (convexOn_toReal_effectiveDomain hf).continuousOn_interior
  have hvalue (x : ℝ) (hx : 0 < x) : H x = ((x * τ : ℝ) : EReal) - F x := by
    have hc : ((positiveExtension F x).toReal : EReal) = F x := by
      rw [EReal.coe_toReal (by
        simpa only [positiveExtension, if_pos hx] using ne_of_lt (hfinite x hx)) (hf.2.2 x)]
      simp only [positiveExtension, if_pos hx]
    simp only [H, EReal.coe_sub, hc]
  have hmaps : MapsTo H R (Iic S) := by
    rintro _ ⟨q, hq, rfl⟩
    have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (show (0 : ℚ) < q from hq)
    change H (q : ℝ) ≤ S
    rw [hvalue (q : ℝ) hqpos]
    exact le_iSup_of_le q (le_iSup_of_le hq le_rfl)
  apply le_antisymm
  · apply iSup_le
    intro t
    apply iSup_le
    intro ht
    have hH : ContinuousAt H t := by
      have hreal : ContinuousAt (fun x : ℝ ↦ x * τ - (positiveExtension F x).toReal) t :=
        (continuous_id.continuousAt.mul continuous_const.continuousAt).sub
          (hcont.continuousAt (isOpen_Ioi.mem_nhds ht))
      exact continuous_coe_real_ereal.continuousAt.comp hreal
    have h := hH.continuousWithinAt.mem_closure (hdense t ht) hmaps
    have hle : H t ≤ S := by
      simpa only [isClosed_Iic.closure_eq, mem_Iic] using h
    simpa only [hvalue t ht] using hle
  · apply iSup_le
    intro q
    apply iSup_le
    intro hq
    have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
    exact le_iSup_of_le (q : ℝ) (le_iSup_of_le hqpos le_rfl)

end SGPT.Convex
