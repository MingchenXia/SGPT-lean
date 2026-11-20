import Mathlib.Analysis.Convex.Function
import Mathlib.Data.EReal.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Extended-real convex functions

The definition follows Appendix A, `def:convexfun`, of Mingchen Xia's
*Singularities in global pluripotential theory*: convexity means convexity of
the epigraph in `V × ℝ`. This treats both infinite values without performing
undefined arithmetic on them. The effective domain and properness have the
same conventions as the source.
-/

namespace SGPT.Convex

open Set

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The epigraph uses real heights even for extended-real-valued functions. -/
def epigraph (f : V → EReal) : Set (V × ℝ) := {p | f p.1 ≤ (p.2 : EReal)}

/-- A function is convex precisely when its real-height epigraph is convex. -/
def IsConvex (f : V → EReal) : Prop := Convex ℝ (epigraph f)

/-- The effective domain consists of all points where the value is below `+∞`. -/
def effectiveDomain (f : V → EReal) : Set V := {x | f x < ⊤}

/-- A proper convex function has nonempty effective domain and never equals `-∞`. -/
def IsProper (f : V → EReal) : Prop :=
  IsConvex f ∧ (effectiveDomain f).Nonempty ∧ ∀ x, f x ≠ ⊥

/-- For a real-valued function, epigraph convexity agrees with mathlib's `ConvexOn`. -/
theorem isConvex_coe_iff {f : V → ℝ} :
    IsConvex (fun x ↦ (f x : EReal)) ↔ ConvexOn ℝ Set.univ f := by
  simpa [IsConvex, epigraph] using
    (convexOn_iff_convex_epigraph (𝕜 := ℝ) (s := Set.univ) (f := f)).symm

/-- Real constants are convex, by mathlib's constant-function theorem. -/
theorem isConvex_const (c : ℝ) : IsConvex (fun _ : V ↦ (c : EReal)) :=
  isConvex_coe_iff.mpr (convexOn_const c convex_univ)

/-- Real linear functionals are convex, using mathlib rather than reproving Jensen's inequality. -/
theorem isConvex_linear (l : V →ₗ[ℝ] ℝ) : IsConvex (fun x ↦ (l x : EReal)) :=
  isConvex_coe_iff.mpr (l.convexOn convex_univ)

/-- Adding a real constant to a linear functional gives a convex function. -/
theorem isConvex_affine (l : V →ₗ[ℝ] ℝ) (c : ℝ) :
    IsConvex (fun x ↦ ((l x + c : ℝ) : EReal)) :=
  isConvex_coe_iff.mpr ((l.convexOn convex_univ).add_const c)

@[simp]
theorem isConvex_bot : IsConvex (fun _ : V ↦ (⊥ : EReal)) := by
  simpa [IsConvex, epigraph] using (convex_univ : Convex ℝ (Set.univ : Set (V × ℝ)))

@[simp]
theorem isConvex_top : IsConvex (fun _ : V ↦ (⊤ : EReal)) := by
  simpa [IsConvex, epigraph] using (convex_empty : Convex ℝ (∅ : Set (V × ℝ)))

/-- Arbitrary pointwise suprema preserve epigraph convexity, including an empty family.
This strengthens Appendix A, `prop:supconv`, by allowing an empty index type. -/
theorem isConvex_iSup {I : Sort*} {f : I → V → EReal}
    (hf : ∀ i, IsConvex (f i)) : IsConvex (fun x ↦ ⨆ i, f i x) := by
  intro p hp q hq a b ha hb hab
  have hp' : (⨆ i, f i p.1) ≤ (p.2 : EReal) := hp
  have hq' : (⨆ i, f i q.1) ≤ (q.2 : EReal) := hq
  change (⨆ i, f i (a • p.1 + b • q.1)) ≤ ((a * p.2 + b * q.2 : ℝ) : EReal)
  refine iSup_le fun i ↦ ?_
  exact hf i (x := p) (y := q) ((iSup_le_iff.mp hp') i) ((iSup_le_iff.mp hq') i)
    ha hb hab

/-- The lower convex envelope is the pointwise supremum of all convex minorants.
This is the exact definition `def:LCE` in Appendix A. -/
noncomputable def lowerConvexEnvelope (f : V → EReal) : V → EReal :=
  fun x ↦ ⨆ (g : V → EReal) (_ : IsConvex g) (_ : g ≤ f), g x

/-- The lower convex envelope is convex. -/
theorem isConvex_lowerConvexEnvelope (f : V → EReal) :
    IsConvex (lowerConvexEnvelope f) := by
  apply isConvex_iSup
  intro g
  apply isConvex_iSup
  intro hg
  exact isConvex_iSup fun _ ↦ hg

/-- The lower convex envelope lies below its obstacle. -/
theorem lowerConvexEnvelope_le (f : V → EReal) : lowerConvexEnvelope f ≤ f := by
  intro x
  exact iSup_le fun g ↦ iSup_le fun _ ↦ iSup_le fun hgf ↦ hgf x

/-- Every convex minorant lies below the lower convex envelope. -/
theorem le_lowerConvexEnvelope {f g : V → EReal} (hg : IsConvex g) (hgf : g ≤ f) :
    g ≤ lowerConvexEnvelope f := by
  intro x
  exact le_iSup_of_le g (le_iSup_of_le hg (le_iSup_of_le hgf le_rfl))

/-- The lower convex envelope is monotone in its obstacle. -/
theorem lowerConvexEnvelope_mono {f g : V → EReal} (hfg : f ≤ g) :
    lowerConvexEnvelope f ≤ lowerConvexEnvelope g := by
  exact le_lowerConvexEnvelope (isConvex_lowerConvexEnvelope f)
    ((lowerConvexEnvelope_le f).trans hfg)

/-- A convex function is fixed by the lower convex envelope. -/
theorem lowerConvexEnvelope_eq_self {f : V → EReal} (hf : IsConvex f) :
    lowerConvexEnvelope f = f := by
  exact le_antisymm (lowerConvexEnvelope_le f) (le_lowerConvexEnvelope hf le_rfl)

/-- Taking the lower convex envelope twice gives the same function. -/
theorem lowerConvexEnvelope_idempotent (f : V → EReal) :
    lowerConvexEnvelope (lowerConvexEnvelope f) = lowerConvexEnvelope f :=
  lowerConvexEnvelope_eq_self (isConvex_lowerConvexEnvelope f)

/-- The convex indicator equals zero on the set and `+∞` outside it. -/
noncomputable def indicator (A : Set V) (x : V) : EReal := by
  classical
  exact if x ∈ A then 0 else ⊤

/-- A convex subset has a convex extended-real indicator (`ex:charconvex`). -/
theorem isConvex_indicator {A : Set V} (hA : Convex ℝ A) : IsConvex (indicator A) := by
  classical
  intro p hp q hq a b ha hb hab
  have hpA : p.1 ∈ A := by
    by_contra h
    simp [epigraph, indicator, h] at hp
  have hqA : q.1 ∈ A := by
    by_contra h
    simp [epigraph, indicator, h] at hq
  have hp0 : 0 ≤ p.2 := by
    simpa [epigraph, indicator, hpA] using hp
  have hq0 : 0 ≤ q.2 := by
    simpa [epigraph, indicator, hqA] using hq
  have hcomb := hA hpA hqA ha hb hab
  have hheight : 0 ≤ a * p.2 + b * q.2 :=
    add_nonneg (mul_nonneg ha hp0) (mul_nonneg hb hq0)
  change indicator A (a • p.1 + b • q.1) ≤ ((a * p.2 + b * q.2 : ℝ) : EReal)
  simpa only [indicator, if_pos hcomb, EReal.coe_zero] using (EReal.coe_le_coe hheight)

omit [AddCommGroup V] [Module ℝ V] in
@[simp]
theorem effectiveDomain_indicator (A : Set V) : effectiveDomain (indicator A) = A := by
  classical
  ext x
  by_cases hx : x ∈ A <;> simp [effectiveDomain, indicator, hx]

/-- The indicator of a convex set is proper exactly when the set is nonempty. -/
theorem isProper_indicator_iff {A : Set V} (hA : Convex ℝ A) :
    IsProper (indicator A) ↔ A.Nonempty := by
  classical
  simp only [IsProper, effectiveDomain_indicator]
  constructor
  · exact fun h ↦ h.2.1
  · intro h
    refine ⟨isConvex_indicator hA, h, ?_⟩
    intro x
    by_cases hx : x ∈ A <;> simp [indicator, hx]

/-- Strict real majorants characterize extended-real epigraph convexity.
The source's `t ∈ (0,1)` is expressed as positive coefficients summing to one. -/
theorem isConvex_iff_strict_combo {f : V → EReal} : IsConvex f ↔
    ∀ (x y : V) (r s a b : ℝ), f x < (r : EReal) → f y < (s : EReal) →
      0 < a → 0 < b → a + b = 1 →
      f (a • x + b • y) < ((a * r + b * s : ℝ) : EReal) := by
  constructor
  · intro hf x y r s a b hxr hys ha hb hab
    obtain ⟨r', hr'lo, hr'hi⟩ := EReal.exists_between_coe_real hxr
    obtain ⟨s', hs'lo, hs'hi⟩ := EReal.exists_between_coe_real hys
    have hbound : f (a • x + b • y) ≤ ((a * r' + b * s' : ℝ) : EReal) :=
      hf (x := (x, r')) (y := (y, s')) hr'lo.le hs'lo.le ha.le hb.le hab
    have hr' : r' < r := EReal.coe_lt_coe_iff.mp hr'hi
    have hs' : s' < s := EReal.coe_lt_coe_iff.mp hs'hi
    have hstrict : a * r' + b * s' < a * r + b * s :=
      add_lt_add (mul_lt_mul_of_pos_left hr' ha) (mul_lt_mul_of_pos_left hs' hb)
    exact lt_of_le_of_lt hbound (EReal.coe_lt_coe hstrict)
  · intro h p hp q hq a b ha hb hab
    by_cases ha0 : a = 0
    · have hb1 : b = 1 := by linarith
      simpa [ha0, hb1] using hq
    by_cases hb0 : b = 0
    · have ha1 : a = 1 := by linarith
      simpa [hb0, ha1] using hp
    have ha' : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    have hb' : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
    change f (a • p.1 + b • q.1) ≤ ((a * p.2 + b * q.2 : ℝ) : EReal)
    by_contra hnot
    obtain ⟨u, hu_lo, hu_hi⟩ := EReal.exists_between_coe_real (lt_of_not_ge hnot)
    let ε : ℝ := u - (a * p.2 + b * q.2)
    have hε : 0 < ε := sub_pos.mpr (EReal.coe_lt_coe_iff.mp hu_lo)
    have hp' : f p.1 < ((p.2 + ε : ℝ) : EReal) :=
      lt_of_le_of_lt hp (EReal.coe_lt_coe (lt_add_of_pos_right p.2 hε))
    have hq' : f q.1 < ((q.2 + ε : ℝ) : EReal) :=
      lt_of_le_of_lt hq (EReal.coe_lt_coe (lt_add_of_pos_right q.2 hε))
    have hstrict := h p.1 q.1 (p.2 + ε) (q.2 + ε) a b hp' hq' ha' hb' hab
    have heq : a * (p.2 + ε) + b * (q.2 + ε) = u := by
      calc
        _ = (a * p.2 + b * q.2) + (a + b) * ε := by ring
        _ = u := by rw [hab]; dsimp [ε]; ring
    rw [heq] at hstrict
    exact lt_asymm hstrict hu_hi

/-- The infimum of a downward-directed family of convex functions is convex.
Directedness is pointwise and need not come from a particular indexing order. -/
theorem isConvex_iInf_of_directed {I : Type*} {f : I → V → EReal}
    (hf : ∀ i, IsConvex (f i))
    (hdir : Directed (fun g h : V → EReal ↦ h ≤ g) f) :
    IsConvex (fun x ↦ ⨅ i, f i x) := by
  apply isConvex_iff_strict_combo.mpr
  intro x y r s a b hxr hys ha hb hab
  obtain ⟨i, hi⟩ := iInf_lt_iff.mp hxr
  obtain ⟨j, hj⟩ := iInf_lt_iff.mp hys
  obtain ⟨k, hik, hjk⟩ := hdir i j
  have hk := isConvex_iff_strict_combo.mp (hf k) x y r s a b
    (lt_of_le_of_lt (hik x) hi) (lt_of_le_of_lt (hjk y) hj) ha hb hab
  exact lt_of_le_of_lt (iInf_le (fun i ↦ f i (a • x + b • y)) k) hk

/-- A decreasing net has a convex pointwise infimum (`lma:convdecnet`). -/
theorem isConvex_iInf_of_antitone {I : Type*} [Preorder I] [IsDirectedOrder I]
    {f : I → V → EReal} (hf : ∀ i, IsConvex (f i)) (hanti : Antitone f) :
    IsConvex (fun x ↦ ⨅ i, f i x) := by
  apply isConvex_iInf_of_directed hf
  intro i j
  obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
  exact ⟨k, hanti hik, hanti hjk⟩

/-- Epigraph convexity implies convexity of the effective domain. -/
theorem convex_effectiveDomain {f : V → EReal} (hf : IsConvex f) :
    Convex ℝ (effectiveDomain f) := by
  intro x hx y hy a b ha hb hab
  by_cases ha0 : a = 0
  · have hb1 : b = 1 := by linarith
    simpa [ha0, hb1] using hy
  by_cases hb0 : b = 0
  · have ha1 : a = 1 := by linarith
    simpa [hb0, ha1] using hx
  obtain ⟨r, hr, _⟩ := EReal.exists_between_coe_real (show f x < ⊤ from hx)
  obtain ⟨s, hs, _⟩ := EReal.exists_between_coe_real (show f y < ⊤ from hy)
  exact lt_trans
    (isConvex_iff_strict_combo.mp hf x y r s a b hr hs
      (lt_of_le_of_ne ha (Ne.symm ha0)) (lt_of_le_of_ne hb (Ne.symm hb0)) hab)
    (EReal.coe_lt_top _)

/-- Extended-real convex indicators characterize convex subsets. -/
theorem isConvex_indicator_iff (A : Set V) : IsConvex (indicator A) ↔ Convex ℝ A := by
  constructor
  · intro h
    simpa only [effectiveDomain_indicator] using convex_effectiveDomain h
  · exact isConvex_indicator

end SGPT.Convex
