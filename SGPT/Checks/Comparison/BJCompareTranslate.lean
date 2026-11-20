import SGPT.Checks.Comparison.BJCanonicalModuleTopology

/-!
# Translating Boucksom–Jonsson psh metrics by real constants

An input of `lma:pltest` (`chapter_NApotential.tex`, *The algebraic setting*): the
analytification of a piecewise linear curve is `A^An = max_i (A_{τ_i}^An + τ_i)` with real
`τ_i`, so `PSH(L^An)` (`def:BJpshmetric`, `IsModuleTopologyPSH`) has to be stable under adding a
real constant.  (BJ22 records this among the elementary properties of `PSH(L^an)`.)

For rational constants this is a statement about generically finite Fubini–Study functions:
adding `q ∈ ℚ` to `φ = m⁻¹ max_j (log|s_j| + λ_j)` replaces `λ_j` by `λ_j + m q`
(`gfDataTranslate`).  For a real constant `c` we use a decreasing sequence of rationals
`q_k ↓ c` and the product net `(i, k)`.

## Main results

* `gfDataTranslate`, `rationalGFFunction_gfDataTranslate`;
* `RationalGFPackage.translate`, with the same class and `eval + q`;
* `IsModuleTopologyPSH.add_const`: `φ ∈ PSH(L^An)` implies `φ + c ∈ PSH(L^An)` for `c ∈ ℝ`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

namespace SGPT.NAPotential.BJ.Printed

open AlgebraicGeometry CategoryTheory Filter Topology
open SGPT.NAPotential.Berkovich SGPT.NAPotential.Berkovich.BJSections
open SGPT.NAPotential.BJ.NativePicard SGPT.Foundations.Schemes SGPT.Foundations.Envelope

variable {X : Scheme.{0}}

/-- Shift every rational weight of a GF datum `m⁻¹ max_j (log|s_j| + λ_j)` by `m q`; the
resulting GF function is the original one plus `q`. -/
def gfDataTranslate {L : X.Modules} {n m : ℕ} (D : RationalGFData L n m) (q : ℚ) :
    RationalGFData L n m :=
  { D with weight := fun i => D.weight i + (m : ℚ) * q }

private theorem coe_mul_add_coe' {c : ℝ} (hc : 0 < c) (a : EReal) (r : ℝ) :
    (c : EReal) * (a + (r : EReal)) = (c : EReal) * a + ((c * r : ℝ) : EReal) := by
  induction a with
  | bot => simp [EReal.coe_mul_bot_of_pos hc]
  | top => rw [EReal.top_add_coe, EReal.coe_mul_top_of_pos hc, EReal.top_add_coe]
  | coe a => rw [← EReal.coe_add, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add, mul_add]

/-- Adding `q` to a rational GF function. -/
theorem rationalGFFunction_gfDataTranslate {f : X ⟶ Spec (.of ℂ)} [IsProper f]
    {L : X.Modules} {n m : ℕ} (a : LineBundleAtlas L) (D : RationalGFData L n m) (q : ℚ)
    (v : BerkovichPoint f) :
    rationalGFFunction a (gfDataTranslate D q) v = rationalGFFunction a D v + ((q : ℝ) : EReal) := by
  have hm : (0 : ℝ) < m := Nat.cast_pos.mpr D.denominator_pos
  have hsup : finiteMaximum a (gfDataTranslate D q) v =
      finiteMaximum a D v + (((m : ℝ) * q : ℝ) : EReal) := by
    have hterm : ∀ i : D.I, sectionLogNorm a n (D.sections i) v +
        (((D.weight i + (m : ℚ) * q : ℚ) : ℝ) : EReal) =
        (sectionLogNorm a n (D.sections i) v + ((D.weight i : ℝ) : EReal)) +
          (((m : ℝ) * q : ℝ) : EReal) := by
      intro i
      rw [add_assoc]
      congr 1
      push_cast
      rfl
    apply le_antisymm
    · refine iSup_le fun i => ?_
      change sectionLogNorm a n (D.sections i) v +
        (((D.weight i + (m : ℚ) * q : ℚ) : ℝ) : EReal) ≤ _
      rw [hterm i]
      exact add_le_add_left (le_iSup (fun i : D.I => sectionLogNorm a n (D.sections i) v +
        ((D.weight i : ℝ) : EReal)) i) _
    · obtain ⟨i, hi⟩ := finiteMaximum_attained a D v
      rw [hi, ← hterm i]
      exact le_iSup (fun j : D.I => sectionLogNorm a n (D.sections j) v +
        (((D.weight j + (m : ℚ) * q : ℚ) : ℝ) : EReal)) i
  unfold rationalGFFunction
  rw [hsup, coe_mul_add_coe' (by positivity) _ _]
  congr 2
  field_simp

namespace RationalGFPackage

/-- The GF package with every weight shifted so that its function is shifted by `q`. -/
def translate (D : RationalGFPackage X) (q : ℚ) : RationalGFPackage X :=
  ⟨D.line, D.atlas, D.n, D.m, gfDataTranslate D.data q⟩

variable (p : X ⟶ Spec (.of ℂ)) [IsProjective p]
local instance : IsProper p := (ProjectiveFactorizationRingIso.of_isProjective p).isProper

theorem translate_eval (D : RationalGFPackage X) (q : ℚ) (v : BerkovichPoint p) :
    (D.translate q).eval p v = D.eval p v + ((q : ℝ) : EReal) :=
  rationalGFFunction_gfDataTranslate D.atlas D.data q v

/-- Translation does not change the class (`gfPicardClass` only depends on `n/m` and the
line bundle). -/
theorem translate_numericalClass (D : RationalGFPackage X) (q : ℚ) :
    (D.translate q).numericalClass p = D.numericalClass p := rfl

end RationalGFPackage

variable (p : X ⟶ Spec (.of ℂ)) [IsProjective p]

/-- A strictly decreasing sequence of rationals converging to a given real number. -/
theorem exists_rat_seq_antitone_tendsto (c : ℝ) :
    ∃ q : ℕ → ℚ, Antitone q ∧ Tendsto (fun k => (q k : ℝ)) atTop (𝓝 c) := by
  have h : ∀ k : ℕ, ∃ r : ℚ, c + 1 / ((k : ℝ) + 2) < r ∧ (r : ℝ) < c + 1 / ((k : ℝ) + 1) := by
    intro k
    apply exists_rat_btwn
    have : 1 / ((k : ℝ) + 2) < 1 / ((k : ℝ) + 1) :=
      one_div_lt_one_div_of_lt (by positivity) (by linarith)
    linarith
  choose q hq using h
  refine ⟨q, antitone_nat_of_succ_le fun k => ?_, ?_⟩
  · have h1 := (hq (k + 1)).2
    have h2 := (hq k).1
    have : ((k + 1 : ℕ) : ℝ) + 1 = (k : ℝ) + 2 := by push_cast; ring
    rw [this] at h1
    exact_mod_cast (h1.trans h2).le
  · have hlim : Tendsto (fun k : ℕ => c + 1 / ((k : ℝ) + 1)) atTop (𝓝 c) := by
      simpa using (tendsto_one_div_add_atTop_nhds_zero_nat).const_add c
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun k => ?_) (fun k => (hq k).2.le)
    have : (0 : ℝ) < 1 / ((k : ℝ) + 2) := by positivity
    have := (hq k).1
    linarith

/-- **`PSH(L^An)` is stable under adding real constants.** -/
theorem IsModuleTopologyPSH.add_const {L : RationalPicardSpace X}
    {φ : BerkovichPoint p → EReal} (h : IsModuleTopologyPSH.{u} p L φ) (c : ℝ) :
    IsModuleTopologyPSH.{u} p L (fun v => φ v + (c : EReal)) := by
  obtain ⟨⟨v₀, hv₀⟩, D, hclass, hlim⟩ := h
  obtain ⟨q, hqanti, hqlim⟩ := exists_rat_seq_antitone_tendsto c
  let J : Type u := D.I × ULift.{u} ℕ
  let hdir : IsDirectedOrder J :=
    ⟨fun a b => by
      obtain ⟨i, hi1, hi2⟩ := exists_ge_ge a.1 b.1
      refine ⟨(i, ⟨max a.2.down b.2.down⟩), ⟨hi1, ?_⟩, ⟨hi2, ?_⟩⟩
      · exact ULift.down_le.mp (le_max_left a.2.down b.2.down)
      · exact ULift.down_le.mp (le_max_right a.2.down b.2.down)⟩
  let E : DecreasingGFNet.{u} p :=
    { I := J
      preorder := inferInstance
      nonempty := inferInstance
      directed := hdir
      term := fun ik => (D.term ik.1).translate (q ik.2.down)
      decreasing := fun v a b hab => by
        change ((D.term b.1).translate (q b.2.down)).eval p v ≤
          ((D.term a.1).translate (q a.2.down)).eval p v
        rw [RationalGFPackage.translate_eval, RationalGFPackage.translate_eval]
        refine add_le_add (D.decreasing v hab.1) ?_
        exact EReal.coe_le_coe_iff.mpr (by
          exact_mod_cast hqanti (ULift.down_le.mpr hab.2)) }
  have hfst : Tendsto (fun ik : J => ik.1) atTop atTop := by
    rw [← prod_atTop_atTop_eq]
    exact tendsto_fst
  have hsnd : Tendsto (fun ik : J => ik.2.down) atTop atTop := by
    refine tendsto_atTop_atTop.mpr fun b => ?_
    obtain ⟨i₀⟩ := D.nonempty
    exact ⟨(i₀, ⟨b⟩), fun a ha => ULift.down_le.mpr ha.2⟩
  refine ⟨⟨v₀, fun hbot => hv₀ ?_⟩, E, ?_, fun v => ?_⟩
  · rcases EReal.add_eq_bot_iff.mp hbot with h1 | h1
    · exact h1
    · exact absurd h1 (EReal.coe_ne_bot c)
  · change Tendsto (fun ik : J => ((D.term ik.1).translate (q ik.2.down)).numericalClass p)
      atTop _
    simp only [RationalGFPackage.translate_numericalClass]
    exact hclass.comp hfst
  · change Tendsto (fun ik : J => ((D.term ik.1).translate (q ik.2.down)).eval p v) atTop _
    simp only [RationalGFPackage.translate_eval]
    have h1 : Tendsto (fun ik : J => (D.term ik.1).eval p v) atTop (𝓝 (φ v)) :=
      (hlim v).comp hfst
    have h2 : Tendsto (fun ik : J => (((q ik.2.down : ℚ) : ℝ) : EReal)) atTop (𝓝 (c : EReal)) :=
      (continuous_coe_real_ereal.tendsto c).comp (hqlim.comp hsnd)
    exact (EReal.continuousAt_add (Or.inr (EReal.coe_ne_bot c))
      (Or.inr (EReal.coe_ne_top c))).tendsto.comp (h1.prodMk_nhds h2)

end SGPT.NAPotential.BJ.Printed
