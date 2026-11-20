import SGPT.PSH.SourcePlurithinNeighborhood
import SGPT.PSH.AtlasQPSHAddition

/-!
# Normalizing the witness of thinness (`rmk:cstthindef`)

Source: `rmk:cstthindef` of the chapter *Plurisubharmonic functions*, attached to the
definition of thin sets `def:pshfunctions:L691` (formalized as `SGPT.PSH.sourceThinAt`).

In the second case of the definition (`x ∈ closure E` and a local psh function `φ` on an
open neighbourhood `U` of `x` with `limsup_{(U ∩ E) \ {x} ∋ y → x} φ(y) < φ(x)`), one can always
arrange `φ|_{(E \ {x}) ∩ U} = 0`: after assuming `φ ≤ 0` and choosing `C < 0` with
`limsup < C < φ(x)`, the function `ψ = (-C)⁻¹ (φ ∨ C) + 1` does the job on a smaller `U`.

Main declarations:

* `SGPT.PSH.identityAtlas_isPSHOn_const` — real constants are psh on open sets;
* `SGPT.PSH.exists_nonpos_shift_nhds` — the reduction "we may assume `φ ≤ 0`";
* `SGPT.PSH.book_thin_normalization` — the book's function `ψ = (-C)⁻¹ (φ ∨ C) + 1` vanishes on
  `(E \ {x}) ∩ U'` for a smaller neighbourhood `U'`, is psh there and still witnesses thinness;
* `SGPT.PSH.exists_thin_witness_zero_on_set` — the remark's claim: the thinness witness can be
  chosen to vanish on `(E \ {x}) ∩ U'`;
* `SGPT.PSH.sourceThinAt_iff_zero_witness` — hence thinness is equivalent to the normalized
  definition.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.PSH

open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology

variable {n : ℕ}

open VariableComplexAtlas in
/-- Every real constant is plurisubharmonic on every open subset of `ℂⁿ`. -/
theorem identityAtlas_isPSHOn_const (a : ℝ) {U : Set (ComplexModel n)} (hU : IsOpen U) :
    (identityAtlas n).IsPSHOn (fun _ => (a : EReal)) U := by
  intro x hx
  obtain ⟨r, hr, hb⟩ := Metric.isOpen_iff.mp hU x hx
  refine ⟨(), mem_univ _, Metric.ball x r, Metric.isOpen_ball, Metric.isConnected_ball hr,
    ?_, ?_, ?_⟩
  · intro z hz
    exact ⟨mem_univ _, hb hz⟩
  · exact Metric.mem_ball_self hr
  · exact pshOn_real_const a ⟨x, Metric.mem_ball_self hr⟩

/-- The reduction "we may assume `φ ≤ 0`" of `rmk:cstthindef`: on a smaller open neighbourhood
of `x` the psh function `φ - M` is nonpositive for a suitable real `M` (the limsup gap is
preserved by the shift, see `exists_thin_witness_zero_on_set`). -/
theorem exists_nonpos_shift_nhds {U : Set (ComplexModel n)} {u : ComplexModel n → EReal}
    (hU : IsOpen U) {x : ComplexModel n} (hxU : x ∈ U)
    (hu : (VariableComplexAtlas.identityAtlas n).IsPSHOn u U) :
    ∃ (U₁ : Set (ComplexModel n)) (M : ℝ), IsOpen U₁ ∧ U₁ ⊆ U ∧ x ∈ U₁ ∧
      ∀ y ∈ U₁, u y - (M : EReal) ≤ 0 := by
  have hne : u x ≠ ⊤ := hu.ne_top hxU
  obtain ⟨M, hM⟩ : ∃ M : ℝ, u x < (M : EReal) := by
    rcases EReal.exists_between_coe_real (lt_top_iff_ne_top.mpr hne) with ⟨M, hM, _⟩
    exact ⟨M, hM⟩
  have husc : UpperSemicontinuousOn u U := by
    have h := hu.chartPlurisubharmonic ()
    have hcoord : (VariableComplexAtlas.identityAtlas n).coordinate u () = u := rfl
    have hset : ((VariableComplexAtlas.identityAtlas n).chart ()).target ∩
        ((VariableComplexAtlas.identityAtlas n).chart ()).symm ⁻¹' U = U := by
      ext z
      exact ⟨fun h => h.2, fun h => ⟨mem_univ _, h⟩⟩
    rw [hcoord, hset] at h
    exact h.upperSemicontinuousOn
  have hev : ∀ᶠ y in 𝓝 x, u y < (M : EReal) := by
    have h := husc x hxU (M : EReal) hM
    rwa [nhdsWithin_eq_nhds.2 (hU.mem_nhds hxU)] at h
  obtain ⟨W, hWsub, hW, hxW⟩ := mem_nhds_iff.mp hev
  refine ⟨U ∩ W, M, hU.inter hW, inter_subset_left, ⟨hxU, hxW⟩, ?_⟩
  intro y hy
  have hlt : u y < (M : EReal) := hWsub hy.2
  rw [EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot M)) (Or.inl (EReal.coe_ne_top M)),
    zero_add]
  exact hlt.le

/-- The book's normalization in `rmk:cstthindef`. Let `φ` be psh on the open neighbourhood `U`
of `x`, and let `C < 0` with `limsup_{(U ∩ E) \ {x} ∋ y → x} φ(y) < C < φ(x)`. Then on a smaller
open neighbourhood `U'` of `x` the function `ψ = (-C)⁻¹ (φ ∨ C) + 1` is psh, vanishes on
`(U' ∩ E) \ {x}`, and still satisfies the thinness inequality at `x`. -/
theorem book_thin_normalization (Ω : Opens (ComplexModel n)) (E : Set Ω) (x : Ω)
    {U : Set (ComplexModel n)} {u : ComplexModel n → EReal}
    (hU : IsOpen U) (hxU : x.val ∈ U)
    (hu : (VariableComplexAtlas.identityAtlas n).IsPSHOn u U)
    {C : ℝ} (hC : C < 0)
    (hlt : limsup (fun y : Ω ↦ u y.val) (𝓝[((Subtype.val ⁻¹' U ∩ E) \ {x})] x) < (C : EReal))
    (hCx : (C : EReal) < u x.val) :
    ∃ U' : Set (ComplexModel n), IsOpen U' ∧ U' ⊆ U ∧ x.val ∈ U' ∧
      (VariableComplexAtlas.identityAtlas n).IsPSHOn
        (fun y => (((-C)⁻¹ : ℝ) : EReal) * max (u y) (C : EReal) + 1) U' ∧
      (∀ y ∈ (Subtype.val ⁻¹' U' ∩ E) \ {x},
        (((-C)⁻¹ : ℝ) : EReal) * max (u y.val) (C : EReal) + 1 = 0) ∧
      limsup (fun y : Ω ↦ (((-C)⁻¹ : ℝ) : EReal) * max (u y.val) (C : EReal) + 1)
          (𝓝[((Subtype.val ⁻¹' U' ∩ E) \ {x})] x) <
        (((-C)⁻¹ : ℝ) : EReal) * max (u x.val) (C : EReal) + 1 := by
  set ψ : ComplexModel n → EReal :=
    fun y => (((-C)⁻¹ : ℝ) : EReal) * max (u y) (C : EReal) + 1 with hψ
  -- the region where the original function is below `C` along the set
  have hevent := eventually_lt_of_limsup_lt hlt
  have hevent' : ∀ᶠ y in 𝓝 x,
      y ∈ (Subtype.val ⁻¹' U ∩ E) \ {x} → u y.val < (C : EReal) :=
    eventually_nhdsWithin_iff.mp hevent
  obtain ⟨W, hWsub, hW, hxW⟩ := mem_nhds_iff.mp hevent'
  -- `W` is open in the subtype `Ω`; pull it back to an open subset of `ℂⁿ`
  obtain ⟨W', hW', hWW'⟩ := isOpen_induced_iff.mp hW
  have hΩ : IsOpen (Ω : Set (ComplexModel n)) := Ω.isOpen
  let U' : Set (ComplexModel n) := U ∩ (W' ∩ Ω)
  have hU' : IsOpen U' := hU.inter (hW'.inter hΩ)
  have hxW' : x.val ∈ W' := by
    have : x ∈ Subtype.val ⁻¹' W' := by rw [hWW']; exact hxW
    exact this
  have hxU' : x.val ∈ U' := ⟨hxU, hxW', x.property⟩
  have hU'U : U' ⊆ U := inter_subset_left
  have hinv : 0 < (-C)⁻¹ := inv_pos.mpr (neg_pos.mpr hC)
  have hC0 : C ≠ 0 := ne_of_lt hC
  -- plurisubharmonicity of `ψ` on `U'`
  have huU' := hu.mono_open hU hU' hU'U
  have hmax := huU'.max (identityAtlas_isPSHOn_const C hU') hU'
  have hsmul := hmax.pos_smul hinv
  have hpsh : (VariableComplexAtlas.identityAtlas n).IsPSHOn ψ U' :=
    hsmul.add (identityAtlas_isPSHOn_const 1 hU') hU'
  -- vanishing on the set
  have hzero : ∀ y ∈ (Subtype.val ⁻¹' U' ∩ E) \ {x}, ψ y.val = 0 := by
    rintro y ⟨⟨hyU', hyE⟩, hyx⟩
    have hyW : y ∈ W := by
      have : y ∈ Subtype.val ⁻¹' W' := hyU'.2.1
      rw [hWW'] at this
      exact this
    have hy : u y.val < (C : EReal) := hWsub hyW ⟨⟨hyU'.1, hyE⟩, hyx⟩
    have hm : max (u y.val) (C : EReal) = (C : EReal) := max_eq_right hy.le
    simp only [hψ, hm]
    rw [← EReal.coe_mul, ← EReal.coe_one, ← EReal.coe_add]
    have : (-C)⁻¹ * C + 1 = 0 := by
      rw [inv_neg, neg_mul, inv_mul_cancel₀ hC0]
      norm_num
    rw [this]
    rfl
  -- the value at `x` is positive
  have hpos : (0 : EReal) < ψ x.val := by
    have hfin : u x.val ≠ ⊤ := hu.ne_top hxU
    have hbot : u x.val ≠ ⊥ := ne_bot_of_gt hCx
    obtain ⟨a, ha⟩ : ∃ a : ℝ, u x.val = (a : EReal) := ⟨(u x.val).toReal,
      (EReal.coe_toReal hfin hbot).symm⟩
    have hCa : C < a := by rw [ha] at hCx; exact EReal.coe_lt_coe_iff.mp hCx
    have hm : max (u x.val) (C : EReal) = (a : EReal) := by
      rw [ha]; exact max_eq_left (EReal.coe_le_coe_iff.mpr hCa.le)
    simp only [hψ, hm]
    rw [← EReal.coe_mul, ← EReal.coe_one, ← EReal.coe_add]
    apply EReal.coe_pos.mpr
    have h1 : (-C)⁻¹ * a + 1 = (a - C) / (-C) := by
      rw [eq_div_iff (neg_ne_zero.mpr hC0)]
      rw [add_mul, mul_comm, ← mul_assoc, mul_inv_cancel₀ (neg_ne_zero.mpr hC0)]
      ring
    rw [h1]
    exact div_pos (by linarith) (by linarith)
  -- the limsup of `ψ` along the set is at most `0`
  have hls : limsup (fun y : Ω ↦ ψ y.val) (𝓝[((Subtype.val ⁻¹' U' ∩ E) \ {x})] x) ≤ 0 := by
    apply limsup_le_of_le
    · isBoundedDefault
    · exact eventually_nhdsWithin_of_forall fun y hy => (hzero y hy).le
  exact ⟨U', hU', hU'U, hxU', hpsh, hzero, hls.trans_lt hpos⟩

/-- The claim of `rmk:cstthindef`: in the second case of `def:pshfunctions:L691` the thinness
witness can be chosen to vanish identically on `(E \ {x}) ∩ U'` for an open neighbourhood `U'`
of `x`, while still satisfying the thinness inequality. -/
theorem exists_thin_witness_zero_on_set (Ω : Opens (ComplexModel n)) (E : Set Ω) (x : Ω)
    {U : Set (ComplexModel n)} {u : ComplexModel n → EReal}
    (hU : IsOpen U) (hUΩ : U ⊆ Ω) (hxU : x.val ∈ U)
    (hu : (VariableComplexAtlas.identityAtlas n).IsPSHOn u U)
    (hgap : limsup (fun y : Ω ↦ u y.val) (𝓝[((Subtype.val ⁻¹' U ∩ E) \ {x})] x) < u x.val) :
    ∃ (U' : Set (ComplexModel n)) (ψ : ComplexModel n → EReal),
      IsOpen U' ∧ U' ⊆ Ω ∧ x.val ∈ U' ∧
      (VariableComplexAtlas.identityAtlas n).IsPSHOn ψ U' ∧
      (∀ y ∈ (Subtype.val ⁻¹' U' ∩ E) \ {x}, ψ y.val = 0) ∧
      limsup (fun y : Ω ↦ ψ y.val) (𝓝[((Subtype.val ⁻¹' U' ∩ E) \ {x})] x) < ψ x.val := by
  -- first reduce to `φ ≤ 0` by subtracting a constant on a smaller neighbourhood
  obtain ⟨U₁, M, hU₁, hU₁U, hxU₁, hle⟩ := exists_nonpos_shift_nhds hU hxU hu
  set v : ComplexModel n → EReal := fun y => u y + ((-M : ℝ) : EReal) with hv
  have hvsub : ∀ y, v y = u y - (M : EReal) := by
    intro y; simp only [hv, sub_eq_add_neg, EReal.coe_neg]
  have hv1 : (VariableComplexAtlas.identityAtlas n).IsPSHOn v U₁ :=
    (hu.mono_open hU hU₁ hU₁U).add (identityAtlas_isPSHOn_const (-M) hU₁) hU₁
  -- the gap survives the restriction to `U₁` and the shift
  have hsub : (Subtype.val ⁻¹' U₁ ∩ E) \ {x} ⊆ (Subtype.val ⁻¹' U ∩ E) \ {x} :=
    fun y hy => ⟨⟨hU₁U hy.1.1, hy.1.2⟩, hy.2⟩
  have hgap₁ : limsup (fun y : Ω ↦ u y.val) (𝓝[((Subtype.val ⁻¹' U₁ ∩ E) \ {x})] x) <
      u x.val :=
    (limsup_le_limsup_of_le (nhdsWithin_mono x hsub)).trans_lt hgap
  have hshift : limsup (fun y : Ω ↦ v y.val)
      (𝓝[((Subtype.val ⁻¹' U₁ ∩ E) \ {x})] x) < v x.val := by
    obtain ⟨c, hc1, hc2⟩ := EReal.exists_between_coe_real hgap₁
    have hev := eventually_lt_of_limsup_lt hc1
    have hb : limsup (fun y : Ω ↦ v y.val) (𝓝[((Subtype.val ⁻¹' U₁ ∩ E) \ {x})] x) ≤
        ((c - M : ℝ) : EReal) := by
      apply limsup_le_of_le
      · isBoundedDefault
      · filter_upwards [hev] with y hy
        rw [hv]
        simp only
        rw [EReal.coe_sub, sub_eq_add_neg, ← EReal.coe_neg]
        exact add_le_add hy.le le_rfl
    refine hb.trans_lt ?_
    rw [hv]
    simp only
    rw [EReal.coe_sub, sub_eq_add_neg, ← EReal.coe_neg]
    have hfin : u x.val ≠ ⊤ := hu.ne_top hxU
    obtain ⟨a, ha⟩ : ∃ a : ℝ, u x.val = (a : EReal) := ⟨(u x.val).toReal,
      (EReal.coe_toReal hfin (ne_bot_of_gt hc2)).symm⟩
    rw [ha] at hc2 ⊢
    rw [← EReal.coe_add, ← EReal.coe_add]
    exact EReal.coe_lt_coe_iff.mpr (by have := EReal.coe_lt_coe_iff.mp hc2; linarith)
  -- choose `C < 0` between the limsup and `v x ≤ 0`
  obtain ⟨C, hC1, hC2⟩ := EReal.exists_between_coe_real hshift
  have hvx : v x.val ≤ 0 := by rw [hvsub]; exact hle x.val hxU₁
  have hC : C < 0 := EReal.coe_lt_coe_iff.mp (hC2.trans_le (by simpa using hvx))
  obtain ⟨U', hU', hU'U₁, hxU', hpsh, hzero, hgap'⟩ :=
    book_thin_normalization Ω E x hU₁ hxU₁ hv1 hC hC1 hC2
  exact ⟨U', _, hU', fun y hy => hUΩ (hU₁U (hU'U₁ hy)), hxU', hpsh, hzero, hgap'⟩

/-- `rmk:cstthindef`, packaged: thinness at `x` is equivalent to the normalized form of the
definition, in which the witnessing psh function vanishes on `(E \ {x}) ∩ U`. -/
theorem sourceThinAt_iff_zero_witness (Ω : Opens (ComplexModel n)) (E : Set Ω) (x : Ω) :
    sourceThinAt Ω E x ↔
      x ∉ closure E ∨ (x ∈ closure E ∧
        ∃ (U : Set (ComplexModel n)) (u : ComplexModel n → EReal),
          IsOpen U ∧ U ⊆ Ω ∧ x.val ∈ U ∧
          (VariableComplexAtlas.identityAtlas n).IsPSHOn u U ∧
          (∀ y ∈ (Subtype.val ⁻¹' U ∩ E) \ {x}, u y.val = 0) ∧
          limsup (fun y : Ω ↦ u y.val) (𝓝[((Subtype.val ⁻¹' U ∩ E) \ {x})] x) < u x.val) := by
  constructor
  · rintro (hx | ⟨hx, U, u, hU, hUΩ, hxU, hu, hgap⟩)
    · exact Or.inl hx
    · exact Or.inr ⟨hx, exists_thin_witness_zero_on_set Ω E x hU hUΩ hxU hu hgap⟩
  · rintro (hx | ⟨hx, U, u, hU, hUΩ, hxU, hu, _, hgap⟩)
    · exact Or.inl hx
    · exact Or.inr ⟨hx, U, u, hU, hUΩ, hxU, hu, hgap⟩

end SGPT.PSH
