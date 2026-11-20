import SGPT.Okounkov.TranscendentalWNLegendreInverse
import SGPT.Foundations.Analysis.PlurisubharmonicAE
import SGPT.Foundations.Analysis.FirstPass.ManifoldPluripolar
import SGPT.Foundations.Analysis.FirstPass.Envelopes
import SGPT.Foundations.Analysis.FirstPass.ERealChordUSC
import SGPT.Foundations.Analysis.Pending.ThetaPshCodimTwoExtension
import SGPT.Foundations.Analysis.Pending.MeteredDivisorPositivity

/-!
# Restricting a Legendre supremum to a pluripolar set (package WN-VF3)

Blueprint node `tok-wn-vf3:restriction-abstract` (chapter `claude-tok-wn-vf3`), the abstract
core of `tok-wn:formula-E`; source D. Witt Nyström, *Deformations of Kähler manifolds to normal
bundles and restricted volumes of big classes*, arXiv:2103.03660 (WN21), end of §4: "Thus by
Lemma 3.2 we get that `sup_{λ ∈ [0,b]} φ_λ` is u.s.c. and then also quasi-psh in a neighbourhood
… This means that the equality `ũ = sup_{λ ∈ [0,b]} φ_λ` extends from `X × ℂ*` to `ℰ \ A`".

Let `U` be `θ`-psh on a complex manifold `M` and suppose that, off a locally pluripolar set `A`
and near a point `p ∈ A`, `U = sup_{λ ∈ [a, b]} Φ_λ` for a concave family `Φ_λ`.  Suppose that
for `λ ∈ [a, c]` (`a < c ≤ b`) `Φ_λ` agrees off `A` with a quasi-psh function `Ψ_λ`
(`θ_λ`-psh plus continuous) which is locally bounded near `p`, and that for `λ ∈ (c, b]` the
`Φ_λ` tend to `-∞` at `p`.  Then

  `U(p) = sup_{λ ∈ [a, c]} Ψ_λ(p)`   (`eq_iSup_of_eq_iSup_off`).

The proof avoids any plurisubharmonicity of the supremum on `A`:

* `≥`: each `Ψ_λ ≤ U` off the null set `A`, hence at `p`, by the a.e. comparison principle for
  psh functions against an upper semicontinuous function (`le_of_le_off_pluripolar`, from TN's
  `PlurisubharmonicOn.le_of_ae_le`);
* `≤`: `U` is below the upper regularization `G*` of `G = sup_λ Φ_λ` (extended by `-∞` on `A`),
  again by the a.e. comparison; and `G*(p) ≤ sup_{λ ≤ c} Ψ_λ(p)` by WN21 Lemma 3.2
  (`upperSemicontinuousAt_iSup_concave`, `tok-wn:legendre-usc`) applied at `p` to the family
  equal to `Φ_λ` off `A` and, on `A`, to the constant `sup_{λ ≤ c} Ψ_λ(p)` for `λ ≤ c` and to
  `-∞` for `λ > c` (a concave step family), so that no concavity on `A` is needed.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Okounkov.TranscendentalWN

open Set Filter MeasureTheory
open scoped Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending

/-! ### Concave step families -/

section Step

variable {X : Type*}

/-- The step family `λ ↦ K` for `λ ≤ c`, `-∞` for `λ > c` (`K` finite) is concave. -/
theorem isConcaveFamilyAt_step {v : ℝ → X → EReal} {a b c : ℝ} {y : X} (k : ℝ)
    (hv : ∀ lam, v lam y = if lam ≤ c then (k : EReal) else ⊥) :
    IsConcaveFamilyAt v (Icc a b) y := by
  intro l₁ _ l₂ _ t ht0 ht1
  rw [hv, hv, hv]
  by_cases h₁ : l₁ ≤ c <;> by_cases h₂ : l₂ ≤ c
  · have hle : t * l₁ + (1 - t) * l₂ ≤ c := by nlinarith
    rw [if_pos h₁, if_pos h₂, if_pos hle, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
    exact le_of_eq (by congr 1; ring)
  · rw [if_pos h₁, if_neg h₂]
    rcases ht1.eq_or_lt with rfl | ht1'
    · have hle : 1 * l₁ + (1 - 1) * l₂ ≤ c := by simpa using h₁
      rw [if_pos hle, sub_self, EReal.coe_zero, zero_mul, add_zero, EReal.coe_one, one_mul]
    · rw [EReal.coe_mul_bot_of_pos (by linarith), EReal.add_bot]
      exact bot_le
  · rw [if_neg h₁, if_pos h₂]
    rcases ht0.eq_or_lt with rfl | ht0'
    · have hle : 0 * l₁ + (1 - 0) * l₂ ≤ c := by simpa using h₂
      rw [if_pos hle, EReal.coe_zero, zero_mul, zero_add, sub_zero, EReal.coe_one, one_mul]
    · rw [EReal.coe_mul_bot_of_pos ht0', EReal.bot_add]
      exact bot_le
  · rw [if_neg h₁, if_neg h₂]
    rcases ht0.eq_or_lt with rfl | ht0'
    · have hlt : ¬ (0 * l₁ + (1 - 0) * l₂ ≤ c) := by simpa using h₂
      rw [if_neg hlt, EReal.coe_zero, zero_mul, zero_add, sub_zero, EReal.coe_one, one_mul]
    · rw [EReal.coe_mul_bot_of_pos ht0', EReal.bot_add]
      exact bot_le

/-- Adding a real constant to a concave family keeps it concave. -/
theorem IsConcaveFamilyAt.add_const {v : ℝ → X → EReal} {I : Set ℝ} {y : X}
    (h : IsConcaveFamilyAt v I y) (r : ℝ) :
    IsConcaveFamilyAt (fun lam z => v lam z + (r : EReal)) I y := by
  intro l₁ hl₁ l₂ hl₂ t ht0 ht1
  have h1 := h l₁ hl₁ l₂ hl₂ t ht0 ht1
  simp only
  rw [ereal_coe_mul_add_coe ht0, ereal_coe_mul_add_coe (by linarith : (0 : ℝ) ≤ 1 - t),
    add_add_add_comm, ← EReal.coe_add]
  have e : t * r + (1 - t) * r = r := by ring
  rw [e]
  exact add_le_add h1 le_rfl

end Step

/-! ### Comparison off a pluripolar set -/

section Manifold

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- Cancelling a real summand in an `EReal` inequality. -/
theorem ereal_le_of_add_coe_le_add_coe {x y : EReal} {r : ℝ}
    (h : x + (r : EReal) ≤ y + (r : EReal)) : x ≤ y := by
  have h2 := add_le_add h (le_refl ((-r : ℝ) : EReal))
  rwa [MeteredDivisorPositivity.add_coe_add_neg_coe,
    MeteredDivisorPositivity.add_coe_add_neg_coe] at h2

/-- **Comparison off a pluripolar set.**  If `u` is `θ`-psh on `M`, `v` is upper semicontinuous
at the points of an open set `N`, and `u ≤ v` on `N` off a locally pluripolar set `A`, then
`u ≤ v` on `N` (in a chart, `u + ρ` is psh and `v + ρ` is upper semicontinuous, and `A` is
Lebesgue-null: TN's `PlurisubharmonicOn.le_of_ae_le`). -/
theorem le_of_le_off_pluripolar {θ : SmoothRealForm n M 2} {u v : M → EReal}
    (hu : ThetaPlurisubharmonic θ u) {N : Set M} (hN : IsOpen N)
    (hv : ∀ y ∈ N, UpperSemicontinuousAt v y) {A : Set M}
    (hA : ManifoldLocallyPluripolar (n := n) A)
    (hle : ∀ y ∈ N, y ∉ A → u y ≤ v y) {y : M} (hy : y ∈ N) : u y ≤ v y := by
  set e := complexChartAt (n := n) y with he
  have hye : y ∈ e.val.source := mem_complexChartAt_source y
  obtain ⟨W, ρ, hzW, hρ, hpsh⟩ := hu e (e.val y) (e.val.map_source hye)
  set W' : Set (ComplexModel n) := W ∩ (e.val.target ∩ e.val.symm ⁻¹' N) with hW'
  have hW'o : IsOpen W' := hρ.1.inter (e.val.isOpen_inter_preimage_symm hN)
  have hyW' : e.val y ∈ W' :=
    ⟨hzW, e.val.map_source hye, by simpa [e.val.left_inv hye] using hy⟩
  have hU : PlurisubharmonicOn (fun z => chartFunction u e z + (ρ z : EReal)) W' :=
    hpsh.mono inter_subset_left
  have hρc : ContinuousOn ρ W := hρ.2.2.1.continuousOn
  have hV : UpperSemicontinuousOn (fun z => chartFunction v e z + (ρ z : EReal)) W' := by
    intro z hz
    apply UpperSemicontinuousAt.upperSemicontinuousWithinAt
    have hzt : z ∈ e.val.target := hz.2.1
    have h1 : UpperSemicontinuousAt (chartFunction v e) z := by
      intro r hr
      exact (e.val.continuousAt_symm hzt).eventually (hv _ hz.2.2 r hr)
    exact ThetaPshCodimTwoExtension.upperSemicontinuousAt_add_real h1
      (hρc.continuousAt (hρ.1.mem_nhds hz.1))
  have hnull : volume (pluripolarChartSet A e) = 0 := hA.chart_measure_eq_zero e volume
  have hae : ∀ᵐ z ∂(volume.restrict W'), chartFunction u e z + (ρ z : EReal) ≤
      chartFunction v e z + (ρ z : EReal) := by
    rw [ae_restrict_iff' hW'o.measurableSet]
    have h0 : ∀ᵐ z ∂(volume : Measure (ComplexModel n)), z ∉ pluripolarChartSet A e :=
      measure_eq_zero_iff_ae_notMem.mp hnull
    filter_upwards [h0] with z hzA hzW'
    have hzA' : e.val.symm z ∉ A := fun h => hzA ⟨hzW'.2.1, h⟩
    exact add_le_add (hle _ hzW'.2.2 hzA') le_rfl
  have h := hU.le_of_ae_le hW'o hV volume hae _ hyW'
  simp only [chartFunction, e.val.left_inv hye] at h
  exact ereal_le_of_add_coe_le_add_coe h

/-! ### The restriction of a Legendre supremum -/

/-- **The value of a Legendre supremum on a pluripolar set** (WN21 §4, the extension of
`ũ = sup_λ φ_λ` from `X × ℂ*` to `ℰ \ A`, via WN21 Lemma 3.2).  Let `U` be `θ`-psh, `A` locally
pluripolar, `N` an open neighbourhood of `p ∈ A`, `a < c ≤ b`, and suppose on `N \ A`:
`U = sup_{λ ∈ [a,b]} Φ_λ`, the family `Φ_λ` is concave with values `≠ ⊤`; for `λ ∈ [a, c]`,
`Φ_λ = Ψ_λ` with `Ψ_λ = Q_λ + S_λ` on `N` (`Q_λ` psh for some form, `S_λ` real continuous) and
`Ψ_λ` locally bounded near `p`; for `λ ∈ (c, b]`, `Φ_λ → -∞` at `p`.  Then
`U(p) = sup_{λ ∈ [a, c]} Ψ_λ(p)`. -/
theorem eq_iSup_of_eq_iSup_off {θ : SmoothRealForm n M 2} {U : M → EReal}
    (hU : ThetaPlurisubharmonic θ U) {A : Set M} (hA : ManifoldLocallyPluripolar (n := n) A)
    {N : Set M} (hN : IsOpen N) {p : M} (hpN : p ∈ N) (hpA : p ∈ A)
    {a c b : ℝ} (hac : a < c) (hcb : c ≤ b) {Φ Ψ : ℝ → M → EReal}
    (hdual : ∀ y ∈ N, y ∉ A → U y = ⨆ lam ∈ Icc a b, Φ lam y)
    (hconc : ∀ y ∈ N, y ∉ A → IsConcaveFamilyAt Φ (Icc a b) y)
    (hne : ∀ y ∈ N, y ∉ A → ∀ lam ∈ Icc a b, Φ lam y ≠ ⊤)
    (hΨΦ : ∀ lam ∈ Icc a c, ∀ y ∈ N, y ∉ A → Ψ lam y = Φ lam y)
    (hΨ : ∀ lam ∈ Icc a c, ∃ (θ' : SmoothRealForm n M 2) (Q : M → EReal) (S : M → ℝ),
      ThetaPlurisubharmonic θ' Q ∧ ContinuousOn S N ∧ ∀ y ∈ N, Ψ lam y = Q y + (S y : EReal))
    (hbdd : ∀ lam ∈ Icc a c, ∃ C : ℝ, ∀ᶠ y in 𝓝 p,
      ((-C : ℝ) : EReal) ≤ Ψ lam y ∧ Ψ lam y ≤ (C : EReal))
    (hbot : ∀ lam ∈ Ioc c b, ∀ C : ℝ, ∀ᶠ y in 𝓝 p, y ∉ A → Φ lam y < (C : EReal)) :
    U p = ⨆ lam ∈ Icc a c, Ψ lam p := by
  have hUusc : UpperSemicontinuous U := hU.quasiPlurisubharmonic.upperSemicontinuous
  -- each `Ψ_λ` is upper semicontinuous on `N` and `≤ U`
  have hΨusc : ∀ lam ∈ Icc a c, ∀ y ∈ N, UpperSemicontinuousAt (Ψ lam) y := by
    intro lam hl y hy
    obtain ⟨θ', Q, S, hQ, hS, hΨeq⟩ := hΨ lam hl
    have h1 : UpperSemicontinuousAt (fun z => Q z + (S z : EReal)) y :=
      ThetaPshCodimTwoExtension.upperSemicontinuousAt_add_real
        (hQ.quasiPlurisubharmonic.upperSemicontinuous y) (hS.continuousAt (hN.mem_nhds hy))
    intro r hr
    rw [hΨeq y hy] at hr
    filter_upwards [h1 r hr, hN.mem_nhds hy] with z hz hzN
    rw [hΨeq z hzN]
    exact hz
  have hge : ∀ lam ∈ Icc a c, Ψ lam p ≤ U p := by
    intro lam hl
    obtain ⟨θ', Q, S, hQ, hS, hΨeq⟩ := hΨ lam hl
    have hv : ∀ y ∈ N, UpperSemicontinuousAt (fun z => U z + ((-S z : ℝ) : EReal)) y :=
      fun y hy => ThetaPshCodimTwoExtension.upperSemicontinuousAt_add_real (hUusc y)
        (hS.continuousAt (hN.mem_nhds hy)).neg
    have hle : ∀ y ∈ N, y ∉ A → Q y ≤ U y + ((-S y : ℝ) : EReal) := by
      intro y hy hyA
      have h1 : Ψ lam y ≤ U y := by
        rw [hΨΦ lam hl y hy hyA, hdual y hy hyA]
        exact le_iSup₂ (f := fun lam _ => Φ lam y) lam ⟨hl.1, hl.2.trans hcb⟩
      rw [hΨeq y hy] at h1
      have h2 := add_le_add h1 (le_refl ((-S y : ℝ) : EReal))
      rwa [MeteredDivisorPositivity.add_coe_add_neg_coe] at h2
    have hp := le_of_le_off_pluripolar hQ hN hv hA hle hpN
    rw [hΨeq p hpN]
    have h2 := add_le_add hp (le_refl ((S p : ℝ) : EReal))
    rwa [show ((-S p : ℝ) : EReal) = ((-(S p) : ℝ) : EReal) from rfl,
      add_assoc, ← EReal.coe_add, neg_add_cancel, EReal.coe_zero, add_zero] at h2
  refine le_antisymm ?_ (iSup₂_le hge)
  -- the upper bound
  set M₀ : EReal := ⨆ lam ∈ Icc a c, Ψ lam p with hM₀
  by_cases hMtop : M₀ = ⊤
  · rw [hMtop]; exact le_top
  obtain ⟨Ca, hCa⟩ := hbdd a ⟨le_rfl, hac.le⟩
  have hΨa : ((-Ca : ℝ) : EReal) ≤ Ψ a p := hCa.self_of_nhds.1
  have hMbot : M₀ ≠ ⊥ := by
    refine ne_bot_of_le_ne_bot (EReal.coe_ne_bot (-Ca)) (hΨa.trans ?_)
    exact le_iSup₂ (f := fun lam _ => Ψ lam p) a ⟨le_rfl, hac.le⟩
  set k : ℝ := M₀.toReal with hk
  have hMk : M₀ = (k : EReal) := (EReal.coe_toReal hMtop hMbot).symm
  -- the modified family
  classical
  set v : ℝ → M → EReal := fun lam y =>
    if y ∈ A then (if lam ≤ c then (k : EReal) else ⊥) else Φ lam y with hvdef
  have hNp : N ∈ 𝓝 p := hN.mem_nhds hpN
  have hvconc : ∀ᶠ y in 𝓝 p, IsConcaveFamilyAt v (Icc a b) y := by
    filter_upwards [hNp] with y hy
    by_cases hyA : y ∈ A
    · exact isConcaveFamilyAt_step (c := c) k fun lam => by simp only [hvdef, if_pos hyA]
    · intro l₁ hl₁ l₂ hl₂ t ht0 ht1
      simp only [hvdef, if_neg hyA]
      exact hconc y hy hyA l₁ hl₁ l₂ hl₂ t ht0 ht1
  have hvne : ∀ᶠ y in 𝓝 p, ∀ lam ∈ Icc a b, v lam y ≠ ⊤ := by
    filter_upwards [hNp] with y hy lam hl
    by_cases hyA : y ∈ A
    · simp only [hvdef, if_pos hyA]
      split_ifs
      · exact EReal.coe_ne_top k
      · exact bot_ne_top
    · simp only [hvdef, if_neg hyA]
      exact hne y hy hyA lam hl
  have hvusc : ∀ lam ∈ Icc a b, UpperSemicontinuousAt (v lam) p := by
    intro lam hl r hr
    by_cases hlc : lam ≤ c
    · have hvp : v lam p = (k : EReal) := by simp only [hvdef, if_pos hpA, if_pos hlc]
      rw [hvp] at hr
      have hlc' : lam ∈ Icc a c := ⟨hl.1, hlc⟩
      have hΨp : Ψ lam p < r := by
        refine lt_of_le_of_lt ?_ hr
        rw [← hMk]
        exact le_iSup₂ (f := fun lam _ => Ψ lam p) lam hlc'
      filter_upwards [hΨusc lam hlc' p hpN r hΨp, hNp] with y hy hyN
      by_cases hyA : y ∈ A
      · simp only [hvdef, if_pos hyA, if_pos hlc]; exact hr
      · simp only [hvdef, if_neg hyA]
        rw [← hΨΦ lam hlc' y hyN hyA]; exact hy
    · have hlc' : lam ∈ Ioc c b := ⟨lt_of_not_ge hlc, hl.2⟩
      by_cases hrtop : r = ⊤
      · filter_upwards [hvne] with y hy
        rw [hrtop]; exact lt_top_iff_ne_top.mpr (hy lam hl)
      have hvp : v lam p = ⊥ := by simp only [hvdef, if_pos hpA, if_neg hlc]
      rw [hvp] at hr
      have hrbot : r ≠ ⊥ := ne_bot_of_gt hr
      have hrr : r = ((r.toReal : ℝ) : EReal) := (EReal.coe_toReal hrtop hrbot).symm
      filter_upwards [hbot lam hlc' r.toReal] with y hy
      by_cases hyA : y ∈ A
      · simp only [hvdef, if_pos hyA, if_neg hlc]; exact hr
      · simp only [hvdef, if_neg hyA]
        rw [hrr]; exact hy hyA
  have hvbdd : ∀ lam ∈ Icc a c, ∃ C : ℝ, ∀ᶠ y in 𝓝 p,
      ((-C : ℝ) : EReal) ≤ v lam y ∧ v lam y ≤ (C : EReal) := by
    intro lam hl
    obtain ⟨C, hC⟩ := hbdd lam hl
    refine ⟨max C |k|, ?_⟩
    filter_upwards [hC, hNp] with y hy hyN
    by_cases hyA : y ∈ A
    · simp only [hvdef, if_pos hyA, if_pos hl.2]
      constructor
      · rw [EReal.coe_le_coe_iff]
        have := neg_abs_le k; have := le_max_right C |k|; linarith
      · rw [EReal.coe_le_coe_iff]
        have := le_abs_self k; have := le_max_right C |k|; linarith
    · simp only [hvdef, if_neg hyA]
      rw [← hΨΦ lam hl y hyN hyA]
      constructor
      · refine le_trans ?_ hy.1
        rw [EReal.coe_le_coe_iff]; have := le_max_left C |k|; linarith
      · refine hy.2.trans ?_
        rw [EReal.coe_le_coe_iff]; exact le_max_left C |k|
  have hsusc := upperSemicontinuousAt_iSup_concave (le_refl a) hac hcb hvconc hvne hvusc hvbdd
  have hsp : (⨆ lam ∈ Icc a b, v lam p) = (k : EReal) := by
    apply le_antisymm
    · refine iSup₂_le fun lam _ => ?_
      by_cases hlc : lam ≤ c
      · simp only [hvdef, if_pos hpA, if_pos hlc]; exact le_rfl
      · simp only [hvdef, if_pos hpA, if_neg hlc]; exact bot_le
    · have h := le_iSup₂ (f := fun lam (_ : lam ∈ Icc a b) => v lam p) a
        (show a ∈ Icc a b from ⟨le_rfl, hac.le.trans hcb⟩)
      have hva : v a p = (k : EReal) := by simp only [hvdef, if_pos hpA, if_pos hac.le]
      rw [← hva]
      exact h
  -- the extended supremum and its regularization
  set G : M → EReal := fun y => if y ∈ A then ⊥ else ⨆ lam ∈ Icc a b, Φ lam y with hGdef
  have hGv : ∀ y, G y ≤ ⨆ lam ∈ Icc a b, v lam y := by
    intro y
    by_cases hyA : y ∈ A
    · simp only [hGdef, if_pos hyA]; exact bot_le
    · simp only [hGdef, hvdef, if_neg hyA]; exact le_rfl
  have hGstar : uscRegularization G p ≤ (k : EReal) := by
    refine le_of_forall_gt fun r hr => ?_
    obtain ⟨r', hkr', hr'r⟩ := exists_between hr
    have hV : {y | (⨆ lam ∈ Icc a b, v lam y) < r'} ∈ 𝓝 p := by
      exact hsusc r' (by show (⨆ lam ∈ Icc a b, v lam p) < r'; rw [hsp]; exact hkr')
    refine lt_of_le_of_lt ((uscRegularization_le_localSup G hV).trans ?_) hr'r
    exact iSup₂_le fun y hy => ((hGv y).trans (le_of_lt hy))
  have hUG : U p ≤ uscRegularization G p := by
    refine le_of_le_off_pluripolar hU hN
      (fun y _ => upperSemicontinuous_uscRegularization G y) hA ?_ hpN
    intro y hy hyA
    rw [hdual y hy hyA]
    have : G y = ⨆ lam ∈ Icc a b, Φ lam y := by simp only [hGdef, if_neg hyA]
    rw [← this]
    exact le_uscRegularization G y
  rw [hMk]
  exact hUG.trans hGstar

end Manifold

end SGPT.Okounkov.TranscendentalWN
