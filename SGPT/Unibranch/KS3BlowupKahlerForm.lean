import SGPT.Unibranch.KS2KahlerSpace
import SGPT.Unibranch.KS2LeviEstimate
import SGPT.Unibranch.ComplexSpaceFormPullbackPotentials
import SGPT.Foundations.Analysis.Pending.PluriharmonicLogNorm
import SGPT.Foundations.Analysis.Pending.LogWeightFactorization

/-!
# A Kähler form on a blowup from adapted local charts

Lane KS3 (Kähler preservation under blowups, `def:unibranch:L212`).  Let `p : Y → X` be a
morphism of complex spaces, `C ⊆ X`, `U : X → ℝ` a function with `U > 0` exactly off `C`
(the *Blanchard weight*, `U = Σ_b χ_b |G_b|²` for local generators `G_b` of the ideal of `C`), and
`ω` a Kähler form on `X`.  A *good chart* (`GoodChart`) of `Y` is a local embedding `E` of `Y`
together with

* a holomorphic lift `P` of `p` into a local embedding of `X` on which `ω` restricts to a Kähler
  ambient form `v`;
* a holomorphic `t` (a local generator of `p^{-1} 𝓘_C`) and a smooth positive `R` with
  `U ∘ p = |t|² R` on `Y` (the factorization of the weight);
* holomorphic `h_k` vanishing on `Y` (equations of `Y`);
* the ideal-theoretic properties `t_gen`, `hadamard` of `t` (locally `t = f ∘ P` with `f`
  vanishing on `C`; every such `f ∘ P` is divisible by `t`) and density of `Y \ p^{-1}(C)`;
* a bound `ε₀` such that `P^*v + ddᶜ(ε log R + Σ_k |h_k|²)` is closed, of type `(1,1)` and
  strictly positive on the whole ambient open set for `0 < ε ≤ ε₀`.

The ambient forms `P^*v + ddᶜ(ε log R + Σ|h_k|²)` of all good charts agree on `Y` (`compatible`):
the `P^*v` parts are restrictions of `ω`, the `h_k` vanish on `Y`, and two weights differ by
`log |q|²` with `q` holomorphic and nonvanishing (from the factorization of `U`).  Hence
(`kahlerForm`) they define a smooth form `κ_ε` on `Y`, and (`isKahler_kahlerForm`) if finitely
many good charts cover `Y`, `κ_ε` is a Kähler form for `ε` below all their bounds.  This is the
`p^*ω + ε·(curvature of 𝒪(-E))` construction of a Kähler form on a blowup.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter TopologicalSpace CategoryTheory
open scoped Topology ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass

namespace SGPT.Unibranch.KS3BlowupKahlerForm

variable {X Y : SourceReducedComplexSpace} (p : Y ⟶ X) (Cset : Set X.obj.left)
  (U : X.obj.left → ℝ) (om : SpaceForm X 2)

/-- The ambient representative of the form `κ_ε` in a good chart. -/
def repOf {N M s : ℕ} (P : ComplexModel N → ComplexModel M) (v : AmbientForm M 2)
    (R : ComplexModel N → ℝ) (h : Fin s → ComplexModel N → ℂ) (ε : ℝ) : AmbientForm N 2 :=
  pullbackForm P v + smoothDDC (fun u => ε * Real.log (R u) + ∑ k, Complex.normSq (h k u))

/-- **A good chart of `Y`** (see the module docstring). -/
structure GoodChart where
  E : LocalEmbedding Y
  eX : LocalEmbedding X
  v : AmbientForm eX.dim 2
  v_smooth : ContDiffOn ℝ ∞ v eX.ambient
  v_closed : ∀ z ∈ eX.ambient, extDeriv v z = 0
  v_pos : ∀ z ∈ eX.ambient, IsOneOne (v z) ∧ IsStrictlyPositive (v z)
  v_res : om.RestrictsTo eX v
  P : ComplexModel E.dim → ComplexModel eX.dim
  P_hol : ContDiffOn ℂ ∞ P E.ambient
  P_maps : MapsTo P E.ambient eX.ambient
  P_lift : ∀ c : E.carrier, ∃ d : eX.carrier,
    d.val.val = P c.val.val ∧ eX.toPoint d = p.hom.left.base (E.toPoint c)
  t : ComplexModel E.dim → ℂ
  t_hol : ContDiffOn ℂ ∞ t E.ambient
  R : ComplexModel E.dim → ℝ
  R_smooth : ContDiffOn ℝ ∞ R E.ambient
  R_pos : ∀ u ∈ E.ambient, 0 < R u
  factor : ∀ c : E.carrier,
    U (p.hom.left.base (E.toPoint c)) = Complex.normSq (t c.val.val) * R c.val.val
  s : ℕ
  h : Fin s → ComplexModel E.dim → ℂ
  h_hol : ∀ k, ContDiffOn ℂ ∞ (h k) E.ambient
  h_zero : ∀ k (c : E.carrier), h k c.val.val = 0
  t_gen : ∀ c : E.carrier, p.hom.left.base (E.toPoint c) ∈ Cset →
    ∃ V : Set (ComplexModel eX.dim), IsOpen V ∧ P c.val.val ∈ V ∧
      ∃ f : ComplexModel eX.dim → ℂ, DifferentiableOn ℂ f V ∧
        (∀ d : eX.carrier, d.val.val ∈ V → eX.toPoint d ∈ Cset → f d.val.val = 0) ∧
        ∃ V' : Set (ComplexModel E.dim), IsOpen V' ∧ c.val.val ∈ V' ∧
          ∀ c' : E.carrier, c'.val.val ∈ V' → t c'.val.val = f (P c'.val.val)
  hadamard : ∀ c : E.carrier, p.hom.left.base (E.toPoint c) ∈ Cset →
    ∀ (V : Set (ComplexModel eX.dim)), IsOpen V → P c.val.val ∈ V →
    ∀ f : ComplexModel eX.dim → ℂ, DifferentiableOn ℂ f V →
      (∀ d : eX.carrier, d.val.val ∈ V → eX.toPoint d ∈ Cset → f d.val.val = 0) →
      ∃ V' : Set (ComplexModel E.dim), IsOpen V' ∧ c.val.val ∈ V' ∧
        ∃ q : ComplexModel E.dim → ℂ, DifferentiableOn ℂ q V' ∧
          ∀ c' : E.carrier, c'.val.val ∈ V' → f (P c'.val.val) = t c'.val.val * q c'.val.val
  dense : ∀ c : E.carrier,
    c ∈ closure {c' : E.carrier | p.hom.left.base (E.toPoint c') ∉ Cset}
  epsBound : ℝ
  epsBound_pos : 0 < epsBound
  pos : ∀ ε, 0 < ε → ε ≤ epsBound → ∀ u ∈ E.ambient, IsStrictlyPositive (repOf P v R h ε u)

variable {p Cset U om}

namespace GoodChart

variable (a : GoodChart p Cset U om)

/-- The ambient representative of `κ_ε` in the chart `a`. -/
abbrev rep (ε : ℝ) : AmbientForm a.E.dim 2 := repOf a.P a.v a.R a.h ε

theorem potential_contDiffOn (ε : ℝ) :
    ContDiffOn ℝ ∞ (fun u => ε * Real.log (a.R u) + ∑ k, Complex.normSq (a.h k u)) a.E.ambient := by
  refine (contDiffOn_const.mul (a.R_smooth.log fun u hu => (a.R_pos u hu).ne')).add ?_
  refine ContDiffOn.sum fun k _ => ?_
  have hk := (a.h_hol k).restrict_scalars ℝ
  simp only [Complex.normSq_apply]
  exact ((Complex.reCLM.contDiff.comp_contDiffOn hk).mul
      (Complex.reCLM.contDiff.comp_contDiffOn hk)).add
    ((Complex.imCLM.contDiff.comp_contDiffOn hk).mul (Complex.imCLM.contDiff.comp_contDiffOn hk))

theorem rep_smooth (ε : ℝ) : ContDiffOn ℝ ∞ (a.rep ε) a.E.ambient := by
  have hPr := a.P_hol.restrict_scalars ℝ
  exact (SmoothRealForm.contDiffOn_compContinuousLinearMap (a.v_smooth.comp hPr a.P_maps)
    (hPr.fderiv_of_isOpen a.E.ambient.isOpen (by simp))).add
    (Pending.LogWeightFactorization.smoothDDC_contDiffOn a.E.ambient.isOpen
      (a.potential_contDiffOn ε))

theorem rep_closed (ε : ℝ) : ∀ z ∈ a.E.ambient, extDeriv (a.rep ε) z = 0 := fun z hz =>
  KS2LeviEstimate.extDeriv_pullback_add_ddc a.E.ambient.isOpen a.eX.ambient.isOpen a.P_hol
    a.P_maps a.v_smooth a.v_closed (a.potential_contDiffOn ε) hz

theorem rep_isOneOne (ε : ℝ) : ∀ z ∈ a.E.ambient, IsOneOne (a.rep ε z) := fun z hz =>
  KS2LeviEstimate.isOneOne_pullback_add_ddc a.E.ambient.isOpen a.P_hol a.P_maps
    (fun x hx => (a.v_pos x hx).1) (a.potential_contDiffOn ε) hz

/-- The weight `U` is positive at points of `Y` off `p⁻¹(C)` exactly when `t ≠ 0`. -/
theorem t_ne_zero_iff (hU : ∀ x, 0 < U x ↔ x ∉ Cset) (c : a.E.carrier) :
    a.t c.val.val ≠ 0 ↔ p.hom.left.base (a.E.toPoint c) ∉ Cset := by
  rw [← hU, a.factor c]
  have hR := a.R_pos _ c.val.property
  constructor
  · intro ht
    exact mul_pos (Complex.normSq_pos.mpr ht) hR
  · intro hpos ht
    rw [ht, map_zero, zero_mul] at hpos
    exact lt_irrefl 0 hpos

end GoodChart

/-! ### Comparison of two good charts -/

section Compare

variable (a b : GoodChart p Cset U om)

/-- **Comparison of the weights of two good charts.**  Near every point of `Y` in the domain of a
transition `G` from `a` to `b`, `R_a = |q|² R_b ∘ G` on `Y` for a holomorphic nonvanishing `q`. -/
theorem exists_weight_ratio (hU : ∀ x, 0 < U x ↔ x ∉ Cset)
    {W : Set (ComplexModel a.E.dim)} {G : ComplexModel a.E.dim → ComplexModel b.E.dim}
    (hG : a.E.IsTransition b.E W G) (c : a.E.carrier) (hcW : c.val.val ∈ W) :
    ∃ V : Set (ComplexModel a.E.dim), IsOpen V ∧ c.val.val ∈ V ∧ V ⊆ W ∧
      ∃ q : ComplexModel a.E.dim → ℂ, DifferentiableOn ℂ q V ∧ (∀ u ∈ V, q u ≠ 0) ∧
        ∀ c' : a.E.carrier, c'.val.val ∈ V →
          a.R c'.val.val = Complex.normSq (q c'.val.val) * b.R (G c'.val.val) := by
  -- points of `b` over the points of `a`
  have hbpt : ∀ c' : a.E.carrier, c'.val.val ∈ W → ∃ c'' : b.E.carrier,
      c''.val.val = G c'.val.val ∧ b.E.toPoint c'' = a.E.toPoint c' := hG.2.2.2.2
  have hGcont : ContinuousOn G W := hG.2.2.1.continuousOn
  have hta_cont : ContinuousOn a.t a.E.ambient := a.t_hol.continuousOn
  -- the identity on the points with `t_a ≠ 0`
  have hid : ∀ c' : a.E.carrier, c'.val.val ∈ W → a.t c'.val.val ≠ 0 →
      ∀ q : ℂ, b.t (G c'.val.val) = a.t c'.val.val * q →
        a.R c'.val.val = Complex.normSq q * b.R (G c'.val.val) := by
    intro c' hc'W hta q hq
    obtain ⟨c'', hc'', hc''pt⟩ := hbpt c' hc'W
    have h1 := a.factor c'
    have h2 := b.factor c''
    rw [hc''pt, hc''] at h2
    rw [h2, hq, map_mul] at h1
    have hpos : 0 < Complex.normSq (a.t c'.val.val) := Complex.normSq_pos.mpr hta
    nlinarith [h1]
  by_cases hC : p.hom.left.base (a.E.toPoint c) ∈ Cset
  · -- the centre case: use the ideal-theoretic properties
    obtain ⟨c₂, hc₂, hc₂pt⟩ := hbpt c hcW
    have hC₂ : p.hom.left.base (b.E.toPoint c₂) ∈ Cset := by rw [hc₂pt]; exact hC
    obtain ⟨Vb, hVb, hPbVb, f, hf, hf0, Vb', hVb', hc₂Vb', htb⟩ := b.t_gen c₂ hC₂
    -- an `X`-transition from `a.eX` to `b.eX`
    obtain ⟨da, hda, hdapt⟩ := a.P_lift c
    obtain ⟨db, hdb, hdbpt⟩ := b.P_lift c₂
    have hdab : a.eX.toPoint da ∈ range b.eX.toPoint := ⟨db, by rw [hdbpt, hdapt, hc₂pt]⟩
    obtain ⟨WX, H, hdaWX, hH⟩ := a.eX.exists_isTransition b.eX da hdab
    -- `H` agrees with `P_b ∘ G` on carrier points, through the points of `b.eX`
    have hHda : H da.val.val = db.val.val := by
      obtain ⟨d', hd', hd'pt⟩ := hH.2.2.2.2 da hdaWX
      have : d' = db := b.eX.isOpenEmbedding_toPoint.injective (by rw [hd'pt, hdbpt, hdapt, hc₂pt])
      rw [← hd', this]
    -- the function `f ∘ H` on `a.eX` near `P_a c`
    let V₀ : Set (ComplexModel a.eX.dim) := WX ∩ H ⁻¹' Vb
    have hV₀ : IsOpen V₀ := hH.2.2.1.continuousOn.isOpen_inter_preimage hH.1 hVb
    have hPaV₀ : a.P c.val.val ∈ V₀ := by
      refine ⟨by rw [← hda]; exact hdaWX, ?_⟩
      change H (a.P c.val.val) ∈ Vb
      rw [← hda, hHda, hdb]
      exact hPbVb
    have hfH : DifferentiableOn ℂ (f ∘ H) V₀ :=
      hf.comp (hH.2.2.1.mono inter_subset_left) (fun u hu => hu.2)
    have hfH0 : ∀ d : a.eX.carrier, d.val.val ∈ V₀ → a.eX.toPoint d ∈ Cset →
        (f ∘ H) d.val.val = 0 := by
      intro d hd hdC
      obtain ⟨d', hd', hd'pt⟩ := hH.2.2.2.2 d hd.1
      change f (H d.val.val) = 0
      rw [← hd']
      exact hf0 d' (by rw [hd']; exact hd.2) (by rw [hd'pt]; exact hdC)
    obtain ⟨Va, hVa, hcVa, q, hq, hfq⟩ := a.hadamard c hC V₀ hV₀ hPaV₀ (f ∘ H) hfH hfH0
    -- the neighbourhood: `G` lands in `Vb'`, `P_a` lands in `V₀`
    let V₁ : Set (ComplexModel a.E.dim) :=
      Va ∩ (W ∩ G ⁻¹' Vb') ∩ (a.E.ambient ∩ a.P ⁻¹' V₀)
    have hV₁ : IsOpen V₁ :=
      (hVa.inter (hGcont.isOpen_inter_preimage hG.1 hVb')).inter
        (a.P_hol.continuousOn.isOpen_inter_preimage a.E.ambient.isOpen hV₀)
    have hcV₁ : c.val.val ∈ V₁ :=
      ⟨⟨hcVa, hcW, by change G c.val.val ∈ Vb'; rw [← hc₂]; exact hc₂Vb'⟩,
        c.val.property, hPaV₀⟩
    -- the relation `t_b ∘ G = t_a q` on carrier points of `V₁`
    have hrel : ∀ c' : a.E.carrier, c'.val.val ∈ V₁ →
        b.t (G c'.val.val) = a.t c'.val.val * q c'.val.val := by
      intro c' hc'
      obtain ⟨c'', hc'', hc''pt⟩ := hbpt c' hc'.1.2.1
      obtain ⟨da', hda', hda'pt⟩ := a.P_lift c'
      obtain ⟨db', hdb', hdb'pt⟩ := b.P_lift c''
      have hda'WX : da'.val.val ∈ WX := by rw [hda']; exact hc'.2.2.1
      obtain ⟨d', hd', hd'pt⟩ := hH.2.2.2.2 da' hda'WX
      have hd'db' : d' = db' :=
        b.eX.isOpenEmbedding_toPoint.injective (by rw [hd'pt, hdb'pt, hda'pt, hc''pt])
      have hPb : b.P (G c'.val.val) = H (a.P c'.val.val) := by
        rw [← hc'', ← hdb', ← hd'db', hd', hda']
      rw [← hc'', htb c'' (by rw [hc'']; exact hc'.1.2.2), hc'', hPb]
      exact hfq c' hc'.1.1
    -- `q` does not vanish at `c`, by the factorization and density
    have hdense_id : ∀ c' : a.E.carrier, c'.val.val ∈ V₁ →
        a.R c'.val.val = Complex.normSq (q c'.val.val) * b.R (G c'.val.val) := by
      -- on the dense set of points off the centre
      have hcl : ∀ c' : a.E.carrier, c'.val.val ∈ V₁ →
          p.hom.left.base (a.E.toPoint c') ∉ Cset →
          a.R c'.val.val = Complex.normSq (q c'.val.val) * b.R (G c'.val.val) := by
        intro c' hc' hnC
        exact hid c' hc'.1.2.1 ((a.t_ne_zero_iff hU c').mpr hnC) _ (hrel c' hc')
      intro c' hc'
      -- both sides are continuous on the carrier near `c'`
      let F₁ : a.E.carrier → ℝ := fun c'' => a.R c''.val.val
      let F₂ : a.E.carrier → ℝ := fun c'' => Complex.normSq (q c''.val.val) * b.R (G c''.val.val)
      let S : Set a.E.carrier := {c'' | c''.val.val ∈ V₁}
      have hSo : IsOpen S := hV₁.preimage (continuous_subtype_val.comp continuous_subtype_val)
      have hF₁ : ContinuousOn F₁ S := by
        refine (a.R_smooth.continuousOn.comp
          (continuous_subtype_val.comp continuous_subtype_val).continuousOn ?_)
        intro c'' _
        exact c''.val.property
      have hF₂ : ContinuousOn F₂ S := by
        have hqc : ContinuousOn q Va := hq.continuousOn
        have hbR : ContinuousOn b.R b.E.ambient := b.R_smooth.continuousOn
        have hGm : ∀ c'' ∈ S, G (c'' : a.E.carrier).val.val ∈ b.E.ambient :=
          fun c'' hc'' => hG.2.2.2.1 hc''.1.2.1
        refine ContinuousOn.mul ?_ ?_
        · exact (Complex.continuous_normSq.comp_continuousOn
            (hqc.comp (continuous_subtype_val.comp continuous_subtype_val).continuousOn
              (fun c'' hc'' => hc''.1.1)))
        · exact hbR.comp ((hGcont.comp (continuous_subtype_val.comp continuous_subtype_val).continuousOn
              (fun c'' hc'' => hc''.1.2.1))) hGm
      have heqOn : EqOn F₁ F₂ (S ∩ {c'' | p.hom.left.base (a.E.toPoint c'') ∉ Cset}) :=
        fun c'' hc'' => hcl c'' hc''.1 hc''.2
      have hc'S : c' ∈ S := hc'
      let T : Set a.E.carrier :=
        S ∩ closure (S ∩ {c'' | p.hom.left.base (a.E.toPoint c'') ∉ Cset})
      have hc'T : c' ∈ T := ⟨hc'S, hSo.inter_closure ⟨hc'S, a.dense c'⟩⟩
      have hEq := heqOn.of_subset_closure (hF₁.mono inter_subset_left) (hF₂.mono inter_subset_left)
        (fun c'' hc'' => ⟨hc''.1, subset_closure hc''⟩) inter_subset_right
      exact hEq hc'T
    have hqc : q c.val.val ≠ 0 := by
      intro h0
      have := hdense_id c hcV₁
      rw [h0, map_zero, zero_mul] at this
      exact (a.R_pos _ c.val.property).ne' this
    -- shrink to where `q ≠ 0`
    have hqcont : ContinuousOn q Va := hq.continuousOn
    let V : Set (ComplexModel a.E.dim) := V₁ ∩ (Va ∩ q ⁻¹' {0}ᶜ)
    have hV : IsOpen V := hV₁.inter (hqcont.isOpen_inter_preimage hVa isClosed_singleton.isOpen_compl)
    refine ⟨V, hV, ⟨hcV₁, hcVa, hqc⟩, fun u hu => hu.1.1.2.1, q,
      hq.mono fun u hu => hu.1.1.1, fun u hu => hu.2.2, fun c' hc' => hdense_id c' hc'.1⟩
  · -- off the centre: `t_a ≠ 0` near `c`
    have hta : a.t c.val.val ≠ 0 := (a.t_ne_zero_iff hU c).mpr hC
    obtain ⟨c₂, hc₂, hc₂pt⟩ := hbpt c hcW
    have htb : b.t (G c.val.val) ≠ 0 := by
      rw [← hc₂]
      exact (b.t_ne_zero_iff hU c₂).mpr (by rw [hc₂pt]; exact hC)
    have htb_hol : DifferentiableOn ℂ (b.t ∘ G) W :=
      (b.t_hol.differentiableOn (by simp)).comp hG.2.2.1 hG.2.2.2.1
    let V : Set (ComplexModel a.E.dim) :=
      (W ∩ (b.t ∘ G) ⁻¹' {0}ᶜ) ∩ (a.E.ambient ∩ a.t ⁻¹' {0}ᶜ)
    have hV : IsOpen V :=
      (htb_hol.continuousOn.isOpen_inter_preimage hG.1 isClosed_singleton.isOpen_compl).inter
        (hta_cont.isOpen_inter_preimage a.E.ambient.isOpen isClosed_singleton.isOpen_compl)
    refine ⟨V, hV, ⟨⟨hcW, htb⟩, c.val.property, hta⟩, fun u (hu : u ∈ V) => hu.1.1,
      fun u => b.t (G u) / a.t u, ?_, ?_, ?_⟩
    · have h1 : DifferentiableOn ℂ (fun u => b.t (G u)) V :=
        htb_hol.mono fun u (hu : u ∈ V) => hu.1.1
      have h2 : DifferentiableOn ℂ (fun u => (a.t u)⁻¹) V :=
        ((a.t_hol.differentiableOn (by simp)).mono fun u (hu : u ∈ V) => hu.2.1).inv
          fun u (hu : u ∈ V) => hu.2.2
      refine (h1.mul h2).congr fun u _ => ?_
      simp only [Pi.mul_apply, div_eq_mul_inv]
    · intro u hu
      exact div_ne_zero hu.1.2 hu.2.2
    · intro c' hc'
      refine hid c' hc'.1.1 hc'.2.2 _ ?_
      field_simp
      exact (mul_div_cancel_right₀ _ hc'.2.2).symm


/-- Pull-backs along maps which agree near the point coincide. -/
theorem pullbackForm_congr_eventuallyEq {m N k : ℕ} {F F' : ComplexModel m → ComplexModel N}
    (v : AmbientForm N k) {z : ComplexModel m} (h : F =ᶠ[𝓝 z] F') :
    pullbackForm F v z = pullbackForm F' v z := by
  simp only [pullbackForm, h.self_of_nhds, h.fderiv_eq]

/-- **Compatibility of good charts**: the ambient representatives of `κ_ε` agree on `Y` along
every holomorphic transition. -/
theorem vanishesOn_rep (hU : ∀ x, 0 < U x ↔ x ∉ Cset) (a b : GoodChart p Cset U om) (ε : ℝ)
    {W : Set (ComplexModel a.E.dim)} {G : ComplexModel a.E.dim → ComplexModel b.E.dim}
    (hG : a.E.IsTransition b.E W G) :
    a.E.VanishesOn W (a.rep ε - pullbackForm G (b.rep ε)) := by
  intro m D φ hD hφ hφm z hz
  obtain ⟨hzW, c, hc⟩ := hφm z hz
  have hcW : c.val.val ∈ W := by rw [hc]; exact hzW
  obtain ⟨V, hV, hcV, hVW, q, hq, hq0, hR⟩ := exists_weight_ratio a b hU hG c hcW
  let D' : Set (ComplexModel m) := D ∩ φ ⁻¹' V
  have hD' : IsOpen D' := hφ.continuousOn.isOpen_inter_preimage hD hV
  have hzD' : z ∈ D' := ⟨hz, by change φ z ∈ V; rw [← hc]; exact hcV⟩
  have hφc : ContDiffOn ℂ ∞ φ D := contDiffOn_of_differentiableOn_complex hφ hD
  have hφz : DifferentiableAt ℝ φ z :=
    (hφ.differentiableAt (hD.mem_nhds hz)).restrictScalars ℝ
  have hGz : DifferentiableAt ℝ G (φ z) :=
    (hG.2.2.1.differentiableAt (hG.1.mem_nhds hzW)).restrictScalars ℝ
  have hφA : MapsTo φ D a.E.ambient := fun w hw => hG.2.1 (hφm w hw).1
  have hGφB : MapsTo (G ∘ φ) D b.E.ambient := fun w hw => hG.2.2.2.1 (hφm w hw).1
  have hGφc : ContDiffOn ℂ ∞ (G ∘ φ) D :=
    (contDiffOn_of_differentiableOn_complex hG.2.2.1 hG.1).comp hφc fun w hw => (hφm w hw).1
  -- carrier points along the probe
  have hpt : ∀ w ∈ D, ∃ (ca : a.E.carrier) (cb : b.E.carrier), ca.val.val = φ w ∧
      cb.val.val = G (φ w) ∧ b.E.toPoint cb = a.E.toPoint ca := by
    intro w hw
    obtain ⟨ca, hca⟩ := (hφm w hw).2
    obtain ⟨cb, hcb, hcbpt⟩ := hG.2.2.2.2 ca (by rw [hca]; exact (hφm w hw).1)
    exact ⟨ca, cb, hca, by rw [hcb, hca], hcbpt⟩
  rw [pullbackForm_sub, Pi.sub_apply, pullbackForm_comp hφz hGz, sub_eq_zero]
  simp only [GoodChart.rep, repOf, pullbackForm_add, Pi.add_apply]
  congr 1
  · -- the pull-backs of `om`
    have hPa : DifferentiableAt ℝ a.P (φ z) :=
      ((a.P_hol.differentiableOn (by simp)).differentiableAt
        (a.E.ambient.isOpen.mem_nhds (hφA hz))).restrictScalars ℝ
    have hPb : DifferentiableAt ℝ b.P (G (φ z)) :=
      ((b.P_hol.differentiableOn (by simp)).differentiableAt
        (b.E.ambient.isOpen.mem_nhds (hGφB hz))).restrictScalars ℝ
    rw [pullbackForm_comp hφz hPa, pullbackForm_comp (hGz.comp z hφz) hPb]
    -- an `X`-transition from `a.eX` to `b.eX`
    obtain ⟨ca₀, cb, hca₀, hcb, hcbpt⟩ := hpt z hz
    obtain ⟨da, hda, hdapt⟩ := a.P_lift ca₀
    obtain ⟨db, hdb, hdbpt⟩ := b.P_lift cb
    have hdab : a.eX.toPoint da ∈ range b.eX.toPoint := ⟨db, by rw [hdbpt, hdapt, hcbpt]⟩
    obtain ⟨WX, H, hdaWX, hH⟩ := a.eX.exists_isTransition b.eX da hdab
    let D'' : Set (ComplexModel m) := D ∩ (a.P ∘ φ) ⁻¹' WX
    have hPφ : DifferentiableOn ℂ (a.P ∘ φ) D :=
      (a.P_hol.differentiableOn (by simp)).comp hφ hφA
    have hD'' : IsOpen D'' := hPφ.continuousOn.isOpen_inter_preimage hD hH.1
    have hzD'' : z ∈ D'' := ⟨hz, by
      change a.P (φ z) ∈ WX
      rw [← hca₀, ← hda]
      exact hdaWX⟩
    have hvan := (a.v_res.vanishesOn_sub b.v_res hH) m D'' (a.P ∘ φ) hD''
      (hPφ.mono inter_subset_left) (by
        intro w hw
        refine ⟨hw.2, ?_⟩
        obtain ⟨ca, hca⟩ := (hφm w hw.1).2
        obtain ⟨d, hd, -⟩ := a.P_lift ca
        exact ⟨d, by rw [hd, hca]; rfl⟩) z hzD''
    have hHz : DifferentiableAt ℝ H (a.P (φ z)) :=
      (hH.2.2.1.differentiableAt (hH.1.mem_nhds hzD''.2)).restrictScalars ℝ
    rw [pullbackForm_sub, Pi.sub_apply, sub_eq_zero, pullbackForm_comp (hPa.comp z hφz) hHz]
      at hvan
    rw [hvan]
    apply pullbackForm_congr_eventuallyEq
    filter_upwards [hD''.mem_nhds hzD''] with w hw
    obtain ⟨ca, cb', hca, hcb', hcb'pt⟩ := hpt w hw.1
    obtain ⟨da', hda', hda'pt⟩ := a.P_lift ca
    obtain ⟨db', hdb', hdb'pt⟩ := b.P_lift cb'
    obtain ⟨d', hd', hd'pt⟩ := hH.2.2.2.2 da' (by rw [hda', hca]; exact hw.2)
    have : d' = db' := b.eX.isOpenEmbedding_toPoint.injective
      (by rw [hd'pt, hdb'pt, hda'pt, hcb'pt])
    change H (a.P (φ w)) = b.P (G (φ w))
    calc H (a.P (φ w)) = H da'.val.val := by rw [hda', hca]
      _ = d'.val.val := hd'.symm
      _ = db'.val.val := by rw [this]
      _ = b.P cb'.val.val := hdb'
      _ = b.P (G (φ w)) := by rw [hcb']
  · -- the `ddᶜ` parts
    have h1 := HolomorphicDDC.smoothDDC_comp hD a.E.ambient.isOpen hφc
      (a.potential_contDiffOn ε) hφA hz
    have h2 := HolomorphicDDC.smoothDDC_comp hD b.E.ambient.isOpen hGφc
      (b.potential_contDiffOn ε) hGφB hz
    unfold pullbackForm
    rw [← h1, ← h2]
    -- on the probe the potentials differ by `ε log |q ∘ φ|²`
    have hqφ : DifferentiableOn ℂ (q ∘ φ) D' :=
      hq.comp (hφ.mono inter_subset_left) fun w hw => hw.2
    have hqφ0 : ∀ w ∈ D', (q ∘ φ) w ≠ 0 := fun w hw => hq0 _ hw.2
    have hlogR : ContDiffOn ℝ ∞ (fun w => Real.log (b.R (G (φ w)))) D' :=
      ((b.R_smooth.comp (hGφc.restrict_scalars ℝ) hGφB).log fun w hw =>
        (b.R_pos _ (hGφB hw)).ne').mono inter_subset_left
    have hlogq : ContDiffOn ℝ ∞ (fun w => Real.log (Complex.normSq ((q ∘ φ) w))) D' := by
      have hq' := (contDiffOn_of_differentiableOn_complex hqφ hD').restrict_scalars ℝ
      have hn : ContDiffOn ℝ ∞ (fun w => Complex.normSq ((q ∘ φ) w)) D' := by
        simp only [Complex.normSq_apply]
        exact ((Complex.reCLM.contDiff.comp_contDiffOn hq').mul
          (Complex.reCLM.contDiff.comp_contDiffOn hq')).add
          ((Complex.imCLM.contDiff.comp_contDiffOn hq').mul
            (Complex.imCLM.contDiff.comp_contDiffOn hq'))
      exact hn.log fun w hw => (Complex.normSq_pos.mpr (hqφ0 w hw)).ne'
    have heqa : (fun w => (fun u => ε * Real.log (a.R u) + ∑ k, Complex.normSq (a.h k u)) (φ w))
        =ᶠ[𝓝 z] fun w => ε * Real.log (b.R (G (φ w))) +
          ε * Real.log (Complex.normSq ((q ∘ φ) w)) := by
      filter_upwards [hD'.mem_nhds hzD'] with w hw
      obtain ⟨ca, cb', hca, hcb', hcb'pt⟩ := hpt w hw.1
      have hh : ∀ k, a.h k (φ w) = 0 := fun k => by rw [← hca]; exact a.h_zero k ca
      simp only [hh, map_zero, Finset.sum_const_zero, add_zero]
      have hRa := hR ca (by rw [hca]; exact hw.2)
      rw [hca] at hRa
      have hq1 : Complex.normSq (q (φ w)) ≠ 0 := (Complex.normSq_pos.mpr (hqφ0 w hw)).ne'
      have hb1 : b.R (G (φ w)) ≠ 0 := (b.R_pos _ (hGφB hw.1)).ne'
      rw [hRa, Real.log_mul hq1 hb1]
      simp only [Function.comp]
      ring
    have heqb : (fun w => (fun u => ε * Real.log (b.R u) + ∑ k, Complex.normSq (b.h k u))
        ((G ∘ φ) w)) =ᶠ[𝓝 z] fun w => ε * Real.log (b.R (G (φ w))) := by
      filter_upwards [hD.mem_nhds hz] with w hw
      obtain ⟨ca, cb', hca, hcb', hcb'pt⟩ := hpt w hw
      have hh : ∀ k, b.h k (G (φ w)) = 0 := fun k => by rw [← hcb']; exact b.h_zero k cb'
      simp only [Function.comp, hh, map_zero, Finset.sum_const_zero, add_zero]
    rw [smoothDDC_congr heqa, smoothDDC_congr heqb]
    rw [smoothDDC_add hD' (contDiffOn_const.mul hlogR) (contDiffOn_const.mul hlogq) hzD']
    have hzero : smoothDDC (fun w => ε * Real.log (Complex.normSq ((q ∘ φ) w))) z = 0 := by
      have h1 := smoothDDC_smul hD' hlogq ε hzD'
      simp only [smul_eq_mul] at h1
      rw [h1, Pending.PluriharmonicLogNorm.smoothDDC_log_normSq_eq_zero
        (Filter.eventually_of_mem (hD'.mem_nhds hzD') fun w hw =>
          hqφ.differentiableAt (hD'.mem_nhds hw)) (hqφ0 z hzD'), smul_zero]
    rw [hzero, add_zero]

/-- **The form `κ_ε`** on `Y`, defined by the good charts (assumed to cover `Y`). -/
def kahlerForm (hU : ∀ x, 0 < U x ↔ x ∉ Cset) (ε : ℝ)
    (hcover : ∀ y : Y.obj.left, ∃ a : GoodChart p Cset U om, y ∈ range a.E.toPoint) :
    SpaceForm Y 2 where
  ι := GoodChart p Cset U om
  chart a := a.E
  covers := hcover
  rep a := a.rep ε
  smooth a := a.rep_smooth ε
  compatible a b _W _G hG := vanishesOn_rep hU a b ε hG

/-- **`κ_ε` is a Kähler form** when every point lies in a good chart whose bound is at least
`ε`. -/
theorem isKahler_kahlerForm (hU : ∀ x, 0 < U x ↔ x ∉ Cset) {ε : ℝ} (hε : 0 < ε)
    (hcover : ∀ y : Y.obj.left, ∃ a : GoodChart p Cset U om, y ∈ range a.E.toPoint)
    (hgood : ∀ y : Y.obj.left, ∃ a : GoodChart p Cset U om, y ∈ range a.E.toPoint ∧
      ε ≤ a.epsBound) :
    (kahlerForm hU ε hcover).IsKahler := by
  intro y
  obtain ⟨a, hy, hεa⟩ := hgood y
  refine ⟨a.E, hy, a.rep ε, a.rep_smooth ε, a.rep_closed ε, fun z hz =>
    ⟨a.rep_isOneOne ε z hz, a.pos ε hε hεa z hz⟩, ?_⟩
  intro b W G hG
  exact vanishesOn_rep hU a b ε hG

/-- **A blowup with a covering family of good charts is Kähler**, when `Y` is compact. -/
theorem isKahlerSpace_of_goodCharts (hU : ∀ x, 0 < U x ↔ x ∉ Cset) [CompactSpace Y.obj.left]
    (hcover : ∀ y : Y.obj.left, ∃ a : GoodChart p Cset U om, y ∈ range a.E.toPoint) :
    Y.IsKahlerSpace := by
  classical
  choose a ha using hcover
  obtain ⟨F, hF⟩ := isCompact_univ.elim_finite_subcover (fun y => range (a y).E.toPoint)
    (fun y => (a y).E.isOpen_range_toPoint) (fun y _ => mem_iUnion.mpr ⟨y, ha y⟩)
  by_cases hFe : F.Nonempty
  · let ε := F.inf' hFe fun y => (a y).epsBound
    have hε : 0 < ε := (Finset.lt_inf'_iff hFe).mpr fun y _ => (a y).epsBound_pos
    refine ⟨kahlerForm hU ε (fun y => ⟨a y, ha y⟩), isKahler_kahlerForm hU hε _ ?_⟩
    intro y
    obtain ⟨y', hy'F, hyy'⟩ := mem_iUnion₂.mp (hF (mem_univ y))
    exact ⟨a y', hyy', Finset.inf'_le _ hy'F⟩
  · -- `Y` is empty
    have hYe : ∀ y : Y.obj.left, False := fun y => by
      obtain ⟨y', hy'F, -⟩ := mem_iUnion₂.mp (hF (mem_univ y))
      exact hFe ⟨y', hy'F⟩
    refine ⟨kahlerForm hU 1 (fun y => ⟨a y, ha y⟩), fun y => (hYe y).elim⟩

end Compare

end SGPT.Unibranch.KS3BlowupKahlerForm
