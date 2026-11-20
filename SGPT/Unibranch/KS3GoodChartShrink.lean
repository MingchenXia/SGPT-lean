import SGPT.Unibranch.KS3BlowupKahlerForm
import SGPT.Unibranch.KS3BlowupPositivity

/-!
# Good charts from local data

Lane KS3 (Kähler preservation under blowups, `def:unibranch:L212`).  The fields of a good chart
(`KS3BlowupKahlerForm.GoodChart`) are required on the whole ambient open set of a local
embedding of `Y`.  Here they are produced from data given only on an open neighbourhood `Ω` of
a carrier point `c₀`, with the weight `R` positive only at `c₀` and with `ddᶜ log R` positive at
`c₀` on the common kernel of `dP` and `dH` (`H` = the equations of `Y`): restricting the local
embedding to the neighbourhood of `c₀` provided by
`KS3BlowupPositivity.exists_isStrictlyPositive_near` gives a good chart through `c₀`
(`exists_goodChart_of_nhds`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter TopologicalSpace CategoryTheory
open scoped Topology ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass

namespace SGPT.Unibranch.KS3GoodChartShrink

open KS3BlowupKahlerForm

variable {X Y : SourceReducedComplexSpace} {p : Y ⟶ X} {Cset : Set X.obj.left}
  {U : X.obj.left → ℝ} {om : SpaceForm X 2}

/-- **A good chart through a point from data near the point.** -/
theorem exists_goodChart_of_nhds (E : LocalEmbedding Y) (c₀ : E.carrier)
    {Ω : Set (ComplexModel E.dim)} (hΩ : IsOpen Ω) (hc₀ : c₀.val.val ∈ Ω)
    (eX : LocalEmbedding X) (v : AmbientForm eX.dim 2)
    (v_smooth : ContDiffOn ℝ ∞ v eX.ambient)
    (v_closed : ∀ z ∈ eX.ambient, extDeriv v z = 0)
    (v_pos : ∀ z ∈ eX.ambient, IsOneOne (v z) ∧ IsStrictlyPositive (v z))
    (v_res : om.RestrictsTo eX v)
    (P : ComplexModel E.dim → ComplexModel eX.dim) (P_hol : ContDiffOn ℂ ∞ P Ω)
    (P_maps : MapsTo P Ω eX.ambient)
    (P_lift : ∀ c : E.carrier, c.val.val ∈ Ω → ∃ d : eX.carrier,
      d.val.val = P c.val.val ∧ eX.toPoint d = p.hom.left.base (E.toPoint c))
    (t : ComplexModel E.dim → ℂ) (t_hol : ContDiffOn ℂ ∞ t Ω)
    (R : ComplexModel E.dim → ℝ) (R_smooth : ContDiffOn ℝ ∞ R Ω) (R_pos : 0 < R c₀.val.val)
    (factor : ∀ c : E.carrier, c.val.val ∈ Ω →
      U (p.hom.left.base (E.toPoint c)) = Complex.normSq (t c.val.val) * R c.val.val)
    {s : ℕ} (H : ComplexModel E.dim → ComplexModel s) (H_hol : ContDiffOn ℂ ∞ H Ω)
    (H_zero : ∀ c : E.carrier, c.val.val ∈ Ω → H c.val.val = 0)
    (t_gen : ∀ c : E.carrier, c.val.val ∈ Ω → p.hom.left.base (E.toPoint c) ∈ Cset →
      ∃ V : Set (ComplexModel eX.dim), IsOpen V ∧ P c.val.val ∈ V ∧
        ∃ f : ComplexModel eX.dim → ℂ, DifferentiableOn ℂ f V ∧
          (∀ d : eX.carrier, d.val.val ∈ V → eX.toPoint d ∈ Cset → f d.val.val = 0) ∧
          ∃ V' : Set (ComplexModel E.dim), IsOpen V' ∧ c.val.val ∈ V' ∧
            ∀ c' : E.carrier, c'.val.val ∈ V' → t c'.val.val = f (P c'.val.val))
    (hadamard : ∀ c : E.carrier, c.val.val ∈ Ω → p.hom.left.base (E.toPoint c) ∈ Cset →
      ∀ (V : Set (ComplexModel eX.dim)), IsOpen V → P c.val.val ∈ V →
      ∀ f : ComplexModel eX.dim → ℂ, DifferentiableOn ℂ f V →
        (∀ d : eX.carrier, d.val.val ∈ V → eX.toPoint d ∈ Cset → f d.val.val = 0) →
        ∃ V' : Set (ComplexModel E.dim), IsOpen V' ∧ c.val.val ∈ V' ∧
          ∃ q : ComplexModel E.dim → ℂ, DifferentiableOn ℂ q V' ∧
            ∀ c' : E.carrier, c'.val.val ∈ V' →
              f (P c'.val.val) = t c'.val.val * q c'.val.val)
    (dense : ∀ c : E.carrier,
      c ∈ closure {c' : E.carrier | p.hom.left.base (E.toPoint c') ∉ Cset})
    (hfib : ∀ ξ : ComplexModel E.dim, ξ ≠ 0 → fderiv ℝ P c₀.val.val ξ = 0 →
      fderiv ℝ H c₀.val.val ξ = 0 →
      0 < smoothDDC (fun u => Real.log (R u)) c₀.val.val ![ξ, Complex.I • ξ]) :
    ∃ a : GoodChart p Cset U om, E.toPoint c₀ ∈ range a.E.toPoint := by
  classical
  -- the open set where the data are defined and `R > 0`
  let Ω₁ : Set (ComplexModel E.dim) := (Ω ∩ E.ambient) ∩ R ⁻¹' Ioi 0
  have hΩ₁ : IsOpen Ω₁ :=
    (R_smooth.continuousOn.mono inter_subset_left).isOpen_inter_preimage
      (hΩ.inter E.ambient.isOpen) isOpen_Ioi
  have hu₀ : c₀.val.val ∈ Ω₁ := ⟨⟨hc₀, c₀.val.property⟩, R_pos⟩
  have hΩ₁Ω : Ω₁ ⊆ Ω := fun u hu => hu.1.1
  obtain ⟨ε₀, hε₀, T, hT, hu₀T, hTΩ₁, hpos⟩ :=
    KS3BlowupPositivity.exists_isStrictlyPositive_near hΩ₁ hu₀ (P_hol.mono hΩ₁Ω)
      eX.ambient.isOpen (P_maps.mono_left hΩ₁Ω) v_smooth (fun x hx => (v_pos x hx).2)
      (H_hol.mono hΩ₁Ω) (R_smooth.mono hΩ₁Ω) (fun u hu => hu.2) hfib
  let T' : Opens (ComplexModel E.dim) := ⟨T, hT⟩
  have hT' : T' ≤ E.ambient := fun u hu => (hTΩ₁ hu).1.2
  have hTΩ : T ⊆ Ω := fun u hu => (hTΩ₁ hu).1.1
  let E' := E.restrict T' hT'
  -- carrier points of the restriction are carrier points of `E`
  let ι : E'.carrier → E.carrier := fun c => ⟨Opens.inclusion hT' c.val, c.property⟩
  have hιval : ∀ c : E'.carrier, (ι c).val.val = c.val.val := fun _ => rfl
  have hιpt : ∀ c : E'.carrier, E'.toPoint c = E.toPoint (ι c) := fun _ => rfl
  have hιΩ : ∀ c : E'.carrier, (ι c).val.val ∈ Ω := fun c => hTΩ c.val.property
  have hιopen : Topology.IsOpenEmbedding ι :=
    Topology.IsOpenEmbedding.of_comp ι E.isOpenEmbedding_toPoint E'.isOpenEmbedding_toPoint
  have hnorm : ∀ u, ∑ k, Complex.normSq (H u k) = ‖H u‖ ^ 2 := fun u =>
    KS3FibreLevi.sum_normSq_eq_norm_sq (H u)
  let a : GoodChart p Cset U om :=
    { E := E'
      eX := eX
      v := v
      v_smooth := v_smooth
      v_closed := v_closed
      v_pos := v_pos
      v_res := v_res
      P := P
      P_hol := P_hol.mono hTΩ
      P_maps := P_maps.mono_left hTΩ
      P_lift := fun c => P_lift (ι c) (hιΩ c)
      t := t
      t_hol := t_hol.mono hTΩ
      R := R
      R_smooth := R_smooth.mono hTΩ
      R_pos := fun u hu => (hTΩ₁ hu).2
      factor := fun c => factor (ι c) (hιΩ c)
      s := s
      h := fun k u => H u k
      h_hol := fun k =>
        ((EuclideanSpace.proj k : ComplexModel s →L[ℂ] ℂ).contDiff.comp_contDiffOn H_hol).mono
          hTΩ
      h_zero := fun k c => by
        change H (ι c).val.val k = 0
        rw [H_zero (ι c) (hιΩ c)]
        rfl
      t_gen := fun c hc => by
        obtain ⟨V, hV, hPV, f, hf, hf0, V', hV', hcV', ht⟩ := t_gen (ι c) (hιΩ c) hc
        exact ⟨V, hV, hPV, f, hf, hf0, V', hV', hcV', fun c' hc' => ht (ι c') hc'⟩
      hadamard := fun c hc V hV hPV f hf hf0 => by
        obtain ⟨V', hV', hcV', q, hq, hfq⟩ := hadamard (ι c) (hιΩ c) hc V hV hPV f hf hf0
        exact ⟨V', hV', hcV', q, hq, fun c' hc' => hfq (ι c') hc'⟩
      dense := fun c => by
        have h1 := dense (ι c)
        have h2 : c ∈ ι ⁻¹' closure {c' : E.carrier |
            p.hom.left.base (E.toPoint c') ∉ Cset} := h1
        rw [hιopen.isOpenMap.preimage_closure_eq_closure_preimage hιopen.continuous] at h2
        exact h2
      epsBound := ε₀
      epsBound_pos := hε₀
      pos := fun ε hε hεle u hu => by
        have h := hpos ε hε hεle u hu
        have hfun : (fun u => ε * Real.log (R u) + ∑ k, Complex.normSq (H u k)) =
            fun u => ε * Real.log (R u) + ‖H u‖ ^ 2 := funext fun u => by rw [hnorm]
        change IsStrictlyPositive (pullbackForm P v u +
          smoothDDC (fun u => ε * Real.log (R u) + ∑ k, Complex.normSq (H u k)) u)
        rw [hfun]
        exact h }
  refine ⟨a, ⟨⟨⟨c₀.val.val, hu₀T⟩, ?_⟩, ?_⟩⟩
  · change Opens.inclusion hT' ⟨c₀.val.val, hu₀T⟩ ∈ E.carrier
    have : Opens.inclusion hT' ⟨c₀.val.val, hu₀T⟩ = c₀.val := rfl
    rw [this]
    exact c₀.property
  · change E.toPoint ⟨Opens.inclusion hT' ⟨c₀.val.val, hu₀T⟩, _⟩ = E.toPoint c₀
    rfl

end SGPT.Unibranch.KS3GoodChartShrink
