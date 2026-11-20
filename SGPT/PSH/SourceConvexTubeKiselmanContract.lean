import SGPT.PSH.SourceConvexTubeKiselman

/-! Literal current prop:Kis input and real-fibre output dictionary.
The actual printed family is constrained only on the original projection;
the all-base-point convention in the core is produced using empty fibres.
No value, topology, dimension or finiteness hypothesis is added. -/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.KiselmanNext

open Set Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology

/-- The source constrains fibres only above its actual projection. Outside it,
the original complex fibre is empty, so the core's total convention is internal. -/
theorem convex_tube_fibres_of_projected_fibres {m n : ℕ}
    {Ω : Set (ComplexModel m × ComplexModel n)}
    (hfib : ∀ z ∈ Prod.fst '' Ω, ∃ E : Set (Fin n → ℝ),
      E.Nonempty ∧ IsOpen E ∧ Convex ℝ E ∧
        BookDeep2Kiselman.slice Ω z = {w | (fun k => (w k).re) ∈ E}) :
    ∀ z, ∃ E : Set (Fin n → ℝ), Convex ℝ E ∧
      BookDeep2Kiselman.slice Ω z = {w | (fun k => (w k).re) ∈ E} := by
  intro z
  by_cases hz : z ∈ Prod.fst '' Ω
  · obtain ⟨E, _, _, hconv, hE⟩ := hfib z hz
    exact ⟨E, hconv, hE⟩
  · refine ⟨∅, convex_empty, ?_⟩
    ext w
    constructor
    · intro hw
      exact (hz ⟨(z, w), hw, rfl⟩).elim
    · intro hw
      exact hw.elim

/-- Entire literal current `prop:Kis`: nonempty open convex real fibres are
specified only on the original projection; the output is the same printed
real-fibre infimum, with its possible identically-bottom case retained. -/
theorem source_kiselman_convex_tube {m n : ℕ}
    (Ω : Set (ComplexModel m × ComplexModel n)) (hConnected : IsConnected Ω)
    (hΩ : BookDeep2Kiselman.IsPseudoconvex Ω)
    (E : ComplexModel m → Set (Fin n → ℝ))
    (hfib : ∀ z ∈ Prod.fst '' Ω, (E z).Nonempty ∧ IsOpen (E z) ∧
      Convex ℝ (E z) ∧
        BookDeep2Kiselman.slice Ω z = {w | (fun k => (w k).re) ∈ E z})
    (φ : ComplexModel m × ComplexModel n → EReal) (hφ : SGPT.PSH.PSHOn φ Ω)
    (hinv : ∀ z w w', (z, w) ∈ Ω → (∀ k, (w k).re = (w' k).re) →
      φ (z, w') = φ (z, w)) :
    (∀ z ∈ Prod.fst '' Ω,
      (⨅ t ∈ E z, φ (z, WithLp.toLp 2 (fun k => (t k : ℂ)))) = ⊥) ∨
      SGPT.PSH.PSHOn
        (fun z => ⨅ t ∈ E z, φ (z, WithLp.toLp 2 (fun k => (t k : ℂ))))
        (Prod.fst '' Ω) := by
  have htube := convex_tube_fibres_of_projected_fibres
    (fun z hz => ⟨E z, hfib z hz⟩)
  have heq : ∀ z ∈ Prod.fst '' Ω, tubeInfimum Ω φ z =
      ⨅ t ∈ E z, φ (z, WithLp.toLp 2 (fun k => (t k : ℂ))) := by
    intro z hz
    exact tubeInfimum_eq_realInfimum hinv z (hfib z hz).2.2.2
  obtain hbot | hp := kiselmanPrincipleConvexSlices m n Ω hConnected hΩ htube φ hφ hinv
  · exact Or.inl (fun z hz => (heq z hz).symm.trans (hbot z hz))
  · apply Or.inr
    have hU : IsOpen (Prod.fst '' Ω) := isOpenMap_fst _ hΩ.1
    have hp' : PlurisubharmonicOn
        (fun z => ⨅ t ∈ E z, φ (z, WithLp.toLp 2 (fun k => (t k : ℂ))))
        (Prod.fst '' Ω) := by
      intro z hz
      exact (hp.disc.plurisubharmonicOn hU z hz).congr
        (Filter.Eventually.mono (hU.mem_nhds hz) (fun y hy => heq y hy))
    refine ⟨hp'.discPshOn, ?_⟩
    obtain ⟨z, hz, hne⟩ := hp.nontrivial
    exact ⟨z, hz, (heq z hz).symm ▸ hne⟩

end SGPT.PSH.KiselmanNext
