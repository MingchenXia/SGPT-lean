import SGPT.GAGA.CoreCLaurent
import SGPT.GAGA.PN2Dehomog

/-!
# `AffineSectionsDecompose` on the Laurent polyhedra and Theorem B on the sets `K_s`

Lane SERRE-CORE3 (Serre's GAGA, towards source `lma:GAGA`, `chapter_NApotential.tex`
lines 1143--1145), step M2.6 of `blueprint/src/claude-serre-core.tex`: the statement requested by
lane SERRE-PN (`claude-serre-pn.tex`, paragraph "Interface with SERRE-CORE2"), in the exact form
`SGPT.GAGA.PN.AffineSectionsDecompose` stated by lane SERRE-PN2 (`PN2Dehomog`).

* `affineSectionsDecompose_lpoly`: every compact Reinhardt Laurent polyhedron
  `lpoly ρ s = {w : |w_j| ≤ ρ, 1 ≤ ρ|w_k|, |w_j| ≤ ρ|w_k| (k ∈ s)}` (`ρ ≥ 0`) satisfies
  `AffineSectionsDecompose` (`Laurent.exists_decompose_lpoly`).
* `affineSectionsDecompose_chart_coverSet`: for `i ∈ s`, the chart preimage `chart i ⁻¹' K_s`
  of the cone set `K_s = coverSet ρ s` satisfies it (it is `lpoly ρ s'` for `ρ ≥ 1` and empty
  otherwise, `Laurent.preimage_coverSet_eq`).
* `sectionsDecompose_coverSet_all`: hence, by SERRE-PN2's dehomogenization
  (`PN.sectionsDecompose_coverSet_of_affine`), every `K_s` with `s ≠ ∅` satisfies
  `PN.SectionsDecompose`, the Theorem-B hypothesis of `PN.coverSystem_les`.
-/

set_option autoImplicit false

open Set

namespace SGPT.GAGA.Core.Laurent

/-- **Theorem B on compact Reinhardt Laurent polyhedra**, in the form
`SGPT.GAGA.PN.AffineSectionsDecompose` requested by lanes SERRE-PN / SERRE-PN2. -/
theorem affineSectionsDecompose_lpoly {N : ℕ} {ρ : ℝ} (hρ : 0 ≤ ρ) (s : Finset (Fin N)) :
    PN.AffineSectionsDecompose (lpoly ρ s) := by
  intro κ ι _ _ P Q W hW hLW hP hQ A hA b U hU hLU _ hb
  obtain ⟨V, hV, hLV, p, a, hp, ha, hpm, ham, heq⟩ :=
    exists_decompose_lpoly hρ s hW hLW hP hQ hA hU hLU hb
  exact ⟨p, a, V, hV, hLV, hp, ha, fun y hy => ⟨hpm y hy, ham y hy⟩, heq⟩

/-- The empty set satisfies `AffineSectionsDecompose`. -/
theorem affineSectionsDecompose_empty {N : ℕ} :
    PN.AffineSectionsDecompose (∅ : Set (EuclideanSpace ℂ (Fin N))) := by
  intro κ ι _ _ P Q W _ _ _ _ A _ b U _ _ _ _
  exact ⟨fun _ _ => 0, fun _ _ => 0, ∅, isOpen_empty, subset_rfl,
    fun _ => differentiableOn_empty, fun _ => differentiableOn_empty,
    fun _ hy => False.elim hy, fun _ hy => False.elim hy⟩

/-- **Theorem B on `K_s` in the chart `z_i = 1`** (`i ∈ s`). -/
theorem affineSectionsDecompose_chart_coverSet {N : ℕ} (ρ : ℝ) {s : Finset (Fin (N + 1))}
    {i : Fin (N + 1)} (hi : i ∈ s) :
    PN.AffineSectionsDecompose (PN.chart i ⁻¹' PN.coverSet ρ s) := by
  by_cases hρ : 1 ≤ ρ
  · have h : PN.chart i ⁻¹' PN.coverSet ρ s =
        lpoly ρ (Finset.univ.filter fun m => i.succAbove m ∈ s) := preimage_coverSet_eq hρ hi
    rw [h]
    exact affineSectionsDecompose_lpoly (by linarith) _
  · have h : PN.chart i ⁻¹' PN.coverSet ρ s = ∅ := preimage_coverSet_eq_empty (not_le.1 hρ) hi
    rw [h]
    exact affineSectionsDecompose_empty

/-- **Theorem B in degree one on the sets `K_s` of the cover of `ℙᴺ`**: every `K_s`, `s ≠ ∅`,
satisfies `SectionsDecompose`, the hypothesis of the long exact sequences
(`PN.coverSystem_shortExact`, `PN.coverSystem_les`). -/
theorem sectionsDecompose_coverSet_all {N : ℕ} (ρ : ℝ) :
    ∀ s : Finset (Fin (N + 1)), s.Nonempty → PN.SectionsDecompose (PN.coverSet ρ s) :=
  PN.sectionsDecompose_coverSet_of_affine fun _ hs =>
    ⟨hs.choose, hs.choose_spec, affineSectionsDecompose_chart_coverSet ρ hs.choose_spec⟩

end SGPT.GAGA.Core.Laurent
