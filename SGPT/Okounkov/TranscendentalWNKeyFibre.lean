import SGPT.Okounkov.TranscendentalWNKeyGeometry

/-!
# The fibres `X_τ` converge to `X'` away from `ℰ` (package WN-KEY)

Blueprint `claude-tok-wn-key`, node `tok-wn-key:fibre-limit-strict` (first half: the topological
convergence); source WN21 §5.

For `τ ≠ 0` let `s_τ : X → 𝒳` be the section of `μ` over `x ↦ (x, τ)` (image `X_τ`), and `ι'` the
lift of `x ↦ (x, 0)` (image `X'`).  Off the centre `Z × {0}`, `μ` has a holomorphic inverse `s`
(TN `BlowupIsomorphismOff.exists_section_compl`), and `s_τ(x) = s(x, τ)`, `ι'(x) = s(x, 0)` for
`x ∉ Z`.  Hence `s_τ → ι'` locally uniformly on `X \ Z` as `τ → 0`
(`eventually_fibreSection_mapsTo`): for every `x ∉ Z` and every neighbourhood `O` of `ι'(x)` there
are neighbourhoods `U ∋ x` and `W ∋ 0` with `s_τ(U) ⊆ O` for all `τ ∈ W \ {0}`.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalWN

open Set Filter
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open scoped SGPT.Foundations.Analysis.Pending.ProductComplexManifold
open SGPT.Okounkov.TranscendentalMain

variable {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))

variable {𝒳 : Type u} [TopologicalSpace 𝒳] [ChartedSpace (ComplexModel (m + 1 + 1)) 𝒳]
  [IsComplexManifold (m + 1 + 1) 𝒳] {μ : 𝒳 → F.carrier × ProjectiveLine}

/-- **The fibres converge to `X'` away from `ℰ`** (`tok-wn-key:fibre-limit-strict`, topological
part): for `x ∉ Z` and a neighbourhood `O` of `ι'(x)` there are open `U ∋ x` and `W ∋ 0` such that
every section `s` of `μ` over `y ↦ (y, τ)`, `τ ∈ W \ {0}`, maps `U` into `O`. -/
theorem eventually_fibreSection_mapsTo (hμ : IsNormalConeDeformation F μ) {ι : F.carrier → 𝒳}
    (hμι : ∀ x, μ (ι x) = (x, projectiveZero)) {x : F.carrier}
    (hx : x ∉ F.flag (1 : Fin (m + 2))) {O : Set 𝒳} (hO : IsOpen O) (hxO : ι x ∈ O) :
    ∃ U : Set F.carrier, IsOpen U ∧ x ∈ U ∧ ∃ W : Set ProjectiveLine, IsOpen W ∧
      projectiveZero ∈ W ∧ ∀ p ∈ W, p ≠ projectiveZero → ∀ s : F.carrier → 𝒳,
        (∀ y, μ (s y) = (y, p)) → MapsTo s U O := by
  obtain ⟨sec, hsec, hsecμ, hsecinv⟩ := BlowupIsomorphismOff.exists_section_compl hμ
  have hC : IsOpen ((deformationCentre F)ᶜ : Set (F.carrier × ProjectiveLine)) :=
    hμ.1.1.isOpen_compl
  have hx0 : (x, projectiveZero) ∈ ((deformationCentre F)ᶜ : Set (F.carrier × ProjectiveLine)) :=
    fun h => hx ((mem_deformationCentre_iff F).mp h).1
  have hιx : μ (ι x) ∈ ((deformationCentre F)ᶜ : Set (F.carrier × ProjectiveLine)) := by
    rw [hμι]; exact hx0
  -- `sec⁻¹(O)` is an open neighbourhood of `(x, 0)` in the complement of the centre
  have hpre : IsOpen (sec ⁻¹' O) := hO.preimage hsec.continuous
  have hmem : (⟨(x, projectiveZero), hx0⟩ : (⟨(deformationCentre F)ᶜ, hC⟩ :
      TopologicalSpace.Opens (F.carrier × ProjectiveLine))) ∈ sec ⁻¹' O := by
    show sec ⟨(x, projectiveZero), hx0⟩ ∈ O
    have h := hsecinv (ι x) hιx
    have heq : (⟨μ (ι x), hιx⟩ : (⟨(deformationCentre F)ᶜ, hC⟩ :
        TopologicalSpace.Opens (F.carrier × ProjectiveLine))) = ⟨(x, projectiveZero), hx0⟩ :=
      Subtype.ext (hμι x)
    rw [← heq, h]
    exact hxO
  have hopen : IsOpen (Subtype.val '' (sec ⁻¹' O) : Set (F.carrier × ProjectiveLine)) :=
    hC.isOpenMap_subtype_val _ hpre
  have hxmem : (x, projectiveZero) ∈ (Subtype.val '' (sec ⁻¹' O) :
      Set (F.carrier × ProjectiveLine)) := ⟨_, hmem, rfl⟩
  obtain ⟨U, W, hU, hW, hxU, h0W, hUW⟩ := isOpen_prod_iff.mp hopen x projectiveZero hxmem
  refine ⟨U, hU, hxU, W, hW, h0W, fun p hp hp0 s hs y hy => ?_⟩
  obtain ⟨q, hqO, hq⟩ := hUW (mk_mem_prod hy hp)
  have hyC : μ (s y) ∈ ((deformationCentre F)ᶜ : Set (F.carrier × ProjectiveLine)) := by
    rw [hs]
    exact fun h => hp0 ((mem_deformationCentre_iff F).mp h).2
  have hsy : sec ⟨μ (s y), hyC⟩ = s y := hsecinv (s y) hyC
  have hqeq : q = ⟨μ (s y), hyC⟩ := Subtype.ext (hq.trans (hs y).symm)
  rw [← hsy, ← hqeq]
  exact hqO

end SGPT.Okounkov.TranscendentalWN
