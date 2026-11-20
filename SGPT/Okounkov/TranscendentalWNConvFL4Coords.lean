import SGPT.Okounkov.TranscendentalWNConvFL4Statement
import SGPT.Okounkov.TranscendentalWNKeyLSCSlice
import SGPT.Okounkov.TranscendentalWNConvFL3Obstacle

/-!
# Fibre-disc coordinates near `ℰ \ X'`

Blueprint `claude-tok-wn-fl4`, node `tok-wn-fl4:coords`; source WN21 §7 (the local coordinates
`(z̃₁, z₂, …, z_n, τ)` at a point of `ℰ`, in which `ℰ = {τ = 0}` and the fibres are `{τ = const}`).

`ExcCoords F μ p` bundles a holomorphic family of fibre discs `Γ : G → 𝒳`
(`G ⊆ ℂ × ℂ^{m+1}` open, `π_{ℙ¹}(μ(Γ(τ, y))) = [τ : 1]`) through `p = Γ(0, y₀)`, together with a
holomorphic left inverse `ν` of `y` on an open `O ∋ p` such that every `z ∈ O` over `[τ : 1]` is
`Γ(τ, ν z)`; `Γ(0, y) ∈ ℰ`, and the base points `π_X(μ(Γ(τ, y)))` lie in one chart of `X`.

`exists_excCoords`: such coordinates exist at every `p ∈ ℰ \ X'` (from the monomial chart data
`LSC.ExcChart` and the slice coordinates `LSC.SliceCoords` of lane WN-LSC:
`Γ(τ, y) = ℓ_j(Λ(τ, y))`, `ν = ν_S ∘ W`).

Auxiliary: the chart of `ℙ¹` at `0` is the affine coordinate (`zeroChart_affineLinePoint`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalWN

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.BlowupMonomialCharts
open SGPT.Foundations.Analysis.Pending.ProductComplexManifold
open scoped SGPT.Foundations.Analysis.Pending.ProductComplexManifold
open SGPT.Toric
open SGPT.Okounkov.TranscendentalMain
open SGPT.Okounkov.TranscendentalWN.LSC

/-! ### The chart of `ℙ¹` at `0` -/

theorem zeroChart_eq : (zeroChart : OpenPartialHomeomorph ProjectiveLine (ComplexModel 1)) =
    projectiveModelChart false := chartAt_projectiveZero

theorem zeroChart_symm (z : ComplexModel 1) :
    (zeroChart : OpenPartialHomeomorph ProjectiveLine (ComplexModel 1)).symm z =
      affineLinePoint (z 0) := by
  rw [zeroChart_eq]
  exact projectiveModelChart_false_symm z

theorem zeroChart_target :
    (zeroChart : OpenPartialHomeomorph ProjectiveLine (ComplexModel 1)).target = univ := by
  rw [zeroChart_eq]
  exact projectiveModelChart_target_eq false

theorem affineLinePoint_mem_zeroChart_source (ζ : ℂ) :
    affineLinePoint ζ ∈ (zeroChart : OpenPartialHomeomorph ProjectiveLine (ComplexModel 1)).source := by
  rw [zeroChart_eq]
  exact affineLinePoint_mem_source_false ζ

/-- **The chart of `ℙ¹` at `0` is the affine coordinate.** -/
theorem zeroChart_affineLinePoint (ζ : ℂ) :
    (zeroChart : OpenPartialHomeomorph ProjectiveLine (ComplexModel 1)) (affineLinePoint ζ) =
      projectiveModelEquiv ζ := by
  have h := zeroChart_symm (projectiveModelEquiv ζ)
  rw [projectiveModelEquiv_apply_zero] at h
  rw [← h]
  exact zeroChart.right_inv (by rw [zeroChart_target]; trivial)

theorem zeroChart_projectiveZero :
    (zeroChart : OpenPartialHomeomorph ProjectiveLine (ComplexModel 1)) projectiveZero = 0 := by
  rw [← affineLinePoint_zero, zeroChart_affineLinePoint, map_zero]

theorem eq_affineLinePoint_of_mem_zeroChart_source {q : ProjectiveLine}
    (hq : q ∈ (zeroChart : OpenPartialHomeomorph ProjectiveLine (ComplexModel 1)).source) :
    q = affineLinePoint ((zeroChart : OpenPartialHomeomorph ProjectiveLine (ComplexModel 1)) q 0) := by
  rw [← zeroChart_symm, zeroChart.left_inv hq]

/-! ### Fibre-disc coordinates -/

variable {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))

variable {𝒳 : Type u} [TopologicalSpace 𝒳] [ChartedSpace (ComplexModel (m + 1 + 1)) 𝒳]
  [IsComplexManifold (m + 1 + 1) 𝒳]

/-- **`tok-wn-fl4:coords`**: a holomorphic family of fibre discs through `p` with a holomorphic
left inverse `ν` of the parameter `y` near `p`. -/
structure ExcCoords (μ : 𝒳 → F.carrier × ProjectiveLine) (p : 𝒳) where
  Γ : ℂ × ComplexModel (m + 1) → 𝒳
  G : Set (ℂ × ComplexModel (m + 1))
  isOpen_G : IsOpen G
  smooth : ∀ q ∈ G, ContMDiffAt 𝓘(ℂ, ℂ × ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1 + 1)) ∞ Γ q
  fibre : ∀ q ∈ G, (μ (Γ q)).2 = affineLinePoint q.1
  y₀ : ComplexModel (m + 1)
  mem_G : ((0 : ℂ), y₀) ∈ G
  Γ_y₀ : Γ (0, y₀) = p
  O : Set 𝒳
  isOpen_O : IsOpen O
  mem_O : p ∈ O
  ν : 𝒳 → ComplexModel (m + 1)
  smooth_ν : ∀ z ∈ O, ContMDiffAt 𝓘(ℂ, ComplexModel (m + 1 + 1)) 𝓘(ℂ, ComplexModel (m + 1)) ∞ ν z
  ν_Γ : ∀ q ∈ G, Γ q ∈ O → ν (Γ q) = q.2
  affine : ∀ z ∈ O, ∃ ζ : ℂ, (μ z).2 = affineLinePoint ζ
  Γ_ν : ∀ z ∈ O, ∀ ζ : ℂ, (μ z).2 = affineLinePoint ζ → (ζ, ν z) ∈ G ∧ Γ (ζ, ν z) = z
  exceptional : ∀ y, ((0 : ℂ), y) ∈ G → Γ (0, y) ∈ O → Γ (0, y) ∈ exceptionalSet F μ
  x₀ : F.carrier
  base : ∀ q ∈ G, (μ (Γ q)).1 ∈ (chartAt (ComplexModel (m + 1)) x₀).source

namespace ExcCoords

variable {F} {μ : 𝒳 → F.carrier × ProjectiveLine} {p : 𝒳} (K : ExcCoords F μ p)

theorem continuousOn_Γ : ContinuousOn K.Γ K.G := fun q hq =>
  (K.smooth q hq).continuousAt.continuousWithinAt

theorem continuousOn_ν : ContinuousOn K.ν K.O := fun z hz =>
  (K.smooth_ν z hz).continuousAt.continuousWithinAt

/-- The slice `y ↦ Γ(τ, y)` is holomorphic. -/
theorem smooth_slice {τ : ℂ} {y : ComplexModel (m + 1)} (h : (τ, y) ∈ K.G) :
    ContMDiffAt 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1 + 1)) ∞
      (fun y => K.Γ (τ, y)) y := by
  have hin : ContMDiffAt 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ℂ × ComplexModel (m + 1)) ∞
      (fun y => (τ, y)) y :=
    (contDiff_const.prodMk contDiff_id).contMDiff.contMDiffAt
  exact ContMDiffAt.comp (g := K.Γ) y (K.smooth _ h) hin

/-- Points of `O` over `0` lie on the slice `τ = 0`. -/
theorem Γ_ν_zero {z : 𝒳} (hz : z ∈ K.O) (h0 : (μ z).2 = projectiveZero) :
    ((0 : ℂ), K.ν z) ∈ K.G ∧ K.Γ (0, K.ν z) = z :=
  K.Γ_ν z hz 0 (by rw [h0, affineLinePoint_zero])

end ExcCoords

/-- **`tok-wn-fl4:coords`**: fibre-disc coordinates exist at every point of `ℰ \ X'`. -/
theorem exists_excCoords {μ : 𝒳 → F.carrier × ProjectiveLine} (hμ : IsNormalConeDeformation F μ)
    {p : 𝒳} (hpE : p ∈ exceptionalSet F μ) (hpX : p ∉ strictCentralFibre F μ) :
    Nonempty (ExcCoords F μ p) := by
  classical
  obtain ⟨C⟩ := nonempty_excChart F hμ hpE
  obtain ⟨S⟩ := SliceCoords.nonempty C hpE hpX
  set D := monomialDomain C.Ψ m C.j with hD
  have hWpD : C.W p ∈ D := C.W_mem_monomialDomain C.hqO
  set p₀ : LiftedOpen.{u} D := LiftedOpen.mk D (C.W p) hWpD with hp₀
  set Γ₁ : ComplexModel 1 × ComplexModel (m + 1) → 𝒳 := fun q => C.ℓ (liftMk D p₀ (S.Λ q))
    with hΓ₁
  set L : ℂ × ComplexModel (m + 1) → ComplexModel 1 × ComplexModel (m + 1) :=
    fun q => (projectiveModelEquiv q.1, q.2) with hL
  have hLc : ContDiff ℂ ∞ L :=
    ((projectiveModelEquiv : ℂ →L[ℂ] ComplexModel 1).contDiff.comp contDiff_fst).prodMk contDiff_snd
  set G₀ : Set (ComplexModel 1 × ComplexModel (m + 1)) := S.G ∩ S.Λ ⁻¹' D with hG₀
  have hΛc : ContinuousOn S.Λ S.G := fun q hq => (S.hΛ q hq).continuousAt.continuousWithinAt
  have hG₀o : IsOpen G₀ := hΛc.isOpen_inter_preimage S.hG D.isOpen
  have hΓ₁sm : ∀ q ∈ G₀, ContMDiffAt 𝓘(ℂ, ComplexModel 1 × ComplexModel (m + 1))
      𝓘(ℂ, ComplexModel (m + 1 + 1)) ∞ Γ₁ q := fun q hq =>
    (C.hℓ _).comp q ((contMDiffAt_liftMk p₀ hq.2).comp q (S.hΛ q hq.1).contMDiffAt)
  have hΓ₁W : ∀ q ∈ G₀, Γ₁ q ∈ C.O → C.W (Γ₁ q) = S.Λ q := fun q hq hO => C.W_ℓ hq.2 hO
  have hΓ₁τ : ∀ q ∈ G₀, (μ (Γ₁ q)).2 ∈ zeroChart.source ∧
      zeroChart (μ (Γ₁ q)).2 = q.1 + zeroChart projectiveZero := by
    intro q hq
    have hf := C.μ_ℓ_mem_flatDomain (liftMk D p₀ (S.Λ q))
    have h1 := C.hΨτ _ hf
    rw [C.μ_ℓ, C.flat_monomialChart, toModel_liftMk p₀ hq.2, S.hτΛ q hq.1] at h1
    have hsrc : (μ (Γ₁ q)).2 ∈ zeroChart.source := by
      have := hf.1
      simp only [chartAt_prod, prodChart_source, mem_prod] at this
      exact this.2
    refine ⟨hsrc, ?_⟩
    rw [C.μ_ℓ] at hsrc ⊢
    rw [h1, sub_add_cancel]
  have hq0 : (μ p).2 = projectiveZero := ((mem_deformationCentre_iff F).mp hpE).2
  have hτp : ((splitL m).symm (monomial m C.j (C.W p))).2 = 0 := by
    rw [C.tau_eq C.hqO, hq0, sub_self]
  obtain ⟨hP₀G, hΛp⟩ := S.hΛν p S.hqO' 0 hτp
  refine ⟨{
    Γ := fun q => Γ₁ (L q)
    G := L ⁻¹' G₀
    isOpen_G := hG₀o.preimage hLc.continuous
    smooth := fun q hq => ContMDiffAt.comp (g := Γ₁) q (hΓ₁sm _ hq) hLc.contMDiff.contMDiffAt
    fibre := fun q hq => by
      obtain ⟨hsrc, heq⟩ := hΓ₁τ _ hq
      rw [zeroChart_projectiveZero, add_zero] at heq
      rw [eq_affineLinePoint_of_mem_zeroChart_source hsrc, heq]
      simp [hL, projectiveModelEquiv_apply_zero]
    y₀ := S.ν (C.W p)
    mem_G := by
      show L (0, S.ν (C.W p)) ∈ G₀
      simp only [hL, map_zero]
      exact ⟨hP₀G, show S.Λ (0, S.ν (C.W p)) ∈ D by rw [hΛp]; exact hWpD⟩
    Γ_y₀ := by
      show Γ₁ (L (0, S.ν (C.W p))) = p
      simp only [hL, map_zero, hΓ₁]
      rw [hΛp]
      exact C.ℓ_W C.hqO
    O := S.O'
    isOpen_O := S.hO'
    mem_O := S.hqO'
    ν := fun z => S.ν (C.W z)
    smooth_ν := fun z hz => S.ν.contMDiff.contMDiffAt.comp z (C.hW z (S.hO'O hz))
    ν_Γ := fun q hq hO => by
      show S.ν (C.W (Γ₁ (L q))) = q.2
      rw [hΓ₁W _ hq (S.hO'O hO), S.hνΛ _ hq.1]
    affine := fun z hz => by
      have hsrc : (μ z).2 ∈ zeroChart.source := by
        have := (C.hWμ z (S.hO'O hz)).1.1
        simp only [chartAt_prod, prodChart_source, mem_prod] at this
        exact this.2
      exact ⟨_, eq_affineLinePoint_of_mem_zeroChart_source hsrc⟩
    Γ_ν := fun z hz ζ hζ => by
      have hτz : ((splitL m).symm (monomial m C.j (C.W z))).2 = projectiveModelEquiv ζ := by
        rw [C.tau_eq (S.hO'O hz), hζ, zeroChart_affineLinePoint, zeroChart_projectiveZero,
          sub_zero]
      obtain ⟨hG, hΛ⟩ := S.hΛν z hz _ hτz
      refine ⟨⟨hG, show S.Λ (projectiveModelEquiv ζ, S.ν (C.W z)) ∈ D by
        rw [hΛ]; exact C.W_mem_monomialDomain (S.hO'O hz)⟩, ?_⟩
      show C.ℓ (liftMk D p₀ (S.Λ (projectiveModelEquiv ζ, S.ν (C.W z)))) = z
      rw [hΛ]
      exact C.ℓ_W (S.hO'O hz)
    exceptional := fun y hy hO => by
      have hy' : (0, y) ∈ G₀ := by simpa [hL] using hy
      have hO' : Γ₁ (0, y) ∈ C.O := by simpa [hL] using S.hO'O hO
      show Γ₁ (L (0, y)) ∈ exceptionalSet F μ
      simp only [hL, map_zero]
      rw [C.mem_exceptional_iff hO', hΓ₁W _ hy' hO']
      exact S.hΛE y hy'.1
    x₀ := C.x₀
    base := fun q _ => by
      have := (C.μ_ℓ_mem_flatDomain (liftMk D p₀ (S.Λ (L q)))).1
      simp only [chartAt_prod, prodChart_source, mem_prod] at this
      exact this.1 }⟩

end SGPT.Okounkov.TranscendentalWN
