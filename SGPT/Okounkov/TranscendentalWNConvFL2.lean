import SGPT.Okounkov.TranscendentalWNConvFL2Strict
import SGPT.Okounkov.TranscendentalWNConvFL2Exc
import SGPT.Okounkov.TranscendentalWNConvFL2Node

/-!
# The smallness estimate (eqeq) of WN21 §7

Blueprint `claude-tok-wn-fl2`, node `tok-wn-fl2:fibre-volume-small` (= `tok-wn-fl:small-neighbourhood`
of `claude-tok-wn-fl`, refining `tok-wn-conv7:small-neighbourhood`); source D. Witt Nyström,
arXiv:2103.03660 (WN21), §7, estimate (eqeq) in the proof of the hard inequality of Theorem 1.7
(`references/wn21-restricted-volume`).

**`fibreVolumeSmall : FibreVolumeSmallStatement F`.**  For every deformation `μ : 𝒳 → X × ℙ¹` to
the normal cone of `Z = Y₁`, every closed real `(1,1)`-form `Θ` on `𝒳`, every `K ⊆ X₀` whose
traces `ι⁻¹(K) ⊆ X` and `K ∩ ℰ ⊆ ℰ` are pluripolar and every `δ > 0`, there are an open
`U ⊇ (X' ∩ ℰ) ∪ K` and `r > 0` with `∫_{s⁻¹(U)} (s^*Θ)ⁿ ≤ δ` for all `0 < |τ| < r` and all
holomorphic sections `s` of `μ` over `x ↦ (x, τ)`.

## Proof

* `X' ∩ ℰ` is compact; near each of its points the monomial chart `j = m` gives polydiscs with
  fibre volumes `O(R²)` (`node_local`); a finite cover (`exists_fibreSmall_of_local`) gives an
  open `U₁ ⊇ X' ∩ ℰ` with fibre volumes `≤ δ/2`.
* `X₀ \ U₁` is compact and consists of points of `X₀ \ ℰ` (`strict_local`: product coordinates,
  `ι⁻¹(K)` Lebesgue null in charts) and of `ℰ \ X'` (`exc_local`: slice coordinates, `K ∩ ℰ`
  Lebesgue null in charts); a finite cover gives an open `U₂ ⊇ K \ U₁` with fibre volumes
  `≤ δ/2`.  Take `U = U₁ ∪ U₂`.

The pluripolar sets are only used through their Lebesgue nullity in charts and outer regularity
of Lebesgue measure, so no closedness of `K` is needed.
-/

set_option autoImplicit false

noncomputable section

universe u

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff ENNReal

namespace SGPT.Okounkov.TranscendentalWN

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Okounkov.TranscendentalWN.FL2

variable {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))

/-- **`tok-wn-fl2:fibre-volume-small`** (WN21 §7, estimate (eqeq)): `FibreVolumeSmallStatement`
holds. -/
theorem fibreVolumeSmall : FibreVolumeSmallStatement F := by
  intro 𝒳 _ _ _ μ hμ Θ ι _ hμι K hK hKι hKE δ hδ
  have _ := compactSpace_normalCone F hμ
  have hδ2 : 0 < δ / 2 := ENNReal.half_pos hδ.ne'
  -- the node `X' ∩ ℰ`
  have hS₁ : IsCompact (strictCentralFibre F μ ∩ exceptionalSet F μ) :=
    ((isClosed_strictCentralFibre F).inter (isClosed_exceptionalSet F hμ)).isCompact
  obtain ⟨U₁, hU₁o, hU₁, hU₁s⟩ := exists_fibreSmall_of_local (Θ := Θ) hS₁
    (T := strictCentralFibre F μ ∩ exceptionalSet F μ)
    (fun q hq => node_local hμ Θ hq.2 hq.1) (δ / 2) hδ2
  -- the rest of the central fibre
  set S₂ : Set 𝒳 := centralFibre F μ \ U₁ with hS₂def
  have hS₂ : IsCompact S₂ :=
    ((isClosed_centralBase F).preimage hμ.continuous).isCompact.diff hU₁o
  obtain ⟨U₂, hU₂o, hU₂, hU₂s⟩ := exists_fibreSmall_of_local (Θ := Θ) hS₂ (T := K)
    (fun q hq => by
      by_cases hqE : q ∈ exceptionalSet F μ
      · have hqX : q ∉ strictCentralFibre F μ := fun hX => hq.2 (hU₁ ⟨⟨hX, hqE⟩, ⟨hX, hqE⟩⟩)
        exact exc_local hμ Θ hK hKE hqE hqX
      · exact strict_local hμ Θ hμι hK hKι hq.1 hqE) (δ / 2) hδ2
  refine ⟨U₁ ∪ U₂, hU₁o.union hU₂o, fun z hz => Or.inl (hU₁ ⟨hz, hz⟩), fun z hzK => ?_, ?_⟩
  · by_cases hz1 : z ∈ U₁
    · exact Or.inl hz1
    · exact Or.inr (hU₂ ⟨hzK, hK hzK, hz1⟩)
  · obtain ⟨r, hr, h⟩ := hU₁s.union hU₂s
    exact ⟨r, hr, fun τ hτ hτr s hs hsμ =>
      (h τ hτ hτr s hs hsμ).trans (ENNReal.add_halves δ).le⟩

end SGPT.Okounkov.TranscendentalWN
