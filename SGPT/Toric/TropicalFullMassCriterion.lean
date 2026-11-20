import SGPT.Toric.TropicalLocalMass
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

set_option autoImplicit false
noncomputable section

open Set MeasureTheory
open scoped ENNReal RealInnerProductSpace

namespace SGPT.Convex

/-- The original Euclidean Haar rigidity is the genuine volume-preserving
transport of the completed coordinate compact-body theorem. -/
theorem subset_of_euclidean_volume_inter_eq {n : ℕ}
    {K L : Set (EuclideanSpace ℝ (Fin n))}
    (hK : IsCompact K) (hL : IsClosed L) (hconv : Convex ℝ K)
    (hint : (interior K).Nonempty) (heq : volume.real (K ∩ L) = volume.real K) :
    K ⊆ L := by
  let e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (Fin n → ℝ) :=
    PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)
  have hpres : MeasurePreserving e (volume : Measure (EuclideanSpace ℝ (Fin n))) volume := by
    simpa only [e, PiLp.coe_continuousLinearEquiv] using
      PiLp.volume_preserving_ofLp (Fin n)
  have hvolume (S : Set (EuclideanSpace ℝ (Fin n))) : volume (e '' S) = volume S := by
    have h := hpres.measure_preimage_emb e.toHomeomorph.measurableEmbedding (e '' S)
    rw [preimage_image_eq _ e.injective] at h
    exact h.symm
  have hreal (S : Set (EuclideanSpace ℝ (Fin n))) : volume.real (e '' S) = volume.real S := by
    rw [measureReal_def, measureReal_def, hvolume]
  have hinterior : (interior (e '' K)).Nonempty := by
    change (interior (e.toHomeomorph '' K)).Nonempty
    rw [← e.toHomeomorph.image_interior]
    exact hint.image e
  have hmeasure : volume.real ((e '' K) ∩ (e '' L)) = volume.real (e '' K) := by
    rw [← image_inter e.injective, hreal, hreal]
    exact heq
  have hsub := SGPT.AlmostSemigroup.Intersection.subset_of_volume_inter_eq
    (hK.image e.continuous) (e.toHomeomorph.isClosed_image.mpr hL)
    (hconv.linear_image e.toLinearMap) hinterior hmeasure
  intro x hx
  obtain ⟨y, hy, hxy⟩ := hsub ⟨x, hx, rfl⟩
  exact e.injective hxy ▸ hy

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The genuine original Euclidean Haar converse keeps the same perfect
pairing, actual support-growth class and ordinary empty-interior branch. -/
theorem mem_fullMassClass_iff_alexandrovMeasure_univ_eq_euclidean {n : ℕ}
    (B : E →ₗ[ℝ] (EuclideanSpace ℝ (Fin n)) →ₗ[ℝ] ℝ) [B.IsContPerfPair]
    {P : Set (EuclideanSpace ℝ (Fin n))} (hP : IsCompact P) (hne : P.Nonempty)
    (hconv : Convex ℝ P) {f : E → EReal} (hf : f ∈ GrowthClass B P) :
    f ∈ FullMassClass B P ↔ alexandrovMeasure B volume f univ =
      ((Module.finrank ℝ E).factorial : ENNReal) * volume P := by
  have hlsc := lowerSemicontinuous_of_isClosedConvex
    (isClosedConvex_of_mem_growthClass B hP hne hf)
  have hsub := ((singularityLE_support_iff_full_domain_rawSubgradientImage_subset
    B hP hne hconv hf.1).mp hf.2).2
  have hclSub : closure (rawSubgradientImage B f) ⊆ P := closure_minimal hsub hP.isClosed
  constructor
  · exact alexandrovMeasure_univ_eq_body_of_mem_fullMassClass B hP hne hconv
  · intro hmass
    refine ⟨hf, ?_⟩
    by_cases hempty : interior P = ∅
    · exact Or.inl hempty
    · apply Or.inr
      have hmass' : ((Module.finrank ℝ E).factorial : ENNReal) *
          volume (closure (rawSubgradientImage B f)) =
          ((Module.finrank ℝ E).factorial : ENNReal) * volume P := by
        rw [← alexandrovMeasure_univ_eq_closure_rawSubgradientImage B hf.1 hlsc]
        exact hmass
      have hcoef : ((Module.finrank ℝ E).factorial : ENNReal) ≠ 0 := by
        exact_mod_cast Nat.factorial_ne_zero (Module.finrank ℝ E)
      have hmeasure := (ENNReal.mul_right_inj hcoef
        (ENNReal.natCast_ne_top (Module.finrank ℝ E).factorial)).mp hmass'
      have hreal : volume.real (P ∩ closure (rawSubgradientImage B f)) = volume.real P := by
        rw [inter_eq_right.mpr hclSub, measureReal_def, measureReal_def, hmeasure]
      have hPsub := subset_of_euclidean_volume_inter_eq
        hP isClosed_closure hconv (Set.nonempty_iff_ne_empty.mpr hempty) hreal
      exact subset_antisymm hclSub hPsub

end SGPT.Convex

namespace SGPT.Toric

open SGPT.Convex

/-- The SAME canonical tropical BT total is equivalent to the genuine
geometric full-mass class, without a global finite-mass or NP premise. -/
theorem mem_fullMassClass_iff_tropicalCanonicalBTMeasure_univ_eq {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hc : ConvexOn ℝ univ f)
    {P : Set (EuclideanSpace ℝ (Fin n))} (hP : IsCompact P) (hne : P.Nonempty)
    (hconv : Convex ℝ P)
    (hf : (fun a => (f a : EReal)) ∈ GrowthClass (innerₗ (EuclideanSpace ℝ (Fin n))) P) :
    (fun a => (f a : EReal)) ∈ FullMassClass (innerₗ (EuclideanSpace ℝ (Fin n))) P ↔
      tropicalCanonicalBTMeasure hc univ = (n.factorial : ENNReal) * volume P := by
  obtain ⟨hT, _⟩ := exists_compact_tropical_torus_lift (n := n) isCompact_empty
  have htotal := congrArg (fun μ : Measure (EuclideanSpace ℝ (Fin n)) => μ univ)
    (tropicalization_canonicalBTMeasure_eq_alexandrov hc)
  rw [Measure.map_apply hT MeasurableSet.univ, preimage_univ] at htotal
  rw [htotal]
  simpa using mem_fullMassClass_iff_alexandrovMeasure_univ_eq_euclidean
    (innerₗ (EuclideanSpace ℝ (Fin n))) hP hne hconv hf

end SGPT.Toric
