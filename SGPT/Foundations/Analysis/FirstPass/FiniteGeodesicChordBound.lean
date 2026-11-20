import SGPT.Foundations.Analysis.FirstPass.FiniteGeodesics
import SGPT.Foundations.Analysis.FirstPass.SubgeodesicChord
import SGPT.Foundations.Analysis.FirstPass.SubgeodesicAffineTranslation

set_option autoImplicit false

/-!
# Chord upper bound for Perron finite geodesics

Every competitor lies below the chord joining its actual endpoint limits.
Monotonicity of a nonnegative extended-real affine combination then moves
that chord to the requested Perron endpoint bounds.
-/

open Set

namespace SGPT.Foundations.Analysis.FirstPass

noncomputable section

/-- The extended-real chord is monotone in both endpoints at a time in the
closed unit interval. -/
theorem eRealChord_mono {a b c d : EReal} {t : ℝ}
    (ha : a ≤ c) (hb : b ≤ d) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    eRealChord a b t ≤ eRealChord c d t := by
  apply add_le_add
  · exact mul_le_mul_of_nonneg_left ha
      (EReal.coe_nonneg.mpr (sub_nonneg.mpr ht1))
  · exact mul_le_mul_of_nonneg_left hb (EReal.coe_nonneg.mpr ht0)

/-- A chord of two values below `⊤` stays below `⊤` on the closed unit
interval.  Either endpoint may still be the pole `⊥`. -/
theorem eRealChord_ne_top {a b : EReal} {t : ℝ}
    (ha : a ≠ ⊤) (hb : b ≠ ⊤) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    eRealChord a b t ≠ ⊤ := by
  exact EReal.add_ne_top
    (eReal_const_mul_ne_top (sub_nonneg.mpr ht1) ha)
    (eReal_const_mul_ne_top ht0 hb)

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The Perron finite geodesic lies below the extended-real chord joining
the requested theta-PSH endpoint bounds. -/
theorem finiteGeodesic_le_eRealChord
    {θ : SmoothRealForm n M 2} {u₀ u₁ : M → EReal}
    (hu₀ : IsThetaPshPotential θ u₀) (hu₁ : IsThetaPshPotential θ u₁)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    finiteGeodesic θ u₀ u₁ t ≤ fun x => eRealChord (u₀ x) (u₁ x) t := by
  apply (finiteGeodesic_le_iff
    (hu₀.upperSemicontinuous_eRealChord hu₁ ht.1.le ht.2.le)).2
  intro curve hcurve x
  rcases hcurve with ⟨v₀, v₁, hv₀, hv₁, hv₀u₀, hv₁u₁, hcurve⟩
  exact (hcurve.le_eRealChord ht x).trans
    (eRealChord_mono (hv₀u₀ x) (hv₁u₁ x) ht.1.le ht.2.le)

/-- For ordered endpoints, every nonnegative affine downward translate of
the left endpoint is a Perron competitor. -/
theorem affineLower_le_finiteGeodesic_of_le
    {θ : SmoothRealForm n M 2} {u₀ u₁ : M → EReal}
    (hu₀ : IsThetaPshPotential θ u₀) (hu₀u₁ : u₀ ≤ u₁)
    {C : ℝ} (hC : 0 ≤ C) (t : ℝ) :
    (fun x => u₀ x + (((-C) * t : ℝ) : EReal)) ≤
      finiteGeodesic θ u₀ u₁ t := by
  let curve : ℝ → M → EReal :=
    affineTranslatedCurve (fun _ : ℝ => u₀) (-C) 0
  have hcurve : IsSubgeodesicFrom θ curve u₀
      (fun x => u₀ x + ((-C : ℝ) : EReal)) := by
    simpa [curve] using (isSubgeodesicFrom_const hu₀).affineTranslated (-C) 0
  have hright : (fun x => u₀ x + ((-C : ℝ) : EReal)) ≤ u₁ := by
    intro x
    apply le_trans ?_ (hu₀u₁ x)
    apply (EReal.addLECancellable_coe C).add_le_add_iff_right.mp
    calc
      (u₀ x + ((-C : ℝ) : EReal)) + (C : EReal) =
          u₀ x + (((-C) + C : ℝ) : EReal) := by
            rw [add_assoc, ← EReal.coe_add]
      _ = u₀ x := by simp
      _ ≤ u₀ x + (C : EReal) :=
        le_add_of_nonneg_right (EReal.coe_nonneg.mpr hC)
  have hmem : curve ∈ finiteGeodesicCompetitors θ u₀ u₁ :=
    ⟨u₀, fun x => u₀ x + ((-C : ℝ) : EReal), hu₀,
      hcurve.right_endpoint, le_rfl, hright, hcurve⟩
  intro x
  simpa only [curve, affineTranslatedCurve_apply, add_zero] using
    competitor_slice_le_finiteGeodesic hmem t x

end

end SGPT.Foundations.Analysis.FirstPass
