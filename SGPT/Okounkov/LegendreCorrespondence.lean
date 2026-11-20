import SGPT.Okounkov.Legendre

noncomputable section

namespace SGPT.Okounkov

open Set Filter Metric MeasureTheory
open scoped Topology Pointwise

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {Δ : ConvexBody V}

namespace TestFunction

@[ext] theorem ext {G H : TestFunction Δ} (hv : ∀ x, G.value x = H.value x) : G = H := by
  cases G
  cases H
  cases funext hv
  rfl

end TestFunction

namespace TestCurve

/-- Genuine body equality retains the actual source dependent cutoff interval. -/
@[ext (iff := false)] theorem ext {K L : SGPT.Okounkov.TestCurve Δ} (hm : K.max = L.max)
    (hb : ∀ t : Iio K.max,
      K.body t = L.body ⟨t, by simpa only [← hm] using t.property⟩) : K = L := by
  cases K with
  | mk m b hmono hconc hlim =>
    cases L with
    | mk m' b' hmono' hconc' hlim' =>
      dsimp only at hm
      subst m'
      have hbody : b = b' := by
        funext t
        exact hb t
      subst b'
      rfl

/-- The actual endpoint witness gives the original supremum cutoff, not an assumed maximum. -/
theorem iSup_transform_eq_max (K : SGPT.Okounkov.TestCurve Δ) :
    (⨆ x : Δ, K.transform x) = (K.max : EReal) := by
  apply le_antisymm (iSup_le K.transform_le_max)
  obtain ⟨p, hp⟩ := K.endpoint.nonempty
  let t : Iio K.max := ⟨K.max - 1, show K.max - 1 < K.max by linarith⟩
  have hpΔ : p ∈ Δ := K.body_subset t ((K.mem_endpoint p).mp hp t)
  let x : Δ := ⟨p, hpΔ⟩
  have hmax : K.transform x = (K.max : EReal) := (K.transform_eq_max_iff x).mpr hp
  rw [← hmax]
  exact le_iSup K.transform x

end TestCurve

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  {Δw : ConvexBody W}

namespace TestCurve

theorem maxReal_toTestFunction_eq (K : SGPT.Okounkov.TestCurve Δw) :
    K.toTestFunction.maxReal = K.max := by
  change (⨆ x : Δw, K.transform x).toReal = K.max
  rw [K.iSup_transform_eq_max, EReal.toReal_coe]

/-- Original inverse levels and the produced cutoff recover the entire actual original curve. -/
theorem inverse_forward (K : SGPT.Okounkov.TestCurve Δw)
    (hint : (interior (Δw : Set W)).Nonempty) :
    K.toTestFunction.toTestCurve hint = K := by
  apply TestCurve.ext K.maxReal_toTestFunction_eq
  intro t
  apply ConvexBody.ext
  ext x
  constructor
  · rintro ⟨hx, ht⟩
    exact (K.mem_body_iff_le_transform ⟨x, hx⟩ _).mpr ht
  · intro hx
    have hxΔ := K.body_subset _ hx
    exact ⟨hxΔ, (K.mem_body_iff_le_transform ⟨x, hxΔ⟩ _).mp hx⟩

/-- Exact original boundedness correspondence, obtained from true eventual low-level equality. -/
theorem isBounded_iff_toTestFunction_isBounded (K : SGPT.Okounkov.TestCurve Δw) :
    K.IsBounded ↔ K.toTestFunction.IsBounded := by
  constructor
  · intro hK
    obtain ⟨t, ht⟩ := hK.exists
    refine ⟨t, fun x ↦ K.le_transform_of_mem x t ?_⟩
    rw [ht]
    exact x.property
  · rintro ⟨c, hc⟩
    let u : Iio K.max := ⟨min c (K.max - 1),
      lt_of_le_of_lt (min_le_right c (K.max - 1)) (show K.max - 1 < K.max by linarith)⟩
    filter_upwards [eventually_le_atBot u] with t ht
    apply ConvexBody.ext
    apply subset_antisymm (K.body_subset t)
    intro x hx
    apply (K.mem_body_iff_le_transform ⟨x, hx⟩ t).mpr
    exact (EReal.coe_le_coe ((show (t : ℝ) ≤ u from ht).trans
      (min_le_left _ _))).trans (hc ⟨x, hx⟩)

end TestCurve

namespace TestFunction

/-- The genuine pointwise inverse identity recovers the actual original test function. -/
theorem forward_inverse (G : TestFunction Δw) (hint : (interior (Δw : Set W)).Nonempty) :
    (G.toTestCurve hint).toTestFunction = G := by
  apply TestFunction.ext
  intro x
  exact G.transform_toTestCurve hint x

theorem toTestCurve_isBounded_iff (G : TestFunction Δw)
    (hint : (interior (Δw : Set W)).Nonempty) :
    (G.toTestCurve hint).IsBounded ↔ G.IsBounded := by
  rw [TestCurve.isBounded_iff_toTestFunction_isBounded, G.forward_inverse hint]

end TestFunction

/-- The actual two original source transforms, with their proved inverse identities. -/
def legendreEquivOfInterior (hint : (interior (Δw : Set W)).Nonempty) :
    SGPT.Okounkov.TestCurve Δw ≃ TestFunction Δw where
  toFun := TestCurve.toTestFunction
  invFun := fun G ↦ G.toTestCurve hint
  left_inv := fun K ↦ K.inverse_forward hint
  right_inv := fun G ↦ G.forward_inverse hint

/-- Exact original positive-volume Euclidean body specialization of the genuine source bijection. -/
def legendreEquiv {n : ℕ} (Δ : ConvexBody (EuclideanSpace ℝ (Fin n)))
    (hΔ : 0 < volume (Δ : Set (EuclideanSpace ℝ (Fin n)))) :
    SGPT.Okounkov.TestCurve Δ ≃ TestFunction Δ :=
  legendreEquivOfInterior
    (SGPT.AlmostSemigroup.ConvexIntersection.interior_nonempty_of_measure_pos volume Δ.convex hΔ)

end SGPT.Okounkov
