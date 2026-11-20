import SGPT.AlmostSemigroup.OkounkovExtension

/-! Actual almost-semigroup membership and bodies descend across zero source distance. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.AlmostSemigroup.DistanceZeroTransport
open Class OkounkovExtension

/-- Zero source distance transports both genuine closure membership and positive volume. -/
theorem mem_almostSemigroupLocus_of_dist_eq_zero {n : ℕ} {C : AdmissibleCone n}
    (S T : ConeSubset C) (hzero : dist S T = 0) (hT : T ∈ almostSemigroupLocus C) :
    S ∈ almostSemigroupLocus C := by
  refine ⟨?_, ?_⟩
  · apply Metric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨U,hU,hUT⟩ := Metric.mem_closure_iff.mp hT.1 ε hε
    refine ⟨U,hU,?_⟩
    calc
      dist S U ≤ dist S T + dist T U := dist_triangle _ _ _
      _ < ε := by rw [hzero,zero_add]; exact hUT
  · have hvol : S.volume = T.volume :=
      ((Metric.inseparable_iff.mpr hzero).map ConeSubset.continuous_volume).eq
    change 0 < S.volume
    rw [hvol]
    exact hT.2

/-- The SAME actual continuous body extension agrees on a source-distance-zero pair. -/
theorem bodyExtension_eq_of_dist_eq_zero {n : ℕ} {C : AdmissibleCone n}
    (S T : ConeSubset C) (hzero : dist S T = 0) (hT : T ∈ almostSemigroupLocus C) :
    bodyExtension (⟨S,mem_almostSemigroupLocus_of_dist_eq_zero S T hzero hT⟩ : AlmostSpace C) =
      bodyExtension (⟨T,hT⟩ : AlmostSpace C) := by
  have hi : Inseparable
      (⟨S,mem_almostSemigroupLocus_of_dist_eq_zero S T hzero hT⟩ : AlmostSpace C)
      (⟨T,hT⟩ : AlmostSpace C) := Metric.inseparable_iff.mpr hzero
  exact (hi.map (continuous_bodyExtension C)).eq

end SGPT.AlmostSemigroup.DistanceZeroTransport
