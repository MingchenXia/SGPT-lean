import SGPT.Projective.OkounkovOriginalBigRatios

/-! Full ORIGINAL section lattice for every SURJECTIVE original valuation.
Blueprint: okounkov-original-valuation-generation.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Okounkov.OriginalRationalPairs
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Opposite TopologicalSpace Filter
open SGPT.Okounkov SGPT.Okounkov.AlgebraicValuation SGPT.AlmostSemigroup
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
variable {X : Scheme.{0}} [IsIntegral X]
  (f : X ⟶ Spec (.of ℂ)) (E : ClosedProjectiveEmbedding f)
  {m : ℕ} [SmoothOfRelativeDimension (m+1) f] [Nonempty (SchemeComplexPoint f)]
local instance originalGenerationTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance originalGenerationCharts : ChartedSpace (ComplexModel (m+1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (m+1)
local instance originalGenerationManifold [IsSeparated f] [QuasiCompact f] :
    IsComplexManifold (m+1) (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f (m+1)
variable (Y : Fin (m+1+1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y)
  {L : X.Modules} (a : LineBundleAtlas L) (hbig : SGPT.LineBundle.IsBig f L (m+1))
  (v : AddValuation X.functionField (WithTop (Lex (Fin (m+1) → ℤ))))
  (hv : Function.Surjective v) (c : X)

include f E Y hY hbig hv

/-- Every horizontal original lattice vector is a difference of SAME-degree actual original section points. -/
theorem horizontal_mem_generatedGroup_of_surjective (z : Fin (m+1) → ℤ) :
    (z,(0:ℤ)) ∈ LatticeSlices.generatedGroup (sectionSemigroup v c a) := by
  obtain ⟨r,hr⟩ := hv ((toLex z : Lex (Fin (m+1) → ℤ)) : WithTop _)
  have hr0 : r ≠ 0 := by
    intro h0
    rw [h0,v.map_zero] at hr
    exact WithTop.top_ne_coe hr
  obtain ⟨k,-,s,t,hs,ht,hq⟩ := exists_bigLine_equalDegree_sectionPair a f E Y hY hbig r hr0
  let U := a.opens (a.centerIndex c)
  let : Nonempty U := ⟨⟨c,a.centerIndex_mem c⟩⟩
  let e := (a.frame (a.centerIndex c)).tensorPower k
  have hquot := hq U inferInstance e
  have hd : sectionValue v c a k s - sectionValue v c a k t =
      ((toLex z : Lex (Fin (m+1) → ℤ)) : WithTop _) := by
    change v (globalSectionToFunctionField e s) - v (globalSectionToFunctionField e t) = _
    rw [← v.map_div,hquot]
    exact hr
  rw [sectionValue_eq_vector c a k s hs,sectionValue_eq_vector c a k t ht] at hd
  rw [← WithTop.LinearOrderedAddCommGroup.coe_sub] at hd
  have hz : sectionVector v c a k s hs - sectionVector v c a k t ht = z :=
    toLex.injective (WithTop.coe_injective hd)
  have h1 : (sectionVector v c a k s hs,(k:ℤ)) ∈ sectionSemigroup v c a := ⟨k,s,hs,rfl⟩
  have h2 : (sectionVector v c a k t ht,(k:ℤ)) ∈ sectionSemigroup v c a := ⟨k,t,ht,rfl⟩
  have he : (sectionVector v c a k s hs,(k:ℤ)) - (sectionVector v c a k t ht,(k:ℤ)) = (z,0) := by
    apply Prod.ext
    · exact hz
    · simp
  exact he ▸ AddSubgroup.sub_mem _ (AddSubgroup.subset_closure h1) (AddSubgroup.subset_closure h2)

/-- Source prop:Okounbiglbdl Step2 for an ARBITRARY SURJECTIVE valuation, with NO cone/generation premise. -/
theorem generatedGroup_sectionSemigroup_eq_top_of_surjective :
    LatticeSlices.generatedGroup (sectionSemigroup v c a) = ⊤ := by
  classical
  let G := LatticeSlices.generatedGroup (sectionSemigroup v c a)
  have hh (z : Fin (m+1) → ℤ) : (z,(0:ℤ)) ∈ G :=
    horizontal_mem_generatedGroup_of_surjective f E Y hY a hbig v hv c z
  obtain ⟨N,hN⟩ := eventually_atTop.mp hbig.eventually_exists_ne_zero
  obtain ⟨s,hs⟩ := hN N le_rfl
  obtain ⟨t,ht⟩ := hN (N+1) (Nat.le_succ N)
  let x := sectionVector v c a N s hs
  let y := sectionVector v c a (N+1) t ht
  have h1 : (x,(N:ℤ)) ∈ G := AddSubgroup.subset_closure (show (x,(N:ℤ)) ∈ sectionSemigroup v c a from ⟨N,s,hs,rfl⟩)
  have h2 : (y,((N+1:ℕ):ℤ)) ∈ G := AddSubgroup.subset_closure
    (show (y,((N+1:ℕ):ℤ)) ∈ sectionSemigroup v c a from ⟨N+1,t,ht,rfl⟩)
  have hd : (y-x,(1:ℤ)) ∈ G := by
    convert G.sub_mem h2 h1 using 1
    ext <;> simp
  have h01 : ((0 : Fin (m+1) → ℤ),(1:ℤ)) ∈ G := by
    convert G.sub_mem hd (hh (y-x)) using 1
    ext <;> simp
  apply eq_top_iff.mpr
  rintro ⟨z,k⟩ _
  have h := G.add_mem (hh z) (G.zsmul_mem h01 k)
  simpa using h

end SGPT.Okounkov.OriginalRationalPairs
