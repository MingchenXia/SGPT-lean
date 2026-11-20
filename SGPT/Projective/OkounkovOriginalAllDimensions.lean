import SGPT.Projective.OkounkovOriginalBookCone

/-! ENTIRE prop:Okounbiglbdl, ANY original surjective valuation, including dimension zero.
Blueprint: okounkov-original-all-dimensions.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Okounkov.OriginalBook
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set Filter MeasureTheory
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Okounkov SGPT.Okounkov.AlgebraicValuation SGPT.AlmostSemigroup
open SGPT.AlmostSemigroup.Okounkov SGPT.AlmostSemigroup.Class SGPT.Okounkov.BodyFromGrowth
open scoped Topology
variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ))
  {L : X.Modules} (a : LineBundleAtlas L)

/-- True consecutive original sections manufacture the ENTIRE original rank-zero group. -/
theorem generatedGroup_sectionSemigroup_eq_top_zero (hbig : SGPT.LineBundle.IsBig f L 0)
    (v : AddValuation X.functionField (WithTop (Lex (Fin 0 → ℤ)))) (c : X) :
    LatticeSlices.generatedGroup (sectionSemigroup v c a) = ⊤ := by
  let G := LatticeSlices.generatedGroup (sectionSemigroup v c a)
  obtain ⟨N,hN⟩ := eventually_atTop.mp hbig.eventually_exists_ne_zero
  obtain ⟨s,hs⟩ := hN N le_rfl
  obtain ⟨t,ht⟩ := hN (N+1) (Nat.le_succ N)
  have h1 : ((0 : Fin 0 → ℤ),(N:ℤ)) ∈ G := by
    have hmem : (sectionVector v c a N s hs,(N:ℤ)) ∈ G := AddSubgroup.subset_closure
      (show (sectionVector v c a N s hs,(N:ℤ)) ∈ sectionSemigroup v c a from ⟨N,s,hs,rfl⟩)
    exact (show (sectionVector v c a N s hs,(N:ℤ)) = (0,(N:ℤ)) from
      Prod.ext (Subsingleton.elim _ _) rfl) ▸ hmem
  have h2 : ((0 : Fin 0 → ℤ),((N+1:ℕ):ℤ)) ∈ G := by
    have hmem : (sectionVector v c a (N+1) t ht,((N+1:ℕ):ℤ)) ∈ G := AddSubgroup.subset_closure
      (show (sectionVector v c a (N+1) t ht,((N+1:ℕ):ℤ)) ∈ sectionSemigroup v c a from ⟨N+1,t,ht,rfl⟩)
    exact (show (sectionVector v c a (N+1) t ht,((N+1:ℕ):ℤ)) = (0,((N+1:ℕ):ℤ)) from
      Prod.ext (Subsingleton.elim _ _) rfl) ▸ hmem
  have h01 : ((0 : Fin 0 → ℤ),(1:ℤ)) ∈ G := by
    convert G.sub_mem h2 h1 using 1
    apply Prod.ext
    · exact Subsingleton.elim _ _
    · simp
  apply eq_top_iff.mpr
  rintro ⟨z,k⟩ _
  have hk := G.zsmul_mem h01 k
  convert hk using 1
  apply Prod.ext
  · exact Subsingleton.elim _ _
  · simp

/-- Genuine original dimension-zero cone from actual rank-zero section counts. -/
theorem exists_original_admissibleCone_zero (hbig : SGPT.LineBundle.IsBig f L 0)
    (v : AddValuation X.functionField (WithTop (Lex (Fin 0 → ℤ)))) (c : X) :
    ∃ C : AdmissibleCone 0, sectionSemigroup v c a ≤ latticePoints C.cone ∧
      LatticeSlices.generatedGroup (sectionSemigroup v c a) = ⊤ := by
  have hG := generatedGroup_sectionSemigroup_eq_top_zero f a hbig v c
  have hfinite (k : ℕ) : (slice (sectionSemigroup v c a : Set ((Fin 0 → ℤ) × ℤ)) (k:ℤ)).Finite :=
    Set.toFinite _
  have hpositive := positiveHeight_of_nonnegative_finiteZeroSlice (sectionSemigroup v c a)
    (sectionSemigroup_degree_nonneg (v:=v) c a) (hfinite 0)
  have hcount (k : ℕ) (_hk : 1 ≤ k) :
      (Nat.card (slice (sectionSemigroup v c a : Set ((Fin 0 → ℤ) × ℤ)) (k:ℤ)) : ℝ) ≤ 1*(k:ℝ)^0 := by
    simp only [pow_zero,mul_one]
    have hcard := Nat.card_le_card_of_injective
      (Subtype.val : slice (sectionSemigroup v c a : Set ((Fin 0 → ℤ) × ℤ)) (k:ℤ) → (Fin 0 → ℤ))
      Subtype.val_injective
    have hcard1 : Nat.card (Fin 0 → ℤ) = 1 := by simp
    rw [hcard1] at hcard
    exact_mod_cast hcard
  obtain ⟨C,hC⟩ := exists_admissibleCone_of_polynomial_growth (sectionSemigroup v c a)
    hpositive hG hfinite 1 zero_le_one hcount
  exact ⟨C,hC,hG⟩

variable (n : ℕ) [SmoothOfRelativeDimension n f] (E : ClosedProjectiveEmbedding f)
  [Nonempty (SchemeComplexPoint f)]
  (hbig : SGPT.LineBundle.IsBig f L n)
  (v : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ))))
  (hv : Function.Surjective v) (c : X)

include f E hbig hv

/-- No-dimensional-gap true original cone/full-group producer, with no auxiliary flag or cone premise. -/
theorem exists_original_admissibleCone_allDimensions :
    ∃ C : AdmissibleCone n, sectionSemigroup v c a ≤ latticePoints C.cone ∧
      LatticeSlices.generatedGroup (sectionSemigroup v c a) = ⊤ := by
  cases n with
  | zero => exact exists_original_admissibleCone_zero f a hbig v c
  | succ m => exact exists_original_admissibleCone_of_surjective f E a hbig v hv c

/-- ENTIRE source prop:Okounbiglbdl, SAME actual original body/locus, ALL dimensions/valuations. -/
theorem sectionSemigroup_mem_ownBody_fullSemigroupLocus_allDimensions :
    ∃ (hKc : IsCompact (okounkovBody v c a)) (hKv : Convex ℝ (okounkovBody v c a)),
      (interior (okounkovBody v c a)).Nonempty ∧
      ∃ hS : sectionSemigroup v c a ≤
          latticePoints (SGPT.GAGA.OkoClose.coneOver _ hKc hKv).cone,
        sourceSubset (SGPT.GAGA.OkoClose.coneOver _ hKc hKv) (sectionSemigroup v c a) hS ∈
          fullSemigroupLocus (SGPT.GAGA.OkoClose.coneOver _ hKc hKv) := by
  obtain ⟨C,hC,hG⟩ := exists_original_admissibleCone_allDimensions f a n E hbig v hv c
  obtain ⟨hKc,hKv,hS⟩ := ValGen.le_latticePoints_coneOver C (sectionSemigroup v c a) hC hG
  exact ⟨hKc,hKv,BodyGeometry.interior_body_nonempty C _ hC hG,hS,
    sourceSubset_mem_fullSemigroupLocus _ _ hS hG⟩

end SGPT.Okounkov.OriginalBook
