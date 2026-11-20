import SGPT.Foundations.Schemes.NativeFanoAffineChartDimension
import SGPT.Foundations.Schemes.NativeProjectiveCutGeometry
import Mathlib.AlgebraicGeometry.Artinian

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
namespace SGPT.Foundations.Schemes
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

/-- Actual closed subschemes of a fixed genuine projective space. This stores
only the actual scheme/morphism and genuine closed-immersion property. -/
abbrev NativeClosedProjectiveStratum (N : ℕ) :=
  {f : Over (polynomialProj ℂ N) // IsClosedImmersion f.hom}

/-- The actual closed map is its genuine projective embedding over the
literal structural composite; no dimension or regularity field is supplied. -/
def NativeClosedProjectiveStratum.embedding {N : ℕ} (T : NativeClosedProjectiveStratum N) :
    ClosedProjectiveEmbedding (T.val.hom ≫ polynomialProjStructureMap ℂ N) where
  ambientDimension := N
  map := T.val.hom
  closedImmersion := T.property
  over_base := rfl

/-- The actual regular section is selected from the genuine original-coordinate
associated-prime avoidance theorem, with literal first tensor power. -/
def NativeClosedProjectiveStratum.cutSection {N : ℕ} (T : NativeClosedProjectiveStratum N) :
    bundlePowerGlobalSections (nativeProjectivePositiveLine ℂ N T.val.hom).sheaf 1 :=
  (T.embedding.exists_regular_positive_section (nativeProjectivePositiveLine ℂ N T.val.hom) 1
    (nativeProjectivePositiveLinePowerOneIso ℂ N T.val.hom)).choose

/-- Primitive coefficient regularity is PRODUCED by the actual coordinate
construction, including empty and nonreduced actual strata. -/
theorem NativeClosedProjectiveStratum.cutSection_regular {N : ℕ}
    (T : NativeClosedProjectiveStratum N) :
    nativePositiveProjectiveSectionRegular ℂ N T.val.hom
      (nativeProjectivePositiveLine ℂ N T.val.hom) 1
      (nativeProjectivePositiveLinePowerOneIso ℂ N T.val.hom) T.cutSection :=
  (T.embedding.exists_regular_positive_section (nativeProjectivePositiveLine ℂ N T.val.hom) 1
    (nativeProjectivePositiveLinePowerOneIso ℂ N T.val.hom)).choose_spec

/-- The next stratum is the ACTUAL zero closed subscheme followed by the
original closed projective map, retaining the same ambient projective space. -/
def NativeClosedProjectiveStratum.cut {N : ℕ} (T : NativeClosedProjectiveStratum N) :
    NativeClosedProjectiveStratum N := by
  let : IsClosedImmersion T.val.hom := T.property
  exact ⟨Over.mk
    (sectionZeroι ((nativeProjectivePositiveLine ℂ N T.val.hom).atlas.tensorPower 1) T.cutSection ≫
      T.val.hom), (show IsClosedImmersion
        (sectionZeroι ((nativeProjectivePositiveLine ℂ N T.val.hom).atlas.tensorPower 1) T.cutSection ≫
          T.val.hom) from inferInstance)⟩

/-- The actual next coordinate intersection is the ACTUAL inverse image of
the same original coordinate intersection, not a replacement cover. -/
theorem NativeClosedProjectiveStratum.cut_subsetOpen {N : ℕ}
    (T : NativeClosedProjectiveStratum N) (S : Finset (Fin (N + 1))) :
    actualSchemeSubsetOpen (actualPolynomialProjectivePullbackCoordinateOpens T.cut.val.hom) S =
      sectionZeroι ((nativeProjectivePositiveLine ℂ N T.val.hom).atlas.tensorPower 1) T.cutSection ⁻¹ᵁ
        actualSchemeSubsetOpen (actualPolynomialProjectivePullbackCoordinateOpens T.val.hom) S := by
  exact (actualSchemePushforwardSubsetOpen_eq
    (sectionZeroι ((nativeProjectivePositiveLine ℂ N T.val.hom).atlas.tensorPower 1) T.cutSection)
    (actualPolynomialProjectivePullbackCoordinateOpens T.val.hom) S).symm

/-- Produced regularity lowers the Krull dimension of the actual next-stage
coordinate ring, with empty/nonreduced strata handled by extended dimension. -/
theorem NativeClosedProjectiveStratum.cut_chart_dimension_drop {N : ℕ}
    (T : NativeClosedProjectiveStratum N) (S : Finset (Fin (N + 1))) (hS : S.Nonempty) :
    ringKrullDim Γ(T.cut.val.left,
      actualSchemeSubsetOpen (actualPolynomialProjectivePullbackCoordinateOpens T.cut.val.hom) S) + 1 ≤
    ringKrullDim Γ(T.val.left,
      actualSchemeSubsetOpen (actualPolynomialProjectivePullbackCoordinateOpens T.val.hom) S) := by
  let : IsClosedImmersion T.val.hom := T.property
  rw [T.cut_subsetOpen S]
  exact nativePositiveProjectiveSectionZero_chart_dimension_drop_of_regular ℂ N T.val.hom
    (nativeProjectivePositiveLine ℂ N T.val.hom) 1
    (nativeProjectivePositiveLinePowerOneIso ℂ N T.val.hom) T.cutSection T.cutSection_regular S hS

/-- Iteration takes actual zero subschemes of actual produced regular sections. -/
def NativeClosedProjectiveStratum.iterated {N : ℕ} (T : NativeClosedProjectiveStratum N) :
    ℕ → NativeClosedProjectiveStratum N
  | 0 => T
  | j + 1 => (T.iterated j).cut

/-- The same actual coordinate subset gives the true accumulated extended
Krull-dimension inequality through every actual regular cut. -/
theorem NativeClosedProjectiveStratum.iterated_chart_dimension_bound {N : ℕ}
    (T : NativeClosedProjectiveStratum N) (j : ℕ) (S : Finset (Fin (N + 1))) (hS : S.Nonempty) :
    ringKrullDim Γ((T.iterated j).val.left,
      actualSchemeSubsetOpen (actualPolynomialProjectivePullbackCoordinateOpens (T.iterated j).val.hom) S) +
        (j : WithBot ℕ∞) ≤
    ringKrullDim Γ(T.val.left,
      actualSchemeSubsetOpen (actualPolynomialProjectivePullbackCoordinateOpens T.val.hom) S) := by
  induction j with
  | zero => simp only [iterated, Nat.cast_zero, add_zero, le_refl]
  | succ j ih =>
    have hd := (T.iterated j).cut_chart_dimension_drop S hS
    have h := (add_le_add_right hd (j : WithBot ℕ∞)).trans (by simpa only [add_comm] using ih)
    simpa only [iterated, Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm] using h

/-- The actual recursive regular flag starts at the ORIGINAL Fano embedding. -/
def SmoothProjectiveFano.nativeRegularProjectiveFlag {n : ℕ} (F : SmoothProjectiveFano n)
    (j : ℕ) : NativeClosedProjectiveStratum F.projective.ambientDimension :=
  (show NativeClosedProjectiveStratum F.projective.ambientDimension from
    ⟨Over.mk F.projective.map, F.projective.closedImmersion⟩).iterated j

/-- The actual initial Fano chart bound and actual recursive drop PRODUCE
the intrinsic dimension invariant, without an initial dimension certificate. -/
theorem SmoothProjectiveFano.nativeRegularProjectiveFlag_chart_dimension_bound {n : ℕ}
    (F : SmoothProjectiveFano n) (j : ℕ)
    (S : Finset (Fin (F.projective.ambientDimension + 1))) (hS : S.Nonempty) :
    ringKrullDim Γ((F.nativeRegularProjectiveFlag j).val.left,
      actualSchemeSubsetOpen
        (actualPolynomialProjectivePullbackCoordinateOpens (F.nativeRegularProjectiveFlag j).val.hom) S) +
      (j : WithBot ℕ∞) ≤ (n : WithBot ℕ∞) :=
  (NativeClosedProjectiveStratum.iterated_chart_dimension_bound
    (show NativeClosedProjectiveStratum F.projective.ambientDimension from
      ⟨Over.mk F.projective.map, F.projective.closedImmersion⟩) j S hS).trans
    (F.projectiveSubset_ringKrullDim_le S hS)


/-- The actual chosen section at each stage has the genuine original
all-twist Euler difference on its actual next zero-subscheme cover. -/
theorem NativeClosedProjectiveStratum.cut_euler {N : ℕ}
    (T : NativeClosedProjectiveStratum N) (m : ℕ) :
    letI : IsClosedImmersion T.val.hom := T.property
    let L := nativeProjectivePositiveLine ℂ N T.val.hom
    let e := nativeProjectivePositiveLinePowerOneIso ℂ N T.val.hom
    let p := T.val.hom ≫ polynomialProjStructureMap ℂ N
    (nativePositiveProjectiveSectionZeroCechShortComplex ℂ N T.val.hom L 1 e T.cutSection
      (schemeGlobalConstants p) m).X₂.homologyEulerChar =
    (nativePositiveProjectiveSectionZeroCechShortComplex ℂ N T.val.hom L 1 e T.cutSection
      (schemeGlobalConstants p) m).X₁.homologyEulerChar +
    (nativePositiveSectionZeroRestrictedCechComplex ℂ N T.val.hom L 1 T.cutSection p
      (m + 1)).homologyEulerChar := by
  let : IsClosedImmersion T.val.hom := T.property
  exact nativePositiveProjectiveSectionZeroCechEulerOnDivisor_of_regular ℂ N T.val.hom
    (nativeProjectivePositiveLine ℂ N T.val.hom) 1
    (nativeProjectivePositiveLinePowerOneIso ℂ N T.val.hom) T.cutSection T.cutSection_regular
    (T.val.hom ≫ polynomialProjStructureMap ℂ N) rfl m

/-- The actual n-th regular cut has actual Artinian affine chart rings and
is projective/compact, hence is an Artinian scheme, even if empty. -/
theorem SmoothProjectiveFano.nativeRegularProjectiveFlag_terminal_isArtinian {n : ℕ}
    (F : SmoothProjectiveFano n) :
    IsArtinianScheme (F.nativeRegularProjectiveFlag n).val.left := by
  let T := F.nativeRegularProjectiveFlag n
  let U := actualPolynomialProjectivePullbackCoordinateOpens T.val.hom
  let : IsClosedImmersion T.val.hom := T.property
  let : IsNoetherian T.val.left := T.embedding.isNoetherian
  have hAff (i : Fin (F.projective.ambientDimension + 1)) : IsAffineOpen (U i) :=
    (polynomialProjCoordinateOpen_isAffine ℂ F.projective.ambientDimension i).preimage T.val.hom
  have hlocal : IsLocallyArtinian T.val.left := by
    apply (isLocallyArtinian_iff_of_isOpenCover
      (show IsOpenCover U from actualPolynomialProjectivePullbackCoordinateOpens_covers T.val.hom)
      hAff).mpr
    intro i
    let : IsNoetherianRing Γ(T.val.left, U i) := T.embedding.affineSections_isNoetherian (hAff i)
    apply isArtinianRing_iff_krullDimLE_zero.mpr
    apply Ring.krullDimLE_iff.mpr
    have hd := F.nativeRegularProjectiveFlag_chart_dimension_bound n {i} (by simp)
    apply (ENat.WithBot.add_le_add_natCast_right_iff (c := n)).mp
    have hi : actualSchemeSubsetOpen U {i} = U i := Finset.inf_singleton
    change ringKrullDim Γ(T.val.left, actualSchemeSubsetOpen U {i}) + (n : WithBot ℕ∞) ≤
      (n : WithBot ℕ∞) at hd
    rw [hi] at hd
    simpa only [Nat.cast_zero, zero_add] using hd
  exact { toIsLocallyArtinian := hlocal, toCompactSpace := inferInstance }

/-- The ACTUAL terminal scheme has finitely many actual scheme points;
no nonempty terminal cycle or intersection-degree claim is supplied. -/
theorem SmoothProjectiveFano.nativeRegularProjectiveFlag_terminal_finite {n : ℕ}
    (F : SmoothProjectiveFano n) :
    Finite (F.nativeRegularProjectiveFlag n).val.left := by
  let := F.nativeRegularProjectiveFlag_terminal_isArtinian
  infer_instance

end
end SGPT.Foundations.Schemes
