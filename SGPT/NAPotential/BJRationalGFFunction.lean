import SGPT.NAPotential.BJSectionLogNorm
import Mathlib.Order.ConditionallyCompleteLattice.Finset

/-! Actual finite rational section functions on all source Berkovich points.
This is genuine GF infrastructure; no arbitrary numerical-class map or
varying-bundle BJ net-closure proposition is installed by these definitions. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.NAPotential.Berkovich.BJSections
open AlgebraicGeometry CategoryTheory Topology Opposite SGPT.Foundations.Schemes
variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} [IsProper f]

/-- Genuine finite nonzero native sections of A^n and rational weights,
normalized by the positive integer m. Its rational presentation is (n/m)A. -/
structure RationalGFData (L : X.Modules) (n m : ℕ) where
  I : Type
  fintype : Fintype I
  nonempty : Nonempty I
  sections : I → bundlePowerGlobalSections L n
  sections_ne_zero : ∀ i,sections i≠0
  weight : I → ℚ
  power_pos : 0<n
  denominator_pos : 0<m

attribute [instance] RationalGFData.fintype RationalGFData.nonempty

variable {L : X.Modules} {n m : ℕ}

/-- Actual finite maximum before normalization. -/
def finiteMaximum (a : LineBundleAtlas L) (D : RationalGFData L n m)
    (v : BerkovichPoint f) : EReal :=
  ⨆ i : D.I,sectionLogNorm a n (D.sections i) v+((D.weight i:ℝ):EReal)

/-- Literal rational GF formula; every evaluation is an actual source
semi-valuation of a nonzero actual sheaf section. -/
def rationalGFFunction (a : LineBundleAtlas L) (D : RationalGFData L n m)
    (v : BerkovichPoint f) : EReal :=
  (((1/(m:ℝ)):ℝ):EReal)*finiteMaximum a D v

def weightMaximum (D : RationalGFData L n m) : EReal :=
  ⨆ i : D.I,((D.weight i:ℝ):EReal)

/-- The source finite maximum really is attained, even on common base loci. -/
theorem finiteMaximum_attained (a : LineBundleAtlas L) (D : RationalGFData L n m)
    (v : BerkovichPoint f) :
    ∃ i : D.I,finiteMaximum a D v=
      sectionLogNorm a n (D.sections i) v+((D.weight i:ℝ):EReal) := by
  obtain ⟨i,hi⟩ := exists_eq_ciSup_of_finite
    (f:=fun i:D.I => sectionLogNorm a n (D.sections i) v+((D.weight i:ℝ):EReal))
  exact ⟨i,hi.symm⟩

theorem finiteMaximum_le_weightMaximum (a : LineBundleAtlas L) (D : RationalGFData L n m)
    (v : BerkovichPoint f) : finiteMaximum a D v≤weightMaximum D := by
  apply iSup_le
  intro i
  have hlog := sectionLogNorm_nonpos a n (D.sections i) v
  calc
    sectionLogNorm a n (D.sections i) v+((D.weight i:ℝ):EReal)≤((D.weight i:ℝ):EReal) := by
      simpa only [zero_add] using add_le_add hlog (le_refl ((D.weight i:ℝ):EReal))
    _≤weightMaximum D := le_iSup (fun i:D.I => ((D.weight i:ℝ):EReal)) i

theorem weightMaximum_eq_coe (D : RationalGFData L n m) :
    ∃ r : ℝ,weightMaximum D=(r:EReal) := by
  obtain ⟨i,hi⟩ := exists_eq_ciSup_of_finite (f:=fun i:D.I => ((D.weight i:ℝ):EReal))
  exact ⟨(D.weight i:ℝ),hi.symm⟩

/-- No positive infinity can occur anywhere on the full Berkovich space. -/
theorem rationalGFFunction_ne_top (a : LineBundleAtlas L) (D : RationalGFData L n m)
    (v : BerkovichPoint f) : rationalGFFunction a D v≠⊤ := by
  obtain ⟨r,hr⟩ := weightMaximum_eq_coe D
  have hc : 0≤1/(m:ℝ) := div_nonneg zero_le_one (Nat.cast_nonneg _)
  have hb := mul_le_mul_of_nonneg_left (finiteMaximum_le_weightMaximum a D v)
    (EReal.coe_nonneg.mpr hc)
  rw [hr,← EReal.coe_mul] at hb
  exact ne_of_lt (hb.trans_lt (EReal.coe_lt_top _))

/-- The actual proper-center frame choice never affects the GF function. -/
theorem rationalGFFunction_atlas_independent (a b : LineBundleAtlas L)
    (D : RationalGFData L n m) (v : BerkovichPoint f) :
    rationalGFFunction a D v=rationalGFFunction b D v := by
  unfold rationalGFFunction finiteMaximum
  congr 1
  apply iSup_congr
  intro i
  rw [sectionLogNorm_atlas_independent a b]

theorem finiteMaximum_trivial [IsIntegral X] (a : LineBundleAtlas L)
    (D : RationalGFData L n m) :
    finiteMaximum a D (BerkovichPoint.trivial f)=weightMaximum D := by
  apply iSup_congr
  intro i
  rw [sectionLogNorm_trivial a n (D.sections i) (D.sections_ne_zero i),zero_add]

/-- Generic finiteness is internally produced at the ACTUAL trivial point. -/
theorem rationalGFFunction_trivial_finite [IsIntegral X] (a : LineBundleAtlas L)
    (D : RationalGFData L n m) :
    ∃ r : ℝ,rationalGFFunction a D (BerkovichPoint.trivial f)=(r:EReal) := by
  obtain ⟨r,hr⟩ := weightMaximum_eq_coe D
  refine ⟨(1/(m:ℝ))*r,?_⟩
  rw [rationalGFFunction,finiteMaximum_trivial,hr,EReal.coe_mul]

/-- The source nontriviality of an individual GF function is a theorem. -/
theorem rationalGFFunction_not_identically_bot [IsIntegral X] (a : LineBundleAtlas L)
    (D : RationalGFData L n m) : rationalGFFunction (f:=f) a D≠fun _ => ⊥ := by
  obtain ⟨r,hr⟩ := rationalGFFunction_trivial_finite (f:=f) a D
  intro h
  have hv := congrFun h (BerkovichPoint.trivial f)
  rw [hr] at hv
  exact EReal.coe_ne_bot r hv

/-- The union is an actual finite family of native sections, not a supplied
max-closure field in a metric class. -/
def RationalGFData.union (D E : RationalGFData L n m) : RationalGFData L n m where
  I := D.I⊕E.I
  fintype := inferInstance
  nonempty := inferInstance
  sections := Sum.elim D.sections E.sections
  sections_ne_zero := by intro i; cases i with
    | inl i => exact D.sections_ne_zero i
    | inr j => exact E.sections_ne_zero j
  weight := Sum.elim D.weight E.weight
  power_pos := D.power_pos
  denominator_pos := D.denominator_pos

theorem finiteMaximum_union (a : LineBundleAtlas L) (D E : RationalGFData L n m)
    (v : BerkovichPoint f) :
    finiteMaximum a (D.union E) v=max (finiteMaximum a D v) (finiteMaximum a E v) := by
  unfold finiteMaximum RationalGFData.union
  exact iSup_sum (f:=fun i:D.I⊕E.I =>
    sectionLogNorm a n (Sum.elim D.sections E.sections i) v+
      (((Sum.elim D.weight E.weight i:ℚ):ℝ):EReal))

/-- Genuine pointwise max is represented by actual section union for the
same honest rational presentation. This does not assert the printed BJ
closure for arbitrary varying-NS-class decreasing approximating nets. -/
theorem rationalGFFunction_union (a : LineBundleAtlas L) (D E : RationalGFData L n m)
    (v : BerkovichPoint f) :
    rationalGFFunction a (D.union E) v=max (rationalGFFunction a D v) (rationalGFFunction a E v) := by
  unfold rationalGFFunction
  rw [finiteMaximum_union]
  have hc : 0≤1/(m:ℝ) := div_nonneg zero_le_one (Nat.cast_nonneg _)
  have hmono : Monotone (fun z:EReal => (((1/(m:ℝ)):ℝ):EReal)*z) :=
    fun _ _ h => mul_le_mul_of_nonneg_left h (EReal.coe_nonneg.mpr hc)
  exact hmono.map_max

end SGPT.NAPotential.Berkovich.BJSections
