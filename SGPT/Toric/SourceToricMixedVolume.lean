import SGPT.Toric.InvariantCurrentPotential
import SGPT.Toric.BookInvariantCurrentPotential
import SGPT.Toric.ToricFiniteCurrentBodies
import SGPT.Toric.ToricMixedVolumeZero
import SGPT.PSH.SourceCurrentFinitePolarization

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric

open Set Filter MeasureTheory SGPT.PSH SGPT.PSH.VariableComplexAtlas SGPT.Convex
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open CanonicalCurrentFrame NaturalThetaPshGeometricCurrent CurrentBottChernClass
open GlobalPositiveCurrentACRestriction
open scoped Topology ContDiff BigOperators Pointwise ENNReal

variable {m : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin (m + 1) → ℤ} {hs : latticePolytopeEdgeSmooth γ}
local notation "X" => PolytopeToricVariety γ hs
local notation "b" => canonicalBasis (m + 1)
local notation "Pos" => (sourcePositiveCurrentCone (m := m) (M := X))

namespace BigToricMetric

variable {D : ToricDivisor γ hs} (h : BigToricMetric D)

/-- The actual invariant potential manufactured from the original current,
its prescribed class and literal geometric invariance. -/
def sourceInvariantCurrentPotential
    (T : ClosedOneOneCurrent (M := X) b (Nat.succ_pos m))
    (hT : IsFullPositive T.val)
    (hclass : bottChernClass b (Nat.succ_pos m) T = RealBottChern.ofRepresentative h.form)
    (hinv : IsCompactTorusInvariantCurrent T hT) : X → EReal :=
  Classical.choose (h.exists_mem_PSHTor_of_invariant_current_class T hT hclass hinv)

theorem sourceInvariantCurrentPotential_spec
    (T : ClosedOneOneCurrent (M := X) b (Nat.succ_pos m))
    (hT : IsFullPositive T.val)
    (hclass : bottChernClass b (Nat.succ_pos m) T = RealBottChern.ofRepresentative h.form)
    (hinv : IsCompactTorusInvariantCurrent T hT) :
    ∃ hu : IsThetaPshPotential h.form.val (h.sourceInvariantCurrentPotential T hT hclass hinv),
      T.val = thetaPotentialCurrent h.form.val
        (h.sourceInvariantCurrentPotential T hT hclass hinv) hu ∧
      h.sourceInvariantCurrentPotential T hT hclass hinv ∈ h.PSHTor :=
  Classical.choose_spec (h.exists_mem_PSHTor_of_invariant_current_class T hT hclass hinv)

/-- The source closed-subgradient Newton body of the ORIGINAL current, using
its internally produced actual toric potential, never an abstract body token. -/
def sourceInvariantCurrentNewtonBody
    (T : ClosedOneOneCurrent (M := X) b (Nat.succ_pos m))
    (hT : IsFullPositive T.val)
    (hclass : bottChernClass b (Nat.succ_pos m) T = RealBottChern.ofRepresentative h.form)
    (hinv : IsCompactTorusInvariantCurrent T hT) : Set (EuclideanSpace ℝ (Fin (m + 1))) :=
  h.newtonBody (h.sourceInvariantCurrentPotential T hT hclass hinv)

/-- The manufactured body's value is the source body of EVERY genuine
presentation of this SAME invariant current in this prescribed background.
The other potential's torus invariance is internally derived as well. -/
theorem sourceInvariantCurrentNewtonBody_eq_of_presentation
    (omega : KahlerBackground (m + 1) X)
    (T : ClosedOneOneCurrent (M := X) b (Nat.succ_pos m))
    (hT : IsFullPositive T.val)
    (hclass : bottChernClass b (Nat.succ_pos m) T = RealBottChern.ofRepresentative h.form)
    (hinv : IsCompactTorusInvariantCurrent T hT)
    (u : X → EReal) (hu : IsThetaPshPotential h.form.val u)
    (hread : T.val = thetaPotentialCurrent h.form.val u hu) :
    h.sourceInvariantCurrentNewtonBody T hT hclass hinv = h.newtonBody u := by
  obtain ⟨hv, hreadv, hmemv⟩ :=
    h.sourceInvariantCurrentPotential_spec T hT hclass hinv
  obtain ⟨c, hc⟩ := CurrentPotential.exists_const_difference_of_current_eq hu hv
    (hread.symm.trans hreadv)
  have hmem : u ∈ h.PSHTor := by
    refine ⟨(isThetaPSH_iff_nativeThetaPotential h.atlasForm u).mpr hu, ?_⟩
    intro a ha x
    rw [hc (polytopeToricAction γ hs a x), hc x, hmemv.2 a ha x]
  have hI := SGPT.Okounkov.iEquivalent_of_thetaPotentialCurrent_eq omega hv hu
    (hreadv.symm.trans hread)
  have hsource := (sourceIEquivalent_iff_native
    ⟨h.atlasForm, hmemv.1⟩ ⟨h.atlasForm, hmem.1⟩).mpr hI
  exact (h.sourceIEquivalent_iff_newtonBody_eq hmemv hmem).mp hsource

end BigToricMetric

/-- Source thm:mix_vol_newbod, positive dimension: ACTUAL original invariant
closed positive currents in their prescribed toric divisor classes have
mixed I-volume equal to n! times independent geometric Minkowski mixed volume.

All invariant global presentations, finite subset currents, sum metrics,
body identities and source scalar volume identities are produced internally.
There is no incoming invariant-presentation, mixed-mass or body-equality
certificate. Divisor bigness is unnecessary for the stronger proved claim.
The source dimension-zero empty tuple is covered separately by
source_toric_mixed_volume_dim_zero, imported above. -/
theorem sourceCurrentMixedIVolume_eq_factorial_toricMixedVolume
    (omega : KahlerBackground (m + 1) X)
    (D : Fin (m + 1) → ToricDivisor γ hs) (h : ∀ i, BigToricMetric (D i))
    (T : Fin (m + 1) → ClosedOneOneCurrent (M := X) b (Nat.succ_pos m))
    (hT : ∀ i, IsFullPositive (T i).val)
    (hclass : ∀ i, bottChernClass b (Nat.succ_pos m) (T i) =
      RealBottChern.ofRepresentative (h i).form)
    (hinv : ∀ i, IsCompactTorusInvariantCurrent (T i) (hT i)) :
    (sourceCurrentMixedIVolume omega (fun i => (T i).val)
      (fun i => (T i).property.1) (fun i => (T i).property.2) hT).toReal =
        ((m + 1).factorial : ℝ) * sourceGeometricMixedVolume
          (fun i => (h i).sourceInvariantCurrentNewtonBody (T i) (hT i) (hclass i) (hinv i)) := by
  classical
  let u : Fin (m + 1) → X → EReal := fun i =>
    (h i).sourceInvariantCurrentPotential (T i) (hT i) (hclass i) (hinv i)
  choose hu hread hmem using fun i =>
    (h i).sourceInvariantCurrentPotential_spec (T i) (hT i) (hclass i) (hinv i)
  let A : Fin (m + 1) → Pos := fun i =>
    ⟨(T i).val, (T i).property.1, (T i).property.2, hT i⟩
  change sourcePositiveCurrentMixedReal omega A =
    ((m + 1).factorial : ℝ) * sourceGeometricMixedVolume
      (fun i => (h i).newtonBody (u i))
  have hdiag (S : Finset (Fin (m + 1))) :
      sourcePositiveCurrentMixedReal omega (fun _ => ∑ i ∈ S, A i) =
        ((m + 1).factorial : ℝ) *
          (volume (sourceMinkowskiSubsetSum (fun i => (h i).newtonBody (u i)) S)).toReal := by
    obtain ⟨H, hU, hcur, htor, hvol⟩ :=
      exists_finite_sum_toric_current_and_body D h u hmem S
    have hsumread : (∑ i ∈ S, A i).val =
        thetaPotentialCurrent H.form.val (fun p => ∑ i ∈ S, u i p) hU := by
      rw [AddSubmonoidClass.coe_finsetSum]
      change (∑ i ∈ S, (T i).val) = _
      rw [hcur]
      exact Finset.sum_congr rfl (fun i _ => hread i)
    have hd := sourceCurrentMixedIVolume_diagonal_eq_IVolume_of_representation omega
      (∑ i ∈ S, A i).val (∑ i ∈ S, A i).property.1
      (∑ i ∈ S, A i).property.2.1 (∑ i ∈ S, A i).property.2.2
      H.form (fun p => ∑ i ∈ S, u i p) hU hsumread
    have hdreal := congrArg ENNReal.toReal hd
    change (sourceCurrentMixedIVolume omega (fun _ => (∑ i ∈ S, A i).val)
      (fun _ => (∑ i ∈ S, A i).property.1)
      (fun _ => (∑ i ∈ S, A i).property.2.1)
      (fun _ => (∑ i ∈ S, A i).property.2.2)).toReal =
        (sourceIVolume H.atlasForm (fun p => ∑ i ∈ S, u i p) htor.1).toReal at hdreal
    rw [hvol, ENNReal.toReal_mul] at hdreal
    simpa only [sourcePositiveCurrentMixedReal, ENNReal.toReal_natCast] using hdreal
  have hp := factorial_mul_sourcePositiveCurrentMixedReal_eq_diagonal_polarization omega A
  simp_rw [hdiag] at hp
  have hfac : ((m + 1).factorial : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (m + 1)
  apply mul_left_cancel₀ hfac
  rw [factorial_mul_sourceGeometricMixedVolume]
  rw [hp, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S _
  ring

/-- EXACT original source-current subtype version of thm:mix_vol_newbod.
The source positivity and class-membership predicates are consumed directly.
The native full-positive domains are manufactured internally. -/
theorem sourceBookCurrentMixedIVolume_eq_factorial_toricMixedVolume
    (omega : KahlerBackground (m + 1) X)
    (D : Fin (m + 1) → ToricDivisor γ hs) (h : ∀ i, BigToricMetric (D i))
    (T : ∀ i : Fin (m + 1), SGPT.PSH.BookCurrent.ClosedPositiveCurrentIn m X
      (RealBottChern.ofRepresentative (h i).form))
    (hinv : ∀ i, IsCompactTorusInvariantBookCurrent (T i).val) :
    (sourceCurrentMixedIVolume omega (fun i => (T i).val.current)
      (fun i => (T i).val.isClosed) (fun i => (T i).val.isTypeOneOne)
      (fun i => bookCurrent_full_positive (T i).val)).toReal =
        ((m + 1).factorial : ℝ) * sourceGeometricMixedVolume
          (fun i => (h i).sourceInvariantCurrentNewtonBody (T i).val.val
            (bookCurrent_full_positive (T i).val) (T i).property (hinv i)) := by
  exact sourceCurrentMixedIVolume_eq_factorial_toricMixedVolume omega D h
    (fun i => (T i).val.val) (fun i => bookCurrent_full_positive (T i).val)
    (fun i => (T i).property) hinv

end SGPT.Toric
