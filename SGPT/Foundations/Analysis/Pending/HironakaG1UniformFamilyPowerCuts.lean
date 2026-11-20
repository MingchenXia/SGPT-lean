import SGPT.Foundations.Analysis.Pending.HironakaG1OriginalUnequalMarkCanonical

/-! COMPLETE original cuts across TWO actual chronological family heads.
Blueprint FIRST: hironaka-g1-uniform-family-power-cuts.tex.
Only INITIAL E is empty; all later old/born/empty slots remain actual. -/
set_option autoImplicit false
namespace SGPT.Foundations.Analysis.Pending.HironakaG1UniformFamilyPowerCuts
noncomputable section
open FirstPass FirstPass.HolomorphicIdealSheaves BlowupTowers BlowupTowerTransforms
  MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionInvariantSpec CanonicalCentres
  HironakaG1OriginalUnequalMarkCanonical HironakaActualPowerBoundaryExponents
  HironakaG8LocalHistory HironakaG8LocalPower HironakaG11InvBMClass DivisorExponentAlong

private theorem uniform_strict_cut {n : ℕ} {ι : Type*} {X : ι → CMfd.{0} n}
    (P : ∀i,MarkedIdeal n (X i)) (hP : ∀i,IsInvDomain n (P i)) (hE : ∀i,(P i).E=[])
    (hd : ∀i j,(P i).d=(P j).d) (e : ℕ) (he : 1≤e)
    (i j : ι) {Y Z : CMfd.{0} n} (T : BlowupTower (X i) Y) (S : BlowupTower (X j) Z)
    (hT : IsCanonical (P i) ((canonicalInvariant n).inv (P i)) T)
    (hS : IsCanonical (P j) ((canonicalInvariant n).inv (P j)) S)
    (x : Y) (hx : x∈(geoTransformAlong (P i) T).cosupp)
    (y : Z) (hy : y∈(geoTransformAlong (P j) S).cosupp) :
    ((canonicalInvariant n).inv (P i) T x < (canonicalInvariant n).inv (P j) S y ↔
      (canonicalInvariant n).inv (powerMarked (P i) e) T x <
        (canonicalInvariant n).inv (powerMarked (P j) e) S y) := by
  have hPi:=powerMarked_isInvDomain (P i) (hP i) he
  have hPj:=powerMarked_isInvDomain (P j) (hP j) he
  have hLi:=locEquiv_powerMarked (κ := Kinds.wp) rfl (P i) (hP i) he
  have hLj:=locEquiv_powerMarked (κ := Kinds.wp) rfl (P j) (hP j) he
  have hExpI : ∀H∈(P i).E,∀x∈(P i).cosupp,x∈H →
      (powerMarked (P i) e).d*divExpAlong n (P i).N (P i).ideal H x=
        (P i).d*divExpAlong n (powerMarked (P i) e).N (powerMarked (P i) e).ideal H x:=by
    intro H hH
    rw [hE i] at hH
    exact (List.not_mem_nil hH).elim
  have hExpJ : ∀H∈(P j).E,∀x∈(P j).cosupp,x∈H →
      (powerMarked (P j) e).d*divExpAlong n (P j).N (P j).ideal H x=
        (P j).d*divExpAlong n (powerMarked (P j) e).N (powerMarked (P j) e).ideal H x:=by
    intro H hH
    rw [hE j] at hH
    exact (List.not_mem_nil hH).elim
  have hTpow:=(canonicalInvariant_isCanonical_power_iff (P i) (hP i) e he T).mp hT
  have hSpow:=(canonicalInvariant_isCanonical_power_iff (P j) (hP j) e he S).mp hS
  exact canonicalTwoPairCuts_canonicalInvariant n
    (P i) (powerMarked (P i) e) (P j) (powerMarked (P j) e)
    (hP i) hPi (hP j) hPj hLi (SameCarrierDim.of_N_eq rfl) hExpI
    hLj (SameCarrierDim.of_N_eq rfl) hExpJ (hd i j)
    (congrArg (fun a=>a*e) (hd i j)) trivial trivial trivial trivial
    T S hT hTpow hS hSpow x hx y hy

/-- FULL </≤/= comparisons, for ANY TWO genuine original canonical
prefixes and their actual points. No unequal-mark raw-value equality. -/
theorem uniform_power_comparisons {n : ℕ} {ι : Type*} {X : ι → CMfd.{0} n}
    (P : ∀i,MarkedIdeal n (X i)) (hP : ∀i,IsInvDomain n (P i)) (hE : ∀i,(P i).E=[])
    (hd : ∀i j,(P i).d=(P j).d) (e : ℕ) (he : 1≤e)
    (i j : ι) {Y Z : CMfd.{0} n} (T : BlowupTower (X i) Y) (S : BlowupTower (X j) Z)
    (hT : IsCanonical (P i) ((canonicalInvariant n).inv (P i)) T)
    (hS : IsCanonical (P j) ((canonicalInvariant n).inv (P j)) S)
    (x : Y) (hx : x∈(geoTransformAlong (P i) T).cosupp)
    (y : Z) (hy : y∈(geoTransformAlong (P j) S).cosupp) :
    ((canonicalInvariant n).inv (P i) T x < (canonicalInvariant n).inv (P j) S y ↔
      (canonicalInvariant n).inv (powerMarked (P i) e) T x <
        (canonicalInvariant n).inv (powerMarked (P j) e) S y) ∧
    ((canonicalInvariant n).inv (P i) T x ≤ (canonicalInvariant n).inv (P j) S y ↔
      (canonicalInvariant n).inv (powerMarked (P i) e) T x ≤
        (canonicalInvariant n).inv (powerMarked (P j) e) S y) ∧
    ((canonicalInvariant n).inv (P i) T x = (canonicalInvariant n).inv (P j) S y ↔
      (canonicalInvariant n).inv (powerMarked (P i) e) T x =
        (canonicalInvariant n).inv (powerMarked (P j) e) S y) := by
  have hLt:=uniform_strict_cut P hP hE hd e he i j T S hT hS x hx y hy
  have hRev:=uniform_strict_cut P hP hE hd e he j i S T hS hT y hy x hx
  have hLe : (canonicalInvariant n).inv (P i) T x ≤ (canonicalInvariant n).inv (P j) S y ↔
      (canonicalInvariant n).inv (powerMarked (P i) e) T x ≤
        (canonicalInvariant n).inv (powerMarked (P j) e) S y:=by
    constructor
    · intro h;exact le_of_not_gt (fun hh=>not_lt_of_ge h (hRev.mpr hh))
    · intro h;exact le_of_not_gt (fun hh=>not_lt_of_ge h (hRev.mp hh))
  have hGe : (canonicalInvariant n).inv (P j) S y ≤ (canonicalInvariant n).inv (P i) T x ↔
      (canonicalInvariant n).inv (powerMarked (P j) e) S y ≤
        (canonicalInvariant n).inv (powerMarked (P i) e) T x:=by
    constructor
    · intro h;exact le_of_not_gt (fun hh=>not_lt_of_ge h (hLt.mpr hh))
    · intro h;exact le_of_not_gt (fun hh=>not_lt_of_ge h (hLt.mp hh))
  refine ⟨hLt,hLe,?_⟩
  constructor
  · intro h;exact le_antisymm (hLe.mp h.le) (hGe.mp h.ge)
  · intro h;exact le_antisymm (hLe.mpr h.le) (hGe.mpr h.ge)

end
end SGPT.Foundations.Analysis.Pending.HironakaG1UniformFamilyPowerCuts
