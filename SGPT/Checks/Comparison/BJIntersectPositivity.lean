import SGPT.Checks.Comparison.BJIntersectNumbers
import SGPT.Foundations.Envelope.AlgGeom.SeshadriAmplenessCriterionNefAmpleMixedIntersections
import SGPT.Foundations.Envelope.AlgGeom.SeshadriAmplenessCriterionNefAmple
import SGPT.Foundations.Envelope.AlgGeom.NativeNumericalAmpleConeGeneration

/-!
# Positivity of intersection numbers (lane BJ-INTERSECT, R6)

* `mixedEulerDifference_ample_nonneg`: on a projective scheme of dimension `≤ d`, the
  intersection number of `d` ample invertible sheaves (possibly all different) with a coherent
  sheaf is nonnegative;
* `mixedEulerDifference_nef_nonneg`: the same for `d` nef invertible sheaves (Kleiman: nef plus
  ample is ample, and a polynomial expansion in the nef parts);
* `IsNefOn`: nonnegative degree on all closed integral curves inside a given closed set
  (relative nefness over the central fibre of a test configuration);
* `mixedEulerDifference_effective_nonneg`: **the geometric core of [BJ22, `lem:enmono`]** — on an
  integral projective scheme, an invertible sheaf with a nonzero section has nonnegative
  intersection with invertible sheaves that are nef on the zero locus of the section;
  `interFormQ_effective_nonneg` is its form for `ℚ`-line bundles;
* `mixedEulerDifference_eq_zero_of_trivial_on_zero`: the cut by a section kills every entry that
  is trivial on its zero scheme (vertical divisors are orthogonal to the fibre class).

Source: Lazarsfeld, *Positivity I*, Thm. 1.4.9 and Example 1.4.16; [BJ22, `prop:intpairing`
(vi), `lem:enmono`]. Blueprint: `claude-bj-intersect.tex`.
-/

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Scheme.Modules TopologicalSpace
open scoped TensorProduct

universe u

namespace SGPT.NAPotential.BJIntersect

open SGPT.Foundations.Envelope SGPT.Foundations.Envelope.SeshadriAmplenessCriterion
open SGPT.Foundations.Envelope.SeshadriAmplenessCriterionNefAmpleMixedIntersections

attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory

/-! ### Small helpers -/

theorem isProjective_closed_comp {Z Y W : Scheme.{u}}
    (i : Z ⟶ Y) [IsClosedImmersion i] (p : Y ⟶ W) [IsProjective p] :
    IsProjective (i ≫ p) := by
  constructor
  obtain ⟨E, hE, hEF, j, hj, hjp⟩ := IsProjective.exists_isClosedImmersion (f := p)
  let : IsClosedImmersion j := hj
  exact ⟨E, hE, hEF, i ≫ j, inferInstance,
    (Category.assoc i j E.projectiveBundleπ).trans (congrArg (fun q => i ≫ q) hjp)⟩

theorem isSeparated_of_closed {Z Y : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    [Y.IsSeparated] : Z.IsSeparated :=
  ⟨by
    have h : IsSeparated (i ≫ terminal.from Y) := inferInstance
    simpa only [terminal.comp_from] using h⟩

theorem isQuasicoherent_of_isInvertible {X : Scheme.{u}} {T : X.Modules} (hT : IsInvertible T) :
    T.IsQuasicoherent := hT.isQuasicoherent

theorem isFiniteType_of_isInvertible {X : Scheme.{u}} {T : X.Modules} (hT : IsInvertible T) :
    T.IsFiniteType := by
  let : T.IsFinitePresentation := hT.isFinitePresentation
  exact SheafOfModules.instIsFiniteTypeOfIsFinitePresentation (R := X.ringCatSheaf) T

instance unitObj_isQuasicoherent (X : Scheme.{u}) : (unitObj X).IsQuasicoherent :=
  isInvertible_unit.isQuasicoherent

instance unitObj_isFiniteType (X : Scheme.{u}) : (unitObj X).IsFiniteType :=
  isFiniteType_of_isInvertible isInvertible_unit

/-! ### Mixed ample positivity -/

section ample

variable {k : Type u} [Field k]

/-- Reduction of ample positivity to integral schemes with an invertible coefficient. -/
private theorem ample_nonneg_of_integral (d : ℕ)
    (H : ∀ {Z : Scheme.{u}} [IsIntegral Z] [CompactSpace Z] [Z.IsSeparated]
      (q : Z ⟶ Spec (.of k)) [IsProjective q] (_ : topologicalKrullDim Z ≤ d)
      (ls : List Z.Modules) (_ : ls.length = d)
      (_ : ∀ A ∈ ls, SchemeLineAmpleness.IsAmple q A) (T : Z.Modules) (_ : IsInvertible T),
        0 ≤ mixedEulerDifference q ls T)
    {X : Scheme.{u}} [CompactSpace X] [X.IsSeparated]
    (p : X ⟶ Spec (.of k)) [IsProjective p] (hdim : topologicalKrullDim X ≤ d)
    (ls : List X.Modules) (hlen : ls.length = d)
    (hls : ∀ A ∈ ls, SchemeLineAmpleness.IsAmple p A)
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    0 ≤ mixedEulerDifference p ls F := by
  have hinv : ∀ L ∈ ls, IsInvertible L := fun L hL => (hls L hL).1
  obtain ⟨n, hfil⟩ := exists_finite_coherent_primeFiltration p F
  induction hfil with
  | zero M hM => exact (mixedEulerDifference_eq_zero_of_isZero p ls hinv M hM).ge
  | iso e _ ih => exact le_of_le_of_eq ih (mixedEulerDifference_eq_of_iso p _ e)
  | extension S hS hQ₁ hQ₂ hQ₃ hF₁ hF₂ hF₃ eta T hT e _ ih =>
    let : S.X₁.IsQuasicoherent := hQ₁
    let : S.X₂.IsQuasicoherent := hQ₂
    let : S.X₃.IsQuasicoherent := hQ₃
    let : S.X₁.IsFiniteType := hF₁
    let : S.X₂.IsFiniteType := hF₂
    let : S.X₃.IsFiniteType := hF₃
    let I := Scheme.IdealSheafData.vanishingIdeal
      (⟨closure ({eta} : Set X), isClosed_closure⟩ : Closeds X)
    let Z := I.subscheme
    let i : Z ⟶ X := I.subschemeι
    let : IsIntegral Z := SchemePointClosureIntegral.isIntegral_pointClosure eta
    let : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace i
    let : Z.IsSeparated := isSeparated_of_closed i
    let : IsProjective (i ≫ p) := isProjective_closed_comp i p
    have hdimZ := IntegralSchemeDimension.topologicalKrullDim_le_of_isIntegralHom i d hdim
    have hZ := H (i ≫ p) hdimZ (ls.map (Scheme.Modules.pullback i).obj) (by simpa using hlen)
      (by
        intro A hA
        obtain ⟨B, hB, rfl⟩ := List.mem_map.mp hA
        exact isAmple_closedPullback i p B (hls B hB)) T hT
    let : T.IsQuasicoherent := hT.isQuasicoherent
    have hpush := mixedEulerDifference_pushforward p i ls hinv T
    have hquotient : 0 ≤ mixedEulerDifference p ls S.X₃ := by
      rw [mixedEulerDifference_eq_of_iso p _ e, hpush]
      exact hZ
    rw [mixedEulerDifference_add p _ hinv S hS]
    exact add_nonneg ih hquotient

/-- The cutting step for ample positivity. -/
private theorem integral_ample_cut (d : ℕ)
    (ih : ∀ {Y : Scheme.{u}} [CompactSpace Y] [Y.IsSeparated]
      (q : Y ⟶ Spec (.of k)) [IsProjective q] (_ : topologicalKrullDim Y ≤ d)
      (ls : List Y.Modules) (_ : ls.length = d)
      (_ : ∀ A ∈ ls, SchemeLineAmpleness.IsAmple q A)
      (G : Y.Modules) [G.IsQuasicoherent] [G.IsFiniteType], 0 ≤ mixedEulerDifference q ls G)
    {Z : Scheme.{u}} [IsIntegral Z] [CompactSpace Z] [Z.IsSeparated]
    (r : Z ⟶ Spec (.of k)) [IsProjective r] (hdimZ : topologicalKrullDim Z ≤ (d + 1 : ℕ))
    (ls : List Z.Modules) (hlen : ls.length = d + 1)
    (hls : ∀ A ∈ ls, SchemeLineAmpleness.IsAmple r A) (T : Z.Modules) (hT : IsInvertible T) :
    0 ≤ mixedEulerDifference r ls T := by
  obtain ⟨C, rest, rfl⟩ : ∃ C rest, ls = C :: rest := by
    cases ls with
    | nil => simp at hlen
    | cons C rest => exact ⟨C, rest, rfl⟩
  have hrest : rest.length = d := by simpa using hlen
  have hC : SchemeLineAmpleness.IsAmple r C := hls C (by simp)
  have hrestA : ∀ A ∈ rest, SchemeLineAmpleness.IsAmple r A := fun A hA => hls A (by simp [hA])
  have hrestI : ∀ A ∈ rest, IsInvertible A := fun A hA => (hrestA A hA).1
  let : T.IsQuasicoherent := hT.isQuasicoherent
  let : T.IsFiniteType := isFiniteType_of_isInvertible hT
  obtain ⟨s, hs, a, ha, _⟩ :=
    ProjectiveAmpleSectionContainingClosedSubset.exists_nonzero_power_section_containing_closed
      r ⊥ (closeds_bot_ne_top_of_isIntegral Z) C hC
  let P := CanonicalGeometry.bundleTensorPower C s
  let hP : IsInvertible P := TensorPowerBaseIdealGrading.tensorPower_isInvertible hC.1 s
  let D := LineSectionZeroIdeal.zeroIdeal P hP a
  let i := D.subschemeι
  let : CompactSpace D.subscheme := QuasiCompact.compactSpace_of_compactSpace i
  let : D.subscheme.IsSeparated := isSeparated_of_closed i
  let : IsProjective (i ≫ r) := isProjective_closed_comp i r
  have hTP : IsInvertible (T ⊗ P) :=
    (hT.tensorObj hP).of_iso (SGPT.Support.ModularCurves.monoidalTensorObjIso T P)
  let Ti := (Scheme.Modules.pullback i).obj (T ⊗ P)
  have hTi : IsInvertible Ti := hTP.pullback i
  let : Ti.IsQuasicoherent := hTi.isQuasicoherent
  let : Ti.IsFiniteType := isFiniteType_of_isInvertible hTi
  have hdimD : topologicalKrullDim D.subscheme ≤ d :=
    sectionZero_dimension_drop d hdimZ P hP a ha
  have hD := ih (i ≫ r) hdimD (rest.map (Scheme.Modules.pullback i).obj) (by simpa using hrest)
    (by
      intro A hA
      obtain ⟨B, hB, rfl⟩ := List.mem_map.mp hA
      exact isAmple_closedPullback i r B (hrestA B hB)) Ti
  have hcut := mixedEulerDifference_sectionDifference r P hP a ha rest hrestI T hT
  rw [mixedEulerDifference_tensorPower_cons r (d + 1) hdimZ C hC.1 rest (by omega) hrestI T s]
    at hcut
  have hmul : 0 ≤ (s : ℤ) * mixedEulerDifference r (C :: rest) T := by
    rw [hcut]
    exact hD
  have hsZ : (0 : ℤ) < s := by exact_mod_cast hs
  exact (mul_nonneg_iff_of_pos_left hsZ).mp hmul

/-- **Mixed ample positivity.** On a projective scheme of dimension at most `d`, `d` ample
invertible sheaves `A₁, …, A_d` and a coherent sheaf `F` satisfy `(A₁ ⋯ A_d · F) ≥ 0`. -/
theorem mixedEulerDifference_ample_nonneg (d : ℕ) {X : Scheme.{u}} [CompactSpace X]
    [X.IsSeparated] (p : X ⟶ Spec (.of k)) [IsProjective p]
    (hdim : topologicalKrullDim X ≤ d) (ls : List X.Modules) (hlen : ls.length = d)
    (hls : ∀ A ∈ ls, SchemeLineAmpleness.IsAmple p A)
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    0 ≤ mixedEulerDifference p ls F := by
  have all : ∀ d : ℕ, ∀ {Y : Scheme.{u}} [CompactSpace Y] [Y.IsSeparated]
      (q : Y ⟶ Spec (.of k)) [IsProjective q] (_ : topologicalKrullDim Y ≤ d)
      (ls : List Y.Modules) (_ : ls.length = d)
      (_ : ∀ A ∈ ls, SchemeLineAmpleness.IsAmple q A)
      (G : Y.Modules) [G.IsQuasicoherent] [G.IsFiniteType],
        0 ≤ mixedEulerDifference q ls G := by
    intro d
    induction d with
    | zero =>
      intro Y _ _ q _ hdimY ls hlenY _ G _ _
      obtain ⟨A, hA⟩ := NativeRealNumericalClasses.exists_geometric_ample_line q
      have h := mixedEulerDifference_replicate_nonneg_of_isAmple q 0 hdimY G A hA
      rw [List.length_eq_zero_iff.mp hlenY]
      simpa using h
    | succ d ih =>
      intro Y _ _ q _ hdimY ls hlenY hlsY G _ _
      exact ample_nonneg_of_integral (d + 1)
        (fun r _ hdimZ ls hlen hls T hT => integral_ample_cut d ih r hdimZ ls hlen hls T hT)
        q hdimY ls hlenY hlsY G
  exact all d p hdim ls hlen hls F

end ample

/-! ### Classes of tensor products and powers -/

section classes

variable {X : Scheme.{u}}

theorem pic_val_mul (a b : X.Pic) : (a * b).val = a.val * b.val := rfl

theorem pic_val_one : (1 : X.Pic).val = 1 := rfl

theorem lineCls_eq_of_iso {L M : X.Modules} (hL : IsInvertible L) (hM : IsInvertible M)
    (e : L ≅ M) : lineCls ⟨L, hL⟩ = lineCls ⟨M, hM⟩ := by
  apply congrArg Additive.ofMul
  apply Units.ext
  rw [CurvePicardDegrees.lineClass_val, CurvePicardDegrees.lineClass_val]
  exact congr_toSkeleton_of_iso e

theorem lineCls_tensor {L M : X.Modules} (hL : IsInvertible L) (hM : IsInvertible M)
    (hLM : IsInvertible (L ⊗ M)) :
    lineCls ⟨L ⊗ M, hLM⟩ = lineCls ⟨L, hL⟩ + lineCls ⟨M, hM⟩ := by
  apply congrArg Additive.ofMul
  apply Units.ext
  change (CurvePicardDegrees.lineClass (L ⊗ M) hLM).val =
    (CurvePicardDegrees.lineClass L hL * CurvePicardDegrees.lineClass M hM).val
  rw [pic_val_mul, CurvePicardDegrees.lineClass_val, CurvePicardDegrees.lineClass_val,
    CurvePicardDegrees.lineClass_val]
  exact Skeleton.toSkeleton_tensorObj L M

theorem lineCls_unit : lineCls ⟨unitObj X, isInvertible_unit⟩ = 0 := by
  apply congrArg Additive.ofMul
  apply Units.ext
  change (CurvePicardDegrees.lineClass (unitObj X) isInvertible_unit).val = (1 : X.Pic).val
  rw [CurvePicardDegrees.lineClass_val, pic_val_one, Skeleton.one_eq]
  exact congr_toSkeleton_of_iso (SGPT.Support.ModularCurves.monoidalUnitObjIso X).symm

theorem lineCls_tensorPower {N : X.Modules} (hN : IsInvertible N) (m : ℕ) :
    lineCls ⟨CanonicalGeometry.bundleTensorPower N m,
      TensorPowerBaseIdealGrading.tensorPower_isInvertible hN m⟩ = m • lineCls ⟨N, hN⟩ := by
  induction m with
  | zero => exact (lineCls_unit (X := X)).trans (zero_smul ℕ _).symm
  | succ m ih =>
    have hm := TensorPowerBaseIdealGrading.tensorPower_isInvertible hN m
    have hmN : IsInvertible (CanonicalGeometry.bundleTensorPower N m ⊗ N) :=
      (hm.tensorObj hN).of_iso (SGPT.Support.ModularCurves.monoidalTensorObjIso _ N)
    have he := lineCls_eq_of_iso (TensorPowerBaseIdealGrading.tensorPower_isInvertible hN (m + 1))
      hmN (SGPT.Support.ModularCurves.monoidalTensorObjIso (CanonicalGeometry.bundleTensorPower N m) N).symm
    rw [he, lineCls_tensor hm hN hmN, ih, succ_nsmul]

end classes

/-! ### Mixed nef positivity -/

section nef

variable {k : Type u} [Field k]

/-- **Mixed nef positivity.** On a projective scheme of dimension at most `d`, `d` nef
invertible sheaves `N₁, …, N_d` and a coherent sheaf `F` satisfy `(N₁ ⋯ N_d · F) ≥ 0`. -/
theorem mixedEulerDifference_nef_nonneg (d : ℕ) {X : Scheme.{u}} [CompactSpace X]
    [X.IsSeparated] (p : X ⟶ Spec (.of k)) [IsProjective p]
    (hdim : topologicalKrullDim X ≤ d) (ns : List {N : X.Modules // IsInvertible N})
    (hlen : ns.length = d)
    (hnef : ∀ N ∈ ns, NativeRealNumericalClasses.lineClass p N.1 N.2 ∈
      NativeRealNumericalClasses.nefCone p)
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    0 ≤ mixedEulerDifference p (ns.map Subtype.val) F := by
  classical
  obtain ⟨A, hA⟩ := NativeRealNumericalClasses.exists_geometric_ample_line p
  let Φ := interForm p d hdim F
  let a : Additive X.Pic := lineCls ⟨A, hA.1⟩
  let pairs : Multiset (Additive X.Pic × Additive X.Pic) :=
    ((ns.map fun N => (lineCls N, a) : List _) : Multiset _)
  obtain ⟨P, hdeg, hcoeff, heval⟩ := Φ.exists_polynomial pairs 0
  have hcard : Multiset.card pairs = d := by simp [pairs, hlen]
  -- the twisted sheaves `N^m ⊗ A` are ample
  let tw : ℕ → {N : X.Modules // IsInvertible N} → {N : X.Modules // IsInvertible N} :=
    fun m N => ⟨CanonicalGeometry.bundleTensorPower N.1 m ⊗ A,
      ((TensorPowerBaseIdealGrading.tensorPower_isInvertible N.2 m).tensorObj hA.1).of_iso
        (SGPT.Support.ModularCurves.monoidalTensorObjIso _ A)⟩
  have hev : ∀ m : ℕ, 0 ≤ P.eval (m : ℤ) := by
    intro m
    rw [heval, zero_add]
    have hlist : (pairs.map fun q => (m : ℤ) • q.1 + q.2) =
        (((ns.map (tw m)).map lineCls : List _) : Multiset _) := by
      simp only [pairs, Multiset.map_coe, List.map_map]
      congr 1
      refine List.map_congr_left fun N _ => ?_
      simp only [Function.comp_apply, tw]
      rw [lineCls_tensor (TensorPowerBaseIdealGrading.tensorPower_isInvertible N.2 m) hA.1,
        lineCls_tensorPower N.2 m, natCast_zsmul]
    rw [hlist]
    change 0 ≤ interNum p d F _
    rw [interNum_ofLines p d F _ (by simpa using hlen), List.map_map]
    refine mixedEulerDifference_ample_nonneg d p hdim _ (by simpa using hlen) ?_ F
    intro B hB
    obtain ⟨N, hN, rfl⟩ := List.mem_map.mp hB
    exact SeshadriAmplenessCriterionNefAmple.isAmple_tensor_nef p _ A _
      (SeshadriAmplenessCriterionNefAmple.lineClass_tensorPower_mem_nefCone p N.1 N.2
        (hnef N hN) m) hA
  -- a polynomial which is nonnegative on `ℕ` has nonnegative coefficient in degree `d`
  let Q : Polynomial ℚ := P.map (Int.castRingHom ℚ)
  have hQdeg : Q.natDegree ≤ d :=
    (Polynomial.natDegree_map_le).trans (hcard ▸ hdeg)
  have hQ := polynomial_coeff_nonneg_of_eventual_nat_nonneg Q d hQdeg
    ⟨0, fun m _ => by
      rw [Polynomial.eval_map, show ((m : ℕ) : ℚ) = Int.castRingHom ℚ (m : ℤ) by simp,
        Polynomial.eval₂_at_apply, eq_intCast]
      exact_mod_cast hev m⟩
  rw [Polynomial.coeff_map, ← hcard, hcoeff, eq_intCast] at hQ
  have h0 : (0 : ℤ) ≤ Φ (0 + pairs.map Prod.fst) := by exact_mod_cast hQ
  have hfst : 0 + pairs.map Prod.fst = ((ns.map lineCls : List _) : Multiset _) := by
    simp [pairs, Multiset.map_coe, List.map_map, Function.comp_def]
  rw [hfst] at h0
  change 0 ≤ interNum p d F _ at h0
  rwa [interNum_ofLines p d F _ hlen] at h0

end nef

/-! ### Relative nefness and positivity of effective divisors -/

section effective

variable {k : Type u} [Field k]

/-- `N` is **nef on** the set `W ⊆ X`: it has nonnegative degree on every closed integral curve of
`X` contained in `W`. For `W` the central fibre of a test configuration this is relative
nefness over `𝔸¹` ([BJ22, §3]). -/
def IsNefOn {X : Scheme.{u}} [CompactSpace X] (p : X ⟶ Spec (.of k)) (N : X.Modules)
    (W : Set X) : Prop :=
  ∀ C : NativeClosedCurveDegrees.ClosedIntegralCurve X, Set.range C.inclusion ⊆ W →
    letI : IsClosedImmersion C.inclusion := C.closed
    letI : CompactSpace C.carrier := QuasiCompact.compactSpace_of_compactSpace C.inclusion
    0 ≤ CurveLineDegrees.degree (C.inclusion ≫ p) ((Scheme.Modules.pullback C.inclusion).obj N)

theorem IsNefOn.mono {X : Scheme.{u}} [CompactSpace X] {p : X ⟶ Spec (.of k)} {N : X.Modules}
    {W W' : Set X} (h : IsNefOn p N W) (hW : W' ⊆ W) : IsNefOn p N W' :=
  fun C hC => h C (hC.trans hW)

/-- Nef on a closed set restricts along closed immersions. -/
theorem IsNefOn.pullback {X Y : Scheme.{u}} [CompactSpace X] [CompactSpace Y]
    {p : X ⟶ Spec (.of k)} {N : X.Modules} {W : Set X} (h : IsNefOn p N W)
    (i : Y ⟶ X) [IsClosedImmersion i] :
    IsNefOn (i ≫ p) ((Scheme.Modules.pullback i).obj N) (i ⁻¹' W) := by
  intro C hC
  let : IsClosedImmersion C.inclusion := C.closed
  let C' : NativeClosedCurveDegrees.ClosedIntegralCurve X :=
    ⟨C.carrier, C.integral, C.inclusion ≫ i, inferInstance, C.dimension⟩
  have hC' : Set.range C'.inclusion ⊆ W := by
    rintro _ ⟨x, rfl⟩
    exact hC ⟨x, rfl⟩
  have h' := h C' hC'
  let : CompactSpace C.carrier := QuasiCompact.compactSpace_of_compactSpace C.inclusion
  change 0 ≤ CurveLineDegrees.degree ((C.inclusion ≫ i) ≫ p)
    ((Scheme.Modules.pullback (C.inclusion ≫ i)).obj N) at h'
  rw [Category.assoc, CurveLineDegrees.degree_eq_of_iso _
    ((Scheme.Modules.pullbackComp C.inclusion i).app N).symm] at h'
  exact h'

/-- Nef everywhere is nef in the sense of the numerical nef cone. -/
theorem IsNefOn.mem_nefCone {X : Scheme.{u}} [CompactSpace X] {p : X ⟶ Spec (.of k)}
    [IsProjective p] {N : X.Modules} (hN : IsInvertible N) (h : IsNefOn p N Set.univ) :
    NativeRealNumericalClasses.lineClass p N hN ∈ NativeRealNumericalClasses.nefCone p := by
  apply (NativeRealNumericalClasses.lineClass_mem_nefCone_iff p N hN).mpr
  intro C
  exact_mod_cast h C (Set.subset_univ _)

/-- **Effective divisors against relatively nef classes** (the geometric core of
[BJ22, `lem:enmono`]). Let `X` be integral and projective of dimension `≤ d + 1`, `L` invertible
with a nonzero section `s` and `N₁, …, N_d` invertible and nef on the zero locus of `s`. Then
`(L · N₁ ⋯ N_d · T) ≥ 0` for every invertible `T`. -/
theorem mixedEulerDifference_effective_nonneg (d : ℕ) {X : Scheme.{u}} [IsIntegral X]
    [CompactSpace X] [X.IsSeparated] (p : X ⟶ Spec (.of k)) [IsProjective p]
    (hdim : topologicalKrullDim X ≤ (d + 1 : ℕ)) (L : X.Modules) (hL : IsInvertible L)
    (s : unitObj X ⟶ L) (hs : s ≠ 0) (ns : List {N : X.Modules // IsInvertible N})
    (hlen : ns.length = d)
    (hnef : ∀ N ∈ ns, IsNefOn p N.1 (LineSectionZeroIdeal.zeroIdeal L hL s).support)
    (T : X.Modules) (hT : IsInvertible T) :
    0 ≤ mixedEulerDifference p (L :: ns.map Subtype.val) T := by
  let D := LineSectionZeroIdeal.zeroIdeal L hL s
  let i := D.subschemeι
  let : CompactSpace D.subscheme := QuasiCompact.compactSpace_of_compactSpace i
  let : D.subscheme.IsSeparated := isSeparated_of_closed i
  let : IsProjective (i ≫ p) := isProjective_closed_comp i p
  have hinv : ∀ K ∈ ns.map Subtype.val, IsInvertible K := by
    intro K hK
    obtain ⟨N, -, rfl⟩ := List.mem_map.mp hK
    exact N.2
  have hcut := mixedEulerDifference_sectionDifference p L hL s hs (ns.map Subtype.val) hinv T hT
  rw [hcut]
  have hTL : IsInvertible (T ⊗ L) :=
    (hT.tensorObj hL).of_iso (SGPT.Support.ModularCurves.monoidalTensorObjIso T L)
  let Ti := (Scheme.Modules.pullback i).obj (T ⊗ L)
  have hTi : IsInvertible Ti := hTL.pullback i
  let : Ti.IsQuasicoherent := hTi.isQuasicoherent
  let : Ti.IsFiniteType := isFiniteType_of_isInvertible hTi
  have hdimD : topologicalKrullDim D.subscheme ≤ d := sectionZero_dimension_drop d hdim L hL s hs
  let ns' : List {N : D.subscheme.Modules // IsInvertible N} :=
    ns.map fun N => ⟨(Scheme.Modules.pullback i).obj N.1, N.2.pullback i⟩
  have h := mixedEulerDifference_nef_nonneg d (i ≫ p) hdimD ns' (by simpa [ns'] using hlen)
    (by
      intro N' hN'
      obtain ⟨N, hN, rfl⟩ := List.mem_map.mp hN'
      apply IsNefOn.mem_nefCone
      refine ((hnef N hN).pullback i).mono ?_
      intro x _
      change i x ∈ (D.support : Set X)
      rw [← Scheme.IdealSheafData.range_subschemeι]
      exact ⟨x, rfl⟩) Ti
  simpa [ns', List.map_map, Function.comp_def] using h

/-- **Vertical divisors are orthogonal to the fibre.** If `P` has a nonzero section on the
integral scheme `X` and `M` is trivial on its zero scheme, every intersection number with entries
`P` and `M` vanishes. -/
theorem mixedEulerDifference_eq_zero_of_trivial_on_zero {X : Scheme.{u}} [IsIntegral X]
    [CompactSpace X] [X.IsSeparated] (p : X ⟶ Spec (.of k)) [IsProjective p]
    (P : X.Modules) (hP : IsInvertible P) (s : unitObj X ⟶ P) (hs : s ≠ 0)
    (M : X.Modules)
    (htriv : Nonempty ((Scheme.Modules.pullback
      (LineSectionZeroIdeal.zeroIdeal P hP s).subschemeι).obj M ≅
        unitObj (LineSectionZeroIdeal.zeroIdeal P hP s).subscheme))
    (hM : IsInvertible M) (ls : List X.Modules) (hls : ∀ K ∈ ls, IsInvertible K)
    (T : X.Modules) (hT : IsInvertible T) :
    mixedEulerDifference p (P :: M :: ls) T = 0 := by
  let D := LineSectionZeroIdeal.zeroIdeal P hP s
  let i := D.subschemeι
  let : CompactSpace D.subscheme := QuasiCompact.compactSpace_of_compactSpace i
  have hinv : ∀ K ∈ M :: ls, IsInvertible K := by
    intro K hK
    rcases List.mem_cons.mp hK with rfl | hK
    · exact hM
    · exact hls K hK
  rw [mixedEulerDifference_sectionDifference p P hP s hs (M :: ls) hinv T hT, List.map_cons]
  obtain ⟨e⟩ := htriv
  rw [mixedEulerDifference_congr (i ≫ p) (ms := unitObj D.subscheme ::
      ls.map (Scheme.Modules.pullback i).obj)
    (List.Forall₂.cons ⟨e⟩ (List.forall₂_same.mpr fun _ _ => ⟨Iso.refl _⟩)),
    mixedEulerDifference_unit_cons]

end effective

/-! ### `ℚ`-line bundles -/

section rational

variable {k : Type u} [Field k]

/-- **Effective `ℚ`-divisors against relatively nef `ℚ`-classes.** With the hypotheses of
`mixedEulerDifference_effective_nonneg`, for rationals `c ≥ 0` and `cᵢ ≥ 0` the intersection form
on `ℚ`-line bundles satisfies `(c [L] · c₁ [N₁] ⋯ c_d [N_d]) ≥ 0`. -/
theorem interFormQ_effective_nonneg (d : ℕ) {X : Scheme.{u}} [IsIntegral X]
    [CompactSpace X] [X.IsSeparated] (p : X ⟶ Spec (.of k)) [IsProjective p]
    (hdim : topologicalKrullDim X ≤ (d + 1 : ℕ)) (L : X.Modules) (hL : IsInvertible L)
    (s : unitObj X ⟶ L) (hs : s ≠ 0) (ns : List ({N : X.Modules // IsInvertible N} × ℚ))
    (hlen : ns.length = d)
    (hnef : ∀ N ∈ ns, IsNefOn p N.1.1 (LineSectionZeroIdeal.zeroIdeal L hL s).support)
    (hc : ∀ N ∈ ns, 0 ≤ N.2) (c : ℚ) (hc0 : 0 ≤ c) :
    0 ≤ interFormQ p (d + 1) hdim (unitObj X)
      ((c • picQ ⟨L, hL⟩) ::ₘ ((ns.map fun N => N.2 • picQ N.1 : List _) : Multiset _)) := by
  set Φ := interFormQ p (d + 1) hdim (unitObj X) with hΦ
  -- pull the scalars out of every entry
  have hscal : ∀ (l : List ({N : X.Modules // IsInvertible N} × ℚ)) (t : Multiset (PicQ X)),
      Φ (t + ((l.map fun N => N.2 • picQ N.1 : List _) : Multiset _)) =
        (l.map Prod.snd).prod * Φ (t + ((l.map fun N => picQ N.1 : List _) : Multiset _)) := by
    intro l
    induction l with
    | nil => intro t; simp
    | cons N l ih =>
      intro t
      simp only [List.map_cons, List.prod_cons]
      rw [← Multiset.cons_coe, Multiset.add_cons, Φ.map_smul, ← Multiset.cons_add, ih,
        ← Multiset.cons_coe, Multiset.add_cons, ← Multiset.cons_add]
      ring
  have h := hscal ns {c • picQ ⟨L, hL⟩}
  rw [Multiset.singleton_add, Multiset.singleton_add] at h
  rw [h, Φ.map_smul]
  have hval : Φ (picQ ⟨L, hL⟩ ::ₘ ((ns.map fun N => picQ N.1 : List _) : Multiset _)) =
      mixedEulerDifference p (L :: (ns.map Prod.fst).map Subtype.val) (unitObj X) := by
    have := interFormQ_picQ p (d + 1) hdim (unitObj X) (⟨L, hL⟩ :: ns.map Prod.fst)
      (by simp [hlen])
    simpa [List.map_map, Function.comp_def] using this
  rw [hval]
  refine mul_nonneg (List.prod_nonneg fun x hx => ?_) (mul_nonneg hc0 ?_)
  · obtain ⟨N, hN, rfl⟩ := List.mem_map.mp hx
    exact hc N hN
  · have := mixedEulerDifference_effective_nonneg d p hdim L hL s hs (ns.map Prod.fst)
      (by simpa using hlen)
      (by
        intro N hN
        obtain ⟨M, hM, rfl⟩ := List.mem_map.mp hN
        exact hnef M hM) (unitObj X) isInvertible_unit
    exact_mod_cast this

end rational

end SGPT.NAPotential.BJIntersect
