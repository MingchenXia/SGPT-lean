import SGPT.Checks.Comparison.BJIntersectCut
import SGPT.Foundations.Envelope.AlgGeom.SchemeGlobalPullbackCartierRatio
import SGPT.Foundations.Envelope.AlgGeom.SchemeLineZeroSupportPullback
import SGPT.Foundations.Envelope.AlgGeom.SchemeAmpleLineGlobalGeneration
import SGPT.Foundations.Envelope.AlgGeom.CurveLineZeroSections
import SGPT.Foundations.Envelope.AlgGeom.AmpleLineTwistGeneration
import SGPT.Foundations.Envelope.AlgGeom.GeneratedLineBaseIdealUnit
import SGPT.Foundations.Envelope.AlgGeom.InvertibleBaseIdealFrameCoefficients

/-!
# Pull-backs from lower-dimensional targets have vanishing intersection numbers (lane BJ-INTERSECT, R3)

Let `π : Y ⟶ X'` be a morphism of projective `k`-schemes, `X'` integral, and suppose that `π`
maps `Y` into a closed subset `C ⊆ X'` of dimension `< r`. Then for all invertible sheaves
`L₁, …, L_r` on `X'` and every coherent sheaf `G` on `Y` (of any dimension),

  `Δ_{π^*L₁} ⋯ Δ_{π^*L_r} χ(Y, G) = 0`   (`mixedEulerDifference_pullback_eq_zero`).

In particular, on a projective scheme `Y` of dimension `≤ n + 1` with a morphism to a projective
integral `X'` of dimension `≤ n`, the intersection form vanishes on pulled-back `ℚ`-line bundles
(`interFormQ_pullback_eq_zero`). For a test configuration `𝒳̄ → X × ℙ¹ → X` this is
[BJ22, `prop:intpairing` (iii)]: `(θ₀, 0) ⋯ (θ_n, 0) = 0`; it is also the vanishing of the
contribution of contracted components in the projection formula.

Proof: write the first entry as a difference of ample sheaves, reduce by a prime filtration to an
integral `V ⊆ Y`, cut `V` by the pull-back of a section of a power of the ample first entry that
does not vanish at the image of the generic point of `V`, and induct on the dimension of the
target set; lists longer than `dim Y` vanish by SGPT.Foundations.Envelope, which starts a downward
induction on the length.

Blueprint: `claude-bj-intersect.tex` (`claude-bj-intersect:pullback-vanishing`).
-/

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Scheme.Modules TopologicalSpace Topology
open scoped TensorProduct

universe u

namespace SGPT.NAPotential.BJIntersect

open SGPT.Foundations.Envelope SGPT.Foundations.Envelope.SeshadriAmplenessCriterion

attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory

/-! ### Helpers -/

section helpers

variable {k : Type u} [Field k]

/-- `Δ_{L ⊗ M} = Δ_L + Δ_M + Δ_L Δ_M`, in any degree. -/
theorem mixedEulerDifference_tensor_identity {X : Scheme.{u}} [CompactSpace X]
    (f : X ⟶ Spec (.of k)) (L M : X.Modules) (ls : List X.Modules) (F : X.Modules) :
    mixedEulerDifference f ((L ⊗ M) :: ls) F =
      mixedEulerDifference f (L :: ls) F + mixedEulerDifference f (M :: ls) F +
        mixedEulerDifference f (L :: M :: ls) F := by
  have h := mixedEulerDifference_eq_of_iso f ls (α_ F L M).symm
  change mixedEulerDifference f ls (F ⊗ (L ⊗ M)) - mixedEulerDifference f ls F =
    (mixedEulerDifference f ls (F ⊗ L) - mixedEulerDifference f ls F) +
      (mixedEulerDifference f ls (F ⊗ M) - mixedEulerDifference f ls F) +
      ((mixedEulerDifference f ls ((F ⊗ L) ⊗ M) - mixedEulerDifference f ls (F ⊗ L)) -
        (mixedEulerDifference f ls (F ⊗ M) - mixedEulerDifference f ls F))
  rw [h]
  ring

/-- Pulling back twice is pulling back along the composite. -/
theorem mixedEulerDifference_map_pullback_comp {V Y X : Scheme.{u}} [CompactSpace V]
    (f : V ⟶ Spec (.of k)) (i : V ⟶ Y) (π : Y ⟶ X) (ls : List X.Modules) (F : V.Modules) :
    mixedEulerDifference f ((ls.map (Scheme.Modules.pullback π).obj).map
        (Scheme.Modules.pullback i).obj) F =
      mixedEulerDifference f (ls.map (Scheme.Modules.pullback (i ≫ π)).obj) F := by
  apply mixedEulerDifference_congr
  rw [List.map_map, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  exact List.forall₂_same.mpr fun L _ => ⟨(Scheme.Modules.pullbackComp i π).app L⟩

/-- Global generation gives a section not vanishing at a given point. -/
theorem exists_section_not_mem_support {X : Scheme.{u}} (M : X.Modules) (hM : IsInvertible M)
    (G : M.GeneratingSections) (x : X) :
    ∃ s : Γ(M, ⊤), x ∉ (LineSectionZeroIdeal.zeroIdeal M hM
      (SchemeModuleGlobalSections.sectionHom M s)).support := by
  by_contra h
  push Not at h
  have hxB : x ∈ (InvertibleSheafBaseIdeal.baseIdeal hM).support := by
    rw [InvertibleSheafBaseIdeal.baseIdeal, Scheme.IdealSheafData.support_iSup]
    apply Closeds.mem_iInf.mpr
    intro s
    rw [InvertibleBaseIdealFrameCoefficients.sectionIdeal_eq_zeroIdeal]
    exact h s
  rw [GeneratedLineBaseIdealUnit.baseIdeal_eq_top_of_generatingSections hM G,
    Scheme.IdealSheafData.support_top] at hxB
  exact hxB

/-- Reduction to integral closed subschemes with an invertible coefficient. -/
theorem mixedEulerDifference_eq_zero_of_integral {Y : Scheme.{u}} [CompactSpace Y]
    [Y.IsSeparated] (p : Y ⟶ Spec (.of k)) [IsProjective p] (ls : List Y.Modules)
    (hls : ∀ L ∈ ls, IsInvertible L)
    (H : ∀ (eta : Y) (T : (Scheme.IdealSheafData.vanishingIdeal
        (⟨closure ({eta} : Set Y), isClosed_closure⟩ : Closeds Y)).subscheme.Modules),
      IsInvertible T →
      letI : CompactSpace (Scheme.IdealSheafData.vanishingIdeal
          (⟨closure ({eta} : Set Y), isClosed_closure⟩ : Closeds Y)).subscheme :=
        QuasiCompact.compactSpace_of_compactSpace (Scheme.IdealSheafData.vanishingIdeal
          (⟨closure ({eta} : Set Y), isClosed_closure⟩ : Closeds Y)).subschemeι
      mixedEulerDifference ((Scheme.IdealSheafData.vanishingIdeal
          (⟨closure ({eta} : Set Y), isClosed_closure⟩ : Closeds Y)).subschemeι ≫ p)
        (ls.map (Scheme.Modules.pullback (Scheme.IdealSheafData.vanishingIdeal
          (⟨closure ({eta} : Set Y), isClosed_closure⟩ : Closeds Y)).subschemeι).obj) T = 0)
    (G : Y.Modules) [G.IsQuasicoherent] [G.IsFiniteType] :
    mixedEulerDifference p ls G = 0 := by
  obtain ⟨n, hfil⟩ := exists_finite_coherent_primeFiltration p G
  induction hfil with
  | zero M hM => exact mixedEulerDifference_eq_zero_of_isZero p ls hls M hM
  | iso e _ ih => exact (mixedEulerDifference_eq_of_iso p _ e).symm.trans ih
  | extension S hS hQ₁ hQ₂ hQ₃ hF₁ hF₂ hF₃ eta T hT e _ ih =>
    let : S.X₁.IsQuasicoherent := hQ₁
    let : S.X₂.IsQuasicoherent := hQ₂
    let : S.X₃.IsQuasicoherent := hQ₃
    let : S.X₁.IsFiniteType := hF₁
    let : S.X₂.IsFiniteType := hF₂
    let : S.X₃.IsFiniteType := hF₃
    let I := Scheme.IdealSheafData.vanishingIdeal
      (⟨closure ({eta} : Set Y), isClosed_closure⟩ : Closeds Y)
    let i := I.subschemeι
    let : CompactSpace I.subscheme := QuasiCompact.compactSpace_of_compactSpace i
    let : I.subscheme.IsSeparated := isSeparated_of_closed i
    let : T.IsQuasicoherent := hT.isQuasicoherent
    have h₃ : mixedEulerDifference p ls S.X₃ = 0 := by
      rw [mixedEulerDifference_eq_of_iso p _ e, mixedEulerDifference_pushforward p i ls hls T]
      exact H eta T hT
    rw [mixedEulerDifference_add p _ hls S hS, ih, h₃, add_zero]

theorem isInducing_inclusion {X : Type*} [TopologicalSpace X] {s t : Set X} (h : s ⊆ t) :
    IsInducing (Set.inclusion h) :=
  IsInducing.of_comp (continuous_inclusion h) continuous_subtype_val IsInducing.subtypeVal

/-- A proper closed subset of the closure of a point has smaller dimension. -/
theorem exists_dim_drop {X : Type*} [TopologicalSpace X] (x : X) (Z : Set X) (hZ : IsClosed Z)
    (hxZ : x ∉ Z) (hne : (closure ({x} : Set X) ∩ Z).Nonempty) (e : ℕ)
    (hdim : topologicalKrullDim (closure ({x} : Set X)) ≤ e) :
    ∃ d : ℕ, e = d + 1 ∧ topologicalKrullDim (closure ({x} : Set X) ∩ Z : Set X) ≤ d := by
  let S : Set X := closure ({x} : Set X)
  have hS : IsIrreducible S := isIrreducible_singleton.closure
  let : IrreducibleSpace S := Subtype.irreducibleSpace hS
  let x' : S := ⟨x, subset_closure rfl⟩
  let Z' : Closeds S := ⟨Subtype.val ⁻¹' Z, hZ.preimage continuous_subtype_val⟩
  have hZ' : Z' ≠ ⊤ := by
    intro h
    have : x' ∈ (Z' : Set S) := by rw [h]; trivial
    exact hxZ this
  obtain ⟨y, hyS, hyZ⟩ := hne
  let y' : S := ⟨y, hyS⟩
  -- `1 ≤ dim S`: the chain `closure {y} < S`
  have hone : (1 : WithBot ℕ∞) ≤ topologicalKrullDim S := by
    apply Order.one_le_krullDim_iff.mpr
    refine ⟨⟨closure ({y'} : Set S), isIrreducible_singleton.closure, isClosed_closure⟩,
      ⟨Set.univ, IrreducibleSpace.isIrreducible_univ S, isClosed_univ⟩, ?_⟩
    refine lt_of_le_of_ne (fun _ _ => trivial) ?_
    intro h
    have hx' : x' ∈ closure ({y'} : Set S) := by
      have := congrArg (fun T : IrreducibleCloseds S => (T : Set S)) h
      change closure ({y'} : Set S) = Set.univ at this
      rw [this]
      trivial
    have hsub : closure ({y'} : Set S) ⊆ (Z' : Set S) :=
      closure_minimal (Set.singleton_subset_iff.mpr hyZ) Z'.isClosed
    exact hxZ (hsub hx')
  obtain ⟨d, rfl⟩ : ∃ d, e = d + 1 := by
    rcases e with _ | d
    · exfalso
      have h10 := hone.trans hdim
      have h01 : (0 : WithBot ℕ∞) < 1 := by exact_mod_cast (zero_lt_one : (0 : ℕ∞) < 1)
      exact absurd h10 (not_le.mpr (by simp))
    · exact ⟨d, rfl⟩
  refine ⟨d, rfl, ?_⟩
  have hdrop := properClosed_dimension_drop Z' hZ' d hdim
  refine le_trans ?_ hdrop
  let f : (S ∩ Z : Set X) → Z' := fun z => ⟨⟨z.1, z.2.1⟩, z.2.2⟩
  have hf : IsInducing f := by
    refine IsInducing.of_comp (g := fun w : Z' => (w.1 : X)) ?_ ?_ IsInducing.subtypeVal
    · fun_prop
    · fun_prop
  exact hf.topologicalKrullDim_le

end helpers

/-! ### The main vanishing statement -/

section main

variable {k : Type u} [Field k] {X' : Scheme.{u}} [IsIntegral X'] (q : X' ⟶ Spec (.of k))
  [IsProjective q]

/-- The vanishing statement for lists of length `ℓ`, sources of dimension `≤ D` and target sets of
dimension `< e`. -/
def PullbackVanishing (D e ℓ : ℕ) : Prop :=
  ∀ {Y : Scheme.{u}} [CompactSpace Y] [Y.IsSeparated] (π : Y ⟶ X') [IsProjective (π ≫ q)],
    topologicalKrullDim Y ≤ D → ∀ C : Set X', IsClosed C → Set.range π ⊆ C →
    topologicalKrullDim C < e → ∀ ls : List X'.Modules, (∀ L ∈ ls, IsInvertible L) →
    ls.length = ℓ → ∀ (G : Y.Modules) [G.IsQuasicoherent] [G.IsFiniteType],
      mixedEulerDifference (π ≫ q) (ls.map (Scheme.Modules.pullback π).obj) G = 0

omit [IsIntegral X'] [IsProjective q] in
/-- Lists longer than the dimension of the source vanish. -/
theorem pullbackVanishing_of_dim_lt (D e ℓ : ℕ) (h : D + 1 ≤ ℓ) :
    PullbackVanishing q D e ℓ := by
  intro Y _ _ π _ hY C _ _ _ ls hls hlen G _ _
  obtain ⟨d, rfl⟩ : ∃ d, ℓ = d + 1 := ⟨ℓ - 1, by omega⟩
  refine mixedEulerDifference_eq_zero_of_dimension_le d (π ≫ q) (hY.trans ?_) _
    (by simpa using hlen) ?_ G
  · exact_mod_cast (by omega : D ≤ d)
  · intro K hK
    obtain ⟨L, hL, rfl⟩ := List.mem_map.mp hK
    exact (hls L hL).pullback π

omit [IsIntegral X'] [IsProjective q] in
/-- The integral cutting step, for an ample first entry. -/
private theorem integral_ample_first (D e ℓ : ℕ) (he : 1 ≤ e) (hel : e ≤ ℓ)
    (outer : ∀ e' : ℕ, e' < e → 1 ≤ e' → ∀ ℓ' : ℕ, e' ≤ ℓ' → PullbackVanishing q D e' ℓ')
    (longer : ∀ ℓ' : ℕ, ℓ < ℓ' → PullbackVanishing q D e ℓ')
    {V : Scheme.{u}} [IsIntegral V] [CompactSpace V] [V.IsSeparated] (πV : V ⟶ X')
    [IsProjective (πV ≫ q)] (hV : topologicalKrullDim V ≤ D) (C : Set X') (hC : IsClosed C)
    (hπC : Set.range πV ⊆ C) (hdimC : topologicalKrullDim C < e)
    (A : X'.Modules) (hA : SchemeLineAmpleness.IsAmple q A) (rest : List X'.Modules)
    (hrest : ∀ L ∈ rest, IsInvertible L) (hlen : rest.length + 1 = ℓ)
    (T : V.Modules) (hT : IsInvertible T) :
    mixedEulerDifference (πV ≫ q) ((A :: rest).map (Scheme.Modules.pullback πV).obj) T = 0 := by
  let F := Scheme.Modules.pullback πV
  let : F.Monoidal := Scheme.Modules.pullbackMonoidal πV
  let : T.IsQuasicoherent := hT.isQuasicoherent
  let : T.IsFiniteType := isFiniteType_of_isInvertible hT
  have hrestF : ∀ K ∈ rest.map F.obj, IsInvertible K := by
    intro K hK
    obtain ⟨L, hL, rfl⟩ := List.mem_map.mp hK
    exact (hrest L hL).pullback πV
  -- `Δ_{π^* A^j} = j Δ_{π^* A}` modulo longer lists
  have hpow : ∀ j : ℕ, mixedEulerDifference (πV ≫ q)
      (F.obj (CanonicalGeometry.bundleTensorPower A j) :: rest.map F.obj) T =
      (j : ℤ) * mixedEulerDifference (πV ≫ q) (F.obj A :: rest.map F.obj) T := by
    intro j
    induction j with
    | zero =>
      rw [mixedEulerDifference_congr (πV ≫ q)
        (ls := F.obj (CanonicalGeometry.bundleTensorPower A 0) :: rest.map F.obj)
        (ms := unitObj V :: rest.map F.obj)
        (List.Forall₂.cons ⟨Scheme.Modules.pullbackUnitIso πV⟩
          (List.forall₂_same.mpr fun _ _ => ⟨Iso.refl _⟩)), mixedEulerDifference_unit_cons]
      simp
    | succ j ih =>
      have hj := TensorPowerBaseIdealGrading.tensorPower_isInvertible hA.1 j
      rw [mixedEulerDifference_congr (πV ≫ q)
          (ls := F.obj (CanonicalGeometry.bundleTensorPower A (j + 1)) :: rest.map F.obj)
          (ms := (F.obj (CanonicalGeometry.bundleTensorPower A j) ⊗ F.obj A) :: rest.map F.obj)
          (List.Forall₂.cons
            ⟨F.mapIso (SGPT.Support.ModularCurves.monoidalTensorObjIso
              (CanonicalGeometry.bundleTensorPower A j) A).symm ≪≫
              (Functor.Monoidal.μIso F _ _).symm⟩
            (List.forall₂_same.mpr fun _ _ => ⟨Iso.refl _⟩)),
        mixedEulerDifference_tensor_identity, ih]
      have hz : mixedEulerDifference (πV ≫ q)
          (F.obj (CanonicalGeometry.bundleTensorPower A j) :: F.obj A :: rest.map F.obj) T = 0 :=
        longer (ℓ + 1) (by omega) πV hV C hC hπC hdimC
          (CanonicalGeometry.bundleTensorPower A j :: A :: rest)
          (by
            intro L hL
            rcases List.mem_cons.mp hL with rfl | hL
            · exact hj
            rcases List.mem_cons.mp hL with rfl | hL
            · exact hA.1
            · exact hrest L hL)
          (by simp [hlen]) T
      rw [hz]
      push_cast
      ring
  -- a section of a power of `A` not vanishing at the image of the generic point
  obtain ⟨N, hN⟩ := SchemeAmpleLineGlobalGeneration.exists_eventual_generatingSections q A hA
  let m := N + 1
  obtain ⟨Gs, -⟩ := hN m (by omega)
  let Am := CanonicalGeometry.bundleTensorPower A m
  have hAm : IsInvertible Am := TensorPowerBaseIdealGrading.tensorPower_isInvertible hA.1 m
  let x : X' := πV (genericPoint V)
  obtain ⟨s, hs⟩ := exists_section_not_mem_support Am hAm Gs x
  let σ := SchemeModuleGlobalSections.sectionHom Am s
  let τ := SchemeLineSectionEvaluation.pullbackSectionHom πV σ
  have hτ : τ ≠ 0 :=
    SchemeGlobalPullbackCartierRatio.pullbackSection_ne_zero πV Am hAm σ (genericPoint V) hs
  have hFAm : IsInvertible (F.obj Am) := hAm.pullback πV
  suffices hcut : mixedEulerDifference (πV ≫ q) (F.obj Am :: rest.map F.obj) T = 0 by
    rw [hpow m] at hcut
    have hm : (m : ℤ) ≠ 0 := by positivity
    simpa [List.map_cons, hm] using hcut
  -- the zero scheme of the pulled-back section
  let Dz := LineSectionZeroIdeal.zeroIdeal (F.obj Am) hFAm τ
  by_cases hsupp : Dz.support = ⊥
  · -- the pulled-back section vanishes nowhere: the pulled-back sheaf is trivial
    have htop : Dz = ⊤ := (Scheme.IdealSheafData.support_eq_bot_iff _).mp hsupp
    let ε := CurveLineZeroSections.trivializationOfZeroIdealTop (F.obj Am) hFAm τ hτ htop
    rw [mixedEulerDifference_congr (πV ≫ q) (ms := unitObj V :: rest.map F.obj)
      (List.Forall₂.cons ⟨ε⟩ (List.forall₂_same.mpr fun _ _ => ⟨Iso.refl _⟩)),
      mixedEulerDifference_unit_cons]
  · let j := Dz.subschemeι
    let : CompactSpace Dz.subscheme := QuasiCompact.compactSpace_of_compactSpace j
    let : Dz.subscheme.IsSeparated := isSeparated_of_closed j
    let : IsProjective ((j ≫ πV) ≫ q) := by
      rw [Category.assoc]; exact isProjective_closed_comp j (πV ≫ q)
    rw [mixedEulerDifference_sectionDifference (πV ≫ q) (F.obj Am) hFAm τ hτ _ hrestF T hT,
      ← Category.assoc, mixedEulerDifference_map_pullback_comp]
    -- the target set of the zero scheme
    let Zσ : Set X' := ((LineSectionZeroIdeal.zeroIdeal Am hAm σ).support : Set X')
    have hZσ : IsClosed Zσ := (LineSectionZeroIdeal.zeroIdeal Am hAm σ).support.isClosed
    have hspec : ∀ v : V, πV v ∈ closure ({x} : Set X') := by
      intro v
      exact specializes_iff_mem_closure.mp ((genericPoint_specializes v).map πV.continuous)
    have hDsupp : ∀ v ∈ (Dz.support : Set V), πV v ∈ Zσ := by
      intro v hv
      have : v ∈ (Dz.support : Set V) := hv
      rw [SchemeLineZeroSupportPullback.support_pullback πV Am hAm σ] at this
      exact this
    have hrange : Set.range (j ≫ πV) ⊆ closure ({x} : Set X') ∩ Zσ := by
      rintro _ ⟨y, rfl⟩
      refine ⟨hspec _, hDsupp _ ?_⟩
      rw [← Scheme.IdealSheafData.range_subschemeι]
      exact ⟨y, rfl⟩
    obtain ⟨v, hv⟩ : (Dz.support : Set V).Nonempty := by
      rw [Set.nonempty_iff_ne_empty]
      intro h
      apply hsupp
      ext1
      simpa using h
    have hne : (closure ({x} : Set X') ∩ Zσ).Nonempty := ⟨πV v, hspec v, hDsupp v hv⟩
    obtain ⟨e₀, rfl⟩ : ∃ e₀, e = e₀ + 1 := ⟨e - 1, by omega⟩
    have hxC : x ∈ C := hπC ⟨_, rfl⟩
    have hclC : closure ({x} : Set X') ⊆ C :=
      closure_minimal (Set.singleton_subset_iff.mpr hxC) hC
    have hdimx : topologicalKrullDim (closure ({x} : Set X')) ≤ e₀ := by
      have h1 := (isInducing_inclusion hclC).topologicalKrullDim_le
      exact ENat.WithBot.lt_add_one_iff.mp (lt_of_le_of_lt h1 (by exact_mod_cast hdimC))
    obtain ⟨d, rfl, hdimd⟩ := exists_dim_drop x Zσ hZσ hs hne e₀ hdimx
    have hDdim : topologicalKrullDim Dz.subscheme ≤ D := by
      exact IntegralSchemeDimension.topologicalKrullDim_le_of_isIntegralHom j D hV
    have hTA : IsInvertible (T ⊗ F.obj Am) :=
      (hT.tensorObj hFAm).of_iso (SGPT.Support.ModularCurves.monoidalTensorObjIso T _)
    have hTj : IsInvertible ((Scheme.Modules.pullback j).obj (T ⊗ F.obj Am)) := hTA.pullback j
    let : ((Scheme.Modules.pullback j).obj (T ⊗ F.obj Am)).IsQuasicoherent :=
      hTj.isQuasicoherent
    let : ((Scheme.Modules.pullback j).obj (T ⊗ F.obj Am)).IsFiniteType :=
      isFiniteType_of_isInvertible hTj
    exact outer (d + 1) (by omega) (by omega) rest.length (by omega) (j ≫ πV) hDdim
      (closure ({x} : Set X') ∩ Zσ) (isClosed_closure.inter hZσ) hrange
      (ENat.WithBot.lt_add_one_iff.mpr (by exact_mod_cast hdimd)) rest hrest rfl _

omit [IsIntegral X'] [IsProjective q] in
/-- The step for an ample first entry, for any source (prime filtrations). -/
private theorem ample_first (D e ℓ : ℕ) (he : 1 ≤ e) (hel : e ≤ ℓ)
    (outer : ∀ e' : ℕ, e' < e → 1 ≤ e' → ∀ ℓ' : ℕ, e' ≤ ℓ' → PullbackVanishing q D e' ℓ')
    (longer : ∀ ℓ' : ℕ, ℓ < ℓ' → PullbackVanishing q D e ℓ')
    {Y : Scheme.{u}} [CompactSpace Y] [Y.IsSeparated] (π : Y ⟶ X') [IsProjective (π ≫ q)]
    (hY : topologicalKrullDim Y ≤ D) (C : Set X') (hC : IsClosed C)
    (hπC : Set.range π ⊆ C) (hdimC : topologicalKrullDim C < e)
    (A : X'.Modules) (hA : SchemeLineAmpleness.IsAmple q A) (rest : List X'.Modules)
    (hrest : ∀ L ∈ rest, IsInvertible L) (hlen : rest.length + 1 = ℓ)
    (G : Y.Modules) [G.IsQuasicoherent] [G.IsFiniteType] :
    mixedEulerDifference (π ≫ q) ((A :: rest).map (Scheme.Modules.pullback π).obj) G = 0 := by
  have hinv : ∀ K ∈ (A :: rest).map (Scheme.Modules.pullback π).obj, IsInvertible K := by
    intro K hK
    obtain ⟨L, hL, rfl⟩ := List.mem_map.mp hK
    rcases List.mem_cons.mp hL with rfl | hL
    · exact hA.1.pullback π
    · exact (hrest L hL).pullback π
  refine mixedEulerDifference_eq_zero_of_integral (π ≫ q) _ hinv (fun eta T hT => ?_) G
  let I := Scheme.IdealSheafData.vanishingIdeal
    (⟨closure ({eta} : Set Y), isClosed_closure⟩ : Closeds Y)
  let i := I.subschemeι
  let : IsIntegral I.subscheme := SchemePointClosureIntegral.isIntegral_pointClosure eta
  let : CompactSpace I.subscheme := QuasiCompact.compactSpace_of_compactSpace i
  let : I.subscheme.IsSeparated := isSeparated_of_closed i
  let : IsProjective ((i ≫ π) ≫ q) := by
    rw [Category.assoc]; exact isProjective_closed_comp i (π ≫ q)
  change mixedEulerDifference (i ≫ π ≫ q)
    (((A :: rest).map (Scheme.Modules.pullback π).obj).map (Scheme.Modules.pullback i).obj) T = 0
  rw [← Category.assoc, mixedEulerDifference_map_pullback_comp]
  exact integral_ample_first q D e ℓ he hel outer longer (i ≫ π)
    (IntegralSchemeDimension.topologicalKrullDim_le_of_isIntegralHom i D hY) C hC
    (by
      rintro _ ⟨y, rfl⟩
      exact hπC ⟨i y, rfl⟩) hdimC A hA rest hrest hlen T hT

/-- The step for an arbitrary first entry: write it as a difference of ample sheaves. -/
private theorem any_first (D e ℓ : ℕ) (he : 1 ≤ e) (hel : e ≤ ℓ)
    (outer : ∀ e' : ℕ, e' < e → 1 ≤ e' → ∀ ℓ' : ℕ, e' ≤ ℓ' → PullbackVanishing q D e' ℓ')
    (longer : ∀ ℓ' : ℕ, ℓ < ℓ' → PullbackVanishing q D e ℓ') :
    PullbackVanishing q D e ℓ := by
  intro Y _ _ π _ hY C hC hπC hdimC ls hls hlen G _ _
  obtain ⟨L, rest, rfl⟩ : ∃ L rest, ls = L :: rest := by
    cases ls with
    | nil => simp at hlen; omega
    | cons L rest => exact ⟨L, rest, rfl⟩
  have hL : IsInvertible L := hls L (by simp)
  have hrest : ∀ K ∈ rest, IsInvertible K := fun K hK => hls K (by simp [hK])
  have hlen' : rest.length + 1 = ℓ := by simpa using hlen
  obtain ⟨A, hA⟩ := NativeRealNumericalClasses.exists_geometric_ample_line q
  obtain ⟨N, hN⟩ := AmpleLineTwistGeneration.exists_eventual_isVeryAmple q A hA L hL
  let m := N + 1
  let Am := CanonicalGeometry.bundleTensorPower A m
  have hAm : SchemeLineAmpleness.IsAmple q Am :=
    SeshadriAmplenessCriterionNefAmple.positive_power_ample_general q A hA m (by omega)
  have hB : SchemeLineAmpleness.IsAmple q (Am ⊗ L) :=
    AmpleLineTwistGeneration.isAmple_of_isVeryAmple (hN m (by omega))
  let F := Scheme.Modules.pullback π
  let : F.Monoidal := Scheme.Modules.pullbackMonoidal π
  have h₁ := ample_first q D e ℓ he hel outer longer π hY C hC hπC hdimC (Am ⊗ L) hB rest hrest
    hlen' G
  have h₂ := ample_first q D e ℓ he hel outer longer π hY C hC hπC hdimC Am hAm rest hrest
    hlen' G
  have h₃ := longer (ℓ + 1) (by omega) π hY C hC hπC hdimC (Am :: L :: rest)
    (by
      intro K hK
      rcases List.mem_cons.mp hK with rfl | hK
      · exact hAm.1
      · exact hls K hK)
    (by simp [hlen']) G
  simp only [List.map_cons] at h₁ h₂ h₃ ⊢
  rw [mixedEulerDifference_congr (π ≫ q) (ms := (F.obj Am ⊗ F.obj L) :: rest.map F.obj)
      (List.Forall₂.cons ⟨(Functor.Monoidal.μIso F Am L).symm⟩
        (List.forall₂_same.mpr fun _ _ => ⟨Iso.refl _⟩)),
    mixedEulerDifference_tensor_identity] at h₁
  change mixedEulerDifference (π ≫ q) (F.obj Am :: rest.map F.obj) G = 0 at h₂
  change mixedEulerDifference (π ≫ q) (F.obj Am :: F.obj L :: rest.map F.obj) G = 0 at h₃
  rw [h₂, h₃, zero_add, add_zero] at h₁
  exact h₁

/-- All lengths `ℓ ≥ e`, by downward induction from `D + 1`. -/
private theorem all_lengths (D e : ℕ) (he : 1 ≤ e)
    (outer : ∀ e' : ℕ, e' < e → 1 ≤ e' → ∀ ℓ' : ℕ, e' ≤ ℓ' → PullbackVanishing q D e' ℓ') :
    ∀ ℓ : ℕ, e ≤ ℓ → PullbackVanishing q D e ℓ := by
  -- `Q n`: every length `ℓ ≥ e` with `D + 1 ≤ ℓ + n` vanishes
  have key : ∀ n : ℕ, ∀ ℓ : ℕ, e ≤ ℓ → D + 1 ≤ ℓ + n → PullbackVanishing q D e ℓ := by
    intro n
    induction n with
    | zero => exact fun ℓ _ h => pullbackVanishing_of_dim_lt q D e ℓ (by omega)
    | succ n ih =>
      intro ℓ hel hD
      by_cases h : D + 1 ≤ ℓ + n
      · exact ih ℓ hel h
      · exact any_first q D e ℓ he hel outer (fun ℓ' hℓ' => ih ℓ' (by omega) (by omega))
  exact fun ℓ hel => key (D + 1) ℓ hel (by omega)

/-- All target dimensions, by strong induction. -/
private theorem all_dims (D : ℕ) : ∀ e : ℕ, 1 ≤ e → ∀ ℓ : ℕ, e ≤ ℓ → PullbackVanishing q D e ℓ := by
  intro e
  induction e using Nat.strong_induction_on with
  | _ e ih =>
    intro he
    exact all_lengths q D e he fun e' he' h1 ℓ' hl => ih e' he' h1 ℓ' hl

/-- **Pull-backs from lower-dimensional targets have vanishing intersection numbers.** Let
`q : X' ⟶ Spec k` be projective with `X'` integral, `π : Y ⟶ X'` a morphism with `Y` projective
over `k` and `π(Y) ⊆ C` for a closed set `C` with `dim C < r`. Then
`Δ_{π^*L₁} ⋯ Δ_{π^*L_r} χ(Y, G) = 0` for all invertible `Lᵢ` on `X'` and coherent `G` on `Y`. -/
theorem mixedEulerDifference_pullback_eq_zero {Y : Scheme.{u}} [CompactSpace Y] [Y.IsSeparated]
    (π : Y ⟶ X') [IsProjective (π ≫ q)] (C : Set X') (hC : IsClosed C)
    (hπC : Set.range π ⊆ C) (ls : List X'.Modules) (hls : ∀ L ∈ ls, IsInvertible L)
    (hne : ls ≠ []) (hdimC : topologicalKrullDim C < ls.length)
    (G : Y.Modules) [G.IsQuasicoherent] [G.IsFiniteType] :
    mixedEulerDifference (π ≫ q) (ls.map (Scheme.Modules.pullback π).obj) G = 0 := by
  obtain ⟨D, hD⟩ := NativeProjectiveDimensionBounds.exists_dimension_le_of_isProjective (π ≫ q)
  have hpos : 1 ≤ ls.length := List.length_pos_iff.mpr hne
  exact all_dims q D ls.length hpos ls.length le_rfl π hD C hC hπC hdimC ls hls rfl G

/-- **The intersection form vanishes on pulled-back `ℚ`-line bundles** when the target has
smaller dimension: for `π : Y ⟶ X'` with `dim X' ≤ n` and `dim Y ≤ n + 1`,
`(π^*θ₀ ⋯ π^*θ_n)_Y = 0` against any coherent sheaf. This is [BJ22, `prop:intpairing` (iii)]
for models dominating `X × ℙ¹`. -/
theorem interFormQ_pullback_eq_zero (n : ℕ) (hX' : topologicalKrullDim X' ≤ n)
    {Y : Scheme.{u}} [CompactSpace Y] [Y.IsSeparated] (π : Y ⟶ X') [IsProjective (π ≫ q)]
    (hY : topologicalKrullDim Y ≤ (n + 1 : ℕ)) (F : Y.Modules) [F.IsQuasicoherent]
    [F.IsFiniteType] (s : Multiset (PicQ X')) :
    interFormQ (π ≫ q) (n + 1) hY F (s.map (picPullbackQ π)) = 0 := by
  let Z : MultisetForm ℚ (PicQ X') := ⟨fun _ => 0, fun _ _ _ => by simp, fun _ _ _ => by simp⟩
  have key := MultisetForm.ext_tmul ((interFormQ (π ≫ q) (n + 1) hY F).comp (picPullbackQ π)) Z
    (by
      intro u
      rw [MultisetForm.comp_apply, Multiset.map_map]
      change _ = (0 : ℚ)
      have h3 : ((picPullbackQ π) ∘ fun a : Additive X'.Pic => (1 : ℚ) ⊗ₜ[ℤ] a) =
          (fun a => (1 : ℚ) ⊗ₜ[ℤ] a) ∘ picPullbackAdd π := rfl
      rw [h3, ← Multiset.map_map, interFormQ_tmul]
      by_cases hu : Multiset.card u = n + 1
      · obtain ⟨l, rfl⟩ : ∃ l : List (Additive X'.Pic), (l : Multiset _) = u :=
          ⟨u.toList, Multiset.coe_toList u⟩
        have hl : l.length = n + 1 := by simpa using hu
        rw [Multiset.map_coe, interNum_coe (π ≫ q) (n + 1) F _ (by simpa using hl)]
        unfold interList
        rw [List.map_map]
        have hcongr := mixedEulerDifference_congr (π ≫ q)
          (ls := l.map ((fun a => picRep a.toMul) ∘ picPullbackAdd π))
          (ms := (l.map fun a => picRep a.toMul).map (Scheme.Modules.pullback π).obj)
          (by
            rw [List.map_map, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
            refine List.forall₂_same.mpr fun a _ => ?_
            exact picRep_picPullback π a.toMul) F
        rw [hcongr]
        have := mixedEulerDifference_pullback_eq_zero q π Set.univ isClosed_univ
          (Set.subset_univ _) (l.map fun a => picRep a.toMul)
          (by
            intro K hK
            obtain ⟨c, -, rfl⟩ := List.mem_map.mp hK
            exact picRep_isInvertible _)
          (by
            intro h
            have : (l.map fun a => picRep a.toMul).length = 0 := by rw [h]; rfl
            simp [hl] at this)
          (by
            rw [List.length_map, hl]
            refine lt_of_le_of_lt ?_ (ENat.WithBot.lt_add_one_iff.mpr le_rfl)
            refine le_trans ?_ hX'
            exact (IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ X').isHomeomorph).le)
          F
        exact_mod_cast this
      · rw [interNum_of_card_ne (π ≫ q) (n + 1) F _ (by simpa using hu)]
        rfl) s
  simpa [Z] using key

end main

end SGPT.NAPotential.BJIntersect
