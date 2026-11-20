import SGPT.Okounkov.OF15CoordFlag
import SGPT.Okounkov.OF15ModelData
import SGPT.Okounkov.OF13Final
import SGPT.Okounkov.OF9ValCurrIndependence
import SGPT.Okounkov.OF2AbhyankarFlagExample
import SGPT.GAGA.OkoCloseDXMain
import SGPT.Foundations.Analysis.Pending.DominationLogResolution
import SGPT.Foundations.Analysis.Pending.BlowupConnected

/-!
# `rmk:valcurr`: existence of presentations `ν = ν_{Y•} g` by smooth flags

Source: chapter *The theory of Okounkov bodies*, `rmk:valcurr`:

> Consider a rank `n` (surjective) valuation `ν : ℂ(X)^× → ℤⁿ` … Take a resolution `π : Y → X`
> such that there is a smooth flag `Y•` on `Y` and `g ∈ Aut(ℤⁿ_lex)` such that `ν = ν_{Y•} g`.

The remark takes the existence of such a resolution for granted (it is [CFKLRS17, Thm 2.9],
`rmk:Abhyankar`, followed by an embedded resolution of the flag). Here, for an integral smooth
projective complex scheme `X` of dimension `n = m + 1`:

* **`exists_blowupPresentation_of_hasRationalAlgebraization`**: if every blow-up tower of `X(ℂ)`
  has a rational algebraization (the `HasRationalAlgebraization`, the only input not yet
  proved, lane OF14), then every surjective valuation `ν : ℂ(X)^× → ℤⁿ_lex` has a presentation
  `ν = ν_{Y•} G` (the `BlowupPresentation`) by a **smooth flag** `Y•` on a finite blow-up
  tower `π : Y → X(ℂ)` (a modification, `def:modif`) with `G` unit upper triangular. No embedded
  resolution is needed: the flag consists of connected components of intersections of the members
  of the simple normal crossings divisor of the principalization of `u₁, …, uₙ` (`ν(u_k) = e_k`)
  through the centre of `ν` (`OF15.sncFlag`).

Proof. Principalize `u₁, …, uₙ` with a normal crossings divisor `E` on a tower `Y`
(`exists_tower_snc_monomial`); algebraize `Y ≃ V(ℂ)`, `ℂ(V) ≃ ℂ(X)` (hypothesis); `ν` has a
centre `x = p` on `V` (properness); at `y = φ(p)` the `u_k` are monomials in the flat coordinates
`ℓⱼ` of an adapted chart, every `ℓⱼ` cuts out a member `E (idx j)`, and Chow gives algebraic local
equations `zⱼ` with an order `σ` making `(ν(z_{σ(i)}))ᵢ` unit upper triangular
(`exists_coordinates_of_analyticLogResolution`). The flag of members `Y•` (`sncFlag`, smooth by
`isSmoothFlag_sncFlag`) has unit upper triangular matrix `(ν_{Y•}(ℓ_{σ(i)}))ᵢ`
(`isUnitUpperTriangular_sncFlag_matrix`), so `ν` and `ν_{Y•} ∘ π^*` are both equivalent to the
coordinate admissible flag valuation of `z, σ` on `V` (the `lexEquivalent_of_coordFlag`).

For a **normal** `X`, every resolution `ρ : Y → X` (`OF12.Resolution`) carries a
presentation (`nonempty_presentation_of_resolution`), under the same hypothesis for `Y`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.Okounkov.OF15

open CategoryTheory AlgebraicGeometry Set Filter IsLocalRing SGPT.Foundations.Schemes
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
open SGPT.Foundations.Analysis.Pending.NormalCrossings SGPT.Foundations.Analysis.Pending.BoundaryCount
open BlowupFlatCoordinates
open SGPT.Okounkov SGPT.Okounkov.OF5 SGPT.Okounkov.OF6 SGPT.Okounkov.ValCurr SGPT.Okounkov.OF9
open SGPT.Okounkov.OF13
open scoped Topology Manifold ContDiff

section Main

variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ)) {m : ℕ}
  [SmoothOfRelativeDimension (m + 1) f] [IsSeparated f] [QuasiCompact f]

local instance of15pTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance of15pCharts : ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (m + 1)
local instance of15pManifold : IsComplexManifold (m + 1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (m + 1)

/-- **Every blow-up tower of `X(ℂ)` has a rational algebraization** (lane OF13's
`HasRationalAlgebraization` for all towers: the hypothesis of
`OF13.exists_admissibleFlag_lexEquivalent_of_hasRationalAlgebraization`, being proved by lane
OF14). -/
def TowersAlgebraize : Prop :=
  ∀ (Y : Type) [TopologicalSpace Y] [ChartedSpace (ComplexModel (m + 1)) Y]
    [IsComplexManifold (m + 1) Y] (π : Y → SchemeComplexPoint f)
    (hseq : IsBlowupSequence (m + 1) (SchemeComplexPoint f) Y π),
    HasRationalAlgebraization f (m + 1)
      (HironakaChowLemma.isAnalyticModification_of_isBlowupSequence hseq)

set_option maxHeartbeats 1000000 in
/-- **`rmk:valcurr`, existence of a presentation `ν = ν_{Y•} g` (smooth `X`).** Let `X` be an
integral smooth projective complex scheme of dimension `n = m + 1` all of whose blow-up towers have
rational algebraizations. Then every surjective valuation `ν : ℂ(X)^× → ℤⁿ_lex` is
`ν = ν_{Y•} G` for a smooth flag `Y•` on a finite blow-up tower `π : Y → X(ℂ)` and a unit upper
triangular `G` (the `BlowupPresentation`). -/
theorem exists_blowupPresentation_of_towersAlgebraize (E : ClosedProjectiveEmbedding f)
    (halg : TowersAlgebraize f (m := m))
    (ν : AddValuation X.functionField (WithTop (Lex (Fin (m + 1) → ℤ))))
    (hν : Function.Surjective ν) : Nonempty (BlowupPresentation f ν) := by
  classical
  /- the functions `u_k` with `ν(u_k) = e_k` -/
  have hu : ∀ k : Fin (m + 1), ∃ q, ν q = basisValue k := fun k => hν _
  choose u hνu using hu
  have hu0 : ∀ k, u k ≠ 0 := fun k h => by
    have := hνu k
    rw [h, AddValuation.map_zero] at this
    exact WithTop.top_ne_coe this
  /- the log resolution tower with its normal crossings divisor, and its algebraization -/
  obtain ⟨Y, tY, cY, mY, π, hseq, E', hsnc, hmono⟩ := exists_tower_snc_monomial f (m + 1) E u hu0
  set hmod := HironakaChowLemma.isAnalyticModification_of_isBlowupSequence hseq with hmod_def
  obtain ⟨V, hV, g, hsm, EV, hrest⟩ := halg Y π hseq
  let := hsm
  let := EV.isSeparated
  let := EV.quasiCompact
  let := EV.isProper
  obtain ⟨φ, e, hcompat⟩ := hrest
  let hφmod := isAnalyticModification_of_diffeomorph φ
  /- the centre of `ν` on `V` -/
  let ν' := ν.comap e.symm.toRingHom
  have hν' : Function.Surjective ν' := fun w => by
    obtain ⟨q, hq⟩ := hν w
    exact ⟨e q, by change ν (e.symm (e q)) = w; rw [e.symm_apply_apply, hq]⟩
  have hclosed := OF4.isClosed_valuationCenter g (m + 1) ν' hν'
  obtain ⟨p, hp⟩ := exists_schemeComplexPoint_eq_of_isClosed g hclosed
  have hcent : AlgebraicValuation.IsValuationCenter ν' (schemeComplexPointImage g p) := by
    rw [hp]
    exact AlgebraicValuation.isValuationCenter_valuationCenter g ν'
  /- an adapted chart at `y = φ(p)` and the monomial data there -/
  obtain ⟨S, Φ, hΦ⟩ := exists_isAdaptedChart hsnc (φ p)
  obtain ⟨η, a, haM, huY, hregY⟩ := hmono (φ p) S Φ hΦ
  /- pull-back of germs along `φ` at `p` -/
  let c := NativeHolGerm.comap φ hφmod.1 p
  have hφz : ∀ᶠ z' in 𝓝 p,
      ContMDiffAt 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1)) ∞ φ z' :=
    Eventually.of_forall fun z' => φ.contMDiff z'
  have hψ : ∀ᶠ y' in 𝓝 (φ p),
      ContMDiffAt 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1)) ∞ φ.symm y' :=
    Eventually.of_forall fun y' => φ.symm.contMDiff y'
  have hcmk : ∀ (h : Y → ℂ) (hh : HolomorphicAt (m + 1) h (φ p))
      (hh' : HolomorphicAt (m + 1) (h ∘ φ) p),
      c (NativeHolGerm.mk h hh) = NativeHolGerm.mk (h ∘ φ) hh' := fun h hh hh' =>
    Subtype.ext (NativeHolGerm.comap_mk φ hφmod.1 p h hh)
  have hback : ∀ (h : SchemeComplexPoint g → ℂ), HolomorphicAt (m + 1) h p →
      HolomorphicAt (m + 1) (h ∘ φ.symm) (φ p) := fun h hh => by
    have h1 : HolomorphicAt (m + 1) h (φ.symm (φ p)) := by rwa [φ.symm_apply_apply]
    exact h1.comp_contMDiff hψ
  have hcomp_back : ∀ (h : SchemeComplexPoint g → ℂ), (h ∘ φ.symm) ∘ φ = h := fun h => by
    funext w
    simp
  have hcsurj : Function.Surjective c := by
    intro gm
    obtain ⟨h, hh, rfl⟩ := NativeHolGerm.exists_eq_mk gm
    refine ⟨NativeHolGerm.mk (h ∘ φ.symm) (hback h hh), ?_⟩
    rw [hcmk _ (hback h hh) (by rw [hcomp_back]; exact hh)]
    apply NativeHolGerm.mk_eq_mk_iff.mpr
    exact Eventually.of_forall fun w => by simp
  have hcinj : Function.Injective c := OF2.nativeHolGerm_comap_injective hφmod p
  let cE : NativeHolGerm (m + 1) Y (φ p) ≃+* NativeHolGerm (m + 1) (SchemeComplexPoint g) p :=
    RingEquiv.ofBijective c ⟨hcinj, hcsurj⟩
  /- the log resolution data transported to `V(ℂ)` at `p` -/
  let ℓ : Fin (m + 1) → SchemeComplexPoint g → ℂ := fun j => flatCoord Φ j ∘ φ
  have hℓ : ∀ j, HolomorphicAt (m + 1) (ℓ j) p := fun j =>
    (holomorphicAt_flatCoord Φ j (mem_flatDomain_self Φ)).comp_contMDiff hφz
  have hcℓ : ∀ j, c (flatGerm Φ j) = NativeHolGerm.mk (ℓ j) (hℓ j) := fun j => hcmk _ _ _
  have hspanV : Ideal.span (Set.range fun j => NativeHolGerm.mk (ℓ j) (hℓ j)) =
      maximalIdeal (NativeHolGerm (m + 1) (SchemeComplexPoint g) p) := by
    have h1 := congrArg (Ideal.map cE) (span_flatCoord_eq_maximalIdeal Φ hΦ.2.1 hΦ.1)
    rw [Ideal.map_span, IsLocalRing.map_ringEquiv_maximalIdeal, ← Set.range_comp] at h1
    rw [← h1]
    congr 2
  have hcoordV : Ideal.span (Set.range fun j =>
      NativeHolGerm.chartEquiv p (NativeHolGerm.mk (ℓ j) (hℓ j))) =
      maximalIdeal (HolGerm (ComplexModel (m + 1))) := by
    have h := congrArg (Ideal.map (NativeHolGerm.chartEquiv (n := m + 1) p)) hspanV
    rw [Ideal.map_span, IsLocalRing.map_ringEquiv_maximalIdeal, ← Set.range_comp] at h
    exact h
  let Mem : Fin (m + 1) → Prop := fun j => ∃ i, φ p ∈ E'.get i ∧ S i = {j}
  let M : Finset (Fin (m + 1)) := Finset.univ.filter Mem
  let HV : Fin (m + 1) → Set (SchemeComplexPoint g) := fun j =>
    if h : Mem j then φ ⁻¹' E'.get h.choose else ∅
  have hHV : ∀ j (h : Mem j), HV j = φ ⁻¹' E'.get h.choose := fun j h => by
    simp only [HV, dif_pos h]
  have hHan : ∀ j ∈ M, IsComplexAnalyticSubset (n := m + 1) (HV j) := by
    intro j hj
    have hj' : Mem j := (Finset.mem_filter.mp hj).2
    rw [hHV j hj']
    exact AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage φ.contMDiff
      (isComplexAnalyticSubset_of_isSNCDivisor hsnc _)
  -- on `Y`: the member through `φ p` with coordinate `j` is `{ℓⱼ = 0}` near `φ p`
  have hflatY : ∀ j (h : Mem j) {w : Y}, w ∈ flatDomain Φ →
      (w ∈ E'.get h.choose ↔ flatCoord Φ j w = 0) := by
    intro j h w hw
    have h1 := hΦ.2.2.1 h.choose h.choose_spec.1 hw.1 hw.2
    refine h1.trans ?_
    have hsub : coordSubspace (S h.choose) = coordSubspace ({j} : Finset (Fin (m + 1))) :=
      congrArg coordSubspace h.choose_spec.2
    rw [hsub]
    simp only [coordSubspace, Finset.mem_singleton, forall_eq, Set.mem_ofPred_eq]
    rfl
  have hℓmem : ∀ j ∈ M, (vanishingIdeal (n := m + 1) (HV j)).mem p (ℓ j) := by
    intro j hj
    have hj' : Mem j := (Finset.mem_filter.mp hj).2
    rw [hHV j hj']
    refine ⟨hℓ j, ?_⟩
    have hev : ∀ᶠ w in 𝓝 (φ p), w ∈ flatDomain Φ :=
      (isOpen_flatDomain Φ).mem_nhds (mem_flatDomain_self Φ)
    filter_upwards [φ.continuous.continuousAt.eventually hev] with w hw hwE
    change φ w ∈ E'.get hj'.choose at hwE
    exact (hflatY j hj' hw).mp hwE
  have hℓgen : ∀ j ∈ M, ∀ (h : SchemeComplexPoint g → ℂ) (hh : HolomorphicAt (m + 1) h p),
      (vanishingIdeal (n := m + 1) (HV j)).mem p h →
        NativeHolGerm.mk h hh ∈ Ideal.span {NativeHolGerm.mk (ℓ j) (hℓ j)} := by
    intro j hj h hh hhv
    have hj' : Mem j := (Finset.mem_filter.mp hj).2
    rw [hHV j hj'] at hhv
    have hvY : (vanishingIdeal (n := m + 1) (E'.get hj'.choose)).mem (φ p) (h ∘ φ.symm) := by
      refine ⟨hback h hh, ?_⟩
      obtain ⟨-, hv⟩ := hhv
      have hcont : Tendsto φ.symm (𝓝 (φ p)) (𝓝 p) := by
        have := φ.symm.continuous.continuousAt (x := φ p)
        rwa [ContinuousAt, φ.symm_apply_apply] at this
      filter_upwards [hcont.eventually hv] with y' hy' hy'E
      apply hy'
      change φ (φ.symm y') ∈ E'.get hj'.choose
      rw [φ.apply_symm_apply]
      exact hy'E
    have hmem := flatCoord_generates_vanishingIdeal Φ hΦ.2.1 hΦ.1 (H := E'.get hj'.choose)
      (j := j) (fun {w} hz hzN => by
        have hchart := hΦ.2.2.1 hj'.choose hj'.choose_spec.1 hz hzN
        have hsub : coordSubspace (S hj'.choose) =
            coordSubspace ({j} : Finset (Fin (m + 1))) :=
          congrArg coordSubspace hj'.choose_spec.2
        exact hchart.trans (Iff.of_eq (congrArg
          (fun A => Φ.toFun ((complexChartAt (φ p)).val w) ∈ A) hsub))) (h ∘ φ.symm) (hback h hh) hvY
    have h2 := Ideal.mem_map_of_mem c hmem
    rw [Ideal.map_span, Set.image_singleton] at h2
    rw [hcmk _ (hback h hh) (by rw [hcomp_back]; exact hh)] at h2
    have h3 : NativeHolGerm.mk ((h ∘ φ.symm) ∘ φ) (by rw [hcomp_back]; exact hh) =
        NativeHolGerm.mk h hh := by
      apply NativeHolGerm.mk_eq_mk_iff.mpr
      exact Eventually.of_forall fun w => by simp
    rw [h3] at h2
    change NativeHolGerm.mk h hh ∈ Ideal.span {c (flatGerm Φ j)} at h2
    rwa [hcℓ j] at h2
  -- the monomials on `V(ℂ)` at `p`
  have hfrac : ∀ q : X.functionField, schemeNativeFunctionFieldGerm g (m + 1) p (e q) =
      fracComap hφmod p (ratGerm f hmod (φ p) q) := fun q => hcompat q p
  have huV : ∀ k, schemeNativeFunctionFieldGerm g (m + 1) p (e (u k)) =
      algebraMap _ (FractionRing (NativeHolGerm (m + 1) (SchemeComplexPoint g) p))
          ((Units.map c.toMonoidHom (η k) : (NativeHolGerm (m + 1) (SchemeComplexPoint g) p)ˣ) :
            NativeHolGerm (m + 1) (SchemeComplexPoint g) p) *
        ∏ j, (algebraMap _ (FractionRing (NativeHolGerm (m + 1) (SchemeComplexPoint g) p))
          (NativeHolGerm.mk (ℓ j) (hℓ j))) ^ (a k j) := by
    intro k
    rw [hfrac, huY k, map_mul, map_prod, fracComap_algebraMap]
    simp only [map_zpow₀, fracComap_algebraMap]
    congr 1
  have hregV : ∀ k, (∃ h : NativeHolGerm (m + 1) (SchemeComplexPoint g) p,
        schemeNativeFunctionFieldGerm g (m + 1) p (e (u k)) = algebraMap _ _ h) ∨
      ∃ h : NativeHolGerm (m + 1) (SchemeComplexPoint g) p,
        (schemeNativeFunctionFieldGerm g (m + 1) p (e (u k)))⁻¹ = algebraMap _ _ h := by
    intro k
    rcases hregY k with ⟨h, hh⟩ | ⟨h, hh⟩
    · exact Or.inl ⟨c h, by rw [hfrac, hh, fracComap_algebraMap]⟩
    · exact Or.inr ⟨c h, by rw [hfrac, ← map_inv₀, hh, fracComap_algebraMap]⟩
  have hregV' : ∀ k, (∃ h : NativeHolGerm (m + 1) (SchemeComplexPoint g) p,
        schemeNativeFunctionFieldGerm g (m + 1) p (e (u k)) = algebraMap _ _ h) ∨
      ∃ h : NativeHolGerm (m + 1) (SchemeComplexPoint g) p,
        schemeNativeFunctionFieldGerm g (m + 1) p (e (u k))⁻¹ = algebraMap _ _ h := by
    intro k
    rcases hregV k with h | ⟨h, hh⟩
    · exact Or.inl h
    · exact Or.inr ⟨h, by rw [map_inv₀]; exact hh⟩
  /- algebraic coordinates at the centre and the order `σ` -/
  obtain ⟨hMuniv, z, B, σ, hzB, hsncz, hσ⟩ := exists_coordinates_of_analyticLogResolution EV e ν p
    hcent ℓ hℓ hcoordV M HV hHan hℓmem hℓgen u (fun k => Units.map c.toMonoidHom (η k)) a
    (fun k j hj => haM k j fun hmem => hj (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hmem⟩))
    huV hregV' hνu
  /- every coordinate hyperplane is a member: the flag of members -/
  have hMem : ∀ j, Mem j := fun j => by
    have hj : j ∈ M := by rw [hMuniv]; exact Finset.mem_univ j
    exact (Finset.mem_filter.mp hj).2
  let idx : Fin (m + 1) → Fin E'.length := fun j => (hMem j).choose
  have hidx : ∀ j, φ p ∈ E'.get (idx j) ∧ S (idx j) = {j} := fun j => (hMem j).choose_spec
  have hidx_inj : Function.Injective idx := by
    intro j j' h
    have h1 := (hidx j).2
    rw [h, (hidx j').2] at h1
    exact (Finset.singleton_injective h1).symm
  let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  have hXne : Nonempty (SchemeComplexPoint f) := OF2.nonempty_schemeComplexPoint f E
  have hXconn : ConnectedSpace (SchemeComplexPoint f) :=
    SGPT.GAGA.OkoClose.connectedSpace_of_isIntegral f E (m + 1)
  have hYconn : ConnectedSpace Y := BlowupConnected.connectedSpace_of_isBlowupSequence π hseq
  obtain ⟨hYc, ⟨omegaY⟩⟩ := DominationLogResolution.compactSpace_and_kahler_of_isBlowupSequence
    ⟨schemeProjectiveTNKahlerBackground f (m + 1) E⟩ hseq
  have hsmF : IsSmoothFlag (sncFlag E' idx σ (φ p)) :=
    isSmoothFlag_sncFlag E' idx σ (φ p) (Nat.succ_pos m) hsnc hidx_inj fun j => (hidx j).1
  have hyL : φ p ∈ sncFlag E' idx σ (φ p) (Fin.last (m + 1)) :=
    mem_connectedComponentIn (mem_memberInter_of_forall E' idx (φ p) (fun j => (hidx j).1) _)
  let F : OriginalFlagGeometry.{0} (m + 1) :=
    OriginalFlagGeometry.ofOriginal omegaY (sncFlag E' idx σ (φ p)) hsmF
  let x0 : OriginalFlagGermPoint F := ⟨φ p, hyL⟩
  have hGmat := isUnitUpperTriangular_sncFlag_matrix omegaY (Nat.succ_pos m) hsnc hΦ hidx σ hsmF hyL
  /- the valuation induced by the flag, read on `V` -/
  let μ := OF2.modificationFlagValuation f F (π := π) hmod
  let μ' := μ.comap e.symm.toRingHom
  have hμ' : ∀ a : V.presheaf.stalk (schemeComplexPointImage g p),
      μ' (algebraMap _ V.functionField a) =
        originalFlagGermValuation F x0 (cE.symm (schemeNativeStalkGerm g (m + 1) p a)) := by
    intro a
    have hrat : ratGerm f hmod (φ p) (e.symm (algebraMap _ V.functionField a)) =
        algebraMap _ _ (cE.symm (schemeNativeStalkGerm g (m + 1) p a)) := by
      apply (fracComap hφmod p).injective
      rw [← hfrac, e.apply_symm_apply, schemeNativeFunctionFieldGerm_stalk,
        fracComap_algebraMap]
      congr 1
      exact (cE.apply_symm_apply _).symm
    change OF2.modificationFlagValuation f F hmod (e.symm (algebraMap _ V.functionField a)) = _
    rw [OF2.modificationFlagValuation_eq_at f F hmod x0]
    change originalFlagGermFractionValuation F x0
      (ratGerm f hmod (φ p) (e.symm (algebraMap _ V.functionField a))) = _
    rw [hrat]
    exact originalFlagGermFractionValuation_algebraMap F x0 _
  have hcentμ : AlgebraicValuation.IsValuationCenter μ' (schemeComplexPointImage g p) := by
    refine ⟨fun a => ?_, fun a ha => ?_⟩
    · rw [hμ']
      exact originalFlagGermValuation_nonneg F x0 _
    · rw [hμ']
      apply originalFlagGermValuation_pos_of_mem_maximalIdeal
      have h1 : schemeNativeStalkGerm g (m + 1) p a ∈
          maximalIdeal (NativeHolGerm (m + 1) (SchemeComplexPoint g) p) :=
        (mem_maximalIdeal _).mpr fun hu => (mem_maximalIdeal a).mp ha
          (isUnit_of_map_unit (schemeNativeStalkGerm g (m + 1) p) a hu)
      rw [mem_maximalIdeal, mem_nonunits_iff] at h1 ⊢
      intro hu
      have hunit : IsUnit (cE (cE.symm (schemeNativeStalkGerm g (m + 1) p a))) := hu.map cE
      rw [RingEquiv.apply_symm_apply] at hunit
      exact h1 hunit
  have hμz : ∀ i, μ' (algebraMap _ V.functionField (z (σ i))) =
      vecValue (fun j => (originalFlagGermVector F x0 (flatGerm Φ (σ i))
        (flatGerm_ne_zero Φ hΦ.1 hΦ.2.1 (σ i)) j : ℤ)) := by
    intro i
    rw [hμ', hzB, map_mul]
    have h1 : cE.symm (NativeHolGerm.mk (ℓ (σ i)) (hℓ (σ i))) = flatGerm Φ (σ i) := by
      rw [RingEquiv.symm_apply_eq]
      exact (hcℓ (σ i)).symm
    rw [h1, (originalFlagGermValuation F x0).map_mul,
      OF9.originalFlagGermValuation_eq_zero_of_isUnit F x0 ((B (σ i)).isUnit.map cE.symm),
      zero_add, originalFlagGermValuation_apply_of_ne_zero F x0 _
        (flatGerm_ne_zero Φ hΦ.1 hΦ.2.1 (σ i))]
    rfl
  have hGμ : IsUnitUpperTriangular (fun i => ofLex ((μ' (algebraMap _ V.functionField
      (z (σ i)))).untopD 0)) := by
    have h1 : (fun i => ofLex ((μ' (algebraMap _ V.functionField (z (σ i)))).untopD 0)) =
        fun i j => (originalFlagGermVector F x0 (flatGerm Φ (σ i))
          (flatGerm_ne_zero Φ hΦ.1 hΦ.2.1 (σ i)) j : ℤ) := by
      funext i
      rw [hμz i, WithTop.untopD_coe, ofLex_toLex]
    rw [h1]
    exact hGmat
  /- both valuations are equivalent to the coordinate admissible flag valuation on `V` -/
  obtain ⟨Yf, hYf, hpt, hgen⟩ := OF11.exists_admissibleFlag_of_isSNCCoordinates hsncz σ
  have h1 := OF11.lexEquivalent_of_coordFlag hYf hpt z σ hgen ν' hcent hσ
  have h2 := OF11.lexEquivalent_of_coordFlag hYf hpt z σ hgen μ' hcentμ hGμ
  obtain ⟨G, hG, hνμ⟩ :=
    valuationsLexEquivalent_equivalence.trans (valuationsLexEquivalent_equivalence.symm h2) h1
  refine ⟨{ F := F
            π := π
            isModification := hmod
            isBlowupSequence := hseq
            G := G
            unitriangular := hG
            presents := ?_ }⟩
  ext q
  have h := congrArg (fun w : AddValuation V.functionField (WithTop (Lex (Fin (m + 1) → ℤ))) =>
    w (e q)) hνμ
  change ν (e.symm (e q)) = lexWithTopHom G hG (μ (e.symm (e q))) at h
  rw [e.symm_apply_apply] at h
  rw [lexMapValuation_apply]
  exact h

end Main

end SGPT.Okounkov.OF15
