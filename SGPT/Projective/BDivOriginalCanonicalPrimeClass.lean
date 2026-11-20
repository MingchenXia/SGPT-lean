import SGPT.Projective.BDivOriginalPrimeCartierGlobalize
import SGPT.Projective.BDivOriginalPrimeSectionClass
import SGPT.Projective.BDivOriginalCartierCanonicalSection
import SGPT.Projective.BDivOriginalDirectChowIdeal
import SGPT.Projective.OriginalSectionUnit
import SGPT.Okounkov.SchemeLineBundleStructuralMetric
import SGPT.NAPotential.BJModelFlagIdeal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Set Filter SGPT.Foundations.Schemes SGPT.Okounkov
open SGPT.NAPotential.GAGAMult SGPT.PSH.IdealRestriction
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves InvertibleIdealQuotient
open scoped Topology Manifold ContDiff

namespace SGPT.Projective.BDivNov16

noncomputable section

/-- The actual stalk of an invertible native ideal has a nonzero generator
in the ring of native holomorphic germs. -/
theorem nativeInvertibleIdeal_stalk_eq_span_nonzero
    {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    [IsComplexManifold n M] (I : GermIdeal n M) (hI : I.IsInvertible) (p : M) :
    ∃ b : NativeHolGerm n M p, b ≠ 0 ∧ stalkIdeal I p = Ideal.span {b} := by
  obtain ⟨U,hU,hpU,t,ht,hdense,hmem⟩ := hI p
  have hthol : HolomorphicAt n t p := by
    filter_upwards [hU.mem_nhds hpU] with q hq
    exact (ht q hq).mdifferentiableAt (hU.mem_nhds hq)
  refine ⟨NativeHolGerm.mk t hthol, ?_, ?_⟩
  · intro hz
    have heq : t =ᶠ[nhds p] (0 : M → ℂ) := Germ.coe_eq.mp
      (congrArg (fun a : NativeHolGerm n M p => (a : Germ (nhds p) ℂ)) hz)
    obtain ⟨W, hW, hWo, hpW⟩ := mem_nhds_iff.mp (heq.and (hU.mem_nhds hpU))
    obtain ⟨q,hq,hqt⟩ := hdense W hWo (fun y hy => (hW hy).2) ⟨p,hpW⟩
    exact hqt (hW hq).1
  · change spanGerms (n := n) (I.mem p) p = _
    apply le_antisymm
    · apply Ideal.span_le.mpr
      rintro γ ⟨F,hF,hFm,rfl⟩
      exact (nativeGerm_principal_mem_iff_isInSpanAt p t hthol F hF).mpr
        ((hmem p hpU F).mp hFm)
    · apply Ideal.span_le.mpr
      rintro γ hγ
      obtain rfl := Set.mem_singleton_iff.mp hγ
      apply mk_mem_spanGerms hthol
      apply (hmem p hpU t).mpr
      exact (nativeGerm_principal_mem_iff_isInSpanAt p t hthol t hthol).mp
        (Ideal.mem_span_singleton_self _)

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (m : ℕ)
  [SmoothOfRelativeDimension (m+1) f] [IsSeparated f] [QuasiCompact f]
  (E : ClosedProjectiveEmbedding f)

local instance : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance : ChartedSpace (ComplexModel (m+1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (m+1)
local instance : IsComplexManifold (m+1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (m+1)

/-- The class of the native prime equals the original inverse ideal line's
curvature for any metric on that very line. -/
theorem primeClass_eq_originalCanonicalCartier_chern [IsIntegral X]
    [CompactSpace (SchemeComplexPoint f)]
    (P : SGPT.PSH.GeometricPrimeCarrier (m + 1) (SchemeComplexPoint f))
    (I : X.IdealSheafData) (hI : I.IsInvertible) (hne : I ≠ ⊥)
    (H : SchemeLineBundleMetric f (m + 1) E (bundleDual I.toModules))
    (hfull : ∀ p : SchemeComplexPoint f,
      Ideal.map (schemeNativeStalkGerm f (m + 1) p)
        (I.stalkIdeal (schemeComplexPointImage f p)) =
        stalkIdeal (vanishingIdeal (n := m + 1) P.val) p) :
    SGPT.BDivisor.DFAlg.cycleClass (SGPT.Siu.primeEffectiveDivisor P) =
      RealBottChern.ofRepresentative
        (H.curvature (originalCartierIdealAtlas I hI).dual) := by
  let a := (originalCartierIdealAtlas I hI).dual
  let σ := originalCartierCanonicalSection I
  let τ := SGPT.Projective.NumEq.AlgebraicCurveDegree.originalSectionUnit σ
  have hτ : τ ≠ 0 :=
    (SGPT.Projective.NumEq.AlgebraicCurveDegree.originalSectionUnit_ne_zero_iff σ).mpr
      (originalCartierCanonicalSection_ne_zero I hI hne)
  have hzero : sectionZeroIdealSheaf (a.tensorPower 1) τ = I :=
    (SGPT.Projective.NumEq.AlgebraicCurveDegree.originalSectionUnit_zeroIdeal a σ).trans
      (originalCartierCanonicalSection_zeroIdeal I hI)
  apply primeClass_eq_originalCartierSection_chern f m E P a τ hτ H
  intro p
  rw [hzero]
  exact hfull p

/-- Each geometric analytic prime on the original smooth integral projective
scheme is literally the complex-point image of an integral effective Cartier
subscheme. Its integration-current class is the first Chern class of the
actual inverse ideal line. The canonical section of that line vanishes on
the original Cartier subscheme with its entire scheme structure. -/
theorem exists_originalCartierPrime_cycleClass [IsIntegral X]
    (P : SGPT.PSH.GeometricPrimeCarrier (m + 1) (SchemeComplexPoint f)) :
    letI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    ∃ (I : X.IdealSheafData) (hI : I.IsInvertible),
      I.radical = I ∧ IsIntegral I.subscheme ∧
      Set.range (schemeComplexPointMap (I.subschemeι ≫ f) f I.subschemeι rfl) = P.val ∧
      originalCartierCanonicalSection I ≠ 0 ∧
      sectionZeroIdealSheaf (originalCartierIdealAtlas I hI).dual
        (originalCartierCanonicalSection I) = I ∧
      SGPT.BDivisor.DFAlg.cycleClass (SGPT.Siu.primeEffectiveDivisor P) =
        RealBottChern.ofRepresentative
          ((schemeLineBundleMetric f (m + 1) E (originalCartierIdealAtlas I hI).dual).curvature
            (originalCartierIdealAtlas I hI).dual) := by
  let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  let : LocallyOfFiniteType f := E.locallyOfFiniteType
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hP : IsComplexAnalyticallyIrreducible (n := m+1) P.val := by
    rw [← P.subvariety_carrier]
    exact P.subvariety.irreducible_carrier
  obtain ⟨I, hrad, _hred, hint, himage, _hinj, _hstalk, hfull⟩ :=
    exists_original_integral_ideal_of_native_irreducible_direct f m E P.val hP
  have hprincipal (p : SchemeComplexPoint f) :
      ∃ b : NativeHolGerm (m+1) (SchemeComplexPoint f) p, b ≠ 0 ∧
      Ideal.map (schemeNativeStalkGerm f (m+1) p)
        (I.stalkIdeal (schemeComplexPointImage f p)) = Ideal.span {b} := by
    rw [hfull p, ← SGPT.PSH.geometricPrimeCarrierEffectiveDivisor_ideal P]
    exact nativeInvertibleIdeal_stalk_eq_span_nonzero _ (SGPT.Siu.primeEffectiveDivisor P).isInvertible p
  have hI := originalIdeal_isInvertible_of_nativePrincipal f m I hprincipal
  have hne : I ≠ ⊥ := by
    intro h
    obtain ⟨p, _⟩ := P.nonempty
    obtain ⟨b, hb, hbI⟩ := hprincipal p
    rw [h] at hbI
    change Ideal.map (schemeNativeStalkGerm f (m + 1) p)
      (SGPT.NAPotential.Berkovich.stalkIdeal (⊥ : X.IdealSheafData)
        (schemeComplexPointImage f p)) = Ideal.span {b} at hbI
    rw [SGPT.NAPotential.BJModel.stalkIdeal_bot, Ideal.map_bot] at hbI
    exact hb (Ideal.span_singleton_eq_bot.mp hbI.symm)
  refine ⟨I, hI, hrad, hint, himage, originalCartierCanonicalSection_ne_zero I hI hne,
    originalCartierCanonicalSection_zeroIdeal I hI, ?_⟩
  exact primeClass_eq_originalCanonicalCartier_chern f m E P I hI hne _ hfull

end

end SGPT.Projective.BDivNov16
