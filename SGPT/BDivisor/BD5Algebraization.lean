import SGPT.BDivisor.BD5SmoothStalk
import SGPT.BDivisor.BD5Transport
import SGPT.GAGA.ChowBlEmbed

/-!
# every model of the book's blow-up system is algebraic

Source: `rmk:bdiv:L749` (chapter_bdiv.tex, line 749): "our transcendental intersection theory
coincides with [Dang–Favre's] in the algebraic setting".  Dang–Favre compute intersection numbers
of Cartier b-divisors on the algebraic models of `X`.  For the book's model system over the
analytification `X(ℂ)` of an integral smooth projective complex scheme `X` (finite sequences of
blow-ups along smooth centres, `SGPT.BDivisor.ModelSystem.blowup`):

* `exists_algebraization_of_chow_bd5`: a compact complex manifold `Y` with a holomorphic embedding
  `Ψ : Y → ℙᴺ` whose image is cut out by homogeneous `P_k` generating the ideal of its cone
  (Chow's theorem) is biholomorphic to `V(ℂ)` for the smooth projective scheme
  `V = Proj(ℂ[x]/(P_k))`, compatibly with the embeddings (`Ψ ∘ e = (V(ℂ) → ℙᴺ)`);
* `exists_algebraization_of_blowup_model_bd5`: every model `π : Y → X(ℂ)` of the book's system is
  biholomorphic to `V(ℂ)` for a smooth projective complex scheme `V` (lane CHOW-BLOWUP's
  projective embedding of blow-up towers and Chow presentation,
  `SGPT.GAGA.ChowBl.exists_chow_presentation_of_isBlowupSequence`);
* **`nefIntersectionReal_eq_snapperKleiman_on_model_bd5`**: on every model `Y` there is such an
  algebraization `e : V(ℂ) ≃ Y`, and for all real Cartier classes `vᵢ` of `V` (real combinations of
  line bundles with any smooth metrics), Weil b-divisors `Dᵢ` realized on `Y` by nef forms whose
  pull-backs to `V(ℂ)` are cohomologous to the Chern forms of the `vᵢ` have book product
  (`def:DF_ext`) equal to Dang–Favre's (multilinearly extended Snapper–Kleiman) number of the `vᵢ`
  on `V` (the `originalRealMixedEuler`, for any base line bundle).
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.BDivisor.BD5

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set Filter
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending
open SGPT.NAPotential.AlgPrimes3.GradedGraphQuotient
open SGPT.NAPotential.AlgPrimes3.ProjectiveGraphProjectivePoint
open SGPT.Okounkov SGPT.GAGA.H0S SGPT.GAGA.ChowBl SGPT.NAPotential.FSPos
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Hodge.BDivChain.NativeDraft SGPT.Hodge.BDivChain.SourceNefIntersectionDraft
open SGPT.Hodge.BDivChain.SourceMixedOrderDraft

attribute [local instance] MvPolynomial.gradedAlgebra

local instance bd5AlgTopology {X : Scheme.{0}} (h : X ⟶ Spec (.of ℂ)) :
    TopologicalSpace (SchemeComplexPoint h) := schemeAnalyticPointTopology h
local instance bd5AlgCharts {X : Scheme.{0}} (h : X ⟶ Spec (.of ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d h] : ChartedSpace (ComplexModel d) (SchemeComplexPoint h) :=
  schemeAnalyticTNChartedSpace h d
local instance bd5AlgManifold {X : Scheme.{0}} (h : X ⟶ Spec (.of ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d h] [IsSeparated h] [QuasiCompact h] :
    IsComplexManifold d (SchemeComplexPoint h) := schemeAnalyticTN_isComplexManifold h d

/-! ### The projective point map of `V(P)` -/

section ProjPoint

variable {N : ℕ} {K : ℕ} (P : Fin K → MvPolynomial (Fin (N + 1)) ℂ) {m : ℕ}
  (hP : ∀ k, (P k).IsHomogeneous m) {n : ℕ} [SmoothOfRelativeDimension n (zeroStructure P hP)]

/-- The homogeneous coordinates of a complex point of `V(P)` are those of its image in `ℙᴺ(ℂ)`. -/
theorem homCoords_zeroEmbedding (q : SchemeComplexPoint (zeroStructure P hP)) (k : Fin (N + 1)) :
    letI := (zeroEmbedding P hP).isSeparated
    letI := (zeroEmbedding P hP).quasiCompact
    homCoords (zeroStructure P hP) (zeroEmbedding P hP) n
      (frameIndex (zeroStructure P hP) (zeroEmbedding P hP) q) q k =
    homCoords (polynomialProjStructureMap ℂ N) (identityEmbedding N) N
      (frameIndex (zeroStructure P hP) (zeroEmbedding P hP) q) (zeroPoint P hP q) k := by
  let := (zeroEmbedding P hP).isSeparated
  let := (zeroEmbedding P hP).quasiCompact
  have hq := mem_coordOpen_frameIndex (zeroStructure P hP) (zeroEmbedding P hP) q
  have hq' : schemeComplexPointImage (polynomialProjStructureMap ℂ N) (zeroPoint P hP q) ∈
      coordOpen (identityEmbedding N) (frameIndex (zeroStructure P hP) (zeroEmbedding P hP) q) :=
    hq
  simp only [homCoords]
  rw [schemeOpenRegularFunction_apply _ n _ _ _ q hq, schemeNativeStalkGerm_eval,
    schemeOpenRegularFunction_apply _ N _ _ _ _ hq', schemeNativeStalkGerm_eval]
  set i := frameIndex (zeroStructure P hP) (zeroEmbedding P hP) q with hi
  have hmem : (zeroSchemeι P hP) (schemeComplexPointImage _ q) ∈
      polynomialProjCoordinateOpen ℂ N i := hq
  have hcomp := schemeComplexPointStalkEval_comp (zeroStructure P hP)
    (polynomialProjStructureMap ℂ N) (zeroSchemeι P hP) rfl q
  have hc := RingHom.congr_fun hcomp ((polynomialProj ℂ N).presheaf.germ
    (polynomialProjCoordinateOpen ℂ N i) ((zeroSchemeι P hP) (schemeComplexPointImage _ q)) hmem
    (polynomialProjCoordinateRegularRatio ℂ N i k))
  have hgs := Scheme.Hom.germ_stalkMap_apply (zeroSchemeι P hP)
    (polynomialProjCoordinateOpen ℂ N i) (schemeComplexPointImage _ q) hmem
    (polynomialProjCoordinateRegularRatio ℂ N i k)
  rw [RingHom.comp_apply] at hc
  erw [hgs] at hc
  exact hc.symm

/-- The complex points of `V(P)` read in `ℙᴺ` through its own embedding are the points of
`ℙᴺ(ℂ)` they define. -/
theorem projectivePoint_zeroEmbedding (q : SchemeComplexPoint (zeroStructure P hP)) :
    letI := (zeroEmbedding P hP).isSeparated
    letI := (zeroEmbedding P hP).quasiCompact
    projectivePoint (zeroStructure P hP) (zeroEmbedding P hP) n q =
      nativeProj N (zeroPoint P hP q) := by
  let := (zeroEmbedding P hP).isSeparated
  let := (zeroEmbedding P hP).quasiCompact
  have hq := mem_coordOpen_frameIndex (zeroStructure P hP) (zeroEmbedding P hP) q
  have hq' : schemeComplexPointImage (polynomialProjStructureMap ℂ N) (zeroPoint P hP q) ∈
      coordOpen (identityEmbedding N) (frameIndex (zeroStructure P hP) (zeroEmbedding P hP) q) :=
    hq
  rw [projectivePoint_eq (zeroStructure P hP) (zeroEmbedding P hP) n _ hq]
  change _ = projectivePoint (polynomialProjStructureMap ℂ N) (identityEmbedding N) N _
  rw [projectivePoint_eq (polynomialProjStructureMap ℂ N) (identityEmbedding N) N _ hq']
  have hv : homCoords (zeroStructure P hP) (zeroEmbedding P hP) n
      (frameIndex (zeroStructure P hP) (zeroEmbedding P hP) q) q =
    homCoords (polynomialProjStructureMap ℂ N) (identityEmbedding N) N
      (frameIndex (zeroStructure P hP) (zeroEmbedding P hP) q) (zeroPoint P hP q) :=
    funext fun k => homCoords_zeroEmbedding P hP q k
  exact (mk_eq_mk_iff _ _).mpr ⟨1, by rw [one_smul]; exact hv.symm⟩

theorem range_projectivePoint_zeroEmbedding :
    letI := (zeroEmbedding P hP).isSeparated
    letI := (zeroEmbedding P hP).quasiCompact
    range (projectivePoint (zeroStructure P hP) (zeroEmbedding P hP) n) =
      commonZeros P := by
  let := (zeroEmbedding P hP).isSeparated
  let := (zeroEmbedding P hP).quasiCompact
  ext x
  constructor
  · rintro ⟨q, rfl⟩
    rw [projectivePoint_zeroEmbedding]
    exact (mem_range_zeroPoint_iff P hP _).mp ⟨q, rfl⟩
  · intro hx
    obtain ⟨p, rfl⟩ := nativeProj_surjective N x
    obtain ⟨q, rfl⟩ := (mem_range_zeroPoint_iff P hP p).mpr hx
    exact ⟨q, projectivePoint_zeroEmbedding P hP q⟩

end ProjPoint

/-! ### Algebraization of projective manifolds with Chow equations -/

section Chow

universe u

/-- **Projective manifolds are algebraic.**  A compact complex manifold `Y` of dimension `n` with
a holomorphic embedding `Ψ : Y → ℙᴺ` whose image is the common zero set of homogeneous `P_k`
generating the ideal sheaf of its cone (Chow's theorem) is biholomorphic to `V(ℂ)` for the
smooth projective complex scheme `V = Proj(ℂ[x]/(P_k))` of relative dimension `n`, compatibly with
the embeddings into `ℙᴺ`. -/
theorem exists_algebraization_of_chow_bd5 {n N : ℕ} {Y : Type} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y] [CompactSpace Y]
    {Ψ : Y → ComplexProjectiveSpace N} (hΨ : IsHolomorphicEmbedding (n := n) Ψ)
    {μ : Type} [Fintype μ] (P : μ → MvPolynomial (Fin (N + 1)) ℂ) {m : ℕ}
    (hP : ∀ k, (P k).IsHomogeneous m)
    (hgen : (coneIdeal (range Ψ)).GeneratedOn (SGPT.GAGA.PN.puncture (SGPT.GAGA.PN.ConeSpace N))
      (fun k => SGPT.GAGA.PN.polyTuple (P k)))
    (hzero : range Ψ = {x | ∀ k, MvPolynomial.eval x.rep (P k) = 0}) :
    ∃ (V : Scheme.{0}) (g : V ⟶ Spec (.of ℂ)) (hsm : SmoothOfRelativeDimension n g)
      (EV : ClosedProjectiveEmbedding g),
      letI := hsm
      letI := EV.isSeparated
      letI := EV.quasiCompact
      ∃ e : SchemeComplexPoint g ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y,
        EV.ambientDimension = N ∧ ∀ q, HEq (Ψ (e q)) (projectivePoint g EV n q) := by
  classical
  -- reindex the equations by `Fin K`
  let eμ := Fintype.equivFin μ
  set K := Fintype.card μ
  let P' : Fin K → MvPolynomial (Fin (N + 1)) ℂ := fun l => P (eμ.symm l)
  have hP' : ∀ l, (P' l).IsHomogeneous m := fun l => hP _
  have hgen' : (coneIdeal (range Ψ)).GeneratedOn (SGPT.GAGA.PN.puncture (SGPT.GAGA.PN.ConeSpace N))
      (fun l => SGPT.GAGA.PN.polyTuple (P' l)) := by
    refine hgen.of_generators (fun l j => hgen.1 _ j) (fun y hy l => ?_) (fun y _ k => ?_)
    · exact (hgen.2 y hy _).2 (SGPT.GAGA.Core.isCombinationAt_gen _ y (eμ.symm l))
    · have h := SGPT.GAGA.Core.isCombinationAt_gen (fun l => SGPT.GAGA.PN.polyTuple (P' l)) y (eμ k)
      simpa [P'] using h
  have hzero' : range Ψ = commonZeros P' := by
    rw [hzero]
    ext x
    simp only [commonZeros, mem_ofPred_eq]
    exact ⟨fun h l => h _, fun h k => by simpa [P'] using h (eμ k)⟩
  have hsm := zeroStructure_smoothOfRelativeDimension hΨ P' hP' hgen' hzero'
  refine ⟨zeroScheme P' hP', zeroStructure P' hP', hsm, zeroEmbedding P' hP', ?_⟩
  let := hsm
  let := (zeroEmbedding P' hP').isSeparated
  let := (zeroEmbedding P' hP').quasiCompact
  let : CompactSpace (SchemeComplexPoint (zeroStructure P' hP')) :=
    (zeroEmbedding P' hP').analyticCompact
  have hemb : IsHolomorphicEmbedding (n := n)
      (projectivePoint (zeroStructure P' hP') (zeroEmbedding P' hP') n) :=
    isHolomorphicEmbedding_projectivePoint _ _ n
  have hrange : range (projectivePoint (zeroStructure P' hP') (zeroEmbedding P' hP') n) =
      range Ψ := by
    rw [range_projectivePoint_zeroEmbedding, hzero']
  refine ⟨diffeomorphOfRangeEq_bd5 hemb hΨ hrange, rfl, fun q => ?_⟩
  exact heq_of_eq (diffeomorphOfRangeEq_bd5_apply hemb hΨ hrange q)

end Chow

/-! ### The book's models -/

section Models

/-- **Every model of the book's blow-up system is algebraic.**  For `X` smooth projective over
`ℂ` of dimension `d` and every model `π : Y → X(ℂ)` of `ModelSystem.blowup` (a finite composition
of blow-ups along smooth centres), there are a smooth projective complex scheme `V` of relative
dimension `d` and a biholomorphism `V(ℂ) ≃ Y`. -/
theorem exists_algebraization_of_blowup_model_bd5 {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ))
    (E : ClosedProjectiveEmbedding f) {d : ℕ} [SmoothOfRelativeDimension d f] :
    let := E.isSeparated
    let := E.quasiCompact
    let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    ∀ π : (SGPT.BDivisor.ModelSystem.blowup d (SchemeComplexPoint f)).Model,
      ∃ (V : Scheme.{0}) (g : V ⟶ Spec (.of ℂ)) (hsm : SmoothOfRelativeDimension d g)
        (EV : ClosedProjectiveEmbedding g),
        letI := hsm
        letI := EV.isSeparated
        letI := EV.quasiCompact
        Nonempty (SchemeComplexPoint g ≃ₘ⟮𝓘(ℂ, ComplexModel d), 𝓘(ℂ, ComplexModel d)⟯
          π.1.carrier) := by
  let := E.isSeparated
  let := E.quasiCompact
  let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  dsimp only
  intro π
  have hX := isHolomorphicEmbedding_projectivePoint f E d
  have hseq : SGPT.Foundations.Analysis.FirstPass.BlowupSequences.IsBlowupSequence d
      (SchemeComplexPoint f) π.1.carrier π.1.map := π.2
  obtain ⟨hc, -⟩ := exists_isHolomorphicEmbedding_of_isBlowupSequence hX hseq
  have := hc
  obtain ⟨N', Ψ', hΨ', m₀, hm⟩ := exists_chow_presentation_of_isBlowupSequence hX hseq
  obtain ⟨μ, hμ, P, hP, hgen, hzero⟩ := hm m₀ le_rfl
  obtain ⟨V, g, hsm, EV, e, -, -⟩ := exists_algebraization_of_chow_bd5 hΨ' P hP hgen hzero
  exact ⟨V, g, hsm, EV, ⟨e⟩⟩

/-- **The Snapper–Kleiman item of `rmk:bdiv:L749` on every model of the book's system.**  Let `X`
be an integral scheme, smooth projective of dimension `k + 1` over `ℂ`, and `π : Y → X(ℂ)` any
model of the book's blow-up system.  Then `Y` has an algebraization: a smooth projective complex
scheme `V` with a biholomorphism `e : V(ℂ) ≃ Y`; and for all real Cartier classes
`vᵢ = ∑_A vᵢ(A) [A]` of `V` (any smooth metrics `K_A`, any base line bundle `B`), every Kähler
form `κ` of `Y`, closed real `(1,1)`-forms `θᵢ` on `Y` nef for `κ` with `e^*{θᵢ} = {∑_A vᵢ(A)
c₁(A, K_A)}`, and Weil b-divisors `Dᵢ` over `X(ℂ)` realized on `Y` by `{θᵢ}`, the book's product
`(D₀, …, D_k)` (`def:DF_ext`) is Dang–Favre's number of the `vᵢ` on `V`, the multilinear extension
of the Snapper–Kleiman numbers `Δ_{A₀} ⋯ Δ_{A_k} χ(B)`. -/
theorem nefIntersectionReal_eq_snapperKleiman_on_model_bd5 {X : Scheme.{0}}
    (f : X ⟶ Spec (.of ℂ)) (E : ClosedProjectiveEmbedding f) [IsIntegral X] {k : ℕ}
    [SmoothOfRelativeDimension (k + 1) f] [Nonempty (SchemeComplexPoint f)] :
    let := E.isSeparated
    let := E.quasiCompact
    let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    let : ConnectedSpace (SchemeComplexPoint f) :=
      SGPT.GAGA.OkoClose.connectedSpace_of_isIntegral f E (k + 1)
    ∀ π : (SGPT.BDivisor.ModelSystem.blowup (k + 1) (SchemeComplexPoint f)).Model,
      ∃ (V : Scheme.{0}) (g : V ⟶ Spec (.of ℂ)) (hsm : SmoothOfRelativeDimension (k + 1) g)
        (EV : ClosedProjectiveEmbedding g),
        letI := hsm
        letI := EV.isSeparated
        letI := EV.quasiCompact
        ∃ e : SchemeComplexPoint g ≃ₘ⟮𝓘(ℂ, ComplexModel (k + 1)), 𝓘(ℂ, ComplexModel (k + 1))⟯
            π.1.carrier,
          ∀ (K : ∀ A : IntrinsicLineBundle V, SchemeLineBundleMetric g (k + 1) EV A.sheaf)
            (B : IntrinsicLineBundle V) (v : Fin (k + 1) → IntrinsicLineBundle V →₀ ℝ)
            (κ : KahlerBackground (k + 1) π.1.carrier)
            (θ : Fin (k + 1) → ClosedRealOneOneForm (k + 1) π.1.carrier),
            (∀ i, NefWithRespectTo κ (θ i)) →
            (∀ i, RealBottChern.ofRepresentative
                (ClosedRealOneOneForm.pullback e.contMDiff (θ i)) =
              RealBottChern.ofRepresentative (Finsupp.linearCombination ℝ
                (fun A : IntrinsicLineBundle V => (K A).curvature A.atlas) (v i))) →
            ∀ D : Fin (k + 1) →
                WeilFamilyAny (SGPT.BDivisor.ModelSystem.blowup (k + 1) (SchemeComplexPoint f)),
              (∀ i, IsRealizationAny (D i) π (RealBottChern.ofRepresentative (θ i))) →
              nefIntersectionReal D =
                SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI.originalRealMixedEuler
                  g EV (k + 1) B v := by
  let := E.isSeparated
  let := E.quasiCompact
  let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  let : ConnectedSpace (SchemeComplexPoint f) :=
    SGPT.GAGA.OkoClose.connectedSpace_of_isIntegral f E (k + 1)
  dsimp only
  intro π
  obtain ⟨V, g, hsm, EV, ⟨e⟩⟩ := exists_algebraization_of_blowup_model_bd5 f E π
  refine ⟨V, g, hsm, EV, e, fun K B v κ θ hnef hclass D hD => ?_⟩
  let := hsm
  exact SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI.nefIntersectionReal_eq_originalRealMixedEuler_of_diffeomorph_bd5
    f E g EV K B v π e κ θ hnef hclass D hD

end Models

end SGPT.BDivisor.BD5
