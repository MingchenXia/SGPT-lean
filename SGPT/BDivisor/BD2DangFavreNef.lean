import SGPT.BDivisor.BD2Kleiman
import SGPT.BDivisor.BDDangFavreCartier

/-!
# Dang–Favre's nef Cartier classes are the algebraic nef Cartier b-divisors

Source `rmk:bdiv:L749` (`chapter_bdiv.tex`): "The algebraic nef b-divisors are introduced by
Dang--Favre [DF20] [...] our transcendental intersection theory coincides with theirs in the
algebraic setting."

Over a compact connected projective manifold `X` (b-divisors over the book's blow-up models),
lane BD identified Dang–Favre's Weil classes with the algebraic b-divisors
(`DFAlg.dangFavreWeilEquiv`) and Dang–Favre's Cartier classes determined on a model `Y` by a
numerical class `c ∈ N¹(Y)_ℝ` with the algebraic b-divisors realized on `Y` by `cl(c)`
(`DFAlg.isDeterminedOn_iff_isRealizationAny`).  Dang–Favre call such a class nef when `c` is
nef in their sense, i.e. `c · Γ ≥ 0` for every curve `Γ` (`DFAlg.IsCurveNef`).  With Kleiman's
criterion (`Kleiman.classNef_of_isCurveNef`, lane BD2) this file proves:

* `isAlgNefCartierAny_of_dangFavreNefCartier`: the image of every Dang–Favre nef Cartier class is
  an algebraic nef Cartier b-divisor (realized on a model by a **nef** class of `NS(Y)_ℝ`);
* `isAlgNefCartierAny_iff_exists_dangFavreNefCartier`: **the algebraic nef Cartier b-divisors
  are exactly the images of Dang–Favre's nef Cartier classes**;
* `isCurveNef_numericalClass_iff_classNef`: on every model, Dang–Favre's nef cone in `N¹(Y)_ℝ`
  is the nef cone of `NS(Y)_ℝ` under `N¹(Y)_ℝ ≃ NS(Y)_ℝ`;
* `IsDangFavreNef`: Dang–Favre's nef Weil classes, the limits of nets of nef Cartier classes in
  the projective-limit topology (each `N¹(Y)_ℝ` with its Euclidean topology);
  `isAlgNefAny_iff_isDangFavreNef`, `isAlgNefAny_iff_exists_dangFavreNef`: **the algebraic nef
  b-divisors (`IsAlgNefAny`) are exactly the images of Dang–Favre's nef classes** (the cycle class
  maps identify the Euclidean topologies, `tendsto_euclideanTopology_iff_of_injective`).
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.BDivisor.DFAlg

open Filter
open scoped Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses
  SGPT.Hodge.BDivChain.NativeDraft

attribute [local instance] blowup_model_connectedSpace

variable {m : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X]
  [IsComplexManifold (m + 1) X] [CompactSpace X] [ConnectedSpace X]

/-- **Dang–Favre's nef cone on a model is the nef cone**: for a numerical class `c ∈ N¹(Y)_ℝ` on a
model `Y` of a compact connected projective manifold, `cl(c)` is curve-nef iff it is nef. -/
theorem isCurveNef_numericalClass_iff_classNef
    (hX : SGPT.Trace.Bertini.IsProjectiveManifold (m + 1) X)
    (π : (ModelSystem.blowup (m + 1) X).Model) (κ : KahlerBackground (m + 1) π.1.carrier)
    (c : NumericalClasses m π.1.carrier) :
    IsCurveNef (numericalClassEquiv (blowup_model_isProjective hX π) c :
        RealBottChern (m + 1) π.1.carrier) ↔
      ClassNefWithRespectTo κ (numericalClassEquiv (blowup_model_isProjective hX π) c :
        RealBottChern (m + 1) π.1.carrier) :=
  Kleiman.isCurveNef_iff_classNef (blowup_model_isProjective hX π) κ
    (numericalClassEquiv (blowup_model_isProjective hX π) c).2

/-- **Dang–Favre nef Cartier classes give algebraic nef Cartier b-divisors**: if the Dang–Favre
Weil class `d` is determined on the model `π` by a numerical class `c` with `c · Γ ≥ 0` for
every curve `Γ`, then its image is realized on `π` by the nef class `cl(c) ∈ NS(Y_π)_ℝ`. -/
theorem isAlgNefCartierAny_of_dangFavreNefCartier
    (hX : SGPT.Trace.Bertini.IsProjectiveManifold (m + 1) X)
    (d : dangFavreWeilClasses hX) (π : (ModelSystem.blowup (m + 1) X).Model)
    (c : NumericalClasses m π.1.carrier) (hd : IsDeterminedOn hX d π c)
    (hc : IsCurveNef (numericalClassEquiv (blowup_model_isProjective hX π) c :
      RealBottChern (m + 1) π.1.carrier)) :
    IsAlgNefCartierAny (dangFavreWeilEquiv hX d).1 := by
  have hproj := blowup_model_isProjective hX π
  obtain ⟨ω, hK, -⟩ :=
    SGPT.BDivisor.NSKodaira.isProjectiveManifold_iff_exists_kahler_mem_neronSeveri.mp hproj
  refine ⟨π, _, (numericalClassEquiv hproj c).2,
    (isDeterminedOn_iff_isRealizationAny hX d π c).mp hd, ⟨ω, hK⟩, ?_⟩
  exact Kleiman.classNef_of_isCurveNef hproj ⟨ω, hK⟩ (numericalClassEquiv hproj c).2 hc

/-- **The algebraic nef Cartier b-divisors are exactly the images of Dang–Favre's nef Cartier
classes** (Kleiman's criterion for one direction, `exists_dangFavreNefCartier_of_isAlgNefCartierAny`
for the other). -/
theorem isAlgNefCartierAny_iff_exists_dangFavreNefCartier
    (hX : SGPT.Trace.Bertini.IsProjectiveManifold (m + 1) X)
    (C : WeilFamilyAny (ModelSystem.blowup (m + 1) X)) :
    IsAlgNefCartierAny C ↔
      ∃ (d : dangFavreWeilClasses hX) (π : (ModelSystem.blowup (m + 1) X).Model)
        (c : NumericalClasses m π.1.carrier),
        (dangFavreWeilEquiv hX d).1 = C ∧ IsDeterminedOn hX d π c ∧
          IsCurveNef (numericalClassEquiv (blowup_model_isProjective hX π) c :
            RealBottChern (m + 1) π.1.carrier) := by
  constructor
  · intro hC
    obtain ⟨d, π, c, hdC, hd, hc, -⟩ := exists_dangFavreNefCartier_of_isAlgNefCartierAny hX hC
    exact ⟨d, π, c, hdC, hd, hc⟩
  · rintro ⟨d, π, c, rfl, hd, hc⟩
    exact isAlgNefCartierAny_of_dangFavreNefCartier hX d π c hd hc

/-! ### Nef Weil classes -/

omit [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
  [CompactSpace X] [ConnectedSpace X] in
/-- **Euclidean convergence is detected by an injective linear map** (a linear functional on the
source extends along the map). -/
theorem tendsto_euclideanTopology_iff_of_injective {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] (L : V →ₗ[ℝ] W) (hL : Function.Injective L)
    {ι : Type*} {l : Filter ι} {x : ι → V} {y : V} :
    Tendsto x l (@nhds V (SGPT.BDivisor.euclideanTopology V) y) ↔
      Tendsto (fun i => L (x i)) l (@nhds W (SGPT.BDivisor.euclideanTopology W) (L y)) := by
  rw [SGPT.BDivisor.tendsto_euclideanTopology_iff, SGPT.BDivisor.tendsto_euclideanTopology_iff]
  constructor
  · intro h f
    exact h (f.comp L)
  · intro h g
    let e := LinearEquiv.ofInjective L hL
    obtain ⟨f, hf⟩ := LinearMap.exists_extend (g.comp e.symm.toLinearMap)
    have hfg : ∀ v, f (L v) = g v := by
      intro v
      have h1 := congrArg (fun φ : LinearMap.range L →ₗ[ℝ] ℝ => φ (e v)) hf
      simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearEquiv.coe_coe,
        LinearEquiv.symm_apply_apply] at h1
      rwa [LinearEquiv.ofInjective_apply] at h1
    have h2 := h f
    simp only [hfg] at h2
    exact h2

/-- The cycle class map of a model, `N¹(Y)_ℝ → H^{1,1}(Y, ℝ)`, as an injective linear map. -/
theorem injective_numericalClassMap (hX : SGPT.Trace.Bertini.IsProjectiveManifold (m + 1) X)
    (π : (ModelSystem.blowup (m + 1) X).Model) :
    Function.Injective ((neronSeveri (m + 1) π.1.carrier).subtype.comp
      (numericalClassEquiv (blowup_model_isProjective hX π)).toLinearMap) :=
  Subtype.val_injective.comp (numericalClassEquiv (blowup_model_isProjective hX π)).injective

/-- **Dang–Favre's nef Weil b-divisor classes**: the limits of nets of Dang–Favre nef Cartier
classes (determined on some model by a numerical class `c` with `c · Γ ≥ 0` for every curve), in
the projective-limit topology of the spaces `N¹(Y)_ℝ`, each with its Euclidean topology. -/
def IsDangFavreNef (hX : SGPT.Trace.Bertini.IsProjectiveManifold (m + 1) X)
    (d : dangFavreWeilClasses hX) : Prop :=
  ∃ (ι : Type 1) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι)
    (dn : ι → dangFavreWeilClasses hX),
    (∀ i, ∃ (π : (ModelSystem.blowup (m + 1) X).Model) (c : NumericalClasses m π.1.carrier),
      IsDeterminedOn hX (dn i) π c ∧
        IsCurveNef (numericalClassEquiv (blowup_model_isProjective hX π) c :
          RealBottChern (m + 1) π.1.carrier)) ∧
    ∀ π : (ModelSystem.blowup (m + 1) X).Model, Tendsto (fun i => (dn i).1 π) atTop
      (@nhds _ (SGPT.BDivisor.euclideanTopology (NumericalClasses m π.1.carrier)) (d.1 π))

/-- Convergence of Dang–Favre Weil classes is convergence of their images. -/
theorem tendsto_dangFavreWeil_iff (hX : SGPT.Trace.Bertini.IsProjectiveManifold (m + 1) X)
    {ι : Type*} {l : Filter ι} (dn : ι → dangFavreWeilClasses hX) (d : dangFavreWeilClasses hX)
    (π : (ModelSystem.blowup (m + 1) X).Model) :
    Tendsto (fun i => (dn i).1 π) l
        (@nhds _ (SGPT.BDivisor.euclideanTopology (NumericalClasses m π.1.carrier)) (d.1 π)) ↔
      Tendsto (fun i => (dangFavreWeilEquiv hX (dn i)).1.1 π) l
        (@nhds _ (SGPT.BDivisor.euclideanTopology (RealBottChern (m + 1) π.1.carrier))
          ((dangFavreWeilEquiv hX d).1.1 π)) :=
  tendsto_euclideanTopology_iff_of_injective _ (injective_numericalClassMap hX π)

/-- **Dang–Favre's nef classes are the algebraic nef b-divisors**: the image of a Dang–Favre Weil
class is an algebraic nef b-divisor (`IsAlgNefAny`) iff the class is nef in Dang–Favre's sense. -/
theorem isAlgNefAny_iff_isDangFavreNef
    (hX : SGPT.Trace.Bertini.IsProjectiveManifold (m + 1) X) (d : dangFavreWeilClasses hX) :
    IsAlgNefAny (dangFavreWeilEquiv hX d).1 ↔ IsDangFavreNef hX d := by
  constructor
  · rintro ⟨-, ι, hι, hdir, hne, Dn, hDn, hconv⟩
    choose dn π c hdC hdet hcn _hnef using
      fun i => exists_dangFavreNefCartier_of_isAlgNefCartierAny hX (hDn i)
    refine ⟨ι, hι, hdir, hne, dn, fun i => ⟨π i, c i, hdet i, hcn i⟩, fun ρ => ?_⟩
    rw [tendsto_dangFavreWeil_iff hX dn d ρ]
    have h := hconv ρ
    have hfun : (fun i => (Dn i).val ρ) = fun i => (dangFavreWeilEquiv hX (dn i)).1.1 ρ := by
      funext i
      rw [← hdC i]
    rw [hfun] at h
    exact h
  · rintro ⟨ι, hι, hdir, hne, dn, hdn, hconv⟩
    refine ⟨(dangFavreWeilEquiv hX d).2, ι, hι, hdir, hne,
      fun i => (dangFavreWeilEquiv hX (dn i)).1, fun i => ?_, fun ρ => ?_⟩
    · obtain ⟨π, c, hdet, hcn⟩ := hdn i
      exact isAlgNefCartierAny_of_dangFavreNefCartier hX (dn i) π c hdet hcn
    · exact (tendsto_dangFavreWeil_iff hX dn d ρ).mp (hconv ρ)

/-- **The algebraic nef b-divisors are exactly the images of Dang–Favre's nef classes.** -/
theorem isAlgNefAny_iff_exists_dangFavreNef
    (hX : SGPT.Trace.Bertini.IsProjectiveManifold (m + 1) X)
    (D : WeilFamilyAny (ModelSystem.blowup (m + 1) X)) :
    IsAlgNefAny D ↔ ∃ d : dangFavreWeilClasses hX, (dangFavreWeilEquiv hX d).1 = D ∧
      IsDangFavreNef hX d := by
  constructor
  · intro hD
    refine ⟨(dangFavreWeilEquiv hX).symm ⟨D, hD.1⟩, ?_, ?_⟩
    · rw [LinearEquiv.apply_symm_apply]
    · rw [← isAlgNefAny_iff_isDangFavreNef, LinearEquiv.apply_symm_apply]
      exact hD
  · rintro ⟨d, rfl, hd⟩
    exact (isAlgNefAny_iff_isDangFavreNef hX d).mpr hd

end SGPT.BDivisor.DFAlg
