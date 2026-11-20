import SGPT.Convex.Legendre
import Mathlib.Topology.Algebra.Module.PerfectPairing
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Source convex family operations

The actual rooftop is the lower convex envelope of the pointwise infimum.
The convex maximum is the pointwise supremum. Conjugation exchanges the
former with the supremum of the actual conjugates, including infinite values.
-/

namespace SGPT.Convex

open Set

variable {V W : Type*} [AddCommGroup V] [Module ℝ V]
  [AddCommGroup W] [Module ℝ W] {I : Sort*}

/-- The source convex rooftop of an actual indexed family. -/
noncomputable def convexInf (f : I → V → EReal) : V → EReal :=
  lowerConvexEnvelope (fun x ↦ ⨅ i, f i x)

/-- The source convex maximum of an actual indexed family. -/
noncomputable def convexSup (f : I → V → EReal) : V → EReal :=
  fun x ↦ ⨆ i, f i x

/-- The actual convex rooftop is convex, even for nonconvex obstacles. -/
theorem isConvex_convexInf (f : I → V → EReal) : IsConvex (convexInf f) :=
  isConvex_lowerConvexEnvelope _

/-- The actual convex rooftop lies below every member of its family. -/
theorem convexInf_le (f : I → V → EReal) (i : I) : convexInf f ≤ f i := by
  intro x
  exact (lowerConvexEnvelope_le _ x).trans (iInf_le (fun j ↦ f j x) i)

/-- Every actual convex common minorant lies below the convex rooftop. -/
theorem le_convexInf {f : I → V → EReal} {g : V → EReal}
    (hg : IsConvex g) (hgf : ∀ i, g ≤ f i) : g ≤ convexInf f :=
  le_lowerConvexEnvelope hg (fun x ↦ le_iInf fun i ↦ hgf i x)

/-- Finite-real subtraction sends arbitrary infima to suprema of differences. -/
theorem real_sub_iInf (a : ℝ) (b : I → EReal) :
    (a : EReal) - (⨅ i, b i) = ⨆ i, (a : EReal) - b i := by
  apply le_antisymm
  · apply (real_sub_le_iff_comm a _ _).mpr
    apply le_iInf
    intro i
    exact (real_sub_le_iff_comm a _ _).mpr (le_iSup (fun j ↦ (a : EReal) - b j) i)
  · exact iSup_le fun i ↦ EReal.sub_le_sub le_rfl (iInf_le b i)

/-- Conjugation sends an actual pointwise infimum to the supremum of conjugates. -/
theorem conjugate_iInf (B : V →ₗ[ℝ] W →ₗ[ℝ] ℝ) (f : I → V → EReal) :
    conjugate B (fun x ↦ ⨅ i, f i x) = convexSup (fun i ↦ conjugate B (f i)) := by
  funext y
  simp only [conjugate, convexSup, real_sub_iInf]
  exact iSup_comm

/-- The first equality of source `prop:Legendretranssup`, for arbitrary families. -/
theorem conjugate_convexInf (B : V →ₗ[ℝ] W →ₗ[ℝ] ℝ) (f : I → V → EReal) :
    conjugate B (convexInf f) = convexSup (fun i ↦ conjugate B (f i)) := by
  rw [convexInf, conjugate_lowerConvexEnvelope, conjugate_iInf]

section Topology

variable [TopologicalSpace V]

/-- The source closed classification implies lower semicontinuity in all cases. -/
theorem lowerSemicontinuous_of_isClosedConvex {f : V → EReal}
    (hf : IsClosedConvex f) : LowerSemicontinuous f := by
  rcases hf with h | h | h
  · rw [h]
    exact continuous_const.lowerSemicontinuous
  · rw [h]
    exact continuous_const.lowerSemicontinuous
  · exact h.2

/-- Actual suprema preserve the source closed classification, including constants. -/
theorem isClosedConvex_convexSup {f : I → V → EReal}
    (hf : ∀ i, IsClosedConvex (f i)) : IsClosedConvex (convexSup f) := by
  classical
  have hc : IsConvex (convexSup f) := isConvex_iSup fun i ↦ isConvex_of_isClosedConvex (hf i)
  have hlsc : LowerSemicontinuous (convexSup f) :=
    lowerSemicontinuous_iSup fun i ↦ lowerSemicontinuous_of_isClosedConvex (hf i)
  by_cases hbot : ∀ i, f i = (fun _ ↦ ⊥)
  · left
    funext x
    simp [convexSup, hbot]
  obtain ⟨i, hi⟩ := not_forall.mp hbot
  have hnobot : ∀ x, f i x ≠ ⊥ := by
    rcases hf i with h | h | h
    · exact False.elim (hi h)
    · simp [h]
    · exact h.1.2.2
  have hsup : ∀ x, convexSup f x ≠ ⊥ := by
    intro x
    exact ne_of_gt ((bot_lt_iff_ne_bot.mpr (hnobot x)).trans_le
      (le_iSup (fun j ↦ f j x) i))
  by_cases htop : convexSup f = (fun _ ↦ ⊤)
  · exact Or.inr (Or.inl htop)
  have hfinite : ∃ x, convexSup f x ≠ ⊤ := by
    by_contra h
    apply htop
    funext x
    by_contra hx
    exact h ⟨x, hx⟩
  obtain ⟨x, hx⟩ := hfinite
  exact Or.inr (Or.inr ⟨⟨hc, ⟨x, lt_top_iff_ne_top.mpr hx⟩, hsup⟩, hlsc⟩)

end Topology

section PerfectPairing

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

omit [FiniteDimensional ℝ F] in
/-- Transport full-dual biconjugation through a genuine continuous perfect pairing. -/
theorem biconjugate_eq_convexClosure_of_isContPerfPair
    (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [B.IsContPerfPair] {f : E → EReal} (hf : IsConvex f) :
    conjugate B.flip (conjugate B f) = convexClosure f := by
  let e : F ≃ₗ[ℝ] Module.Dual ℝ E := B.flip.toContPerfPair.trans
    (LinearMap.toContinuousLinearMap : Module.Dual ℝ E ≃ₗ[ℝ] StrongDual ℝ E).symm
  have hreindex : conjugate B.flip (conjugate B f) =
      conjugate (Module.Dual.eval ℝ E).flip (conjugate (Module.Dual.eval ℝ E) f) := by
    funext x
    let G : Module.Dual ℝ E → EReal := fun m ↦
      (m x : EReal) - conjugate (Module.Dual.eval ℝ E) f m
    change (⨆ y : F, G (e y)) = ⨆ m : Module.Dual ℝ E, G m
    exact e.toEquiv.iSup_comp
  rw [hreindex, biconjugate_eq_convexClosure hf]

/-- Actual bounded evaluation between a vector space and its normed continuous dual. -/
noncomputable def continuousDualPairing : E →ₗ[ℝ] StrongDual ℝ E →ₗ[ℝ] ℝ :=
  (ContinuousLinearMap.coeLM ℝ).comp
    (ContinuousLinearMap.apply ℝ ℝ : E →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] ℝ).toLinearMap

/-- The actual canonical evaluation pairing is perfect in finite dimension. -/
instance continuousDualPairing_isContPerfPair : (continuousDualPairing (E := E)).IsContPerfPair where
  continuous_uncurry :=
    (ContinuousLinearMap.apply ℝ ℝ : E →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] ℝ).continuous₂
  bijective_left := by
    let e : Module.Dual ℝ E ≃ₗ[ℝ] StrongDual ℝ E := LinearMap.toContinuousLinearMap
    let j : E ≃ₗ[ℝ] StrongDual ℝ (StrongDual ℝ E) :=
      ((Module.evalEquiv ℝ E).trans e.dualMap.symm).trans LinearMap.toContinuousLinearMap
    convert! j.bijective
  bijective_right := by
    convert! (Equiv.refl (StrongDual ℝ E)).bijective

/-- The unconditional second family identity, with actual source closure on both sides. -/
theorem conjugate_convexSup_convexClosure (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [B.IsContPerfPair]
    {f : I → E → EReal} (hf : ∀ i, IsConvex (f i)) :
    conjugate B (convexSup (fun i ↦ convexClosure (f i))) =
      convexClosure (convexInf (fun i ↦ conjugate B (f i))) := by
  have hfirst : conjugate B.flip (convexInf (fun i ↦ conjugate B (f i))) =
      convexSup (fun i ↦ convexClosure (f i)) := by
    rw [conjugate_convexInf]
    congr 1
    funext i
    exact biconjugate_eq_convexClosure_of_isContPerfPair B (hf i)
  rw [← hfirst]
  exact biconjugate_eq_convexClosure_of_isContPerfPair B.flip (isConvex_convexInf _)

/-- Source second equality with the genuine actual full dual evaluation pairing. -/
theorem conjugate_convexSup_convexClosure_dual {f : I → E → EReal}
    (hf : ∀ i, IsConvex (f i)) :
    conjugate continuousDualPairing (convexSup (fun i ↦ convexClosure (f i))) =
      convexClosure (convexInf (fun i ↦ conjugate continuousDualPairing (f i))) :=
  conjugate_convexSup_convexClosure continuousDualPairing hf

end PerfectPairing

end SGPT.Convex
