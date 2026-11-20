import SGPT.Okounkov.NativeFirstFlagGermDivision
import SGPT.Foundations.Analysis.Pending.AnalyticTypeRestriction

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov

open Set Filter
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending

/-- Actual original flattening-chart extension makes the literal original
tail restriction surjective. No extension or lift certificate is supplied. -/
theorem originalFirstFlagGermRestriction_surjective {m : ℕ}
    (F : OriginalFlagGeometry.{u} (m + 1)) (x : F.tail.carrier) :
    Function.Surjective (originalFirstFlagGermRestriction F x) := by
  intro g
  obtain ⟨f, hf, rfl⟩ := NativeHolGerm.exists_eq_mk g
  obtain ⟨G, hG, hres⟩ := AnalyticTypeRestriction.exists_holomorphicAt_extension
    (n := m + 1) (k := m) (X := F.carrier) (W := F.flag (1 : Fin (m + 2)))
    (Nat.le_succ m) F.firstDivisor.2.2 x f hf
  refine ⟨NativeHolGerm.mk G hG, ?_⟩
  rw [Subtype.ext_iff]
  change ((fun y : F.tail.carrier => G y.1) : Germ (𝓝 x) ℂ) = (f : Germ (𝓝 x) ℂ)
  exact Germ.coe_eq.mpr hres

namespace NativeHolGerm

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel 0) M]
  [IsComplexManifold 0 M] {x : M}

/-- Actual centered original charts and the singleton model `ℂ^0` prove
injectivity of original evaluation; no residue-field dictionary is assumed. -/
theorem zeroDimensionEval_injective :
    Function.Injective (eval : NativeHolGerm 0 M x →+* ℂ) := by
  intro g h heq
  apply (chartEquiv x).injective
  have hzero : HolGerm.eval (chartEquiv x g) = HolGerm.eval (chartEquiv x h) := by
    simpa only [eval_chartEquiv] using heq
  generalize chartEquiv x g = a at hzero ⊢
  generalize chartEquiv x h = b at hzero ⊢
  obtain ⟨f, hf, rfl⟩ := HolGerm.exists_eq_mk a
  obtain ⟨q, hq, rfl⟩ := HolGerm.exists_eq_mk b
  apply HolGerm.mk_eq_mk_iff.mpr
  exact Eventually.of_forall fun z => by
    have hz : z = (0 : ComplexModel 0) := Subsingleton.elim _ _
    simpa only [hz, HolGerm.eval_mk] using hzero

/-- The actual zero-dimensional original local ring is `ℂ`, through the
literal original evaluation homomorphism. -/
def zeroDimensionEquiv (x : M) : NativeHolGerm 0 M x ≃+* ℂ :=
  RingEquiv.ofBijective eval ⟨zeroDimensionEval_injective, fun c =>
    ⟨constHom c, rfl⟩⟩

theorem zeroDimensionEquiv_apply (g : NativeHolGerm 0 M x) :
    zeroDimensionEquiv x g = eval g :=
  rfl

end NativeHolGerm

/-- The curve flag's final literal original restriction, followed by the
actual zero-dimensional ring equivalence, is the whole original evaluation
map. This is a geometric residue readback, with no rank/value premise. -/
theorem originalCurveFlagGermRestriction_eq_eval
    (F : OriginalFlagGeometry.{u} 1) (x : F.tail.carrier) :
    (NativeHolGerm.zeroDimensionEquiv x).toRingHom.comp
      (originalFirstFlagGermRestriction F x) = NativeHolGerm.eval := by
  ext g
  obtain ⟨f, hf, rfl⟩ := NativeHolGerm.exists_eq_mk g
  rfl

end SGPT.Okounkov
