import SGPT.Toric.MonomialProjectiveOrbit
import SGPT.Foundations.Analysis.PSHD.ProjectiveTopology
import Mathlib.Analysis.Normed.Module.FiniteDimension

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set Metric Filter
open scoped Topology

variable {I : Type*} [Fintype I]
local notation "V" => I → ℂ
local notation "P" => Projectivization ℂ V
local notation "Vnz" => {v : V // v ≠ 0}

private def normalizeProjectiveVector (v : Vnz) : sphere (0 : V) 1 :=
  ⟨(‖v.val‖⁻¹ : ℂ) • v.val, by
    simp [norm_smul, norm_inv, Complex.norm_real, norm_ne_zero_iff.mpr v.property]⟩

private theorem continuous_normalizeProjectiveVector : Continuous (@normalizeProjectiveVector I _) := by
  have hc : Continuous (fun v : Vnz => (‖v.val‖⁻¹ : ℂ)) :=
    (Complex.continuous_ofReal.comp
      (continuous_subtype_val : Continuous (fun v : Vnz => v.val)).norm).inv₀
        (fun v => Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr v.property))
  exact (hc.smul continuous_subtype_val).subtype_mk _

private theorem hopf_normalizeProjectiveVector (v : Vnz) :
    SGPT.Foundations.Analysis.PSHD.hopf (normalizeProjectiveVector v) = Projectivization.mk' ℂ v := by
  change Projectivization.mk ℂ ((‖v.val‖⁻¹ : ℂ) • v.val) _ = Projectivization.mk ℂ v.val v.property
  exact (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr ⟨(‖v.val‖⁻¹ : ℂ), rfl⟩

/-- Actual unit normalization and inclusion identify the two genuine quotient
topologies. The already proved Hopf compactness/T2 mothers are not silently substituted. -/
theorem monomialProjectiveTopology_eq_hopf :
    monomialProjectiveTopology I = SGPT.Foundations.Analysis.PSHD.projectiveTopology (E := I → ℂ) := by
  apply le_antisymm
  · apply continuous_id_iff_le.mp
    apply continuous_coinduced_dom.mpr
    have hq : @Continuous Vnz P inferInstance
        (SGPT.Foundations.Analysis.PSHD.projectiveTopology (E := V)) (Projectivization.mk' ℂ) := by
      let : TopologicalSpace P := SGPT.Foundations.Analysis.PSHD.projectiveTopology
      exact ((SGPT.Foundations.Analysis.PSHD.continuous_hopf (E := V)).comp
        (continuous_normalizeProjectiveVector (I := I))).congr
          hopf_normalizeProjectiveVector
    exact hq
  · apply continuous_id_iff_le.mp
    apply continuous_coinduced_dom.mpr
    have hj : Continuous (fun v : sphere (0 : V) 1 =>
        (⟨v.val, by
          have hv : ‖v.val‖ = 1 := by simp
          intro h
          simp [h] at hv⟩ : Vnz)) := continuous_subtype_val.subtype_mk _
    exact continuous_quotient_mk'.comp hj

/-- Existing genuine Hopf compactness transports to the original nonzero-vector quotient. -/
theorem monomialProjectiveCompactSpace :
    @CompactSpace (Projectivization ℂ (I → ℂ)) (monomialProjectiveTopology I) := by
  rw [monomialProjectiveTopology_eq_hopf]
  exact SGPT.Foundations.Analysis.PSHD.projectiveCompactSpace

/-- Existing closed-phase/open-Hopf Hausdorffness transports to that SAME original quotient. -/
theorem monomialProjectiveT2Space :
    @T2Space (Projectivization ℂ (I → ℂ)) (monomialProjectiveTopology I) := by
  rw [monomialProjectiveTopology_eq_hopf]
  exact SGPT.Foundations.Analysis.PSHD.projectiveT2Space

attribute [local instance] monomialProjectiveTopology
variable {n : ℕ} [Nonempty I]

/-- The literal monomial orbit closure is genuinely compact in the original quotient topology. -/
theorem isCompact_monomialProjectiveOrbitClosure (β : I → Fin n → ℤ) :
    IsCompact (monomialProjectiveOrbitClosure β) := by
  let : CompactSpace P := monomialProjectiveCompactSpace (I := I)
  exact isClosed_closure.isCompact

/-- Actual compactness of the same original orbit-closure subtype. -/
theorem compactSpace_monomialProjectiveOrbitClosure (β : I → Fin n → ℤ) :
    CompactSpace (monomialProjectiveOrbitClosure β) :=
  isCompact_iff_compactSpace.mp (isCompact_monomialProjectiveOrbitClosure β)

/-- Actual Hausdorffness of the same original orbit-closure subtype. -/
theorem t2Space_monomialProjectiveOrbitClosure (β : I → Fin n → ℤ) :
    T2Space (monomialProjectiveOrbitClosure β) := by
  let : T2Space P := monomialProjectiveT2Space (I := I)
  infer_instance

end SGPT.Toric
