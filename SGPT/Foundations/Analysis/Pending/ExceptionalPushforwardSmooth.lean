import SGPT.Foundations.Analysis.Pending.RegularPatchPushforward
import SGPT.Foundations.Analysis.Pending.ExceptionalPushforwardPotential

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

/-!
# The pushed-down potential is smooth where the pulled-back one is

`Pending.ExceptionalPushforwardPotential` produces `ψ` downstairs with `ψ ∘ g = u - h_Z +
ε₀ψ_E` off `Exc g`, and the right-hand side is smooth in charts at a point off `Exc g` and
off the poles.  CT22's density comparison reads `ddᶜψ` in a chart of `Y`, and the chain
rule of `Pending.RegularPatchPushforward` transports `ddᶜ` only of a function that is
SMOOTH near the DOWNSTAIRS point.  This module supplies exactly that: at a non-exceptional
`z` the chart expression of `g` is a local biholomorphism, so the smooth germ of `ψ ∘ g`
upstairs becomes a smooth germ of `ψ` downstairs, by precomposition with its holomorphic
inverse.

No positivity, no analytic singularities and no manifold-level local inverse of `g`: this
is the coordinate statement that a local biholomorphism transports smooth germs.
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace SGPT.Foundations.Analysis.Pending.ExceptionalPushforwardSmooth

open FirstPass FirstPass.BlowupSequences FirstPass.HolomorphicMaps

noncomputable section

variable {n : ℕ} {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y]
  {Z : Type u} [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z]

/-- **A local biholomorphism carries a smooth germ downwards.**  If the chart expression of
`ψ ∘ g` at a non-exceptional `z` is smooth near `e z`, then the chart expression of `ψ` in
any chart at `g z` is smooth near `φ (g z)`. -/
theorem eventually_contDiffAt_chartFunction_of_comp
    {g : Z → Y} (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g)
    {psi : Y → EReal} {z : Z} (hz : z ∉ exceptionalLocus n g)
    (e : ComplexChart n Z) (hze : z ∈ e.val.source)
    (hw : ∀ᶠ ζ in 𝓝 (e.val z),
      ContDiffAt ℝ ∞ (fun ζ' => (psi (g (e.val.symm ζ'))).toReal) ζ)
    (d : ComplexChart n Y) (hgz : g z ∈ d.val.source) :
    ∀ᶠ y in 𝓝 (d.val (g z)),
      ContDiffAt ℝ ∞ (fun y' => (psi (d.val.symm y')).toReal) y := by
  classical
  set ζ₀ : ComplexModel n := e.val z with hζ₀
  set F : ComplexModel n → ComplexModel n := fun ζ => d.val (g (e.val.symm ζ)) with hF
  set D : Set (ComplexModel n) := coordinateDomain g e d with hD
  have hDopen : IsOpen D := coordinateDomain_isOpen hg e d
  have hesymm : e.val.symm ζ₀ = z := e.val.left_inv hze
  have hζ₀D : ζ₀ ∈ D := ⟨e.val.map_source hze, by
    show g (e.val.symm ζ₀) ∈ d.val.source
    rw [hesymm]; exact hgz⟩
  have hFdiff : DifferentiableOn ℂ F D :=
    (coordinateMap_contDiffOn hg e d).differentiableOn (by simp)
  have hinj := RegularPatchPushforward.injective_fderiv_chartExpr' hg hz e hze d hgz
  obtain ⟨Ψ, hΨD, hΨF, -⟩ := exists_localHolomorphicEquivAt hDopen hζ₀D hFdiff hinj
  have hΨc : Ψ.toFun ζ₀ = d.val (g z) := by rw [hΨF, hF]; simp [hesymm]
  have htgt : d.val (g z) ∈ Ψ.target := by
    rw [← hΨc]; exact Ψ.mapsTo_toFun Ψ.center_mem_source
  have hinvc : Ψ.invFun (d.val (g z)) = ζ₀ := by
    rw [← hΨc]; exact Ψ.left_inv _ Ψ.center_mem_source
  obtain ⟨S₀, hS₀sub, hS₀open, hS₀mem⟩ := mem_nhds_iff.mp hw
  set S : Set (ComplexModel n) := Ψ.source ∩ S₀ with hS
  have hSopen : IsOpen S := Ψ.isOpen_source.inter hS₀open
  have hζ₀S : ζ₀ ∈ S := ⟨Ψ.center_mem_source, hS₀mem⟩
  set N : Set (ComplexModel n) := Ψ.target ∩ Ψ.invFun ⁻¹' S with hN
  have hinvcont : ContinuousOn Ψ.invFun Ψ.target := Ψ.invFun_holomorphic.continuousOn
  have hNopen : IsOpen N := hinvcont.isOpen_inter_preimage Ψ.isOpen_target hSopen
  have hNmem : d.val (g z) ∈ N := ⟨htgt, by rw [mem_preimage, hinvc]; exact hζ₀S⟩
  -- on `N` the chart expression of `ψ` is that of `ψ ∘ g`, precomposed with `Ψ⁻¹`
  have hEq : EqOn (fun y' => (psi (d.val.symm y')).toReal)
      (fun y' => (psi (g (e.val.symm (Ψ.invFun y')))).toReal) N := by
    intro y hy
    show (psi (d.val.symm y)).toReal = (psi (g (e.val.symm (Ψ.invFun y)))).toReal
    have hζD : Ψ.invFun y ∈ D := hΨD hy.2.1
    have hFζ : F (Ψ.invFun y) = y := by rw [← hΨF]; exact Ψ.right_inv y hy.1
    have hgsrc : g (e.val.symm (Ψ.invFun y)) ∈ d.val.source := hζD.2
    have h1 : d.val (g (e.val.symm (Ψ.invFun y))) = y := hFζ
    have hdsymm : d.val.symm y = g (e.val.symm (Ψ.invFun y)) := by
      conv_lhs => rw [← h1]
      exact d.val.left_inv hgsrc
    rw [hdsymm]
  have hsmooth : ∀ y ∈ N,
      ContDiffAt ℝ ∞ (fun y' => (psi (g (e.val.symm (Ψ.invFun y')))).toReal) y := by
    intro y hy
    have hinvC : ContDiffAt ℝ ∞ Ψ.invFun y :=
      (((contDiffOn_of_differentiableOn_complex Ψ.invFun_holomorphic
        Ψ.isOpen_target).restrict_scalars ℝ) y hy.1).contDiffAt
          (Ψ.isOpen_target.mem_nhds hy.1)
    have hc : ContDiffAt ℝ ∞ (fun ζ' => (psi (g (e.val.symm ζ'))).toReal) (Ψ.invFun y) :=
      hS₀sub hy.2.2
    exact hc.comp y hinvC
  filter_upwards [hNopen.mem_nhds hNmem] with y hy
  exact (hsmooth y hy).congr_of_eventuallyEq
    (Filter.eventuallyEq_of_mem (hNopen.mem_nhds hy) hEq)

end

end SGPT.Foundations.Analysis.Pending.ExceptionalPushforwardSmooth
