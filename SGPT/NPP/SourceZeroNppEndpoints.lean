import SGPT.NPP.NonPluripolarCurrent3Currents

/-! Actual missing global0 source surface of prop:npp1: actual emptytuple
NPP well-definedness/current invariance/open restriction/arbitrary covers.
Full before-code blueprint is source-npp-zero:whole. Frozen105 unchanged. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.NPP.SourceZeroEndpointsDraft
open Set Filter
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.LocalProductCurrents
open SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorLocality
open SGPT.NPP.NonPluripolarCurrent
variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel 0) M]
  [IsManifold 𝓘(ℂ,ComplexModel 0) ∞ M]

/-- Genuine actual original global NPP well-definedness of the emptytuple. -/
theorem emptyTuple_wellDefined (φ : Fin 0 → M → EReal) :
    IsNonPluripolarWellDefined (q := 0) (p := 0) rfl φ := by
  let v : Fin 0 → M → ℝ := fun i => Fin.elim0 i
  have heq : φ = fun i x => ((v i x : ℝ) : EReal) := by
    funext i
    exact Fin.elim0 i
  rw [heq]
  exact isNonPluripolarWellDefined_of_isLocallyBoundedPSH rfl (fun i => Fin.elim0 i)

/-- Actual original global0 current-invariance/open-restriction/cover
endpoints. Actual well-definedness is internally produced, with literal
original currents, opens, chart domains and arbitrary original covers. -/
theorem sourceZeroNppEndpoints
    (φ ψ : Fin 0 → M → EReal)
    (hφ : ∀ i, SGPT.PSH.ManifoldPSH (n := 0) (φ i))
    (hψ : ∀ i, SGPT.PSH.ManifoldPSH (n := 0) (ψ i)) :
    let hWφ := emptyTuple_wellDefined φ
    let hWψ := emptyTuple_wellDefined ψ
    (IsNonPluripolarWellDefined (q := 0) (p := 0) rfl φ ↔
      IsNonPluripolarWellDefined (q := 0) (p := 0) rfl ψ) ∧
    (SGPT.NPP.nonPluripolarProduct rfl φ hφ hWφ =
      SGPT.NPP.nonPluripolarProduct rfl ψ hψ hWψ) ∧
    (∀ O : TopologicalSpace.Opens M,
      (∀ e : ComplexChart 0 M, IsWellDefinedOn (q := 0) (p := 0) rfl
        (chartDomain e O) (fun i z => φ i (e.val.symm z))) ∧
      ∀ e : ComplexChart 0 M,
        restrict (chartDomain_le e O) ((SGPT.NPP.nonPluripolarProduct rfl φ hφ hWφ).inChart e) =
          NonPluripolarCurrent.nonPluripolarProduct rfl (chartDomain e O)
            (fun i z => φ i (e.val.symm z))) ∧
    (∀ (𝒰 : Set (TopologicalSpace.Opens M)) (_h𝒰 : ∀ x : M, ∃ U ∈ 𝒰, x ∈ U),
      IsNonPluripolarWellDefined (q := 0) (p := 0) rfl φ ↔
        ∀ U ∈ 𝒰, ∀ e : ComplexChart 0 M, IsWellDefinedOn (q := 0) (p := 0) rfl
          (chartDomain e U) (fun i z => φ i (e.val.symm z))) := by
  dsimp only
  have heq : φ = ψ := Subsingleton.elim _ _
  refine ⟨?_,?_,?_,?_⟩
  · rw [heq]
  · subst ψ
    rfl
  · intro O
    exact ⟨fun e => isWellDefinedOn_restrict rfl (chartPlurisubharmonicOn hφ e)
        (emptyTuple_wellDefined φ e) (chartDomain_le e O),
      fun e => restrict_nonPluripolarProduct rfl (chartPlurisubharmonicOn hφ e)
        (emptyTuple_wellDefined φ e) (chartDomain_le e O)⟩
  · intro 𝒰 h𝒰
    constructor
    · intro hW U _ e
      exact isWellDefinedOn_restrict rfl (chartPlurisubharmonicOn hφ e) (hW e) (chartDomain_le e U)
    · intro h e
      refine isWellDefinedOn_of_cover rfl (chartPlurisubharmonicOn hφ e)
        (fun U : 𝒰 => chartDomain e U.1) (fun U => chartDomain_le e U.1) ?_
        (fun U => h U.1 U.2 e)
      intro z hz
      obtain ⟨U,hU,hzU⟩ := h𝒰 (e.val.symm z)
      exact mem_iUnion.mpr ⟨⟨U,hU⟩,hz,hzU⟩

end SGPT.NPP.SourceZeroEndpointsDraft
