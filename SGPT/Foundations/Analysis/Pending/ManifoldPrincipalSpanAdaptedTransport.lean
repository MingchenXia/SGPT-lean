import SGPT.Foundations.Analysis.Pending.ManifoldFiniteSpanChartTransport

set_option autoImplicit false

/-! # The complete original principal stalk for every literal adapted test function -/

open Set Filter
open scoped Topology Manifold

namespace SGPT.Foundations.Analysis.Pending.ManifoldPrincipalSpanAdaptedTransport

open FirstPass FirstPass.HolomorphicIdealSheaves

noncomputable section

/-- All literal adapted tests, not only given manifold tests, retain the complete principal stalk. -/
theorem full_principal_generation_comp_adapted {n s : ℕ} {M : Type*}
    [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    (x : M) (Φ : LocalHolomorphicEquivAt (n := n) ((chartAt (ComplexModel n) x) x))
    (hsrc : Φ.source ⊆ (chartAt (ComplexModel n) x).target)
    (h0 : Φ.toFun ((chartAt (ComplexModel n) x) x) = 0)
    (G : Fin s → M → ℂ) (H : M → ℂ)
    (hfull : ∀ F : M → ℂ, IsInSpanAt (n := n) (· ∈ Set.range G) x F ↔
      IsInSpanAt (n := n) (· = H) x F) :
    ∀ F : ComplexModel n → ℂ,
      IsInSpanAt (n := n) (· ∈ Set.range fun i z =>
        G i ((chartAt (ComplexModel n) x).symm (Φ.invFun z))) (0 : ComplexModel n) F ↔
      IsInSpanAt (n := n)
        (· = fun z => H ((chartAt (ComplexModel n) x).symm (Φ.invFun z)))
        (0 : ComplexModel n) F := by
  classical
  let e := chartAt (ComplexModel n) x
  let T : ComplexModel n → M := fun z => e.symm (Φ.invFun z)
  let R : M → ComplexModel n := fun y => Φ.toFun (e y)
  have h0t : (0 : ComplexModel n) ∈ Φ.target := by
    rw [← h0]
    exact Φ.mapsTo_toFun Φ.center_mem_source
  have hRT : (fun z => R (T z)) =ᶠ[𝓝 (0 : ComplexModel n)] id := by
    filter_upwards [Φ.isOpen_target.mem_nhds h0t] with z hz
    dsimp only [R, T, id]
    rw [e.right_inv (hsrc (Φ.mapsTo_invFun hz)), Φ.right_inv z hz]
  intro F
  let FM : M → ℂ := fun y => F (R y)
  have hround : (fun z => FM (T z)) =ᶠ[𝓝 (0 : ComplexModel n)] F :=
    hRT.mono fun z hz => congrArg F hz
  have hG := ManifoldFiniteSpanChartTransport.isInSpanAt_comp_adapted_iff x Φ h0 G FM
  have hH : IsInSpanAt (n := n) (· = H) x FM ↔
      IsInSpanAt (n := n) (· = fun z => H (T z)) (0 : ComplexModel n)
        (fun z => FM (T z)) := by
    have h := ManifoldFiniteSpanChartTransport.isInSpanAt_comp_adapted_iff x Φ h0
      (fun _ : Fin 1 => H) FM
    simpa only [Set.range_const, Set.mem_singleton_iff] using h
  constructor
  · intro hf
    have hGM : IsInSpanAt (n := n) (· ∈ Set.range G) x FM :=
      hG.mpr (CoherentIdealColon.isInSpanAt_range_congr
        (fun _ => EventuallyEq.rfl) hround.symm hf)
    have hHT := hH.mp ((hfull FM).mp hGM)
    exact InvertibleIdealQuotient.IsInSpanAt.congr' hHT hround
  · intro hf
    have hHM : IsInSpanAt (n := n) (· = H) x FM :=
      hH.mpr (InvertibleIdealQuotient.IsInSpanAt.congr' hf hround.symm)
    have hGT := hG.mp ((hfull FM).mpr hHM)
    exact CoherentIdealColon.isInSpanAt_range_congr
      (fun _ => EventuallyEq.rfl) hround hGT

end
end SGPT.Foundations.Analysis.Pending.ManifoldPrincipalSpanAdaptedTransport
