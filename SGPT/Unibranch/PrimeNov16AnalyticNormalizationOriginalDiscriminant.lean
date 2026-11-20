import SGPT.Foundations.Analysis.Pending.IrreducibleGermConnected

/-! Actual retained Noether discriminant in the original analytic coordinates.
Blueprint: prime-nov16-analytic-normalization-original-discriminant.tex. -/
set_option autoImplicit false
noncomputable section
open Set Filter Metric
open scoped Topology
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalDiscriminant
open AnalyticGermDecomposition GermParametrization HolGerm GermAlgebraicParametrization RegularLocusDense

theorem exists_original_regular_discriminant {n : ℕ} {Z : Set (ComplexModel n)}
    (hZ : IsIrreducibleGerm Z) {N : Set (ComplexModel n)} (hN : N ∈ 𝓝 0) :
    ∃ (d : ℕ) (Δ : Set (ComplexModel n)) (D : ComplexModel n → ℂ),
      IsOpen Δ ∧ (0 : ComplexModel n) ∈ Δ ∧ Z ∩ Δ ⊆ N ∧
      (∀ᶠ z in 𝓝 0,DifferentiableAt ℂ D z) ∧
      (¬ ∀ᶠ z in 𝓝 0,z ∈ Z → D z=0) ∧
      (∀ z ∈ Z ∩ Δ,DifferentiableAt ℂ D z) ∧
      Z ∩ Δ ⊆ closure ((Z ∩ Δ) ∩ {z | D z ≠ 0}) ∧
      ∀ z ∈ Z ∩ Δ,D z ≠ 0 → RegularAtDim (n := n) (Z ∩ Δ) z d := by
  have hprime : (vanishingIdeal Z).IsPrime := (isIrreducibleGerm_iff_isPrime hZ.1).1 hZ
  obtain ⟨d₀,L,hNN⟩ := exists_isNoetherNormalization (vanishingIdeal Z)
  rw [map_vanishingIdeal_comapEquiv] at hNN
  have : (vanishingIdeal (L ⁻¹' Z)).IsPrime := by
    rw [← map_vanishingIdeal_comapEquiv]
    exact Ideal.map_isPrime_of_equiv _
  obtain ⟨AP⟩ := exists_algebraicParametrization hNN
  obtain ⟨P⟩ := GermParametrizationData.nonempty_parametrizationData
    (isAnalyticGerm_preimage L hZ.1) AP
  obtain ⟨S⟩ := GermParametrizationData.nonempty_setsData P
  let T : ComplexModel n → ComplexModel P.dim := fun z => coordinateProjection n P.dim (L.symm z)
  let D : ComplexModel n → ℂ := fun z => P.disc (T z)
  have hTd : Differentiable ℂ T := (coordinateProjection n P.dim).differentiable.comp L.symm.differentiable
  have hT0 : Tendsto T (𝓝 0) (𝓝 0) := by
    simpa only [T,map_zero] using hTd.continuous.tendsto (0 : ComplexModel n)
  have hDb : ∀ᶠ z in 𝓝 (0 : ComplexModel P.dim),DifferentiableAt ℂ P.disc z :=
    eventually_of_mem (ball_mem_nhds 0 P.rad_pos) fun z hz =>
      P.differentiableOn_disc.differentiableAt (isOpen_ball.mem_nhds hz)
  have hD : ∀ᶠ z in 𝓝 0,DifferentiableAt ℂ D z := by
    filter_upwards [hT0.eventually hDb] with z hz
    exact hz.comp z (hTd z)
  have hDn : ¬ ∀ᶠ z in 𝓝 0,z ∈ Z → D z=0 := by
    intro hz
    apply P.disc_not_eventually_zero
    apply P.base P.disc hDb
    filter_upwards [(tendsto_linearEquiv_nhds_zero L).eventually hz] with z hz hzZ
    simpa only [D,T,ContinuousLinearEquiv.symm_apply_apply] using hz hzZ
  let N' : Set (ComplexModel n) := L ⁻¹' N ∩
    {z | coordinateProjection n P.dim z ∈ ball (0 : ComplexModel P.dim) P.rad}
  have hp0 : Tendsto (coordinateProjection n P.dim) (𝓝 0) (𝓝 0) := by
    simpa only [map_zero] using (coordinateProjection n P.dim).continuous.tendsto (0 : ComplexModel n)
  have hN' : N' ∈ 𝓝 0 := inter_mem (tendsto_linearEquiv_nhds_zero L hN)
    (hp0.eventually (ball_mem_nhds (0 : ComplexModel P.dim) P.rad_pos))
  obtain ⟨Δ,hΔo,hΔ0,hΔN,_hc,hdense,hreg⟩ :=
    GermParametrizationData.exists_isPreconnected_regularPart P S
      (eventually_differentiableAt_const 1) (by simpa using NeBot.ne (nhds_neBot (x := (0 : ComplexModel P.dim)))) hN'
  let Ω : Set (ComplexModel n) := L.symm ⁻¹' Δ
  have hset : L.symm ⁻¹' (L ⁻¹' Z ∩ Δ) = Z ∩ Ω := by ext z; simp [Ω]
  refine ⟨P.dim,Ω,D,hΔo.preimage L.symm.continuous,by simpa [Ω] using hΔ0,?_,hD,hDn,?_,?_,?_⟩
  · rintro z ⟨hzZ,hzΩ⟩
    have hz := hΔN ⟨by simpa using hzZ,hzΩ⟩
    simpa using hz.1
  · rintro z ⟨hzZ,hzΩ⟩
    have hz := hΔN ⟨by simpa using hzZ,hzΩ⟩
    exact (P.differentiableOn_disc.differentiableAt (isOpen_ball.mem_nhds hz.2)).comp z (hTd z)
  · rintro z ⟨hzZ,hzΩ⟩
    have hz := hdense ⟨by simpa using hzZ,hzΩ⟩
    have he := L.symm.toHomeomorph.preimage_closure
      ((L ⁻¹' Z ∩ Δ) ∩ coordinateProjection n P.dim ⁻¹' {x | P.disc x * 1 ≠ 0})
    have hz' : z ∈ L.symm ⁻¹' closure
        ((L ⁻¹' Z ∩ Δ) ∩ coordinateProjection n P.dim ⁻¹' {x | P.disc x * 1 ≠ 0}) := hz
    have hz'' : z ∈ closure (L.symm.toHomeomorph ⁻¹'
        ((L ⁻¹' Z ∩ Δ) ∩ coordinateProjection n P.dim ⁻¹' {x | P.disc x * 1 ≠ 0})) := he ▸ hz'
    convert hz'' using 1
    congr 1
    ext u
    simp [D,T,Ω]
  · rintro z ⟨hzZ,hzΩ⟩ hzD
    have hr := regularAtDim_preimage_linearEquiv L.symm
      (hreg (L.symm z) ⟨by simpa using hzZ,hzΩ⟩ (by simpa [D,T] using hzD))
    rwa [hset] at hr

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalDiscriminant
