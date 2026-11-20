import SGPT.Projective.OkoNov16OriginalVeroneseInftyTransport
import SGPT.Okounkov.AlgebraicValuationBodies

/-! Blueprint first: oko-nov16-original-infty-veronese-carrier.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Okounkov.OkoNov16
open SGPT.Okounkov.AlgebraicValuation
open Set Filter CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.NAPotential.GAGAMult SGPT.GAGA.H0L SGPT.PSH
open scoped Topology
variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  (J : ClosedProjectiveEmbedding f) [SmoothOfRelativeDimension n f]
  [IsSeparated f] [QuasiCompact f]
local instance inftyVeroneseCarrierTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance inftyVeroneseCarrierCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance inftyVeroneseCarrierManifold : IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n

omit [IsSeparated f] [QuasiCompact f] in
theorem original_inftySectionSet_veronese_iff [IsIntegral X]
    (v : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ)))) (c : X)
    (hc : IsNonnegAt v c) {L : X.Modules} (a : LineBundleAtlas L)
    (u : SchemeComplexPoint f → EReal) {r : ℕ} (hr : 0<r)
    (x : Fin n → ℤ) (j : ℤ) :
    (x,j)∈AlgebraicValuation.inftySectionSet f n J v c (a.tensorPower r) (fun y => (r:EReal)*u y) ↔
      (x,(r:ℤ)*j)∈AlgebraicValuation.inftySectionSet f n J v c a u := by
  let := J.isSeparated
  let := J.quasiCompact
  constructor
  · rintro ⟨k,s,hs,hInf,hz⟩
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj hz
    let Φ := nativeLineTensorPowerMulIso a r k
    let t := Φ.inv.val.app (Opposite.op ⊤) s
    have hst : Φ.hom.val.app (Opposite.op ⊤) t=s :=
      congrArg (fun α => α.val.app (Opposite.op ⊤) s) Φ.inv_hom_id
    have ht : t≠0 := by
      intro h0
      apply hs
      rw [←hst,h0,map_zero]
    have hInfT : IsInftySection f n J u (r*k) t := by
      apply (original_veronesePower_isInfty_iff f n J a r k t u).mp
      rw [hst]
      exact hInf
    refine ⟨r*k,t,ht,hInfT,?_⟩
    have hv := sectionValue_tensorPowerMulIso hc a r k t
    rw [hst] at hv
    rw [sectionVector_eq_of_value_eq c c _ _ _ _ s t hs ht hv]
    push_cast
    rfl
  · rintro ⟨k',t,ht,hInf,hz⟩
    obtain ⟨hx,hj⟩ := Prod.mk.inj hz
    have hj0 : 0≤j := by
      have h : (0:ℤ)≤(r:ℤ)*j := by rw [hj]; exact Int.natCast_nonneg _
      have hr' : (0:ℤ)<r := by exact_mod_cast hr
      nlinarith
    lift j to ℕ using hj0
    have hk : k'=r*j := by exact_mod_cast hj.symm
    subst hk hx
    let Φ := nativeLineTensorPowerMulIso a r j
    have hΦt : Φ.hom.val.app (Opposite.op ⊤) t≠0 := by
      intro h0
      apply ht
      have hh := congrArg (fun α => α.val.app (Opposite.op ⊤) t) Φ.hom_inv_id
      change Φ.inv.val.app (Opposite.op ⊤) (Φ.hom.val.app (Opposite.op ⊤) t)=t at hh
      rw [←hh,h0,map_zero]
    refine ⟨j,Φ.hom.val.app (Opposite.op ⊤) t,hΦt,?_,?_⟩
    · exact (original_veronesePower_isInfty_iff f n J a r j t u).mpr hInf
    · rw [sectionVector_eq_of_value_eq c c _ _ _ _ _ t hΦt ht
        (sectionValue_tensorPowerMulIso hc a r j t)]
end SGPT.Okounkov.OkoNov16
