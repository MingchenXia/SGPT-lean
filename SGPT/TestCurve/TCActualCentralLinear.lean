import SGPT.TestCurve.TCActualCentralSections

/-! Complex linearity of the ACTUAL geometric central H0 point maps.
Their underlying function remains the genuine Cech-glued native action. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.TestCurve.CentralFiber
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry SGPT.Foundations.Schemes Opposite
open SGPT.LineBundle SGPT.TestCurve.TCEnc SGPT.TestCurve.TCLin SGPT.TestCurve.GeomLin

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} {L : X.Modules}
  {a : LineBundleAtlas L} (T : TestConfiguration f a) (Λ : GeomLinearization T)

private theorem centralPatch_ext (c : ℂˣ) (m : ℕ) (u v : centralFiberSectionSpace T m)
    (h : ∀ i j : T.atlas.I,
      (centralFiberScheme T).presheaf.map (homOfLE (inf_le_right :
        pullOpen (centralActionAtlas T) (centralActionAtlas T) (centralActAt T Λ.action c) i j ≤
          (centralActionAtlas T).opens j)).op
        (atlasPowerGlobalCoefficients (centralActionAtlas T) m j u) =
      (centralFiberScheme T).presheaf.map (homOfLE (inf_le_right :
        pullOpen (centralActionAtlas T) (centralActionAtlas T) (centralActAt T Λ.action c) i j ≤
          (centralActionAtlas T).opens j)).op
        (atlasPowerGlobalCoefficients (centralActionAtlas T) m j v)) : u = v := by
  apply TopCat.Presheaf.IsSheaf.section_ext
    (F := (bundleTensorPower (centralFiberLine T) m).val.presheaf)
    (bundleTensorPower (centralFiberLine T) m).isSheaf
  intro x _hx
  obtain ⟨i,hi⟩ := (centralActionAtlas T).covers (centralActAt T Λ.action c x)
  obtain ⟨j,hj⟩ := (centralActionAtlas T).covers x
  refine ⟨pullOpen (centralActionAtlas T) (centralActionAtlas T) (centralActAt T Λ.action c) i j,
    le_top,⟨hi,hj⟩,?_⟩
  apply ((((centralActionAtlas T).frame j).tensorPower m).coefficients (homOfLE inf_le_right)).injective
  have hu := LocalBundleFrame.global_coefficients_restrict ((centralActionAtlas T).frame j) m
    (homOfLE (inf_le_right :
      pullOpen (centralActionAtlas T) (centralActionAtlas T) (centralActAt T Λ.action c) i j ≤
        (centralActionAtlas T).opens j)) u
  have hv := LocalBundleFrame.global_coefficients_restrict ((centralActionAtlas T).frame j) m
    (homOfLE (inf_le_right :
      pullOpen (centralActionAtlas T) (centralActionAtlas T) (centralActAt T Λ.action c) i j ≤
        (centralActionAtlas T).opens j)) v
  exact hu.trans ((h i j).trans hv.symm)

private theorem centralActAt_global_constants (c : ℂˣ) (b : ℂ) :
    (centralActAt T Λ.action c).appTop (schemeGlobalConstants (centralFiberStructureMap T) b) =
      schemeGlobalConstants (centralFiberStructureMap T) b := by
  have h := congrArg (fun g => schemeGlobalConstants g b) (centralActAt_over_base T Λ.action c)
  exact h

private theorem centralActAt_local_constants (c : ℂˣ) (b : ℂ)
    (U V : (centralFiberScheme T).Opens) (e : V ≤ centralActAt T Λ.action c ⁻¹ᵁ U) :
    (centralActAt T Λ.action c).appLE U V e
      ((centralFiberScheme T).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
        (schemeGlobalConstants (centralFiberStructureMap T) b)) =
      (centralFiberScheme T).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op
        (schemeGlobalConstants (centralFiberStructureMap T) b) := by
  rw [appLE_of_res]
  have hh := appLE_res (centralActAt T Λ.action c)
    (le_preimage_top (centralActAt T Λ.action c) ⊤) (le_top : V ≤ ⊤)
    (schemeGlobalConstants (centralFiberStructureMap T) b)
  have htop : (centralActAt T Λ.action c).appLE ⊤ ⊤
      (le_preimage_top (centralActAt T Λ.action c) ⊤) = (centralActAt T Λ.action c).appTop :=
    (Scheme.Hom.app_eq_appLE (centralActAt T Λ.action c) (U := ⊤)).symm
  rw [htop,centralActAt_global_constants] at hh
  exact hh.symm

private def targetCoefficient (c : ℂˣ) (m : ℕ) (i j : T.atlas.I) :
    centralFiberSectionSpace T m →+
      Γ(centralFiberScheme T,
        pullOpen (centralActionAtlas T) (centralActionAtlas T) (centralActAt T Λ.action c) i j) :=
  ((centralFiberScheme T).presheaf.map (homOfLE (inf_le_right :
    pullOpen (centralActionAtlas T) (centralActionAtlas T) (centralActAt T Λ.action c) i j ≤
      (centralActionAtlas T).opens j)).op).hom.toAddMonoidHom.comp
    (coeffHom (centralActionAtlas T) m j)

private def sourceCoefficient (c : ℂˣ) (m : ℕ) (i j : T.atlas.I) :
    centralFiberSectionSpace T m →+
      Γ(centralFiberScheme T,
        pullOpen (centralActionAtlas T) (centralActionAtlas T) (centralActAt T Λ.action c) i j) :=
  ((centralActAt T Λ.action c).appLE ((centralActionAtlas T).opens i)
    (pullOpen (centralActionAtlas T) (centralActionAtlas T) (centralActAt T Λ.action c) i j)
      inf_le_left).hom.toAddMonoidHom.comp (coeffHom (centralActionAtlas T) m i)

private theorem coefficient_act (c : ℂˣ) (m : ℕ) (i j : T.atlas.I)
    (u : centralFiberSectionSpace T m) :
    targetCoefficient T Λ c m i j (centralActSection T Λ c m u) =
      sourceCoefficient T Λ c m i j u * centralPhiAt T Λ c i j ^ m :=
  centralActSection_coefficients T Λ c m u i j

private def localConstant (U : (centralFiberScheme T).Opens) (b : ℂ) :
    Γ(centralFiberScheme T,U) :=
  (centralFiberScheme T).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
    (schemeGlobalConstants (centralFiberStructureMap T) b)

private theorem targetCoefficient_smul (c : ℂˣ) (m : ℕ) (i j : T.atlas.I)
    (b : ℂ) (u : centralFiberSectionSpace T m) :
    targetCoefficient T Λ c m i j (b • u) =
      localConstant T
        (pullOpen (centralActionAtlas T) (centralActionAtlas T) (centralActAt T Λ.action c) i j) b *
          targetCoefficient T Λ c m i j u := by
  have hc : coeffHom (centralActionAtlas T) m j (b • u) =
      localConstant T ((centralActionAtlas T).opens j) b *
          coeffHom (centralActionAtlas T) m j u :=
    SectionSpace.atlasPowerGlobalCoefficients_smul_const
      (centralFiberStructureMap T) (centralActionAtlas T) m j b u
  have hh := congrArg
    (fun r : Γ(centralFiberScheme T,(centralActionAtlas T).opens j) =>
      (centralFiberScheme T).presheaf.map (homOfLE (inf_le_right :
        pullOpen (centralActionAtlas T) (centralActionAtlas T) (centralActAt T Λ.action c) i j ≤
          (centralActionAtlas T).opens j)).op r) hc
  dsimp only [localConstant] at hh
  rw [map_mul,presheaf_map_map] at hh
  exact hh

private theorem sourceCoefficient_smul (c : ℂˣ) (m : ℕ) (i j : T.atlas.I)
    (b : ℂ) (u : centralFiberSectionSpace T m) :
    sourceCoefficient T Λ c m i j (b • u) =
      localConstant T
        (pullOpen (centralActionAtlas T) (centralActionAtlas T) (centralActAt T Λ.action c) i j) b *
          sourceCoefficient T Λ c m i j u := by
  have hc : coeffHom (centralActionAtlas T) m i (b • u) =
      localConstant T ((centralActionAtlas T).opens i) b *
          coeffHom (centralActionAtlas T) m i u :=
    SectionSpace.atlasPowerGlobalCoefficients_smul_const
      (centralFiberStructureMap T) (centralActionAtlas T) m i b u
  have hh := congrArg
    (fun r : Γ(centralFiberScheme T,(centralActionAtlas T).opens i) =>
      (centralActAt T Λ.action c).appLE ((centralActionAtlas T).opens i)
        (pullOpen (centralActionAtlas T) (centralActionAtlas T) (centralActAt T Λ.action c) i j)
          inf_le_left r) hc
  dsimp only [localConstant] at hh
  rw [map_mul,centralActAt_local_constants] at hh
  exact hh

/-- The actual geometric central H0 function is genuinely complex linear, without quotient transport. -/
def centralActSectionLinearMap (c : ℂˣ) (m : ℕ) :
    centralFiberSectionSpace T m →ₗ[ℂ] centralFiberSectionSpace T m where
  toFun := centralActSection T Λ c m
  map_add' u v := by
    apply centralPatch_ext T Λ c m
    intro i j
    change targetCoefficient T Λ c m i j (centralActSection T Λ c m (u + v)) =
      targetCoefficient T Λ c m i j (centralActSection T Λ c m u + centralActSection T Λ c m v)
    rw [map_add,coefficient_act,coefficient_act,coefficient_act,map_add,add_mul]
  map_smul' b u := by
    change centralActSection T Λ c m (b • u) = b • centralActSection T Λ c m u
    apply centralPatch_ext T Λ c m
    intro i j
    change targetCoefficient T Λ c m i j (centralActSection T Λ c m (b • u)) =
      targetCoefficient T Λ c m i j (b • centralActSection T Λ c m u)
    rw [coefficient_act,targetCoefficient_smul,sourceCoefficient_smul,coefficient_act]
    ring

end SGPT.TestCurve.CentralFiber
