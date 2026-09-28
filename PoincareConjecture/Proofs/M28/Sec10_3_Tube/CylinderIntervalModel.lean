import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CompactRegions

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.OpenCylinderModel

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] {U V : Set M}

theorem exists_model_of_interval_reparametrization
    (T : OpenCylinderModel U) {J : Set ℝ} (hJ : J ⊆ Ioo (0 : ℝ) 1)
    (hV : ∀ x : M, x ∈ V ↔ x ∈ U ∧ (T.inverse x).2 ∈ J)
    (f g : ℝ → ℝ) (hf : ContDiffOn ℝ ∞ f (Ioo (0 : ℝ) 1))
    (hg : ContDiffOn ℝ ∞ g J) (hfJ : MapsTo f (Ioo (0 : ℝ) 1) J)
    (hgI : MapsTo g J (Ioo (0 : ℝ) 1))
    (hgf : LeftInvOn g f (Ioo (0 : ℝ) 1)) (hfg : LeftInvOn f g J) :
    ∃ T' : OpenCylinderModel V,
      T'.coordinate = (fun z => T.coordinate (z.1, f z.2)) ∧
      T'.inverse = (fun x => ((T.inverse x).1, g (T.inverse x).2)) := by
  let F : RoundCylinderSpace → RoundCylinderSpace := fun z => (z.1, f z.2)
  have hFs : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ))
      ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ F (univ ×ˢ Ioo (0 : ℝ) 1) :=
    contMDiff_fst.contMDiffOn.prodMk
      (hf.contMDiffOn.comp contMDiff_snd.contMDiffOn (fun _ hz => hz.2))
  have hFmem (z : RoundCylinderSpace) (hz : z ∈ univ ×ˢ Ioo (0 : ℝ) 1) :
      F z ∈ univ ×ˢ Ioo (0 : ℝ) 1 := ⟨mem_univ _, hJ (hfJ hz.2)⟩
  let c : RoundCylinderSpace → M := fun z => T.coordinate (F z)
  let v : M → RoundCylinderSpace := fun x => ((T.inverse x).1, g (T.inverse x).2)
  have hcmem (z : RoundCylinderSpace) (hz : z ∈ univ ×ˢ Ioo (0 : ℝ) 1) :
      c z ∈ V := by
    apply (hV _).mpr
    refine ⟨T.coordinate_mem_m28 (hFmem z hz).2, ?_⟩
    change (T.inverse (T.coordinate (F z))).2 ∈ J
    rw [T.left_inverse (hFmem z hz)]
    exact hfJ hz.2
  have hvmem (x : M) (hx : x ∈ V) : v x ∈ univ ×ˢ Ioo (0 : ℝ) 1 :=
    ⟨mem_univ _, hgI ((hV x).mp hx).2⟩
  have hleft (z : RoundCylinderSpace) (hz : z ∈ univ ×ˢ Ioo (0 : ℝ) 1) :
      v (c z) = z := by
    dsimp only [v, c]
    rw [T.left_inverse (hFmem z hz)]
    change (z.1, g (f z.2)) = z
    rw [hgf hz.2]
  have hright (x : M) (hx : x ∈ V) : c (v x) = x := by
    change T.coordinate ((T.inverse x).1, f (g (T.inverse x).2)) = x
    rw [hfg ((hV x).mp hx).2, Prod.mk.eta]
    exact T.right_inverse ((hV x).mp hx).1
  have hcs : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ c
      (univ ×ˢ Ioo (0 : ℝ) 1) := T.coordinate_smooth.comp hFs hFmem
  have hTi := T.inverse_smooth.mono (fun x hx => ((hV x).mp hx).1)
  have hvs : ContMDiffOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ v V :=
    (contMDiff_fst.comp_contMDiffOn hTi).prodMk
      (hg.contMDiffOn.comp (contMDiff_snd.comp_contMDiffOn hTi)
        (fun x hx => ((hV x).mp hx).2))
  have hc : Continuous (fun z : UnitTwoSphere × Ioo (0 : ℝ) 1 =>
      c (z.1, (z.2 : ℝ))) :=
    hcs.continuousOn.comp_continuous
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
      (fun z => ⟨mem_univ _, z.2.property⟩)
  have hv : Continuous (fun x : V => v x) :=
    hvs.continuousOn.comp_continuous continuous_subtype_val (fun x => x.property)
  let e : (UnitTwoSphere × Ioo (0 : ℝ) 1) ≃ₜ V := {
    toFun z := ⟨c (z.1, (z.2 : ℝ)), hcmem _ ⟨mem_univ _, z.2.property⟩⟩
    invFun x := ((v x).1, ⟨(v x).2, (hvmem x x.property).2⟩)
    left_inv z := by
      have hh := hleft (z.1, (z.2 : ℝ)) ⟨mem_univ _, z.2.property⟩
      apply Prod.ext
      · change (v (c (z.1, (z.2 : ℝ)))).1 = z.1
        exact congrArg Prod.fst hh
      · apply Subtype.ext
        change (v (c (z.1, (z.2 : ℝ)))).2 = (z.2 : ℝ)
        exact congrArg Prod.snd hh
    right_inv x := Subtype.ext (hright x x.property)
    continuous_toFun := hc.subtype_mk _
    continuous_invFun := hv.fst.prodMk (hv.snd.subtype_mk _) }
  exact ⟨{
    homeomorph := e
    coordinate := c
    coordinate_eq := fun _ => rfl
    coordinate_smooth := hcs
    inverse := v
    inverse_mem := hvmem
    left_inverse := hleft
    right_inverse := hright
    inverse_smooth := hvs }, rfl, rfl⟩

end PoincareConjecture.OpenCylinderModel
