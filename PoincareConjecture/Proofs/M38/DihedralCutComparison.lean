import PoincareConjecture.Proofs.M38.ReflectionComponentComparison
import PoincareConjecture.Proofs.M38.CylinderCarrier
import PoincareConjecture.Proofs.M38.SphereBundleCutChart

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

theorem dihedral_cut_component_precompact
    {Q : Type*} (q : RoundCylinderSpace → Q)
    (htranslation : ∀ n : ℤ, ∀ p, q (cylinderIntegerTranslation n p) = q p)
    (D : RoundCylinderSpace ≃ₜ RoundCylinderSpace) (a : RoundCylinderSpace) :
    IsCompact (closure (connectedComponentIn
      (q ⁻¹' (range (fun z : UnitTwoSphere => q (D (z, 0))))ᶜ) a)) := by
  let : ConnectedSpace UnitTwoSphere := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (E := StandardCapSpace)
      (Module.one_lt_rank_of_one_lt_finrank (by simp)) _ zero_le_one)
  apply cylindrical_translates_complement_precompact (Homeomorph.refl RoundCylinderSpace) D
    Prod.snd isProperMap_snd_of_compactSpace (fun _ => rfl)
    cylinderIntegerTranslation (fun _ _ => rfl) isPreconnected_connectedComponentIn
  intro n
  apply disjoint_left.mpr
  rintro y hy ⟨z, rfl⟩
  have hout := connectedComponentIn_subset
    (q ⁻¹' (range (fun z : UnitTwoSphere => q (D (z, 0))))ᶜ) a hy
  exact hout ⟨z, (htranslation n (D (z, 0))).symm⟩

theorem dihedral_cut_connected_standard_chart
    {Q : GeneralizedSliceCarrier.{u}}
    (q : RoundCylinderSpace → Q.carrier)
    (hq : IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ q)
    (hqsurj : Function.Surjective q)
    (hfibers : ∀ x y, q x = q y ↔
      ∃ n : ℤ, x = cylinderIntegerTranslation n y ∨ x = cylinderIntegerReflection n y)
    (D : RoundCylinderSpace ≃ₜ RoundCylinderSpace)
    {K : Set Q.carrier} (hK : IsConnected K)
    (havoid : Disjoint K (range (fun z : UnitTwoSphere => q (D (z, 0))))) :
    (∃ e : PartialDiffeomorph (𝓡 3) (𝓡 3) Q.carrier sphereCarrier.{u}.carrier ∞,
      K ⊆ e.source) ∨
    (∃ (a : RoundCylinderSpace) (n : ℤ),
      let C := connectedComponentIn
        (q ⁻¹' (range (fun z : UnitTwoSphere => q (D (z, 0))))ᶜ) a
      cylinderIntegerReflection n '' C = C ∧
        ∃ e : PartialDiffeomorph (𝓡 3) (𝓡 3) Q.carrier projectiveCarrier.{u}.carrier ∞,
          e.source = q '' C ∧ K ⊆ e.source ∧
          ∀ p ∈ C, e (q p) = projectivePolarMap
            (LinearIsometryEquiv.refl ℝ (EuclideanSpace ℝ (Fin 4)))
            (cylinderReflectionCenterShift n p)) := by
  let : LocallyConnectedSpace UnitTwoSphere :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 2)) UnitTwoSphere
  let U := (range (fun z : UnitTwoSphere => q (D (z, 0))))ᶜ
  obtain ⟨b, hb⟩ := hK.nonempty
  obtain ⟨a, ha⟩ := hqsurj b
  let : Nonempty RoundCylinderSpace := ⟨a⟩
  have hU : IsOpen U := (isCompact_range
    (hq.contMDiff.continuous.comp (D.continuous.comp
      (continuous_id.prodMk continuous_const)))).isClosed.isOpen_compl
  have hKU : K ⊆ U := disjoint_left.mp havoid
  have hKa : q a ∈ K := ha.symm ▸ hb
  let C := connectedComponentIn (q ⁻¹' U) a
  have hcompact : IsCompact (closure C) := dihedral_cut_component_precompact q
    (fun n p => (hfibers _ _).mpr ⟨n, Or.inl rfl⟩) D a
  rcases dihedral_precompact_component_fibers q hfibers U a hcompact with hinj | ⟨n, hn, hnfibers⟩
  · left
    have hKC : K ⊆ q '' C := connected_subset_image_precompact_component q
      hq.contMDiff.continuous hq.isLocalHomeomorph.isOpenMap hU (hKU hKa)
      hcompact hK.isPreconnected hKU hKa
    obtain ⟨d, _, hdt, _⟩ := localDiffeomorph_injective_open_sheet_generic q hq
      (hU.preimage hq.contMDiff.continuous).connectedComponentIn hinj
    obtain ⟨s, hss, hs, hsi⟩ := exists_spherical_chart_of_global_cylinder
      cylinderCarrier.{u} cylinderCarrierDiffeomorph
    let s' : PartialDiffeomorph (𝓡 3) (𝓡 3) cylinderCarrier.{u}.carrier sphereCarrier.{u}.carrier ∞ := {
      toPartialEquiv := s.toPartialEquiv
      open_source := s.open_source
      open_target := s.open_target
      contMDiffOn_toFun := hs
      contMDiffOn_invFun := hsi }
    let c := cylinderCarrierDiffeomorph.toPartialDiffeomorph.trans s'
    have hcs : c.source = univ := by
      change univ ∩ cylinderCarrierDiffeomorph ⁻¹' s.source = univ
      rw [hss, preimage_univ, inter_self]
    refine ⟨d.symm.trans c, ?_⟩
    intro y hy
    refine ⟨hdt.symm ▸ hKC hy, ?_⟩
    change d.symm y ∈ c.source
    rw [hcs]
    exact mem_univ _
  · right
    obtain ⟨e, hes, hKe, he⟩ := reflection_component_projective_comparison q hq
      (LinearIsometryEquiv.refl ℝ (EuclideanSpace ℝ (Fin 4))) n hU a
      hK.isPreconnected hKU hKa hcompact hnfibers
    exact ⟨a, n, hn, e, hes, hKe, he⟩

end PoincareConjecture.M38
