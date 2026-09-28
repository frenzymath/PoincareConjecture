import PoincareConjecture.Proofs.M02.Topology.IntegralCapMayerVietoris
import PoincareConjecture.Proofs.M02.Topology.IntegralSupportCapMap
import PoincareConjecture.Proofs.M02.Topology.IntegralChartSupport



set_option autoImplicit false

noncomputable section

open CategoryTheory Limits HomologicalComplex

universe u

namespace PoincareConjecture.Proofs.M02.Topology

variable {X : Type u} [TopologicalSpace X]

theorem exists_integralLocalizedRelativeChain (U K : Set X) (n : Nat)
    (c : (integralChains X).X n)
    (hc : c ∈ integralSmallChains (integralBinaryCover U Kᶜ) n) :
    ∃ a : (integralRelativeChains ((Subtype.val : U → X) ⁻¹' Kᶜ)).X n,
      (integralOpenSupportMap K U).f n a = (integralRelativeProjection Kᶜ).f n c := by
  rw [integralSmallChains_two_eq_sup] at hc
  obtain ⟨_, ⟨a, rfl⟩, _, ⟨b, rfl⟩, hab⟩ := Submodule.mem_sup.mp hc
  refine ⟨(integralRelativeProjection ((Subtype.val : U → X) ⁻¹' Kᶜ)).f n a, ?_⟩
  have ha := congrArg (fun f => f.f n a) (integralPairInclusion_projection Kᶜ U)
  have hb := congrArg (fun f => f.f n b) (cokernel.condition (integralSubspaceChains Kᶜ))
  change (integralRelativeProjection Kᶜ).f n ((integralSubspaceChains Kᶜ).f n b) = 0 at hb
  rw [← hab, map_add, hb, add_zero]
  exact ha

theorem integralLocalizedRelativeChain_cycle (U K : Set X) (n m : Nat)
    (a : (integralRelativeChains ((Subtype.val : U → X) ⁻¹' Kᶜ)).X n)
    (c : (integralChains X).X n)
    (ha : (integralOpenSupportMap K U).f n a = (integralRelativeProjection Kᶜ).f n c)
    (hdc : (integralChains X).d n m c ∈
      LinearMap.range ((integralSubspaceChains Kᶜ).f m).hom) :
    (integralRelativeChains ((Subtype.val : U → X) ⁻¹' Kᶜ)).d n m a = 0 := by
  apply integralPairInclusion_injective Kᶜ U m
  rw [map_zero]
  change (integralOpenSupportMap K U).f m
    ((integralRelativeChains ((Subtype.val : U → X) ⁻¹' Kᶜ)).d n m a) = 0
  have hinc := congrArg (fun f => f a) ((integralOpenSupportMap K U).comm n m)
  have hproj := congrArg (fun f => f c) ((integralRelativeProjection Kᶜ).comm n m)
  change (integralRelativeChains Kᶜ).d n m ((integralOpenSupportMap K U).f n a) =
    (integralOpenSupportMap K U).f m
      ((integralRelativeChains ((Subtype.val : U → X) ⁻¹' Kᶜ)).d n m a) at hinc
  rw [← hinc, ha]
  exact hproj.trans ((integralProjection_eq_zero_iff (integralSubspaceChains Kᶜ) m _).mpr hdc)

theorem integralLocalizedCap_eq_supportCap (U K : Set X) (p q : Nat)
    (c : (integralChains X).X (p + q))
    (hc : c ∈ integralSmallChains (integralBinaryCover U Kᶜ) (p + q))
    (a : (integralRelativeChains ((Subtype.val : U → X) ⁻¹' Kᶜ)).X (p + q))
    (ha : (integralOpenSupportMap K U).f (p + q) a =
      (integralRelativeProjection Kᶜ).f (p + q) c)
    (phi : (integralSupportCochains K).X q) :
    integralLocalizedCap U K p q c hc phi =
      integralSupportCap ((Subtype.val : U → X) ⁻¹' Kᶜ) p q a
        ((integralDualMap (integralOpenSupportMap K U)).f q phi) := by
  let := integralSubspaceChains_mono U
  apply (ModuleCat.mono_iff_injective ((integralSubspaceChains U).f p)).mp inferInstance
  rw [integralLocalizedCap_inclusion]
  have hn := integralSupportCap_naturality
    (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X))
    (A := (Subtype.val : U → X) ⁻¹' Kᶜ) (B := Kᶜ) (fun _ hx => hx) p q a phi
  change (integralSubspaceChains U).f p
      (integralSupportCap ((Subtype.val : U → X) ⁻¹' Kᶜ) p q a
        ((integralDualMap (integralOpenSupportMap K U)).f q phi)) =
    integralSupportCap Kᶜ p q ((integralOpenSupportMap K U).f (p + q) a) phi at hn
  rw [ha, integralSupportCap_projection] at hn
  exact hn.symm

theorem integralLocalizedRelativeChain_homology
    (U K : Set X) (hU : IsOpen U) (hK : IsClosed K) (hKU : K ⊆ U)
    (a : LinearMap.ker
      ((integralRelativeChains ((Subtype.val : U → X) ⁻¹' Kᶜ)).sc' 4 3 2).g.hom)
    (z : LinearMap.ker ((integralRelativeChains Kᶜ).sc' 4 3 2).g.hom)
    (ha : (integralOpenSupportMap K U).f 3 a.val = z.val) :
    moduleComplexHomologyClass (integralRelativeChains ((Subtype.val : U → X) ⁻¹' Kᶜ))
        4 3 2 (by simp) (by simp) a =
      (integralOpenSupportHomologyIso K U hK hU hKU 3).inv
        (moduleComplexHomologyClass (integralRelativeChains Kᶜ) 4 3 2 (by simp) (by simp) z) := by
  let e := integralOpenSupportHomologyIso K U hK hU hKU 3
  apply (ModuleCat.mono_iff_injective e.hom).mp inferInstance
  rw [Iso.inv_hom_id_apply]
  change homologyMap (integralOpenSupportMap K U) 3 _ = _
  rw [moduleComplexHomologyClass_map]
  congr 1
  exact Subtype.ext ha

theorem integralLocalizedCap_three_one_cycle (U K : Set X)
    (c : (integralChains X).X 3)
    (hc : c ∈ integralSmallChains (integralBinaryCover U Kᶜ) 3)
    (hdc : (integralChains X).d 3 2 c ∈
      LinearMap.range ((integralSubspaceChains Kᶜ).f 2).hom)
    (phi : (integralSupportCochains K).X 1)
    (hphi : (integralSupportCochains K).d 1 2 phi = 0) :
    (integralChains U).d 2 1 (integralLocalizedCap U K 2 1 c hc phi) = 0 := by
  rw [integralLocalizedCap_three_one_boundary U K c hc hdc, hphi, map_zero]

theorem integralLocalizedCapHomologyOne_class
    (U K : Set X) (hU : IsOpen U) (hK : IsClosed K) (hKU : K ⊆ U)
    (c : (integralChains X).X 3)
    (hc : c ∈ integralSmallChains (integralBinaryCover U Kᶜ) 3)
    (hdc : (integralChains X).d 3 2 c ∈
      LinearMap.range ((integralSubspaceChains Kᶜ).f 2).hom)
    (z : LinearMap.ker ((integralRelativeChains Kᶜ).sc' 4 3 2).g.hom)
    (hz : z.val = (integralRelativeProjection Kᶜ).f 3 c)
    (phi : LinearMap.ker ((integralSupportCochains K).sc' 0 1 2).g.hom) :
    integralSupportCapHomologyOne ((Subtype.val : U → X) ⁻¹' Kᶜ)
        ((integralOpenSupportHomologyIso K U hK hU hKU 3).inv
          (moduleComplexHomologyClass (integralRelativeChains Kᶜ) 4 3 2 (by simp) (by simp) z))
        (homologyMap (integralDualMap (integralOpenSupportMap K U)) 1
          (moduleComplexHomologyClass (integralSupportCochains K) 0 1 2
            (by simp) (by simp) phi)) =
      moduleComplexHomologyClass (integralChains U) 3 2 1 (by simp) (by simp)
        ⟨integralLocalizedCap U K 2 1 c hc phi.val,
          integralLocalizedCap_three_one_cycle U K c hc hdc phi.val phi.property⟩ := by
  obtain ⟨a, ha⟩ := exists_integralLocalizedRelativeChain U K 3 c hc
  let ac : LinearMap.ker
      ((integralRelativeChains ((Subtype.val : U → X) ⁻¹' Kᶜ)).sc' 4 3 2).g.hom :=
    ⟨a, integralLocalizedRelativeChain_cycle U K 3 2 a c ha hdc⟩
  rw [← integralLocalizedRelativeChain_homology U K hU hK hKU ac z (ha.trans hz.symm),
    moduleComplexHomologyClass_map]
  simp only [moduleComplexHomologyClass]
  rw [integralSupportCapHomologyOne_class]
  apply congrArg ((integralChains U).homologyIsoSc' 3 2 1 (by simp) (by simp)).inv
  apply congrArg (moduleHomologyClass ((integralChains U).sc' 3 2 1))
  apply Subtype.ext
  exact (integralLocalizedCap_eq_supportCap U K 2 1 c hc a ha phi.val).symm

theorem integralLocalizedCapHomologyTwo_class
    (U K : Set X) (hU : IsOpen U) (hK : IsClosed K) (hKU : K ⊆ U)
    (c : (integralChains X).X 3)
    (hc : c ∈ integralSmallChains (integralBinaryCover U Kᶜ) 3)
    (hdc : (integralChains X).d 3 2 c ∈
      LinearMap.range ((integralSubspaceChains Kᶜ).f 2).hom)
    (z : LinearMap.ker ((integralRelativeChains Kᶜ).sc' 4 3 2).g.hom)
    (hz : z.val = (integralRelativeProjection Kᶜ).f 3 c)
    (phi : LinearMap.ker ((integralSupportCochains K).sc' 1 2 3).g.hom) :
    integralSupportCapHomologyTwo ((Subtype.val : U → X) ⁻¹' Kᶜ)
        ((integralOpenSupportHomologyIso K U hK hU hKU 3).inv
          (moduleComplexHomologyClass (integralRelativeChains Kᶜ) 4 3 2 (by simp) (by simp) z))
        (homologyMap (integralDualMap (integralOpenSupportMap K U)) 2
          (moduleComplexHomologyClass (integralSupportCochains K) 1 2 3
            (by simp) (by simp) phi)) =
      moduleComplexHomologyClass (integralChains U) 2 1 0 (by simp) (by simp)
        ⟨integralLocalizedCap U K 1 2 c hc phi.val,
          integralLocalizedCap_three_two_cycle U K c hc hdc phi.val phi.property⟩ := by
  obtain ⟨a, ha⟩ := exists_integralLocalizedRelativeChain U K 3 c hc
  let ac : LinearMap.ker
      ((integralRelativeChains ((Subtype.val : U → X) ⁻¹' Kᶜ)).sc' 4 3 2).g.hom :=
    ⟨a, integralLocalizedRelativeChain_cycle U K 3 2 a c ha hdc⟩
  rw [← integralLocalizedRelativeChain_homology U K hU hK hKU ac z (ha.trans hz.symm),
    moduleComplexHomologyClass_map]
  simp only [moduleComplexHomologyClass]
  rw [integralSupportCapHomologyTwo_class]
  apply congrArg ((integralChains U).homologyIsoSc' 2 1 0 (by simp) (by simp)).inv
  apply congrArg (moduleHomologyClass ((integralChains U).sc' 2 1 0))
  apply Subtype.ext
  exact (integralLocalizedCap_eq_supportCap U K 1 2 c hc a ha phi.val).symm

theorem integralLocalizedCapHomologyThree_class
    (U K : Set X) (hU : IsOpen U) (hK : IsClosed K) (hKU : K ⊆ U)
    (c : (integralChains X).X 3)
    (hc : c ∈ integralSmallChains (integralBinaryCover U Kᶜ) 3)
    (hdc : (integralChains X).d 3 2 c ∈
      LinearMap.range ((integralSubspaceChains Kᶜ).f 2).hom)
    (z : LinearMap.ker ((integralRelativeChains Kᶜ).sc' 4 3 2).g.hom)
    (hz : z.val = (integralRelativeProjection Kᶜ).f 3 c)
    (phi : LinearMap.ker ((integralSupportCochains K).sc' 2 3 4).g.hom) :
    integralSupportCapHomologyThree ((Subtype.val : U → X) ⁻¹' Kᶜ)
        ((integralOpenSupportHomologyIso K U hK hU hKU 3).inv
          (moduleComplexHomologyClass (integralRelativeChains Kᶜ) 4 3 2 (by simp) (by simp) z))
        (homologyMap (integralDualMap (integralOpenSupportMap K U)) 3
          (moduleComplexHomologyClass (integralSupportCochains K) 2 3 4
            (by simp) (by simp) phi)) =
      moduleComplexHomologyClass (integralChains U) 1 0 0 (by simp) (by simp)
        ⟨integralLocalizedCap U K 0 3 c hc phi.val, by
          change (integralChains U).d 0 0 _ = 0
          rw [(integralChains U).shape 0 0 (by simp)]
          rfl⟩ := by
  obtain ⟨a, ha⟩ := exists_integralLocalizedRelativeChain U K 3 c hc
  let ac : LinearMap.ker
      ((integralRelativeChains ((Subtype.val : U → X) ⁻¹' Kᶜ)).sc' 4 3 2).g.hom :=
    ⟨a, integralLocalizedRelativeChain_cycle U K 3 2 a c ha hdc⟩
  rw [← integralLocalizedRelativeChain_homology U K hU hK hKU ac z (ha.trans hz.symm),
    moduleComplexHomologyClass_map]
  simp only [moduleComplexHomologyClass]
  rw [integralSupportCapHomologyThree_class]
  apply congrArg ((integralChains U).homologyIsoSc' 1 0 0 (by simp) (by simp)).inv
  apply congrArg (moduleHomologyClass ((integralChains U).sc' 1 0 0))
  apply Subtype.ext
  exact (integralLocalizedCap_eq_supportCap U K 0 3 c hc a ha phi.val).symm

end PoincareConjecture.Proofs.M02.Topology
