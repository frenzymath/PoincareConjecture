import PoincareConjecture.Definitions.Ch11.SingularLimits
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.InverseFunction.ModelSpaces
import Mathlib.Topology.Maps.Proper.CompactlyGenerated

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M32

variable {F : GeneralizedRicciFlowData.{u}} {T epsilon : ℝ}
  {E : GeneralizedFlowExtension F T}

theorem horn_isClosed_carrier (horn : StrongHorn E epsilon) : IsClosed horn.carrier := by
  let f : UnitTwoSphere × Ico (0 : ℝ) 1 → (E.extended.slice T).carrier :=
    fun z => horn.coordinate z
  have hf : Continuous f := continuous_subtype_val.comp horn.coordinate.continuous
  have hp : IsProperMap f := isProperMap_iff_isCompact_preimage.mpr ⟨hf, by
    intro K hK
    change IsCompact {z | (horn.coordinate z : (E.extended.slice T).carrier) ∈ K}
    simpa only [horn.coordinate_eq] using horn.proper K hK⟩
  have hrange : range f = horn.carrier := by
    apply Subset.antisymm
    · rintro x ⟨z, rfl⟩
      exact (horn.coordinate z).property
    · intro x hx
      exact ⟨horn.coordinate.symm ⟨x, hx⟩,
        congrArg Subtype.val (horn.coordinate.apply_symm_apply ⟨x, hx⟩)⟩
  rw [← hrange]
  exact hp.isClosed_range

theorem horn_carrier_diff_boundary_eq_image (horn : StrongHorn E epsilon) :
    horn.carrier \ horn.boundary_sphere =
      horn.parameterization '' (univ ×ˢ Ioo (0 : ℝ) 1) := by
  apply Subset.antisymm
  · intro x hx
    let z := horn.coordinate.symm ⟨x, hx.1⟩
    have hz : horn.parameterization (z.1, (z.2 : ℝ)) = x := by
      rw [← horn.coordinate_eq]
      exact congrArg Subtype.val (horn.coordinate.apply_symm_apply ⟨x, hx.1⟩)
    have hpos : 0 < (z.2 : ℝ) := by
      apply lt_of_le_of_ne z.2.property.1
      intro hzero
      apply hx.2
      rw [horn.boundary_sphere_eq]
      refine ⟨(z.1, 0), ⟨mem_univ _, rfl⟩, ?_⟩
      simpa only [hzero] using hz
    exact ⟨(z.1, (z.2 : ℝ)), ⟨mem_univ _, hpos, z.2.property.2⟩, hz⟩
  · rintro x ⟨⟨s, t⟩, ⟨_, ht0, ht1⟩, rfl⟩
    have hmem := (horn.coordinate (s, ⟨t, ht0.le, ht1⟩)).property
    rw [horn.coordinate_eq] at hmem
    refine ⟨hmem, ?_⟩
    rw [horn.boundary_sphere_eq]
    rintro ⟨⟨s', t'⟩, ⟨_, ht'⟩, heq⟩
    have ht'0 : t' = 0 := ht'
    subst t'
    have heq' : horn.coordinate (s', ⟨0, le_rfl, by norm_num⟩) =
        horn.coordinate (s, ⟨t, ht0.le, ht1⟩) := by
      apply Subtype.ext
      simpa only [horn.coordinate_eq] using heq
    have hzero := congrArg (fun z : UnitTwoSphere × Ico (0 : ℝ) 1 => (z.2 : ℝ))
      (horn.coordinate.injective heq')
    exact (ne_of_gt ht0) hzero.symm

theorem horn_isOpen_carrier_diff_boundary (horn : StrongHorn E epsilon) :
    IsOpen (horn.carrier \ horn.boundary_sphere) := by
  let : ChartedSpace (EuclideanSpace ℝ (Fin 2) × ℝ) RoundCylinderSpace :=
    prodChartedSpace (EuclideanSpace ℝ (Fin 2)) UnitTwoSphere ℝ ℝ
  rw [horn_carrier_diff_boundary_eq_image]
  apply isOpen_iff_mem_nhds.mpr
  rintro x ⟨z, hz, rfl⟩
  have hzcollar : z ∈ univ ×ˢ Ioo (-horn.collar) 1 :=
    ⟨hz.1, (neg_lt_zero.mpr horn.collar_pos).trans hz.2.1, hz.2.2⟩
  have hsmooth := horn.parameterization_smooth.contMDiffAt
    ((isOpen_univ.prod isOpen_Ioo).mem_nhds hzcollar)
  have hsmooth' : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) (𝓡 3) ∞
      horn.parameterization z := by
    simpa only [modelWithCornersSelf_prod] using hsmooth
  have hderiv : (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) (𝓡 3)
      horn.parameterization z :
      (EuclideanSpace ℝ (Fin 2) × ℝ) →L[ℝ] EuclideanSpace ℝ (Fin 3)) =
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) horn.parameterization z :
      (EuclideanSpace ℝ (Fin 2) × ℝ) →L[ℝ] EuclideanSpace ℝ (Fin 3)) :=
    congrArg (β := (EuclideanSpace ℝ (Fin 2) × ℝ) →L[ℝ] EuclideanSpace ℝ (Fin 3))
      (fun I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin 2) × ℝ)
        (EuclideanSpace ℝ (Fin 2) × ℝ) =>
        (mfderiv I (𝓡 3) horn.parameterization z :
          (EuclideanSpace ℝ (Fin 2) × ℝ) →L[ℝ] EuclideanSpace ℝ (Fin 3)))
      modelWithCornersSelf_prod
  have hbij : Function.Bijective
      (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) (𝓡 3) horn.parameterization z) := by
    rw [hderiv]
    exact horn.parameterization_regular z ⟨hz.2.1.le, hz.2.2⟩
  rw [← Poincare.Geometry.Manifold.map_nhds_eq_of_contMDiffAt_bijective_mfderiv_modelSpaces
    hsmooth' hbij]
  change horn.parameterization ⁻¹' (horn.parameterization '' (univ ×ˢ Ioo (0 : ℝ) 1)) ∈ 𝓝 z
  exact mem_of_superset ((isOpen_univ.prod isOpen_Ioo).mem_nhds hz)
    (fun y hy => ⟨y, hy, rfl⟩)

theorem horn_frontier_carrier_subset_boundary (horn : StrongHorn E epsilon) :
    frontier horn.carrier ⊆ horn.boundary_sphere := by
  intro x hx
  have hxc : x ∈ horn.carrier := by
    simpa only [(horn_isClosed_carrier horn).closure_eq] using hx.1
  by_contra hnot
  apply hx.2
  apply mem_interior_iff_mem_nhds.mpr
  exact mem_of_superset ((horn_isOpen_carrier_diff_boundary horn).mem_nhds ⟨hxc, hnot⟩)
    (fun y hy => hy.1)

theorem horn_subset_carrier_of_isPreconnected (horn : StrongHorn E epsilon)
    {S : Set (E.extended.slice T).carrier} (hS : IsPreconnected S)
    (hmeet : (S ∩ horn.carrier).Nonempty) (havoid : Disjoint S horn.boundary_sphere) :
    S ⊆ horn.carrier := by
  have hsub : S ⊆ (horn.carrier \ horn.boundary_sphere) ∪ horn.carrierᶜ := by
    intro x hx
    by_cases hxc : x ∈ horn.carrier
    · exact Or.inl ⟨hxc, fun hxb => disjoint_left.mp havoid hx hxb⟩
    · exact Or.inr hxc
  have hmeet' : (S ∩ (horn.carrier \ horn.boundary_sphere)).Nonempty := by
    obtain ⟨x, hx, hxc⟩ := hmeet
    exact ⟨x, hx, hxc, fun hxb => disjoint_left.mp havoid hx hxb⟩
  have hd : Disjoint (horn.carrier \ horn.boundary_sphere) horn.carrierᶜ :=
    disjoint_left.mpr (fun x hx hxc => hxc hx.1)
  have hinside := hS.subset_left_of_subset_union (horn_isOpen_carrier_diff_boundary horn)
    (horn_isClosed_carrier horn).isOpen_compl hd hsub hmeet'
  exact fun x hx => (hinside hx).1

end PoincareConjecture.M32
