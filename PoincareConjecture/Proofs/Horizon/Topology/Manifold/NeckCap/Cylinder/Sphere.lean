import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cylinder








noncomputable section

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.EpsilonNeck

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} (N : EpsilonNeck g)

private theorem centralCylinder_mem (p : UnitTwoSphere) :
    (p, (0 : ℝ)) ∈ N.cylinderDomain :=
  ⟨mem_univ _, neg_neg_of_pos (inv_pos.mpr N.epsilon_pos), inv_pos.mpr N.epsilon_pos⟩

theorem centralSphere_contMDiff :
    ContMDiff (𝓡 2) (𝓡 3) ∞ (fun p : UnitTwoSphere => N.coordinate_map (p, 0)) := by
  intro p
  exact (N.coordinate_map_smooth.contMDiffAt
    (N.cylinderDomain_open.mem_nhds (N.centralCylinder_mem p))).comp p
      (contMDiffAt_id.prodMk contMDiffAt_const)

private def centralSphereChart (p : UnitTwoSphere) :
    OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)) :=
  (N.coordinatePartialHomeomorph.symm.trans
    ((chartAt (EuclideanSpace ℝ (Fin 2)) p).prod (OpenPartialHomeomorph.refl ℝ))).trans
    (RiemannianMetric.lineModelEquiv 2).toHomeomorph.toOpenPartialHomeomorph

private theorem centralSphereChart_mem_maximalAtlas (p : UnitTwoSphere) :
    N.centralSphereChart p ∈ IsManifold.maximalAtlas (𝓡 3) ∞ M := by
  apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
  · apply (RiemannianMetric.lineModelEquiv 2).contDiff.contMDiff.comp_contMDiffOn
    apply ContMDiffOn.prodMk_space
    · apply (contMDiffOn_chart (I := 𝓡 2) (x := p)).comp
      · exact contMDiff_fst.comp_contMDiffOn
          (N.coordinate_inverse_smooth.mono (fun x hx => hx.1.1))
      · intro x hx
        exact hx.1.2.1
    · exact contMDiff_snd.comp_contMDiffOn
        (N.coordinate_inverse_smooth.mono (fun x hx => hx.1.1))
  · apply N.coordinate_map_smooth.comp
    · apply ContMDiffOn.prodMk
      · apply (contMDiffOn_chart_symm (I := 𝓡 2) (x := p)).comp
        · exact (contDiff_fst.comp (RiemannianMetric.lineModelEquiv 2).symm.contDiff).contMDiff.contMDiffOn
        · intro z hz
          exact hz.2.1.1
      · exact (contDiff_snd.comp (RiemannianMetric.lineModelEquiv 2).symm.contDiff).contMDiff.contMDiffOn
    · intro z hz
      exact hz.2.2

theorem centralSphere_isImmersion :
    Manifold.IsImmersion (𝓡 2) (𝓡 3) ∞
      (fun p : UnitTwoSphere => N.coordinate_map (p, 0)) := by
  apply Manifold.IsImmersionOfComplement.isImmersion (F := ℝ)
  intro p
  refine Manifold.IsImmersionAtOfComplement.mk_of_continuousAt
    (N.centralSphere_contMDiff.continuous.continuousAt)
    (RiemannianMetric.lineModelEquiv 2)
    (chartAt (EuclideanSpace ℝ (Fin 2)) p) (N.centralSphereChart p)
    (mem_chart_source _ p) ?_ (IsManifold.chart_mem_maximalAtlas p)
    (N.centralSphereChart_mem_maximalAtlas p) ?_
  · change ((N.coordinate_map (p, 0) ∈ N.carrier ∧
      N.coordinate_inverse (N.coordinate_map (p, 0)) ∈
        (chartAt (EuclideanSpace ℝ (Fin 2)) p).source ×ˢ univ) ∧ _)
    refine ⟨⟨N.coordinate_map_mem (N.centralCylinder_mem p), ?_⟩, mem_univ _⟩
    rw [N.coordinate_inverse_coordinate_map (N.centralCylinder_mem p)]
    exact ⟨mem_chart_source _ p, mem_univ _⟩
  · intro y hy
    have hy' : y ∈ (chartAt (EuclideanSpace ℝ (Fin 2)) p).target := by
      exact hy.2
    change RiemannianMetric.lineModelEquiv 2
      (((chartAt (EuclideanSpace ℝ (Fin 2)) p)
        (N.coordinate_inverse (N.coordinate_map
          ((chartAt (EuclideanSpace ℝ (Fin 2)) p).symm y, 0))).1),
        (N.coordinate_inverse (N.coordinate_map
          ((chartAt (EuclideanSpace ℝ (Fin 2)) p).symm y, 0))).2) = _
    rw [N.coordinate_inverse_coordinate_map (N.centralCylinder_mem _)]
    dsimp
    rw [(chartAt (EuclideanSpace ℝ (Fin 2)) p).right_inv hy']

theorem centralSphere_isSmoothEmbedding :
    Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞
      (fun p : UnitTwoSphere => N.coordinate_map (p, 0)) := by
  refine ⟨N.centralSphere_isImmersion, ?_⟩
  let z : Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ :=
    ⟨0, neg_neg_of_pos (inv_pos.mpr N.epsilon_pos), inv_pos.mpr N.epsilon_pos⟩
  have h := Topology.IsEmbedding.subtypeVal.comp
    (N.coordinate.isEmbedding.comp (isEmbedding_prodMkLeft z))
  convert h using 1
  funext p
  exact (N.coordinate_map_eq (p, z)).symm

theorem centralSphere_range :
    Set.range (fun p : UnitTwoSphere => N.coordinate_map (p, 0)) = N.central_sphere := by
  rw [N.central_sphere_eq]
  ext x
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨(p, 0), ⟨mem_univ _, mem_singleton 0⟩, rfl⟩
  · rintro ⟨⟨p, t⟩, ⟨_, ht⟩, hx⟩
    have ht' : t = 0 := ht
    subst t
    exact ⟨p, hx⟩


theorem central_sphere_isotopic_self :
    SmoothSphereIsotopicIn N.carrier N.central_sphere N.central_sphere := by
  refine ⟨fun z => N.coordinate_map (z.2, 0),
    (N.centralSphere_contMDiff.comp contMDiff_snd).contMDiffOn, ?_,
    N.centralSphere_range, N.centralSphere_range⟩
  intro t ht
  refine ⟨N.centralSphere_isSmoothEmbedding, ?_⟩
  rw [N.centralSphere_range]
  exact N.central_sphere_subset

end PoincareConjecture.EpsilonNeck
