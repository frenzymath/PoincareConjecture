import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Core.Euclidean
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cylinder.Sphere












set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.CapCertificate

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] {g : RiemannianMetric 3 M}
  (C : CapCertificate g)
  (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
  (hs : e.source = C.carrier) (ht : e.target = univ)

include hs

omit [T2Space M] in
private theorem boundary_param_mem_source (p : UnitTwoSphere) :
    C.boundary_neck.coordinate_map (p, 0) ∈ e.source := by
  rw [hs]
  apply C.boundary_subset
  rw [C.boundary_eq_neck_sphere, ← C.boundary_neck.centralSphere_range]
  exact mem_range_self p

omit [T2Space M] in


theorem boundary_param_isSmoothEmbedding
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target) :
    Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞
      (fun p : UnitTwoSphere => e (C.boundary_neck.coordinate_map (p, 0))) := by
  have hsm : ContMDiff (𝓡 2) (𝓡 3) ∞
      (fun p : UnitTwoSphere => e (C.boundary_neck.coordinate_map (p, 0))) := by
    intro p
    exact (he.contMDiffAt (e.open_source.mem_nhds
      (C.boundary_param_mem_source e hs p))).comp p (C.boundary_neck.centralSphere_contMDiff p)
  refine ⟨?_, ?_⟩
  · have himm := C.boundary_neck.centralSphere_isImmersion
    refine ⟨himm.complement, inferInstance, inferInstance, ?_⟩
    intro p
    have hi := himm.isImmersionOfComplement_complement p
    have hchart : e.symm.trans hi.codChart ∈
        IsManifold.maximalAtlas (𝓡 3) ∞ (EuclideanSpace ℝ (Fin 3)) := by
      apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
      · exact (contMDiffOn_of_mem_maximalAtlas hi.codChart_mem_maximalAtlas).comp
          (hei.mono (fun x hx => hx.1)) (fun x hx => hx.2)
      · exact he.comp
          ((contMDiffOn_symm_of_mem_maximalAtlas hi.codChart_mem_maximalAtlas).mono
            (fun x hx => hx.1)) (fun x hx => hx.2)
    refine Manifold.IsImmersionAtOfComplement.mk_of_continuousAt
      (hsm.continuous.continuousAt) hi.equiv hi.domChart (e.symm.trans hi.codChart)
      hi.mem_domChart_source ?_ hi.domChart_mem_maximalAtlas hchart ?_
    · refine ⟨e.map_source (C.boundary_param_mem_source e hs p), ?_⟩
      change e.symm (e (C.boundary_neck.coordinate_map (p, 0))) ∈ hi.codChart.source
      rw [e.left_inv (C.boundary_param_mem_source e hs p)]
      exact hi.mem_codChart_source
    · intro y hy
      convert hi.writtenInCharts hy using 1
      dsimp only [Function.comp_apply, OpenPartialHomeomorph.extend_coe]
      change hi.codChart (e.symm (e (C.boundary_neck.coordinate_map
        ((hi.domChart.extend (𝓡 2)).symm y, 0)))) = _
      rw [e.left_inv (C.boundary_param_mem_source e hs _)]
      rfl
  · apply (hsm.continuous.isClosedEmbedding ?_).isEmbedding
    intro p q hpq
    apply C.boundary_neck.centralSphere_isSmoothEmbedding.isEmbedding.injective
    exact e.injOn (C.boundary_param_mem_source e hs p)
      (C.boundary_param_mem_source e hs q) hpq

include ht



theorem range_boundary_param :
    range (fun p : UnitTwoSphere => e (C.boundary_neck.coordinate_map (p, 0))) =
      frontier (e '' C.core) := by
  rw [C.frontier_image_core e hs ht, C.boundary_eq_neck_sphere,
    ← C.boundary_neck.centralSphere_range, ← range_comp]
  rfl

omit hs ht



theorem exists_euclidean_core_boundary_coordinates (hkind : C.model_kind = .euclidean) :
    ∃ e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)),
      e.source = C.carrier ∧ e.target = univ ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target ∧
      Nonempty (Poincare.Manifold.SmoothDomain 3 (e '' C.core)) ∧
      closure (e '' C.core) = e '' C.closed_core ∧
      Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞
        (fun p : UnitTwoSphere => e (C.boundary_neck.coordinate_map (p, 0))) ∧
      range (fun p : UnitTwoSphere => e (C.boundary_neck.coordinate_map (p, 0))) =
        frontier (e '' C.core) := by
  obtain ⟨e, hs, ht, he, hei, hcore, hclosure, _⟩ := C.exists_euclidean_core_coordinates hkind
  exact ⟨e, hs, ht, he, hei, hcore, hclosure,
    C.boundary_param_isSmoothEmbedding e hs he hei, C.range_boundary_param e hs ht⟩

end PoincareConjecture.CapCertificate
