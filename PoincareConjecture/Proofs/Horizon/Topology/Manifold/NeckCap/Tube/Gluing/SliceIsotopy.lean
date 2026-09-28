import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Tube.Gluing.SliceProjection
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Overlap.GraphIsotopy

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.EpsilonNeck

theorem exists_sphereSlice_graph_and_isotopy :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M} (A B : EpsilonNeck g),
        A.epsilon ≤ ε₀ → B.epsilon ≤ ε₀ →
        ∀ {s : ℝ}, s ∈ Ioo (-B.epsilon⁻¹) B.epsilon⁻¹ →
        (∀ q : UnitTwoSphere, B.coordinate_map (q, s) ∈ A.carrier) →
        ∃ h : UnitTwoSphere → ℝ,
          ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ h ∧
          (∀ q, h q ∈ Ioo (-A.epsilon⁻¹) A.epsilon⁻¹) ∧
          range (fun q : UnitTwoSphere => B.coordinate_map (q, s)) =
            range (fun q : UnitTwoSphere => A.coordinate_map (q, h q)) ∧
          SmoothSphereIsotopicIn A.carrier A.central_sphere
            (range (fun q : UnitTwoSphere => B.coordinate_map (q, s))) := by
  obtain ⟨ε₀, hε₀, hsmall, hprojection⟩ := exists_sphereSlice_projection_diffeomorph.{u}
  refine ⟨ε₀, hε₀, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g A B hA hB s hs hc
  obtain ⟨e, he⟩ := hprojection A B hA hB hs hc
  let h : UnitTwoSphere → ℝ :=
    fun q => (A.coordinate_inverse (B.coordinate_map (e.symm q, s))).2
  have hh : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ h := by
    have hcoord : ContMDiff (𝓡 2) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞
        (fun q => A.coordinate_inverse (B.coordinate_map (e.symm q, s))) := by
      intro q
      exact (A.coordinate_inverse_smooth.contMDiffAt
        (A.carrier_open.mem_nhds (hc (e.symm q)))).comp q
        ((B.sphereSlice_contMDiff hs).comp e.symm.contMDiff q)
    exact contMDiff_snd.comp hcoord
  have hdom (q : UnitTwoSphere) : h q ∈ Ioo (-A.epsilon⁻¹) A.epsilon⁻¹ :=
    (A.coordinate_inverse_mem _ (hc (e.symm q))).2
  have hgraph (q : UnitTwoSphere) :
      A.coordinate_map (q, h q) = B.coordinate_map (e.symm q, s) := by
    have hcoord : (q, h q) = A.coordinate_inverse (B.coordinate_map (e.symm q, s)) := by
      refine Prod.ext ?_ (show h q = _ from rfl)
      rw [← he, e.apply_symm_apply]
    rw [hcoord, A.coordinate_map_coordinate_inverse (hc (e.symm q))]
  have hrange : range (fun q : UnitTwoSphere => B.coordinate_map (q, s)) =
      range (fun q : UnitTwoSphere => A.coordinate_map (q, h q)) := by
    ext x
    constructor
    · rintro ⟨q, rfl⟩
      exact ⟨e q, by simpa only [e.symm_apply_apply] using hgraph (e q)⟩
    · rintro ⟨q, rfl⟩
      exact ⟨e.symm q, (hgraph q).symm⟩
  refine ⟨h, hh, hdom, hrange, ?_⟩
  have hzero (q : UnitTwoSphere) : (0 : ℝ) ∈ Ioo (-A.epsilon⁻¹) A.epsilon⁻¹ :=
    ⟨neg_neg_of_pos (inv_pos.mpr A.epsilon_pos), inv_pos.mpr A.epsilon_pos⟩
  have hisotopy := A.coordinate_graphs_isotopic (fun _ => 0) h contMDiff_const hh hzero hdom
  rwa [A.centralSphere_range, ← hrange] at hisotopy

end PoincareConjecture.EpsilonNeck
