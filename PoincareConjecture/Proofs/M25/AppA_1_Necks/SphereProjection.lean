import PoincareConjecture.Proofs.M25.AppA_1_Necks.GraphIsotopy
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.Diffeomorph.Sphere












set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.EpsilonNeck

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}




theorem exists_coordinate_graph_of_slice_projection_localDiffeomorph
    (N N' : EpsilonNeck g) {t : ℝ} (ht : t ∈ Ioo (-N'.epsilon⁻¹) N'.epsilon⁻¹)
    (hsub : ∀ q : UnitTwoSphere, N'.coordinate_map (q, t) ∈ N.carrier)
    (hlocal : IsLocalDiffeomorph (𝓡 2) (𝓡 2) ∞
      (fun q : UnitTwoSphere => (N.coordinate_inverse (N'.coordinate_map (q, t))).1)) :
    ∃ h : UnitTwoSphere → ℝ, ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ h ∧
      (∀ q, h q ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) ∧
      range (fun q => N.coordinate_map (q, h q)) =
        range (fun q => N'.coordinate_map (q, t)) := by
  let : SimplyConnectedSpace UnitTwoSphere :=
    Poincare.Topology.sphereSimplyConnected_of_two_le (n := 2) (by norm_num)
  let F : UnitTwoSphere → UnitTwoSphere :=
    fun q => (N.coordinate_inverse (N'.coordinate_map (q, t))).1
  let e := Poincare.Geometry.Manifold.sphereDiffeomorphOfLocalDiffeomorph
    (n := 0) F hlocal
  have he (q : UnitTwoSphere) : e q = F q := rfl
  let p : UnitTwoSphere → M := fun q => N'.coordinate_map (e.symm q, t)
  have hp : ContMDiff (𝓡 2) (𝓡 3) ∞ p :=
    (N'.coordinate_slice_isSmoothEmbedding ht).contMDiff.comp e.symm.contMDiff
  have hcoord : ContMDiff (𝓡 2) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞
      (fun q => N.coordinate_inverse (p q)) :=
    N.coordinate_inverse_smooth.comp_contMDiff hp (fun q => hsub (e.symm q))
  let h : UnitTwoSphere → ℝ := fun q => (N.coordinate_inverse (p q)).2
  have hh : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ h := contMDiff_snd.comp hcoord
  have hdom (q : UnitTwoSphere) : h q ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ :=
    (N.coordinate_inverse_mem (p q) (hsub (e.symm q))).2
  have hfst (q : UnitTwoSphere) : (N.coordinate_inverse (p q)).1 = q :=
    (he (e.symm q)).symm.trans (e.apply_symm_apply q)
  have hgraph (q : UnitTwoSphere) : N.coordinate_map (q, h q) = p q := by
    calc
      N.coordinate_map (q, h q) = N.coordinate_map (N.coordinate_inverse (p q)) :=
        congrArg N.coordinate_map
          (show (q, h q) = N.coordinate_inverse (p q) from Prod.ext (hfst q).symm rfl)
      _ = p q := N.coordinate_map_coordinate_inverse (hsub (e.symm q))
  refine ⟨h, hh, hdom, ?_⟩
  ext x
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨e.symm q, (hgraph q).symm⟩
  · rintro ⟨q, rfl⟩
    refine ⟨e q, ?_⟩
    change N.coordinate_map (e q, h (e q)) = N'.coordinate_map (q, t)
    rw [hgraph]
    simp only [p, e.symm_apply_apply]




theorem slice_isotopic_of_projection_localDiffeomorph
    (N N' : EpsilonNeck g) {t : ℝ} (ht : t ∈ Ioo (-N'.epsilon⁻¹) N'.epsilon⁻¹)
    (hsub : ∀ q : UnitTwoSphere, N'.coordinate_map (q, t) ∈ N.carrier)
    (hlocal : IsLocalDiffeomorph (𝓡 2) (𝓡 2) ∞
      (fun q : UnitTwoSphere => (N.coordinate_inverse (N'.coordinate_map (q, t))).1)) :
    SmoothSphereIsotopicIn N.carrier N.central_sphere
      (range (fun q => N'.coordinate_map (q, t))) := by
  obtain ⟨h, hsmooth, hdom, hrange⟩ :=
    N.exists_coordinate_graph_of_slice_projection_localDiffeomorph N' ht hsub hlocal
  have hi := N.m25_coordinate_graphs_isotopic (fun _ => 0) h contMDiff_const hsmooth
    (fun _ => N.zero_mem_interval) hdom
  change SmoothSphereIsotopicIn N.carrier (range (fun q => N.coordinate_map (q, 0))) _ at hi
  rwa [N.coordinate_zero_range, hrange] at hi

end PoincareConjecture.EpsilonNeck
