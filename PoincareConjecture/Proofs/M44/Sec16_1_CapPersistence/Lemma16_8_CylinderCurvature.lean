import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Def_CylinderRicciFlow
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma16_8_LocalCurvatureTransport
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma16_8_ComponentExclusion










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M44.CylinderRicciFlow

local notation "E" => EuclideanSpace ℝ (Fin 3)

variable {F : SurgeryFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
  {origin scale : ℝ} {I : Set ℝ} {U : Set C.carrier}
  {e : SurgeryFlowCylinder F C origin scale I U}
  {f : PartialDiffeomorph (𝓡 3) (𝓡 3) E C.carrier ∞}



theorem scalar_eq (G : CylinderRicciFlow e f) (hU : IsOpen U) (hmap : f.target ⊆ U)
    (s : ℝ) (hs : s ∈ I) (x : (⟨f.target, f.open_target⟩ : Opens C.carrier)) :
    (G.flow.connection s).scalarCurvature x =
      (F.connection (origin + s / scale)).scalarCurvature (cylinderTargetTransport e f s hs x) /
        scale := by
  have h := scalar_eq_of_local_homothety (G.flow.connection s) (F.connection (origin + s / scale))
    isOpen_univ (cylinderTargetTransport_smooth e f hmap s hs).contMDiffOn
    (fun y _ => cylinderTargetTransport_invertible e hU f hmap s hs y)
    (inv_pos.mpr e.scale_pos) (fun y _ => G.physical_metric_link s hs y) (mem_univ x)
  rw [div_inv_eq_mul] at h
  exact (eq_div_iff e.scale_pos.ne').mpr h.symm




theorem curvatureTensorNorm_eq
    (G : CylinderRicciFlow e f) (hU : IsOpen U) (hmap : f.target ⊆ U)
    (s : ℝ) (hs : s ∈ I) (x : (⟨f.target, f.open_target⟩ : Opens C.carrier)) :
    (G.flow.connection s).curvatureTensorNorm x =
      (F.connection (origin + s / scale)).curvatureTensorNorm
        (cylinderTargetTransport e f s hs x) / scale := by
  have h := curvatureTensorNorm_eq_of_local_homothety
    (G.flow.connection s) (F.connection (origin + s / scale))
    isOpen_univ (cylinderTargetTransport_smooth e f hmap s hs).contMDiffOn
    (fun y _ => cylinderTargetTransport_invertible e hU f hmap s hs y)
    (inv_pos.mpr e.scale_pos) (fun y _ => G.physical_metric_link s hs y) (mem_univ x)
  rw [div_inv_eq_mul] at h
  exact (eq_div_iff e.scale_pos.ne').mpr h.symm




theorem scalar_evolution_eq
    (P : M44CapPersistencePredecessors.{u}) (G : CylinderRicciFlow e f)
    (hU : IsOpen U) (hmap : f.target ⊆ U) (s : ℝ) (hs : s ∈ I)
    (x : (⟨f.target, f.open_target⟩ : Opens C.carrier)) :
    (G.flow.connection s).laplacian (G.flow.connection s).scalarCurvature x +
        2 * (G.flow.connection s).ricciNormSq x =
      ((F.connection (origin + s / scale)).laplacian
          (F.connection (origin + s / scale)).scalarCurvature (cylinderTargetTransport e f s hs x) +
        2 * (F.connection (origin + s / scale)).ricciNormSq (cylinderTargetTransport e f s hs x)) /
          scale ^ 2 := by
  have h := scalar_evolution_eq_of_local_homothety
    (G.flow.connection s) (F.connection (origin + s / scale))
    isOpen_univ (cylinderTargetTransport_smooth e f hmap s hs).contMDiffOn
    (fun y _ => cylinderTargetTransport_invertible e hU f hmap s hs y)
    (inv_pos.mpr e.scale_pos) (fun y _ => G.physical_metric_link s hs y) (mem_univ x)
    (scalar_smooth_of_predecessors P (G.flow.connection s))
    (scalar_smooth_of_predecessors P (F.connection (origin + s / scale)) _)
  rw [inv_pow, div_inv_eq_mul] at h
  exact (eq_div_iff (sq_pos_of_pos e.scale_pos).ne').mpr h.symm




theorem scalar_evolution_bound
    (P : M44CapPersistencePredecessors.{u}) (G : CylinderRicciFlow e f)
    (hU : IsOpen U) (hmap : f.target ⊆ U) (s : ℝ) (hs : s ∈ I)
    (x : (⟨f.target, f.open_target⟩ : Opens C.carrier)) {L : ℝ}
    (hbound : |(F.connection (origin + s / scale)).laplacian
        (F.connection (origin + s / scale)).scalarCurvature (cylinderTargetTransport e f s hs x) +
      2 * (F.connection (origin + s / scale)).ricciNormSq (cylinderTargetTransport e f s hs x)| ≤
        L * (F.connection (origin + s / scale)).scalarCurvature
          (cylinderTargetTransport e f s hs x) ^ 2) :
    |(G.flow.connection s).laplacian (G.flow.connection s).scalarCurvature x +
      2 * (G.flow.connection s).ricciNormSq x| ≤
        L * (G.flow.connection s).scalarCurvature x ^ 2 := by
  rw [scalar_evolution_eq P G hU hmap s hs x, abs_div, abs_of_nonneg (sq_nonneg scale),
    G.scalar_eq hU hmap s hs x, div_pow, ← mul_div_assoc]
  exact div_le_div_of_nonneg_right hbound (sq_nonneg scale)




theorem physical_collar_plane
    (G : CylinderRicciFlow e f) (hU : IsOpen U) (hmap : f.target ⊆ U)
    (s : ℝ) (hs : s ∈ I) (x : (⟨f.target, f.open_target⟩ : Opens C.carrier)) (K : ℝ)
    (u v : TangentSpace (𝓡 3) x)
    (horth : LeviCivitaData.IsOrthonormalPair (G.flow.metric s) x u v)
    (hmargin : (G.flow.connection s).sectionalCurvature x u v <
      K⁻¹ * (G.flow.connection s).scalarCurvature x) :
    ∃ p q : TangentSpace (𝓡 3) (cylinderTargetTransport e f s hs x),
      LeviCivitaData.IsOrthonormalPair (F.metric (origin + s / scale))
        (cylinderTargetTransport e f s hs x) p q ∧
      (F.connection (origin + s / scale)).sectionalCurvature
          (cylinderTargetTransport e f s hs x) p q <
        K⁻¹ * (F.connection (origin + s / scale)).scalarCurvature
          (cylinderTargetTransport e f s hs x) :=
  exists_collar_plane_of_local_homothety
    (G.flow.connection s) (F.connection (origin + s / scale))
    isOpen_univ (cylinderTargetTransport_smooth e f hmap s hs).contMDiffOn
    (fun y _ => cylinderTargetTransport_invertible e hU f hmap s hs y)
    (inv_pos.mpr e.scale_pos) (fun y _ => G.physical_metric_link s hs y) (mem_univ x)
    K u v horth hmargin




theorem not_component_of_collar
    (P : M44CapPersistencePredecessors.{u}) (G : CylinderRicciFlow e f)
    (hU : IsOpen U) (hmap : f.target ⊆ U) (hconnected : IsPreconnected f.target)
    (s : ℝ) (hs : s ∈ I) (x : (⟨f.target, f.open_target⟩ : Opens C.carrier)) (K : ℝ)
    (u v : TangentSpace (𝓡 3) x)
    (horth : LeviCivitaData.IsOrthonormalPair (G.flow.metric s) x u v)
    (hmargin : (G.flow.connection s).sectionalCurvature x u v <
      K⁻¹ * (G.flow.connection s).scalarCurvature x)
    (y : (⟨f.target, f.open_target⟩ : Opens C.carrier)) :
    ¬ ∃ N : SingularCComponent (F.metric (origin + s / scale))
      (F.connection (origin + s / scale)) K, cylinderTargetTransport e f s hs y ∈ N.carrier := by
  obtain ⟨p, q, horth', hmargin'⟩ := G.physical_collar_plane hU hmap s hs x K u v horth hmargin
  exact not_component_of_collar_plane
    (hconnected.image (e.forward s hs) ((e.forward_smooth s hs).continuousOn.mono hmap))
    (scalar_smooth_of_predecessors P (F.connection (origin + s / scale))).continuous
    (mem_image_of_mem _ x.2) p q horth' hmargin'.le (mem_image_of_mem _ y.2)

end PoincareConjecture.M44.CylinderRicciFlow
