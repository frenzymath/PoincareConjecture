import PoincareConjecture.Proofs.M25.Topology3D.Sphere2.Normalization
import PoincareConjecture.Proofs.M25.Topology3D.Sphere2.CompactPlaneTransfer










set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M25.Topology3D

private instance sphereDimensionFact : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩




theorem diffSphereIsotopyService_of_compactPlanarIsotopyProperty
    (hPlane : CompactPlanarIsotopyProperty) : DiffSphereIsotopyService := by
  intro f
  obtain ⟨v, hv⟩ :=
    (NormedSpace.sphere_nonempty (x := (0 : E3)) (r := 1)).2 zero_le_one
  let p : UnitTwoSphere := ⟨v, hv⟩
  obtain ⟨A, N, k, U, hN, hN0, hN1, hU, hp, hfix⟩ :=
    exists_sphere_pole_normalization p f
  obtain ⟨J, hJ, _, hJ0, hJ1⟩ :=
    exists_sphere_isotopy_of_identity_near_pole hPlane p k hU hp hfix
  let I (t : ℝ) := (J (1 - t)).trans (N t)
  have ha : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun t : ℝ => 1 - t) :=
    (contDiff_const.sub contDiff_id).contMDiff
  have hJrev : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 2) ∞
      (fun q : ℝ × UnitTwoSphere => J (1 - q.1) q.2) :=
    hJ.comp ((ha.comp contMDiff_fst).prodMk contMDiff_snd)
  have hI : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 2) ∞
      (fun q : ℝ × UnitTwoSphere => I q.1 q.2) :=
    hN.comp (contMDiff_fst.prodMk hJrev)
  refine ⟨{
    isometry := A
    isotopy := fun t x => I t x
    isotopy_smooth := hI
    isotopy_diffeo := fun t => ⟨I t, fun _ => rfl⟩
    isotopy_zero := ?_
    isotopy_one := ?_ }⟩
  · intro x
    change N 0 (J (1 - 0) x) = sphereMap A x
    rw [sub_zero, hJ1 1 le_rfl, hN0]
  · intro x
    change N 1 (J (1 - 1) x) = f x
    rw [sub_self, hJ0 0 le_rfl, hN1]

end PoincareConjecture.M25.Topology3D
