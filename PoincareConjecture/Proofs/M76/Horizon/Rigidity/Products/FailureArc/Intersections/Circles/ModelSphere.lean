import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.TargetMapPasting
import PoincareConjecture.Proofs.M76.Triangulation.PLDiskSurgeryModels
import PoincareConjecture.Proofs.M76.Wall.Mathlib.FinitePLCubeSphereModel
import PoincareConjecture.Proofs.M76.Wall.OriginalFinitePLSphereImage

set_option autoImplicit false
open Set Geometry TriangularRoofModel

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "V3" => (Fin 3 → ℝ)
local notation "P3" => ((ℝ × ℝ) × ℝ)

theorem nonempty_original_sphere_of_standard_disk_maps
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3}
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    {f g : P3 → X}
    (hf : PolyhedralPLInCharts e f (cap 1)) (hg : PolyhedralPLInCharts e g disk)
    (hfi : InjOn f (cap 1)) (hgi : InjOn g disk)
    (hagree : EqOn f g rim) (hinter : (f '' cap 1) ∩ (g '' disk) = f '' rim) :
    Nonempty (ChartwisePLSphere e ((f '' cap 1) ∪ (g '' disk))) := by
  have hcap := isFinitePLBallPair_cap 1
  have hdisk := isFinitePLBallPair_disk
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨C, hC, hCs, _⟩, _⟩, _⟩ := isFinitePLBallPair_cap 1
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨D, hD, hDs, _⟩, _⟩, _⟩ := isFinitePLBallPair_disk
  obtain ⟨k, hk, hkc, hkd⟩ := _root_.Dehn.exists_circle_attachment_map_union he C D hC hD
    (hCs.symm ▸ hf) (hDs.symm ▸ hg)
    (fun _ hx hy => hagree ((cap_inter_disk one_ne_zero).subset
      ⟨hCs.subset hx, hDs.subset hy⟩))
  have hkc' : EqOn k f (cap 1) := hCs ▸ hkc
  have hkd' : EqOn k g disk := hDs ▸ hkd
  have hmix (x y : P3) (hx : x ∈ cap 1) (hy : y ∈ disk)
      (hxy : f x = g y) : x = y := by
    obtain ⟨z, hz, hzx⟩ := hinter.subset ⟨⟨x, hx, rfl⟩, ⟨y, hy, hxy.symm⟩⟩
    have hzx' : z = x := hfi (hcap.1 hz) hx hzx
    have hzy : z = y := hgi (hdisk.1 hz) hy ((hagree hz).symm.trans (hzx.trans hxy))
    exact hzx'.symm.trans hzy
  have hki : InjOn k (cap 1 ∪ disk) := by
    intro x hx y hy hxy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact hfi hx hy ((hkc' hx).symm.trans (hxy.trans (hkc' hy)))
    · exact hmix x y hx hy ((hkc' hx).symm.trans (hxy.trans (hkd' hy)))
    · exact (hmix y x hy hx ((hkc' hy).symm.trans (hxy.symm.trans (hkd' hx)))).symm
    · exact hgi hx hy ((hkd' hx).symm.trans (hxy.trans (hkd' hy)))
  obtain ⟨K, hK, hKs⟩ := C.exists_finite_triangulation_union D hC hD
  have hKunion : K.space = cap 1 ∪ disk := by rw [hKs, hCs, hDs]
  have hkK : PolyhedralPLInCharts e k K.space := by
    simpa only [hKs] using hk
  obtain ⟨H, hH, _, _⟩ := hcap.exists_sphere_model_of_disk_union hdisk
    (cap_inter_disk one_ne_zero)
  have hcv : Convex ℝ (halfBall 1) := by
    rw [halfBall_eq_halfspaces]
    simp only [ofPred_forall]
    exact convex_iInter fun i => (convex_Iic 0).affine_preimage (halfBallForms 1 i)
  obtain ⟨b, hb⟩ := hH.exists_unit_cube_sphere_model
    (isCompact_halfBall (Or.inl rfl)) hcv (interior_halfBall_nonempty (Or.inl rfl))
    (by simp [Module.finrank_prod])
  have hs := exists_chartwisePLSphere_image K hkK (hKunion.symm ▸ hki)
    hKunion.symm.subset b hb
  have himage : k '' (cap 1 ∪ disk) = (f '' cap 1) ∪ (g '' disk) := by
    rw [image_union, image_congr hkc', image_congr hkd']
  exact himage ▸ hs

end PoincareConjecture.M76.Dehn.Annuli
