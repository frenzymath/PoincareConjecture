import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Surgery.Counts.CompressionCylinderEulerCount
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Surgery.Counts.FinitePLImageFaceBounds
import PoincareConjecture.Proofs.M76.Rigidity.OriginalProductCut
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLInverse
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Mathlib.PLSurfaceCount

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.OriginalDiskProduct

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1
local notation "J" => Icc (-(1 / 2 : ℝ)) (1 / 2)

theorem annulus_image_surfaceEulerCount
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {L N : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e L j) (phi : X → E)
    (hphiPL : ∀ i, LocallyPiecewiseAffineOn (phi ∘ (e i).symm) (e i).target)
    (hphi : InjOn phi N) (hstrip : P.closedStrip ⊆ N)
    (Annulus : SimplicialComplex ℝ E) (hAnnulus : Annulus.faces.Finite)
    (hspace : Annulus.space = phi '' (P.map '' (Q ×ˢ J))) :
    Annulus.surfaceEulerCount = 0 := by
  choose C hC hCs using CompressionCylinder.exists_side_complex
  obtain ⟨Cylinder, hCylinder, hCylinders, _⟩ :=
    Geometry.SimplicialComplex.exists_finite_triangulation_iUnion C hC
  have hCylinderEq : Cylinder.space = Q ×ˢ J := by
    rw [hCylinders]
    simp only [hCs]
    simpa only [CompressionCylinder.carrier, neg_div] using CompressionCylinder.iUnion_side
  have hfull : Cylinder.space ⊆ D ×ˢ Icc (-1 : ℝ) 1 := by
    rw [hCylinderEq]
    intro z hz
    exact ⟨sphere_subset_closedBall hz.1, by linarith [hz.2.1], by linarith [hz.2.2]⟩
  have hmapstrip (z) (hz : z ∈ Cylinder.space) : P.map z ∈ P.closedStrip := by
    have hz' := hCylinderEq.subset hz
    exact mem_image_of_mem P.map ⟨sphere_subset_closedBall hz'.1, hz'.2⟩
  have hf := (P.polyhedral.restrict_finite Cylinder hCylinder hfull).finitePiecewiseAffineOn_comp
    Cylinder hCylinder hphiPL
  have hinj : InjOn (phi ∘ P.map) Cylinder.space := by
    intro x hx y hy hxy
    exact P.injective (hfull hx) (hfull hy)
      (hphi (hstrip (hmapstrip x hx)) (hstrip (hmapstrip y hy)) hxy)
  have himage : (phi ∘ P.map) '' Cylinder.space = Annulus.space := by
    rw [hspace, hCylinderEq, image_image]
    rfl
  have hdim : ∀ s ∈ Cylinder.faces, s.card ≤ 3 :=
    CompressionCylinder.face_card_le_three Cylinder (by
      simpa only [CompressionCylinder.carrier, neg_div] using hCylinderEq.subset)
  have htargetdim := hf.face_card_le_of_image hCylinder hdim Annulus himage.symm.subset
  have hcount : Cylinder.surfaceEulerCount = 0 :=
    CompressionCylinder.surfaceEulerCount_eq_zero Cylinder hCylinder (by
      simpa only [neg_div] using hCylinderEq)
  exact (hf.surfaceEulerCount_eq_of_injOn hCylinder hAnnulus hdim htargetdim
    hinj himage).symm.trans hcount

end PoincareConjecture.M76.OriginalDiskProduct
