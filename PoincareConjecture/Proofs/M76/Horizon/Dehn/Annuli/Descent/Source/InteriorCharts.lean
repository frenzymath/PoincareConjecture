import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Towers.CylinderLift
import PoincareConjecture.Proofs.M76.Rigidity.CenteredHalfspaceCharts
import PoincareConjecture.Proofs.M76.Mathlib.PiecewiseAffineProd

set_option autoImplicit false

open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn.ProtectedAnnulus

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V" => (V1 × V2)

theorem exists_interior_source_chart {x : V} (hx : x ∈ source)
    (hxr : x.1 ∉ sphere (0 : V1) 1) :
    ∃ (H : OpenPartialHomeomorph V V) (B : V →ₗ[ℝ] ℝ),
      x ∈ H.source ∧ H x = 0 ∧ B ≠ 0 ∧
      H.source ⊆ ball (0 : V1) 1 ×ˢ (univ : Set V2) ∧
      LocallyPiecewiseAffineOn H H.source ∧
      LocallyPiecewiseAffineOn H.symm H.target ∧
      ∀ y ∈ H.source, y ∈ source ↔ B (H y) = 0 := by
  obtain ⟨G, B, hxG, hGx, hB, hGPL, hGiPL, _, hrim⟩ :=
    exists_centered_disk_rim_chart hx.2
  have hxball : x.1 ∈ ball (0 : V1) 1 := by
    rw [mem_ball_zero_iff]
    exact lt_of_le_of_ne (mem_closedBall_zero_iff.mp hx.1)
      (fun h ↦ hxr (mem_sphere_zero_iff_norm.mpr h))
  let a : V1 ≃ᴬ[ℝ] V1 := ContinuousAffineEquiv.constVAdd ℝ V1 (-x.1)
  let G' := a.toHomeomorph.toOpenPartialHomeomorph.prod G
  let H := G'.restrOpen (ball (0 : V1) 1 ×ˢ (univ : Set V2))
    (isOpen_ball.prod isOpen_univ)
  let ell : V →ₗ[ℝ] ℝ := B.comp (LinearMap.snd ℝ V1 V2)
  have hG' : G' ∈ piecewiseAffineGroupoid V := piecewiseAffineGroupoid_prod _ _
    ⟨locallyPiecewiseAffineOn_affine a.toContinuousAffineMap isOpen_univ,
      locallyPiecewiseAffineOn_affine a.symm.toContinuousAffineMap isOpen_univ⟩
    ⟨hGPL, hGiPL⟩
  refine ⟨H, ell, ⟨⟨mem_univ _, hxG⟩, hxball, mem_univ _⟩, ?_, ?_,
    fun _ hy ↦ hy.2, hG'.1.mono H.open_source (fun _ hy ↦ hy.1),
    hG'.2.mono H.open_target (fun _ hy ↦ hy.1), ?_⟩
  · change (-x.1 + x.1, G x.2) = (0, 0)
    rw [neg_add_cancel, hGx]
  · intro hell
    apply hB
    apply LinearMap.ext
    intro v
    have h := LinearMap.congr_fun hell ((0 : V1), v)
    exact h
  · intro y hy
    change y.1 ∈ closedBall (0 : V1) 1 ∧ y.2 ∈ sphere (0 : V2) 1 ↔
      B (G y.2) = 0
    exact (and_iff_right (ball_subset_closedBall hy.2.1)).trans (hrim y.2 hy.1.2)

end PoincareConjecture.M76.Dehn.ProtectedAnnulus
