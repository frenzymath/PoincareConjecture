import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Coordinates.PLAtlasTransport
import PoincareConjecture.Proofs.M76.Mathlib.PLHypersurfaceAtlas



set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

theorem PLDomain.of_compatible_cover
    {X ι κ : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {d : κ → OpenPartialHomeomorph X V3}
    {Q : Set X} (hQ : PLDomain e Q)
    (hcover : ∀ x, ∃ j, x ∈ (d j).source)
    (hcompat : ∀ i j, (d i).symm.trans (d j) ∈ piecewiseAffineGroupoid V3)
    (hchange : ∀ i j, (e i).symm.trans (d j) ∈ piecewiseAffineGroupoid V3) :
    PLDomain d Q := by
  refine ⟨hcover,hcompat,hQ.closed,?_⟩
  intro x hx
  obtain ⟨ell,v,B,hv,hxB,hzero,hB,hhalf⟩ := hQ.halfspace x hx
  refine ⟨ell,v,B,hv,hxB,hzero,?_,hhalf⟩
  intro j
  exact OpenPartialHomeomorph.compatible_of_piecewiseAffine_cover e hQ.compatible hQ.cover
    (d j) B (fun i => hchange i j) hB

theorem PLDomain.image_of_original_atlas_move
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {Q : Set X}
    (hQ : PLDomain e Q) (F : X ≃ₜ X)
    (hF : ∀ i j, (e i).symm.trans (F.toOpenPartialHomeomorph.trans (e j)) ∈
      piecewiseAffineGroupoid V3) : PLDomain e (F '' Q) := by
  have h := hQ.preimage_homeomorph F.symm
  rw [←F.image_eq_preimage_symm] at h
  apply h.of_compatible_cover hQ.cover hQ.compatible
  intro i j
  convert hF i j using 1
  apply OpenPartialHomeomorph.ext
  · intro z; rfl
  · intro z; rfl
  · ext z
    simp [Homeomorph.transOpenPartialHomeomorph]

end PoincareConjecture.M76
