import PoincareConjecture.Proofs.M76.Mathlib.LocallyPiecewiseAffineInverse








set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)



theorem original_PL_motion_trans
    {X ι : Type*} [TopologicalSpace X]
    (e : ι → OpenPartialHomeomorph X V3)
    (hcover : ∀ y, ∃ i, y ∈ (e i).source)
    (F G : X ≃ₜ X)
    (hF : ∀ i j, (e i).symm.trans (F.toOpenPartialHomeomorph.trans (e j)) ∈
      piecewiseAffineGroupoid V3)
    (hG : ∀ i j, (e i).symm.trans (G.toOpenPartialHomeomorph.trans (e j)) ∈
      piecewiseAffineGroupoid V3) :
    ∀ i j, (e i).symm.trans ((F.trans G).toOpenPartialHomeomorph.trans (e j)) ∈
      piecewiseAffineGroupoid V3 := by
  intro i j
  let D := (e i).symm.trans ((F.trans G).toOpenPartialHomeomorph.trans (e j))
  apply (mem_piecewiseAffineGroupoid_iff_forward D).mpr
  apply LocallyPiecewiseAffineOn.locality
  intro x hx
  obtain ⟨k, hk⟩ := hcover (F ((e i).symm x))
  let A := (e i).symm.trans (F.toOpenPartialHomeomorph.trans (e k))
  let B := (e k).symm.trans (G.toOpenPartialHomeomorph.trans (e j))
  have hxA : x ∈ A.source := ⟨hx.1, mem_univ _, hk⟩
  have hcomp := ((mem_piecewiseAffineGroupoid_iff_forward B).mp (hG k j)).comp
    ((mem_piecewiseAffineGroupoid_iff_forward A).mp (hF i k))
  refine ⟨A.source, hxA, ?_⟩
  have hsub : D.source ∩ A.source ⊆ A.source ∩ A ⁻¹' B.source := by
    intro y hy
    have hyk : F ((e i).symm y) ∈ (e k).source := hy.2.2.2
    refine ⟨hy.2, (e k).map_source hyk, mem_univ _, ?_⟩
    change G ((e k).symm ((e k) (F ((e i).symm y)))) ∈ (e j).source
    rw [(e k).left_inv hyk]
    exact hy.1.2.2
  apply (hcomp.mono (D.open_source.inter A.open_source) hsub).congr
  intro y hy
  have hyk : F ((e i).symm y) ∈ (e k).source := hy.2.2.2
  change (e j) (G ((e k).symm ((e k) (F ((e i).symm y))))) =
    (e j) (G (F ((e i).symm y)))
  rw [(e k).left_inv hyk]

end PoincareConjecture.M76
