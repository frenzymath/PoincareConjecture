import PoincareConjecture.Proofs.M76.Triangulation.HamiltonPLDomainMaps
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallImages

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

variable {X Y ι κ : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  {e : ι → OpenPartialHomeomorph X V3}
  {d : κ → OpenPartialHomeomorph Y V3} {R : Set X} {T : Set Y}

theorem ChartwisePLMap.inverse_homeomorph {h : R ≃ₜ T}
    (hh : ChartwisePLMap e d ⟨h, h.continuous⟩) :
    ChartwisePLMap d e ⟨h.symm, h.symm.continuous⟩ := by
  classical
  refine ⟨hh.target_domain, hh.source_domain, isOpen_univ, ?_⟩
  intro y _
  obtain ⟨i, j, J, V, F, hJ, hV, hxV, _, hVi, hVJ, hJt, hJR, hF, hvalue⟩ :=
    hh.coordinates (h.symm y) (mem_univ _)
  let a : V3 → R := fun z =>
    if hz : (e i).symm z ∈ R then ⟨(e i).symm z, hz⟩ else h.symm y
  have haval (z : V3) (hz : z ∈ J.space) : (a z : X) = (e i).symm z := by
    obtain ⟨x, _, hx⟩ := hJR hz
    have hzR : (e i).symm z ∈ R := hx ▸ x.property
    simp only [a, dif_pos hzR]
  have hai (z : V3) (hz : z ∈ J.space) : (a z : X) ∈ (e i).source := by
    rw [haval z hz]
    exact (e i).map_target (hJt hz)
  have hae (z : V3) (hz : z ∈ J.space) : e i (a z) = z := by
    rw [haval z hz, (e i).right_inv (hJt hz)]
  have hFval (z : V3) (hz : z ∈ J.space) :
      (h (a z) : Y) ∈ (d j).source ∧ F z = d j (h (a z)) := by
    have haJ : e i (a z) ∈ J.space := (hae z hz).symm ▸ hz
    have hv := hvalue (a z) (hai z hz) haJ
    change (h (a z) : Y) ∈ (d j).source ∧ F (e i (a z)) = d j (h (a z)) at hv
    rwa [hae z hz] at hv
  have hFinj : InjOn F J.space := by
    intro z hz w hw heq
    have hhw : (h (a z) : Y) = h (a w) :=
      (d j).injOn (hFval z hz).1 (hFval w hw).1
        ((hFval z hz).2.symm.trans (heq.trans (hFval w hw).2))
    have haw : a z = a w := h.injective (Subtype.ext hhw)
    exact (hae z hz).symm.trans
      ((congrArg (fun x : R => e i x) haw).trans (hae w hw))
  obtain ⟨b, hb, hbval⟩ := hF.exists_homeomorph_image hFinj
  obtain ⟨G, hG, hGval⟩ := hb.symm
  have hGF (z : V3) (hz : z ∈ J.space) : G (F z) = z := by
    have hzG := hGval (b ⟨z, hz⟩)
    rw [b.symm_apply_apply] at hzG
    simpa only [hbval] using hzG.symm
  obtain ⟨K, hK, hKspace, hGK⟩ := hG
  let W : Set T := h '' V
  have hW : IsOpen W := h.isOpenMap V hV
  have hyW : y ∈ W := ⟨h.symm y, hxV, h.apply_symm_apply y⟩
  have hWV (v : R) (hv : v ∈ V) :
      (h v : Y) ∈ (d j).source ∧ F (e i v) = d j (h v) :=
    hvalue v (hVi hv) (hVJ ⟨v, hv, rfl⟩)
  refine ⟨j, i, K, W, G, hK, hW, hyW, subset_univ _, ?_, ?_, ?_, ?_,
    hGK.finitePiecewiseAffineOn hK, ?_⟩
  · rintro _ ⟨v, hv, rfl⟩
    exact (hWV v hv).1
  · rintro _ ⟨v, ⟨x, hx, rfl⟩, rfl⟩
    apply hKspace.symm.subset
    exact ⟨e i x, hVJ ⟨x, hx, rfl⟩, (hWV x hx).2⟩
  · intro z hz
    obtain ⟨w, hw, rfl⟩ := hKspace.subset hz
    rw [(hFval w hw).2]
    exact (d j).map_source (hFval w hw).1
  · intro z hz
    obtain ⟨w, hw, rfl⟩ := hKspace.subset hz
    refine ⟨h (a w), mem_univ _, ?_⟩
    rw [(hFval w hw).2, (d j).left_inv (hFval w hw).1]
  · intro y' hyj hyK
    obtain ⟨z, hz, hze⟩ := hKspace.subset hyK
    have hhy : h (a z) = y' :=
      Subtype.ext ((d j).injOn (hFval z hz).1 hyj
        ((hFval z hz).2.symm.trans hze))
    have hay : a z = h.symm y' := by
      rw [← hhy, h.symm_apply_apply]
    refine ⟨hay ▸ hai z hz, ?_⟩
    change G (d j y') = e i (h.symm y')
    rw [← hze, hGF z hz, ← hay, hae z hz]

theorem ChartwisePLMap.chartwisePLHomeomorph {h : R ≃ₜ T}
    (hh : ChartwisePLMap e d ⟨h, h.continuous⟩) :
    ChartwisePLHomeomorph e d h :=
  ⟨hh, hh.inverse_homeomorph⟩

end PoincareConjecture.M76
