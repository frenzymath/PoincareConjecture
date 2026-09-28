import PoincareConjecture.Proofs.M76.Horizon.Polyhedral.Collars.PolygonClosedExteriorCollar








set_option autoImplicit false

open Set unitInterval

namespace Polygon

theorem exists_transported_closed_exterior_collar {X : Type*} [TopologicalSpace X]
    {n : ℕ} (P : Polygon (ℝ × ℝ) (n + 3)) (hP : P.HasSimplicialEdges)
    (hinj : Function.Injective P) (e : X ≃ₜ (ℝ × ℝ)) {s B W : Set X}
    (hs : P.boundary ℝ = e '' s) (hB : B = e.symm '' closure P.inside)
    (hW : IsOpen W) (hsW : s ⊆ W) :
    ∃ c : C(s × I, X), Topology.IsEmbedding c ∧
      (∀ z : s, c (z, 0) = z) ∧ (∀ z, c z ∈ W) ∧
      (∀ (z : s) (t : I), 0 < (t : ℝ) → c (z, t) ∉ B) ∧
      IsCompact (B ∪ range c) ∧ B ⊆ interior (B ∪ range c) ∧
      frontier (B ∪ range c) ⊆ range (fun z : s => c (z, 1)) := by
  let b : s ≃ₜ P.boundary ℝ := (e.image s).trans (Homeomorph.setCongr hs.symm)
  have hb (z : s) : (b z : ℝ × ℝ) = e z := rfl
  obtain ⟨p, hpi, hp0, hpW, hpside, _, hpcompact, _, hpint, hpfront⟩ :=
    P.exists_closed_exterior_collar_inside_with_frontier hP hinj
      (e.isOpenMap _ hW) (hs ▸ image_mono hsW)
  let c : C(s × I, X) := ⟨fun z => e.symm (p (b z.1, z.2)),
    e.symm.continuous.comp (p.continuous.comp
      ((b.continuous.comp continuous_fst).prodMk continuous_snd))⟩
  have hci : Topology.IsEmbedding c := e.symm.isEmbedding.comp
    (hpi.comp (b.prodCongr (Homeomorph.refl I)).isEmbedding)
  have hrange : range c = e.symm '' range p := by
    ext x
    constructor
    · rintro ⟨⟨z, t⟩, rfl⟩
      exact ⟨p (b z, t), mem_range_self _, rfl⟩
    · rintro ⟨y, ⟨⟨z, t⟩, rfl⟩, rfl⟩
      exact ⟨(b.symm z, t), by simp [c]⟩
  have hE : B ∪ range c = e.symm '' (closure P.inside ∪ range p) := by
    rw [hB, hrange, image_union]
  refine ⟨c, hci, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z
    change e.symm (p (b z, 0)) = z
    rw [hp0, hb, e.symm_apply_apply]
  · intro z
    obtain ⟨x, hx, hxe⟩ := hpW (b z.1, z.2)
    change e.symm (p (b z.1, z.2)) ∈ W
    rw [← hxe, e.symm_apply_apply]
    exact hx
  · intro z t ht hx
    rw [hB] at hx
    obtain ⟨y, hy, heq⟩ := hx
    exact hpside (b z) t ht ((e.symm.injective heq) ▸ hy)
  · rw [hE]
    exact hpcompact.image e.symm.continuous
  · rw [hE, hB, ← e.symm.image_interior]
    exact image_mono hpint
  · rw [hE, ← e.symm.image_frontier]
    rintro x ⟨y, hy, rfl⟩
    obtain ⟨z, rfl⟩ := hpfront hy
    exact ⟨b.symm z, by simp [c]⟩

end Polygon
