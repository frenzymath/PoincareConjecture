import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.LeafFields.OriginalEdgeCofaceCharts

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

theorem HasOriginalEdgeCofaceCharts.image_of_disjoint_contact_support
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {S C : Set X}
    {K : SimplicialComplex ℝ E} {g : E → X} {a : Finset E}
    (h : HasOriginalEdgeCofaceCharts e S K g a) (G : X ≃ₜ X)
    (hC : IsClosed C)
    (hcontact : Disjoint C ((G '' S) ∩ (g '' convexHull ℝ (a : Set E))))
    (hG : EqOn G id Cᶜ) :
    HasOriginalEdgeCofaceCharts e (G '' S) K g a := by
  have hmem (x : X) (hx : x ∉ C) : x ∈ G '' S ↔ x ∈ S := by
    constructor
    · rintro ⟨y, hy, hyx⟩
      exact G.injective (hyx.trans (hG hx).symm) ▸ hy
    · intro hxs
      exact ⟨x, hxs, hG hx⟩
  intro y hy
  have hyC : y ∉ C := fun hc => disjoint_left.mp hcontact hc hy
  obtain ⟨B, V, F, hB, hyB, hV, hyV, hVB, hF, hFS, hFL, hcofaces⟩ :=
    h y ⟨(hmem y hyC).mp hy.1, hy.2⟩
  let W := V ∩ (B.target ∩ B.symm ⁻¹' Cᶜ)
  refine ⟨B, W, F, hB, hyB,
    hV.inter (B.isOpen_inter_preimage_symm hC.isOpen_compl),
    ⟨hyV, B.mapsTo hyB, ?_⟩, (fun _ hz => hz.2.1), hF, ?_, ?_, hcofaces⟩
  · change B.symm (B y) ∉ C
    simpa only [B.left_inv hyB] using hyC
  · intro z hz
    exact (hmem (B.symm (F z)) hz.2.2).trans (hFS z hz.1)
  · intro z hz
    exact hFL z hz.1

theorem HasOriginalEdgeCofaceCharts.symm_image_of_contact_removal
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {S C w : Set X}
    {K : SimplicialComplex ℝ E} {g : E → X} {a : Finset E} {u v : X}
    (h : HasOriginalEdgeCofaceCharts e S K g a) (F : X ≃ₜ X)
    (hC : IsClosed C) (hF : EqOn F id Cᶜ)
    (hCedge : (g '' convexHull ℝ (a : Set E)) ∩ C ⊆ w)
    (hold : w ∩ S = {u, v})
    (hnew : (g '' convexHull ℝ (a : Set E)) ∩ (F.symm '' S) =
      ((g '' convexHull ℝ (a : Set E)) ∩ S) \ ({u, v} : Set X)) :
    HasOriginalEdgeCofaceCharts e (F.symm '' S) K g a := by
  apply h.image_of_disjoint_contact_support F.symm hC
  · apply disjoint_left.mpr
    rintro x hxC ⟨hxS, hxe⟩
    have hxold := hnew.subset ⟨hxe, hxS⟩
    exact hxold.2 (hold.subset ⟨hCedge ⟨hxe, hxC⟩, hxold.1.2⟩)
  · intro x hx
    apply F.injective
    change F (F.symm x) = F x
    rw [F.apply_symm_apply, hF hx, id_eq]

end PoincareConjecture.M76
