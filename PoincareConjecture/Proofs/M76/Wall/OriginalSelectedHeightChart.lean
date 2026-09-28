import PoincareConjecture.Proofs.M76.Wall.Mathlib.SelectedStarNeighborhood
import PoincareConjecture.Proofs.M76.Wall.Mathlib.OriginalCarrierHeightChart

set_option autoImplicit false

open Set Geometry Geometry.SimplicialComplex

namespace PoincareConjecture.M76

open Classical in

theorem exists_original_selected_height_chart
    {E V X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [TopologicalSpace X]
    (e : ι → OpenPartialHomeomorph X V)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {C W : Set X} (H : C ≃ₜ K.space) (g : E → C)
    (hg : ∀ z : K.space, (g z : X) = (H.symm z : X))
    (F : X → E) (hHF : ∀ y : C, (H y : E) = F y)
    (A : Set E) {f : E → ℝ} (hf : K.AffineOnFaces f)
    (hzero : ∀ v ∈ K.vertices, v ∉ A → f v = 0)
    (hstars : ∀ p ∈ K.vertices, p ∈ A →
      ∃ G : OpenPartialHomeomorph X V,
        MapsTo (fun z => (g z : X)) (K.closedStar p).space G.source ∧
        (K.closedStar p).AffineOnFaces (fun z => G (g z)) ∧
        (∀ i, (e i).symm.trans G ∈ piecewiseAffineGroupoid V) ∧
        G.source ⊆ interior C ∩ W)
    (x : K.space) (hx : f x ≠ 0)
    (hreg : ∀ v ∈ K.vertices, f v ≠ f x) :
    ∃ (b : V →ᴬ[ℝ] ℝ) (w : V) (Q : OpenPartialHomeomorph X V),
      b.contLinear w = 1 ∧ (g x : X) ∈ Q.source ∧ b (Q (g x)) = 0 ∧
      Q.source ⊆ interior C ∩ W ∧ MapsTo F Q.source K.space ∧
      (∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V) ∧
      ∀ y ∈ Q.source, b (Q y) = f (F y) - f x := by
  classical
  obtain ⟨p, hpK, hpA, O, hO, hxO, hOT⟩ :=
    K.exists_selected_star_neighborhood hK hf A hzero x hx
  obtain ⟨G, hsource, hcoord, hcompat, hinside⟩ := hstars p hpK hpA
  let T := K.closedStar p
  have hTK : T ≤ K := fun _ hs => hs.1
  have hxT : (x : E) ∈ T.space := hOT (mem_image_of_mem Subtype.val hxO)
  have hfT : T.AffineOnFaces f := fun s hs => hf s (hTK hs)
  have hregT : ∀ v ∈ T.vertices, f v ≠ f x := fun v hv => hreg v (hTK hv)
  obtain ⟨b, w, Q, hbw, _, hxQ, _, hbQ, hQG, hQF, hQPL, hheight, _, _⟩ :=
    K.exists_original_carrier_height_chart e hK H g hg F hHF T T hTK le_rfl
      x hxT hO hxO hOT G hsource (fun y hy => (hinside hy).1)
      hcoord hcompat hfT hregT 0 (fun _ _ => rfl)
  refine ⟨b, w, Q, hbw, hxQ, hbQ, ?_, ?_, hQPL, hheight⟩
  · exact fun y hy => hinside (hQG hy).1
  · exact fun y hy => space_subset_of_le hTK (hQF hy)

end PoincareConjecture.M76
