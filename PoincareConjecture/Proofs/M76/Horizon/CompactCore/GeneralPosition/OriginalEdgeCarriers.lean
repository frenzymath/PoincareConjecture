import PoincareConjecture.Proofs.M76.Horizon.CompactCore.GeneralPosition.OriginalEdgeHomotopies
import PoincareConjecture.Proofs.M76.Horizon.Polyhedral.Maps.EdgeCarrierPasting










set_option autoImplicit false

open Set Geometry Geometry.SimplicialComplex unitInterval

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

theorem PLDomain.exists_original_edge_carrier_homotopy
    {E X ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X] [Nonempty X] [Finite κ]
    {e : ι → OpenPartialHomeomorph X V3} {N Y F : Set X}
    (hN : PLDomain e N) (hY : IsOpen Y) (hcut : Y ∩ frontier N = F)
    (K : SimplicialComplex ℝ E) (f : E → X) (hfY : MapsTo f K.space Y)
    (a b : κ → K.vertices) (hab : ∀ k, (a k : E) ≠ b k)
    (hedges : ∀ k, {(a k : E), (b k : E)} ∈ K.faces)
    (hinj : Function.Injective (fun k => ({(a k : E), (b k : E)} : Finset E)))
    (B : κ → OpenPartialHomeomorph X V3)
    (hcompat : ∀ k i, (e i).symm.trans (B k) ∈ piecewiseAffineGroupoid V3)
    (hsource : ∀ k, MapsTo f (K.closedStar (a k)).space (B k).source)
    (hcoord : ∀ k, (K.closedStar (a k)).AffineOnFaces (B k ∘ f))
    (U : κ → Set X) (hU : ∀ k, IsOpen (U k)) (hUY : ∀ k, U k ⊆ Y)
    (hfU : ∀ k, MapsTo f (segment ℝ (a k : E) (b k : E)) (U k)) :
    ∃ (T : SimplicialComplex ℝ E) (G : C(I × T.space, X))
      (g : E → X) (p : K.vertices → C(I, X)),
      T.faces.Finite ∧ T ≤ K ∧ T.space = ⋃ k, segment ℝ (a k : E) (b k : E) ∧
      (∀ v, p v 0 = f v) ∧ (∀ v t, p v t ∈ Y) ∧
      (∀ v : K.vertices, f v ∉ F → ∀ t, p v t = f v) ∧
      (∀ v (t : I), 0 < (t : ℝ) → p v t ∉ F) ∧
      (∀ z, G z ∈ Y) ∧
      (∀ k (t s : I) (hx : AffineMap.lineMap (a k : E) (b k : E) (s : ℝ) ∈ T.space),
        G (t, ⟨AffineMap.lineMap (a k : E) (b k : E) (s : ℝ), hx⟩) ∈ U k ∧
        B k (G (t, ⟨AffineMap.lineMap (a k : E) (b k : E) (s : ℝ), hx⟩)) =
          AffineMap.lineMap (B k (p (a k) t)) (B k (p (b k) t)) (s : ℝ)) ∧
      (∀ k (t : I) (ha : (a k : E) ∈ T.space) (hb : (b k : E) ∈ T.space),
        G (t, ⟨a k, ha⟩) = p (a k) t ∧ G (t, ⟨b k, hb⟩) = p (b k) t) ∧
      (∀ x : T.space, G (0, x) = f x) ∧
      (∀ x : T.space, G (1, x) = g x) ∧ PolyhedralPLInCharts e g T.space := by
  obtain ⟨p, H, q, hp0, hpY, hpfix, hpoff, hHU, hend, hstart, hfinal, hPL, hcoords⟩ :=
    hN.exists_original_edge_homotopies hY hcut K f hfY a b hedges B hcompat
      hsource hcoord U hU hfU
  obtain ⟨T, G, g, hT, hTK, hTS, hG, hG0, hG1, hgPL⟩ :=
    exists_edge_carrier_pasting e hN.cover hN.compatible K a b hab hedges hinj f p H
      hend hstart q hfinal hPL
  refine ⟨T, G, g, p, hT, hTK, hTS, hp0, hpY, hpfix, hpoff, ?_, ?_, ?_, hG0, hG1, hgPL⟩
  · rintro ⟨t, x⟩
    obtain ⟨k, hk⟩ := mem_iUnion.mp (hTS.subset x.property)
    rw [segment_eq_image_lineMap] at hk
    obtain ⟨s, hs, heq⟩ := hk
    have hparam : G (t, x) = H k (t, ⟨s, hs⟩) := by
      have hh := hG k t ⟨s, hs⟩ (heq.symm ▸ x.property)
      simpa only [heq] using hh
    rw [hparam]
    exact hUY k (hHU k (t, ⟨s, hs⟩))
  · intro k t s hx
    rw [hG k t s hx]
    exact ⟨hHU k (t, s), hcoords k t s⟩
  · intro k t ha hb
    have hga := hG k t 0 (by simpa using ha)
    have hgb := hG k t 1 (by simpa using hb)
    exact ⟨(by simpa using hga.trans (hend k t).1),
      (by simpa using hgb.trans (hend k t).2)⟩

end PoincareConjecture.M76
