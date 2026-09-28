import PoincareConjecture.Proofs.M76.Wall.OriginalSelectedHeightChart










set_option autoImplicit false

open Set Geometry Geometry.SimplicialComplex

namespace PoincareConjecture.M76

open Classical in





theorem exists_original_relative_height_chart
    {E V X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [TopologicalSpace X]
    (e : ι → OpenPartialHomeomorph X V)
    (K D : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hDK : D ≤ K)
    {C L W : Set X} (hL : IsClosed L) (hLC : L ⊆ C)
    (H : C ≃ₜ K.space) (g : E → C)
    (hg : ∀ z : K.space, (g z : X) = (H.symm z : X))
    (F : X → E) (hHF : ∀ y : C, (H y : E) = F y)
    (hD : D.space = F '' frontier L)
    (A : Set E) {f : E → ℝ} (hf : K.AffineOnFaces f)
    (hzero : ∀ v ∈ K.vertices, v ∉ A → f v = 0)
    (hstars : ∀ p ∈ K.vertices, p ∈ A →
      ∃ G : OpenPartialHomeomorph X V,
        MapsTo (fun z => (g z : X)) (K.closedStar p).space G.source ∧
        (K.closedStar p).AffineOnFaces (fun z => G (g z)) ∧
        (∀ i, (e i).symm.trans G ∈ piecewiseAffineGroupoid V) ∧
        G.source ⊆ interior C ∩ W ∧
        (G.source ⊆ Lᶜ ∨ ∃ (psi : V →ᴬ[ℝ] ℝ) (u : V),
          psi.contLinear u = 1 ∧
          (∀ y ∈ G.source, y ∈ L ↔ 0 ≤ psi (G y)) ∧
          ∀ y ∈ G.source, y ∈ frontier L ↔ psi (G y) = 0))
    (x : K.space) (hxD : (x : E) ∈ D.space) (hx : f x ≠ 0)
    (hreg : ∀ v ∈ K.vertices, f v ≠ f x) :
    ∃ (a b : V →ᴬ[ℝ] ℝ) (u w : V) (Q : OpenPartialHomeomorph X V),
      a.contLinear u = 1 ∧ b.contLinear w = 1 ∧ a.contLinear w = 0 ∧
      (g x : X) ∈ Q.source ∧ a (Q (g x)) = 0 ∧ b (Q (g x)) = 0 ∧
      Q.source ⊆ interior C ∩ W ∧
      (∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V) ∧
      (∀ y ∈ Q.source, b (Q y) = f (F y) - f x) ∧
      (∀ y ∈ Q.source, y ∈ L ↔ 0 ≤ a (Q y)) ∧
      ∀ y ∈ Q.source, y ∈ frontier L ↔ a (Q y) = 0 := by
  classical
  have hgF (y : X) (hy : y ∈ C) : (g (F y) : X) = y := by
    have h := hg (H ⟨y, hy⟩)
    rw [H.symm_apply_apply] at h
    simpa only [hHF] using h
  have hDg : MapsTo (fun z => (g z : X)) D.space (frontier L) := by
    intro z hz
    obtain ⟨y, hy, hyz⟩ := hD.subset hz
    change (g z : X) ∈ frontier L
    rw [← hyz, hgF y (hLC (hL.frontier_subset hy))]
    exact hy
  obtain ⟨p, hpK, hpA, O, hO, hxO, hOT⟩ :=
    K.exists_selected_star_neighborhood hK hf A hzero x hx
  obtain ⟨G, hsource, hcoord, hcompat, hinside, hregion⟩ := hstars p hpK hpA
  let T := K.closedStar p
  have hTK : T ≤ K := fun _ hs => hs.1
  have hxT : (x : E) ∈ T.space := hOT (mem_image_of_mem Subtype.val hxO)
  rcases hregion with hout | ⟨psi, u, hu, hhalf, hfront⟩
  · exact False.elim ((hout (hsource hxT)) (hL.frontier_subset (hDg hxD)))
  let B := T ⊓ D
  have hBT : B ≤ T := inf_le_left
  have hBD : B ≤ D := inf_le_right
  have hxB : (x : E) ∈ B.space := by
    obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hxT
    obtain ⟨t, ht, hxt⟩ := mem_space_iff.mp hxD
    have hxu : (x : E) ∈ convexHull ℝ ((s ∩ t : Finset E) : Set E) := by
      simpa only [Finset.coe_inter] using
        K.inter_subset_convexHull (hTK hs) (hDK ht) ⟨hxs, hxt⟩
    have hne : (s ∩ t).Nonempty :=
      Finset.coe_nonempty.mp (convexHull_nonempty_iff.mp ⟨(x : E), hxu⟩)
    exact mem_space_iff.mpr ⟨s ∩ t,
      ⟨T.down_closed hs Finset.inter_subset_left hne,
        D.down_closed ht Finset.inter_subset_right hne⟩, hxu⟩
  have hpsix : psi (G (g x)) = 0 := (hfront _ (hsource hxT)).mp (hDg hxD)
  have hpsi : ∀ z ∈ B.space, psi (G (g z)) = psi (G (g x)) := by
    intro z hz
    rw [hpsix]
    exact (hfront _ (hsource (space_subset_of_le hBT hz))).mp
      (hDg (space_subset_of_le hBD hz))
  have hfT : T.AffineOnFaces f := fun s hs => hf s (hTK hs)
  have hregT : ∀ v ∈ T.vertices, f v ≠ f x := fun v hv => hreg v (hTK hv)
  obtain ⟨b, w, Q, hbw, hpsiw, hxQ, _, hbQ, hQG, _, hQPL,
    hheight, hpreserve, _⟩ :=
    K.exists_original_carrier_height_chart e hK H g hg F hHF T B hTK hBT
      x hxB hO hxO hOT G hsource (fun y hy => (hinside hy).1)
      hcoord hcompat hfT hregT psi hpsi
  refine ⟨psi, b, u, w, Q, hu, hbw, hpsiw, hxQ, ?_, hbQ,
    (fun y hy => hinside (hQG hy).1), hQPL, hheight, ?_, ?_⟩
  · rw [hpreserve _ hxQ]
    exact hpsix
  · intro y hy
    rw [hpreserve y hy]
    exact hhalf y (hQG hy).1
  · intro y hy
    rw [hpreserve y hy]
    exact hfront y (hQG hy).1

end PoincareConjecture.M76
