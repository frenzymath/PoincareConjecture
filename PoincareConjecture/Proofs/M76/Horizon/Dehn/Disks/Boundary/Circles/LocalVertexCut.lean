import PoincareConjecture.Proofs.M76.Dehn.Mathlib.SurfaceVertexDualDisk
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLProperArcCut
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLCircleArcs
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLMarkedInterval

set_option autoImplicit false
open Set Geometry Geometry.SimplicialComplex

namespace PoincareConjecture.M76.Dehn

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]

theorem exists_boundary_circle_vertex_cut
    (A L : SimplicialComplex ℝ E) [Fintype A.faces] [Fintype L.faces]
    (hLA : L ≤ A)
    (hpure : ∀ s ∈ A.faces, ∃ t ∈ A.faces, t.card = 3 ∧ s ⊆ t)
    (hcofaces : ∀ s ∈ A.faces, s.card = 2 →
      {t : Finset E | t ∈ A.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2)
    (hLcard : ∀ s ∈ L.faces, s.card ≤ 2)
    {p : E} (hp : p ∈ L.vertices) (hlink : IsConnected (A.link p).space)
    (s : Bool → Finset E) (hs : ∀ j, s j ∈ L.faces)
    (hsc : ∀ j, (s j).card = 2) (hps : ∀ j, p ∈ s j)
    (hsne : s false ≠ s true)
    (hexhaust : ∀ t ∈ L.faces, p ∈ t → t.card = 2 → t = s false ∨ t = s true) :
    let V := (A.barycentricDualBlock {p}).space
    let W := (A.barycentricSubdivision.link p).space
    let Z := V ∩ L.space
    let c := fun j => (s j).centroid ℝ id
    c false ≠ c true ∧
      IsFinitePLBallPair (ℝ × ℝ) V W ∧
      IsFinitePLBallPair ℝ Z {c false, c true} ∧
      Z ∩ W = {c false, c true} ∧
      (∃ z : Icc (0 : ℝ) 1 ≃ₜ Z, z.IsFinitePL ∧
        (z ⟨0, le_rfl, zero_le_one⟩ : E) = c false ∧
        (z ⟨1, zero_le_one, le_rfl⟩ : E) = c true) ∧
      ∃ U₀ U₁ H₀ H₁ : Set E,
        IsFinitePLBallPair ℝ U₀ {c false, c true} ∧
        IsFinitePLBallPair ℝ U₁ {c false, c true} ∧
        U₀ ∪ U₁ = W ∧ U₀ ∩ U₁ = {c false, c true} ∧
        IsFinitePLBallPair (ℝ × ℝ) H₀ (U₀ ∪ Z) ∧
        IsFinitePLBallPair (ℝ × ℝ) H₁ (Z ∪ U₁) ∧
        H₀ ∪ H₁ = V ∧ H₀ ∩ H₁ = Z ∧
        H₀ ∩ W = U₀ ∧ H₁ ∩ W = U₁ := by
  classical
  have hpA : p ∈ A.vertices := hLA hp
  have hball := A.isFinitePLBallPair_barycentricDualBlock_vertex hpure hcofaces hpA hlink
  have hsub (j : Bool) : ({p} : Finset E) ⊆ s j :=
    Finset.singleton_subset_iff.mpr (hps j)
  have hexhaust' (t : Finset E) (ht : t ∈ L.faces)
      (hpt : ({p} : Finset E) ⊆ t) (htc : t.card = 2) :
      t = s false ∨ t = s true :=
    hexhaust t ht (hpt (Finset.mem_singleton_self p)) htc
  have hbase := (L.isFinitePLBallPair_barycentricDualBlock_of_paired_facet
    (n := 1) hLcard hp (hs false) (hs true) (Finset.card_singleton p)
    (hsc false) (hsc true) (hsub false) (hsub true) hsne hexhaust').1
  have hZeq := A.barycentricDualBlock_space_inter_subcomplex L hLA {p}
  have hinter : (L.barycentricDualBlock {p}).space ∩
      (A.barycentricSubdivision.link p).space =
      {(s false).centroid ℝ id, (s true).centroid ℝ id} := by
    have hblocks : L.barycentricDualBlock {p} ≤ A.barycentricSubdivision :=
      (A.barycentricDualBlock_mono_of_subcomplex L hLA {p}).trans
        (A.barycentricDualBlock_le {p})
    have hstar : (L.barycentricDualBlock {p}).closedStar p =
        L.barycentricDualBlock {p} := by
      simpa only [Finset.centroid_singleton, id_eq] using
        L.barycentricDualBlock_closedStar_faceCentroid hp
    rw [← link_space_eq_inter_of_closedStar_eq _ _ hblocks p hstar]
    simpa only [Finset.centroid_singleton, id_eq] using
      L.barycentricDualBlock_link_space_of_paired_facet (n := 1) hLcard hp
        (hs false) (hs true) (Finset.card_singleton p) (hsc false) (hsc true)
        (hsub false) (hsub true) hexhaust'
  have hne : (s false).centroid ℝ id ≠ (s true).centroid ℝ id := by
    intro h
    exact hsne (congrArg Subtype.val (L.faceCentroid_injective
      (a₁ := ⟨s false, hs false⟩) (a₂ := ⟨s true, hs true⟩) h))
  have ha := (hinter.symm.subset (Or.inl rfl)).2
  have hb := (hinter.symm.subset (Or.inr rfl)).2
  obtain ⟨U₀, U₁, hU₀, hU₁, hU, hUi⟩ := hball.exists_boundary_arcs ha hb hne
  have hproper : (L.barycentricDualBlock {p}).space \
        {(s false).centroid ℝ id, (s true).centroid ℝ id} ⊆
      (A.barycentricDualBlock {p}).space \ (A.barycentricSubdivision.link p).space := by
    intro x hx
    exact ⟨space_subset_of_le (A.barycentricDualBlock_mono_of_subcomplex L hLA {p}) hx.1,
      fun h => hx.2 (hinter.subset ⟨hx.1, h⟩)⟩
  obtain ⟨H₀, H₁, hH₀, hH₁, hH, hHi, hHW₀, hHW₁⟩ :=
    hball.exists_proper_arc_cut hU₀ hU₁ hbase hne hUi.subset hU hproper
  dsimp only
  rw [hZeq]
  exact ⟨hne, hball, hbase, hinter, hbase.exists_unitInterval_chart_with_endpoints hne,
    U₀, U₁, H₀, H₁, hU₀, hU₁, hU, hUi, hH₀, hH₁, hH, hHi, hHW₀, hHW₁⟩

end PoincareConjecture.M76.Dehn
