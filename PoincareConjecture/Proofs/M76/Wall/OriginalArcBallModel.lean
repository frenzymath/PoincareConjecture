import PoincareConjecture.Proofs.M76.Wall.OriginalStarredArcModel
import PoincareConjecture.Proofs.M76.Wall.OriginalArcExteriorModel
import PoincareConjecture.Proofs.M76.Wall.OriginalArcModelContacts
import PoincareConjecture.Proofs.M76.Wall.OriginalArcDualGeometry
import PoincareConjecture.Proofs.M76.Wall.Mathlib.OrderedIntervalComplex
import PoincareConjecture.Proofs.M76.Wall.Mathlib.ArcDualBallChain











set_option autoImplicit false

open Set Geometry Geometry.SimplicialComplex

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "I" => Icc (0 : ℝ) 1

open Classical in






theorem PLDomain.exists_arc_ball_model
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {L : Set X}
    (he : PLDomain e L) (hL : IsCompact L)
    {q : ℝ → X} (hq : PolyhedralPLInCharts e q I) (hqi : InjOn q I)
    (hzero : q 0 ∈ frontier L) (hone : q 1 ∈ frontier L)
    (hproper : ∀ t ∈ Ioo (0 : ℝ) 1, q t ∉ L)
    {W : Set X} (hW : IsOpen W) (hqW : MapsTo q I W)
    (U : Fin 2 → Set X) (hU : ∀ i, IsOpen (U i))
    (hU0 : q 0 ∈ U 0) (hU1 : q 1 ∈ U 1)
    (S : Fin 2 → Set X) (hsphere : ∀ i, ChartwisePLSphere e (S i))
    (hSL : ∀ i, S i ⊆ frontier L) :
    ∃ (s : Finset (L ∪ q '' I : Set X)) (F : X → (s → ℝ × V3)) (C : Set X)
      (K : SimplicialComplex ℝ (s → ℝ × V3))
      (A : Fin 5 → SimplicialComplex ℝ (s → ℝ × V3))
      (H : C ≃ₜ K.space) (g : (s → ℝ × V3) → C)
      (N : SimplicialComplex ℝ (s → ℝ × V3))
      (Hext : (C \ interior L : Set X) ≃ₜ N.space)
      (v : (s → ℝ × V3) → (C \ interior L : Set X))
      (n : ℕ) (p : Fin (n + 2) → (s → ℝ × V3))
      (hN : N.faces.Finite) (hD : (A 1).faces.Finite),
      let _ : Fintype N.faces := hN.fintype
      let _ : Fintype (A 1).faces := hD.fintype
      IsCompact C ∧ L ∪ q '' I ⊆ interior C ∧ Continuous F ∧
      (∀ i, LocallyPiecewiseAffineOn (F ∘ (e i).symm) (e i).target) ∧
      K.faces.Finite ∧
      (∀ i, A i ≤ K ∧ (A i).faces.Finite ∧
        ∀ t ∈ K.faces, (∀ z ∈ t, z ∈ (A i).vertices) → t ∈ (A i).faces) ∧
      K.space = F '' C ∧ (A 0).space = F '' L ∧
      (A 1).space = F '' frontier L ∧ (A 2).space = F '' (q '' I) ∧
      (A 3).space = F '' S 0 ∧ (A 4).space = F '' S 1 ∧
      (∀ x : C, (H x : s → ℝ × V3) = F x) ∧
      ContinuousOn g K.space ∧
      (∀ z : K.space, (g z : X) = (H.symm z : X)) ∧
      PolyhedralPLInCharts e (fun z => (g z : X)) K.space ∧
      N ≤ K ∧ N.space = F '' (C \ interior L) ∧
      A 1 ≤ N ∧ A 2 ≤ N ∧ A 3 ≤ N ∧ A 4 ≤ N ∧
      (∀ x : (C \ interior L : Set X), (Hext x : s → ℝ × V3) = F x) ∧
      ContinuousOn v N.space ∧
      (∀ z : N.space, (v z : X) = (Hext.symm z : X)) ∧
      PolyhedralPLInCharts e (fun z => (v z : X)) N.space ∧
      (∀ z ∈ N.space, (v z : X) = (g z : X)) ∧
      (∀ t ∈ (A 2).faces, t.card ≤ 2) ∧
      (∀ z ∈ (A 2).vertices, ∃ G : OpenPartialHomeomorph X V3,
        MapsTo (fun y => (g y : X)) (K.closedStar z).space G.source ∧
        (K.closedStar z).AffineOnFaces (fun y => G (g y)) ∧
        (∀ i, (e i).symm.trans G ∈ piecewiseAffineGroupoid V3) ∧
        G.source ⊆ interior C ∩ W ∧
        (G.source ⊆ Lᶜ ∨ ∃ (i : Fin 2) (ell : V3 →L[ℝ] ℝ) (w : V3),
          G.source ⊆ U i ∧ ell w = 1 ∧
          (∀ y ∈ G.source, y ∈ L ↔ 0 ≤ ell (G y)) ∧
          ∀ y ∈ G.source, y ∈ frontier L ↔ ell (G y) = 0)) ∧
      Function.Injective p ∧ p 0 = F (q 0) ∧
      p (Fin.last (n + 1)) = F (q 1) ∧
      (∀ i : Fin (n + 1), {p i.castSucc, p i.succ} ∈ (A 2).faces) ∧
      (A 2).space = ⋃ i : Fin (n + 1), segment ℝ (p i.castSucc) (p i.succ) ∧
      (A 2).vertices = range p ∧
      (A 2).space ∩ (A 1).space = {p 0, p (Fin.last (n + 1))} ∧
      (∀ z ∈ (A 2).vertices, z ∈ (A 1).vertices →
        IsFinitePLBallPair (ℝ × ℝ) ((N.barycentricDualBlock {z}).link z).space
          (((N.barycentricDualBlock {z}).link z).space ∩
            ((A 1).barycentricDualBlock {z}).space) ∧
        IsFinitePLBallPair (ℝ × ℝ) ((A 1).barycentricDualBlock {z}).space
          (((N.barycentricDualBlock {z}).link z).space ∩
            ((A 1).barycentricDualBlock {z}).space)) ∧
      let T := fun i : Fin (n + 2) =>
        ((N.barycentricDualBlock {p i}).link (p i)).space ∪
          ((A 1).barycentricDualBlock {p i}).space
      let J := fun i : Fin (n + 1) => (N.barycentricDualBlock {p i.castSucc, p i.succ}).space
      let Q := fun i : Fin (n + 1) =>
        ((N.barycentricDualBlock {p i.castSucc, p i.succ}).link
          (({p i.castSucc, p i.succ} : Finset (s → ℝ × V3)).centroid ℝ id)).space
      IsFinitePLBallPair ((ℝ × ℝ) × ℝ) (N.barycentricNeighborhood (A 2)).space
          ((⋃ i, T i) \ ⋃ i, J i \ Q i) ∧
        ((A 1).barycentricDualBlock {p 0}).space ⊆ ((⋃ i, T i) \ ⋃ i, J i \ Q i) ∧
        ((A 1).barycentricDualBlock {p (Fin.last (n + 1))}).space ⊆
          ((⋃ i, T i) \ ⋃ i, J i \ Q i) ∧
        (N.barycentricNeighborhood (A 2)).space ∩ (A 1).space =
          ((A 1).barycentricDualBlock {p 0}).space ∪
            ((A 1).barycentricDualBlock {p (Fin.last (n + 1))}).space := by
  classical
  obtain ⟨s, F, C, K, A, H, g, b, hC, hcore, hFc, hFPL, hK, hA,
    hKs, hA0, hA1, hA2, hA3, hA4, hHF, hgc, hg, hgPL, _, hb,
    hdim, hproj, hstars⟩ := he.exists_starred_arc_model hL hq hqi
      hzero hone hproper hW hqW U hU hU0 hU1 S hsphere hSL
  let E := s → ℝ × V3
  have hLC : L ⊆ interior C := fun _ hx => hcore (Or.inl hx)
  have hqC : MapsTo q I (interior C) := fun _ ht => hcore (Or.inr ⟨_, ht, rfl⟩)
  have hFi : InjOn F C := by
    intro x hx y hy hxy
    have heq : H ⟨x, hx⟩ = H ⟨y, hy⟩ := Subtype.ext
      ((hHF ⟨x, hx⟩).trans (hxy.trans (hHF ⟨y, hy⟩).symm))
    exact congrArg Subtype.val (H.injective heq)
  have hgF (x : X) (hx : x ∈ C) : (g (F x) : X) = x := by
    have h := hg (H ⟨x, hx⟩)
    rw [H.symm_apply_apply] at h
    simpa only [hHF] using h
  let B : Fin 2 → SimplicialComplex ℝ E := Fin.cases (A 3) (fun _ => A 4)
  have hBK (i : Fin 2) : B i ≤ K := by
    fin_cases i
    · exact (hA 3).1
    · exact (hA 4).1
  have hB (i : Fin 2) : (B i).space = F '' S i := by
    fin_cases i
    · exact hA3
    · exact hA4
  obtain ⟨N, Hext, v, hNK, hN, hNs, hDN, hAN, hBN,
    hJF, hvc, hv, hvPL, hvg⟩ := exists_original_arc_exterior_model e hC hL.isClosed
      hcore hzero hone hproper S hSL K (A 0) (A 1) (A 2) B hK
      (hA 0).1 (hA 1).1 (hA 2).1 hBK F hFc H g hHF hg hA0 hA1 hA2 hB hproj
  let : Fintype N.faces := hN.fintype
  let : Fintype (A 1).faces := (hA 1).2.1.fintype
  have hB0 : A 3 ≤ N := hBN 0
  have hB1 : A 4 ≤ N := hBN 1
  obtain ⟨_, hcontact0, hq0A, _, hq1A, _⟩ := original_arc_model_contacts
    hL.isClosed (fun _ hx => interior_subset (hLC hx)) hzero hone hproper
    (fun _ ht => interior_subset (hqC ht)) hFi K (A 2) (A 0) (A 1)
    (hA 2).1 (hA 1).1 hA2 hA0 hA1
  obtain ⟨n, p, hpi, hp0, hp1, hedge, hcover, hverts⟩ :=
    (A 2).exists_ordered_edge_chain_of_interval (hA 2).2.1 b
      (by rw [hb]; exact hq0A) (by rw [hb]; exact hq1A)
  have hp0F : p 0 = F (q 0) := hp0.trans (hb _)
  have hp1F : p (Fin.last (n + 1)) = F (q 1) := hp1.trans (hb _)
  have hcontact : (A 2).space ∩ (A 1).space = {p 0, p (Fin.last (n + 1))} := by
    rw [hp0F, hp1F]
    exact hcontact0
  have hfinite : ((A 2).space ∩ (A 1).space).Finite := by
    rw [hcontact]
    exact (finite_singleton _).insert _
  have hgarc : MapsTo (fun z => (v z : X)) (A 2).space (q '' I) := by
    intro z hz
    have hvz := hvg z (space_subset_of_le hAN hz)
    obtain ⟨x, hx, hxz⟩ := hA2.subset hz
    change (v z : X) ∈ q '' I
    rw [hvz, ← hxz, hgF x (interior_subset (hcore (Or.inr hx)))]
    exact hx
  have hstarN : ∀ z ∈ (A 2).vertices, ∃ G : OpenPartialHomeomorph X V3,
      MapsTo (fun y => (v y : X)) (N.closedStar z).space G.source ∧
      (N.closedStar z).AffineOnFaces (fun y => G (v y)) ∧
      G.source ⊆ interior C ∧
      (G.source ⊆ Lᶜ ∨ ∃ (ell : V3 →L[ℝ] ℝ) (w : V3),
        ell w = 1 ∧ ∀ y ∈ G.source, y ∈ L ↔ 0 ≤ ell (G y)) := by
    intro z hz
    obtain ⟨G, hsource, hface, _, hinside, hregion⟩ := hstars z hz
    have hstar : N.closedStar z ≤ K.closedStar z := fun _ ht => ⟨hNK ht.1, hNK ht.2⟩
    have hsub : (N.closedStar z).space ⊆ N.space := space_subset_of_le (fun _ ht => ht.1)
    have haff : (N.closedStar z).AffineOnFaces (fun y => G (g y)) :=
      fun t ht => hface t (hstar ht)
    refine ⟨G, ?_, haff.congr ?_, fun y hy => (hinside hy).1, ?_⟩
    · intro y hy
      change (v y : X) ∈ G.source
      rw [hvg y (hsub hy)]
      exact hsource (space_subset_of_le hstar hy)
    · intro y hy
      exact congrArg G (hvg y (hsub hy)).symm
    · rcases hregion with h | ⟨i, ell, w, _, hw, hhalf, _⟩
      · exact Or.inl h.1
      · exact Or.inr ⟨ell, w, hw, hhalf⟩
  obtain ⟨hballs, hdisks⟩ := original_arc_dual_geometry hL.isClosed hLC
    N (A 2) (A 1) hAN hDN (fun t ht => (hA 1).2.2 t (hNK ht)) hfinite
    F Hext v hJF hv hA1 hzero hone hproper hqC hgarc hstarN
  have hchain := N.isFinitePLBallPair_arc_dual_chain (A 2) (A 1) hAN hDN
    (fun t ht => (hA 2).2.2 t (hNK ht)) (fun t ht => (hA 1).2.2 t (hNK ht))
    p hpi hverts hedge hcover hcontact (fun z hz => (hballs z hz).1)
    (fun t ht hc => (hdisks t ht hc).1)
  refine ⟨s, F, C, K, A, H, g, N, Hext, v, n, p, hN, (hA 1).2.1,
    hC, hcore, hFc, hFPL,
    hK, hA, hKs, hA0, hA1, hA2, hA3, hA4, hHF, hgc, hg, hgPL,
    hNK, hNs, hDN, hAN, hB0, hB1, hJF, hvc, hv, hvPL, hvg, hdim,
    ?_, hpi, hp0F, hp1F, hedge, hcover, hverts, hcontact,
    fun z hz => (hballs z hz).2, hchain⟩
  intro z hz
  obtain ⟨G, hsource, hface, hcompat, hinside, hregion⟩ := hstars z hz
  refine ⟨G, hsource, hface, hcompat, hinside, ?_⟩
  rcases hregion with h | ⟨i, ell, w, hU', hw, hhalf, hfront, _⟩
  · exact Or.inl h.1
  · exact Or.inr ⟨i, ell, w, hU', hw, hhalf, hfront⟩

end PoincareConjecture.M76
