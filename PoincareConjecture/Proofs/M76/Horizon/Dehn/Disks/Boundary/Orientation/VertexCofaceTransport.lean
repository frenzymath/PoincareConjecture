import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Boundary.Orientation.VertexLinkArcPaths
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Boundary.Orientation.GeometricCofaceSigns









set_option autoImplicit false
open Set Geometry Geometry.SimplicialComplex AbstractSimplicialComplex

namespace PoincareConjecture.M76.Dehn

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]



theorem vertex_rim_arc_coface_sign_eq
    (A : SimplicialComplex ℝ E) [Fintype A.faces]
    (number : E → ℕ) (sign : Finset E → ZMod 2) (hnumber : InjOn number A.vertices)
    (hcancel : ∀ t ∈ A.faces, t.card = 3 → ∀ u ∈ A.faces, u.card = 3 → t ≠ u →
      ∀ s : Finset E, s.card = 2 → s ⊆ t → s ⊆ u →
        (sign t + boundaryFaceParity number t s) +
          (sign u + boundaryFaceParity number u s) = 1)
    (v : E) (p : Bool → E) (hvp : ∀ j, v ≠ p j) (hpne : p false ≠ p true)
    (hedge : ∀ j, {v, p j} ∈ A.faces)
    (arc : Bool → Set E) (hclosed : ∀ b, IsClosed (arc b))
    (hconnected : ∀ b, IsPreconnected (arc b))
    (hcover : arc false ∪ arc true = (A.barycentricSubdivision.link v).space)
    (hinter : arc false ∩ arc true =
      {({v, p false} : Finset E).centroid ℝ id, ({v, p true} : Finset E).centroid ℝ id})
    (hend : ∀ j b, ({v, p j} : Finset E).centroid ℝ id ∈ arc b)
    (t : Bool → Bool → Finset E)
    (hexhaust : ∀ j u, u ∈ A.faces → u.card = 3 → {v, p j} ⊆ u →
      u = t j false ∨ u = t j true)
    (htarc : ∀ j b, (t j b).centroid ℝ id ∈ arc b) :
    ∀ b, sign (t false b) + orderedCofaceParity number (t false b) (p false) v =
      sign (t true b) + orderedCofaceParity number (t true b) v (p true) := by
  classical
  have hedgecard (j : Bool) : ({v, p j} : Finset E).card = 2 := Finset.card_pair (hvp j)
  have hnot (u : Finset E) (hu : u ∈ A.faces) (huc : u.card = 3) :
      u.centroid ℝ id ∉
        ({({v, p false} : Finset E).centroid ℝ id,
          ({v, p true} : Finset E).centroid ℝ id} : Set E) := by
    rintro (h | h)
    · have he := congrArg Subtype.val (A.faceCentroid_injective
        (a₁ := ⟨u, hu⟩) (a₂ := ⟨{v, p false}, hedge false⟩) h)
      have hc := congrArg Finset.card he
      rw [huc, hedgecard] at hc
      omega
    · have he := congrArg Subtype.val (A.faceCentroid_injective
        (a₁ := ⟨u, hu⟩) (a₂ := ⟨{v, p true}, hedge true⟩) h)
      have hc := congrArg Finset.card he
      rw [huc, hedgecard] at hc
      omega
  have hunique (j b : Bool) (u : Finset E) (hu : u ∈ A.faces)
      (huc : u.card = 3) (hsu : {v, p j} ⊆ u) (hU : u.centroid ℝ id ∈ arc b) :
      u = t j b := by
    rcases hexhaust j u hu huc hsu with h | h
    · cases b
      · exact h
      · exfalso
        exact hnot u hu huc (hinter ▸ ⟨h.symm ▸ htarc j false, hU⟩)
    · cases b
      · exfalso
        exact hnot u hu huc (hinter ▸ ⟨hU, h.symm ▸ htarc j true⟩)
      · exact h
  intro b
  have hcover' : arc b ∪ arc (!b) = (A.barycentricSubdivision.link v).space := by
    cases b
    · exact hcover
    · simpa only [Bool.not_true, union_comm] using hcover
  have hinter' : arc b ∩ arc (!b) ⊆
      {({v, p false} : Finset E).centroid ℝ id,
        ({v, p true} : Finset E).centroid ℝ id} := by
    cases b
    · exact hinter.subset
    · simpa only [Bool.not_true, inter_comm] using hinter.subset
  obtain ⟨n, q, hn, hq0, hqn, hqi, hvq, hqtri⟩ :=
    exists_original_triangle_chain_in_vertex_rim_arc A (hvp false) (hvp true) hpne
      (hedge false) (hedge true) (arc b) (arc (!b)) (hclosed b) (hclosed (!b))
      hcover' hinter' (hconnected b) (hend false b) (hend true b)
  let m := n - 1
  have hm : m + 1 = n := by dsimp [m]; omega
  let tri : ℕ → Finset E := fun k ↦ {v, q k, q (k + 1)}
  have hvm : v ∈ A.vertices := A.down_closed (hedge false) (by simp) (by simp)
  have hqv (k : ℕ) (hk : k ≤ n) : q k ∈ A.vertices := by
    rcases hk.eq_or_lt with h | h
    · rw [h, hqn]
      exact A.down_closed (hedge true) (by simp) (by simp)
    · exact A.down_closed (hqtri k h).2.1 (by simp) (by simp)
  have hlabels (k : ℕ) (hk : k ≤ m) : number v ≠ number (q k) ∧
      number v ≠ number (q (k + 1)) ∧ number (q k) ≠ number (q (k + 1)) := by
    have hk' : k < n := by omega
    exact ⟨fun h ↦ hvq k hk'.le (hnumber hvm (hqv k hk'.le) h),
      fun h ↦ hvq (k + 1) (by omega) (hnumber hvm (hqv (k + 1) (by omega)) h),
      fun h ↦ (hqtri k hk').1 (hnumber (hqv k hk'.le) (hqv (k + 1) (by omega)) h)⟩
  have hstep (k : ℕ) (hk : k < m) :
      (sign (tri k) + boundaryFaceParity number (tri k) {v, q (k + 1)}) +
        (sign (tri (k + 1)) + boundaryFaceParity number (tri (k + 1)) {v, q (k + 1)}) =
        1 := by
    have hne : tri k ≠ tri (k + 1) := by
      intro h
      have hq : q k ∈ tri (k + 1) := h ▸
        (show q k ∈ tri k by simp only [tri, Finset.mem_insert, Finset.mem_singleton]; tauto)
      simp only [tri, Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with hq | hq | hq
      · exact hvq k (by omega) hq.symm
      · have he := hqi ⟨Nat.zero_le _, by omega⟩ ⟨Nat.zero_le _, by omega⟩ hq
        omega
      · have he := hqi ⟨Nat.zero_le _, by omega⟩ ⟨Nat.zero_le _, by omega⟩ hq
        omega
    exact hcancel (tri k) (hqtri k (by omega)).2.1 (hqtri k (by omega)).2.2.1
      (tri (k + 1)) (hqtri (k + 1) (by omega)).2.1 (hqtri (k + 1) (by omega)).2.2.1
      hne {v, q (k + 1)} (Finset.card_pair (hvq (k + 1) (by omega)))
      (by simp [tri]) (by simp [tri])
  have hsign := orderedCofaceParity_through_vertex_of_label_ne number v q tri
    (fun k ↦ sign (tri k)) m (fun _ _ ↦ rfl) hlabels hstep
  have hfirst : tri 0 = t false b := by
    apply hunique false b _ (hqtri 0 hn).2.1 (hqtri 0 hn).2.2.1
    · simp [hq0]
    · exact (hqtri 0 hn).2.2.2
  have hlast : tri m = t true b := by
    have hmn : m < n := by omega
    apply hunique true b _ (hqtri m hmn).2.1 (hqtri m hmn).2.2.1
    · simp [hm, hqn]
    · exact (hqtri m hmn).2.2.2
  simpa only [hfirst, hlast, hq0, hm, hqn] using hsign

end PoincareConjecture.M76.Dehn
