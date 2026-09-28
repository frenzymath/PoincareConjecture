import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Boundary.Orientation.RimArcPaths
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Boundary.Orientation.CofaceSideTransport









set_option autoImplicit false
open Set Geometry AbstractSimplicialComplex
open PreAbstractSimplicialComplex.ModTwoCochains

namespace PoincareConjecture.M76

open Dehn

open Classical in
theorem boundary_coface_signs_through_vertex
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (number : E → ℕ) (hnumber : InjOn number K.vertices)
    (sign : Finset E → ZMod 2)
    (hcancel : ∀ t ∈ K.faces, t.card = 3 → ∀ u ∈ K.faces, u.card = 3 → t ≠ u →
      ∀ s : Finset E, s.card = 2 → s ⊆ t → s ⊆ u →
        (sign t + boundaryFaceParity number t s) +
          (sign u + boundaryFaceParity number u s) = 1)
    {v a b : E} (hva : v ≠ a) (hvb : v ≠ b) (hab : a ≠ b)
    (ha : {v, a} ∈ K.faces) (hb : {v, b} ∈ K.faces)
    (hlink : IsConnected (K.link v).space)
    (t u : Finset E)
    (huniqueA : ∀ q ∈ K.faces, q.card = 3 → {v, a} ⊆ q → q = t)
    (huniqueB : ∀ q ∈ K.faces, q.card = 3 → {v, b} ⊆ q → q = u) :
    (sign t + orderedCofaceParity number t v a) +
      (sign u + orderedCofaceParity number u v b) = 1 := by
  classical
  have haL : a ∈ (K.link v).vertices := by
    refine ⟨K.down_closed ha (by simp) (by simp), ?_, ha⟩
    simpa only [Finset.mem_singleton] using hva
  have hbL : b ∈ (K.link v).vertices := by
    refine ⟨K.down_closed hb (by simp) (by simp), ?_, hb⟩
    simpa only [Finset.mem_singleton] using hvb
  have hKL := K.finite_link_faces hK v
  obtain ⟨n, p, hn, hp0, hpn, hpi, _, hpe⟩ :=
    exists_edge_path_in_closed_vertex_partition (K.link v) hKL (K.link v).space ∅
      ((K.link v).isCompact_space_of_finite hKL).isClosed isClosed_empty
      (union_empty _) (by simp) hlink.isPreconnected haL hbL
      ((K.link v).vertices_subset_space haL) ((K.link v).vertices_subset_space hbL) hab
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hn)
  have hpv (k : ℕ) (hk : k ≤ m + 1) : p k ∈ (K.link v).vertices := by
    rcases hk.eq_or_lt with rfl | hk
    · rw [hpn]
      exact hbL
    · exact (K.link v).down_closed (hpe k hk).1 (by simp) (by simp)
  have hvp (k : ℕ) (hk : k ≤ m + 1) : v ≠ p k := by
    intro h
    exact (hpv k hk).2.1 (Finset.mem_singleton.mpr h)
  have hpp (k : ℕ) (hk : k ≤ m) : p k ≠ p (k + 1) := by
    intro h
    have hi := hpi ⟨Nat.zero_le _, by omega⟩ ⟨Nat.zero_le _, by omega⟩ h
    omega
  let tri (k : ℕ) : Finset E := {v, p k, p (k + 1)}
  have htri (k : ℕ) (hk : k ≤ m) : tri k ∈ K.faces ∧ (tri k).card = 3 := by
    refine ⟨(hpe k (by omega)).1.2.2, ?_⟩
    simp [tri, hvp k (by omega), hvp (k + 1) (by omega), hpp k hk]
  have hlabels (k : ℕ) (hk : k ≤ m) : number v ≠ number (p k) ∧
      number v ≠ number (p (k + 1)) ∧ number (p k) ≠ number (p (k + 1)) := by
    have hv : v ∈ K.vertices := K.down_closed (htri k hk).1 (by simp [tri]) (by simp)
    have hk0 : p k ∈ K.vertices := K.down_closed (htri k hk).1 (by simp [tri]) (by simp)
    have hk1 : p (k + 1) ∈ K.vertices := K.down_closed (htri k hk).1 (by simp [tri]) (by simp)
    exact ⟨fun h => hvp k (by omega) (hnumber hv hk0 h),
      fun h => hvp (k + 1) (by omega) (hnumber hv hk1 h),
      fun h => hpp k hk (hnumber hk0 hk1 h)⟩
  have hcross (k : ℕ) (hk : k < m) :
      (sign (tri k) + boundaryFaceParity number (tri k) {v, p (k + 1)}) +
        (sign (tri (k + 1)) + boundaryFaceParity number (tri (k + 1)) {v, p (k + 1)}) = 1 := by
    have hne : tri k ≠ tri (k + 1) := by
      intro heq
      have hp : p k ∈ tri (k + 1) := heq ▸ (by simp [tri])
      simp only [tri, Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with hp | hp | hp
      · exact hvp k (by omega) hp.symm
      · exact hpp k (by omega) hp
      · have hi := hpi ⟨Nat.zero_le _, by omega⟩ ⟨Nat.zero_le _, by omega⟩ hp
        omega
    exact hcancel _ (htri k (by omega)).1 (htri k (by omega)).2
      _ (htri (k + 1) (by omega)).1 (htri (k + 1) (by omega)).2 hne
      _ (by simp [hvp (k + 1) (by omega)]) (by simp [tri]) (by simp [tri])
  have ht : tri 0 = t := huniqueA _ (htri 0 (by omega)).1
    (htri 0 (by omega)).2 (by simp [tri, hp0])
  have hu : tri m = u := huniqueB _ (htri m le_rfl).1
    (htri m le_rfl).2 (by simp [tri, hpn])
  have h := orderedCofaceParity_chain_of_label_ne number v p tri (fun k => sign (tri k)) m
    (fun _ _ => rfl) hlabels hcross
  simpa only [ht, hu, hp0, hpn] using h

end PoincareConjecture.M76
