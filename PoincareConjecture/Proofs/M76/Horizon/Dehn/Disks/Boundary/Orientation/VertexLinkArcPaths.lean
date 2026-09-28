import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Boundary.Orientation.RimArcPaths
import PoincareConjecture.Proofs.M76.Mathlib.BarycentricDualLink
import PoincareConjecture.Proofs.M76.Mathlib.BarycentricDualSubcomplex









set_option autoImplicit false
open Set Geometry Geometry.SimplicialComplex

namespace PoincareConjecture.M76.Dehn

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]



theorem exists_centroid_vertex_rim_homeomorph
    (A : SimplicialComplex ℝ E) [Fintype A.faces] {v : E} (hv : v ∈ A.vertices) :
    ∃ e : (A.link v).space ≃ₜ (A.barycentricSubdivision.link v).space,
      e.IsFinitePL ∧ ∀ (s : Finset E) (hs : s ∈ (A.link v).faces),
        (e ⟨s.centroid ℝ id, (A.link v).convexHull_subset_space hs
          (s.centroid_mem_convexHull ((A.link v).nonempty_of_mem_faces hs))⟩ : E) =
            (insert v s).centroid ℝ id := by
  classical
  obtain ⟨f, e, he, hcent, hvalue⟩ := A.exists_finitePL_barycentricDualLink hv
  have hdom := A.faceLink_singleton_eq_link v
  have hcod : ((A.barycentricDualBlock {v}).link (({v} : Finset E).centroid ℝ id)) =
      A.barycentricSubdivision.link v := by
    rw [Finset.centroid_singleton, id_eq, A.barycentricDualBlock_singleton_eq_closedStar hv]
    ext s
    change ((s ∈ A.barycentricSubdivision.faces ∧
      insert v s ∈ A.barycentricSubdivision.faces) ∧ v ∉ s ∧
      insert v s ∈ A.barycentricSubdivision.faces ∧
      insert v (insert v s) ∈ A.barycentricSubdivision.faces) ↔
      s ∈ A.barycentricSubdivision.faces ∧ v ∉ s ∧
        insert v s ∈ A.barycentricSubdivision.faces
    simp only [Finset.insert_idem]
    tauto
  let e' := (Homeomorph.setCongr (congrArg SimplicialComplex.space hdom).symm).trans
    (e.trans (Homeomorph.setCongr (congrArg SimplicialComplex.space hcod)))
  refine ⟨e', he.setCongr (congrArg SimplicialComplex.space hdom)
    (congrArg SimplicialComplex.space hcod), ?_⟩
  intro s hs
  have hs' : s ∈ (A.faceLink {v}).faces := hdom.symm ▸ hs
  change (e _ : E) = (insert v s).centroid ℝ id
  rw [hvalue]
  change f (s.centroid ℝ id) = (insert v s).centroid ℝ id
  rw [hcent s hs', Finset.singleton_union]



theorem exists_original_triangle_chain_in_vertex_rim_arc
    (A : SimplicialComplex ℝ E) [Fintype A.faces] {v a b : E}
    (hva : v ≠ a) (hvb : v ≠ b) (hab : a ≠ b)
    (ha : {v, a} ∈ A.faces) (hb : {v, b} ∈ A.faces)
    (U V : Set E) (hU : IsClosed U) (hV : IsClosed V)
    (hcover : U ∪ V = (A.barycentricSubdivision.link v).space)
    (hinter : U ∩ V ⊆
      {({v, a} : Finset E).centroid ℝ id, ({v, b} : Finset E).centroid ℝ id})
    (hconn : IsPreconnected U)
    (haU : ({v, a} : Finset E).centroid ℝ id ∈ U)
    (hbU : ({v, b} : Finset E).centroid ℝ id ∈ U) :
    ∃ (n : ℕ) (p : ℕ → E), 0 < n ∧ p 0 = a ∧ p n = b ∧
      InjOn p (Icc 0 n) ∧ (∀ k ≤ n, v ≠ p k) ∧
      ∀ k < n, p k ≠ p (k + 1) ∧ {v, p k, p (k + 1)} ∈ A.faces ∧
        ({v, p k, p (k + 1)} : Finset E).card = 3 ∧
        ({v, p k, p (k + 1)} : Finset E).centroid ℝ id ∈ U := by
  classical
  have hv : v ∈ A.vertices := A.down_closed ha (by simp) (by simp)
  have haL : a ∈ (A.link v).vertices := by
    refine ⟨A.down_closed ha (by simp) (by simp), ?_, ?_⟩
    · simpa only [Finset.mem_singleton] using hva
    · exact ha
  have hbL : b ∈ (A.link v).vertices := by
    refine ⟨A.down_closed hb (by simp) (by simp), ?_, ?_⟩
    · simpa only [Finset.mem_singleton] using hvb
    · exact hb
  obtain ⟨e, _, hcent⟩ := exists_centroid_vertex_rim_homeomorph A hv
  have hca : (e ⟨a, (A.link v).vertices_subset_space haL⟩ : E) =
      ({v, a} : Finset E).centroid ℝ id := by
    simpa only [Finset.centroid_singleton, id_eq] using hcent {a} haL
  have hcb : (e ⟨b, (A.link v).vertices_subset_space hbL⟩ : E) =
      ({v, b} : Finset E).centroid ℝ id := by
    simpa only [Finset.centroid_singleton, id_eq] using hcent {b} hbL
  obtain ⟨n, p, hn, hp0, hpn, hpi, _, hpe⟩ :=
    exists_edge_path_in_homeomorphic_rim_arc (A.link v)
      (finite_link_faces (Set.toFinite A.faces) v) e U V hU hV hcover hconn
      haL hbL hab (hca.symm ▸ haU) (hcb.symm ▸ hbU) (by rwa [hca, hcb])
  have hpv (k : ℕ) (hk : k ≤ n) : p k ∈ (A.link v).vertices := by
    rcases hk.eq_or_lt with h | h
    · simpa only [h, hpn] using hbL
    · exact (A.link v).down_closed (hpe k h).1 (by simp) (by simp)
  have hvp (k : ℕ) (hk : k ≤ n) : v ≠ p k := by
    exact fun h ↦ (hpv k hk).2.1 (Finset.mem_singleton.mpr h)
  refine ⟨n, p, hn, hp0, hpn, hpi, hvp, ?_⟩
  intro k hk
  have hne : p k ≠ p (k + 1) := by
    intro h
    have he := hpi ⟨Nat.zero_le _, hk.le⟩ ⟨Nat.zero_le _, by omega⟩ h
    omega
  have hface := (hpe k hk).1
  have hc := hcent {p k, p (k + 1)} hface
  refine ⟨hne, hface.2.2, ?_, ?_⟩
  · simp [hvp k hk.le, hvp (k + 1) (by omega), hne]
  · rw [← hc]
    apply (hpe k hk).2
    simpa only [Finset.coe_pair] using
      ({p k, p (k + 1)} : Finset E).centroid_mem_convexHull (Finset.insert_nonempty _ _)

end PoincareConjecture.M76.Dehn
