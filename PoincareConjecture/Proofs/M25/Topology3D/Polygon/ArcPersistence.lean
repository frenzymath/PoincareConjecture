import PoincareConjecture.Proofs.M25.Topology3D.Polygon.ArcPush
import PoincareConjecture.Proofs.M25.Topology3D.Plane.TrianglePersistence
import Mathlib.Order.Filter.Finite










set_option autoImplicit false

open Set Filter
open scoped Topology

namespace PoincareConjecture.M25.Topology3D

variable {E Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace Z] {n : ℕ} {p : Z → Polygon E (n + 2)} {z0 : Z}



theorem IsSimplePolygonalArc.eventually_isAdmissibleArcVertex
    (hp : IsSimplePolygonalArc (p z0)) (k : Fin (n + 2))
    (had : IsAdmissibleArcVertex (p z0) k)
    (hc : ∀ i, ContinuousAt (fun z => p z i) z0) :
    ∀ᶠ z in 𝓝 z0, IsAdmissibleArcVertex (p z) k := by
  classical
  let a := (finRotate (n + 2)).symm k
  let b := finRotate (n + 2) k
  let arms (z : Z) := segment ℝ (p z k) (p z a) ∪ segment ℝ (p z k) (p z b)
  obtain ⟨i, j, hik, hjk, hip, hjs, _⟩ :=
    exists_arc_incident_edge_indices k had.1 had.2.1
  have ha : i.castSucc = a := hip
  have hb : j.succ = b := hjs
  have hav : a.val + 1 = k.val := by rw [← ha, ← hik]; rfl
  have hbv : b.val = k.val + 1 := by rw [← hb, ← hjk]; rfl
  have hak : a ≠ k := by intro h; have hh := congrArg Fin.val h; omega
  have hbk : b ≠ k := by intro h; have hh := congrArg Fin.val h; omega
  have hab : a ≠ b := by intro h; have hh := congrArg Fin.val h; omega
  have hpointa : p z0 a ∉ segment ℝ (p z0 k) (p z0 b) := by
    intro h
    have he : p z0 a ∈ (p z0).edgeSet ℝ j.castSucc := by
      rw [polygon_arcEdge_eq_segment, hjk, hb]
      exact h
    have hh := (hp.vertex_mem_edgeSet_iff a j).mp he
    rw [hjk, hb] at hh
    exact hh.elim hak hab
  have hpointb : p z0 b ∉ segment ℝ (p z0 k) (p z0 a) := by
    intro h
    have he : p z0 b ∈ (p z0).edgeSet ℝ i.castSucc := by
      rw [polygon_arcEdge_eq_segment, ha, hik, segment_symm]
      exact h
    have hh := (hp.vertex_mem_edgeSet_iff b i).mp he
    rw [ha, hik] at hh
    exact hh.elim (Ne.symm hab) hbk
  have hattach (s t o : Fin (n + 2))
      (horder : (s = a ∧ t = b) ∨ (s = b ∧ t = a)) (hso : s ≠ o)
      (hcontact : polygonVertexTriangle (p z0) k ∩
        segment ℝ (p z0 s) (p z0 o) ⊆ {p z0 s}) :
      ∀ᶠ z in 𝓝 z0, polygonVertexTriangle (p z) k ∩
        segment ℝ (p z s) (p z o) ⊆ arms z := by
    have htri (z : Z) : convexHull ℝ {p z s, p z k, p z t} =
        polygonVertexTriangle (p z) k := by
      change convexHull ℝ {p z s, p z k, p z t} = convexHull ℝ {p z k, p z a, p z b}
      congr 1
      rcases horder with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        ext x <;> simp only [mem_insert_iff, mem_singleton_iff] <;> tauto
    have hpoint : p z0 s ∉ segment ℝ (p z0 k) (p z0 t) := by
      rcases horder with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hpointa
      · exact hpointb
    have hh := eventually_triangle_inter_attached_segment_subset
      (hc s) (hc k) (hc t) (hc o) hpoint
      (fun h => hso (hp.vertices_injective h)) (by rw [htri]; exact hcontact)
    filter_upwards [hh] with z hz
    intro x hx
    have hxs : x = p z s := hz (by rw [htri]; exact hx)
    rw [hxs]
    rcases horder with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · exact Or.inl (right_mem_segment ℝ _ _)
    · exact Or.inr (right_mem_segment ℝ _ _)
  have hevent (l : Fin (n + 1)) :
      ∀ᶠ z in 𝓝 z0, polygonVertexTriangle (p z) k ∩
        (p z).edgeSet ℝ l.castSucc ⊆ arms z := by
    by_cases hlk : l.castSucc = k
    · have hlj : l = j := by
        have hh := congrArg Fin.val (hlk.trans hjk.symm)
        exact Fin.ext hh
      filter_upwards [] with z
      intro x hx
      apply Or.inr
      have hh := hx.2
      rw [hlj, polygon_arcEdge_eq_segment, hjk, hb] at hh
      exact hh
    by_cases hls : l.succ = k
    · have hli : l = i := by
        apply Fin.ext
        have hh := congrArg Fin.val (hls.trans hik.symm)
        simpa only [Fin.val_succ, Nat.add_right_cancel_iff] using hh
      filter_upwards [] with z
      intro x hx
      apply Or.inl
      have hh := hx.2
      rw [hli, polygon_arcEdge_eq_segment, ha, hik, segment_symm] at hh
      exact hh
    have hcontact := hp.triangle_inter_edge_subset_of_admissible k had l hlk hls
    change polygonVertexTriangle (p z0) k ∩ (p z0).edgeSet ℝ l.castSucc ⊆
      {p z0 a, p z0 b} ∩ {p z0 l.castSucc, p z0 l.succ} at hcontact
    have hends : l.castSucc ≠ l.succ := by
      intro h
      have hh := congrArg Fin.val h
      change l.val = l.val + 1 at hh
      omega
    have hnoab : ¬ (l.castSucc = a ∧ l.succ = b) := by
      rintro ⟨hu, hv⟩
      have huu := congrArg Fin.val hu
      have hvv := congrArg Fin.val hv
      change l.val = a.val at huu
      change l.val + 1 = b.val at hvv
      omega
    have hnoba : ¬ (l.castSucc = b ∧ l.succ = a) := by
      rintro ⟨hu, hv⟩
      have huu := congrArg Fin.val hu
      have hvv := congrArg Fin.val hv
      change l.val = b.val at huu
      change l.val + 1 = a.val at hvv
      omega
    by_cases hua : l.castSucc = a
    · have hvb : l.succ ≠ b := fun h => hnoab ⟨hua, h⟩
      have hh := hattach a b l.succ (Or.inl ⟨rfl, rfl⟩)
        (fun h => hends (hua.trans h)) (by
          intro x hx
          have hh := hcontact ⟨hx.1, by
            rw [polygon_arcEdge_eq_segment, hua]
            exact hx.2⟩
          rcases hh.1 with hxa | hxb
          · exact hxa
          · rcases hh.2 with hxu | hxv
            · exact hxu.trans (congrArg (p z0) hua)
            · exact (hvb (hp.vertices_injective (hxv.symm.trans hxb))).elim)
      filter_upwards [hh] with z hz
      rw [polygon_arcEdge_eq_segment, hua]
      exact hz
    by_cases hva : l.succ = a
    · have hub : l.castSucc ≠ b := fun h => hnoba ⟨h, hva⟩
      have hh := hattach a b l.castSucc (Or.inl ⟨rfl, rfl⟩)
        (fun h => hends (hva.trans h).symm) (by
          intro x hx
          have hh := hcontact ⟨hx.1, by
            rw [polygon_arcEdge_eq_segment, hva, segment_symm]
            exact hx.2⟩
          rcases hh.1 with hxa | hxb
          · exact hxa
          · rcases hh.2 with hxu | hxv
            · exact (hub (hp.vertices_injective (hxu.symm.trans hxb))).elim
            · exact hxv.trans (congrArg (p z0) hva))
      filter_upwards [hh] with z hz
      rw [polygon_arcEdge_eq_segment, hva, segment_symm]
      exact hz
    by_cases hub : l.castSucc = b
    · have hh := hattach b a l.succ (Or.inr ⟨rfl, rfl⟩)
        (fun h => hends (hub.trans h)) (by
          intro x hx
          have hh := hcontact ⟨hx.1, by
            rw [polygon_arcEdge_eq_segment, hub]
            exact hx.2⟩
          rcases hh.1 with hxa | hxb
          · rcases hh.2 with hxu | hxv
            · exact hxu.trans (congrArg (p z0) hub)
            · exact (hva (hp.vertices_injective (hxv.symm.trans hxa))).elim
          · exact hxb)
      filter_upwards [hh] with z hz
      rw [polygon_arcEdge_eq_segment, hub]
      exact hz
    by_cases hvb : l.succ = b
    · have hh := hattach b a l.castSucc (Or.inr ⟨rfl, rfl⟩)
        (fun h => hends (hvb.trans h).symm) (by
          intro x hx
          have hh := hcontact ⟨hx.1, by
            rw [polygon_arcEdge_eq_segment, hvb, segment_symm]
            exact hx.2⟩
          rcases hh.1 with hxa | hxb
          · rcases hh.2 with hxu | hxv
            · exact (hua (hp.vertices_injective (hxu.symm.trans hxa))).elim
            · exact hxv.trans (congrArg (p z0) hvb)
          · exact hxb)
      filter_upwards [hh] with z hz
      rw [polygon_arcEdge_eq_segment, hvb, segment_symm]
      exact hz
    have hdis : Disjoint (polygonVertexTriangle (p z0) k)
        (segment ℝ (p z0 l.castSucc) (p z0 l.succ)) := by
      apply Set.disjoint_left.mpr
      intro x hxT hxS
      have hh := hcontact ⟨hxT, by rw [polygon_arcEdge_eq_segment]; exact hxS⟩
      rcases hh.1 with hxa | hxb <;> rcases hh.2 with hxu | hxv
      · exact hua (hp.vertices_injective (hxu.symm.trans hxa))
      · exact hva (hp.vertices_injective (hxv.symm.trans hxa))
      · exact hub (hp.vertices_injective (hxu.symm.trans hxb))
      · exact hvb (hp.vertices_injective (hxv.symm.trans hxb))
    have hh := eventually_disjoint_triangle_segment
      (hc k) (hc a) (hc b) (hc l.castSucc) (hc l.succ) hdis
    filter_upwards [hh] with z hz
    intro x hx
    exact (Set.disjoint_left.mp hz hx.1
      (by simpa only [polygon_arcEdge_eq_segment] using hx.2)).elim
  filter_upwards [Filter.eventually_all.mpr hevent] with z hz
  refine ⟨had.1, had.2.1, subset_antisymm ?_
    (polygonArcIncidentEdges_subset_triangle_inter_boundary (p z) k had.1 had.2.1)⟩
  intro x hx
  obtain ⟨l, hl⟩ := mem_iUnion.mp hx.2
  exact hz l ⟨hx.1, hl⟩

end PoincareConjecture.M25.Topology3D
