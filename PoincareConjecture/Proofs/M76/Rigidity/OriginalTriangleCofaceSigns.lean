import PoincareConjecture.Proofs.M76.Rigidity.OriginalTriangleSignWitness
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.SingleVertexAffineSigns









set_option autoImplicit false

open Set Metric Geometry SignType

namespace PoincareConjecture.M76.OriginalProperDiskTriangulation

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)

variable {X ι : Type*} [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}
  (T : OriginalProperDiskTriangulation e R j)




theorem sign_eq_on_triangle_coface
    (p q : (T.marked 2).vertices) {s t : Finset (T.index → ℝ × V3)}
    (hs : s ∈ (T.marked 2).faces) (hscard : s.card = 3)
    (hps : (p : T.index → ℝ × V3) ∈ s) (hqs : (q : T.index → ℝ × V3) ∈ s)
    (ht : t ∈ T.ambient.faces) (htcard : t.card = 4) (hst : s ⊆ t) :
    EqOn (fun x => sign (T.height p x)) (fun x => sign (T.height q x))
      (convexHull ℝ (t : Set (T.index → ℝ × V3))) := by
  classical
  obtain ⟨v, _, hvt, _⟩ := T.exists_triangle_coface_apex hs hscard ht htcard hst
  have htp : t ∈ (T.ambient.closedStar p).faces :=
    ⟨ht, by simpa only [Finset.insert_eq_of_mem (hst hps)] using ht⟩
  have htq : t ∈ (T.ambient.closedStar q).faces :=
    ⟨ht, by simpa only [Finset.insert_eq_of_mem (hst hqs)] using ht⟩
  have hHullp := (T.ambient.closedStar p).convexHull_subset_space htp
  have hHullq := (T.ambient.closedStar q).convexHull_subset_space htq
  have hHullR := (T.marked 0).convexHull_subset_space
    (T.triangle_coface_mem_region hs hscard ht hst)
  obtain ⟨a, ha⟩ := T.height_affine p t htp
  obtain ⟨b, hb⟩ := T.height_affine q t htq
  have hzero (z : T.index → ℝ × V3) (hz : z ∈ t) (hzv : z ≠ v) :
      a.toAffineMap z = 0 ∧ b.toAffineMap z = 0 := by
    have hzs : z ∈ s := (Finset.mem_insert.mp (hvt.symm ▸ hz)).resolve_left hzv
    have hzD := (T.marked 2).subset_space hs hzs
    have hzHull : z ∈ convexHull ℝ (t : Set (T.index → ℝ × V3)) :=
      subset_convexHull ℝ _ hz
    exact ⟨(ha hzHull).symm.trans
      ((T.height_eq_zero_iff p (hHullp hzHull) (hHullR hzHull)).mpr hzD),
      (hb hzHull).symm.trans
        ((T.height_eq_zero_iff q (hHullq hzHull) (hHullR hzHull)).mpr hzD)⟩
  obtain ⟨w, hw, hpos⟩ :=
    T.exists_triangle_coface_sign_witness p q hs hscard hps hqs ht htcard hst
  have hpos' : 0 < a.toAffineMap w * b.toAffineMap w := by
    rw [ha hw, hb hw] at hpos
    exact hpos
  have heq := a.toAffineMap.sign_eqOn_convexHull_of_single_vertex
    b.toAffineMap hzero hw hpos'
  intro x hx
  change sign (T.height p x) = sign (T.height q x)
  rw [ha hx, hb hx]
  exact heq hx

end PoincareConjecture.M76.OriginalProperDiskTriangulation
