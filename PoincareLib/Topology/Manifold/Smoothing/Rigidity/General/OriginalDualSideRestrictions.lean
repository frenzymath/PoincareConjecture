import PoincareLib.Topology.Manifold.Smoothing.Rigidity.General.OriginalEdgeDualSigns
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Polygons.OriginalTriangleDualSigns

/-!
# Both coherent original sides and their complete face restrictions

Original square purity exhausts the vertex, edge and triangle cases.
Dual antitonicity then retains the whole positive and negative halves
under each actual face inclusion. See rigidity024, section5.
-/

set_option autoImplicit false

open Set Geometry SignType

namespace PoincareMT.M76.OriginalProperDiskTriangulation

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)

variable {X ι : Type*} [TopologicalSpace X] [T2Space X]
  {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}
  (T : OriginalProperDiskTriangulation e R j)

/-- Every original disk face has one complete sign on its entire
region dual, using only the already fixed labels. See rigidity024. -/
theorem sign_eq_on_dualRegion
    (p q : (T.marked 2).vertices) {s : Finset (T.index → ℝ × V3)}
    (hs : s ∈ (T.marked 2).faces)
    (hps : (p : T.index → ℝ × V3) ∈ s) (hqs : (q : T.index → ℝ × V3) ∈ s) :
    EqOn (fun x => sign (T.height p x)) (fun x => sign (T.height q x))
      (T.dualRegion s) := by
  classical
  have hbound := T.disk_face_card_le hs
  have hpos := Finset.card_pos.mpr ((T.marked 2).nonempty_of_mem_faces hs)
  have hcases : s.card = 1 ∨ s.card = 2 ∨ s.card = 3 := by omega
  rcases hcases with hcard | hcard | hcard
  · obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hcard
    have hp : (p : T.index → ℝ × V3) = x := by
      simpa only [hx, Finset.mem_singleton] using hps
    have hq : (q : T.index → ℝ × V3) = x := by
      simpa only [hx, Finset.mem_singleton] using hqs
    have hpq : p = q := Subtype.ext (hp.trans hq.symm)
    subst q
    exact fun _ _ => rfl
  · exact T.sign_eq_on_edge_dualRegion p q hs hcard hps hqs
  · let : Fintype T.ambient.faces := T.finite.fintype
    exact (T.sign_eq_on_triangle_dualBlock p q hs hcard hps hqs).mono inter_subset_left

/-- Both complete closed halves are independent of the chosen
original vertex label, including every zero point. See rigidity024. -/
theorem dualRegion_halves_eq
    (p q : (T.marked 2).vertices) {s : Finset (T.index → ℝ × V3)}
    (hs : s ∈ (T.marked 2).faces)
    (hps : (p : T.index → ℝ × V3) ∈ s) (hqs : (q : T.index → ℝ × V3) ∈ s) :
    (T.dualRegion s ∩ {x | 0 ≤ T.height p x} =
      T.dualRegion s ∩ {x | 0 ≤ T.height q x}) ∧
    (T.dualRegion s ∩ {x | T.height p x ≤ 0} =
      T.dualRegion s ∩ {x | T.height q x ≤ 0}) := by
  have heq := T.sign_eq_on_dualRegion p q hs hps hqs
  constructor
  · ext x
    apply and_congr_right
    intro hx
    have hsign : sign (T.height p x) = sign (T.height q x) := heq hx
    change 0 ≤ T.height p x ↔ 0 ≤ T.height q x
    rw [← sign_nonneg_iff (a := T.height p x),
      ← sign_nonneg_iff (a := T.height q x), hsign]
  · ext x
    apply and_congr_right
    intro hx
    have hsign : sign (T.height p x) = sign (T.height q x) := heq hx
    change T.height p x ≤ 0 ↔ T.height q x ≤ 0
    rw [← sign_nonpos_iff (a := T.height p x),
      ← sign_nonpos_iff (a := T.height q x), hsign]

/-- The entire positive half restricts exactly to the positive half
of each smaller original dual, with arbitrary incident labels.
See rigidity024, section5. -/
theorem positive_dualRegion_restriction
    {s t : Finset (T.index → ℝ × V3)} (ht : t ∈ (T.marked 2).faces)
    (hst : s ⊆ t) (p q : (T.marked 2).vertices)
    (hps : (p : T.index → ℝ × V3) ∈ s) (hqt : (q : T.index → ℝ × V3) ∈ t) :
    (T.dualRegion s ∩ {x | 0 ≤ T.height p x}) ∩ T.dualRegion t =
      T.dualRegion t ∩ {x | 0 ≤ T.height q x} := by
  have h := (T.dualRegion_halves_eq p q ht (hst hps) hqt).1
  apply Subset.antisymm
  · intro x hx
    exact h.subset ⟨hx.2, hx.1.2⟩
  · intro x hx
    exact ⟨⟨T.dualRegion_antitone hst hx.1, (h.symm.subset hx).2⟩, hx.1⟩

/-- The entire negative half has the same exact restriction, with
the whole central disk retained. See rigidity024, section5. -/
theorem negative_dualRegion_restriction
    {s t : Finset (T.index → ℝ × V3)} (ht : t ∈ (T.marked 2).faces)
    (hst : s ⊆ t) (p q : (T.marked 2).vertices)
    (hps : (p : T.index → ℝ × V3) ∈ s) (hqt : (q : T.index → ℝ × V3) ∈ t) :
    (T.dualRegion s ∩ {x | T.height p x ≤ 0}) ∩ T.dualRegion t =
      T.dualRegion t ∩ {x | T.height q x ≤ 0} := by
  have h := (T.dualRegion_halves_eq p q ht (hst hps) hqt).2
  apply Subset.antisymm
  · intro x hx
    exact h.subset ⟨hx.2, hx.1.2⟩
  · intro x hx
    exact ⟨⟨T.dualRegion_antitone hst hx.1, (h.symm.subset hx).2⟩, hx.1⟩

end PoincareMT.M76.OriginalProperDiskTriangulation
