import PoincareConjecture.Proofs.M76.Rigidity.OriginalTriangleCofaceSigns
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.DualPointCoface

set_option autoImplicit false

open Set Metric Geometry SignType

namespace PoincareConjecture.M76.OriginalProperDiskTriangulation

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)

variable {X ι : Type*} [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}
  (T : OriginalProperDiskTriangulation e R j)

open Classical in

theorem sign_eq_on_triangle_dualBlock
    (p q : (T.marked 2).vertices) {s : Finset (T.index → ℝ × V3)}
    (hs : s ∈ (T.marked 2).faces) (hscard : s.card = 3)
    (hps : (p : T.index → ℝ × V3) ∈ s) (hqs : (q : T.index → ℝ × V3) ∈ s) :
    let : Fintype T.ambient.faces := T.finite.fintype
    EqOn (fun x => sign (T.height p x)) (fun x => sign (T.height q x))
      (T.ambient.barycentricDualBlock s).space := by
  classical
  let : Fintype T.ambient.faces := T.finite.fintype
  change EqOn (fun x => sign (T.height p x)) (fun x => sign (T.height q x))
    (T.ambient.barycentricDualBlock s).space
  intro x hx
  change sign (T.height p x) = sign (T.height q x)
  obtain ⟨t, ht, hst, hxt⟩ := T.ambient.exists_coface_of_mem_dualBlock hx
  have htp : t ∈ (T.ambient.closedStar p).faces :=
    ⟨ht, by simpa only [Finset.insert_eq_of_mem (hst hps)] using ht⟩
  have htq : t ∈ (T.ambient.closedStar q).faces :=
    ⟨ht, by simpa only [Finset.insert_eq_of_mem (hst hqs)] using ht⟩
  have hcard : t.card ≤ 4 := by
    simpa [Module.finrank_prod] using
      (T.star_affine p).face_card_le_of_injOn (T.star_injective p) htp
  have hle := Finset.card_le_card hst
  by_cases htcard : t.card = 4
  · exact T.sign_eq_on_triangle_coface p q hs hscard hps hqs ht htcard hst hxt
  · have hts : s = t := Finset.eq_of_subset_of_card_le hst (by omega)
    have hxD : x ∈ (T.marked 2).space :=
      (T.marked 2).convexHull_subset_space hs (hts.symm ▸ hxt)
    have hxR := T.triangle_dualBlock_subset_region hs hscard hx
    rw [(T.height_eq_zero_iff p
      ((T.ambient.closedStar p).convexHull_subset_space htp hxt) hxR).mpr hxD,
      (T.height_eq_zero_iff q
        ((T.ambient.closedStar q).convexHull_subset_space htq hxt) hxR).mpr hxD]

open Classical in

theorem triangle_dualBlock_halves_eq
    (p q : (T.marked 2).vertices) {s : Finset (T.index → ℝ × V3)}
    (hs : s ∈ (T.marked 2).faces) (hscard : s.card = 3)
    (hps : (p : T.index → ℝ × V3) ∈ s) (hqs : (q : T.index → ℝ × V3) ∈ s) :
    let : Fintype T.ambient.faces := T.finite.fintype
    ((T.ambient.barycentricDualBlock s).space ∩ {x | 0 ≤ T.height p x} =
      (T.ambient.barycentricDualBlock s).space ∩ {x | 0 ≤ T.height q x}) ∧
    ((T.ambient.barycentricDualBlock s).space ∩ {x | T.height p x ≤ 0} =
      (T.ambient.barycentricDualBlock s).space ∩ {x | T.height q x ≤ 0}) := by
  classical
  let : Fintype T.ambient.faces := T.finite.fintype
  have heq := T.sign_eq_on_triangle_dualBlock p q hs hscard hps hqs
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

end PoincareConjecture.M76.OriginalProperDiskTriangulation
