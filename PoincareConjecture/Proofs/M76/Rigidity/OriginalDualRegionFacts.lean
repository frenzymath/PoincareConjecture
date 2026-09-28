import PoincareConjecture.Proofs.M76.Rigidity.OriginalDualRegion
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.DualPointCoface









set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.OriginalProperDiskTriangulation

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)

variable {X ι : Type*} [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}
  (T : OriginalProperDiskTriangulation e R j)

open Classical in


theorem dualRegion_subset_star (p : (T.marked 2).vertices)
    {s : Finset (T.index → ℝ × V3)} (hps : (p : T.index → ℝ × V3) ∈ s) :
    T.dualRegion s ⊆ (T.ambient.closedStar p).space := by
  classical
  let : Fintype T.ambient.faces := T.finite.fintype
  intro x hx
  obtain ⟨t, ht, hst, hxt⟩ := T.ambient.exists_coface_of_mem_dualBlock hx.1
  exact (T.ambient.closedStar p).convexHull_subset_space
    ⟨ht, by simpa only [Finset.insert_eq_of_mem (hst hps)] using ht⟩ hxt

open Classical in


theorem continuousOn_height_star (p : (T.marked 2).vertices) :
    ContinuousOn (T.height p) (T.ambient.closedStar p).space := by
  have hstar : T.ambient.closedStar p ≤ T.ambient := fun _ ht => ht.1
  have hgc : ContinuousOn (fun x => (T.inverse x : X))
      (T.ambient.closedStar p).space :=
    continuous_subtype_val.comp_continuousOn
      (T.inverse_continuous.mono (SimplicialComplex.space_subset_of_le hstar))
  exact continuousOn_const.mul
    (((T.chart (T.chart_index p)).continuousOn.comp hgc (T.star_source p)).snd)



theorem continuousOn_height_dualRegion (p : (T.marked 2).vertices)
    {s : Finset (T.index → ℝ × V3)} (hps : (p : T.index → ℝ × V3) ∈ s) :
    ContinuousOn (T.height p) (T.dualRegion s) :=
  (T.continuousOn_height_star p).mono (T.dualRegion_subset_star p hps)



theorem height_eq_zero_iff_on_dualRegion (p : (T.marked 2).vertices)
    {s : Finset (T.index → ℝ × V3)} (hps : (p : T.index → ℝ × V3) ∈ s)
    {x : T.index → ℝ × V3} (hx : x ∈ T.dualRegion s) :
    T.height p x = 0 ↔ x ∈ (T.marked 2).space :=
  T.height_eq_zero_iff p (T.dualRegion_subset_star p hps hx) hx.2



theorem dualRegion_antitone {s t : Finset (T.index → ℝ × V3)} (hst : s ⊆ t) :
    T.dualRegion t ⊆ T.dualRegion s := by
  classical
  let : Fintype T.ambient.faces := T.finite.fintype
  intro x hx
  exact ⟨SimplicialComplex.space_subset_of_le
    (T.ambient.barycentricDualBlock_antitone hst) hx.1, hx.2⟩

end PoincareConjecture.M76.OriginalProperDiskTriangulation
