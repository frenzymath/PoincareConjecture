import PoincareLib.Topology.Manifold.Smoothing.Schoenflies.Coordinates.RelativeHalfspaceCharts
import Mathlib.Topology.Algebra.Group.Basic

/-!
# Local collars from the actual side equations

Retain the signed coordinate of the original pair chart and use its
complete halfspace equivalence. Reflection supplies the other side.
See Brown derivation013, section4.
-/

set_option autoImplicit false

open Set

namespace BrownCollar

variable {X P : Type*} [TopologicalSpace X] [TopologicalSpace P]

/-- The positive side has an actual local collar fixing every original
base point in its source. See Brown derivation013, section4. -/
theorem exists_positive_halfspace_local_collar
    (e : OpenPartialHomeomorph X (P × ℝ)) {S R : Set X} (hSR : S ⊆ R)
    (hpair : ∀ y ∈ e.source, y ∈ S ↔ (e y).2 = 0)
    (hside : ∀ y ∈ e.source, y ∈ R ↔ 0 ≤ (e y).2)
    (x : S) (hx : (x : X) ∈ e.source) :
    ∃ c : OpenPartialHomeomorph (S × Ico (0 : ℝ) 1) R,
      collarBase x ∈ c.source ∧
        ∀ a, collarBase a ∈ c.source → c (collarBase a) = Set.inclusion hSR a := by
  obtain ⟨q, hqx, hqt, hbase, hnormal⟩ :=
    exists_local_pair_chart_with_normal e S hpair x hx
  apply exists_relative_halfspace_local_collar q R _ (Set.inclusion hSR) hbase x hqx
  intro z hz
  rw [hside _ (hqt (q.map_source hz)), hnormal z hz]

/-- Reflect the literal normal coordinate to construct the negative
side's actual local collar. See Brown derivation013, section4. -/
theorem exists_negative_halfspace_local_collar
    (e : OpenPartialHomeomorph X (P × ℝ)) {S R : Set X} (hSR : S ⊆ R)
    (hpair : ∀ y ∈ e.source, y ∈ S ↔ (e y).2 = 0)
    (hside : ∀ y ∈ e.source, y ∈ R ↔ (e y).2 ≤ 0)
    (x : S) (hx : (x : X) ∈ e.source) :
    ∃ c : OpenPartialHomeomorph (S × Ico (0 : ℝ) 1) R,
      collarBase x ∈ c.source ∧
        ∀ a, collarBase a ∈ c.source → c (collarBase a) = Set.inclusion hSR a := by
  let f := e.transHomeomorph ((Homeomorph.refl P).prodCongr (Homeomorph.neg ℝ))
  have hpair' (y : X) (hy : y ∈ f.source) : y ∈ S ↔ (f y).2 = 0 := by
    change y ∈ S ↔ -(e y).2 = 0
    rw [neg_eq_zero]
    exact hpair y hy
  have hside' (y : X) (hy : y ∈ f.source) : y ∈ R ↔ 0 ≤ (f y).2 := by
    change y ∈ R ↔ 0 ≤ -(e y).2
    rw [neg_nonneg]
    exact hside y hy
  exact exists_positive_halfspace_local_collar f hSR hpair' hside' x hx

/-- The retained ambient patches of both actual regions produce both
families of local collars. The inclusion maps have exactly the original
base values. See Brown derivation013, sections3--4. -/
theorem exists_side_local_collars
    {S Rpos Rneg : Set X} (hp : S ⊆ Rpos) (hm : S ⊆ Rneg)
    (E : S → OpenPartialHomeomorph X (P × ℝ))
    (hpair : ∀ i y, y ∈ (E i).source → (y ∈ S ↔ (E i y).2 = 0))
    (hlocal : ∀ x : S, ∃ (i : S) (V : Set X), IsOpen V ∧ (x : X) ∈ V ∧
      V ⊆ (E i).source ∧
      ∀ y ∈ V, (y ∈ Rpos ↔ 0 ≤ (E i y).2) ∧ (y ∈ Rneg ↔ (E i y).2 ≤ 0)) :
    (∀ x : S, ∃ c : OpenPartialHomeomorph (S × Ico (0 : ℝ) 1) Rpos,
      collarBase x ∈ c.source ∧
        ∀ a, collarBase a ∈ c.source → c (collarBase a) = Set.inclusion hp a) ∧
    (∀ x : S, ∃ c : OpenPartialHomeomorph (S × Ico (0 : ℝ) 1) Rneg,
      collarBase x ∈ c.source ∧
        ∀ a, collarBase a ∈ c.source → c (collarBase a) = Set.inclusion hm a) := by
  have hchoose (x : S) : ∃ e : OpenPartialHomeomorph X (P × ℝ),
      (x : X) ∈ e.source ∧
      (∀ y ∈ e.source, y ∈ S ↔ (e y).2 = 0) ∧
      ∀ y ∈ e.source, (y ∈ Rpos ↔ 0 ≤ (e y).2) ∧ (y ∈ Rneg ↔ (e y).2 ≤ 0) := by
    obtain ⟨i, V, hV, hxV, hVE, hside⟩ := hlocal x
    let e := (E i).restr V
    have hsource : e.source = V := by
      rw [OpenPartialHomeomorph.restr_source' _ _ hV]
      exact inter_eq_right.mpr hVE
    refine ⟨e, ?_, ?_, ?_⟩
    · rw [hsource]
      exact hxV
    · intro y hy
      rw [hsource] at hy
      exact hpair i y (hVE hy)
    · intro y hy
      rw [hsource] at hy
      exact hside y hy
  constructor
  · intro x
    obtain ⟨e, hx, hepair, heside⟩ := hchoose x
    exact exists_positive_halfspace_local_collar e hp hepair
      (fun y hy => (heside y hy).1) x hx
  · intro x
    obtain ⟨e, hx, hepair, heside⟩ := hchoose x
    exact exists_negative_halfspace_local_collar e hm hepair
      (fun y hy => (heside y hy).2) x hx

end BrownCollar
