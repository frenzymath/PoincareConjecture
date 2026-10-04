import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Data.Set.Card

/-!
# Actual local embeddings and finite fibers after projection

A local homeomorphism takes an embedded source to a locally
embedded map on explicit open neighborhoods. Injecting each source
fiber into the actual projection fiber retains both finiteness and
its cardinal bound. See Dehn027, sections3--4, and Hatcher p.46.
-/

set_option autoImplicit false

open Set Topology

/-- A projected embedding has an actual embedding on a relatively
open neighborhood of every source point. This also applies at the
rim of the whole closed disk. See Dehn027, section3. -/
theorem IsLocalHomeomorph.exists_embedding_restrict
    {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    {p : Y → Z} (hp : IsLocalHomeomorph p) {j : X → Y}
    (hj : IsEmbedding j) (x : X) :
    ∃ W : Set X, IsOpen W ∧ x ∈ W ∧
      IsEmbedding (fun z : W => p (j z)) := by
  obtain ⟨B, hx, he⟩ := hp (j x)
  let W : Set X := j ⁻¹' B.source
  have hmap : MapsTo j W B.source := fun _ hz => hz
  have hbranch : IsEmbedding hmap.restrict := hj.restrict hmap
  refine ⟨W, B.open_source.preimage hj.continuous, hx, ?_⟩
  rw [he]
  exact B.isOpenEmbedding_restrict.isEmbedding.comp hbranch

/-- An actual injection into a finite projection fiber proves
finiteness and the cardinal bound for the composed map's fiber.
Neither conclusion is inferred from an infinite set's ncard.
See Dehn027, section4. -/
theorem Function.Injective.finite_fiber_comp_ncard_le
    {X Y Z : Type*} {j : X → Y} (hj : Function.Injective j)
    {p : Y → Z} {y : Z} (hy : (p ⁻¹' {y}).Finite) :
    ((p ∘ j) ⁻¹' {y}).Finite ∧
      ((p ∘ j) ⁻¹' {y}).ncard ≤ (p ⁻¹' {y}).ncard := by
  have hmap : MapsTo j ((p ∘ j) ⁻¹' {y}) (p ⁻¹' {y}) := fun _ hx => hx
  exact ⟨Set.Finite.of_injOn hmap hj.injOn hy,
    ncard_le_ncard_of_injOn j hmap hj.injOn hy⟩
