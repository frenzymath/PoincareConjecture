import PoincareConjecture.Proofs.M76.Triangulation.HamiltonDehnProtectedBall
import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

variable {ι κ : Type*} [Fintype ι] [Fintype κ]
  {L : Submodule ℤ (κ → ℝ)} [DiscreteTopology L]
  {α : Type*}

local notation "V" => ((ι → ℝ) × (κ → ℝ))
local notation "X" => LatticeHandleAmbient ι κ L
local notation "C2" => Set.prod (closedBall (0 : ι → ℝ) 1) (closedBall (0 : κ → ℝ) 2)
local notation "pi" => hamiltonMarkedProjection ι κ L

theorem HamiltonRetainedBlockChart.exists_lifted_compact_subset
    {e : α → OpenPartialHomeomorph X (Fin 3 → ℝ)}
    {h : OpenPartialHomeomorph V (Fin 3 → ℝ)}
    (retained : HamiltonRetainedBlockChart ι κ L e h)
    (S : Set X) (hS : IsCompact S) (hSout : S ⊆ hamiltonHandleBlock ι κ L 2) :
    ∃ P : Set V, P = C2 ∩ pi ⁻¹' S ∧ IsCompact P ∧
      ∃ q : P ≃ₜ S, ∀ x : P, (q x : X) = pi x := by
  let P : Set V := C2 ∩ pi ⁻¹' S
  have hpi : Continuous pi :=
    continuous_fst.prodMk (QuotientAddGroup.continuous_mk.comp continuous_snd)
  have hP : IsCompact P :=
    ((isCompact_closedBall (0 : ι → ℝ) 1).prod
      (isCompact_closedBall (0 : κ → ℝ) 2)).inter_right (hS.isClosed.preimage hpi)
  let : CompactSpace P := isCompact_iff_compactSpace.mp hP
  let q0 : P → S := fun x => ⟨pi x, x.property.2⟩
  have hqcont : Continuous q0 := (hpi.comp continuous_subtype_val).subtype_mk _
  have hqinj : Function.Injective q0 := by
    intro x y hxy
    exact Subtype.ext (retained.quotient_injective x.property.1 y.property.1
      (congrArg Subtype.val hxy))
  have hqsurj : Function.Surjective q0 := by
    intro y
    obtain ⟨x, hx, hxy⟩ := hSout y.property
    refine ⟨⟨x, hx, ?_⟩, ?_⟩
    · change pi x ∈ S
      rw [hxy]
      exact y.property
    · exact Subtype.ext hxy
  let q : P ≃ₜ S :=
    (hqcont.isClosedEmbedding hqinj).isEmbedding.toHomeomorphOfSurjective hqsurj
  exact ⟨P, rfl, hP, q, fun _ => rfl⟩

theorem HamiltonRetainedBlockChart.exists_lifted_enclosing_region
    {e : α → OpenPartialHomeomorph X (Fin 3 → ℝ)}
    {h : OpenPartialHomeomorph V (Fin 3 → ℝ)}
    (retained : HamiltonRetainedBlockChart ι κ L e h)
    {T : Set X} (region : HamiltonDehnEnclosingRegion ι κ L e T) :
    ∃ (P : Set V) (r : ℝ),
      P = C2 ∩ pi ⁻¹' region.region ∧ IsCompact P ∧ 1 < r ∧ r < 2 ∧
        P ⊆ closedBall (0 : ι → ℝ) 1 ×ˢ ball (0 : κ → ℝ) r ∧
        ∃ q : P ≃ₜ region.region, ∀ x : P, (q x : X) = pi x := by
  obtain ⟨P, hPeq, hP, q, hq⟩ := retained.exists_lifted_compact_subset
    region.region region.compact region.subset_outer
  have hPC : P ⊆ C2 := by rw [hPeq]; exact inter_subset_left
  have hPopen : P ⊆ closedBall (0 : ι → ℝ) 1 ×ˢ ball (0 : κ → ℝ) 2 := by
    intro y hy
    obtain ⟨x, hx, hxy⟩ := region.subset_outer_open (q ⟨y, hy⟩).property
    rw [hq] at hxy
    have heq : x = y := retained.quotient_injective
      ⟨hx.1, ball_subset_closedBall hx.2⟩ (hPC hy) hxy
    exact heq ▸ hx
  have hfree : IsCompact (Prod.snd '' P) := hP.image continuous_snd
  have hfreeball : Prod.snd '' P ⊆ ball (0 : κ → ℝ) 2 := by
    rintro _ ⟨x, hx, rfl⟩
    exact (hPopen hx).2
  obtain ⟨s, hs2, hs⟩ := exists_lt_subset_ball hfree.isClosed hfreeball
  obtain ⟨r, hr, hr2⟩ := exists_between (max_lt hs2 (by norm_num : (1 : ℝ) < 2))
  refine ⟨P, r, hPeq, hP, (le_max_right s 1).trans_lt hr, hr2, ?_, q, hq⟩
  intro x hx
  exact ⟨(hPC hx).1,
    ball_subset_ball ((le_max_left s 1).trans hr.le) (hs (mem_image_of_mem Prod.snd hx))⟩

end PoincareConjecture.M76
