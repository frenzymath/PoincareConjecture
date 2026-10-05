import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Levels.PuncturedCutPartition
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.General.CappedZeroSectionResidual
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.General.CircularSubsetTopology
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Polygons.PolygonCircle
import Mathlib.SetTheory.Cardinal.Finite

/-!
# The exact unselected curves in both new zero sections

Every unselected polygon is assigned whole to one original
cut disk. The cap-removal expressions are exactly the two
assigned polygon unions with the marked point adjoined, and
their index counts add to the old residual count. See Alexander
1924, pp. 6--8 and M76 derivation 244.
-/

set_option autoImplicit false

open Set

namespace Polygon

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Finite ι]

/-- The original finite unselected polygon family partitions
the two exact cap-deleted zero sections. Whole curves are
retained, including curves avoiding the marked point. The
cardinality equality counts these original indices. See
Alexander pp. 6--8 and derivation 244. -/
theorem exists_zero_section_cut_partition (n : ι → ℕ) (P : ∀ i, Polygon E (n i + 3))
    (hPe : ∀ i, (P i).HasSimplicialEdges) (hPi : ∀ i, Function.Injective (P i))
    {s₀ s₁ b d Z : Set E} (hs₀ : IsClosed s₀) (hs₁ : IsClosed s₁)
    (hcut : s₀ ∩ s₁ = b) (q : E) (hqb : q ∈ b) (hbd : b ⊆ d)
    (hsection : (s₀ ∪ s₁) ∩ Z = b ∪ ⋃ i, (P i).boundary ℝ)
    (hdP : ∀ i, d ∩ (P i).boundary ℝ ⊆ {q}) :
    ∃ I : Set ι,
      (∀ i ∈ I, (P i).boundary ℝ ⊆ s₀ ∧ (P i).boundary ℝ ∩ s₁ ⊆ {q}) ∧
      (∀ i ∉ I, (P i).boundary ℝ ⊆ s₁ ∧ (P i).boundary ℝ ∩ s₀ ⊆ {q}) ∧
      ((((s₀ ∪ d) ∩ Z) \ d) ∪ (d ∩ {q})) =
        (⋃ i : I, (P i).boundary ℝ) ∪ {q} ∧
      ((((s₁ ∪ d) ∩ Z) \ d) ∪ (d ∩ {q})) =
        (⋃ i : (Iᶜ : Set ι), (P i).boundary ℝ) ∪ {q} ∧
      Nat.card I + Nat.card (Iᶜ : Set ι) = Nat.card ι := by
  classical
  have hpre (i : ι) : IsPreconnected ((P i).boundary ℝ \ {q}) := by
    obtain ⟨e⟩ := (P i).nonempty_boundary_homeomorph_circle (hPe i) (hPi i)
    exact (isConnected_sdiff_singleton_of_homeomorph_circle ((P i).boundary ℝ) e q).isPreconnected
  have hcover (i : ι) : (P i).boundary ℝ ⊆ s₀ ∪ s₁ := fun x hx =>
    (hsection.symm.subset (Or.inr (mem_iUnion.mpr ⟨i, hx⟩))).1
  have hinter (i : ι) : (P i).boundary ℝ ∩ (s₀ ∩ s₁) ⊆ {q} :=
    fun x hx => hdP i ⟨hbd (hcut.subset hx.2), hx.1⟩
  obtain ⟨I, h₀, h₁, he₀, he₁⟩ := exists_punctured_cut_partition hs₀ hs₁ q
    (hcut.symm.subset hqb) (fun i => (P i).boundary ℝ) hpre hcover hinter
  have hdR : d ∩ (⋃ i, (P i).boundary ℝ) ⊆ {q} := by
    intro x hx
    obtain ⟨i, hxi⟩ := mem_iUnion.mp hx.2
    exact hdP i ⟨hx.1, hxi⟩
  refine ⟨I, h₀, h₁, ?_, ?_, ?_⟩
  · exact (capped_zero_section_eq_residual hsection hbd q (hbd hqb) hdR).trans he₀
  · have hsection' : (s₁ ∪ s₀) ∩ Z = b ∪ ⋃ i, (P i).boundary ℝ := by
      rw [union_comm s₁ s₀]
      exact hsection
    exact (capped_zero_section_eq_residual hsection' hbd q (hbd hqb) hdR).trans he₁
  · rw [← Nat.card_sum]
    exact Nat.card_congr (Equiv.Set.sumCompl I)

end Polygon
