


import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Vertices.AttachmentIncidence
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Vertices.CapTransversals
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Intersections







set_option autoImplicit false
open Set
open scoped Topology Manifold ContDiff

namespace PoincareConjecture.Topology.Surface
namespace ChartCircleArrangementVertexPatch.VertexCapFaces

universe u
variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  {r : M → ℝ} {p : M} {P : ChartCircleArrangementVertexPatch r p}
  {x : Bool × Bool → M} (B : VertexCapFaces P x)


noncomputable def chordRemainderInterval (K : Set M) (i : Bool × Bool) (ρ : ℝ) : Set ℝ := by
  classical
  exact Icc (if ((B.face i).boundary 0).map 0 ∈ K then ρ else 0)
    (if ((B.face i).boundary 0).map 1 ∈ K then 1 - ρ else 1)

def chordRemainder (K : Set M) (i : Bool × Bool) (ρ : ℝ) : Set M :=
  ((B.face i).boundary 0).map '' B.chordRemainderInterval K i ρ


noncomputable def openChordAttachment (K : Set M) (i : Bool × Bool)
    (terminal : Bool) (ρ : ℝ) : Set M := by
  classical
  exact if ((B.face i).boundary 0).map (if terminal then 1 else 0) ∈ K then
    ((B.face i).boundary 0).map '' (if terminal then Ioo (1 - ρ) 1 else Ioo 0 ρ)
  else ∅

omit [T2Space M] in
theorem openChordAttachment_eq_ray (K : Set M) (i : Bool × Bool)
    (terminal : Bool) (ρ : ℝ)
    (hattach : ((B.face i).boundary 0).map (if terminal then 1 else 0) ∈ K) :
    B.openChordAttachment K i terminal ρ =
      (fun t : ℝ => (chartAt (EuclideanSpace ℝ (Fin 2)) (x i)).symm
        (B.chordEndpoint i terminal + t • B.chordDirection i terminal)) '' Ioo 0 ρ := by
  classical
  rw [openChordAttachment, if_pos hattach]
  cases terminal
  · symm
    apply image_congr
    intro t ht
    exact B.chord_ray_eq_boundary i false t
  · ext q
    constructor
    · rintro ⟨t, ht, rfl⟩
      refine ⟨1 - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, ?_⟩
      simpa using B.chord_ray_eq_boundary i true (1 - t)
    · rintro ⟨t, ht, rfl⟩
      refine ⟨1 - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, ?_⟩
      exact (B.chord_ray_eq_boundary i true t).symm

omit [T2Space M] in
theorem chordRemainderInterval_subset (K : Set M) (i : Bool × Bool) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    B.chordRemainderInterval K i ρ ⊆ Icc (0 : ℝ) 1 := by
  classical
  intro t ht
  simp only [chordRemainderInterval, mem_Icc] at ht
  split_ifs at ht <;> constructor <;> linarith [ht.1, ht.2]

omit [T2Space M] in
theorem isCompact_chordRemainder (K : Set M) (i : Bool × Bool) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    IsCompact (B.chordRemainder K i ρ) :=
  isCompact_Icc.image_of_continuousOn
    (((B.face i).boundary 0).smooth.continuousOn.mono (B.chordRemainderInterval_subset K i hρ))

omit [T2Space M] in
theorem chordRemainder_subset_chord (K : Set M) (i : Bool × Bool) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    B.chordRemainder K i ρ ⊆ ((B.face i).boundary 0).map '' Icc (0 : ℝ) 1 :=
  image_mono (B.chordRemainderInterval_subset K i hρ)

theorem chordRemainder_subset_carrier (K : Set M) (i : Bool × Bool) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    B.chordRemainder K i ρ ⊆ (B.face i).carrier :=
  (B.chordRemainder_subset_chord K i hρ).trans
    (((B.face i).boundary_image_subset_frontier 0).trans (B.face i).isClosed_carrier.frontier_subset)

omit [T2Space M] in
theorem chord_interior_mem_sector (i : Bool × Bool) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    ((B.face i).boundary 0).map t ∈ P.sector i := by
  have h := B.chord_ray_mem_sector i false ht
  rwa [B.chord_ray_eq_boundary, if_neg Bool.false_ne_true] at h

omit [T2Space M] in
theorem chordRemainder_disjoint (K : Set M)
    (hlocal : ∀ q ∈ P.carrier, q ∈ K ↔ q ∈ P.circles)
    (i : Bool × Bool) {ρ : ℝ} (hρ : 0 < ρ) : Disjoint (B.chordRemainder K i ρ) K := by
  classical
  apply disjoint_left.mpr
  rintro q ⟨t, ht, rfl⟩ hK
  have htunit := B.chordRemainderInterval_subset K i hρ.le ht
  by_cases ht0 : t = 0
  · subst t
    have hbound := ht.1
    simp only [if_pos hK] at hbound
    linarith
  by_cases ht1 : t = 1
  · subst t
    have hbound := ht.2
    simp only [if_pos hK] at hbound
    linarith
  have hsector := B.chord_interior_mem_sector i
    ⟨lt_of_le_of_ne htunit.1 (Ne.symm ht0), lt_of_le_of_ne htunit.2 ht1⟩
  exact disjoint_left.mp (P.sector_disjoint_circles i) hsector
    ((hlocal _ (P.closedSector_subset_carrier i (P.sector_subset_closed i hsector))).mp hK)

omit [T2Space M] in


theorem chord_subset_remainder_attachments (K : Set M) (i : Bool × Bool) (ρ : ℝ) :
    ((B.face i).boundary 0).map '' Icc (0 : ℝ) 1 ⊆
      K ∪ B.chordRemainder K i ρ ∪
        (B.openChordAttachment K i false ρ ∪ B.openChordAttachment K i true ρ) := by
  classical
  rintro q ⟨t, ht, rfl⟩
  by_cases hK : ((B.face i).boundary 0).map t ∈ K
  · exact Or.inl (Or.inl hK)
  by_cases hrem : t ∈ B.chordRemainderInterval K i ρ
  · exact Or.inl (Or.inr ⟨t, hrem, rfl⟩)
  have h0 : ((B.face i).boundary 0).map 0 ∈ K → 0 < t := by
    intro h
    exact lt_of_le_of_ne ht.1 (fun he => hK (he ▸ h))
  have h1 : ((B.face i).boundary 0).map 1 ∈ K → t < 1 := by
    intro h
    exact lt_of_le_of_ne ht.2 (fun he => hK (he.symm ▸ h))
  simp only [chordRemainderInterval, mem_Icc, not_and_or, not_le] at hrem
  rcases hrem with hleft | hright
  · by_cases hstart : ((B.face i).boundary 0).map 0 ∈ K
    · simp only [if_pos hstart] at hleft
      apply Or.inr ∘ Or.inl
      simp only [openChordAttachment, Bool.false_eq_true, ite_false, if_pos hstart]
      exact ⟨t, ⟨h0 hstart, hleft⟩, rfl⟩
    · simp only [if_neg hstart] at hleft
      exact False.elim (not_lt_of_ge ht.1 hleft)
  · by_cases hend : ((B.face i).boundary 0).map 1 ∈ K
    · simp only [if_pos hend] at hright
      apply Or.inr ∘ Or.inr
      simp only [openChordAttachment, ite_true, if_pos hend]
      exact ⟨t, ⟨hright, h1 hend⟩, rfl⟩
    · simp only [if_neg hend] at hright
      exact False.elim (not_lt_of_ge ht.2 hright)

end ChartCircleArrangementVertexPatch.VertexCapFaces

namespace FiniteChartRegionDecomposition

universe u
variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  (D : FiniteChartRegionDecomposition (M := M))
  {P : ∀ p : D.vertices, ChartCircleArrangementVertexPatch D.radius (p : M)}
  {x : D.vertices → Bool × Bool → M}
  (B : ∀ p, ChartCircleArrangementVertexPatch.VertexCapFaces (P p) (x p))
  (region : D.vertices → Bool × Bool → D.regions)

def vertexCapChordRemainders (R : D.regions) (ρ : ℝ) : Set M :=
  ⋃ a : {a : D.vertices × (Bool × Bool) // region a.1 a.2 = R},
    (B a.1.1).chordRemainder (chartDiskBoundaryUnion D.centers D.radius) a.1.2 ρ

omit [T2Space M] in
theorem isCompact_vertexCapChordRemainders (R : D.regions) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    IsCompact (D.vertexCapChordRemainders B region R ρ) :=
  isCompact_iUnion (fun a => (B a.1.1).isCompact_chordRemainder _ a.1.2 hρ)

theorem vertexCapChordRemainders_subset_caps (R : D.regions) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    D.vertexCapChordRemainders B region R ρ ⊆ D.vertexCapsInRegion B region R :=
  iUnion_mono (fun a => (B a.1.1).chordRemainder_subset_carrier _ a.1.2 hρ)

omit [T2Space M] in
theorem vertexCapChordRemainders_disjoint
    (hlocal : ∀ p q, q ∈ (P p).carrier →
      (q ∈ chartDiskBoundaryUnion D.centers D.radius ↔ q ∈ (P p).circles))
    (R : D.regions) {ρ : ℝ} (hρ : 0 < ρ) :
    Disjoint (D.vertexCapChordRemainders B region R ρ) (chartDiskBoundaryUnion D.centers D.radius) := by
  apply disjoint_left.mpr
  intro q hq hK
  obtain ⟨a, ha⟩ := mem_iUnion.mp hq
  exact disjoint_left.mp ((B a.1.1).chordRemainder_disjoint _ (hlocal a.1.1) a.1.2 hρ) ha hK

theorem vertexCapChordRemainders_subset_region
    (hlocal : ∀ p q, q ∈ (P p).carrier →
      (q ∈ chartDiskBoundaryUnion D.centers D.radius ↔ q ∈ (P p).circles))
    (hregion : ∀ p i, ((B p).face i).carrier ⊆ closure (connectedComponentIn
      (chartDiskBoundaryUnion D.centers D.radius)ᶜ (region p i)))
    (R : D.regions) {ρ : ℝ} (hρ : 0 < ρ) :
    D.vertexCapChordRemainders B region R ρ ⊆ connectedComponentIn
      (chartDiskBoundaryUnion D.centers D.radius)ᶜ R := by
  intro q hq
  have hnot := disjoint_left.mp (D.vertexCapChordRemainders_disjoint B region hlocal R hρ) hq
  obtain ⟨a, ha⟩ := mem_iUnion.mp hq
  apply D.region_closure_diff_arrangement_subset R
  refine ⟨?_, hnot⟩
  rw [← a.property]
  exact hregion _ _ ((B a.1.1).chordRemainder_subset_carrier _ a.1.2 hρ.le ha)

end FiniteChartRegionDecomposition
end PoincareConjecture.Topology.Surface
