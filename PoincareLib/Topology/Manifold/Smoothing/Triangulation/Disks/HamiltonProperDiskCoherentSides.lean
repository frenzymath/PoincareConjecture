import PoincareLib.Topology.Manifold.Smoothing.Triangulation.Disks.HamiltonProperDiskEdgeSigns

/-!
# Coherent complete half-carriers on the single proper-disk complex

The original disk parameter constructs the labels. The actual vertex,
edge and triangle cases prove agreement everywhere on shared dual
carriers, and dual antitonicity gives both complete restriction maps.
No orientation or side-coherence premise is supplied. See351b.
-/

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareMT.M76.HamiltonIndexOne

local notation "V2" => (Fin 2 → ℝ)
local notation "V" => (V2 × ℝ)
local notation "Cube" => closedBall (0 : V2) 1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [DecidableEq E] {R D : Set E} {b : Cube ≃ₜ D}

/-- The complete shared-half compatibility used by the finite
relative block extensions. Its labels and agreement are constructed
from the same T below, not assumed as geometric input. See351b. -/
structure HamiltonProperDiskCoherentSides
    (T : HamiltonProperDiskTriangulation R D b) (c : E ≃ᴬ[ℝ] V) where
  /-- The proved original-parameter labels. -/
  labels : HamiltonProperDiskNormalLabels T c
  /-- Every whole original shared dual carrier has one positive half. -/
  agreement : ∀ s ∈ T.disk.faces, ∀ p q : T.disk.vertices,
    (p : E) ∈ s → (q : E) ∈ s →
      T.dualRegion s ∩ {x | 0 ≤ labels.height p x} =
        T.dualRegion s ∩ {x | 0 ≤ labels.height q x}

/-- The actual proper finite PL disk has coherent complete sides
on every face of the retained triangulation. Original square purity
exhausts the vertex, edge and triangle cases. See351b. -/
theorem HamiltonProperDiskTriangulation.exists_coherent_sides
    [FiniteDimensional ℝ E] (T : HamiltonProperDiskTriangulation R D b)
    (hb : b.IsFinitePL)
    (hproper : ∀ x : Cube, (b x : E) ∈ frontier R ↔ (x : V2) ∈ sphere 0 1)
    (c : E ≃ᴬ[ℝ] V) : Nonempty (HamiltonProperDiskCoherentSides T c) := by
  obtain ⟨O⟩ := T.exists_normal_labels hb c
  refine ⟨⟨O, ?_⟩⟩
  intro s hs p q hps hqs
  have hbound := T.disk_face_card_le hs
  have hpos := Finset.card_pos.mpr (T.disk.nonempty_of_mem_faces hs)
  have hcases : s.card = 1 ∨ s.card = 2 ∨ s.card = 3 := by omega
  rcases hcases with hcard | hcard | hcard
  · obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hcard
    have hp : (p : E) = x := by simpa only [hx, Finset.mem_singleton] using hps
    have hq : (q : E) = x := by simpa only [hx, Finset.mem_singleton] using hqs
    have hpq : p = q := Subtype.ext (hp.trans hq.symm)
    rw [hpq]
  · exact O.half_eq_on_edge_dual hproper p q hs hcard hps hqs
  · exact O.half_eq_on_triangle_dual p q hs hcard hps hqs

variable {T : HamiltonProperDiskTriangulation R D b} {c : E ≃ᴬ[ℝ] V}

/-- The same complete zero disk turns positive-half agreement into
negative-half agreement, retaining all boundary points. See351b. -/
theorem HamiltonProperDiskCoherentSides.negative_agreement
    (C : HamiltonProperDiskCoherentSides T c) {s : Finset E}
    (hs : s ∈ T.disk.faces) (p q : T.disk.vertices)
    (hps : (p : E) ∈ s) (hqs : (q : E) ∈ s) :
    T.dualRegion s ∩ {x | C.labels.height p x ≤ 0} =
      T.dualRegion s ∩ {x | C.labels.height q x ≤ 0} := by
  have h := C.agreement s hs p q hps hqs
  have hpS := T.dualRegion_subset_chart_source p hps
  have hqS := T.dualRegion_subset_chart_source q hqs
  apply Subset.antisymm
  · intro x hx
    refine ⟨hx.1, ?_⟩
    by_contra hn
    have hqpos : 0 < C.labels.height q x := lt_of_not_ge hn
    have hpzero : C.labels.height p x = 0 :=
      le_antisymm hx.2 (h.symm.subset ⟨hx.1, hqpos.le⟩).2
    have hxD := (C.labels.height_eq_zero_iff p (hpS hx.1) hx.1.2).mp hpzero
    exact (ne_of_gt hqpos) ((C.labels.height_eq_zero_iff q (hqS hx.1) hx.1.2).mpr hxD)
  · intro x hx
    refine ⟨hx.1, ?_⟩
    by_contra hn
    have hppos : 0 < C.labels.height p x := lt_of_not_ge hn
    have hqzero : C.labels.height q x = 0 :=
      le_antisymm hx.2 (h.subset ⟨hx.1, hppos.le⟩).2
    have hxD := (C.labels.height_eq_zero_iff q (hqS hx.1) hx.1.2).mp hqzero
    exact (ne_of_gt hppos) ((C.labels.height_eq_zero_iff p (hpS hx.1) hx.1.2).mpr hxD)

/-- Under an original face inclusion, restriction of the complete
positive half is exactly the positive half of the smaller dual block.
The arbitrary two vertex charts are compared on that entire block.
See derivation351b. -/
theorem HamiltonProperDiskCoherentSides.positive_restriction
    (C : HamiltonProperDiskCoherentSides T c) {s t : Finset E}
    (ht : t ∈ T.disk.faces) (hst : s ⊆ t) (p q : T.disk.vertices)
    (hps : (p : E) ∈ s) (hqt : (q : E) ∈ t) :
    (T.dualRegion s ∩ {x | 0 ≤ C.labels.height p x}) ∩ T.dualRegion t =
      T.dualRegion t ∩ {x | 0 ≤ C.labels.height q x} := by
  classical
  let : Fintype T.ambient.faces := T.finite.fintype
  have hinc : T.dualRegion t ⊆ T.dualRegion s := by
    intro x hx
    exact ⟨SimplicialComplex.space_subset_of_le
      (T.ambient.barycentricDualBlock_antitone hst) hx.1, hx.2⟩
  have h := C.agreement t ht p q (hst hps) hqt
  apply Subset.antisymm
  · intro x hx
    exact h.subset ⟨hx.2, hx.1.2⟩
  · intro x hx
    exact ⟨⟨hinc hx.1, (h.symm.subset hx).2⟩, hx.1⟩

/-- The complete negative half has the same exact restriction
property, with the full original zero section retained. See351b. -/
theorem HamiltonProperDiskCoherentSides.negative_restriction
    (C : HamiltonProperDiskCoherentSides T c) {s t : Finset E}
    (ht : t ∈ T.disk.faces) (hst : s ⊆ t) (p q : T.disk.vertices)
    (hps : (p : E) ∈ s) (hqt : (q : E) ∈ t) :
    (T.dualRegion s ∩ {x | C.labels.height p x ≤ 0}) ∩ T.dualRegion t =
      T.dualRegion t ∩ {x | C.labels.height q x ≤ 0} := by
  classical
  let : Fintype T.ambient.faces := T.finite.fintype
  have hinc : T.dualRegion t ⊆ T.dualRegion s := by
    intro x hx
    exact ⟨SimplicialComplex.space_subset_of_le
      (T.ambient.barycentricDualBlock_antitone hst) hx.1, hx.2⟩
  have h := C.negative_agreement ht p q (hst hps) hqt
  apply Subset.antisymm
  · intro x hx
    exact h.subset ⟨hx.2, hx.1.2⟩
  · intro x hx
    exact ⟨⟨hinc hx.1, (h.symm.subset hx).2⟩, hx.1⟩

end PoincareMT.M76.HamiltonIndexOne
