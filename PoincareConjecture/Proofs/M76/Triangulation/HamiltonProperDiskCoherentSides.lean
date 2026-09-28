import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProperDiskEdgeSigns

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.HamiltonIndexOne

local notation "V2" => (Fin 2 → ℝ)
local notation "V" => (V2 × ℝ)
local notation "Cube" => closedBall (0 : V2) 1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [DecidableEq E] {R D : Set E} {b : Cube ≃ₜ D}

structure HamiltonProperDiskCoherentSides
    (T : HamiltonProperDiskTriangulation R D b) (c : E ≃ᴬ[ℝ] V) where

  labels : HamiltonProperDiskNormalLabels T c

  agreement : ∀ s ∈ T.disk.faces, ∀ p q : T.disk.vertices,
    (p : E) ∈ s → (q : E) ∈ s →
      T.dualRegion s ∩ {x | 0 ≤ labels.height p x} =
        T.dualRegion s ∩ {x | 0 ≤ labels.height q x}

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

end PoincareConjecture.M76.HamiltonIndexOne
