import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Quotient.CoreTopology











set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M27TwistedSphereLineFlowCertificate

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution 3 M}

theorem cover_mem_image_nonnegative_iff (C : M27TwistedSphereLineFlowCertificate K)
    {s : Set ℝ} (hs : s ⊆ Ici 0) (p : UnitTwoSphere × ℝ) :
    C.cover p ∈ C.cover '' (univ ×ˢ s) ↔ |p.2| ∈ s := by
  constructor
  · rintro ⟨q, hq, heq⟩
    have hqnonneg : 0 ≤ q.2 := hs hq.2
    rcases (C.cover_fibers q p).mp heq with hp | hp
    · rw [hp, abs_of_nonneg hqnonneg]
      exact hq.2
    · rw [hp]
      simpa only [m27TwistedProductInvolution, abs_neg,
        abs_of_nonneg hqnonneg] using hq.2
  · intro hp
    by_cases hsign : 0 ≤ p.2
    · refine ⟨p, ⟨mem_univ _, ?_⟩, rfl⟩
      simpa only [abs_of_nonneg hsign] using hp
    · refine ⟨m27TwistedProductInvolution p, ⟨mem_univ _, ?_⟩, ?_⟩
      · simpa only [m27TwistedProductInvolution,
          abs_of_neg (lt_of_not_ge hsign)] using hp
      · exact ((C.cover_fibers p (m27TwistedProductInvolution p)).mpr (Or.inr rfl)).symm

theorem cover_mem_positiveSlab_iff (C : M27TwistedSphereLineFlowCertificate K)
    {l u : ℝ} (hl : 0 ≤ l) (p : UnitTwoSphere × ℝ) :
    C.cover p ∈ C.cover '' (univ ×ˢ Ioo l u) ↔ l < |p.2| ∧ |p.2| < u :=
  C.cover_mem_image_nonnegative_iff (fun _ hx => hl.trans hx.1.le) p

theorem cover_mem_closedPositiveSlab_iff (C : M27TwistedSphereLineFlowCertificate K)
    {l u : ℝ} (hl : 0 ≤ l) (p : UnitTwoSphere × ℝ) :
    C.cover p ∈ C.cover '' (univ ×ˢ Icc l u) ↔ l ≤ |p.2| ∧ |p.2| ≤ u :=
  C.cover_mem_image_nonnegative_iff (fun _ hx => hl.trans hx.1) p

theorem closure_cover_image_Ioo (C : M27TwistedSphereLineFlowCertificate K)
    {l u : ℝ} (hlu : l < u) :
    closure (C.cover '' (univ ×ˢ Ioo l u)) = C.cover '' (univ ×ˢ Icc l u) := by
  have hc := C.cover_local_diffeomorph.isLocalHomeomorph.continuous
  apply Subset.antisymm
  · apply closure_minimal (image_mono (prod_mono subset_rfl Ioo_subset_Icc_self))
    exact ((isCompact_univ.prod isCompact_Icc).image hc).isClosed
  · have hclosure : closure (univ ×ˢ Ioo l u : Set (UnitTwoSphere × ℝ)) =
        univ ×ˢ Icc l u := by
      rw [closure_prod_eq, closure_univ, closure_Ioo hlu.ne]
    rw [← hclosure]
    exact image_closure_subset_closure_image hc

theorem cover_mem_frontier_positiveSlab_iff (C : M27TwistedSphereLineFlowCertificate K)
    {l u : ℝ} (hl : 0 ≤ l) (hlu : l < u) (p : UnitTwoSphere × ℝ) :
    C.cover p ∈ frontier (C.cover '' (univ ×ˢ Ioo l u)) ↔
      |p.2| = l ∨ |p.2| = u := by
  rw [(C.cover_local_diffeomorph.isOpenMap _ (isOpen_univ.prod isOpen_Ioo)).frontier_eq,
    C.closure_cover_image_Ioo hlu, mem_sdiff, C.cover_mem_closedPositiveSlab_iff hl,
    C.cover_mem_positiveSlab_iff hl]
  constructor
  · intro h
    by_cases hp : |p.2| = l
    · exact Or.inl hp
    · have hlo : l < |p.2| := lt_of_le_of_ne h.1.1 (Ne.symm hp)
      have hupper : ¬ |p.2| < u := fun hu => h.2 ⟨hlo, hu⟩
      exact Or.inr (le_antisymm h.1.2 (le_of_not_gt hupper))
  · rintro (h | h) <;> rw [h] <;> constructor
    · exact ⟨le_rfl, hlu.le⟩
    · exact fun h => (lt_irrefl _ h.1)
    · exact ⟨hlu.le, le_rfl⟩
    · exact fun h => (lt_irrefl _ h.2)

theorem endNeck_subset_capCarrier (C : M27TwistedSphereLineFlowCertificate K)
    {L : ℝ} (hL : 0 < L) :
    C.cover '' (univ ×ˢ Ioo L (3 * L)) ⊆ interior (C.slabCore (3 * L)) := by
  intro x hx
  obtain ⟨p, rfl⟩ := C.cover_surjective x
  rw [C.cover_mem_interior_slabCore_iff]
  exact ((C.cover_mem_positiveSlab_iff hL.le p).mp hx).2

theorem boundaryNeck_subset_capCarrier (C : M27TwistedSphereLineFlowCertificate K)
    {L : ℝ} (hL : 0 < L) :
    C.cover '' (univ ×ˢ Ioo 0 (2 * L)) ⊆ interior (C.slabCore (3 * L)) := by
  intro x hx
  obtain ⟨p, rfl⟩ := C.cover_surjective x
  rw [C.cover_mem_interior_slabCore_iff]
  have hp := ((C.cover_mem_positiveSlab_iff (le_refl 0) p).mp hx).2
  linarith

theorem slabCore_eq_capCarrier_diff_endNeck (C : M27TwistedSphereLineFlowCertificate K)
    {L : ℝ} (hL : 0 < L) :
    C.slabCore L = interior (C.slabCore (3 * L)) \
      C.cover '' (univ ×ˢ Ioo L (3 * L)) := by
  ext x
  obtain ⟨p, rfl⟩ := C.cover_surjective x
  rw [mem_sdiff, C.cover_mem_slabCore_iff, C.cover_mem_interior_slabCore_iff,
    C.cover_mem_positiveSlab_iff hL.le]
  constructor
  · intro hp
    exact ⟨by linarith, fun h => (not_lt_of_ge hp) h.1⟩
  · rintro ⟨hp, hnot⟩
    by_contra h
    exact hnot ⟨lt_of_not_ge h, hp⟩

theorem capCarrier_inter_frontier_endNeck (C : M27TwistedSphereLineFlowCertificate K)
    {L : ℝ} (hL : 0 < L) :
    interior (C.slabCore (3 * L)) ∩ frontier (C.cover '' (univ ×ˢ Ioo L (3 * L))) =
      frontier (C.slabCore L) := by
  ext x
  obtain ⟨p, rfl⟩ := C.cover_surjective x
  rw [mem_inter_iff, C.cover_mem_interior_slabCore_iff,
    C.cover_mem_frontier_positiveSlab_iff hL.le (by linarith),
    C.cover_mem_frontier_slabCore_iff]
  constructor
  · rintro ⟨hp, h | h⟩
    · exact h
    · linarith
  · intro hp
    exact ⟨by linarith, Or.inl hp⟩

theorem frontier_slabCore_subset_negativeEnd_closure
    (C : M27TwistedSphereLineFlowCertificate K) {L : ℝ} (hL : 0 < L) :
    frontier (C.slabCore L) ⊆ closure (C.cover '' (univ ×ˢ Ioo L (3 * L / 2))) := by
  rw [C.frontier_slabCore hL.le, C.closure_cover_image_Ioo (by linarith)]
  apply image_mono
  rintro p ⟨hp, hline⟩
  exact ⟨hp, by rw [mem_singleton_iff] at hline; rw [mem_Icc, hline]; constructor <;> linarith⟩

theorem nonempty_interior_slabCore (C : M27TwistedSphereLineFlowCertificate K)
    {r : ℝ} (hr : 0 < r) : (interior (C.slabCore r)).Nonempty := by
  classical
  let a : UnitTwoSphere := Classical.choice inferInstance
  refine ⟨C.cover (a, 0), ?_⟩
  simpa only [C.cover_mem_interior_slabCore_iff, abs_zero] using hr

theorem slabCore_subset_interior_slabCore (C : M27TwistedSphereLineFlowCertificate K)
    {r R : ℝ} (hrR : r < R) : C.slabCore r ⊆ interior (C.slabCore R) := by
  intro x hx
  obtain ⟨p, rfl⟩ := C.cover_surjective x
  rw [C.cover_mem_interior_slabCore_iff]
  exact ((C.cover_mem_slabCore_iff r p).mp hx).trans_lt hrR

theorem slabCore_subset_capCarrier (C : M27TwistedSphereLineFlowCertificate K)
    {L : ℝ} (hL : 0 < L) : C.slabCore L ⊆ interior (C.slabCore (3 * L)) :=
  C.slabCore_subset_interior_slabCore (by linarith)

end PoincareConjecture.M27TwistedSphereLineFlowCertificate
