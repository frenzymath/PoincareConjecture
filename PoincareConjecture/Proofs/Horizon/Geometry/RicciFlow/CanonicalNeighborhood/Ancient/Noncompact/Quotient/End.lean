import PoincareConjecture.Proofs.Horizon.Compat.M33SphereNonempty
import PoincareConjecture.Definitions.M27ProductModels











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


def slabCore (C : M27TwistedSphereLineFlowCertificate K) (r : ℝ) : Set M :=
  C.cover '' (univ ×ˢ Icc (-r) r)

theorem isCompact_slabCore (C : M27TwistedSphereLineFlowCertificate K) (r : ℝ) :
    IsCompact (C.slabCore r) :=
  (isCompact_univ.prod isCompact_Icc).image C.cover_local_diffeomorph.isLocalHomeomorph.continuous

theorem cover_mem_slabCore_iff (C : M27TwistedSphereLineFlowCertificate K)
    (r : ℝ) (p : UnitTwoSphere × ℝ) :
    C.cover p ∈ C.slabCore r ↔ |p.2| ≤ r := by
  constructor
  · rintro ⟨q, hq, heq⟩
    rcases (C.cover_fibers q p).mp heq with rfl | hp
    · exact abs_le.mpr hq.2
    · rw [hp]
      simpa only [m27TwistedProductInvolution, abs_neg] using abs_le.mpr hq.2
  · intro hp
    exact ⟨p, ⟨mem_univ _, abs_le.mp hp⟩, rfl⟩


theorem positiveEnd_isOpenEmbedding (C : M27TwistedSphereLineFlowCertificate K)
    {r : ℝ} (hr : 0 ≤ r) :
    Topology.IsOpenEmbedding
      (fun p : UnitTwoSphere × Ioi r => C.cover (p.1, p.2.1)) := by
  let i : UnitTwoSphere × Ioi r → UnitTwoSphere × ℝ := fun p => (p.1, p.2.1)
  have hi : Topology.IsOpenEmbedding i :=
    Topology.IsOpenEmbedding.id.prodMap isOpen_Ioi.isOpenEmbedding_subtypeVal
  apply Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
    (C.cover_local_diffeomorph.isLocalHomeomorph.continuous.comp hi.continuous)
    ?_ (C.cover_local_diffeomorph.isOpenMap.comp hi.isOpenMap)
  intro p q hpq
  rcases (C.cover_fibers (i p) (i q)).mp hpq with h | h
  · exact hi.injective h.symm
  · have hline : q.2.1 = -p.2.1 := congrArg Prod.snd h
    have hp := p.2.2
    have hq := q.2.2
    change r < p.2.1 at hp
    change r < q.2.1 at hq
    linarith

theorem complement_slabCore (C : M27TwistedSphereLineFlowCertificate K)
    {r : ℝ} (hr : 0 ≤ r) :
    (C.slabCore r)ᶜ =
      Set.range (fun p : UnitTwoSphere × Ioi r => C.cover (p.1, p.2.1)) := by
  ext x
  obtain ⟨p, rfl⟩ := C.cover_surjective x
  rw [mem_compl_iff, C.cover_mem_slabCore_iff, not_le]
  constructor
  · intro hp
    by_cases hsign : 0 ≤ p.2
    · rw [abs_of_nonneg hsign] at hp
      exact ⟨(p.1, ⟨p.2, hp⟩), rfl⟩
    · rw [abs_of_neg (lt_of_not_ge hsign)] at hp
      refine ⟨(-p.1, ⟨-p.2, hp⟩), ?_⟩
      exact ((C.cover_fibers p (m27TwistedProductInvolution p)).mpr (Or.inr rfl)).symm
  · rintro ⟨q, hq⟩
    change C.cover (q.1, q.2.1) = C.cover p at hq
    have hpos : r < |(q.1, q.2.1).2| := by
      rw [abs_of_pos (lt_of_le_of_lt hr q.2.2)]
      exact q.2.2
    have hnot : C.cover (q.1, q.2.1) ∉ C.slabCore r := by
      rw [C.cover_mem_slabCore_iff]
      exact not_le_of_gt hpos
    rw [hq, C.cover_mem_slabCore_iff] at hnot
    exact lt_of_not_ge hnot

end PoincareConjecture.M27TwistedSphereLineFlowCertificate
