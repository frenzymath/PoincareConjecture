import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Quotient.End

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

theorem not_isCompact_univ (C : M27TwistedSphereLineFlowCertificate K) :
    ¬ IsCompact (univ : Set M) := by
  classical
  obtain ⟨s, hs⟩ := C.cover_surjective.hasRightInverse
  let height : M → ℝ := fun x => |(s x).2|
  have hheight (p : UnitTwoSphere × ℝ) : height (C.cover p) = |p.2| := by
    rcases (C.cover_fibers (s (C.cover p)) p).mp (hs (C.cover p)) with hp | hp
    · exact congrArg (fun q : UnitTwoSphere × ℝ => |q.2|) hp.symm
    · have h := congrArg (fun q : UnitTwoSphere × ℝ => |q.2|) hp
      simpa only [m27TwistedProductInvolution, abs_neg] using h.symm
  have hquot := C.cover_local_diffeomorph.isOpenMap.isQuotientMap
    C.cover_local_diffeomorph.isLocalHomeomorph.continuous C.cover_surjective
  have hcontinuous : Continuous height := by
    apply hquot.continuous_iff.mpr
    have heq : height ∘ C.cover = fun p : UnitTwoSphere × ℝ => |p.2| :=
      funext hheight
    rw [heq]
    exact continuous_snd.abs
  intro hcompact
  obtain ⟨b, hb⟩ := hcompact.bddAbove_image hcontinuous.continuousOn
  let a : UnitTwoSphere := Classical.choice inferInstance
  have hbound : height (C.cover (a, b + 1)) ≤ b :=
    hb (mem_image_of_mem height (mem_univ _))
  rw [hheight] at hbound
  have habs := le_abs_self (b + 1)
  linarith

end PoincareConjecture.M27TwistedSphereLineFlowCertificate
