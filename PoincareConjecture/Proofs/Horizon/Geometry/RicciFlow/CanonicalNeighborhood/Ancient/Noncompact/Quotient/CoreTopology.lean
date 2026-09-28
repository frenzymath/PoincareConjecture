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

theorem preimage_slabCore (C : M27TwistedSphereLineFlowCertificate K) (r : ℝ) :
    C.cover ⁻¹' C.slabCore r = univ ×ˢ Icc (-r) r := by
  ext p
  simp only [mem_preimage, C.cover_mem_slabCore_iff, mem_prod, mem_univ,
    true_and, mem_Icc, abs_le]

theorem preimage_interior_slabCore (C : M27TwistedSphereLineFlowCertificate K)
    (r : ℝ) :
    C.cover ⁻¹' interior (C.slabCore r) = univ ×ˢ Ioo (-r) r := by
  rw [C.cover_local_diffeomorph.isOpenMap.preimage_interior_eq_interior_preimage
    C.cover_local_diffeomorph.isLocalHomeomorph.continuous, C.preimage_slabCore]
  simp only [interior_prod_eq, interior_univ, interior_Icc]

theorem cover_mem_interior_slabCore_iff (C : M27TwistedSphereLineFlowCertificate K)
    (r : ℝ) (p : UnitTwoSphere × ℝ) :
    C.cover p ∈ interior (C.slabCore r) ↔ |p.2| < r := by
  change p ∈ C.cover ⁻¹' interior (C.slabCore r) ↔ _
  rw [C.preimage_interior_slabCore]
  simp only [mem_prod, mem_univ, true_and, mem_Ioo, abs_lt]

theorem interior_slabCore (C : M27TwistedSphereLineFlowCertificate K) (r : ℝ) :
    interior (C.slabCore r) = C.cover '' (univ ×ˢ Ioo (-r) r) := by
  rw [← C.preimage_interior_slabCore, image_preimage_eq _ C.cover_surjective]

theorem cover_mem_frontier_slabCore_iff (C : M27TwistedSphereLineFlowCertificate K)
    (r : ℝ) (p : UnitTwoSphere × ℝ) :
    C.cover p ∈ frontier (C.slabCore r) ↔ |p.2| = r := by
  rw [(C.isCompact_slabCore r).isClosed.frontier_eq, mem_sdiff,
    C.cover_mem_slabCore_iff, C.cover_mem_interior_slabCore_iff]
  exact ⟨fun h => le_antisymm h.1 (le_of_not_gt h.2), fun h => ⟨h.le, not_lt.mpr h.ge⟩⟩

theorem frontier_slabCore (C : M27TwistedSphereLineFlowCertificate K)
    {r : ℝ} (hr : 0 ≤ r) :
    frontier (C.slabCore r) = C.cover '' (univ ×ˢ {r}) := by
  ext x
  obtain ⟨p, rfl⟩ := C.cover_surjective x
  rw [C.cover_mem_frontier_slabCore_iff]
  constructor
  · intro hp
    by_cases hsign : 0 ≤ p.2
    · have hs : p.2 = r := by simpa only [abs_of_nonneg hsign] using hp
      exact ⟨p, ⟨mem_univ _, hs⟩, rfl⟩
    · have hs : -p.2 = r := by simpa only [abs_of_neg (lt_of_not_ge hsign)] using hp
      refine ⟨m27TwistedProductInvolution p, ⟨mem_univ _, hs⟩, ?_⟩
      exact ((C.cover_fibers p (m27TwistedProductInvolution p)).mpr (Or.inr rfl)).symm
  · rintro ⟨q, hq, heq⟩
    have hmem : C.cover q ∈ frontier (C.slabCore r) := by
      rw [C.cover_mem_frontier_slabCore_iff, hq.2, abs_of_nonneg hr]
    rw [heq, C.cover_mem_frontier_slabCore_iff] at hmem
    exact hmem



theorem slabCore_boundary_local_defining_function
    (C : M27TwistedSphereLineFlowCertificate K) {r : ℝ} (hr : 0 < r)
    {A : Set M} (hA : IsOpen A) {x : M} (hx : x ∈ frontier (C.slabCore r))
    (hxA : x ∈ A) :
    ∃ U : Set M, ∃ f : M → ℝ, IsOpen U ∧ x ∈ U ∧ U ⊆ A ∧
      (∀ y ∈ U, y ∈ C.slabCore r ↔ f y ≤ 0) ∧ f x = 0 ∧
      ContMDiffOn (𝓡 3) 𝓘(ℝ, ℝ) ∞ f U ∧
      ∃ d : TangentSpace (𝓡 3) x, d ≠ 0 ∧ mvfderiv (𝓡 3) f x d ≠ 0 := by
  rw [C.frontier_slabCore hr.le] at hx
  obtain ⟨⟨a, s⟩, ⟨_, hs⟩, rfl⟩ := hx
  have hs' : s = r := hs
  subst s
  let hlocal := C.cover_local_diffeomorph (a, r)
  let e := hlocal.localInverse
  have hleft : e (C.cover (a, r)) = (a, r) :=
    hlocal.localInverse_left_inv hlocal.localInverse_mem_target
  let U : Set M := (e.source ∩ e ⁻¹' (univ ×ˢ Ioi (0 : ℝ))) ∩ A
  let g : UnitTwoSphere × ℝ → ℝ := fun q => q.2 - r
  have hg : ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ g :=
    contMDiff_snd.sub contMDiff_const
  have he : ContMDiffOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ e e.source :=
    hlocal.localInverse_contMDiffOn
  refine ⟨U, g ∘ e, ?_, ?_, fun _ hy => hy.2, ?_, ?_, ?_, ?_⟩
  · exact (e.toOpenPartialHomeomorph.isOpen_inter_preimage
      (isOpen_univ.prod isOpen_Ioi)).inter hA
  · exact ⟨⟨hlocal.localInverse_mem_source, by simpa only [mem_preimage, hleft,
      mem_prod, mem_univ, true_and, mem_Ioi] using hr⟩, hxA⟩
  · intro y hy
    have hpos : 0 < (e y).2 := hy.1.2.2
    have hright : C.cover (e y) = y := hlocal.localInverse_right_inv hy.1.1
    rw [← hright, C.cover_mem_slabCore_iff, hright,
      abs_of_pos hpos]
    exact sub_nonpos.symm
  · simp only [Function.comp_apply, hleft, g, sub_self]
  · exact hg.comp_contMDiffOn (he.mono (fun _ hy => hy.1.1))
  · let L := hlocal.localInverse_isLocalDiffeomorphAt.mfderivToContinuousLinearEquiv
      (by simp)
    let d : TangentSpace (𝓡 3) (C.cover (a, r)) := L.symm (0, 1)
    have hLd : mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) e (C.cover (a, r)) d =
        (0, 1) := L.apply_symm_apply _
    have hd : mvfderiv (𝓡 3) (g ∘ e) (C.cover (a, r)) d = 1 := by
      rw [mvfderiv_comp_apply _
        (hg.contMDiffAt.mdifferentiableAt (by simp))
        (hlocal.localInverse_mdifferentiableAt (by simp)), hLd]
      dsimp only [g]
      rw [mvfderiv_fun_sub mdifferentiableAt_snd mdifferentiableAt_const]
      simp [mvfderiv, mfderiv_snd]
      rfl
    refine ⟨d, ?_, by rw [hd]; exact one_ne_zero⟩
    intro hd0
    rw [hd0, map_zero] at hd
    exact zero_ne_one hd

end PoincareConjecture.M27TwistedSphereLineFlowCertificate
