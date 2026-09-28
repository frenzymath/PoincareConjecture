import PoincareConjecture.Proofs.M35.CapGeometry.CarrierTopology

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.CapCertificate

theorem transported_boundary_local_defining_function
    {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
    [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ N]
    [MeasurableSpace M] [BorelSpace M] [T3Space M]
    {g : RiemannianMetric 3 M} (C : CapCertificate g)
    (phi : PartialDiffeomorph (𝓡 3) (𝓡 3) M N ∞)
    (hU : C.carrier ⊆ phi.source) :
    ∀ p ∈ phi '' C.boundary_sphere, ∃ V : Set N, ∃ f : N → ℝ,
      IsOpen V ∧ p ∈ V ∧ V ⊆ phi '' C.carrier ∧
        (∀ q ∈ V, q ∈ phi '' C.closed_core ↔ f q ≤ 0) ∧ f p = 0 ∧
        ContMDiffOn (𝓡 3) 𝓘(ℝ, ℝ) ∞ f V ∧
        ∃ d : TangentSpace (𝓡 3) p, d ≠ 0 ∧ mvfderiv (𝓡 3) f p d ≠ 0 := by
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨V, f, hV, hxV, hVU, hcore, hfx, hf, d, hd, hdf⟩ :=
    C.boundary_local_defining_function x hx
  have hVs : V ⊆ phi.source := hVU.trans hU
  have hxsource := hVs hxV
  have hleft : phi.invFun (phi x) = x := phi.left_inv hxsource
  have himage : phi '' V ⊆ phi.target := by
    rintro _ ⟨z, hz, rfl⟩
    exact phi.map_source (hVs hz)
  have hinverse : MapsTo phi.invFun (phi '' V) V := by
    rintro _ ⟨z, hz, rfl⟩
    have hzleft : phi.invFun (phi z) = z := phi.left_inv (hVs hz)
    exact hzleft.symm ▸ hz
  refine ⟨phi '' V, f ∘ phi.invFun,
    phi.toOpenPartialHomeomorph.isOpen_image_of_subset_source hV hVs,
    ⟨x, hxV, rfl⟩, image_mono hVU, ?_, ?_,
    hf.comp (phi.contMDiffOn_invFun.mono himage) hinverse, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    have hzleft : phi.invFun (phi z) = z := phi.left_inv (hVs hz)
    change phi z ∈ phi '' C.closed_core ↔ f (phi.invFun (phi z)) ≤ 0
    rw [hzleft, ← hcore z hz]
    constructor
    · rintro ⟨w, hw, heq⟩
      have hwU : w ∈ C.carrier := by
        rw [C.closed_core_eq_complement_end] at hw
        exact hw.1
      exact phi.toPartialEquiv.injOn (hU hwU) (hVs hz) heq ▸ hw
    · intro hzc
      exact ⟨z, hzc, rfl⟩
  · change f (phi.invFun (phi x)) = 0
    rw [hleft, hfx]
  · have hphi := phi.mdifferentiableAt (by simp) hxsource
    have hinv : MDifferentiableAt (𝓡 3) (𝓡 3) phi.invFun (phi x) :=
      phi.symm.mdifferentiableAt (by simp) (phi.map_source hxsource)
    have hidentity : (phi.invFun ∘ phi) =ᶠ[𝓝 x] id :=
      eventuallyEq_of_mem (phi.open_source.mem_nhds hxsource)
        (fun z hz => phi.left_inv hz)
    have hderiv : (mfderiv (𝓡 3) (𝓡 3) phi.invFun (phi x))
        ((mfderiv (𝓡 3) (𝓡 3) phi x) d) = d := by
      have h : mfderiv (𝓡 3) (𝓡 3) (phi.invFun ∘ phi) x =
          mfderiv (𝓡 3) (𝓡 3) (id : M → M) x := hidentity.mfderiv_eq
      rw [mfderiv_comp x hinv hphi, mfderiv_id] at h
      exact congrArg (fun A : EuclideanSpace ℝ (Fin 3) →L[ℝ]
        EuclideanSpace ℝ (Fin 3) => A d) h
    refine ⟨mfderiv (𝓡 3) (𝓡 3) phi x d, ?_, ?_⟩
    · intro hzero
      rw [hzero, map_zero] at hderiv
      exact hd hderiv.symm
    · have hfAt : MDifferentiableAt (𝓡 3) 𝓘(ℝ, ℝ) f (phi.invFun (phi x)) := by
        rw [hleft]
        exact (hf.contMDiffAt (hV.mem_nhds hxV)).mdifferentiableAt (by simp)
      rw [mvfderiv_comp_apply (phi x) hfAt hinv, hderiv, hleft]
      exact hdf

end PoincareConjecture.CapCertificate
