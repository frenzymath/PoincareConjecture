import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_PolarInverse
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.CompactExtension





noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff Manifold

namespace PoincareConjecture




theorem m64Intrinsic_exists_compact_radial_inverse
    {e : AnnulusCoordinates → AnnulusCoordinates} {Omega : Set AnnulusCoordinates}
    (hOmega : IsOpen Omega) (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e Omega)
    {v : AnnulusCoordinates}
    (hsub : ∀ t ∈ Icc (0 : ℝ) 1, t • v ∈ Omega)
    (hinj : InjOn (fun t : ℝ => e (t • v)) (Icc (0 : ℝ) 1))
    (hreg : ∀ t ∈ Icc (0 : ℝ) 1,
      Function.Injective (mfderiv (𝓡 2) (𝓡 2) e (t • v))) :
    ∃ F : OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates,
      (fun t : ℝ => t • v) '' Icc (0 : ℝ) 1 ⊆ F.source ∧
      (fun t : ℝ => e (t • v)) '' Icc (0 : ℝ) 1 ⊆ F.target ∧
      EqOn F e F.source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target := by
  let S : Set AnnulusCoordinates := (fun t : ℝ => t • v) '' Icc (0 : ℝ) 1
  have hS : IsCompact S := isCompact_Icc.image (continuous_id.smul continuous_const)
  have hSi : InjOn e S := by
    rintro _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩ heq
    exact congrArg (fun a : ℝ => a • v) (hinj hs ht heq)
  have hlocal : ∀ x ∈ S, IsLocalDiffeomorphAt (𝓡 2) (𝓡 2) ∞ e x := by
    rintro _ ⟨t, ht, rfl⟩
    obtain ⟨F, hxF, _, hF, hFs, hFi⟩ :=
      m64Intrinsic_exists_smooth_polar_inverse hOmega he (hsub t ht) (hreg t ht)
    refine ⟨{ toPartialEquiv := F.toPartialEquiv
              open_source := F.open_source
              open_target := F.open_target
              contMDiffOn_toFun := contMDiffOn_iff_contDiffOn.mpr hFs
              contMDiffOn_invFun := contMDiffOn_iff_contDiffOn.mpr hFi }, hxF, ?_⟩
    intro x _
    exact (congrFun hF x).symm
  obtain ⟨F, hsource, htarget, hF, hFs, hFi⟩ :=
    Poincare.exists_openPartialHomeomorph_of_injOn_compact hS hSi hlocal
  refine ⟨F, hsource, ?_, hF, hFs, hFi⟩
  rintro _ ⟨t, ht, rfl⟩
  exact htarget ⟨t • v, ⟨t, ht, rfl⟩, rfl⟩

end PoincareConjecture
