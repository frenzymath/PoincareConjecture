import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_PolarInverse
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.CompactExtension





noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff Manifold Matrix

namespace PoincareConjecture





theorem m64Intrinsic_exists_compact_normal_inverse
    {e : AnnulusCoordinates → AnnulusCoordinates} (he : ContDiff ℝ ∞ e)
    {a T : ℝ} (hinj : InjOn (fun t => e !₂[a, t]) (Icc 0 T))
    (hreg : ∀ t ∈ Icc 0 T, Function.Injective (mfderiv (𝓡 2) (𝓡 2) e !₂[a, t])) :
    ∃ F : OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates,
      (fun t => !₂[a, t]) '' Icc 0 T ⊆ F.source ∧
      (fun t => e !₂[a, t]) '' Icc 0 T ⊆ F.target ∧
      EqOn F e F.source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target := by
  let S : Set AnnulusCoordinates := (fun t => !₂[a, t]) '' Icc 0 T
  have hline : Continuous (fun t : ℝ => (!₂[a, t] : AnnulusCoordinates)) := by fun_prop
  have hS : IsCompact S := isCompact_Icc.image hline
  have hSi : InjOn e S := by
    rintro _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩ hst
    exact congrArg (fun u : ℝ => (!₂[a, u] : AnnulusCoordinates)) (hinj hs ht hst)
  have hlocal : ∀ x ∈ S, IsLocalDiffeomorphAt (𝓡 2) (𝓡 2) ∞ e x := by
    rintro _ ⟨t, ht, rfl⟩
    obtain ⟨F, hxF, _, hF, hFs, hFi⟩ :=
      m64Intrinsic_exists_smooth_polar_inverse isOpen_univ
        (contMDiff_iff_contDiff.mpr he).contMDiffOn (mem_univ _) (hreg t ht)
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
  exact htarget ⟨!₂[a, t], ⟨t, ht, rfl⟩, rfl⟩





theorem m64Intrinsic_exists_embedded_prefix_tube
    {e : AnnulusCoordinates → AnnulusCoordinates} (he : ContDiff ℝ ∞ e)
    {a T : ℝ} (hinj : InjOn (fun t => e !₂[a, t]) (Icc 0 T))
    (hreg : ∀ t ∈ Icc 0 T, Function.Injective (mfderiv (𝓡 2) (𝓡 2) e !₂[a, t])) :
    ∃ W : Set ℝ, IsOpen W ∧ a ∈ W ∧
      InjOn e {z : AnnulusCoordinates | z 0 ∈ W ∧ z 1 ∈ Icc 0 T} := by
  obtain ⟨F, hsource, _, hF, _, _⟩ :=
    m64Intrinsic_exists_compact_normal_inverse he hinj hreg
  have hpair : Continuous (fun p : ℝ × ℝ => (!₂[p.1, p.2] : AnnulusCoordinates)) := by
    fun_prop
  have hopen : IsOpen {p : ℝ × ℝ | !₂[p.1, p.2] ∈ F.source} :=
    F.open_source.preimage hpair
  have hsub : ({a} : Set ℝ) ×ˢ Icc 0 T ⊆
      {p : ℝ × ℝ | !₂[p.1, p.2] ∈ F.source} := by
    rintro ⟨p, t⟩ ⟨hp, ht⟩
    have hpa : p = a := hp
    subst p
    exact hsource (mem_image_of_mem _ ht)
  obtain ⟨W, J, hW, _, haW, hTJ, hWJ⟩ :=
    generalized_tube_lemma isCompact_singleton isCompact_Icc hopen hsub
  have hsource' : {z : AnnulusCoordinates | z 0 ∈ W ∧ z 1 ∈ Icc 0 T} ⊆ F.source := by
    intro z hz
    have h := hWJ (show (z 0, z 1) ∈ W ×ˢ J from ⟨hz.1, hTJ hz.2⟩)
    have heta : !₂[z 0, z 1] = z := by ext i; fin_cases i <;> rfl
    change !₂[z 0, z 1] ∈ F.source at h
    simpa only [heta] using h
  refine ⟨W, hW, haW (mem_singleton a), ?_⟩
  intro x hx y hy hxy
  exact F.injOn (hsource' hx) (hsource' hy)
    ((hF (hsource' hx)).trans (hxy.trans (hF (hsource' hy)).symm))

end PoincareConjecture
