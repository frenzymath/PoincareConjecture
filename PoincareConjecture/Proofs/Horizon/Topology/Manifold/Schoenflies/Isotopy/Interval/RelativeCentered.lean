import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Isotopy.Interval.RelativeMatching
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Isotopy.Interval.Local

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

private abbrev E2 := EuclideanSpace Real (Fin 2)

private theorem smooth_inverse_family
    (Psi : Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (hPsi : ContDiff Real ∞ (fun z : Real × E2 => Psi z.1 z.2)) :
    ContDiff Real ∞ (fun z : Real × E2 => (Psi z.1).symm z.2) := by
  have hm : ContMDiff (𝓘(Real, Real).prod (𝓡 2)) (𝓡 2) ∞
      (fun z : Real × E2 => Psi z.1 z.2) := by
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
    exact hPsi.contMDiff
  have hi := Poincare.Manifold.contMDiff_diffeomorph_family_symm Psi hm
  rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hi
  exact hi.contDiff

theorem exists_centered_relative_matching_of_interval_families
    {r l l₀ l₁ u₁ u₀ u : Real} (hr : 0 < r)
    (hll₀ : l ≤ l₀) (hl₀l₁ : l₀ < l₁) (hl₁u₁ : l₁ ≤ u₁)
    (hu₁u₀ : u₁ < u₀) (hu₀u : u₀ ≤ u)
    {U : Set E2} (hU : IsOpen U)
    (f g : Real × Real → E2) {W : Set (Real × Real)}
    (hW : IsOpen W) (hrect : Icc (-r) r ×ˢ Icc l u ⊆ W)
    (hf : ContDiffOn Real ∞ f W) (hg : ContDiffOn Real ∞ g W)
    (hfi : ∀ t ∈ Icc (-r) r, InjOn (fun s => f (t, s)) (Icc l u))
    (hgi : ∀ t ∈ Icc (-r) r, InjOn (fun s => g (t, s)) (Icc l u))
    (hfd : ∀ t ∈ Icc (-r) r, ∀ s ∈ Icc l u, deriv (fun y => f (t, y)) s ≠ 0)
    (hgd : ∀ t ∈ Icc (-r) r, ∀ s ∈ Icc l u, deriv (fun y => g (t, y)) s ≠ 0)
    (hstart : ∀ s ∈ Icc l u, f (0, s) = g (0, s))
    (hends : ∀ t ∈ Icc (-r) r, ∀ s ∈ Icc l l₁ ∪ Icc u₁ u, f (t, s) = g (t, s))
    (hfU : ∀ t ∈ Icc (-r) r, ∀ s ∈ Icc l u, f (t, s) ∈ U)
    (hgU : ∀ t ∈ Icc (-r) r, ∀ s ∈ Icc l u, g (t, s) ∈ U) :
    ∃ (K : Set E2) (V : Set (Real × E2)), IsCompact K ∧ K ⊆ U ∧ IsOpen V ∧
      (∀ t ∈ Icc (-r) r, ∀ s ∈ Icc l l₀ ∪ Icc u₀ u, (t, f (t, s)) ∈ V) ∧
      ∃ D : Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
        (∀ x, D 0 x = x) ∧
        ContDiff Real ∞ (fun z : Real × E2 => D z.1 z.2) ∧
        (∀ t x, x ∉ K → D t x = x) ∧
        (∀ t x, (t, x) ∈ V → D t x = x) ∧
        ∀ t ∈ Icc (-r) r, ∀ s ∈ Icc l u, D t (f (t, s)) = g (t, s) := by
  have hab : -r < r := by linarith
  have ha : -r ∈ Icc (-r) r := ⟨le_rfl, hab.le⟩
  have hzero : (0 : Real) ∈ Icc (-r) r := ⟨by linarith, hr.le⟩
  have hmid : Icc l₁ u₁ ⊆ Icc l u :=
    Icc_subset_Icc (hll₀.trans hl₀l₁.le) (hu₁u₀.le.trans hu₀u)
  have hend : Icc l l₁ ∪ Icc u₁ u ⊆ Icc l u := by
    intro s hs
    rcases hs with hs | hs
    · exact ⟨hs.1, hs.2.trans (hl₁u₁.trans (hu₁u₀.le.trans hu₀u))⟩
    · exact ⟨(hll₀.trans (hl₀l₁.le.trans hl₁u₁)).trans hs.1, hs.2⟩
  have hendSmall : Icc l l₀ ∪ Icc u₀ u ⊆ Icc l l₁ ∪ Icc u₁ u := by
    intro s hs
    rcases hs with hs | hs
    · exact Or.inl ⟨hs.1, hs.2.trans hl₀l₁.le⟩
    · exact Or.inr ⟨hu₁u₀.le.trans hs.1, hs.2⟩
  obtain ⟨K₀, hK₀, hK₀U, Psi, hPsiₐ, hPsi, hPsifix, hPsimotion⟩ :=
    exists_ambient_isotopy_of_interval_isotopy_within_of_contDiffOn
      hU g hW hrect hg hgi hgd hgU
  have hPsiinv := smooth_inverse_family Psi hPsi
  have hPsiₐinv (x : E2) : (Psi (-r)).symm x = x := by
    apply (Psi (-r)).injective
    exact ((Psi (-r)).apply_symm_apply x).trans (hPsiₐ x).symm
  have hPsifixinv (t : Real) (x : E2) (hx : x ∉ K₀) : (Psi t).symm x = x := by
    apply (Psi t).injective
    exact ((Psi t).apply_symm_apply x).trans (hPsifix t x hx).symm
  let F : Real × Real → E2 := fun z => (Psi z.1).symm (f z)
  have hF : ContDiffOn Real ∞ F W :=
    hPsiinv.contDiffOn.comp (contDiff_fst.contDiffOn.prodMk hf) (mapsTo_univ _ _)
  have hFₐ (s : Real) : F (-r, s) = f (-r, s) := hPsiₐinv _
  have hFi : ∀ t ∈ Icc (-r) r, InjOn (fun s => F (t, s)) (Icc l u) := by
    intro t ht s hs y hy he
    exact hfi t ht hs hy ((Psi t).symm.injective he)
  have hFd : ∀ t ∈ Icc (-r) r, ∀ s ∈ Icc l u,
      deriv (fun y => F (t, y)) s ≠ 0 := by
    intro t ht s hs
    have hslice : DifferentiableAt Real (fun y => f (t, y)) s :=
      ((hf.contDiffAt (hW.mem_nhds (hrect ⟨ht, hs⟩))).comp s
        ((contDiff_const.prodMk contDiff_id).contDiffAt)).differentiableAt (by simp)
    have hp : HasDerivAt (fun y => F (t, y))
        (fderiv Real (Psi t).symm (f (t, s)) (deriv (fun y => f (t, y)) s)) s :=
      (((Psi t).symm.contMDiff.contDiff.differentiable (by simp) _).hasFDerivAt).comp_hasDerivAt s
        hslice.hasDerivAt
    have hinv : Injective (fderiv Real (Psi t).symm (f (t, s))) := by
      have h : Injective (mfderiv (𝓡 2) (𝓡 2) (Psi t).symm (f (t, s))) :=
        ((Psi t).symm.mfderivToContinuousLinearEquiv (by simp) _).injective
      rwa [mfderiv_eq_fderiv] at h
    rw [hp.deriv]
    intro hz
    exact hfd t ht s hs (hinv (hz.trans (map_zero _).symm))
  have hFend : ∀ t ∈ Icc (-r) r, ∀ s ∈ Icc l l₁ ∪ Icc u₁ u, F (t, s) = F (-r, s) := by
    intro t ht s hs
    change (Psi t).symm (f (t, s)) = F (-r, s)
    rw [hends t ht s hs, ← hPsimotion t ht s (hend hs), (Psi t).symm_apply_apply,
      hFₐ s, hends (-r) ha s hs]
  have hFU : ∀ t ∈ Icc (-r) r, ∀ s ∈ Icc l₁ u₁, F (t, s) ∈ U := by
    intro t ht s hs
    by_contra hout
    have hfix := hPsifix t (F (t, s)) (fun hx => hout (hK₀U hx))
    apply hout
    rw [← hfix]
    change (Psi t) ((Psi t).symm (f (t, s))) ∈ U
    rw [(Psi t).apply_symm_apply]
    exact hfU t ht s (hmid hs)
  have hFcenter (s : Real) (hs : s ∈ Icc l u) : F (0, s) = g (-r, s) := by
    change (Psi 0).symm (f (0, s)) = g (-r, s)
    rw [hstart s hs, ← hPsimotion 0 hzero s hs, (Psi 0).symm_apply_apply]
  obtain ⟨K₁, O, hK₁, hK₁U, hO, hendsO, _, Omega, _, hOmega,
      hOmegafix, hOmegafixO, hOmegamotion⟩ :=
    exists_relative_ambient_isotopy_of_interval_isotopy_within_of_contDiffOn
      hab hll₀ hl₀l₁ hl₁u₁ hu₁u₀ hu₀u hU F hW hrect hF hFi hFd hFend hFU
  have hOmegainv := smooth_inverse_family Omega hOmega
  have hOmegafixinv (t : Real) (x : E2) (hx : x ∉ K₁) : (Omega t).symm x = x := by
    apply (Omega t).injective
    exact ((Omega t).apply_symm_apply x).trans (hOmegafix t x hx).symm
  have hOmegafixOinv (t : Real) (x : E2) (hx : x ∈ O) : (Omega t).symm x = x := by
    apply (Omega t).injective
    exact ((Omega t).apply_symm_apply x).trans (hOmegafixO t x hx).symm
  let D : Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞ :=
    fun t => (Psi t).symm.trans ((Omega t).symm.trans ((Omega 0).trans (Psi t)))
  let V : Set (Real × E2) := (fun z : Real × E2 => (Psi z.1).symm z.2) ⁻¹' O
  refine ⟨K₀ ∪ K₁, V, hK₀.union hK₁, union_subset hK₀U hK₁U,
    hO.preimage hPsiinv.continuous, ?_, D, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht s hs
    change F (t, s) ∈ O
    rw [hFend t ht s (hendSmall hs)]
    exact hendsO (mem_image_of_mem _ hs)
  · intro x
    change Psi 0 (Omega 0 ((Omega 0).symm ((Psi 0).symm x))) = x
    rw [(Omega 0).apply_symm_apply, (Psi 0).apply_symm_apply]
  · exact hPsi.comp (contDiff_fst.prodMk ((Omega 0).contMDiff.contDiff.comp
      (hOmegainv.comp (contDiff_fst.prodMk hPsiinv))))
  · intro t x hx
    change Psi t (Omega 0 ((Omega t).symm ((Psi t).symm x))) = x
    rw [hPsifixinv t x (fun hx₀ => hx (Or.inl hx₀)),
      hOmegafixinv t x (fun hx₁ => hx (Or.inr hx₁)),
      hOmegafix 0 x (fun hx₁ => hx (Or.inr hx₁)),
      hPsifix t x (fun hx₀ => hx (Or.inl hx₀))]
  · intro t x hx
    change Psi t (Omega 0 ((Omega t).symm ((Psi t).symm x))) = x
    rw [hOmegafixOinv t _ hx, hOmegafixO 0 _ hx, (Psi t).apply_symm_apply]
  · intro t ht s hs
    change Psi t (Omega 0 ((Omega t).symm (F (t, s)))) = g (t, s)
    rw [← hOmegamotion t ht s hs, (Omega t).symm_apply_apply,
      hOmegamotion 0 hzero s hs, hFcenter s hs]
    exact hPsimotion t ht s hs

end Poincare.Manifold.Schoenflies
