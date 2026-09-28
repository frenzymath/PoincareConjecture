import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Isotopy.Interval.RelativeLocal
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.BallExtension.ParametricInverse

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function Filter
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies

private abbrev E2 := EuclideanSpace Real (Fin 2)

private theorem contDiff_planar_diffeomorph_family_symm
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

theorem exists_relative_matching_of_interval_families
    {a b l l₀ l₁ u₁ u₀ u : Real} (hab : a < b)
    (hll₀ : l ≤ l₀) (hl₀l₁ : l₀ < l₁) (hl₁u₁ : l₁ ≤ u₁)
    (hu₁u₀ : u₁ < u₀) (hu₀u : u₀ ≤ u)
    {U : Set E2} (hU : IsOpen U)
    (f g : Real × Real → E2) (hf : ContDiff Real ∞ f) (hg : ContDiff Real ∞ g)
    (hfi : ∀ t ∈ Icc a b, InjOn (fun s => f (t, s)) (Icc l u))
    (hgi : ∀ t ∈ Icc a b, InjOn (fun s => g (t, s)) (Icc l u))
    (hfd : ∀ t ∈ Icc a b, ∀ s ∈ Icc l u, deriv (fun y => f (t, y)) s ≠ 0)
    (hgd : ∀ t ∈ Icc a b, ∀ s ∈ Icc l u, deriv (fun y => g (t, y)) s ≠ 0)
    (hstart : ∀ s ∈ Icc l u, f (a, s) = g (a, s))
    (hends : ∀ t ∈ Icc a b, ∀ s ∈ Icc l l₁ ∪ Icc u₁ u, f (t, s) = g (t, s))
    (hfU : ∀ t ∈ Icc a b, ∀ s ∈ Icc l u, f (t, s) ∈ U)
    (hgU : ∀ t ∈ Icc a b, ∀ s ∈ Icc l u, g (t, s) ∈ U) :
    ∃ (K : Set E2) (V : Set (Real × E2)), IsCompact K ∧ K ⊆ U ∧ IsOpen V ∧
      (∀ t ∈ Icc a b, ∀ s ∈ Icc l l₀ ∪ Icc u₀ u, (t, f (t, s)) ∈ V) ∧
      ∃ D : Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
        (∀ x, D a x = x) ∧
        ContDiff Real ∞ (fun z : Real × E2 => D z.1 z.2) ∧
        (∀ t x, x ∉ K → D t x = x) ∧
        (∀ t x, (t, x) ∈ V → D t x = x) ∧
        ∀ t ∈ Icc a b, ∀ s ∈ Icc l u, D t (f (t, s)) = g (t, s) := by
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
  obtain ⟨K₀, hK₀, hK₀U, Psi, hPsi₀, hPsi, hPsifix, hPsimotion⟩ :=
    exists_ambient_isotopy_of_interval_isotopy_within hU g hg hgi hgd hgU
  have hPsiinv := contDiff_planar_diffeomorph_family_symm Psi hPsi
  have hPsi₀inv (x : E2) : (Psi a).symm x = x := by
    apply (Psi a).injective
    exact ((Psi a).apply_symm_apply x).trans (hPsi₀ x).symm
  have hPsifixinv (t : Real) (x : E2) (hx : x ∉ K₀) : (Psi t).symm x = x := by
    apply (Psi t).injective
    exact ((Psi t).apply_symm_apply x).trans (hPsifix t x hx).symm
  let F : Real × Real → E2 := fun z => (Psi z.1).symm (f z)
  have hF : ContDiff Real ∞ F := hPsiinv.comp (contDiff_fst.prodMk hf)
  have hF₀ (s : Real) : F (a, s) = f (a, s) := hPsi₀inv _
  have hFi : ∀ t ∈ Icc a b, InjOn (fun s => F (t, s)) (Icc l u) := by
    intro t ht s hs y hy he
    exact hfi t ht hs hy ((Psi t).symm.injective he)
  have hFd : ∀ t ∈ Icc a b, ∀ s ∈ Icc l u,
      deriv (fun y => F (t, y)) s ≠ 0 := by
    intro t ht s hs
    have hp : HasDerivAt (fun y => F (t, y))
        (fderiv Real (Psi t).symm (f (t, s)) (deriv (fun y => f (t, y)) s)) s :=
      (((Psi t).symm.contMDiff.contDiff.differentiable (by simp) _).hasFDerivAt).comp_hasDerivAt s
        (((hf.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp) s).hasDerivAt)
    have hinv : Injective (fderiv Real (Psi t).symm (f (t, s))) := by
      have h : Injective (mfderiv (𝓡 2) (𝓡 2) (Psi t).symm (f (t, s))) :=
        ((Psi t).symm.mfderivToContinuousLinearEquiv (by simp) _).injective
      rwa [mfderiv_eq_fderiv] at h
    rw [hp.deriv]
    intro hz
    exact hfd t ht s hs (hinv (hz.trans (map_zero _).symm))
  have hFend : ∀ t ∈ Icc a b, ∀ s ∈ Icc l l₁ ∪ Icc u₁ u, F (t, s) = F (a, s) := by
    intro t ht s hs
    change (Psi t).symm (f (t, s)) = F (a, s)
    rw [hends t ht s hs, ← hPsimotion t ht s (hend hs), (Psi t).symm_apply_apply,
      hF₀ s, hstart s (hend hs)]
  have hFU : ∀ t ∈ Icc a b, ∀ s ∈ Icc l₁ u₁, F (t, s) ∈ U := by
    intro t ht s hs
    by_contra hout
    have hfix := hPsifix t (F (t, s)) (fun hx => hout (hK₀U hx))
    apply hout
    rw [← hfix]
    change (Psi t) ((Psi t).symm (f (t, s))) ∈ U
    rw [(Psi t).apply_symm_apply]
    exact hfU t ht s (hmid hs)
  obtain ⟨K₁, O, hK₁, hK₁U, hO, hendsO, _, Omega, hOmega₀, hOmega,
      hOmegafix, hOmegafixO, hOmegamotion⟩ :=
    exists_relative_ambient_isotopy_of_interval_isotopy_within
      hab hll₀ hl₀l₁ hl₁u₁ hu₁u₀ hu₀u hU F hF hFi hFd hFend hFU
  have hOmegainv := contDiff_planar_diffeomorph_family_symm Omega hOmega
  have hOmegafixinv (t : Real) (x : E2) (hx : x ∉ K₁) : (Omega t).symm x = x := by
    apply (Omega t).injective
    exact ((Omega t).apply_symm_apply x).trans (hOmegafix t x hx).symm
  have hOmegafixOinv (t : Real) (x : E2) (hx : x ∈ O) : (Omega t).symm x = x := by
    apply (Omega t).injective
    exact ((Omega t).apply_symm_apply x).trans (hOmegafixO t x hx).symm
  let D : Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞ :=
    fun t => (Psi t).symm.trans ((Omega t).symm.trans (Psi t))
  let V : Set (Real × E2) := (fun z : Real × E2 => (Psi z.1).symm z.2) ⁻¹' O
  refine ⟨K₀ ∪ K₁, V, hK₀.union hK₁, union_subset hK₀U hK₁U,
    hO.preimage hPsiinv.continuous, ?_, D, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht s hs
    change F (t, s) ∈ O
    rw [hFend t ht s (hendSmall hs)]
    exact hendsO (mem_image_of_mem _ hs)
  · intro x
    change (Psi a) ((Omega a).symm ((Psi a).symm x)) = x
    have hOi (y : E2) : (Omega a).symm y = y := by
      apply (Omega a).injective
      exact ((Omega a).apply_symm_apply y).trans (hOmega₀ y).symm
    rw [hOi, (Psi a).apply_symm_apply]
  · exact hPsi.comp (contDiff_fst.prodMk
      (hOmegainv.comp (contDiff_fst.prodMk hPsiinv)))
  · intro t x hx
    change (Psi t) ((Omega t).symm ((Psi t).symm x)) = x
    rw [hPsifixinv t x (fun hx₀ => hx (Or.inl hx₀)),
      hOmegafixinv t x (fun hx₁ => hx (Or.inr hx₁)),
      hPsifix t x (fun hx₀ => hx (Or.inl hx₀))]
  · intro t x hx
    change (Psi t) ((Omega t).symm ((Psi t).symm x)) = x
    rw [hOmegafixOinv t _ hx, (Psi t).apply_symm_apply]
  · intro t ht s hs
    change (Psi t) ((Omega t).symm (F (t, s))) = g (t, s)
    rw [← hOmegamotion t ht s hs, (Omega t).symm_apply_apply, hF₀ s, hstart s hs]
    exact hPsimotion t ht s hs

theorem exists_relative_matching_of_interval_families_of_contDiffOn
    {a b l l₀ l₁ u₁ u₀ u : Real} (hab : a < b)
    (hll₀ : l ≤ l₀) (hl₀l₁ : l₀ < l₁) (hl₁u₁ : l₁ ≤ u₁)
    (hu₁u₀ : u₁ < u₀) (hu₀u : u₀ ≤ u)
    {U : Set E2} (hU : IsOpen U)
    (f g : Real × Real → E2) {W : Set (Real × Real)}
    (hW : IsOpen W) (hrect : Icc a b ×ˢ Icc l u ⊆ W)
    (hf : ContDiffOn Real ∞ f W) (hg : ContDiffOn Real ∞ g W)
    (hfi : ∀ t ∈ Icc a b, InjOn (fun s => f (t, s)) (Icc l u))
    (hgi : ∀ t ∈ Icc a b, InjOn (fun s => g (t, s)) (Icc l u))
    (hfd : ∀ t ∈ Icc a b, ∀ s ∈ Icc l u, deriv (fun y => f (t, y)) s ≠ 0)
    (hgd : ∀ t ∈ Icc a b, ∀ s ∈ Icc l u, deriv (fun y => g (t, y)) s ≠ 0)
    (hstart : ∀ s ∈ Icc l u, f (a, s) = g (a, s))
    (hends : ∀ t ∈ Icc a b, ∀ s ∈ Icc l l₁ ∪ Icc u₁ u, f (t, s) = g (t, s))
    (hfU : ∀ t ∈ Icc a b, ∀ s ∈ Icc l u, f (t, s) ∈ U)
    (hgU : ∀ t ∈ Icc a b, ∀ s ∈ Icc l u, g (t, s) ∈ U) :
    ∃ (K : Set E2) (V : Set (Real × E2)), IsCompact K ∧ K ⊆ U ∧ IsOpen V ∧
      (∀ t ∈ Icc a b, ∀ s ∈ Icc l l₀ ∪ Icc u₀ u, (t, f (t, s)) ∈ V) ∧
      ∃ D : Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
        (∀ x, D a x = x) ∧
        ContDiff Real ∞ (fun z : Real × E2 => D z.1 z.2) ∧
        (∀ t x, x ∉ K → D t x = x) ∧
        (∀ t x, (t, x) ∈ V → D t x = x) ∧
        ∀ t ∈ Icc a b, ∀ s ∈ Icc l u, D t (f (t, s)) = g (t, s) := by
  have hend : Icc l l₁ ∪ Icc u₁ u ⊆ Icc l u := by
    intro s hs
    rcases hs with hs | hs
    · exact ⟨hs.1, hs.2.trans (hl₁u₁.trans (hu₁u₀.le.trans hu₀u))⟩
    · exact ⟨(hll₀.trans (hl₀l₁.le.trans hl₁u₁)).trans hs.1, hs.2⟩
  have hendSmall : Icc l l₀ ∪ Icc u₀ u ⊆ Icc l u := by
    intro s hs
    apply hend
    rcases hs with hs | hs
    · exact Or.inl ⟨hs.1, hs.2.trans hl₀l₁.le⟩
    · exact Or.inr ⟨hu₁u₀.le.trans hs.1, hs.2⟩
  obtain ⟨H, N, hH, hN, hKN, _, hHeq⟩ :=
    Poincare.Analysis.exists_contDiff_extension_near_compact
      (isCompact_Icc.prod isCompact_Icc) hW hrect
      (fun z => (f z, g z)) (hf.prodMk hg)
  let F : Real × Real → E2 := fun z => (H z).1
  let G : Real × Real → E2 := fun z => (H z).2
  have hF : ContDiff Real ∞ F := contDiff_fst.comp hH
  have hG : ContDiff Real ∞ G := contDiff_snd.comp hH
  have heqF (t : Real) (ht : t ∈ Icc a b) (s : Real) (hs : s ∈ Icc l u) :
      F (t, s) = f (t, s) := congrArg Prod.fst (hHeq (hKN ⟨ht, hs⟩))
  have heqG (t : Real) (ht : t ∈ Icc a b) (s : Real) (hs : s ∈ Icc l u) :
      G (t, s) = g (t, s) := congrArg Prod.snd (hHeq (hKN ⟨ht, hs⟩))
  have hnear (t : Real) (ht : t ∈ Icc a b) (s : Real) (hs : s ∈ Icc l u) :
      ∀ᶠ y in 𝓝 s, (t, y) ∈ N :=
    (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds
      (hN.mem_nhds (hKN ⟨ht, hs⟩))
  have hFd (t : Real) (ht : t ∈ Icc a b) (s : Real) (hs : s ∈ Icc l u) :
      deriv (fun y => F (t, y)) s = deriv (fun y => f (t, y)) s :=
    Filter.EventuallyEq.deriv_eq ((hnear t ht s hs).mono
      (fun _ hy => congrArg Prod.fst (hHeq hy)))
  have hGd (t : Real) (ht : t ∈ Icc a b) (s : Real) (hs : s ∈ Icc l u) :
      deriv (fun y => G (t, y)) s = deriv (fun y => g (t, y)) s :=
    Filter.EventuallyEq.deriv_eq ((hnear t ht s hs).mono
      (fun _ hy => congrArg Prod.snd (hHeq hy)))
  have ha : a ∈ Icc a b := ⟨le_rfl, hab.le⟩
  obtain ⟨K, V, hK, hKU, hV, hendV, D, hD₀, hD, hfix, hfixV, hmotion⟩ :=
    exists_relative_matching_of_interval_families
      hab hll₀ hl₀l₁ hl₁u₁ hu₁u₀ hu₀u hU F G hF hG (by
        intro t ht s hs y hy he
        apply hfi t ht hs hy
        simpa only [heqF t ht s hs, heqF t ht y hy] using he) (by
        intro t ht s hs y hy he
        apply hgi t ht hs hy
        simpa only [heqG t ht s hs, heqG t ht y hy] using he) (by
        intro t ht s hs
        rw [hFd t ht s hs]
        exact hfd t ht s hs) (by
        intro t ht s hs
        rw [hGd t ht s hs]
        exact hgd t ht s hs) (by
        intro s hs
        rw [heqF a ha s hs, heqG a ha s hs]
        exact hstart s hs) (by
        intro t ht s hs
        rw [heqF t ht s (hend hs), heqG t ht s (hend hs)]
        exact hends t ht s hs) (by
        intro t ht s hs
        rw [heqF t ht s hs]
        exact hfU t ht s hs) (by
        intro t ht s hs
        rw [heqG t ht s hs]
        exact hgU t ht s hs)
  refine ⟨K, V, hK, hKU, hV, ?_, D, hD₀, hD, hfix, hfixV, ?_⟩
  · intro t ht s hs
    simpa only [heqF t ht s (hendSmall hs)] using hendV t ht s hs
  · intro t ht s hs
    simpa only [heqF t ht s hs, heqG t ht s hs] using hmotion t ht s hs

end Poincare.Manifold.Schoenflies
