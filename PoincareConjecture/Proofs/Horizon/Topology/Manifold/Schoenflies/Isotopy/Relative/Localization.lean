import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Isotopy.Flow
import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.Interior.LocalExtension

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies

theorem exists_supported_relative_family_localization_preserving_linear
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [FiniteDimensional Real E]
    (F : Real → Diffeomorph 𝓘(Real, E) 𝓘(Real, E) E E ∞)
    (hF : ContDiff Real ∞ (fun z : Real × E => F z.1 z.2))
    (hFi : ContDiff Real ∞ (fun z : Real × E => (F z.1).symm z.2))
    {K P U : Set E} (hK : IsCompact K) (hU : IsOpen U)
    (htrace : ∀ t ∈ Icc (0 : Real) 1, ∀ x ∈ K, F t x ∈ U)
    (hinit : EqOn (F 0) id K)
    (hstationary : ∀ t, EqOn (F t) id P)
    (l : E →L[Real] Real) (hlevel : ∀ t x, l (F t x) = l x) :
    ∃ S : Set E, IsCompact S ∧ S ⊆ U ∧
      ∃ G : Diffeomorph 𝓘(Real, E) 𝓘(Real, E) E E ∞,
        (∀ x ∉ S, G x = x) ∧ EqOn G id P ∧
        (∀ x, l (G x) = l x) ∧ EqOn G (F 1) K := by
  let f : Real × E → E := fun z => F z.1 z.2
  let W : Real × E → E := fun z =>
    fderiv Real f (z.1, (F z.1).symm z.2) (1, 0)
  have hW : ContDiff Real ∞ W :=
    ((hF.fderiv_right (by simp)).clm_apply contDiff_const).comp
      (contDiff_fst.prodMk hFi)
  have hpath (t : Real) (x : E) : HasDerivAt (fun s => F s x)
      (fderiv Real f (t, x) (1, 0)) t := by
    have hf : ContDiff Real ∞ f := hF
    exact (hf.differentiable (by simp) (t, x)).hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))
  have hWzero (t : Real) (x : E) (hx : x ∈ P) : W (t, x) = 0 := by
    have hinv : (F t).symm x = x := by
      apply (F t).injective
      change F t ((F t).symm x) = F t x
      rw [(F t).apply_symm_apply, hstationary t hx]
      rfl
    change fderiv Real f (t, (F t).symm x) (1, 0) = 0
    rw [hinv]
    have hc : (fun s => F s x) = fun _ : Real => x :=
      funext fun s => hstationary s hx
    have hd := hpath t x
    rw [hc] at hd
    exact hd.unique (hasDerivAt_const t x)
  have hWlevel (t : Real) (x : E) : l (W (t, x)) = 0 := by
    have hd := l.hasFDerivAt.comp_hasDerivAt t (hpath t ((F t).symm x))
    have hc : (fun s => l (F s ((F t).symm x))) =
        fun _ : Real => l ((F t).symm x) := funext fun s => hlevel s _
    simp only [Function.comp_def] at hd
    rw [hc] at hd
    exact hd.unique (hasDerivAt_const t _)
  let T : Set (Real × E) :=
    (fun z : Real × E => (z.1, F z.1 z.2)) '' (Icc (0 : Real) 1 ×ˢ K)
  have hT : IsCompact T :=
    (isCompact_Icc.prod hK).image (continuous_fst.prodMk hF.continuous)
  have hTU : T ⊆ (univ : Set Real) ×ˢ U := by
    rintro _ ⟨⟨t, x⟩, ⟨ht, hx⟩, rfl⟩
    exact ⟨mem_univ _, htrace t ht x hx⟩
  obtain ⟨χ, hχ, hχc, hχU, hχT⟩ :=
    Poincare.Parabolic.Interior.exists_contDiff_compact_cutoff hT
      (isOpen_univ.prod hU) hTU
  let V : Real × E → E := fun z => χ z • W z
  have hV : ContDiff Real ∞ V := hχ.smul hW
  have hVc : HasCompactSupport V := hχc.smul_right
  let S : Set E := Prod.snd '' tsupport χ
  have hS : IsCompact S := hχc.isCompact.image continuous_snd
  have hSU : S ⊆ U := by
    rintro _ ⟨z, hz, rfl⟩
    exact (hχU hz).2
  have hzero (t : Real) (x : E) (hx : x ∉ S) : V (t, x) = 0 := by
    have hn : (t, x) ∉ tsupport χ := fun hz => hx ⟨(t, x), hz, rfl⟩
    simp only [V, image_eq_zero_of_notMem_tsupport hn, zero_smul]
  obtain ⟨Φ, hi, hs, ho, hfix⟩ :=
    exists_diffeomorph_evolution_of_compact_spatial_support V hV hS hzero
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hVc hV (by simp)
  have hLip (t : Real) : LipschitzWith L (fun x => V (t, x)) := by
    convert! hL.comp (LipschitzWith.prodMk_left t) using 1
    simp
  refine ⟨S, hS, hSU, Φ 0 1, hfix 0 1, ?_, ?_, ?_⟩
  · intro x hx
    have hv (t : Real) : V (t, x) = 0 := by simp [V, hWzero t x hx]
    have heq := ODE_solution_unique (a := 0) (b := 1) hLip
      (f := fun t => Φ 0 t x) (g := fun _ => x)
      ((hs 0).continuous.comp (continuous_id.prodMk continuous_const)).continuousOn
      (fun t _ => (ho 0 x t).hasDerivWithinAt)
      continuous_const.continuousOn
      (fun t _ => by rw [hv]; exact (hasDerivAt_const t x).hasDerivWithinAt)
      (hi 0 x)
    exact heq (by simp)
  · intro x
    have hd (t : Real) : HasDerivAt (fun t => l (Φ 0 t x)) 0 t := by
      have hd := l.hasFDerivAt.comp_hasDerivAt t (ho 0 x t)
      convert! hd using 1
      simp only [V, map_smul, hWlevel, smul_zero]
    have heq := is_const_of_deriv_eq_zero
      (fun t => (hd t).differentiableAt) (fun t => (hd t).deriv) 1 0
    simpa only [hi] using heq
  · intro x hx
    have hvel (t : Real) (ht : t ∈ Icc (0 : Real) 1) :
        V (t, F t x) = fderiv Real f (t, x) (1, 0) := by
      have htT : (t, F t x) ∈ T := ⟨(t, x), ⟨ht, hx⟩, rfl⟩
      simp only [V, (hχT _ htT).eq_of_nhds, one_smul, W,
        (F t).symm_apply_apply]
    have heq := ODE_solution_unique (a := 0) (b := 1) hLip
      (f := fun t => Φ 0 t x) (g := fun t => F t x)
      ((hs 0).continuous.comp (continuous_id.prodMk continuous_const)).continuousOn
      (fun t _ => (ho 0 x t).hasDerivWithinAt)
      (hF.continuous.comp (continuous_id.prodMk continuous_const)).continuousOn
      (fun t ht => by
        rw [hvel t (Ico_subset_Icc_self ht)]
        exact (hpath t x).hasDerivWithinAt)
      ((hi 0 x).trans (hinit hx).symm)
    exact heq (by simp)

theorem exists_supported_relative_family_localization
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [FiniteDimensional Real E]
    (F : Real → Diffeomorph 𝓘(Real, E) 𝓘(Real, E) E E ∞)
    (hF : ContDiff Real ∞ (fun z : Real × E => F z.1 z.2))
    (hFi : ContDiff Real ∞ (fun z : Real × E => (F z.1).symm z.2))
    {K P U : Set E} (hK : IsCompact K) (hU : IsOpen U)
    (htrace : ∀ t ∈ Icc (0 : Real) 1, ∀ x ∈ K, F t x ∈ U)
    (hinit : EqOn (F 0) id K)
    (hstationary : ∀ t, EqOn (F t) id P) :
    ∃ S : Set E, IsCompact S ∧ S ⊆ U ∧
      ∃ G : Diffeomorph 𝓘(Real, E) 𝓘(Real, E) E E ∞,
        (∀ x ∉ S, G x = x) ∧ EqOn G id P ∧ EqOn G (F 1) K := by
  obtain ⟨S, hS, hSU, G, hfix, hP, _, hK⟩ :=
    exists_supported_relative_family_localization_preserving_linear
      F hF hFi hK hU htrace hinit hstationary 0 (by simp)
  exact ⟨S, hS, hSU, G, hfix, hP, hK⟩

end Poincare.Manifold.Schoenflies
