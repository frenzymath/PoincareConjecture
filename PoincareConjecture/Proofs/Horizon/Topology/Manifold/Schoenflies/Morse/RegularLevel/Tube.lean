import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.RegularLevel.Band
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.RegularLevel.Circle
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.InverseFunction.ModelSpaces









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter TopologicalSpace
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies

open Poincare.Geometry.Manifold.RegularLevel
open Poincare.Geometry.Riemannian.SpaceForm

private abbrev E1 := EuclideanSpace Real (Fin 1)
private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : EuclideanSpace Real (Fin 3)) 1
local notation "Iprod" => ModelWithCorners.prod (𝓡 1) 𝓘(Real, Real)

private instance : Fact (Module.finrank Real E2 = 1 + 1) := ⟨by simp⟩
private instance : ChartedSpace (E1 × Real) (S1 × Real) :=
  prodChartedSpace E1 S1 Real Real
private instance : IsManifold 𝓘(Real, E1 × Real) ∞ (S1 × Real) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓡 1) (I' := 𝓘(Real, Real)) S1 Real
private instance : Nonempty S1 := by
  obtain ⟨x, hx⟩ := (NormedSpace.sphere_nonempty (x := (0 : E2))).mpr
    (by norm_num : (0 : Real) ≤ 1)
  exact ⟨⟨x, hx⟩⟩



theorem exists_annular_chart_of_injective_bijective_derivative
    {F : S1 × Real -> S2} {s : Set (S1 × Real)} (hs : IsOpen s)
    (hF : ContMDiffOn Iprod (𝓡 2) ∞ F s) (hinj : InjOn F s)
    (hbij : ∀ z ∈ s, Function.Bijective (mfderiv Iprod (𝓡 2) F z)) :
    ∃ e : OpenPartialHomeomorph (S1 × Real) S2,
      e.source = s ∧ (e : S1 × Real -> S2) = F ∧
      ContMDiffOn Iprod (𝓡 2) ∞ e e.source ∧
      ContMDiffOn (𝓡 2) Iprod ∞ e.symm e.target := by
  let U : Opens (S1 × Real) := ⟨s, hs⟩
  have hFu : ContMDiff Iprod (𝓡 2) ∞ (fun z : U => F z) := by
    intro z
    exact (hF.contMDiffAt (hs.mem_nhds z.property)).comp z (contMDiff_subtype_val z)
  have hbu (z : U) : Function.Bijective
      (mfderiv Iprod (𝓡 2) (fun w : U => F w) z) := by
    rw [mfderiv_opens_restrict U F
      ((hF.contMDiffAt (hs.mem_nhds z.property)).mdifferentiableAt (by simp))]
    exact hbij z z.property
  have hopen : IsOpenMap (fun z : U => F z) := by
    apply IsOpenMap.of_nhds_le
    intro z
    have hsm : ContMDiffAt 𝓘(Real, E1 × Real) (𝓡 2) ∞ (fun z : U => F z) z := by
      simpa only [modelWithCornersSelf_prod] using hFu z
    have hbm : Function.Bijective
        (mfderiv 𝓘(Real, E1 × Real) (𝓡 2) (fun z : U => F z) z) := by
      rw [modelWithCornersSelf_prod]
      exact hbu z
    exact (Poincare.Geometry.Manifold.map_nhds_eq_of_contMDiffAt_bijective_mfderiv_modelSpaces
      hsm hbm).ge
  let p := hinj.toPartialEquiv F s
  let e := OpenPartialHomeomorph.ofContinuousOpenRestrict p hF.continuousOn hopen hs
  refine ⟨e, rfl, rfl, hF, ?_⟩
  intro y hy
  have hx : e.symm y ∈ s := e.map_target hy
  have hleft : ∀ᶠ z in 𝓝 (e.symm y), e.symm (F z) = z := by
    filter_upwards [hs.mem_nhds hx] with z hz
    exact e.left_inv hz
  have hsm : ContMDiffAt 𝓘(Real, E1 × Real) (𝓡 2) ∞ F (e.symm y) := by
    simpa only [modelWithCornersSelf_prod] using hF.contMDiffAt (hs.mem_nhds hx)
  have hbm : Function.Bijective (mfderiv 𝓘(Real, E1 × Real) (𝓡 2) F (e.symm y)) := by
    rw [modelWithCornersSelf_prod]
    exact hbij _ hx
  have hinverse := Poincare.Geometry.Manifold.contMDiffAt_of_local_left_inverse_modelSpaces
    hsm hbm hleft
  have hright : F (e.symm y) = y := e.right_inv hy
  rw [hright] at hinverse
  simpa only [modelWithCornersSelf_prod] using hinverse.contMDiffWithinAt


theorem bijective_mfderiv_of_height_and_slices
    {h : S2 -> Real} (hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ h)
    {F : S1 × Real -> S2} {s : Set (S1 × Real)} (hs : IsOpen s)
    (hF : ContMDiffOn Iprod (𝓡 2) ∞ F s) (c : Real)
    (hheight : ∀ z ∈ s, h (F z) = c + z.2)
    (hslice : ∀ z ∈ s,
      Function.Injective (mfderiv (𝓡 1) (𝓡 2) (fun q => F (q, z.2)) z.1)) :
    ∀ z ∈ s, Function.Bijective (mfderiv Iprod (𝓡 2) F z) := by
  intro z hz
  have hFd := (hF.contMDiffAt (hs.mem_nhds hz)).mdifferentiableAt (by simp)
  have hchain := mfderiv_comp z ((hh (F z)).mdifferentiableAt (by simp)) hFd
  have heq : h ∘ F =ᶠ[𝓝 z] (fun w : S1 × Real => c + w.2) :=
    eventuallyEq_of_mem (hs.mem_nhds hz) hheight
  have hdsnd : mfderiv Iprod 𝓘(Real, Real) (fun w : S1 × Real => c + w.2) z =
      ContinuousLinearMap.snd Real E1 Real := by
    change mfderiv Iprod 𝓘(Real, Real) ((fun _ : S1 × Real => c) + Prod.snd) z = _
    rw [mfderiv_add mdifferentiableAt_const mdifferentiableAt_snd,
      mfderiv_const, zero_add, mfderiv_snd]
    rfl
  rw [heq.mfderiv_eq, hdsnd] at hchain
  have hinj : Function.Injective (mfderiv Iprod (𝓡 2) F z : E1 × Real →L[Real] E2) := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro w hw
    change mfderiv Iprod (𝓡 2) F z w = 0 at hw
    have ht : w.2 = 0 := by
      have he := congrArg (fun L : E1 × Real →L[Real] Real => L w) hchain
      change w.2 = mfderiv (𝓡 2) 𝓘(Real, Real) h (F z)
        (mfderiv Iprod (𝓡 2) F z w) at he
      simpa only [hw, map_zero] using he
    have hq : w.1 = 0 := by
      apply hslice z hz
      rw [map_zero]
      rw [mfderiv_prod_eq_add_apply hFd, ht, map_zero, add_zero] at hw
      exact hw
    exact Prod.ext hq ht
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (V := E1 × Real) (V₂ := E2)
    (by simp [Module.finrank_prod, E1, E2])).mp hinj⟩

private theorem exists_regular_band_around
    {h : S2 -> Real} (hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ h)
    (c : Real) (hc : ∀ p, h p = c -> mfderiv (𝓡 2) 𝓘(Real, Real) h p ≠ 0) :
    ∃ ε : Real, 0 < ε ∧ ∀ p, h p ∈ Icc (c - ε) (c + ε) ->
      mfderiv (𝓡 2) 𝓘(Real, Real) h p ≠ 0 := by
  have hclosed := Poincare.Geometry.Manifold.isClosed_critical_values (hh.of_le (by simp))
  have hnot : c ∈ (h '' {p : S2 | mfderiv (𝓡 2) 𝓘(Real, Real) h p = 0})ᶜ := by
    rintro ⟨p, hp, hpc⟩
    exact hc p hpc hp
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hclosed.isOpen_compl.mem_nhds hnot)
  refine ⟨r / 2, by positivity, ?_⟩
  intro p hp hcrit
  have hd : h p ∈ ball c r := by
    rw [mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hp.1, hp.2]
  exact hball hd ⟨p, hcrit, rfl⟩



theorem image_openLevel_component_of_isCompact
    {h : S2 -> Real} (U : Opens S2) (c : Real)
    (hcompact : IsCompact ((U : Set S2) ∩ h ⁻¹' {c}))
    (p : openLevelSet h U c) :
    openLevelIncl h U c '' connectedComponent p =
      connectedComponentIn (h ⁻¹' {c}) (openLevelIncl h U c p) := by
  let L := (U : Set S2) ∩ h ⁻¹' {c}
  let e : openLevelSet h U c ≃ₜ L :=
    { toFun := fun x => ⟨openLevelIncl h U c x, x.val.property, x.property⟩
      invFun := fun x => ⟨⟨x, x.property.1⟩, x.property.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := ((isEmbedding_openLevelIncl h U c).continuous).subtype_mk _
      continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _ }
  have he := e.image_connectedComponentIn (mem_univ p)
  simp only [Set.image_univ, e.surjective.range_eq, connectedComponentIn_univ] at he
  have hpL : openLevelIncl h U c p ∈ L := ⟨p.val.property, p.property⟩
  have hpfull : openLevelIncl h U c p ∈ h ⁻¹' {c} := p.property
  have himage : openLevelIncl h U c '' connectedComponent p =
      connectedComponentIn L (openLevelIncl h U c p) := by
    rw [connectedComponentIn_eq_image hpL]
    change openLevelIncl h U c '' connectedComponent p = Subtype.val '' connectedComponent (e p)
    rw [← he, image_image]
    rfl
  rw [himage]
  apply Subset.antisymm (connectedComponentIn_mono _ inter_subset_right)
  apply isPreconnected_connectedComponentIn.subset_connectedComponentIn
    (mem_connectedComponentIn hpfull)
  have hclopen : IsClopen ((Subtype.val : (h ⁻¹' {c}) -> S2) ⁻¹' L) := by
    refine ⟨hcompact.isClosed.preimage continuous_subtype_val, ?_⟩
    have heq : (Subtype.val : (h ⁻¹' {c}) -> S2) ⁻¹' L =
        Subtype.val ⁻¹' (U : Set S2) := by
      ext x
      exact and_iff_left x.property
    rw [heq]
    exact U.isOpen.preimage continuous_subtype_val
  rw [connectedComponentIn_eq_image hpfull]
  rintro y ⟨x, hx, rfl⟩
  exact hclopen.connectedComponent_subset hpL hx


theorem image_openLevel_component
    {h : S2 -> Real} (U : Opens S2) (c : Real)
    (hfull : h ⁻¹' {c} ⊆ (U : Set S2)) (p : openLevelSet h U c) :
    openLevelIncl h U c '' connectedComponent p =
      connectedComponentIn (h ⁻¹' {c}) (openLevelIncl h U c p) := by
  let e : openLevelSet h U c ≃ₜ (h ⁻¹' {c}) :=
    { toFun := fun x => ⟨openLevelIncl h U c x, x.property⟩
      invFun := fun x => ⟨⟨x, hfull x.property⟩, x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := ((isEmbedding_openLevelIncl h U c).continuous).subtype_mk _
      continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _ }
  have he := e.image_connectedComponentIn (mem_univ p)
  simp only [Set.image_univ, e.surjective.range_eq, connectedComponentIn_univ] at he
  have hp : openLevelIncl h U c p ∈ h ⁻¹' {c} := p.property
  rw [connectedComponentIn_eq_image hp]
  change openLevelIncl h U c '' connectedComponent p = Subtype.val '' connectedComponent (e p)
  rw [← he, image_image]
  rfl



theorem exists_smooth_regular_level_component_tube_of_smooth
    {h : S2 -> Real} (hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ h)
    (c : Real) (hc : ∀ p, h p = c -> mfderiv (𝓡 2) 𝓘(Real, Real) h p ≠ 0)
    (p : S2) (hp : h p = c) :
    ∃ ε : Real, 0 < ε ∧ ∃ F : OpenPartialHomeomorph (S1 × Real) S2,
      F.source = univ ×ˢ Ioo (-ε) ε ∧
      ContMDiffOn Iprod (𝓡 2) ∞ F F.source ∧
      ContMDiffOn (𝓡 2) Iprod ∞ F.symm F.target ∧
      (∀ q t, t ∈ Ioo (-ε) ε -> h (F (q, t)) = c + t) ∧
      range (fun q : S1 => F (q, 0)) = connectedComponentIn (h ⁻¹' {c}) p := by
  obtain ⟨ε, hε, hregular⟩ := exists_regular_band_around hh c hc
  let a := c - ε
  let b := c + ε
  have hab : a ≤ b := by dsimp [a, b]; linarith
  obtain ⟨U, _, _, _, hfull, hreg, V, δ, Φ, hV, hbottom, hVU, hδ,
    hΦ, hΦzero, hΦcurve, hlevels⟩ :=
    exists_sphere_height_level_diffeomorphisms_on_regular_band_of_smooth hh hab hregular
  have hcband : c ∈ Icc a b := by dsimp [a, b]; constructor <;> linarith
  have hfullc : h ⁻¹' {c} ⊆ (U : Set S2) :=
    inter_eq_right.mp (hfull c hcband)
  let := openLevelSetChartedSpace hh U hreg 1 a
  let := isManifold_openLevelSet hh U hreg 1 a
  let := openLevelSetChartedSpace hh U hreg 1 c
  let := isManifold_openLevelSet hh U hreg 1 c
  let pc : openLevelSet h U c := ⟨⟨p, hfullc hp⟩, hp⟩
  obtain ⟨ec, hec⟩ := hlevels c hcband
  obtain ⟨d⟩ := nonempty_unitCircle_diffeomorph_regularLevelComponent hh U hreg c hfullc pc
  let C := Poincare.connectedComponentOpens E1 pc
  let k : S1 -> openLevelSet h U c := fun q => (d q : openLevelSet h U c)
  have hk : ContMDiff (𝓡 1) (𝓡 1) ∞ k := contMDiff_subtype_val.comp d.contMDiff
  have hkinj : Function.Injective k := Subtype.val_injective.comp d.injective
  have hkderiv (q : S1) : Function.Injective (mfderiv (𝓡 1) (𝓡 1) k q) := by
    change Function.Injective (mfderiv (𝓡 1) (𝓡 1) (Subtype.val ∘ d) q)
    rw [mfderiv_comp q ((contMDiff_subtype_val (n := ∞) (d q)).mdifferentiableAt (by simp))
      (d.contMDiff.mdifferentiable (by simp) q), mfderiv_opens_subtypeVal]
    exact (d.mfderivToContinuousLinearEquiv (by simp) q).injective
  let L : S1 -> openLevelSet h U a := ec.symm ∘ k
  have hL : ContMDiff (𝓡 1) (𝓡 1) ∞ L := ec.symm.contMDiff.comp hk
  have hLinj : Function.Injective L := ec.symm.injective.comp hkinj
  have hLderiv (q : S1) : Function.Injective (mfderiv (𝓡 1) (𝓡 1) L q) := by
    rw [show L = ec.symm ∘ k from rfl,
      mfderiv_comp q (ec.symm.contMDiff.mdifferentiable (by simp) (k q))
        (hk.mdifferentiable (by simp) q)]
    exact (ec.symm.mfderivToContinuousLinearEquiv (by simp) (k q)).injective.comp (hkderiv q)
  let j : S1 -> S2 := openLevelIncl h U a ∘ L
  have hj : ContMDiff (𝓡 1) (𝓡 2) ∞ j :=
    (contMDiff_openLevelIncl hh U hreg 1 a).comp hL
  have hjV (q : S1) : j q ∈ V := hbottom ⟨(L q).val.property, (L q).property⟩
  let G : S1 × Real -> S2 := fun z => Φ (c + z.2 - a, j z.1)
  let s : Set (S1 × Real) := univ ×ˢ Ioo (-ε) ε
  have hs : IsOpen s := isOpen_univ.prod isOpen_Ioo
  have htime {t : Real} (ht : t ∈ Ioo (-ε) ε) : c + t ∈ Icc a b := by
    dsimp [a, b]
    constructor <;> linarith [ht.1, ht.2]
  have hG : ContMDiffOn Iprod (𝓡 2) ∞ G s := by
    apply hΦ.comp
      (((contMDiff_const.add contMDiff_snd).sub contMDiff_const).prodMk
        (hj.comp contMDiff_fst)).contMDiffOn
    intro z hz
    exact ⟨⟨by dsimp [a]; linarith [hz.2.1],
      by dsimp [a, b]; linarith [hz.2.2]⟩, hjV z.1⟩
  have hheight (z : S1 × Real) (hz : z ∈ s) : h (G z) = c + z.2 := by
    obtain ⟨et, het⟩ := hlevels (c + z.2) (htime hz.2)
    rw [show G z = openLevelIncl h U (c + z.2) (et (L z.1)) from (het _).symm]
    exact (et (L z.1)).property
  have hGinj : InjOn G s := by
    intro z hz w hw heq
    have ht : z.2 = w.2 := by
      have := congrArg h heq
      rw [hheight z hz, hheight w hw] at this
      linarith
    obtain ⟨et, het⟩ := hlevels (c + z.2) (htime hz.2)
    have hq : z.1 = w.1 := by
      apply hLinj
      apply et.injective
      apply (isEmbedding_openLevelIncl h U (c + z.2)).injective
      change openLevelIncl h U (c + z.2) (et (L z.1)) =
        openLevelIncl h U (c + z.2) (et (L w.1))
      rw [het, het]
      simpa only [G, j, Function.comp_apply, ht] using heq
    exact Prod.ext hq ht
  have hslice (z : S1 × Real) (hz : z ∈ s) :
      Function.Injective (mfderiv (𝓡 1) (𝓡 2) (fun q => G (q, z.2)) z.1) := by
    let := openLevelSetChartedSpace hh U hreg 1 (c + z.2)
    let := isManifold_openLevelSet hh U hreg 1 (c + z.2)
    obtain ⟨et, het⟩ := hlevels (c + z.2) (htime hz.2)
    have heq : (fun q => G (q, z.2)) = openLevelIncl h U (c + z.2) ∘ et ∘ L := by
      funext q
      exact (het (L q)).symm
    rw [heq, mfderiv_comp z.1
      ((contMDiff_openLevelIncl hh U hreg 1 (c + z.2)).mdifferentiable (by simp) _)
      ((et.contMDiff.comp hL).mdifferentiable (by simp) _),
      mfderiv_comp z.1 (et.contMDiff.mdifferentiable (by simp) _)
        (hL.mdifferentiable (by simp) _)]
    exact (injective_mfderiv_openLevelIncl hh U hreg 1 (c + z.2) _).comp
      ((et.mfderivToContinuousLinearEquiv (by simp) _).injective.comp (hLderiv _))
  obtain ⟨F, hFs, hFG, hF, hFinv⟩ :=
    exists_annular_chart_of_injective_bijective_derivative hs hG hGinj
      (bijective_mfderiv_of_height_and_slices hh hs hG c hheight hslice)
  refine ⟨ε, hε, F, hFs, hF, hFinv, ?_, ?_⟩
  · intro q t ht
    rw [hFG]
    exact hheight (q, t) ⟨mem_univ _, ht⟩
  · have hcentral (q : S1) : F (q, 0) = openLevelIncl h U c (k q) := by
      rw [hFG]
      change Φ (c + 0 - a, openLevelIncl h U a (ec.symm (k q))) = _
      rw [add_zero, ← hec, ec.apply_symm_apply]
    simp_rw [hcentral]
    change range (fun q => openLevelIncl h U c (k q)) =
      connectedComponentIn (h ⁻¹' {c}) (openLevelIncl h U c pc)
    rw [← image_openLevel_component U c hfullc pc]
    ext x
    constructor
    · rintro ⟨q, rfl⟩
      exact ⟨k q, (d q).property, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨q, hq⟩ := d.surjective ⟨y, hy⟩
      exact ⟨q, congrArg (fun z : C => openLevelIncl h U c z.val) hq⟩



theorem exists_smooth_regular_level_component_tube
    {h : S2 -> Real} (hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ h)
    (hfinite : {p : S2 | mfderiv (𝓡 2) 𝓘(Real, Real) h p = 0}.Finite)
    (c : Real) (hc : ∀ p, h p = c -> mfderiv (𝓡 2) 𝓘(Real, Real) h p ≠ 0)
    (p : S2) (hp : h p = c) :
    ∃ ε : Real, 0 < ε ∧ ∃ F : OpenPartialHomeomorph (S1 × Real) S2,
      F.source = univ ×ˢ Ioo (-ε) ε ∧
      ContMDiffOn Iprod (𝓡 2) ∞ F F.source ∧
      ContMDiffOn (𝓡 2) Iprod ∞ F.symm F.target ∧
      (∀ q t, t ∈ Ioo (-ε) ε -> h (F (q, t)) = c + t) ∧
      range (fun q : S1 => F (q, 0)) = connectedComponentIn (h ⁻¹' {c}) p :=
  (fun _ => exists_smooth_regular_level_component_tube_of_smooth hh c hc p hp) hfinite

end Poincare.Manifold.Schoenflies
