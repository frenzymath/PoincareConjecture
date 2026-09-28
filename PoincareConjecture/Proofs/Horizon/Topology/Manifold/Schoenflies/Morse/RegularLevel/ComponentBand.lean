import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.RegularLevel.Tube
import Mathlib.Analysis.Normed.Module.Connected

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
private instance : ConnectedSpace S1 :=
  isConnected_iff_connectedSpace.mp
    (isConnected_sphere (by simp [← Module.finrank_eq_rank, E2]) (0 : E2) zero_le_one)

private theorem exists_regular_band_enlargement
    {h : S2 → Real} (hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ h)
    {a b : Real} (hab : a ≤ b)
    (hregular : ∀ p, h p ∈ Icc a b → mfderiv (𝓡 2) 𝓘(Real, Real) h p ≠ 0) :
    ∃ δ : Real, 0 < δ ∧ ∀ p, h p ∈ Icc (a - δ) (b + δ) →
      mfderiv (𝓡 2) 𝓘(Real, Real) h p ≠ 0 := by
  let K := h '' {p : S2 | mfderiv (𝓡 2) 𝓘(Real, Real) h p = 0}
  have hclosed : IsClosed K :=
    Poincare.Geometry.Manifold.isClosed_critical_values (hh.of_le (by simp))
  have ha : a ∈ Kᶜ := by
    rintro ⟨p, hp, hpa⟩
    exact hregular p (by rw [hpa]; exact ⟨le_rfl, hab⟩) hp
  have hb : b ∈ Kᶜ := by
    rintro ⟨p, hp, hpb⟩
    exact hregular p (by rw [hpb]; exact ⟨hab, le_rfl⟩) hp
  obtain ⟨ra, hra, hras⟩ := Metric.mem_nhds_iff.mp (hclosed.isOpen_compl.mem_nhds ha)
  obtain ⟨rb, hrb, hrbs⟩ := Metric.mem_nhds_iff.mp (hclosed.isOpen_compl.mem_nhds hb)
  let δ := min ra rb / 2
  have hδ : 0 < δ := half_pos (lt_min hra hrb)
  have hδa : δ < ra := by dsimp [δ]; linarith [min_le_left ra rb]
  have hδb : δ < rb := by dsimp [δ]; linarith [min_le_right ra rb]
  refine ⟨δ, hδ, ?_⟩
  intro p hp hcrit
  by_cases hpa : h p < a
  · apply hras (show h p ∈ ball a ra by
      rw [mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith [hp.1])
    exact ⟨p, hcrit, rfl⟩
  by_cases hpb : b < h p
  · apply hrbs (show h p ∈ ball b rb by
      rw [mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith [hp.2])
    exact ⟨p, hcrit, rfl⟩
  exact hregular p ⟨le_of_not_gt hpa, le_of_not_gt hpb⟩ hcrit

private theorem image_closed_strip_eq_component
    {h : S2 → Real} {a b l u : Real} (hab : a ≤ b) (hla : l < a) (hbu : b < u)
    (F : OpenPartialHomeomorph (S1 × Real) S2)
    (hsource : F.source = univ ×ˢ Ioo l u)
    (hheight : ∀ q t, t ∈ Ioo l u → h (F (q, t)) = t)
    {p : S2} (hp : p ∈ range (fun q : S1 => F (q, a))) :
    F '' (univ ×ˢ Icc a b) = connectedComponentIn (h ⁻¹' Icc a b) p := by
  let B := h ⁻¹' Icc a b
  let K := F '' (univ ×ˢ Icc a b)
  have hsub : univ ×ˢ Icc a b ⊆ F.source := by
    rw [hsource]
    rintro ⟨q, t⟩ ⟨hq, ht⟩
    exact ⟨hq, ⟨hla.trans_le ht.1, ht.2.trans_lt hbu⟩⟩
  have hKcompact : IsCompact K :=
    (isCompact_univ.prod isCompact_Icc).image_of_continuousOn (F.continuousOn.mono hsub)
  have hKconn : IsPreconnected K :=
    (isPreconnected_univ.prod isPreconnected_Icc).image _ (F.continuousOn.mono hsub)
  have hKeq : K = F.target ∩ B := by
    ext y
    constructor
    · rintro ⟨⟨q, t⟩, hqt, rfl⟩
      refine ⟨F.map_source (hsub hqt), ?_⟩
      change h (F (q, t)) ∈ Icc a b
      rw [hheight q t ⟨hla.trans_le hqt.2.1, hqt.2.2.trans_lt hbu⟩]
      exact hqt.2
    · rintro ⟨hy, hyt⟩
      have hx := F.map_target hy
      rw [hsource] at hx
      have ht : (F.symm y).2 ∈ Icc a b := by
        change h y ∈ Icc a b at hyt
        rw [← F.right_inv hy, hheight _ _ hx.2] at hyt
        exact hyt
      exact ⟨F.symm y, ⟨mem_univ _, ht⟩, F.right_inv hy⟩
  have hKB : K ⊆ B := hKeq ▸ inter_subset_right
  have hpK : p ∈ K := by
    obtain ⟨q, rfl⟩ := hp
    exact ⟨(q, a), ⟨mem_univ _, ⟨le_rfl, hab⟩⟩, rfl⟩
  apply Subset.antisymm (hKconn.subset_connectedComponentIn hpK hKB)
  have hclopen : IsClopen ((Subtype.val : B → S2) ⁻¹' K) := by
    refine ⟨hKcompact.isClosed.preimage continuous_subtype_val, ?_⟩
    have heq : (Subtype.val : B → S2) ⁻¹' K = Subtype.val ⁻¹' F.target := by
      ext x
      simp only [mem_preimage, hKeq, mem_inter_iff, and_iff_left_iff_imp]
      exact fun _ => x.property
    rw [heq]
    exact F.open_target.preimage continuous_subtype_val
  rw [connectedComponentIn_eq_image (hKB hpK)]
  rintro y ⟨x, hx, rfl⟩
  exact hclopen.connectedComponent_subset hpK hx

theorem exists_smooth_regular_band_component_in_open
    {h : S2 → Real} (hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ h)
    (U : Opens S2) (hreg : ∀ p ∈ U, mfderiv (𝓡 2) 𝓘(Real, Real) h p ≠ 0)
    {a b : Real} (hab : a < b)
    {δ : Real} (hδ : 0 < δ)
    (hcompact : IsCompact ((U : Set S2) ∩ h ⁻¹' Icc (a - δ) (b + δ)))
    (p : S2) (hpU : p ∈ U) (hp : h p = a) :
    ∃ δ : Real, 0 < δ ∧ ∃ F : OpenPartialHomeomorph (S1 × Real) S2,
      F.source = univ ×ˢ Ioo (a - δ) (b + δ) ∧
      ContMDiffOn Iprod (𝓡 2) ∞ F F.source ∧
      ContMDiffOn (𝓡 2) Iprod ∞ F.symm F.target ∧
      (∀ q t, t ∈ Ioo (a - δ) (b + δ) → h (F (q, t)) = t) ∧
      range (fun q : S1 => F (q, a)) = connectedComponentIn (h ⁻¹' {a}) p ∧
      F '' (univ ×ˢ Icc a b) = connectedComponentIn (h ⁻¹' Icc a b) p ∧
      F.target ⊆ U := by
  let a₀ := a - δ
  let b₀ := b + δ
  have hab₀ : a₀ ≤ b₀ := by dsimp [a₀, b₀]; linarith
  obtain ⟨V, ε, Φ, hV, hbottom, hVU, hε, hΦ, hΦzero, hΦcurve, hlevels⟩ :=
    (roundSphereMetric 2).leviCivitaData.exists_level_diffeomorphisms_on_compact_regular_band
      hh U hreg hab₀ hcompact
  have haband : a ∈ Icc a₀ b₀ := by dsimp [a₀, b₀]; constructor <;> linarith
  have hcompacta : IsCompact ((U : Set S2) ∩ h ⁻¹' {a}) := by
    convert hcompact.inter_right (isClosed_singleton.preimage hh.continuous) using 1
    ext x
    constructor
    · rintro ⟨hxU, hxa⟩
      exact ⟨⟨hxU, show h x ∈ Icc a₀ b₀ from hxa ▸ haband⟩, hxa⟩
    · exact fun hx => ⟨hx.1.1, hx.2⟩
  let := openLevelSetChartedSpace hh U hreg 1 a₀
  let := isManifold_openLevelSet hh U hreg 1 a₀
  let := openLevelSetChartedSpace hh U hreg 1 a
  let := isManifold_openLevelSet hh U hreg 1 a
  let pa : openLevelSet h U a := ⟨⟨p, hpU⟩, hp⟩
  obtain ⟨ea, hea⟩ := hlevels a haband
  obtain ⟨d⟩ :=
    nonempty_unitCircle_diffeomorph_regularLevelComponent_of_isCompact hh U hreg a hcompacta pa
  let C := Poincare.connectedComponentOpens E1 pa
  let k : S1 → openLevelSet h U a := fun q => (d q : openLevelSet h U a)
  have hk : ContMDiff (𝓡 1) (𝓡 1) ∞ k := contMDiff_subtype_val.comp d.contMDiff
  have hkinj : Function.Injective k := Subtype.val_injective.comp d.injective
  have hkderiv (q : S1) : Function.Injective (mfderiv (𝓡 1) (𝓡 1) k q) := by
    change Function.Injective (mfderiv (𝓡 1) (𝓡 1) (Subtype.val ∘ d) q)
    rw [mfderiv_comp q ((contMDiff_subtype_val (n := ∞) (d q)).mdifferentiableAt (by simp))
      (d.contMDiff.mdifferentiable (by simp) q), mfderiv_opens_subtypeVal]
    exact (d.mfderivToContinuousLinearEquiv (by simp) q).injective
  let L : S1 → openLevelSet h U a₀ := ea.symm ∘ k
  have hL : ContMDiff (𝓡 1) (𝓡 1) ∞ L := ea.symm.contMDiff.comp hk
  have hLinj : Function.Injective L := ea.symm.injective.comp hkinj
  have hLderiv (q : S1) : Function.Injective (mfderiv (𝓡 1) (𝓡 1) L q) := by
    rw [show L = ea.symm ∘ k from rfl,
      mfderiv_comp q (ea.symm.contMDiff.mdifferentiable (by simp) (k q))
        (hk.mdifferentiable (by simp) q)]
    exact (ea.symm.mfderivToContinuousLinearEquiv (by simp) (k q)).injective.comp (hkderiv q)
  let j : S1 → S2 := openLevelIncl h U a₀ ∘ L
  have hj : ContMDiff (𝓡 1) (𝓡 2) ∞ j :=
    (contMDiff_openLevelIncl hh U hreg 1 a₀).comp hL
  have hjV (q : S1) : j q ∈ V := hbottom ⟨(L q).val.property, (L q).property⟩
  let G : S1 × Real → S2 := fun z => Φ (z.2 - a₀, j z.1)
  let s : Set (S1 × Real) := univ ×ˢ Ioo a₀ b₀
  have hs : IsOpen s := isOpen_univ.prod isOpen_Ioo
  have hG : ContMDiffOn Iprod (𝓡 2) ∞ G s := by
    apply hΦ.comp
      ((contMDiff_snd.sub contMDiff_const).prodMk
        (hj.comp contMDiff_fst)).contMDiffOn
    intro z hz
    exact ⟨⟨by linarith [hz.2.1], by linarith [hz.2.2]⟩, hjV z.1⟩
  have hheight (z : S1 × Real) (hz : z ∈ s) : h (G z) = z.2 := by
    obtain ⟨et, het⟩ := hlevels z.2 (Ioo_subset_Icc_self hz.2)
    rw [show G z = openLevelIncl h U z.2 (et (L z.1)) from (het _).symm]
    exact (et (L z.1)).property
  have hGinj : InjOn G s := by
    intro z hz w hw heq
    have ht : z.2 = w.2 := by
      have := congrArg h heq
      rwa [hheight z hz, hheight w hw] at this
    obtain ⟨et, het⟩ := hlevels z.2 (Ioo_subset_Icc_self hz.2)
    have hq : z.1 = w.1 := by
      apply hLinj
      apply et.injective
      apply (isEmbedding_openLevelIncl h U z.2).injective
      change openLevelIncl h U z.2 (et (L z.1)) = openLevelIncl h U z.2 (et (L w.1))
      rw [het, het]
      simpa only [G, j, Function.comp_apply, ht] using heq
    exact Prod.ext hq ht
  have hslice (z : S1 × Real) (hz : z ∈ s) :
      Function.Injective (mfderiv (𝓡 1) (𝓡 2) (fun q => G (q, z.2)) z.1) := by
    let := openLevelSetChartedSpace hh U hreg 1 z.2
    let := isManifold_openLevelSet hh U hreg 1 z.2
    obtain ⟨et, het⟩ := hlevels z.2 (Ioo_subset_Icc_self hz.2)
    have heq : (fun q => G (q, z.2)) = openLevelIncl h U z.2 ∘ et ∘ L := by
      funext q
      exact (het (L q)).symm
    rw [heq, mfderiv_comp z.1
      ((contMDiff_openLevelIncl hh U hreg 1 z.2).mdifferentiable (by simp) _)
      ((et.contMDiff.comp hL).mdifferentiable (by simp) _),
      mfderiv_comp z.1 (et.contMDiff.mdifferentiable (by simp) _)
        (hL.mdifferentiable (by simp) _)]
    exact (injective_mfderiv_openLevelIncl hh U hreg 1 z.2 _).comp
      ((et.mfderivToContinuousLinearEquiv (by simp) _).injective.comp (hLderiv _))
  obtain ⟨F, hFs, hFG, hF, hFinv⟩ :=
    exists_annular_chart_of_injective_bijective_derivative hs hG hGinj
      (bijective_mfderiv_of_height_and_slices hh hs hG 0
        (fun z hz => by simpa only [zero_add] using hheight z hz) hslice)
  have hFheight (q : S1) (t : Real) (ht : t ∈ Ioo a₀ b₀) : h (F (q, t)) = t := by
    rw [hFG]
    exact hheight (q, t) ⟨mem_univ _, ht⟩
  have hcenter : range (fun q : S1 => F (q, a)) = connectedComponentIn (h ⁻¹' {a}) p := by
    have hcentral (q : S1) : F (q, a) = openLevelIncl h U a (k q) := by
      rw [hFG]
      change Φ (a - a₀, openLevelIncl h U a₀ (ea.symm (k q))) = _
      rw [← hea, ea.apply_symm_apply]
    simp_rw [hcentral]
    change range (fun q => openLevelIncl h U a (k q)) =
      connectedComponentIn (h ⁻¹' {a}) (openLevelIncl h U a pa)
    rw [← image_openLevel_component_of_isCompact U a hcompacta pa]
    ext x
    constructor
    · rintro ⟨q, rfl⟩
      exact ⟨k q, (d q).property, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨q, hq⟩ := d.surjective ⟨y, hy⟩
      exact ⟨q, congrArg (fun z : C => openLevelIncl h U a z.val) hq⟩
  refine ⟨δ, hδ, F, hFs, hF, hFinv, hFheight, hcenter, ?_, ?_⟩
  · apply image_closed_strip_eq_component hab.le (by dsimp [a₀]; linarith)
      (by dsimp [b₀]; linarith) F hFs hFheight
    rw [hcenter]
    exact mem_connectedComponentIn hp
  · intro y hy
    have hx := F.map_target hy
    rw [hFs] at hx
    have ht : (F.symm y).2 - a₀ ∈ Ioo (-ε) (b₀ - a₀ + ε) := by
      constructor <;> linarith [hx.2.1, hx.2.2]
    have hGU := (hΦcurve _ (hjV (F.symm y).1)).1 _ ht
    change G (F.symm y) ∈ U at hGU
    rw [← hFG, F.right_inv hy] at hGU
    exact hGU

theorem exists_smooth_regular_band_component_of_smooth
    {h : S2 → Real} (hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ h)
    {a b : Real} (hab : a < b)
    (hregular : ∀ p : S2, h p ∈ Icc a b →
      mfderiv (𝓡 2) 𝓘(Real, Real) h p ≠ 0)
    (p : S2) (hp : h p = a) :
    ∃ δ : Real, 0 < δ ∧ ∃ F : OpenPartialHomeomorph (S1 × Real) S2,
      F.source = univ ×ˢ Ioo (a - δ) (b + δ) ∧
      ContMDiffOn Iprod (𝓡 2) ∞ F F.source ∧
      ContMDiffOn (𝓡 2) Iprod ∞ F.symm F.target ∧
      (∀ q t, t ∈ Ioo (a - δ) (b + δ) → h (F (q, t)) = t) ∧
      range (fun q : S1 => F (q, a)) = connectedComponentIn (h ⁻¹' {a}) p ∧
      F '' (univ ×ˢ Icc a b) = connectedComponentIn (h ⁻¹' Icc a b) p := by
  obtain ⟨δ, hδ, hregband⟩ := exists_regular_band_enlargement hh hab.le hregular
  obtain ⟨U, _, _, hcompact, hfull, hreg, _⟩ :=
    exists_sphere_height_level_diffeomorphisms_on_regular_band_of_smooth hh
      (show a - δ ≤ b + δ by linarith) hregband
  have hpU : p ∈ U := inter_eq_right.mp (hfull a ⟨by linarith, by linarith⟩) hp
  obtain ⟨ε, hε, F, hFs, hF, hFi, hheight, hcenter, hband, _⟩ :=
    exists_smooth_regular_band_component_in_open hh U hreg hab hδ hcompact p hpU hp
  exact ⟨ε, hε, F, hFs, hF, hFi, hheight, hcenter, hband⟩

theorem exists_smooth_regular_band_component
    {h : S2 → Real} (hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ h)
    (hfinite : {p : S2 | mfderiv (𝓡 2) 𝓘(Real, Real) h p = 0}.Finite)
    {a b : Real} (hab : a < b)
    (hregular : ∀ p : S2, h p ∈ Icc a b →
      mfderiv (𝓡 2) 𝓘(Real, Real) h p ≠ 0)
    (p : S2) (hp : h p = a) :
    ∃ δ : Real, 0 < δ ∧ ∃ F : OpenPartialHomeomorph (S1 × Real) S2,
      F.source = univ ×ˢ Ioo (a - δ) (b + δ) ∧
      ContMDiffOn Iprod (𝓡 2) ∞ F F.source ∧
      ContMDiffOn (𝓡 2) Iprod ∞ F.symm F.target ∧
      (∀ q t, t ∈ Ioo (a - δ) (b + δ) → h (F (q, t)) = t) ∧
      range (fun q : S1 => F (q, a)) = connectedComponentIn (h ⁻¹' {a}) p ∧
      F '' (univ ×ˢ Icc a b) = connectedComponentIn (h ⁻¹' Icc a b) p :=
  (fun _ => exists_smooth_regular_band_component_of_smooth hh hab hregular p hp) hfinite

end Poincare.Manifold.Schoenflies
