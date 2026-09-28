import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.RegularLevel.ComponentBand
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.RegularLevel.Projection
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Isotopy.SpatialCylinder

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies

open Poincare.Geometry.Manifold

private abbrev E1 := EuclideanSpace Real (Fin 1)
private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : E3) 1
local notation "Iprod" => ModelWithCorners.prod (𝓡 1) 𝓘(Real, Real)
local notation "Itime" => ModelWithCorners.prod 𝓘(Real, Real) (𝓡 1)

private instance : Fact (Module.finrank Real E2 = 1 + 1) := ⟨by simp⟩
private instance : Fact (Module.finrank Real E3 = 2 + 1) := ⟨by simp⟩
private instance : ChartedSpace (E1 × Real) (S1 × Real) :=
  prodChartedSpace E1 S1 Real Real
private instance : ChartedSpace (Real × E1) (Real × S1) :=
  prodChartedSpace Real Real E1 S1

private theorem exists_smooth_band_cutoff {a b δ : Real} (hab : a < b) (hδ : 0 < δ) :
    ∃ κ : Real → Real, ContDiff Real ∞ κ ∧
      (∀ t, κ t ∈ Ioo (a - δ) (b + δ)) ∧ ∀ t ∈ Icc a b, κ t = t := by
  let m := (a + b) / 2
  let r := (b - a) / 2
  let χ : ContDiffBump m := ⟨r, r + δ / 2, by dsimp [r]; linarith, by linarith⟩
  refine ⟨fun t => m + χ t * (t - m),
    contDiff_const.add (χ.contDiff.mul (contDiff_id.sub contDiff_const)), ?_, ?_⟩
  · intro t
    have hr : 0 < r := by dsimp [r]; linarith
    have hbound : |χ t * (t - m)| < r + δ := by
      by_cases ht : |t - m| < r + δ / 2
      · rw [abs_mul, abs_of_nonneg χ.nonneg]
        calc
          χ t * |t - m| ≤ 1 * |t - m| :=
            mul_le_mul_of_nonneg_right χ.le_one (abs_nonneg _)
          _ < r + δ := by simpa only [one_mul] using ht.trans (by linarith)
      · rw [χ.zero_of_le_dist (by simpa only [Real.dist_eq] using le_of_not_gt ht)]
        simp only [zero_mul, abs_zero]
        positivity
    obtain ⟨hl, hu⟩ := abs_lt.mp hbound
    dsimp [m, r] at *
    constructor <;> linarith
  · intro t ht
    change m + χ t * (t - m) = t
    rw [χ.one_of_mem_closedBall (by
      change |t - m| ≤ r
      rw [abs_le]
      dsimp [m, r]
      constructor <;> linarith [ht.1, ht.2]), one_mul]
    ring

private theorem smoothEmbedding_projected_band_slice
    {f : S2 → E3} (hf : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f)
    {h : S2 → Real} {v : E3} (hv : ‖v‖ = 1)
    (hheight : ∀ p, inner Real v (f p) = h p)
    (J : (Real ∙ v)ᗮ ≃ₗᵢ[Real] E2)
    (F : OpenPartialHomeomorph (S1 × Real) S2) {l u : Real}
    (hsource : F.source = univ ×ˢ Ioo l u)
    (hF : ContMDiffOn Iprod (𝓡 2) ∞ F F.source)
    (hFinv : ContMDiffOn (𝓡 2) Iprod ∞ F.symm F.target)
    (hlevel : ∀ q t, t ∈ Ioo l u → h (F (q, t)) = t)
    (t : Real) (ht : t ∈ Ioo l u) :
    _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞
      (fun q => J ((Real ∙ v)ᗮ.orthogonalProjectionOnto (f (F (q, t))))) := by
  let D : PartialDiffeomorph Iprod (𝓡 2) (S1 × Real) S2 ∞ :=
    { toPartialEquiv := F.toPartialEquiv
      open_source := F.open_source
      open_target := F.open_target
      contMDiffOn_toFun := hF
      contMDiffOn_invFun := hFinv }
  have hqt (q : S1) : (q, t) ∈ F.source := by rw [hsource]; exact ⟨mem_univ _, ht⟩
  let s : S1 → S2 := fun q => F (q, t)
  have hs : ContMDiff (𝓡 1) (𝓡 2) ∞ s := by
    intro q
    exact (hF.contMDiffAt (F.open_source.mem_nhds (hqt q))).comp q
      ((contMDiff_id.prodMk contMDiff_const) q)
  have hsinj : Injective s := by
    intro q q' heq
    exact congrArg Prod.fst (F.injOn (hqt q) (hqt q') heq)
  have hsder (q : S1) : Injective (mfderiv (𝓡 1) (𝓡 2) s q) := by
    have hpair : MDifferentiableAt (𝓡 1) Iprod (fun q : S1 => (q, t)) q :=
      ((contMDiff_id (n := ∞)).prodMk (contMDiff_const (c := t)) q).mdifferentiableAt (by simp)
    have hloc : IsLocalDiffeomorphAt Iprod (𝓡 2) ∞ F (q, t) :=
      D.isLocalDiffeomorphAt Iprod (𝓡 2) ∞ (hqt q)
    change Injective (mfderiv (𝓡 1) (𝓡 2) (F ∘ fun q : S1 => (q, t)) q)
    rw [mfderiv_comp q (hloc.contMDiffAt.mdifferentiableAt (by simp)) hpair]
    apply (hloc.mfderivToContinuousLinearEquiv (by simp)).injective.comp
    change Injective (mfderiv (𝓡 1) Iprod
      (fun q : S1 => (id q, (fun _ : S1 => t) q)) q)
    rw [mfderiv_prodMk mdifferentiableAt_id mdifferentiableAt_const,
      mfderiv_id, mfderiv_const]
    intro z w heq
    exact congrArg Prod.fst heq
  have hg : ContMDiff (𝓡 1) (𝓡 3) ∞ (f ∘ s) := hf.contMDiff.comp hs
  have hgheight (q : S1) : inner Real v ((f ∘ s) q) = t :=
    (hheight (s q)).trans (hlevel q t ht)
  have hgder (q : S1) : Injective (mfderiv (𝓡 1) (𝓡 3) (f ∘ s) q) := by
    rw [mfderiv_comp q (hf.contMDiff.mdifferentiable (by simp) (s q))
      (hs.mdifferentiable (by simp) q)]
    exact (injective_mfderiv_sphere_embedding hf (s q)).comp (hsder q)
  let k : S1 → (Real ∙ v)ᗮ := fun q => (Real ∙ v)ᗮ.orthogonalProjectionOnto ((f ∘ s) q)
  have hk : ContMDiff (𝓡 1) 𝓘(Real, (Real ∙ v)ᗮ) ∞ k :=
    (Real ∙ v)ᗮ.orthogonalProjectionOnto.contMDiff.comp hg
  have hkinj : Injective k :=
    injective_projection_of_height_eq hv hgheight (hf.isEmbedding.injective.comp hsinj)
  have hkder := injective_mfderiv_projection_of_height_eq hv hg hgheight hgder
  have hJ : ContMDiff 𝓘(Real, (Real ∙ v)ᗮ) (𝓡 2) ∞ J.toContinuousLinearEquiv :=
    J.toContinuousLinearEquiv.contDiff.contMDiff
  apply isSmoothEmbedding_of_injective_mfderiv (hJ.comp hk) (J.injective.comp hkinj)
  intro q
  change Injective (mfderiv (𝓡 1) (𝓡 2) (J.toContinuousLinearEquiv ∘ k) q)
  rw [mfderiv_comp q (hJ.mdifferentiable (by simp) _) (hk.mdifferentiable (by simp) _)]
  exact (J.toContinuousLinearEquiv.toDiffeomorph.mfderivToContinuousLinearEquiv
    (by simp) (k q)).injective.comp (hkder q)

private theorem exists_supported_height_family
    {v : E3} (hv : ‖v‖ = 1) (J : (Real ∙ v)ᗮ ≃ₗᵢ[Real] E2)
    {a b η : Real} (hab : a < b) (hη : 0 < η)
    (Phi : Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (hPhi : ContDiff Real ∞ (fun z : Real × E2 => Phi z.1 z.2))
    (ha : ∀ x, Phi a x = x) {S : Set E2} (hS : IsCompact S)
    (hfix : ∀ t x, x ∉ S → Phi t x = x) :
    ∃ K : Set E3, IsCompact K ∧ K ⊆ {x | inner Real v x ∈ Icc (a - η) (b + η)} ∧
      ∃ H : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
        (∀ x, inner Real v (H x) = inner Real v x) ∧
        (∀ x, inner Real v x = a → H x = x) ∧
        (∀ x ∉ K, H x = x) ∧
        ∀ t ∈ Icc a b, ∀ x : E2,
          H (t • v + (J.symm x : E3)) = t • v + (J.symm (Phi t x) : E3) := by
  let m := (a + b) / 2
  let r := (b - a) / 2
  let χ : ContDiffBump m := ⟨r, r + η, by dsimp [r]; linarith, by linarith⟩
  let β : Real → Real := fun t => a + χ t * (t - a)
  have hβ : ContDiff Real ∞ β :=
    contDiff_const.add (χ.contDiff.mul (contDiff_id.sub contDiff_const))
  have hβa : β a = a := by simp [β]
  have hβid (t : Real) (ht : t ∈ Icc a b) : β t = t := by
    dsimp [β]
    rw [χ.one_of_mem_closedBall (by
      change |t - m| ≤ r
      rw [abs_le]
      dsimp [m, r]
      constructor <;> linarith [ht.1, ht.2]), one_mul]
    ring
  have hPm : ContMDiff (𝓘(Real, Real).prod (𝓡 2)) (𝓡 2) ∞
      (fun z : Real × E2 => Phi z.1 z.2) := by
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
    exact hPhi.contMDiff
  have hPi := Poincare.Manifold.contMDiff_diffeomorph_family_symm Phi hPm
  rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hPi
  let G : Diffeomorph 𝓘(Real, Real × E2) 𝓘(Real, Real × E2)
      (Real × E2) (Real × E2) ∞ := {
    toEquiv := {
      toFun := fun z => (z.1, Phi (β z.1) z.2)
      invFun := fun z => (z.1, (Phi (β z.1)).symm z.2)
      left_inv := fun z => by simp
      right_inv := fun z => by simp }
    contMDiff_toFun := (contDiff_fst.prodMk
      (hPhi.comp ((hβ.comp contDiff_fst).prodMk contDiff_snd))).contMDiff
    contMDiff_invFun := (contDiff_fst.prodMk
      (hPi.contDiff.comp ((hβ.comp contDiff_fst).prodMk contDiff_snd))).contMDiff }
  let A := (((ContinuousLinearEquiv.refl Real Real).prodCongr
    J.symm.toContinuousLinearEquiv).trans
      (Poincare.Geometry.Euclidean.heightCoordinates hv)).toDiffeomorph
  have hA (z : Real × E2) : A z = z.1 • v + (J.symm z.2 : E3) := rfl
  have hheight (z : Real × E2) : inner Real v (A z) = z.1 := by
    rw [hA]
    simp [inner_add_right, inner_smul_right, hv,
      Submodule.mem_orthogonal_singleton_iff_inner_right.mp (J.symm z.2).property]
  let K := A '' (Icc (a - η) (b + η) ×ˢ S)
  let H := (A.symm.trans G).trans A
  refine ⟨K, (isCompact_Icc.prod hS).image A.contMDiff.continuous, ?_, H, ?_, ?_, ?_, ?_⟩
  · rintro x ⟨z, hz, rfl⟩
    change inner Real v (A z) ∈ Icc (a - η) (b + η)
    rw [hheight]
    exact hz.1
  · intro x
    change inner Real v (A (G (A.symm x))) = inner Real v x
    rw [hheight]
    change (A.symm x).1 = inner Real v x
    rw [← hheight, A.apply_symm_apply]
  · intro x hx
    have hz : (A.symm x).1 = a := by rw [← hheight, A.apply_symm_apply, hx]
    change A (G (A.symm x)) = x
    change A ((A.symm x).1, Phi (β (A.symm x).1) (A.symm x).2) = x
    rw [hz, hβa, ha, ← hz]
    exact A.apply_symm_apply x
  · intro x hx
    have hz : A.symm x ∉ Icc (a - η) (b + η) ×ˢ S := by
      intro hin
      exact hx ⟨A.symm x, hin, A.apply_symm_apply x⟩
    have hGfix : G (A.symm x) = A.symm x := by
      refine Prod.ext ?_ ?_
      · rfl
      change Phi (β (A.symm x).1) (A.symm x).2 = (A.symm x).2
      by_cases ht : (A.symm x).1 ∈ Icc (a - η) (b + η)
      · exact hfix _ _ (fun hs => hz ⟨ht, hs⟩)
      · have hdist : r + η ≤ dist (A.symm x).1 m := by
          rw [Real.dist_eq, le_abs]
          simp only [mem_Icc, not_and_or, not_le] at ht
          dsimp [r, m]
          rcases ht with ht | ht
          · right; linarith
          · left; linarith
        change Phi (a + χ (A.symm x).1 * ((A.symm x).1 - a)) _ = _
        rw [χ.zero_of_le_dist hdist, zero_mul, add_zero, ha]
    change A (G (A.symm x)) = x
    rw [hGfix, A.apply_symm_apply]
  · intro t ht x
    rw [← hA (t, x)]
    change A (G (A.symm (A (t, x)))) = _
    rw [A.symm_apply_apply]
    change A (t, Phi (β t) x) = _
    rw [hβid t ht, hA]

theorem exists_supported_ambient_regular_band_flattening_of_smooth
    {f : S2 → E3} (hf : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f)
    {h : S2 → Real} (hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ h)
    {v : E3} (hv : ‖v‖ = 1) (hheight : ∀ p, inner Real v (f p) = h p)
    {a b : Real} (hab : a < b)
    (hregular : ∀ p : S2, h p ∈ Icc a b → mfderiv (𝓡 2) 𝓘(Real, Real) h p ≠ 0)
    (p : S2) (hp : h p = a) {η : Real} (hη : 0 < η) :
    ∃ δ : Real, 0 < δ ∧ ∃ F : OpenPartialHomeomorph (S1 × Real) S2,
      F.source = univ ×ˢ Ioo (a - δ) (b + δ) ∧
      ContMDiffOn Iprod (𝓡 2) ∞ F F.source ∧
      ContMDiffOn (𝓡 2) Iprod ∞ F.symm F.target ∧
      (∀ q t, t ∈ Ioo (a - δ) (b + δ) → h (F (q, t)) = t) ∧
      range (fun q : S1 => F (q, a)) = connectedComponentIn (h ⁻¹' {a}) p ∧
      F '' (univ ×ˢ Icc a b) = connectedComponentIn (h ⁻¹' Icc a b) p ∧
      ∃ K : Set E3, IsCompact K ∧ K ⊆ {x | inner Real v x ∈ Icc (a - η) (b + η)} ∧
        ∃ D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
          (∀ x, inner Real v (D x) = inner Real v x) ∧
          (∀ x, inner Real v x = a → D x = x) ∧
          (∀ x ∉ K, D x = x) ∧
          (∀ t ∈ Icc a b, ∀ q, D (f (F (q, t))) = f (F (q, a)) + (t - a) • v) ∧
          D '' (f '' connectedComponentIn (h ⁻¹' Icc a b) p) =
            (fun z : E3 × Real => z.1 + (z.2 - a) • v) ''
              ((f '' connectedComponentIn (h ⁻¹' {a}) p) ×ˢ Icc a b) := by
  obtain ⟨δ, hδ, F, hsource, hF, hFinv, hlevel, hcentral, hband⟩ :=
    exists_smooth_regular_band_component_of_smooth hh hab hregular p hp
  obtain ⟨κ, hκ, hκrange, hκid⟩ := exists_smooth_band_cutoff hab hδ
  let J : (Real ∙ v)ᗮ ≃ₗᵢ[Real] E2 :=
    (OrthonormalBasis.fromOrthogonalSpanSingleton 2 (by
      intro heq
      simp [heq] at hv)).repr
  let γ : Real × S1 → E2 :=
    fun z => J ((Real ∙ v)ᗮ.orthogonalProjectionOnto (f (F (z.2, κ z.1))))
  have hmap : ContMDiff Itime Iprod ∞ (fun z : Real × S1 => (z.2, κ z.1)) :=
    contMDiff_snd.prodMk (hκ.contMDiff.comp contMDiff_fst)
  have hFt : ContMDiff Itime (𝓡 2) ∞ (fun z : Real × S1 => F (z.2, κ z.1)) := by
    intro z
    have hz : (z.2, κ z.1) ∈ F.source := by
      rw [hsource]
      exact ⟨mem_univ _, hκrange z.1⟩
    exact (hF.contMDiffAt (F.open_source.mem_nhds hz)).comp z (hmap z)
  have hγ : ContMDiff Itime (𝓡 2) ∞ γ :=
    J.toContinuousLinearEquiv.contDiff.contMDiff.comp
      ((Real ∙ v)ᗮ.orthogonalProjectionOnto.contMDiff.comp (hf.contMDiff.comp hFt))
  have hemb (t : Real) :
      _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞ (fun q => γ (t, q)) :=
    smoothEmbedding_projected_band_slice hf hv hheight J F hsource hF hFinv hlevel
      (κ t) (hκrange t)
  obtain ⟨Phi, hPhi0, hPhi, ⟨S, hS, hPhifix⟩, hPhimotion⟩ :=
    exists_ambient_isotopy_of_circle_isotopy hab.le γ hγ (fun t _ => hemb t)
  obtain ⟨K, hK, hKheight, H, hHheight, hHa, hHfix, hHmotion⟩ :=
    exists_supported_height_family hv J hab hη Phi hPhi hPhi0 hS hPhifix
  have hlift (t : Real) (ht : t ∈ Icc a b) (q : S1) :
      f (F (q, t)) = t • v + (J.symm (γ (t, q)) : E3) := by
    have htδ : t ∈ Ioo (a - δ) (b + δ) :=
      ⟨by linarith [ht.1], by linarith [ht.2]⟩
    change f (F (q, t)) = t • v +
      (J.symm (J ((Real ∙ v)ᗮ.orthogonalProjectionOnto (f (F (q, κ t))))) : E3)
    rw [J.symm_apply_apply, hκid t ht]
    exact eq_height_smul_add_projection hv
      (fun q : S1 => (hheight (F (q, t))).trans (hlevel q t htδ)) q
  have hflat (t : Real) (ht : t ∈ Icc a b) (q : S1) :
      H.symm (f (F (q, t))) = f (F (q, a)) + (t - a) • v := by
    rw [hlift t ht q, ← hPhimotion t ht q, ← hHmotion t ht,
      H.symm_apply_apply, hlift a ⟨le_rfl, hab.le⟩ q, sub_smul]
    abel
  refine ⟨δ, hδ, F, hsource, hF, hFinv, hlevel, hcentral, hband,
    K, hK, hKheight, H.symm, ?_, ?_, ?_, hflat, ?_⟩
  · intro x
    have heq := hHheight (H.symm x)
    rw [H.apply_symm_apply] at heq
    exact heq.symm
  · intro x hx
    apply H.injective
    change H (H.symm x) = H x
    rw [H.apply_symm_apply, hHa x hx]
  · intro x hx
    apply H.injective
    change H (H.symm x) = H x
    rw [H.apply_symm_apply, hHfix x hx]
  · rw [← hband]
    ext x
    constructor
    · rintro ⟨y, ⟨z, ⟨w, hw, rfl⟩, rfl⟩, rfl⟩
      refine ⟨(f (F (w.1, a)), w.2), ⟨?_, hw.2⟩, ?_⟩
      · exact ⟨F (w.1, a), hcentral ▸ mem_range_self w.1, rfl⟩
      · exact (hflat w.2 hw.2 w.1).symm
    · rintro ⟨⟨y, t⟩, ⟨⟨z, hz, rfl⟩, ht⟩, rfl⟩
      obtain ⟨q, hq⟩ := hcentral.symm ▸ hz
      change F (q, a) = z at hq
      refine ⟨f (F (q, t)), ⟨F (q, t), ⟨(q, t), ⟨mem_univ _, ht⟩, rfl⟩, rfl⟩, ?_⟩
      rw [hflat t ht q, hq]

theorem exists_supported_ambient_regular_band_flattening
    {f : S2 → E3} (hf : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f)
    {h : S2 → Real} (hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ h)
    (hfinite : {p : S2 | mfderiv (𝓡 2) 𝓘(Real, Real) h p = 0}.Finite)
    {v : E3} (hv : ‖v‖ = 1) (hheight : ∀ p, inner Real v (f p) = h p)
    {a b : Real} (hab : a < b)
    (hregular : ∀ p : S2, h p ∈ Icc a b → mfderiv (𝓡 2) 𝓘(Real, Real) h p ≠ 0)
    (p : S2) (hp : h p = a) {η : Real} (hη : 0 < η) :
    ∃ δ : Real, 0 < δ ∧ ∃ F : OpenPartialHomeomorph (S1 × Real) S2,
      F.source = univ ×ˢ Ioo (a - δ) (b + δ) ∧
      ContMDiffOn Iprod (𝓡 2) ∞ F F.source ∧
      ContMDiffOn (𝓡 2) Iprod ∞ F.symm F.target ∧
      (∀ q t, t ∈ Ioo (a - δ) (b + δ) → h (F (q, t)) = t) ∧
      range (fun q : S1 => F (q, a)) = connectedComponentIn (h ⁻¹' {a}) p ∧
      F '' (univ ×ˢ Icc a b) = connectedComponentIn (h ⁻¹' Icc a b) p ∧
      ∃ K : Set E3, IsCompact K ∧ K ⊆ {x | inner Real v x ∈ Icc (a - η) (b + η)} ∧
        ∃ D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
          (∀ x, inner Real v (D x) = inner Real v x) ∧
          (∀ x, inner Real v x = a → D x = x) ∧
          (∀ x ∉ K, D x = x) ∧
          (∀ t ∈ Icc a b, ∀ q, D (f (F (q, t))) = f (F (q, a)) + (t - a) • v) ∧
          D '' (f '' connectedComponentIn (h ⁻¹' Icc a b) p) =
            (fun z : E3 × Real => z.1 + (z.2 - a) • v) ''
              ((f '' connectedComponentIn (h ⁻¹' {a}) p) ×ˢ Icc a b) :=
  (fun _ => exists_supported_ambient_regular_band_flattening_of_smooth
    hf hh hv hheight hab hregular p hp hη) hfinite

end Poincare.Manifold.Schoenflies
