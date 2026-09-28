import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.RegularLevel.Tube
import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.RegularLevel.Projection
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension







open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.PoincareConjecture

namespace M38Schoenflies








noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies

open _root_.Poincare.Geometry.Manifold

private abbrev E1 := EuclideanSpace Real (Fin 1)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : EuclideanSpace Real (Fin 2)) 1
private abbrev S2 := sphere (0 : E3) 1
local notation "Iprod" => ModelWithCorners.prod (𝓡 1) 𝓘(Real, Real)
local notation "Itime" => ModelWithCorners.prod 𝓘(Real, Real) (𝓡 1)

private instance : Fact (Module.finrank Real (EuclideanSpace Real (Fin 2)) = 1 + 1) :=
  ⟨by simp⟩
private instance : ChartedSpace (E1 × Real) (S1 × Real) :=
  prodChartedSpace E1 S1 Real Real
private instance : ChartedSpace (Real × E1) (Real × S1) :=
  prodChartedSpace Real Real E1 S1

private theorem exists_smooth_time_cutoff {ε : Real} (hε : 0 < ε) :
    ∃ r : Real, 0 < r ∧ r < ε ∧ ∃ a : Real -> Real,
      ContDiff Real ∞ a ∧ (∀ t, a t ∈ Ioo (-ε) ε) ∧
      ∀ t ∈ Icc (-r) r, a t = t := by
  let χ : ContDiffBump (0 : Real) :=
    { rIn := ε / 4
      rOut := ε / 2
      rIn_pos := by positivity
      rIn_lt_rOut := by linarith }
  refine ⟨ε / 4, by positivity, by linarith, fun t => χ t * t,
    χ.contDiff.mul contDiff_id, ?_, ?_⟩
  · intro t
    have hbound : |χ t * t| < ε := by
      by_cases ht : |t| < ε / 2
      · rw [abs_mul, abs_of_nonneg χ.nonneg]
        calc
          χ t * |t| ≤ 1 * |t| := mul_le_mul_of_nonneg_right χ.le_one (abs_nonneg _)
          _ < ε := by simpa using ht.trans (by linarith : ε / 2 < ε)
      · have hz : χ t = 0 := χ.zero_of_le_dist (by
          simpa only [Real.dist_eq, sub_zero] using le_of_not_gt ht)
        simpa only [hz, zero_mul, abs_zero] using hε
    exact abs_lt.mp hbound
  · intro t ht
    change χ t * t = t
    rw [χ.one_of_mem_closedBall (by
      simpa only [mem_closedBall, Real.dist_eq, sub_zero] using abs_le.mpr ht), one_mul]



theorem smoothEmbedding_projected_tube_slice
    {f : S2 -> E3} (hf : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f)
    {h : S2 -> Real} {v : E3} (hv : ‖v‖ = 1)
    (hheight : ∀ p, inner Real v (f p) = h p)
    (F : OpenPartialHomeomorph (S1 × Real) S2) {ε c : Real}
    (hsource : F.source = univ ×ˢ Ioo (-ε) ε)
    (hF : ContMDiffOn Iprod (𝓡 2) ∞ F F.source)
    (hFinv : ContMDiffOn (𝓡 2) Iprod ∞ F.symm F.target)
    (hlevel : ∀ q t, t ∈ Ioo (-ε) ε -> h (F (q, t)) = c + t)
    (t : Real) (ht : t ∈ Ioo (-ε) ε) :
    _root_.Manifold.IsSmoothEmbedding (𝓡 1) 𝓘(Real, (Real ∙ v)ᗮ) ∞
      (fun q => (Real ∙ v)ᗮ.orthogonalProjectionOnto (f (F (q, t)))) := by
  let D : PartialDiffeomorph Iprod (𝓡 2) (S1 × Real) S2 ∞ :=
    { toPartialEquiv := F.toPartialEquiv
      open_source := F.open_source
      open_target := F.open_target
      contMDiffOn_toFun := hF
      contMDiffOn_invFun := hFinv }
  have hqt (q : S1) : (q, t) ∈ F.source := by rw [hsource]; exact ⟨mem_univ _, ht⟩
  let s : S1 -> S2 := fun q => F (q, t)
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
    intro u w heq
    exact congrArg Prod.fst heq
  have hg : ContMDiff (𝓡 1) (𝓡 3) ∞ (f ∘ s) := hf.contMDiff.comp hs
  have hgheight (q : S1) : inner Real v ((f ∘ s) q) = c + t :=
    (hheight (s q)).trans (hlevel q t ht)
  have hgder (q : S1) : Injective (mfderiv (𝓡 1) (𝓡 3) (f ∘ s) q) := by
    rw [mfderiv_comp q (hf.contMDiff.mdifferentiable (by simp) (s q))
      (hs.mdifferentiable (by simp) q)]
    exact (injective_mfderiv_sphere_embedding hf (s q)).comp (hsder q)
  exact isSmoothEmbedding_of_injective_mfderiv
    ((Real ∙ v)ᗮ.orthogonalProjectionOnto.contMDiff.comp hg)
    (injective_projection_of_height_eq hv hgheight (hf.isEmbedding.injective.comp hsinj))
    (injective_mfderiv_projection_of_height_eq hv hg hgheight hgder)




theorem exists_smooth_planar_family_of_regular_level_component_of_smooth
    {f : S2 -> E3} (hf : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f)
    {h : S2 -> Real} (hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ h)
    {v : E3} (hv : ‖v‖ = 1) (hheight : ∀ p, inner Real v (f p) = h p)
    (c : Real) (hc : ∀ p, h p = c -> mfderiv (𝓡 2) 𝓘(Real, Real) h p ≠ 0)
    (p : S2) (hp : h p = c) :
    ∃ ε : Real, 0 < ε ∧ ∃ F : OpenPartialHomeomorph (S1 × Real) S2,
      F.source = univ ×ˢ Ioo (-ε) ε ∧
      ContMDiffOn Iprod (𝓡 2) ∞ F F.source ∧
      ContMDiffOn (𝓡 2) Iprod ∞ F.symm F.target ∧
      (∀ q t, t ∈ Ioo (-ε) ε -> h (F (q, t)) = c + t) ∧
      range (fun q : S1 => F (q, 0)) = connectedComponentIn (h ⁻¹' {c}) p ∧
      ∃ r : Real, 0 < r ∧ r < ε ∧ ∃ γ : Real × S1 -> (Real ∙ v)ᗮ,
        ContMDiff Itime 𝓘(Real, (Real ∙ v)ᗮ) ∞ γ ∧
        (∀ t, _root_.Manifold.IsSmoothEmbedding (𝓡 1) 𝓘(Real, (Real ∙ v)ᗮ) ∞
          (fun q => γ (t, q))) ∧
        range (fun q => γ (0, q)) =
          (fun x => (Real ∙ v)ᗮ.orthogonalProjectionOnto (f x)) ''
            connectedComponentIn (h ⁻¹' {c}) p ∧
        ∀ t ∈ Icc (-r) r, ∀ q,
          γ (t, q) = (Real ∙ v)ᗮ.orthogonalProjectionOnto (f (F (q, t))) ∧
          f (F (q, t)) = (c + t) • v + (γ (t, q) : E3) := by
  obtain ⟨ε, hε, F, hsource, hF, hFinv, hlevel, hcentral⟩ :=
    exists_smooth_regular_level_component_tube_of_smooth hh c hc p hp
  obtain ⟨r, hr, hrε, a, ha, harange, haid⟩ := exists_smooth_time_cutoff hε
  let γ : Real × S1 -> (Real ∙ v)ᗮ :=
    fun z => (Real ∙ v)ᗮ.orthogonalProjectionOnto (f (F (z.2, a z.1)))
  have hmap : ContMDiff Itime Iprod ∞ (fun z : Real × S1 => (z.2, a z.1)) :=
    contMDiff_snd.prodMk (ha.contMDiff.comp contMDiff_fst)
  have hFt : ContMDiff Itime (𝓡 2) ∞ (fun z : Real × S1 => F (z.2, a z.1)) := by
    intro z
    have hz : (z.2, a z.1) ∈ F.source := by
      rw [hsource]
      exact ⟨mem_univ _, harange z.1⟩
    exact (hF.contMDiffAt (F.open_source.mem_nhds hz)).comp z (hmap z)
  have hγ : ContMDiff Itime 𝓘(Real, (Real ∙ v)ᗮ) ∞ γ :=
    (Real ∙ v)ᗮ.orthogonalProjectionOnto.contMDiff.comp (hf.contMDiff.comp hFt)
  have hγeq (t : Real) (ht : t ∈ Icc (-r) r) (q : S1) :
      γ (t, q) = (Real ∙ v)ᗮ.orthogonalProjectionOnto (f (F (q, t))) := by
    change (Real ∙ v)ᗮ.orthogonalProjectionOnto (f (F (q, a t))) = _
    rw [haid t ht]
  refine ⟨ε, hε, F, hsource, hF, hFinv, hlevel, hcentral,
    r, hr, hrε, γ, hγ, ?_, ?_, ?_⟩
  · intro t
    exact smoothEmbedding_projected_tube_slice hf hv hheight F hsource hF hFinv hlevel
      (a t) (harange t)
  · have ha0 : a 0 = 0 := haid 0 ⟨by linarith, hr.le⟩
    change range (fun q => (Real ∙ v)ᗮ.orthogonalProjectionOnto (f (F (q, a 0)))) = _
    rw [ha0, ← hcentral, ← range_comp]
    rfl
  · intro t ht q
    refine ⟨hγeq t ht q, ?_⟩
    have htε : t ∈ Ioo (-ε) ε := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    rw [hγeq t ht q]
    exact eq_height_smul_add_projection hv
      (fun q : S1 => (hheight (F (q, t))).trans (hlevel q t htε)) q


theorem exists_smooth_planar_family_of_regular_level_component
    {f : S2 -> E3} (hf : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f)
    {h : S2 -> Real} (hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ h)
    (hfinite : {p : S2 | mfderiv (𝓡 2) 𝓘(Real, Real) h p = 0}.Finite)
    {v : E3} (hv : ‖v‖ = 1) (hheight : ∀ p, inner Real v (f p) = h p)
    (c : Real) (hc : ∀ p, h p = c -> mfderiv (𝓡 2) 𝓘(Real, Real) h p ≠ 0)
    (p : S2) (hp : h p = c) :
    ∃ ε : Real, 0 < ε ∧ ∃ F : OpenPartialHomeomorph (S1 × Real) S2,
      F.source = univ ×ˢ Ioo (-ε) ε ∧
      ContMDiffOn Iprod (𝓡 2) ∞ F F.source ∧
      ContMDiffOn (𝓡 2) Iprod ∞ F.symm F.target ∧
      (∀ q t, t ∈ Ioo (-ε) ε -> h (F (q, t)) = c + t) ∧
      range (fun q : S1 => F (q, 0)) = connectedComponentIn (h ⁻¹' {c}) p ∧
      ∃ r : Real, 0 < r ∧ r < ε ∧ ∃ γ : Real × S1 -> (Real ∙ v)ᗮ,
        ContMDiff Itime 𝓘(Real, (Real ∙ v)ᗮ) ∞ γ ∧
        (∀ t, _root_.Manifold.IsSmoothEmbedding (𝓡 1) 𝓘(Real, (Real ∙ v)ᗮ) ∞
          (fun q => γ (t, q))) ∧
        range (fun q => γ (0, q)) =
          (fun x => (Real ∙ v)ᗮ.orthogonalProjectionOnto (f x)) ''
            connectedComponentIn (h ⁻¹' {c}) p ∧
        ∀ t ∈ Icc (-r) r, ∀ q,
          γ (t, q) = (Real ∙ v)ᗮ.orthogonalProjectionOnto (f (F (q, t))) ∧
          f (F (q, t)) = (c + t) • v + (γ (t, q) : E3) :=
  (fun _ => exists_smooth_planar_family_of_regular_level_component_of_smooth
    hf hh hv hheight c hc p hp) hfinite

end Poincare.Manifold.Schoenflies

end

end M38Schoenflies
