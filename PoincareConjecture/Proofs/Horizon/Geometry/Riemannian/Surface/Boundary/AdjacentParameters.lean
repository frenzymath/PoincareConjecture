import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.Boundary.AdjacentFrames
import Mathlib.Analysis.Calculus.Deriv.MeanValue

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter VectorField
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.Topology.Surface

variable {S : Type*} [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]

private theorem interval_bijOn_order {φ : ℝ → ℝ}
    (hc : ContinuousOn φ (Icc (0 : ℝ) 1))
    (hb : BijOn φ (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1)) :
    (φ 0 = 0 ∧ φ 1 = 1 ∧ StrictMonoOn φ (Icc (0 : ℝ) 1)) ∨
      (φ 0 = 1 ∧ φ 1 = 0 ∧ StrictAntiOn φ (Icc (0 : ℝ) 1)) := by
  rcases hc.strictMonoOn_of_injOn_Icc' zero_le_one hb.injOn with hm | hm
  · have he := (hc.image_Icc_of_monotoneOn zero_le_one hm.monotoneOn).symm.trans hb.image_eq
    have hends := (Icc_eq_Icc_iff (hm.monotoneOn (by simp) (by simp) zero_le_one)).mp he
    exact Or.inl ⟨hends.1, hends.2, hm⟩
  · have he := (hc.image_Icc_of_antitoneOn zero_le_one hm.antitoneOn).symm.trans hb.image_eq
    have hends := (Icc_eq_Icc_iff (hm.antitoneOn (by simp) (by simp) zero_le_one)).mp he
    exact Or.inr ⟨hends.2, hends.1, hm⟩

omit [IsManifold (𝓡 2) ∞ S] in

theorem chartTriangle_side_parameter
    (e f : OpenPartialHomeomorph S (ℝ × ℝ))
    (he : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ × ℝ) ∞ e e.source)
    (hfi : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ∞ f.symm f.target)
    (het : ∀ s ∈ Icc (0 : ℝ) 1, (0, s) ∈ e.target)
    (hft : ∀ s ∈ Icc (0 : ℝ) 1, (0, s) ∈ f.target)
    (himage : (fun s : ℝ => f.symm (0, s)) '' Icc (0 : ℝ) 1 =
      (fun s : ℝ => e.symm (0, s)) '' Icc (0 : ℝ) 1) :
    let φ := fun t : ℝ => (e (f.symm (0, t))).2
    (∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ ∞ φ t) ∧
      BijOn φ (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1) ∧
      MapsTo φ (Ioo (0 : ℝ) 1) (Ioo (0 : ℝ) 1) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, e.symm (0, φ t) = f.symm (0, t)) := by
  let φ := fun t : ℝ => (e (f.symm (0, t))).2
  have hcoord (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      e (f.symm (0, t)) = (0, φ t) ∧ φ t ∈ Icc (0 : ℝ) 1 ∧
        e.symm (0, φ t) = f.symm (0, t) := by
    obtain ⟨s, hs, hst⟩ := himage.subset (mem_image_of_mem _ ht)
    have hrec : e (f.symm (0, t)) = (0, s) := by rw [← hst, e.right_inv (het s hs)]
    have hφ : φ t = s := congrArg Prod.snd hrec
    exact ⟨by rw [hφ, hrec], hφ ▸ hs, by rw [hφ]; exact hst⟩
  have hsource (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : f.symm (0, t) ∈ e.source := by
    rw [← (hcoord t ht).2.2]
    exact e.map_target (het _ (hcoord t ht).2.1)
  have hsmooth (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : ContDiffAt ℝ ∞ φ t := by
    have hline : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ) ∞ (fun s : ℝ => ((0 : ℝ), s)) t :=
      (show ContDiff ℝ ∞ (fun s : ℝ => ((0 : ℝ), s)) from
        contDiff_const.prodMk contDiff_id).contDiffAt.contMDiffAt
    have hcurve := (hfi.contMDiffAt (f.open_target.mem_nhds (hft t ht))).comp t hline
    have htrans := (he.contMDiffAt (e.open_source.mem_nhds (hsource t ht))).comp t hcurve
    exact (contMDiffAt_iff_contDiffAt.mp htrans).snd
  have hbij : BijOn φ (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1) := by
    refine ⟨fun t ht => (hcoord t ht).2.1, ?_, ?_⟩
    · intro s hs t ht hst
      have hp : f.symm (0, s) = f.symm (0, t) := by
        rw [← (hcoord s hs).2.2, ← (hcoord t ht).2.2, hst]
      exact congrArg Prod.snd (f.symm.injOn (hft s hs) (hft t ht) hp)
    · intro s hs
      obtain ⟨t, ht, hts⟩ := himage.symm.subset (mem_image_of_mem _ hs)
      refine ⟨t, ht, ?_⟩
      change (e (f.symm (0, t))).2 = s
      change f.symm (0, t) = e.symm (0, s) at hts
      rw [hts, e.right_inv (het s hs)]
  refine ⟨hsmooth, hbij, ?_, fun t ht => (hcoord t ht).2.2⟩
  have hc : ContinuousOn φ (Icc (0 : ℝ) 1) :=
    fun t ht => (hsmooth t ht).continuousAt.continuousWithinAt
  intro t ht
  rcases interval_bijOn_order hc hbij with ⟨h0, h1, hm⟩ | ⟨h0, h1, hm⟩
  · exact ⟨by simpa only [h0] using hm (by simp) (Ioo_subset_Icc_self ht) ht.1,
      by simpa only [h1] using hm (Ioo_subset_Icc_self ht) (by simp) ht.2⟩
  · exact ⟨by simpa only [h1] using hm (Ioo_subset_Icc_self ht) (by simp) ht.2,
      by simpa only [h0] using hm (by simp) (Ioo_subset_Icc_self ht) ht.1⟩

omit [IsManifold (𝓡 2) ∞ S] in

theorem chartTriangle_side_parameter_hasDerivAt
    (e f : OpenPartialHomeomorph S (ℝ × ℝ))
    (he : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ × ℝ) ∞ e e.source)
    (hfi : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ∞ f.symm f.target)
    {t : ℝ} (ht : (0, t) ∈ f.target) (hx : f.symm (0, t) ∈ e.source) :
    HasDerivAt (fun s : ℝ => (e (f.symm (0, s))).2)
      (fderiv ℝ (fun p : ℝ × ℝ => e (f.symm p)) (0, t) (0, 1)).2 t := by
  have htrans := (he.contMDiffAt (e.open_source.mem_nhds hx)).comp (0, t)
    (hfi.contMDiffAt (f.open_target.mem_nhds ht))
  have hL := ((contMDiffAt_iff_contDiffAt.mp htrans).differentiableAt (by simp)).hasFDerivAt
  have h := hL.comp_hasDerivAt t ((hasDerivAt_const t (0 : ℝ)).prodMk (hasDerivAt_id t))
  exact (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t h

theorem exists_chartTriangle_side_orientation
    (g : RiemannianMetric 2 S) (e f : OpenPartialHomeomorph S (ℝ × ℝ))
    (he : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ × ℝ) ∞ e e.source)
    (hei : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ∞ e.symm e.target)
    (hf : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ × ℝ) ∞ f f.source)
    (hfi : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ∞ f.symm f.target)
    (Q : RiemannianMetric.AlignedChartFrame g e) (R : RiemannianMetric.AlignedChartFrame g f)
    (het : ∀ s ∈ Icc (0 : ℝ) 1, (0, s) ∈ e.target)
    (hft : ∀ s ∈ Icc (0 : ℝ) 1, (0, s) ∈ f.target)
    (himage : (fun s : ℝ => f.symm (0, s)) '' Icc (0 : ℝ) 1 =
      (fun s : ℝ => e.symm (0, s)) '' Icc (0 : ℝ) 1)
    (hdisjoint : Disjoint
      (e.symm '' {p : ℝ × ℝ | 0 < p.1 ∧ 0 < p.2 ∧ p.1 + p.2 < 1})
      (f.symm '' {p : ℝ × ℝ | 0 < p.1 ∧ 0 < p.2 ∧ p.1 + p.2 < 1})) :
    let φ := fun t : ℝ => (e (f.symm (0, t))).2
    ∃ δ : ℝ, (δ = 1 ∨ δ = -1) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, g.frameOrientation (f.symm (0, t))
        (Q.first (f.symm (0, t))) (Q.second (f.symm (0, t)))
        (R.first (f.symm (0, t))) (R.second (f.symm (0, t))) = δ) ∧
      ((δ = -1 ∧ φ 0 = 0 ∧ φ 1 = 1) ∨ (δ = 1 ∧ φ 0 = 1 ∧ φ 1 = 0)) := by
  let φ := fun t : ℝ => (e (f.symm (0, t))).2
  obtain ⟨hsmooth, hbij, hinner, hpoint⟩ := chartTriangle_side_parameter e f he hfi het hft himage
  have hsource (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : f.symm (0, t) ∈ e.source := by
    rw [← hpoint t ht]
    exact e.map_target (het _ (hbij.mapsTo ht))
  have hc : ContinuousOn φ (Icc (0 : ℝ) 1) :=
    fun t ht => (hsmooth t ht).continuousAt.continuousWithinAt
  have hcurve : ContinuousOn (fun t : ℝ => f.symm (0, t)) (Icc (0 : ℝ) 1) := by
    intro t ht
    exact ((f.symm.continuousAt (hft t ht)).comp
      (f := fun t : ℝ => (0, t)) (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt
  obtain ⟨δ, hδ, hsign⟩ := g.exists_frameOrientation_sign_on_curve
    (Q.smooth_first.mono inter_subset_left) (Q.smooth_second.mono inter_subset_left)
    (R.smooth_first.mono inter_subset_right) (R.smooth_second.mono inter_subset_right)
    (fun x hx => Q.unit_first x hx.1) (fun x hx => Q.unit_second x hx.1)
    (fun x hx => Q.orthogonal x hx.1) (fun x hx => R.unit_first x hx.2)
    (fun x hx => R.unit_second x hx.2) (fun x hx => R.orthogonal x hx.2)
    isPreconnected_Icc hcurve (fun t ht => ⟨hsource t ht, f.map_target (hft t ht)⟩)
  have hnegative (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) : δ * deriv φ t < 0 := by
    have ht' := Ioo_subset_Icc_self ht
    have h := chartTriangle_frameOrientation_mul_tangent_neg g e f he hei hf hfi Q R
      (hinner ht) ht (het _ (hbij.mapsTo ht')) (hft t ht') (hpoint t ht') hdisjoint
      (chartTriangle_shared_edge_germ e f het himage.subset ht)
    dsimp only at h
    rw [hsign t ht'] at h
    change δ * deriv (fun s : ℝ => (e (f.symm (0, s))).2) t < 0
    rw [(chartTriangle_side_parameter_hasDerivAt e f he hfi (hft t ht') (hsource t ht')).deriv]
    exact h
  refine ⟨δ, hδ, hsign, ?_⟩
  rcases hδ with hδ | hδ
  · have hm : StrictAntiOn φ (Icc (0 : ℝ) 1) :=
      strictAntiOn_of_deriv_neg (convex_Icc _ _) hc (fun t ht => by
        rw [interior_Icc] at ht
        simpa only [hδ, one_mul] using hnegative t ht)
    have heq := (hc.image_Icc_of_antitoneOn zero_le_one hm.antitoneOn).symm.trans hbij.image_eq
    have hends := (Icc_eq_Icc_iff (hm.antitoneOn (by simp) (by simp) zero_le_one)).mp heq
    exact Or.inr ⟨hδ, hends.2, hends.1⟩
  · have hm : StrictMonoOn φ (Icc (0 : ℝ) 1) :=
      strictMonoOn_of_deriv_pos (convex_Icc _ _) hc (fun t ht => by
        rw [interior_Icc] at ht
        have hn := hnegative t ht
        rw [hδ, neg_one_mul] at hn
        exact neg_neg_iff_pos.mp hn)
    have heq := (hc.image_Icc_of_monotoneOn zero_le_one hm.monotoneOn).symm.trans hbij.image_eq
    have hends := (Icc_eq_Icc_iff (hm.monotoneOn (by simp) (by simp) zero_le_one)).mp heq
    exact Or.inl ⟨hδ, hends.1, hends.2⟩

end PoincareConjecture.Topology.Surface
