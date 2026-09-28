import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.Boundary.Chart
import Mathlib.Analysis.Calculus.Deriv.Slope









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology Manifold ContDiff

namespace PoincareConjecture.Topology.Surface

variable {S : Type*} [TopologicalSpace S]



theorem chartTriangle_transverse_nonpos
    (e f : OpenPartialHomeomorph S (ℝ × ℝ))
    {a b : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1)
    (he : (0, a) ∈ e.target) (hf : (0, b) ∈ f.target)
    (hpoint : e.symm (0, a) = f.symm (0, b))
    (hdisjoint : Disjoint
      (e.symm '' {p : ℝ × ℝ | 0 < p.1 ∧ 0 < p.2 ∧ p.1 + p.2 < 1})
      (f.symm '' {p : ℝ × ℝ | 0 < p.1 ∧ 0 < p.2 ∧ p.1 + p.2 < 1})) :
    ∀ᶠ u in 𝓝[>] (0 : ℝ), (e (f.symm (u, b))).1 ≤ 0 := by
  have hx : f.symm (0, b) ∈ e.source := hpoint ▸ e.map_target he
  have hpair : ContinuousAt (fun u : ℝ => (u, b)) 0 :=
    continuousAt_id.prodMk continuousAt_const
  have hcurve : ContinuousAt (fun u : ℝ => f.symm (u, b)) 0 :=
    (f.symm.continuousAt hf).comp (f := fun u : ℝ => (u, b)) hpair
  have htransition : ContinuousAt (fun u : ℝ => e (f.symm (u, b))) 0 :=
    (e.continuousAt hx).comp (f := fun u : ℝ => f.symm (u, b)) hcurve
  have hzero : e (f.symm (0, b)) = (0, a) := by rw [← hpoint, e.right_inv he]
  have hsource : ∀ᶠ u in 𝓝 (0 : ℝ), f.symm (u, b) ∈ e.source :=
    hcurve.preimage_mem_nhds (e.open_source.mem_nhds hx)
  have hy : ∀ᶠ u in 𝓝 (0 : ℝ), 0 < (e (f.symm (u, b))).2 :=
    (htransition.snd.eventually (Ioi_mem_nhds (by simpa only [hzero] using ha.1)))
  have hsum : ∀ᶠ u in 𝓝 (0 : ℝ),
      (e (f.symm (u, b))).1 + (e (f.symm (u, b))).2 < 1 :=
    ((htransition.fst.add htransition.snd).eventually
      (Iio_mem_nhds (by simpa only [Pi.add_apply, hzero, zero_add] using ha.2)))
  have hu : ∀ᶠ u in 𝓝 (0 : ℝ), u + b < 1 :=
    (continuousAt_id.add continuousAt_const).eventually
      (Iio_mem_nhds (by simpa using hb.2))
  filter_upwards [hsource.filter_mono nhdsWithin_le_nhds,
    hy.filter_mono nhdsWithin_le_nhds, hsum.filter_mono nhdsWithin_le_nhds,
    hu.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with u hs hy hsum hu hpos
  by_contra h
  have hfirst : 0 < (e (f.symm (u, b))).1 := lt_of_not_ge h
  exact disjoint_left.mp hdisjoint
    ⟨e (f.symm (u, b)), ⟨hfirst, hy, hsum⟩, e.left_inv hs⟩
    ⟨(u, b), ⟨hpos, hb.1, hu⟩, rfl⟩



theorem chartTriangle_transverse_deriv_nonpos
    (e f : OpenPartialHomeomorph S (ℝ × ℝ))
    {a b d : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1)
    (he : (0, a) ∈ e.target) (hf : (0, b) ∈ f.target)
    (hpoint : e.symm (0, a) = f.symm (0, b))
    (hdisjoint : Disjoint
      (e.symm '' {p : ℝ × ℝ | 0 < p.1 ∧ 0 < p.2 ∧ p.1 + p.2 < 1})
      (f.symm '' {p : ℝ × ℝ | 0 < p.1 ∧ 0 < p.2 ∧ p.1 + p.2 < 1}))
    (hd : HasDerivAt (fun u : ℝ => (e (f.symm (u, b))).1) d 0) : d ≤ 0 := by
  have hzero : (e (f.symm (0, b))).1 = 0 := by rw [← hpoint, e.right_inv he]
  apply le_of_tendsto hd.tendsto_slope_zero_right
  filter_upwards [chartTriangle_transverse_nonpos e f ha hb he hf hpoint hdisjoint,
    self_mem_nhdsWithin] with u hu hpos
  simp only [zero_add, hzero, sub_zero, smul_eq_mul]
  exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr (le_of_lt hpos)) hu



theorem chartTriangle_shared_edge_germ
    (e f : OpenPartialHomeomorph S (ℝ × ℝ))
    (he : ∀ s ∈ Icc (0 : ℝ) 1, (0, s) ∈ e.target)
    (himage : (fun s : ℝ => f.symm (0, s)) '' Icc (0 : ℝ) 1 ⊆
      (fun s : ℝ => e.symm (0, s)) '' Icc (0 : ℝ) 1)
    {b : ℝ} (hb : b ∈ Ioo (0 : ℝ) 1) :
    ∀ᶠ s in 𝓝 b, (e (f.symm (0, s))).1 = 0 := by
  filter_upwards [isOpen_Ioo.mem_nhds hb] with s hs
  obtain ⟨t, ht, hts⟩ := himage (mem_image_of_mem _ (Ioo_subset_Icc_self hs))
  rw [← hts, e.right_inv (he t ht)]

variable [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]




theorem chartTriangle_transverse_deriv_neg
    (e f : OpenPartialHomeomorph S (ℝ × ℝ))
    (heD : e.MDifferentiable (𝓡 2) 𝓘(ℝ, ℝ × ℝ))
    (hfD : f.MDifferentiable (𝓡 2) 𝓘(ℝ, ℝ × ℝ))
    {a b : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1)
    (he : (0, a) ∈ e.target) (hf : (0, b) ∈ f.target)
    (hpoint : e.symm (0, a) = f.symm (0, b))
    (hdisjoint : Disjoint
      (e.symm '' {p : ℝ × ℝ | 0 < p.1 ∧ 0 < p.2 ∧ p.1 + p.2 < 1})
      (f.symm '' {p : ℝ × ℝ | 0 < p.1 ∧ 0 < p.2 ∧ p.1 + p.2 < 1}))
    (hboundary : ∀ᶠ s in 𝓝 b, (e (f.symm (0, s))).1 = 0) :
    (fderiv ℝ (fun p : ℝ × ℝ => e (f.symm p)) (0, b) (1, 0)).1 < 0 := by
  let C := f.symm.trans e
  have hCD : C.MDifferentiable 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) := hfD.symm.trans heD
  have hx : f.symm (0, b) ∈ e.source := hpoint ▸ e.map_target he
  have hsrc : (0, b) ∈ C.source := ⟨hf, hx⟩
  let L := fderiv ℝ C (0, b)
  have hL : HasFDerivAt C L (0, b) := (hCD.mdifferentiableAt hsrc).differentiableAt.hasFDerivAt
  have hsurj : Function.Surjective L := by
    have h := hCD.mfderiv_surjective hsrc
    dsimp only [TangentSpace] at h
    simpa only [mfderiv_eq_fderiv] using h
  have hnormal : HasDerivAt (fun u : ℝ => (e (f.symm (u, b))).1) (L (1, 0)).1 0 := by
    have h := hL.comp_hasDerivAt 0 ((hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const 0 b))
    exact (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt 0 h
  have htan : HasDerivAt (fun s : ℝ => (e (f.symm (0, s))).1) (L (0, 1)).1 b := by
    have h := hL.comp_hasDerivAt b ((hasDerivAt_const b (0 : ℝ)).prodMk (hasDerivAt_id b))
    exact (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt b h
  have htan0 : (L (0, 1)).1 = 0 :=
    htan.unique ((hasDerivAt_const b (0 : ℝ)).congr_of_eventuallyEq hboundary)
  have hnonpos := chartTriangle_transverse_deriv_nonpos e f ha hb he hf hpoint hdisjoint hnormal
  have hne : (L (1, 0)).1 ≠ 0 := by
    intro hzero
    obtain ⟨p, hp⟩ := hsurj (1, 0)
    have hpdecomp : p = p.1 • (1, 0) + p.2 • (0, 1) := by ext <;> simp
    have heq := congrArg Prod.fst hp
    rw [hpdecomp, map_add, map_smul, map_smul] at heq
    change p.1 * (L (1, 0)).1 + p.2 * (L (0, 1)).1 = 1 at heq
    rw [hzero, htan0, mul_zero, mul_zero, add_zero] at heq
    exact zero_ne_one heq
  exact lt_of_le_of_ne hnonpos hne

end PoincareConjecture.Topology.Surface
