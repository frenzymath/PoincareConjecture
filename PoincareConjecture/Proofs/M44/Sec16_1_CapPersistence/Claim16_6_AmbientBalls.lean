import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_LengthBarrier
import PoincareConjecture.Proofs.M44.Mathlib.PartialHomeomorphCompact
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Transitions

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u v

namespace PoincareConjecture.RiemannianMetric

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) Y]
  [IsManifold (𝓡 3) ∞ X] [IsManifold (𝓡 3) ∞ Y]

theorem inverse_pullback_eq
    (g : RiemannianMetric 3 X) (h : RiemannianMetric 3 Y)
    (C : PartialDiffeomorph (𝓡 3) (𝓡 3) X Y ∞)
    (hmetric : ∀ x ∈ C.source, ∀ v w : TangentSpace (𝓡 3) x,
      h.inner (C x) (mfderiv (𝓡 3) (𝓡 3) C x v)
        (mfderiv (𝓡 3) (𝓡 3) C x w) = g.inner x v w)
    {y : Y} (hy : y ∈ C.target) (v w : TangentSpace (𝓡 3) y) :
    g.inner (C.symm y) (mfderiv (𝓡 3) (𝓡 3) C.symm y v)
      (mfderiv (𝓡 3) (𝓡 3) C.symm y w) = h.inner y v w := by
  have he : C.toOpenPartialHomeomorph.MDifferentiable (𝓡 3) (𝓡 3) :=
    ⟨C.mdifferentiableOn (by simp), C.symm.mdifferentiableOn (by simp)⟩
  have hd : (mfderiv (𝓡 3) (𝓡 3) C (C.symm y)).comp
      (mfderiv (𝓡 3) (𝓡 3) C.symm y) =
        ContinuousLinearMap.id ℝ (TangentSpace (𝓡 3) y) := he.comp_symm_deriv hy
  have hv : mfderiv (𝓡 3) (𝓡 3) C (C.symm y)
      (mfderiv (𝓡 3) (𝓡 3) C.symm y v) = v := congrArg (fun A => A v) hd
  have hw : mfderiv (𝓡 3) (𝓡 3) C (C.symm y)
      (mfderiv (𝓡 3) (𝓡 3) C.symm y w) = w := congrArg (fun A => A w) hd
  have hm := hmetric (C.symm y) (C.map_target hy)
    (mfderiv (𝓡 3) (𝓡 3) C.symm y v) (mfderiv (𝓡 3) (𝓡 3) C.symm y w)
  rw [hv, hw] at hm
  have hright : C.toPartialEquiv (C.symm.toPartialEquiv y) = y := C.right_inv hy
  exact hm.symm.trans (congrArg (fun q : Y => h.inner q v w) hright)

theorem image_ball_of_precompact_partialDiffeomorph
    [RegularSpace X] [T2Space Y]
    (g : RiemannianMetric 3 X) (h : RiemannianMetric 3 Y)
    (C : PartialDiffeomorph (𝓡 3) (𝓡 3) X Y ∞) (hsource : C.source = univ)
    (hmetric : ∀ x (v w : TangentSpace (𝓡 3) x),
      h.inner (C x) (mfderiv (𝓡 3) (𝓡 3) C x v)
        (mfderiv (𝓡 3) (𝓡 3) C x w) = g.inner x v w)
    (p : X) {r : ℝ} (hr : 0 < r) (hcompact : IsCompact (closure (g.ball p r))) :
    C '' g.ball p r = h.ball (C p) r := by
  have hsrc (x : X) : x ∈ C.source := hsource.symm ▸ mem_univ x
  have hgs : IsOpen (g.ball p r) :=
    isOpen_Iio.preimage ((M36.metric_edist_continuous g).comp
      (continuous_const.prodMk continuous_id))
  have hCs := C.toOpenPartialHomeomorph.isOpen_image_of_subset_source hgs
    (fun x _ => hsrc x)
  have hclosure := C.toOpenPartialHomeomorph.image_closure_of_compact_buffer hcompact
    (fun x _ => hsrc x)
  have hfrontier := C.toOpenPartialHomeomorph.image_frontier_of_compact_buffer hgs hcompact
    (fun x _ => hsrc x)
  change IsOpen (C '' g.ball p r) at hCs
  change C '' closure (g.ball p r) = closure (C '' g.ball p r) at hclosure
  change C '' frontier (g.ball p r) = frontier (C '' g.ball p r) at hfrontier
  have hp : p ∈ g.ball p r := by
    change g.edist p p < ENNReal.ofReal r
    rw [M36.metric_edist_self]
    exact ENNReal.ofReal_pos.mpr hr
  have htarget : closure (C '' g.ball p r) ⊆ C.target := by
    rw [← hclosure]
    rintro _ ⟨x, _, rfl⟩
    exact C.map_source (hsrc x)
  apply Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : X → Type _) :=
      ⟨g.toRiemannianMetric⟩
    have hx' : Manifold.riemannianEDist (𝓡 3) p x < ENNReal.ofReal r := hx
    obtain ⟨γ, hγ0, hγ1, hγ, hlength⟩ := Manifold.exists_lt_of_riemannianEDist_lt hx'
    have hb := M36.edist_comp_le_pathELength_of_pullback_bound g h
      (U := univ) (fun y _ => C.contMDiffOn.contMDiffAt (C.open_source.mem_nhds (hsrc y)))
      (fun y _ v => (hmetric y v v).le) zero_le_one hγ (subset_univ _)
    rw [hγ0, hγ1] at hb
    exact hb.trans_lt hlength
  · apply h.ball_subset_of_inverse_length_barrier g C.symm hCs (mem_image_of_mem C hp)
    · intro y hy
      exact C.symm.contMDiffOn.contMDiffAt (C.open_target.mem_nhds (htarget hy))
    · intro y hy v
      exact (g.inverse_pullback_eq h C (fun x _ => hmetric x) (htarget hy) v v).le
    · intro y hy
      rw [← hfrontier] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      have hleft (z : X) : C.symm.toPartialEquiv (C.toPartialEquiv z) = z := C.left_inv (hsrc z)
      rw [hleft p, hleft x]
      have hnot : x ∉ g.ball p r := by simpa only [hgs.interior_eq] using hx.2
      exact le_of_not_gt hnot

theorem image_ball_of_precompact_pullback
    [RegularSpace X] [T2Space Y] [Nonempty X]
    (g : RiemannianMetric 3 X) (h : RiemannianMetric 3 Y) {f : X → Y}
    (hf : ContMDiff (𝓡 3) (𝓡 3) ∞ f) (hinj : Function.Injective f)
    (hmetric : ∀ x (v w : TangentSpace (𝓡 3) x),
      h.inner (f x) (mfderiv (𝓡 3) (𝓡 3) f x v)
        (mfderiv (𝓡 3) (𝓡 3) f x w) = g.inner x v w)
    (p : X) {r : ℝ} (hr : 0 < r) (hcompact : IsCompact (closure (g.ball p r))) :
    f '' g.ball p r = h.ball (f p) r := by
  have he := g.isOpenEmbedding_of_injective_pullback_eq h hf hinj hmetric
  let C : PartialDiffeomorph (𝓡 3) (𝓡 3) X Y ∞ := {
    toFun := f
    invFun := Function.invFun f
    source := univ
    target := range f
    map_source' := fun x _ => mem_range_self x
    map_target' := fun _ _ => mem_univ _
    left_inv' := fun x _ => Function.leftInverse_invFun hinj x
    right_inv' := fun _ hx => Function.invFun_eq hx
    open_source := isOpen_univ
    open_target := by simpa only [image_univ] using he.isOpenMap univ isOpen_univ
    contMDiffOn_toFun := hf.contMDiffOn
    contMDiffOn_invFun := g.contMDiffOn_invFun_of_injective_pullback_eq h hf hinj hmetric }
  exact g.image_ball_of_precompact_partialDiffeomorph h C rfl hmetric p hr hcompact

end PoincareConjecture.RiemannianMetric
