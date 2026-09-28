import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Continuation.ChangeCoordinates
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Exponential.Uniqueness







noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped ContDiff Manifold Bundle Topology

namespace PoincareConjecture.RiemannianMetric

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 n) ∞ N]
  {g : RiemannianMetric n M} {h : RiemannianMetric n N}
  {f : M → N} {U : Set M}

private theorem contDiffAt_isometry_chart_map
    (hU : IsOpen U) (hf : ContMDiffOn (𝓡 n) (𝓡 n) ∞ f U)
    (p : M) (r : N) {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ (extChartAt (𝓡 n) p).target)
    (hxU : (extChartAt (𝓡 n) p).symm x ∈ U)
    (hr : f ((extChartAt (𝓡 n) p).symm x) ∈ (extChartAt (𝓡 n) r).source) :
    ContDiffAt ℝ ∞ (fun y => extChartAt (𝓡 n) r
      (f ((extChartAt (𝓡 n) p).symm y))) x := by
  apply contMDiffAt_iff_contDiffAt.mp
  exact (contMDiffAt_extChartAt' (by simpa only [extChartAt_source] using hr)).comp x
    (((hf _ hxU).contMDiffAt (hU.mem_nhds hxU)).comp x
      ((contMDiffOn_extChartAt_symm p).contMDiffAt
        ((isOpen_extChartAt_target (I := 𝓡 n) p).mem_nhds hx)))

private theorem isometry_chart_coefficients
    (hU : IsOpen U) (hf : ContMDiffOn (𝓡 n) (𝓡 n) ∞ f U)
    (hmetric : ∀ y ∈ U, ∀ a b : TangentSpace (𝓡 n) y,
      g.inner y a b = h.inner (f y) (mfderiv (𝓡 n) (𝓡 n) f y a)
        (mfderiv (𝓡 n) (𝓡 n) f y b))
    (p : M) (r : N) {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ (extChartAt (𝓡 n) p).target)
    (hxU : (extChartAt (𝓡 n) p).symm x ∈ U)
    (hr : f ((extChartAt (𝓡 n) p).symm x) ∈ (extChartAt (𝓡 n) r).source)
    (u v : EuclideanSpace ℝ (Fin n)) :
    let F := fun y => extChartAt (𝓡 n) r (f ((extChartAt (𝓡 n) p).symm y))
    g.pullbackCoefficients (extChartAt (𝓡 n) p).symm x u v =
      h.pullbackCoefficients (extChartAt (𝓡 n) r).symm (F x)
        (fderiv ℝ F x u) (fderiv ℝ F x v) := by
  let c := extChartAt (𝓡 n) p
  let d := extChartAt (𝓡 n) r
  let F := fun y => d (f (c.symm y))
  have hc := (contMDiffOn_extChartAt_symm (I := 𝓡 n) (n := ∞) p).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓡 n) p).mem_nhds hx)
  have hfx := (hf _ hxU).contMDiffAt (hU.mem_nhds hxU)
  have hF := contDiffAt_isometry_chart_map hU hf p r hx hxU hr
  have hd := (contMDiffOn_extChartAt_symm (I := 𝓡 n) (n := ∞) r).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓡 n) r).mem_nhds (d.map_source hr))
  have heq : (d.symm ∘ F) =ᶠ[𝓝 x] (f ∘ c.symm) := by
    filter_upwards [(hfx.continuousAt.comp hc.continuousAt).preimage_mem_nhds
      ((isOpen_extChartAt_source r).mem_nhds hr)] with y hy
    exact d.left_inv hy
  have hderiv := mfderiv_comp x (hd.mdifferentiableAt (by simp))
    (hF.differentiableAt (by simp)).mdifferentiableAt
  rw [heq.mfderiv_eq,
    mfderiv_comp x (hfx.mdifferentiableAt (by simp)) (hc.mdifferentiableAt (by simp)),
    mfderiv_eq_fderiv] at hderiv
  have he (a : EuclideanSpace ℝ (Fin n)) :
      mfderiv (𝓡 n) (𝓡 n) f (c.symm x) (mfderiv (𝓡 n) (𝓡 n) c.symm x a) =
        mfderiv (𝓡 n) (𝓡 n) d.symm (F x) (fderiv ℝ F x a) :=
    congrArg (fun L => L a) hderiv
  change g.inner (c.symm x) (mfderiv (𝓡 n) (𝓡 n) c.symm x u)
      (mfderiv (𝓡 n) (𝓡 n) c.symm x v) =
    h.inner (d.symm (F x)) (mfderiv (𝓡 n) (𝓡 n) d.symm (F x) (fderiv ℝ F x u))
      (mfderiv (𝓡 n) (𝓡 n) d.symm (F x) (fderiv ℝ F x v))
  rw [hmetric _ hxU, he, he]
  have hpoint : d.symm (F x) = f (c.symm x) := heq.self_of_nhds
  exact congrArg (fun a : N => h.inner a
    (mfderiv (𝓡 n) (𝓡 n) d.symm (F x) (fderiv ℝ F x u))
    (mfderiv (𝓡 n) (𝓡 n) d.symm (F x) (fderiv ℝ F x v))) hpoint.symm

private theorem hasDerivAt_geodesic_isometry_in_charts
    (hU : IsOpen U) (hf : ContMDiffOn (𝓡 n) (𝓡 n) ∞ f U)
    (hmetric : ∀ y ∈ U, ∀ a b : TangentSpace (𝓡 n) y,
      g.inner y a b = h.inner (f y) (mfderiv (𝓡 n) (𝓡 n) f y a)
        (mfderiv (𝓡 n) (𝓡 n) f y b))
    (p : M) (r : N) {q w : ℝ → EuclideanSpace ℝ (Fin n)} {t : ℝ}
    (htp : q t ∈ (extChartAt (𝓡 n) p).target)
    (htU : (extChartAt (𝓡 n) p).symm (q t) ∈ U)
    (htr : f ((extChartAt (𝓡 n) p).symm (q t)) ∈ (extChartAt (𝓡 n) r).source)
    (hq : HasDerivAt q (w t) t)
    (hw : HasDerivAt w
      (-coordinateChristoffel (g.pullbackCoefficients (extChartAt (𝓡 n) p).symm)
        (q t) (w t) (w t)) t) :
    let F := fun y => extChartAt (𝓡 n) r (f ((extChartAt (𝓡 n) p).symm y))
    HasDerivAt (fun s => F (q s)) (fderiv ℝ F (q t) (w t)) t ∧
      HasDerivAt (fun s => fderiv ℝ F (q s) (w s))
        (-coordinateChristoffel (h.pullbackCoefficients (extChartAt (𝓡 n) r).symm)
          (F (q t)) (fderiv ℝ F (q t) (w t)) (fderiv ℝ F (q t) (w t))) t := by
  let F := fun y => extChartAt (𝓡 n) r (f ((extChartAt (𝓡 n) p).symm y))
  have hp := (contMDiffOn_extChartAt_symm (I := 𝓡 n) (n := ∞) p).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓡 n) p).mem_nhds htp)
  have hfp := (hf _ htU).contMDiffAt (hU.mem_nhds htU)
  have hm : ∀ᶠ y in 𝓝 (q t), ∀ u v,
      g.pullbackCoefficients (extChartAt (𝓡 n) p).symm y u v =
        h.pullbackCoefficients (extChartAt (𝓡 n) r).symm (F y)
          (fderiv ℝ F y u) (fderiv ℝ F y v) := by
    filter_upwards [(isOpen_extChartAt_target (I := 𝓡 n) p).mem_nhds htp,
      hp.continuousAt.preimage_mem_nhds (hU.mem_nhds htU),
      (hfp.continuousAt.comp hp.continuousAt).preimage_mem_nhds
        ((isOpen_extChartAt_source r).mem_nhds htr)] with y hyp hyU hyr u v
    exact isometry_chart_coefficients hU hf hmetric p r hyp hyU hyr u v
  have hinv := g.isInvertible_chartCoefficients p htp
  have hsurj : Function.Surjective (fderiv ℝ F (q t)) := by
    apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp
    intro u v huv
    apply hinv.injective
    ext z
    change fderiv ℝ F (q t) u = fderiv ℝ F (q t) v at huv
    rw [hm.self_of_nhds u z, hm.self_of_nhds v z, huv]
  have hrTarget := (extChartAt (𝓡 n) r).map_source htr
  exact hasDerivAt_geodesic_change_coordinates
    (B := g.pullbackCoefficients (extChartAt (𝓡 n) p).symm)
    (C := h.pullbackCoefficients (extChartAt (𝓡 n) r).symm)
    (f := F) (q := q) (w := w) (t := t)
    (((g.contDiffOn_chartCoefficients p _ htp).contDiffAt
      ((isOpen_extChartAt_target (I := 𝓡 n) p).mem_nhds htp)).differentiableAt (by simp))
    (((h.contDiffOn_chartCoefficients r _ hrTarget).contDiffAt
      ((isOpen_extChartAt_target (I := 𝓡 n) r).mem_nhds hrTarget)).differentiableAt (by simp))
    hinv (h.isInvertible_chartCoefficients r hrTarget) (fun u v => h.symm _ _ _)
    (contDiffAt_isometry_chart_map hU hf p r htp htU htr) hsurj hm hq hw



theorem IsGeodesicOn.comp_local_isometry_manifold
    (hU : IsOpen U) (hf : ContMDiffOn (𝓡 n) (𝓡 n) ∞ f U)
    (hmetric : ∀ y ∈ U, ∀ a b : TangentSpace (𝓡 n) y,
      g.inner y a b = h.inner (f y) (mfderiv (𝓡 n) (𝓡 n) f y a)
        (mfderiv (𝓡 n) (𝓡 n) f y b))
    {γ : ℝ → M} {I : Set ℝ} (hγ : g.IsGeodesicOn γ I)
    (hγU : MapsTo γ I U) : h.IsGeodesicOn (f ∘ γ) I := by
  intro t ht
  obtain ⟨p, q, w, hlocal⟩ := hγ t ht
  let r := f (γ t)
  let F := fun y => extChartAt (𝓡 n) r (f ((extChartAt (𝓡 n) p).symm y))
  have hγcont := (hγ.contMDiffAt ht).continuousAt
  have hft := (hf _ (hγU ht)).contMDiffAt (hU.mem_nhds (hγU ht))
  have hdomain : ∀ᶠ s in 𝓝 t, γ s ∈ U :=
    hγcont.preimage_mem_nhds (hU.mem_nhds (hγU ht))
  have htarget : ∀ᶠ s in 𝓝 t, f (γ s) ∈ (extChartAt (𝓡 n) r).source :=
    (hft.continuousAt.comp hγcont).preimage_mem_nhds
      ((isOpen_extChartAt_source r).mem_nhds (mem_extChartAt_source r))
  refine ⟨r, (fun s => F (q s)), (fun s => fderiv ℝ F (q s) (w s)), ?_⟩
  filter_upwards [hlocal, hdomain, htarget] with s hs hsU hsr
  have hsU' : (extChartAt (𝓡 n) p).symm (q s) ∈ U := hs.1 ▸ hsU
  have hsr' : f ((extChartAt (𝓡 n) p).symm (q s)) ∈ (extChartAt (𝓡 n) r).source :=
    hs.1 ▸ hsr
  refine ⟨?_, (extChartAt (𝓡 n) r).map_source hsr', ?_⟩
  · change f (γ s) = (extChartAt (𝓡 n) r).symm
      (extChartAt (𝓡 n) r (f ((extChartAt (𝓡 n) p).symm (q s))))
    rw [hs.1, (extChartAt (𝓡 n) r).left_inv hsr']
  · exact hasDerivAt_geodesic_isometry_in_charts hU hf hmetric p r
      hs.2.1 hsU' hsr' hs.2.2.1 hs.2.2.2

end PoincareConjecture.RiemannianMetric
