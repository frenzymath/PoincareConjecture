import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_InitialPhaseBounds
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.SmoothExtension










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin n)




theorem pullbackCoefficients_eq_of_comp_germ (g : RiemannianMetric n M)
    {a e : E → M} {f : E → E} {x : E}
    (he : MDifferentiableAt (𝓡 n) (𝓡 n) e (f x))
    (hf : DifferentiableAt ℝ f x) (hcomp : e ∘ f =ᶠ[𝓝 x] a) (v w : E) :
    g.pullbackCoefficients a x v w =
      g.pullbackCoefficients e (f x) (fderiv ℝ f x v) (fderiv ℝ f x w) := by
  have hd := mfderiv_comp x he hf.mdifferentiableAt
  rw [hcomp.mfderiv_eq, mfderiv_eq_fderiv] at hd
  have hv := congrArg (fun D => D v) hd
  have hw := congrArg (fun D => D w) hd
  change g.inner (a x) (mfderiv (𝓡 n) (𝓡 n) a x v) (mfderiv (𝓡 n) (𝓡 n) a x w) =
    g.inner (e (f x))
      (mfderiv (𝓡 n) (𝓡 n) e (f x) (fderiv ℝ f x v))
      (mfderiv (𝓡 n) (𝓡 n) e (f x) (fderiv ℝ f x w))
  simp only [TangentSpace] at hv hw ⊢
  rw [hv, hw]
  exact congrArg (fun y : M => g.inner y
    (mfderiv (𝓡 n) (𝓡 n) e (f x) (fderiv ℝ f x v))
    (mfderiv (𝓡 n) (𝓡 n) e (f x) (fderiv ℝ f x w))) hcomp.self_of_nhds.symm

private theorem partialCoordinateChange_smooth
    (e : PartialDiffeomorph (𝓡 n) (𝓡 n) E M ∞) (p : M)
    {x : E} (hx : x ∈ (extChartAt (𝓡 n) p).target)
    (hxe : (extChartAt (𝓡 n) p).symm x ∈ e.target) :
    ContDiffAt ℝ ∞ (fun y => e.symm ((extChartAt (𝓡 n) p).symm y)) x := by
  apply contMDiffAt_iff_contDiffAt.mp
  exact (e.symm.contMDiffOn.contMDiffAt (e.open_target.mem_nhds hxe)).comp x
    ((contMDiffOn_extChartAt_symm p).contMDiffAt
      ((isOpen_extChartAt_target (I := 𝓡 n) p).mem_nhds hx))

private theorem partialCoordinateChange_metric
    (g : RiemannianMetric n M)
    (e : PartialDiffeomorph (𝓡 n) (𝓡 n) E M ∞) (p : M)
    {x : E} (hx : x ∈ (extChartAt (𝓡 n) p).target)
    (hxe : (extChartAt (𝓡 n) p).symm x ∈ e.target) (v w : E) :
    g.pullbackCoefficients (extChartAt (𝓡 n) p).symm x v w =
      g.pullbackCoefficients e (e.symm ((extChartAt (𝓡 n) p).symm x))
        (fderiv ℝ (fun y => e.symm ((extChartAt (𝓡 n) p).symm y)) x v)
        (fderiv ℝ (fun y => e.symm ((extChartAt (𝓡 n) p).symm y)) x w) := by
  have hc := (contMDiffOn_extChartAt_symm (I := 𝓡 n) (n := ∞) p).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓡 n) p).mem_nhds hx)
  have he := e.contMDiffOn.contMDiffAt (e.open_source.mem_nhds (e.map_target hxe))
  apply g.pullbackCoefficients_eq_of_comp_germ (he.mdifferentiableAt (by simp))
    ((partialCoordinateChange_smooth e p hx hxe).differentiableAt (by simp))
  filter_upwards [hc.continuousAt.preimage_mem_nhds (e.open_target.mem_nhds hxe)] with y hy
  exact e.right_inv hy




theorem hasDerivAt_geodesic_in_partialDiffeomorph
    (g : RiemannianMetric n M)
    (e : PartialDiffeomorph (𝓡 n) (𝓡 n) E M ∞) (p : M)
    {q w : ℝ → E} {t : ℝ}
    (hqt : q t ∈ (extChartAt (𝓡 n) p).target)
    (hqe : (extChartAt (𝓡 n) p).symm (q t) ∈ e.target)
    (hq : HasDerivAt q (w t) t)
    (hw : HasDerivAt w
      (-coordinateChristoffel (g.pullbackCoefficients (extChartAt (𝓡 n) p).symm)
        (q t) (w t) (w t)) t) :
    let f := fun y => e.symm ((extChartAt (𝓡 n) p).symm y)
    HasDerivAt (fun s => f (q s)) (fderiv ℝ f (q t) (w t)) t ∧
      HasDerivAt (fun s => fderiv ℝ f (q s) (w s))
        (-coordinateChristoffel (g.pullbackCoefficients e) (f (q t))
          (fderiv ℝ f (q t) (w t)) (fderiv ℝ f (q t) (w t))) t := by
  let f := fun y => e.symm ((extChartAt (𝓡 n) p).symm y)
  have hc := (contMDiffOn_extChartAt_symm (I := 𝓡 n) (n := ∞) p).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓡 n) p).mem_nhds hqt)
  have he := e.contMDiffOn.contMDiffAt (e.open_source.mem_nhds (e.map_target hqe))
  have hmetric : ∀ᶠ y in 𝓝 (q t), ∀ v w,
      g.pullbackCoefficients (extChartAt (𝓡 n) p).symm y v w =
        g.pullbackCoefficients e (f y) (fderiv ℝ f y v) (fderiv ℝ f y w) := by
    filter_upwards [(isOpen_extChartAt_target (I := 𝓡 n) p).mem_nhds hqt,
      hc.continuousAt.preimage_mem_nhds (e.open_target.mem_nhds hqe)] with y hy hye v w
    exact partialCoordinateChange_metric g e p hy hye v w
  have hBinv := g.isInvertible_chartCoefficients p hqt
  have heD : e.toOpenPartialHomeomorph.MDifferentiable (𝓡 n) (𝓡 n) :=
    ⟨e.mdifferentiableOn (by simp), e.symm.mdifferentiableOn (by simp)⟩
  have hCinv := g.isInvertible_pullbackCoefficients (heD.mfderiv_injective (e.map_target hqe))
  have hsurj : Function.Surjective (fderiv ℝ f (q t)) := by
    apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp
    intro v w hvw
    apply hBinv.injective
    ext z
    change fderiv ℝ f (q t) v = fderiv ℝ f (q t) w at hvw
    rw [hmetric.self_of_nhds v z, hmetric.self_of_nhds w z, hvw]
  exact hasDerivAt_geodesic_change_coordinates
    ((g.contDiffAt_pullbackCoefficients hc).differentiableAt (by simp))
    ((g.contDiffAt_pullbackCoefficients he).differentiableAt (by simp)) hBinv hCinv
    (fun v w => g.symm _ _ _) (partialCoordinateChange_smooth e p hqt hqe)
    hsurj hmetric hq hw




theorem IsGeodesicOn.hasDerivAt_phase_in_partialDiffeomorph
    {g : RiemannianMetric n M} {γ : ℝ → M} {S : Set ℝ}
    (hγ : g.IsGeodesicOn γ S)
    (e : PartialDiffeomorph (𝓡 n) (𝓡 n) E M ∞) {t : ℝ} (ht : t ∈ S)
    (he : γ t ∈ e.target) :
    HasDerivAt (fun s => (e.symm (γ s), deriv (fun u => e.symm (γ u)) s))
      (coordinateGeodesicField (g.pullbackCoefficients e)
        (e.symm (γ t), deriv (fun u => e.symm (γ u)) t)) t := by
  let p := γ t
  let c := extChartAt (𝓡 n) p
  let q := fun u => c (γ u)
  let f := fun y => e.symm (c.symm y)
  let W := fun u => fderiv ℝ f (q u) (deriv q u)
  obtain ⟨J, hJ, htJ, hgeo⟩ := hγ.exists_open_nhds ht
  have hsource : γ t ∈ c.source := mem_extChartAt_source p
  have hsrc : ∀ᶠ u in 𝓝 t, γ u ∈ c.source :=
    (hγ.contMDiffAt ht).continuousAt.preimage_mem_nhds
      ((isOpen_extChartAt_source p).mem_nhds hsource)
  have htarget : ∀ᶠ u in 𝓝 t, γ u ∈ e.target :=
    (hγ.contMDiffAt ht).continuousAt.preimage_mem_nhds (e.open_target.mem_nhds he)
  have heq : (fun u => f (q u)) =ᶠ[𝓝 t] (fun u => e.symm (γ u)) := by
    filter_upwards [hsrc] with u hu
    exact congrArg e.symm (c.left_inv hu)
  have hchange {u : ℝ} (huJ : u ∈ J) (hus : γ u ∈ c.source) (hue : γ u ∈ e.target) :
      HasDerivAt (fun s => f (q s)) (W u) u ∧
        HasDerivAt W (-coordinateChristoffel (g.pullbackCoefficients e)
          (f (q u)) (W u) (W u)) u := by
    have hcoord := hgeo.hasDerivAt_chart_at huJ p hus
    exact g.hasDerivAt_geodesic_in_partialDiffeomorph e p (c.map_source hus)
      (by
        change c.symm (q u) ∈ e.target
        simpa only [q, c.left_inv hus] using hue) hcoord.1 hcoord.2
  have hvel : deriv (fun u => e.symm (γ u)) =ᶠ[𝓝 t] W := by
    filter_upwards [hJ.mem_nhds htJ, hsrc, htarget, heq.deriv] with u huJ hus hue hdu
    exact hdu.symm.trans (hchange huJ hus hue).1.deriv
  obtain ⟨hp, hv⟩ := hchange htJ hsource he
  have hpos : HasDerivAt (fun u => e.symm (γ u))
      (deriv (fun u => e.symm (γ u)) t) t := by
    rw [hvel.self_of_nhds]
    exact hp.congr_of_eventuallyEq heq.symm
  have hacc : HasDerivAt (deriv (fun u => e.symm (γ u)))
      (-coordinateChristoffel (g.pullbackCoefficients e) (e.symm (γ t))
        (deriv (fun u => e.symm (γ u)) t) (deriv (fun u => e.symm (γ u)) t)) t := by
    have hpoint : f (q t) = e.symm (γ t) := heq.self_of_nhds
    rw [hvel.self_of_nhds, ← hpoint]
    exact hv.congr_of_eventuallyEq hvel
  exact hpos.prodMk hacc

end PoincareConjecture.RiemannianMetric

namespace PoincareConjecture.SurgeryCapClose

universe u




theorem hasDerivAt_normalized_geodesic_phase
    {g₀ : StandardInitialMetric} {S : GeneralizedSliceCarrier.{u}}
    {g : RiemannianMetric 3 S.carrier} {tip : S.carrier} {scale eta : ℝ}
    (Q : SurgeryCapClose g₀ S g tip scale eta) {γ : ℝ → S.carrier} {I : Set ℝ}
    (hγ : (m01RescaledMetric g (scale⁻¹ ^ 2)
      (sq_pos_of_pos (inv_pos.mpr Q.scale_pos))).IsGeodesicOn γ I)
    {t : ℝ} (ht : t ∈ I) (hchart : γ t ∈ Q.map '' g₀.metric.ball 0 eta⁻¹) :
    HasDerivAt (fun s => (Q.inverse (γ s), deriv (fun u => Q.inverse (γ u)) s))
      (coordinateGeodesicField Q.normalizedCoefficients
        (Q.inverse (γ t), deriv (fun u => Q.inverse (γ u)) t)) t :=
  hγ.hasDerivAt_phase_in_partialDiffeomorph Q.toPartialDiffeomorph ht hchart

end PoincareConjecture.SurgeryCapClose
