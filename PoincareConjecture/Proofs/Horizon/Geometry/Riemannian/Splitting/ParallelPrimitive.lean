import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.Primitive
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Connection.LocalRegularity
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Gradient









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter VectorField Bundle
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

private theorem smooth_constant_model_field
    (v p : EuclideanSpace ℝ (Fin n)) :
    ContMDiffAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞
      (fun y => TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) y
        (E := TangentSpace (𝓡 n)) v) p := by
  rw [contMDiffAt_totalSpace]
  exact ⟨contMDiffAt_id, by simpa using
    (contMDiffAt_const (I := 𝓡 n) (I' := 𝓡 n) (c := v))⟩

private theorem smooth_chart_constant_field
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {x : M} (hx : x ∈ e.source) (v : EuclideanSpace ℝ (Fin n)) :
    ContMDiffAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞
      (T% (mpullback (𝓡 n) (𝓡 n) e (fun _ => v))) x := by
  have hD : e.MDifferentiable (𝓡 n) (𝓡 n) :=
    ⟨he.mdifferentiableOn (by simp), hei.mdifferentiableOn (by simp)⟩
  exact (smooth_constant_model_field v (e x)).mpullback_vectorField_preimage
    (he.contMDiffAt (e.open_source.mem_nhds hx)) ⟨hD.mfderiv hx, rfl⟩ (by simp)

private theorem chart_constant_fields_commute
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    {x : M} (hx : x ∈ e.source) (v w : EuclideanSpace ℝ (Fin n)) :
    mlieBracket (𝓡 n)
      (mpullback (𝓡 n) (𝓡 n) e (fun _ => v))
      (mpullback (𝓡 n) (𝓡 n) e (fun _ => w)) x = 0 := by
  let : IsManifold (𝓡 n) (minSmoothness ℝ 2) M := by
    simpa only [minSmoothness_of_isRCLikeNormedField] using
      (inferInstance : IsManifold (𝓡 n) 2 M)
  have hb := mpullback_mlieBracket
    ((smooth_constant_model_field v (e x)).mdifferentiableAt (by simp))
    ((smooth_constant_model_field w (e x)).mdifferentiableAt (by simp))
    (he.contMDiffAt (e.open_source.mem_nhds hx))
    (by simp only [minSmoothness_of_isRCLikeNormedField]; norm_cast)
  rw [← hb]
  have hzero : mlieBracket (𝓡 n)
      (fun _ : EuclideanSpace ℝ (Fin n) => v) (fun _ => w) = 0 := by
    funext p
    simp only [mlieBracket, mlieBracketWithin_eq_lieBracketWithin,
      lieBracketWithin, fderivWithin_univ, fderiv_const_apply]
    simp +instances
  rw [hzero]
  simp [mpullback]


def chartMetricDual (g : RiemannianMetric n M)
    (V : (x : M) → TangentSpace (𝓡 n) x)
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (z : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
  (g.inner (e.symm z) (V (e.symm z))).comp
    (mfderiv (𝓡 n) (𝓡 n) e (e.symm z)).inverse

private theorem chartMetricDual_apply
    (g : RiemannianMetric n M) (V : (x : M) → TangentSpace (𝓡 n) x)
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (z v : EuclideanSpace ℝ (Fin n)) :
    chartMetricDual g V e z v =
      g.inner (e.symm z) (V (e.symm z))
        (mpullback (𝓡 n) (𝓡 n) e (fun _ => v) (e.symm z)) := rfl


theorem contDiffOn_chartMetricDual
    (g : RiemannianMetric n M) {V : (x : M) → TangentSpace (𝓡 n) x}
    (hV : ContMDiff (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% V))
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target) :
    ContDiffOn ℝ ∞ (chartMetricDual g V e) e.target := by
  rw [contDiffOn_clm_apply]
  intro v z hz
  have hX := smooth_chart_constant_field e he hei (e.map_target hz) v
  have hi := ((g.contMDiff (e.symm z)).clm_bundle_apply (hV _)).clm_bundle_apply hX
  have hscalar := (contMDiffAt_totalSpace.mp hi).2
  have h := hscalar.comp z (hei.contMDiffAt (e.open_target.mem_nhds hz))
  exact (contMDiffAt_iff_contDiffAt.mp h).contDiffWithinAt

omit [IsManifold (𝓡 n) ∞ M] in
private theorem fderiv_chart_composition
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {z : EuclideanSpace ℝ (Fin n)} (hz : z ∈ e.target) {f : M → ℝ}
    (hf : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) f (e.symm z))
    (v : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (f ∘ e.symm) z v =
      mvfderiv (𝓡 n) f (e.symm z)
        (mpullback (𝓡 n) (𝓡 n) e (fun _ => v) (e.symm z)) := by
  have hD : e.MDifferentiable (𝓡 n) (𝓡 n) :=
    ⟨he.mdifferentiableOn (by simp), hei.mdifferentiableOn (by simp)⟩
  have hinv : (mfderiv (𝓡 n) (𝓡 n) e (e.symm z)).IsInvertible :=
    ⟨hD.mfderiv (e.map_target hz), rfl⟩
  have hfield : mpullback (𝓡 n) (𝓡 n) e (fun _ => v) (e.symm z) =
      mfderiv (𝓡 n) (𝓡 n) e.symm z v := by
    apply hD.mfderiv_injective (e.map_target hz)
    simp only [mpullback, hinv.self_apply_inverse]
    exact (congrArg (fun L => L v) (hD.comp_symm_deriv hz)).symm
  rw [hfield]
  have h := congrArg (fun L => L v) (mvfderiv_comp z hf
    ((hei.contMDiffAt (e.open_target.mem_nhds hz)).mdifferentiableAt (by simp)))
  simp only [mvfderiv, mfderiv_eq_fderiv, ContinuousLinearMap.comp_apply] at h
  exact h



theorem fderiv_chartMetricDual_symmetric (D : LeviCivitaData g)
    {V : (x : M) → TangentSpace (𝓡 n) x}
    (hV : ContMDiff (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% V))
    (hparallel : ∀ (x : M) (u : TangentSpace (𝓡 n) x), D.connection V x u = 0)
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {z : EuclideanSpace ℝ (Fin n)} (hz : z ∈ e.target)
    (u v : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (chartMetricDual g V e) z u v =
      fderiv ℝ (chartMetricDual g V e) z v u := by
  let X := fun w : EuclideanSpace ℝ (Fin n) => mpullback (𝓡 n) (𝓡 n) e (fun _ => w)
  have hX (w) := (smooth_chart_constant_field e he hei (e.map_target hz) w).mdifferentiableAt
    (by simp)
  have hα := ((contDiffOn_chartMetricDual g hV e he hei).contDiffAt
    (e.open_target.mem_nhds hz)).differentiableAt (by simp)
  have hderiv (a b : EuclideanSpace ℝ (Fin n)) :
      fderiv ℝ (chartMetricDual g V e) z a b =
        g.inner (e.symm z) (V (e.symm z)) (D.connection (X b) (e.symm z) (X a (e.symm z))) := by
    have hinner := ((g.contMDiff (e.symm z)).clm_bundle_apply (hV _)).clm_bundle_apply
      (smooth_chart_constant_field e he hei (e.map_target hz) b)
    have hs : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞
        (fun x => g.inner x (V x) (X b x)) (e.symm z) := by
      simpa [X] using (contMDiffAt_totalSpace.mp hinner).2
    have hd := fderiv_chart_composition e he hei hz
      (hs.mdifferentiableAt (by simp)) a
    have hpair := D.horizon_mvfderiv_inner (X a) ((hV _).mdifferentiableAt (by simp)) (hX b)
    have heval := (hα.hasFDerivAt.clm_apply (hasFDerivAt_const b z)).fderiv
    have ha := congrArg (fun L => L a) heval
    simp only [add_apply, ContinuousLinearMap.comp_apply,
      zero_apply, map_zero, zero_add, ContinuousLinearMap.flip_apply] at ha
    rw [← ha]
    change fderiv ℝ ((fun x => g.inner x (V x) (X b x)) ∘ e.symm) z a = _
    rw [hd, hpair]
    simp [hparallel, covariantDerivativeOnFields, X]
  rw [hderiv, hderiv]
  have ht := D.connection.torsion_eq_zero_iff.mp D.torsion_eq_zero (hX u) (hX v)
  rw [chart_constant_fields_commute e he (e.map_target hz) u v] at ht
  exact congrArg (g.inner (e.symm z) (V (e.symm z))) (sub_eq_zero.mp ht)




theorem exists_local_potential_of_parallel (D : LeviCivitaData g)
    {V : (x : M) → TangentSpace (𝓡 n) x}
    (hV : ContMDiff (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% V))
    (hparallel : ∀ (x : M) (u : TangentSpace (𝓡 n) x), D.connection V x u = 0)
    (p : M) (c : ℝ) :
    ∃ (U : Set M) (f : M → ℝ), IsOpen U ∧ p ∈ U ∧
      ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ f U ∧ f p = c ∧
      ∀ x ∈ U, mvfderiv (𝓡 n) f x = g.inner x (V x) := by
  let E := EuclideanSpace ℝ (Fin n)
  let e : OpenPartialHomeomorph M E := chartAt E p
  have he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source := by
    simpa [e, E, extChartAt, OpenPartialHomeomorph.extend_coe,
      OpenPartialHomeomorph.extend_source] using
      (contMDiffOn_extChartAt (I := 𝓡 n) (n := ∞) (x := p))
  have hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target := by
    simpa [e, E, extChartAt, OpenPartialHomeomorph.extend_coe_symm,
      OpenPartialHomeomorph.extend_target, modelWithCornersSelf_coe_symm] using
      (contMDiffOn_extChartAt_symm (I := 𝓡 n) (n := ∞) p)
  have hp : p ∈ e.source := mem_chart_source E p
  obtain ⟨r, φ, hr, hrsub, hφ, hφp, hdφ⟩ :=
    Poincare.Analysis.exists_local_primitive_of_fderiv_symmetric e.open_target
      (contDiffOn_chartMetricDual g hV e he hei)
      (fun z hz u v => D.fderiv_chartMetricDual_symmetric hV hparallel e he hei hz u v)
      (e.map_source hp) c
  refine ⟨e.source ∩ e ⁻¹' Metric.ball (e p) r, φ ∘ e,
    e.isOpen_inter_preimage Metric.isOpen_ball, ⟨hp, Metric.mem_ball_self hr⟩, ?_, hφp, ?_⟩
  · intro x hx
    exact ((contMDiffAt_iff_contDiffAt.mpr hφ.contDiffAt).comp x
      (he.contMDiffAt (e.open_source.mem_nhds hx.1))).contMDiffWithinAt
  · intro x hx
    have hD : e.MDifferentiable (𝓡 n) (𝓡 n) :=
      ⟨he.mdifferentiableOn (by simp), hei.mdifferentiableOn (by simp)⟩
    have hinv : (mfderiv (𝓡 n) (𝓡 n) e x).IsInvertible := ⟨hD.mfderiv hx.1, rfl⟩
    ext u
    have hcomp := mvfderiv_comp_apply x
      ((hφ.differentiable (by simp)) (e x)).mdifferentiableAt
      (hD.1 x hx.1 |>.mdifferentiableAt (e.open_source.mem_nhds hx.1)) u
    rw [hcomp]
    have hreal (z v : E) : mvfderiv (𝓡 n) φ z v = fderiv ℝ φ z v := by
      simp only [mvfderiv, mfderiv_eq_fderiv, ContinuousLinearMap.comp_apply,
        NormedSpace.fromTangentSpace]
      rfl
    rw [hreal]
    rw [(hdφ (e x) hx.2).fderiv]
    rw [chartMetricDual_apply]
    erw [mpullback, e.left_inv hx.1, hinv.inverse_apply_self]

end PoincareConjecture.LeviCivitaData
