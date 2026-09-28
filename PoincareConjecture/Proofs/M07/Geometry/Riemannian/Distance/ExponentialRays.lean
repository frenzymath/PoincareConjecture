import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.RadialCurve
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.Gauss.Manifold










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]



theorem geodesic_of_coordinate_exponential
    (g : RiemannianMetric n M) (p : M)
    (z : ℝ → EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))
    (v : EuclideanSpace ℝ (Fin n))
    (h0 : z 0 = (extChartAt (𝓡 n) p p, v))
    (hz : ∀ t ∈ Ioo (-2 : ℝ) 2,
      (z t).1 ∈ (extChartAt (𝓡 n) p).target ∧
      HasDerivAt z
        (coordinateGeodesicField (g.pullbackCoefficients
          (extChartAt (𝓡 n) p).symm) (z t)) t) :
    let γ := fun t => (extChartAt (𝓡 n) p).symm (z t).1
    g.IsGeodesicOn γ (Ioo (-2 : ℝ) 2) ∧ γ 0 = p ∧
      HasDerivAt (fun t => extChartAt (𝓡 n) p (γ t)) v 0 := by
  dsimp only
  refine ⟨g.isGeodesicOn_chart_curve p isOpen_Ioo (fun t ht =>
    ⟨(hz t ht).1, (hz t ht).2.fst, (hz t ht).2.snd⟩), ?_, ?_⟩
  · rw [h0]
    exact (extChartAt (𝓡 n) p).left_inv (mem_extChartAt_source p)
  · have heq : (fun t => extChartAt (𝓡 n) p
        ((extChartAt (𝓡 n) p).symm (z t).1)) =ᶠ[𝓝 0] fun t => (z t).1 := by
      filter_upwards [Ioo_mem_nhds (by norm_num : (-2 : ℝ) < 0)
        (by norm_num : (0 : ℝ) < 2)] with t ht
      exact (extChartAt (𝓡 n) p).right_inv (hz t ht).1
    have hd : HasDerivAt (fun t => (z t).1) (z 0).2 0 :=
      (hz 0 (by norm_num)).2.fst
    have hd' : HasDerivAt (fun t => (z t).1) v 0 := by
      simpa only [coordinateGeodesicField, h0] using hd
    exact hd'.congr_of_eventuallyEq heq


theorem IsGeodesicOn.comp_add {g : RiemannianMetric n M}
    {γ : ℝ → M} {s : Set ℝ} (hγ : g.IsGeodesicOn γ s) (a : ℝ) :
    g.IsGeodesicOn (fun t => γ (t + a)) ((fun t => t + a) ⁻¹' s) := by
  intro t ht
  obtain ⟨p, q, w, hlocal⟩ := hγ (t + a) ht
  refine ⟨p, fun u => q (u + a), fun u => w (u + a), ?_⟩
  have hcont : ContinuousAt (fun u : ℝ => u + a) t := by fun_prop
  filter_upwards [hcont.preimage_mem_nhds hlocal] with u hu
  refine ⟨hu.1, hu.2.1, ?_, ?_⟩
  · simpa only [Function.comp_def, one_smul, id_eq] using!
      hu.2.2.1.scomp u ((hasDerivAt_id u).add_const a)
  · simpa only [Function.comp_def, one_smul, id_eq] using!
      hu.2.2.2.scomp u ((hasDerivAt_id u).add_const a)


theorem IsGeodesicOn.comp_affine {g : RiemannianMetric n M}
    {γ : ℝ → M} {s : Set ℝ} (hγ : g.IsGeodesicOn γ s) (a b : ℝ) :
    g.IsGeodesicOn (fun t => γ (a * t + b)) ((fun t => a * t + b) ⁻¹' s) :=
  (hγ.comp_add b).comp_mul a



theorem exponential_eq_geodesic_of_unit_initial_data [T2Space M]
    {g : RiemannianMetric n M} (p : M)
    {V : Set (EuclideanSpace ℝ (Fin n))} (e : EuclideanSpace ℝ (Fin n) → M)
    (hexp : ∀ v ∈ V, ∃ η : ℝ → M,
      g.IsGeodesicOn η (Icc (0 : ℝ) 1) ∧ η 0 = p ∧
      HasDerivAt (fun t => extChartAt (𝓡 n) p (η t)) v 0 ∧ η 1 = e v)
    {γ : ℝ → M} (hγ : g.IsGeodesicOn γ (Icc (0 : ℝ) 1)) (hγ0 : γ 0 = p)
    {v : EuclideanSpace ℝ (Fin n)}
    (hγv : HasDerivAt (fun t => extChartAt (𝓡 n) p (γ t)) v 0)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (htv : t • v ∈ V) :
    e (t • v) = γ t := by
  obtain ⟨η, hη, hη0, hηv, hη1⟩ := hexp (t • v) htv
  have hscale : g.IsGeodesicOn (fun u => γ (t * u)) (Icc (0 : ℝ) 1) := by
    intro u hu
    exact hγ.comp_mul t u ⟨mul_nonneg ht.1 hu.1,
      (mul_le_mul_of_nonneg_left hu.2 ht.1).trans (by simpa using ht.2)⟩
  have hd : HasDerivAt (fun u => extChartAt (𝓡 n) p (γ (t * u))) (t • v) 0 := by
    have hv' : HasDerivAt (fun u => extChartAt (𝓡 n) p (γ u)) v (t * 0) := by
      simpa only [mul_zero] using hγv
    simpa only [Function.comp_def, id_eq, mul_one] using!
      hv'.scomp 0 ((hasDerivAt_id (0 : ℝ)).const_mul t)
  have heq := hscale.eq_nhds_on_of_initial_data hη (convex_Icc _ _).isPreconnected
    (t₀ := 0) (by simp) p
    (by simpa only [mul_zero, hγ0] using mem_extChartAt_source p)
    (by simpa only [mul_zero, hγ0] using hη0.symm)
    (hd.deriv.trans hηv.deriv.symm)
  simpa only [mul_one, hη1] using (heq 1 (by simp)).self_of_nhds.symm

end PoincareConjecture.RiemannianMetric
