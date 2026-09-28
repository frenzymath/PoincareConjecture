import PoincareConjecture.Proofs.M11.OrdinaryChartMetric





set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.Proofs.M11

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

noncomputable def spatialChartTransition (p q : M) :
    OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)) :=
  (chartAt (EuclideanSpace ℝ (Fin n)) p).symm.trans
    (chartAt (EuclideanSpace ℝ (Fin n)) q)

theorem spatialChartTransition_smooth (p q : M) :
    ContDiffOn ℝ ∞ (spatialChartTransition (n := n) p q)
      (spatialChartTransition p q).source := by
  have h : ContMDiffOn (𝓡 n) (𝓡 n) ∞ (spatialChartTransition p q)
      (spatialChartTransition p q).source :=
    contMDiffOn_chart.comp' contMDiffOn_chart_symm
  exact h.contDiffOn

theorem spatialChartTransition_symm_smooth (p q : M) :
    ContDiffOn ℝ ∞ (spatialChartTransition (n := n) p q).symm
      (spatialChartTransition p q).target :=
  spatialChartTransition_smooth q p

omit [IsManifold (𝓡 n) ∞ M] in
theorem spatialChartTransition_inverse_eq (p q : M) (x : EuclideanSpace ℝ (Fin n))
    (hx : x ∈ (spatialChartTransition p q).source) :
    (chartAt (EuclideanSpace ℝ (Fin n)) q).symm (spatialChartTransition p q x) =
      (chartAt (EuclideanSpace ℝ (Fin n)) p).symm x :=
  (chartAt (EuclideanSpace ℝ (Fin n)) q).left_inv hx.2

theorem spatialChartTransition_inverse_derivative (p q : M)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ (spatialChartTransition p q).source)
    (v : EuclideanSpace ℝ (Fin n)) :
    mfderiv (𝓡 n) (𝓡 n) (chartAt (EuclideanSpace ℝ (Fin n)) q).symm
        (spatialChartTransition p q x) (fderiv ℝ (spatialChartTransition p q) x v) =
      mfderiv (𝓡 n) (𝓡 n) (chartAt (EuclideanSpace ℝ (Fin n)) p).symm x v := by
  let T := spatialChartTransition (n := n) p q
  have hq' := spatialChart_symm_localDiffeomorphAt q (T x) (T.map_source hx).1
  have hq := hq'.mdifferentiableAt (by simp)
  have hT := ((spatialChartTransition_smooth p q).contDiffAt
    (T.open_source.mem_nhds hx)).contMDiffAt.mdifferentiableAt (by simp)
  have heq : (chartAt (EuclideanSpace ℝ (Fin n)) q).symm ∘ T =ᶠ[𝓝 x]
      (chartAt (EuclideanSpace ℝ (Fin n)) p).symm := by
    filter_upwards [T.open_source.mem_nhds hx] with y hy
    exact spatialChartTransition_inverse_eq p q y hy
  have h := mfderiv_comp_apply x hq hT v
  rw [heq.mfderiv_eq] at h
  rw [mfderiv_eq_fderiv] at h
  convert! h.symm using 1

theorem ordinaryChartMetric_transition (g : ℝ → RiemannianMetric n M) (p q : M)
    (t : ℝ) (x : EuclideanSpace ℝ (Fin n))
    (hx : x ∈ (spatialChartTransition p q).source) (v w : EuclideanSpace ℝ (Fin n)) :
    ordinaryChartMetric g p (t, x) v w =
      ordinaryChartMetric g q (t, spatialChartTransition p q x)
        (fderiv ℝ (spatialChartTransition p q) x v)
        (fderiv ℝ (spatialChartTransition p q) x w) := by
  change (g t).inner ((chartAt (EuclideanSpace ℝ (Fin n)) p).symm x)
    (mfderiv (𝓡 n) (𝓡 n) (chartAt (EuclideanSpace ℝ (Fin n)) p).symm x v)
    (mfderiv (𝓡 n) (𝓡 n) (chartAt (EuclideanSpace ℝ (Fin n)) p).symm x w) =
    (g t).inner ((chartAt (EuclideanSpace ℝ (Fin n)) q).symm (spatialChartTransition p q x))
    (mfderiv (𝓡 n) (𝓡 n) (chartAt (EuclideanSpace ℝ (Fin n)) q).symm
      (spatialChartTransition p q x) (fderiv ℝ (spatialChartTransition p q) x v))
    (mfderiv (𝓡 n) (𝓡 n) (chartAt (EuclideanSpace ℝ (Fin n)) q).symm
      (spatialChartTransition p q x) (fderiv ℝ (spatialChartTransition p q) x w))
  rw [spatialChartTransition_inverse_derivative p q x hx,
    spatialChartTransition_inverse_derivative p q x hx,
    spatialChartTransition_inverse_eq p q x hx]

end PoincareConjecture.Proofs.M11
