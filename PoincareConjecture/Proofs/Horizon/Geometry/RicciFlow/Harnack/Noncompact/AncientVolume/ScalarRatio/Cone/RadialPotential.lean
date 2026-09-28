import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.NormalChart
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Exponential.InitialData
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Exponential.Gauss.Manifold
import Mathlib.Analysis.Calculus.TangentCone.Real

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace Poincare.AncientVolume.ScalarRatio

theorem endpoint_eq_of_quadratic_interpolation
    {F : ℝ → ℝ} {a c : ℝ} (hF : HasDerivAt F a 0)
    (hquad : ∀ t ∈ Icc (0 : ℝ) 1,
      F t = (1 - t) * F 0 + t * F 1 - t * (1 - t) * c / 2) :
    F 1 = F 0 + a + c / 2 := by
  have hp : HasDerivAt
      (fun t : ℝ => (1 - t) * F 0 + t * F 1 - t * (1 - t) * c / 2)
      (-F 0 + F 1 - c / 2) 0 := by
    convert! ((((hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub (hasDerivAt_id 0)).mul_const (F 0)).add
      ((hasDerivAt_id 0).mul_const (F 1)) |>.sub
      (((hasDerivAt_id 0).mul
        ((hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub (hasDerivAt_id 0))).mul_const c |>.div_const 2))
      using 1
    simp
  have hw := hp.hasDerivWithinAt.congr hquad (by norm_num)
  have heq := (uniqueDiffOn_Icc_zero_one 0 (by simp)).eq_deriv
    (Icc (0 : ℝ) 1) hF.hasDerivWithinAt hw
  linarith

end Poincare.AncientVolume.ScalarRatio

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem exists_smooth_normal_potential_of_geodesic_quadratic
    (g : RiemannianMetric n M) (f : M → ℝ) (p : M)
    (hf : DifferentiableAt ℝ (f ∘ (extChartAt (𝓡 n) p).symm)
      (extChartAt (𝓡 n) p p))
    (hquad : ∀ (γ : ℝ → M) (ε : ℝ), 0 < ε →
      g.IsGeodesicOn γ (Ioo (-ε) (1 + ε)) → ∀ t ∈ Icc (0 : ℝ) 1,
      f (γ t) = (1 - t) * f (γ 0) + t * f (γ 1) - t * (1 - t) *
        g.tangentNorm (γ 0) (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) γ 0 1) ^ 2 / 2) :
    ∃ e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M,
      (0 : EuclideanSpace ℝ (Fin n)) ∈ e.source ∧ e 0 = p ∧
      ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source ∧
      ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target ∧
      (∀ v ∈ e.source, ∃ γ : ℝ → M,
        g.IsGeodesicOn γ (Ioo (-1 : ℝ) 2) ∧ γ 0 = p ∧
        HasDerivAt (fun t => extChartAt (𝓡 n) p (γ t)) v 0 ∧ γ 1 = e v) ∧
      (∀ v ∈ e.source, f (e v) = f p +
        fderiv ℝ (f ∘ (extChartAt (𝓡 n) p).symm) (extChartAt (𝓡 n) p p) v +
          g.inner p v v / 2) ∧
      ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ f e.target := by
  let E := EuclideanSpace ℝ (Fin n)
  let c := extChartAt (𝓡 n) p
  let B := g.pullbackCoefficients c.symm
  let A := fderiv ℝ (f ∘ c.symm) (c p)
  obtain ⟨e, hzero, hezero, he, heinverse, _, Γ, _, hcurve⟩ :=
    g.exists_exponential_chart p
  have hgeo (v : E) (hv : v ∈ e.source) :
      ∃ γ : ℝ → M,
        g.IsGeodesicOn γ (Ioo (-1 : ℝ) 2) ∧ γ 0 = p ∧
        HasDerivAt (fun t => c (γ t)) v 0 ∧ γ 1 = e v ∧
        HasDerivAt (fun t => f (γ t)) (A v) 0 := by
    let q : ℝ → E := fun t => (Γ (v, t)).1
    let w : ℝ → E := fun t => (Γ (v, t)).2
    let γ : ℝ → M := fun t => c.symm (q t)
    have hdata := hcurve v hv
    have hq0 : q 0 = c p := congrArg Prod.fst hdata.1
    have hw0 : w 0 = v := congrArg Prod.snd hdata.1
    have htime {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 2) : t ∈ Ioo (-2 : ℝ) 2 :=
      ⟨by linarith [ht.1], ht.2⟩
    have hq (t : ℝ) (ht : t ∈ Ioo (-1 : ℝ) 2) :
        q t ∈ c.target ∧ HasDerivAt q (w t) t ∧
        HasDerivAt w (-coordinateChristoffel B (q t) (w t) (w t)) t := by
      have h := hdata.2.2.2 t (htime ht)
      exact ⟨h.1, h.2.1.fst, h.2.1.snd⟩
    have hγ : g.IsGeodesicOn γ (Ioo (-1 : ℝ) 2) :=
      g.isGeodesicOn_chart_curve p isOpen_Ioo hq
    have hγ0 : γ 0 = p := by
      dsimp [γ]
      rw [hq0]
      exact c.left_inv (mem_extChartAt_source p)
    have hqderiv : HasDerivAt q v 0 := by
      simpa only [hw0] using (hq 0 (by norm_num)).2.1
    have hchart : (fun t => c (γ t)) =ᶠ[𝓝 0] q := by
      filter_upwards [isOpen_Ioo.mem_nhds
        (show (0 : ℝ) ∈ Ioo (-1 : ℝ) 2 by norm_num)] with t ht
      exact c.right_inv (hq t ht).1
    have hderiv : HasDerivAt (fun t => f (γ t)) (A v) 0 := by
      have hfp : HasFDerivAt (f ∘ c.symm) A (q 0) := by
        rw [hq0]
        exact hf.hasFDerivAt
      exact hfp.comp_hasDerivAt 0 hqderiv
    exact ⟨γ, hγ, hγ0, hqderiv.congr_of_eventuallyEq hchart,
      hdata.2.1, hderiv⟩
  have hformula (v : E) (hv : v ∈ e.source) :
      f (e v) = f p + A v + g.inner p v v / 2 := by
    obtain ⟨γ, hγ, hγ0, hd, hγ1, hfd⟩ := hgeo v hv
    have hspeed := hγ.tangentNorm_initial (by norm_num) hγ0 hd
    rw [chartCoefficients_self] at hspeed
    have hQ : 0 ≤ g.inner p v v := by
      by_cases hv0 : v = 0
      · subst v; simp
      · exact (g.pos p v hv0).le
    have hspeed2 : g.tangentNorm (γ 0)
        (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) γ 0 1) ^ 2 = g.inner p v v := by
      rw [hspeed, Real.sq_sqrt hQ]
    have h := Poincare.AncientVolume.ScalarRatio.endpoint_eq_of_quadratic_interpolation
      hfd (hquad γ 1 (by norm_num) (by convert! hγ using 1; norm_num))
    simpa only [hγ0, hγ1, hspeed2] using h
  refine ⟨e, hzero, hezero, he, heinverse, ?_, hformula, ?_⟩
  · intro v hv
    obtain ⟨γ, hγ, hγ0, hd, hγ1, _⟩ := hgeo v hv
    exact ⟨γ, hγ, hγ0, hd, hγ1⟩
  · let P : E → ℝ := fun v => f p + A v + g.inner p v v / 2
    have hP : ContDiff ℝ ∞ P := by
      exact (contDiff_const.add A.contDiff).add
        (((contDiff_const.clm_apply contDiff_id).clm_apply contDiff_id).div_const 2)
    have hcomp : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ (P ∘ e.symm) e.target :=
      hP.contMDiff.comp_contMDiffOn heinverse
    apply hcomp.congr
    intro x hx
    change f x = P (e.symm x)
    simpa only [e.right_inv hx] using hformula (e.symm x) (e.map_target hx)

end PoincareConjecture.RiemannianMetric
