import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Compact.Rigidity.CriticalLevel
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Compact.Rigidity.TotalCurvature
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.SublevelVolume

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.LeviCivitaData

variable {M : Type*} [TopologicalSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  [CompactSpace M] [ConnectedSpace M] {g : RiemannianMetric 2 M}

theorem constantPositiveSectionalCurvature_of_compact_surface_soliton
    (D : LeviCivitaData g) {f : M → ℝ} {lambda : ℝ} (hlambda : 0 < lambda)
    (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) 2 f)
    (hsol : ∀ x, ∀ v w : TangentSpace (𝓡 2) x,
      D.ricci x v w + D.hessian f x v w = lambda * g.inner x v w)
    (hRnonneg : ∀ x, 0 ≤ D.scalarCurvature x) :
    ConstantPositiveSectionalCurvature g D := by
  let : MeasurableSpace M := borel M
  let : BorelSpace M := ⟨rfl⟩
  by_contra hnot
  have hfs := D.contMDiff_of_C2_surface_soliton hf hsol
  obtain ⟨p, z, hbounds, hp, hz, hpz, hRp, hRz, hsum⟩ :=
    D.exists_strict_extrema_of_compact_not_round hlambda hf hsol hnot
  have hc : MetricComplete g := by
    unfold MetricComplete
    infer_instance
  have huniq (x : M) (hx : f x = f p) : x = p :=
    (D.eq_of_potential_eq_at_critical_point_of_not_round hc hlambda hf hsol hnot hp hx.symm).symm
  let a : ℝ := lambda - D.scalarCurvature p / 2
  have ha : 0 < a := by dsimp [a]; linarith
  have hhess (v w : TangentSpace (𝓡 2) p) :
      D.hessian f p v w = a * g.inner p v w := by
    rw [D.hessian_eq_of_surface_soliton hsol]
    dsimp [a]
    ring
  have hlimit := D.tendsto_sublevelVolume_div_sub_min hfs (fun x => (hbounds x).1)
    huniq hp ha hhess
  obtain ⟨c, hcpos, hslab⟩ :=
    D.exists_constant_slab_density_of_surface_soliton hlambda hf hsol hRnonneg hp hpz
  have hconst : (fun t : ℝ => (g.volumeMeasure (f ⁻¹' Ioo (f p) t)).toReal / (t - f p))
      =ᶠ[𝓝[>] f p] fun _ => c := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (gt_mem_nhds hpz)] with t ht htz
    change g.volumeMeasure.real (f ⁻¹' Ioo (f p) t) / (t - f p) = c
    rw [g.volume_open_slab_eq_of_constant_slab_density hslab ht htz.le,
      mul_div_cancel_right₀ _ (sub_pos.mpr ht).ne']
  have hcvalue : c = 2 * Real.pi / a :=
    tendsto_nhds_unique (tendsto_const_nhds.congr' hconst.symm) hlimit
  have htotal := D.density_mul_scalar_difference_le_eight_pi hf hsol hRnonneg hpz hslab
  rw [hcvalue, div_mul_eq_mul_div, div_le_iff₀ ha] at htotal
  have hstrict : 4 * a < D.scalarCurvature z - D.scalarCurvature p := by
    dsimp [a]
    linarith
  have hpi := Real.pi_pos
  nlinarith

end PoincareConjecture.LeviCivitaData
