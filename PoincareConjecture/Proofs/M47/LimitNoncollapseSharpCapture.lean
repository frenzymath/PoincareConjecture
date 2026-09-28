import PoincareConjecture.Proofs.M47.LimitNoncollapseCapture
import PoincareConjecture.Proofs.M47.LimitNoncollapseSharpTangent
import PoincareConjecture.Proofs.M34.Standard.GeneralizedCylinderVolume

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M47

theorem limitNoncollapse_physical_capture_and_volume
    {F : GeneralizedRicciFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
    {origin scale : ℝ} {I : Set ℝ} {U : Set C.carrier}
    (e : GeneralizedFlowCylinder F C origin scale I U) (hU : IsOpen U)
    (g : RiemannianMetric 3 C.carrier) (p : C.carrier) (t : ℝ) (ht : t ∈ I)
    {R rho lambda : ℝ} (hR : 0 < R) (hlambda : 0 < lambda)
    (hbuffer : rho / lambda < R)
    (hcompact : IsCompact (closure (g.ball p R)))
    (hsource : closure (g.ball p R) ⊆ U)
    (hlow : ∀ x ∈ closure (g.ball p R), ∀ v : TangentSpace (𝓡 3) x,
      g.tangentNorm x v ≤ (Real.sqrt scale / lambda) *
        (F.metric (origin + t / scale)).tangentNorm (e.forward t ht x)
          (mfderiv (𝓡 3) (𝓡 3) (e.forward t ht) x v))
    (hupp : ∀ x ∈ closure (g.ball p R), ∀ v : TangentSpace (𝓡 3) x,
      (F.metric (origin + t / scale)).tangentNorm (e.forward t ht x)
          (mfderiv (𝓡 3) (𝓡 3) (e.forward t ht) x v) ≤
        (1 / (lambda * Real.sqrt scale)) * g.tangentNorm x v) :
    (F.metric (origin + t / scale)).ball (e.forward t ht p) (rho / Real.sqrt scale) ⊆
        e.forward t ht '' g.ball p (rho / lambda) ∧
      calibratedMetricVolume (F.metric (origin + t / scale))
          ((F.metric (origin + t / scale)).ball (e.forward t ht p)
            (rho / Real.sqrt scale)) ≤
        ENNReal.ofReal (1 / (lambda * Real.sqrt scale)) ^ 3 *
          calibratedMetricVolume g (g.ball p R) := by
  let f := e.spatialOpenPartialHomeomorph hU t ht
  let h := F.metric (origin + t / scale)
  have hf : ContMDiffOn (𝓡 3) (𝓡 3) 1 f f.source :=
    (e.spatialOpenPartialHomeomorph_contMDiffOn hU t ht).of_le (by simp)
  have hi : ContMDiffOn (𝓡 3) (𝓡 3) 1 f.symm f.target :=
    (e.spatialOpenPartialHomeomorph_symm_contMDiffOn hU t ht).of_le (by simp)
  have hroot : 0 < Real.sqrt scale := Real.sqrt_pos.mpr e.scale_pos
  have hcancel : (Real.sqrt scale / lambda) * (rho / Real.sqrt scale) =
      rho / lambda := by field_simp
  have hcapture : h.ball (f p) (rho / Real.sqrt scale) ⊆
      f '' g.ball p (rho / lambda) := by
    rw [← hcancel]
    apply limitNoncollapse_capture_ball g h f p hR (div_pos hroot hlambda)
      (by rwa [hcancel]) hcompact hsource
    · intro y hy
      exact (hi y hy).contMDiffAt (f.open_target.mem_nhds hy)
    · rintro y ⟨x, hx, rfl⟩ v
      apply g.inverse_tangentNorm_le_of_forward_lower_bound h f hf hi
        (f.map_source (hsource hx))
      intro w
      exact hlow (f.symm (f x)) (by rwa [f.left_inv (hsource hx)]) w
  have hsmall : g.ball p (rho / lambda) ⊆ g.ball p R := by
    intro x hx
    exact hx.trans_le (ENNReal.ofReal_le_ofReal hbuffer.le)
  refine ⟨hcapture, ?_⟩
  let : PseudoEMetricSpace C.carrier := g.comparisonPseudoEMetric
  have hV : IsOpen (g.ball p R) :=
    isOpen_lt (continuous_const.edist continuous_id) continuous_const
  let fV := f.restrOpen (g.ball p R) hV
  have hfV : ContMDiffOn (𝓡 3) (𝓡 3) 1 fV fV.source :=
    hf.mono inter_subset_left
  have hVs : g.ball p R ⊆ fV.source :=
    fun x hx => ⟨hsource (subset_closure hx), hx⟩
  have hv := M34.calibratedMetricVolume_image_le_of_local_tangentNorm_le
    g h fV hfV (one_div_pos.mpr (mul_pos hlambda hroot))
    (fun x hx v => hupp x (subset_closure hx.2) v) hV.measurableSet hVs
  apply le_trans _ hv
  exact measure_mono (hcapture.trans (image_mono hsmall))

end PoincareConjecture.M47
