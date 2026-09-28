import PoincareConjecture.Proofs.M47.LimitNoncollapseCapture
import PoincareConjecture.Proofs.M34.Standard.GeneralizedCylinderVolume

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u v

namespace PoincareConjecture.Proofs.M47

theorem seedLimit_physical_chart_capture_and_volume
    {C : GeneralizedSliceCarrier.{u}} {D : GeneralizedSliceCarrier.{v}}
    (g : RiemannianMetric 3 C.carrier) (h : RiemannianMetric 3 D.carrier)
    (f : PartialDiffeomorph (𝓡 3) (𝓡 3) C.carrier D.carrier ∞)
    (p : C.carrier) {Q R rho lambda : ℝ}
    (hQ : 0 < Q) (hR : 0 < R) (hlambda : 0 < lambda)
    (hbuffer : rho / lambda < R)
    (hcompact : IsCompact (closure (g.ball p R)))
    (hsource : closure (g.ball p R) ⊆ f.source)
    (hlow : ∀ x ∈ closure (g.ball p R), ∀ v : TangentSpace (𝓡 3) x,
      g.tangentNorm x v ≤ (Real.sqrt Q / lambda) *
        h.tangentNorm (f x) (mfderiv (𝓡 3) (𝓡 3) f x v))
    (hupp : ∀ x ∈ closure (g.ball p R), ∀ v : TangentSpace (𝓡 3) x,
      h.tangentNorm (f x) (mfderiv (𝓡 3) (𝓡 3) f x v) ≤
        (1 / (lambda * Real.sqrt Q)) * g.tangentNorm x v) :
    h.ball (f p) (rho / Real.sqrt Q) ⊆ f '' g.ball p (rho / lambda) ∧
      calibratedMetricVolume h (h.ball (f p) (rho / Real.sqrt Q)) ≤
        ENNReal.ofReal (1 / (lambda * Real.sqrt Q)) ^ 3 *
          calibratedMetricVolume g (g.ball p R) := by
  let e := f.toOpenPartialHomeomorph
  have hf : ContMDiffOn (𝓡 3) (𝓡 3) 1 e e.source :=
    f.contMDiffOn.of_le (by simp)
  have hi : ContMDiffOn (𝓡 3) (𝓡 3) 1 e.symm e.target :=
    f.symm.contMDiffOn.of_le (by simp)
  have hroot : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQ
  have hcancel : (Real.sqrt Q / lambda) * (rho / Real.sqrt Q) =
      rho / lambda := by field_simp
  have hcapture : h.ball (e p) (rho / Real.sqrt Q) ⊆
      e '' g.ball p (rho / lambda) := by
    rw [← hcancel]
    apply PoincareConjecture.M47.limitNoncollapse_capture_ball g h e p hR
      (div_pos hroot hlambda) (by rwa [hcancel]) hcompact hsource
    · intro y hy
      exact (hi y hy).contMDiffAt (e.open_target.mem_nhds hy)
    · rintro y ⟨x, hx, rfl⟩ v
      apply g.inverse_tangentNorm_le_of_forward_lower_bound h e hf hi
        (e.map_source (hsource hx))
      intro w
      exact hlow (e.symm (e x)) (by rwa [e.left_inv (hsource hx)]) w
  have hsmall : g.ball p (rho / lambda) ⊆ g.ball p R := by
    intro x hx
    exact hx.trans_le (ENNReal.ofReal_le_ofReal hbuffer.le)
  refine ⟨hcapture, ?_⟩
  let : PseudoEMetricSpace C.carrier := g.comparisonPseudoEMetric
  have hV : IsOpen (g.ball p R) :=
    isOpen_lt (continuous_const.edist continuous_id) continuous_const
  let eV := e.restrOpen (g.ball p R) hV
  have heV : ContMDiffOn (𝓡 3) (𝓡 3) 1 eV eV.source :=
    hf.mono inter_subset_left
  have hVs : g.ball p R ⊆ eV.source :=
    fun x hx => ⟨hsource (subset_closure hx), hx⟩
  have hv := M34.calibratedMetricVolume_image_le_of_local_tangentNorm_le
    g h eV heV (one_div_pos.mpr (mul_pos hlambda hroot))
    (fun x hx v => hupp x (subset_closure hx.2) v) hV.measurableSet hVs
  exact (measure_mono (hcapture.trans (image_mono hsmall))).trans hv

end PoincareConjecture.Proofs.M47
