import PoincareConjecture.Proofs.M12.GeneralizedBoxes

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.Proofs.M12

open PoincareConjecture.Proofs.M11

variable (F : GeneralizedRicciFlowData.{u})

noncomputable def refinedSliceMap (b : refinedBoxIndex F) (t : ℝ)
    (ht : t ∈ (F.box b.1).interval) :
    OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 3)) (F.slice t).carrier :=
  (chartAt (EuclideanSpace ℝ (Fin 3)) b.2).symm.trans (boxSliceMap F b.1 t ht)

theorem refinedSliceMap_smooth (b : refinedBoxIndex F) (t : ℝ)
    (ht : t ∈ (F.box b.1).interval) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (refinedSliceMap F b t ht)
      (refinedSliceMap F b t ht).source :=
  ((F.box b.1).forward_smooth t ht).contMDiffOn.comp' contMDiffOn_chart_symm

theorem refinedSliceMap_inverse_smooth (b : refinedBoxIndex F) (t : ℝ)
    (ht : t ∈ (F.box b.1).interval) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (refinedSliceMap F b t ht).symm
      (refinedSliceMap F b t ht).target :=
  contMDiffOn_chart.comp' ((F.box b.1).inverse_smooth t ht)

noncomputable def coordinateTransition (b c : refinedBoxIndex F) (t : ℝ)
    (hb : t ∈ (F.box b.1).interval) (hc : t ∈ (F.box c.1).interval) :
    OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 3)) (EuclideanSpace ℝ (Fin 3)) :=
  (refinedSliceMap F b t hb).trans (refinedSliceMap F c t hc).symm

theorem coordinateTransition_smooth (b c : refinedBoxIndex F) (t : ℝ)
    (hb : t ∈ (F.box b.1).interval) (hc : t ∈ (F.box c.1).interval) :
    ContDiffOn ℝ ∞ (coordinateTransition F b c t hb hc)
      (coordinateTransition F b c t hb hc).source :=
  ((refinedSliceMap_inverse_smooth F c t hc).comp'
    (refinedSliceMap_smooth F b t hb)).contDiffOn

theorem coordinateTransition_inverse_smooth (b c : refinedBoxIndex F) (t : ℝ)
    (hb : t ∈ (F.box b.1).interval) (hc : t ∈ (F.box c.1).interval) :
    ContDiffOn ℝ ∞ (coordinateTransition F b c t hb hc).symm
      (coordinateTransition F b c t hb hc).target :=
  coordinateTransition_smooth F c b t hc hb

theorem coordinateTransition_worldline (b c : refinedBoxIndex F) (t : ℝ)
    (hb : t ∈ (F.box b.1).interval) (hc : t ∈ (F.box c.1).interval)
    (s : ℝ) (hsb : s ∈ (F.box b.1).interval) (hsc : s ∈ (F.box c.1).interval)
    (x : EuclideanSpace ℝ (Fin 3))
    (hx : x ∈ (coordinateTransition F b c t hb hc).source) :
    refinedSliceMap F b s hsb x =
      refinedSliceMap F c s hsc (coordinateTransition F b c t hb hc x) := by
  have h := (refinedSliceMap F c t hc).right_inv hx.2
  exact F.vertical_compatibility b.1 c.1 t hb hc _ _ h.symm s hsb hsc

theorem refinedSliceMap_metric (b : refinedBoxIndex F) (t : ℝ)
    (ht : t ∈ (F.box b.1).interval) (x : EuclideanSpace ℝ (Fin 3))
    (hx : x ∈ (refinedSliceMap F b t ht).source)
    (v w : EuclideanSpace ℝ (Fin 3)) :
    (F.metric t).inner (refinedSliceMap F b t ht x)
      (mfderiv (𝓡 3) (𝓡 3) (refinedSliceMap F b t ht) x v)
      (mfderiv (𝓡 3) (𝓡 3) (refinedSliceMap F b t ht) x w) =
        (refinedBox F b).metric (t, x) v w := by
  let chart := chartAt (EuclideanSpace ℝ (Fin 3)) b.2
  have hchart := (spatialChart_symm_localDiffeomorphAt b.2 x hx.1).mdifferentiableAt
    (by simp)
  have hf := ((F.box b.1).forward_smooth t ht (chart.symm x)).mdifferentiableAt
    (by simp)
  change (F.metric t).inner ((F.box b.1).forward t ht (chart.symm x))
    (mfderiv (𝓡 3) (𝓡 3) ((F.box b.1).forward t ht ∘ chart.symm) x v)
    (mfderiv (𝓡 3) (𝓡 3) ((F.box b.1).forward t ht ∘ chart.symm) x w) = _
  rw [mfderiv_comp_apply x hf hchart v, mfderiv_comp_apply x hf hchart w]
  exact (F.box b.1).metric_pullback t ht (chart.symm x) _ _

theorem coordinateTransition_derivative (b c : refinedBoxIndex F) (t : ℝ)
    (hb : t ∈ (F.box b.1).interval) (hc : t ∈ (F.box c.1).interval)
    (s : ℝ) (hsb : s ∈ (F.box b.1).interval) (hsc : s ∈ (F.box c.1).interval)
    (x : EuclideanSpace ℝ (Fin 3))
    (hx : x ∈ (coordinateTransition F b c t hb hc).source)
    (v : EuclideanSpace ℝ (Fin 3)) :
    mfderiv (𝓡 3) (𝓡 3) (refinedSliceMap F c s hsc)
      (coordinateTransition F b c t hb hc x)
      (fderiv ℝ (coordinateTransition F b c t hb hc) x v) =
        mfderiv (𝓡 3) (𝓡 3) (refinedSliceMap F b s hsb) x v := by
  let e := coordinateTransition F b c t hb hc
  have hcx : e x ∈ (refinedSliceMap F c s hsc).source :=
    ⟨(e.map_source hx).1.1, mem_univ _⟩
  have hC := ((refinedSliceMap_smooth F c s hsc).contMDiffAt
    ((refinedSliceMap F c s hsc).open_source.mem_nhds hcx)).mdifferentiableAt (by simp)
  have he := ((coordinateTransition_smooth F b c t hb hc).contDiffAt
    (e.open_source.mem_nhds hx)).contMDiffAt.mdifferentiableAt (by simp)
  have heq : refinedSliceMap F c s hsc ∘ e =ᶠ[𝓝 x] refinedSliceMap F b s hsb := by
    filter_upwards [e.open_source.mem_nhds hx] with y hy
    exact (coordinateTransition_worldline F b c t hb hc s hsb hsc y hy).symm
  have h := mfderiv_comp_apply x hC he v
  rw [heq.mfderiv_eq, mfderiv_eq_fderiv] at h
  exact h.symm

theorem coordinateTransition_metric (b c : refinedBoxIndex F) (t : ℝ)
    (hb : t ∈ (F.box b.1).interval) (hc : t ∈ (F.box c.1).interval)
    (s : ℝ) (hsb : s ∈ (F.box b.1).interval) (hsc : s ∈ (F.box c.1).interval)
    (x : EuclideanSpace ℝ (Fin 3))
    (hx : x ∈ (coordinateTransition F b c t hb hc).source)
    (v w : EuclideanSpace ℝ (Fin 3)) :
    (refinedBox F b).metric (s, x) v w =
      (refinedBox F c).metric (s, coordinateTransition F b c t hb hc x)
        (fderiv ℝ (coordinateTransition F b c t hb hc) x v)
        (fderiv ℝ (coordinateTransition F b c t hb hc) x w) := by
  let e := coordinateTransition F b c t hb hc
  have hbx : x ∈ (refinedSliceMap F b s hsb).source := ⟨hx.1.1, mem_univ _⟩
  have hcx : e x ∈ (refinedSliceMap F c s hsc).source :=
    ⟨(e.map_source hx).1.1, mem_univ _⟩
  rw [← refinedSliceMap_metric F b s hsb x hbx,
    ← refinedSliceMap_metric F c s hsc (e x) hcx,
    coordinateTransition_derivative F b c t hb hc s hsb hsc x hx v,
    coordinateTransition_derivative F b c t hb hc s hsb hsc x hx w,
    coordinateTransition_worldline F b c t hb hc s hsb hsc x hx]

end PoincareConjecture.Proofs.M12
