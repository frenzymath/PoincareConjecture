import PoincareConjecture.Proofs.M76.Mathlib.AffineLeafCoordinates










set_option autoImplicit false

open Set Filter
open scoped Topology ContDiff

namespace ContinuousAffineMap

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]



theorem projKer_affineLeafMap_sub (a : F →ᴬ[ℝ] E) (Q : F → E →L[ℝ] F)
    (x0 : F) (h0 : Function.RightInverse a.contLinear (Q x0))
    (z : F × (Q x0).ker) :
    (Q x0).projKerOfRightInverse a.contLinear h0
      (a.affineLeafMap Q x0 z - a z.1) = z.2 := by
  have he : a.affineLeafMap Q x0 z - a z.1 =
      (z.2 : E) - a.contLinear (Q z.1 z.2) := by
    unfold affineLeafMap
    abel
  rw [he, map_sub, ContinuousLinearMap.projKerOfRightInverse_apply_idem,
    ContinuousLinearMap.projKerOfRightInverse_comp_inv, sub_zero]



theorem affineLeafMap_projKer (a : F →ᴬ[ℝ] E) (Q : F → E →L[ℝ] F)
    (x0 : F) (h0 : Function.RightInverse a.contLinear (Q x0))
    {x : F} (hx : Function.RightInverse a.contLinear (Q x)) {y : E}
    (hy : y - a x ∈ (Q x).ker) :
    a.affineLeafMap Q x0
      (x, (Q x0).projKerOfRightInverse a.contLinear h0 (y - a x)) = y := by
  change Q x (y - a x) = 0 at hy
  change a x + ((y - a x) - a.contLinear (Q x0 (y - a x))) -
    a.contLinear (Q x ((y - a x) - a.contLinear (Q x0 (y - a x)))) = y
  rw [(Q x).map_sub, hx, hy, zero_sub, map_neg]
  abel





theorem eventually_affineLeaf_base_eq (a : F →ᴬ[ℝ] E) (Q : F → E →L[ℝ] F)
    (x0 : F) (hQ : ∀ x, Function.RightInverse a.contLinear (Q x))
    (e : OpenPartialHomeomorph (F × (Q x0).ker) E)
    (he : (e : F × (Q x0).ker → E) = a.affineLeafMap Q x0)
    {y : E} (hy : y ∈ e.target) :
    ∀ᶠ w in 𝓝 y, w - y ∈ (Q (e.symm y).1).ker →
      (e.symm w).1 = (e.symm y).1 := by
  let x := (e.symm y).1
  let k : E → F × (Q x0).ker := fun w =>
    (x, (Q x0).projKerOfRightInverse a.contLinear (hQ x0) (w - a x))
  have hk : Continuous k := continuous_const.prodMk
    (((Q x0).projKerOfRightInverse a.contLinear (hQ x0)).continuous.comp
      (continuous_id.sub continuous_const))
  have hey : a.affineLeafMap Q x0 (e.symm y) = y := by
    rw [← he]
    exact e.right_inv hy
  have hky : k y = e.symm y := by
    refine Prod.ext rfl ?_
    change (Q x0).projKerOfRightInverse a.contLinear (hQ x0)
      (y - a (e.symm y).1) = (e.symm y).2
    have h := a.projKer_affineLeafMap_sub Q x0 (hQ x0) (e.symm y)
    rwa [hey] at h
  have hnear : ∀ᶠ w in 𝓝 y, k w ∈ e.source :=
    hk.continuousAt.preimage_mem_nhds
      (e.open_source.mem_nhds (hky.symm ▸ e.map_target hy))
  have hyker : y - a x ∈ (Q x).ker := by
    simpa only [hey] using a.affineLeafMap_sub_mem_ker Q x0 hQ (e.symm y)
  filter_upwards [hnear] with w hw hwy
  have hwker : w - a x ∈ (Q x).ker := by
    convert (Q x).ker.add_mem hwy hyker using 1
    abel
  have hew : e (k w) = w := by
    rw [he]
    exact a.affineLeafMap_projKer Q x0 (hQ x0) (hQ x) hwker
  have hi := e.left_inv hw
  rw [hew] at hi
  simpa only [k] using congrArg Prod.fst hi

end ContinuousAffineMap
