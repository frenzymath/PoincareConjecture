import PoincareConjecture.Proofs.M76.Mathlib.LocallyPiecewiseAffineInverse
import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Topology.Algebra.ContinuousAffineEquiv
import Mathlib.Topology.OpenPartialHomeomorph.Constructions

set_option autoImplicit false

open Set Geometry

namespace AddMonoidHom

theorem exists_piecewiseAffine_quotient_cover
    {E F X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [AddCommGroup X] [TopologicalSpace X]
    (p : E →+ X) (hp : IsLocalHomeomorph p) (hsurj : Function.Surjective p)
    (L : E ≃ᴬ[ℝ] F) :
    ∃ c : E → OpenPartialHomeomorph X F,
      (∀ x : X, ∃ i, x ∈ (c i).source) ∧
      (∀ i j, (c i).symm.trans (c j) ∈ piecewiseAffineGroupoid F) ∧
      ∀ i y, (c i).symm y = p (L.symm y) := by
  let c : E → OpenPartialHomeomorph X F := fun i =>
    (hp.localInverseAt i).transHomeomorph L.toHomeomorph
  have hinv (i : E) (y : F) : (c i).symm y = p (L.symm y) := by
    change (hp.localInverseAt i).symm (L.symm y) = p (L.symm y)
    rw [hp.localInverseAt_symm]
  refine ⟨c, ?_, ?_, hinv⟩
  · intro x
    obtain ⟨i, rfl⟩ := hsurj x
    exact ⟨i, hp.apply_self_mem_localInverseAt_source⟩
  · intro i j
    apply (mem_piecewiseAffineGroupoid_iff_forward _).mpr
    apply LocallyPiecewiseAffineOn.locality
    intro z hz
    let v := L.symm z
    have hv : p v ∈ (c j).source := by
      have h := hz.2
      change (c i).symm z ∈ (c j).source at h
      rwa [hinv] at h
    let w := L.symm (c j (p v))
    let delta := w - v
    have hw : p w = p v := by
      rw [← hinv j (c j (p v)), (c j).left_inv hv]
    have hdelta : p delta = 0 := by
      change p (w - v) = 0
      rw [map_sub, hw, sub_self]
    let a : F ≃ᴬ[ℝ] F := L.symm.trans
      ((ContinuousAffineEquiv.constVAdd ℝ E delta).trans L)
    have ha (y : F) : L.symm (a y) = delta + L.symm y := by
      change L.symm (L (delta + L.symm y)) = delta + L.symm y
      rw [L.symm_apply_apply]
    have haz : a z = c j (p v) := by
      change L ((w - v) + v) = c j (p v)
      rw [sub_add_cancel]
      exact L.apply_symm_apply _
    have hquot (y : F) : (c j).symm (a y) = (c i).symm y := by
      rw [hinv, hinv, ha, map_add, hdelta, zero_add]
    let U : Set F := a ⁻¹' (c j).target
    have hU : IsOpen U := (c j).open_target.preimage a.continuous
    have hzU : z ∈ U := by
      change a z ∈ (c j).target
      rw [haz]
      exact (c j).mapsTo hv
    refine ⟨U, hzU, ?_⟩
    apply (locallyPiecewiseAffineOn_affine a.toContinuousAffineMap
      (((c i).symm.trans (c j)).open_source.inter hU)).congr
    intro y hy
    change a y = c j ((c i).symm y)
    rw [← hquot y, (c j).right_inv hy.2]

end AddMonoidHom
