import PoincareConjecture.Proofs.M76.Mathlib.RadialBallQuotient
import Mathlib.Topology.Homotopy.Contractible










set_option autoImplicit false

open Set Metric unitInterval NormedSpace

namespace ContinuousMap

variable {E Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [TopologicalSpace Y]




theorem Nullhomotopic.exists_closedBall_extension (f : C(sphere (0 : E) 1, Y))
    (hf : f.Nullhomotopic) :
    ∃ g : C(closedBall (0 : E) 1, Y),
      ∀ x : sphere (0 : E) 1, g ⟨x, sphere_subset_closedBall x.property⟩ = f x := by
  obtain ⟨y, ⟨H⟩⟩ := hf
  rcases subsingleton_or_nontrivial E with hE | hE
  · let := hE
    refine ⟨ContinuousMap.const _ y, ?_⟩
    intro x
    have hn := norm_eq_of_mem_sphere x
    rw [Subsingleton.elim (x : E) 0, norm_zero] at hn
    exact (zero_ne_one hn).elim
  · let := hE
    let q := unitSphereRadialMap E
    have hq : Topology.IsQuotientMap q := isQuotientMap_unitSphereRadialMap E
    have hfactor : Function.FactorsThrough H.symm.toContinuousMap q := by
      intro z w hzw
      obtain ⟨ht, hz | hu⟩ := (unitSphereRadialMap_eq_iff E z w).mp hzw
      · have hw : w.1 = 0 := ht.symm.trans hz
        change H.symm (z.1, z.2) = H.symm (w.1, w.2)
        rw [hz, hw, H.symm.apply_zero, H.symm.apply_zero]
        rfl
      · exact congrArg H.symm.toContinuousMap (Prod.ext ht hu)
    let g := hq.lift H.symm.toContinuousMap hfactor
    refine ⟨g, ?_⟩
    intro x
    have hqx : q (1, x) = ⟨x, sphere_subset_closedBall x.property⟩ :=
      Subtype.ext (one_smul ℝ (x : E))
    rw [← hqx]
    exact (congrArg (fun k : C(I × sphere (0 : E) 1, Y) => k (1, x))
      (hq.lift_comp H.symm.toContinuousMap hfactor)).trans (H.symm.apply_one x)

variable [ContractibleSpace Y]




theorem exists_closedBall_extension_of_contractible (f : C(sphere (0 : E) 1, Y)) :
    ∃ g : C(closedBall (0 : E) 1, Y),
      ∀ x : sphere (0 : E) 1, g ⟨x, sphere_subset_closedBall x.property⟩ = f x := by
  have hf : f.Nullhomotopic := by
    simpa only [ContinuousMap.id_comp] using (id_nullhomotopic Y).comp_left f
  exact hf.exists_closedBall_extension f

end ContinuousMap
