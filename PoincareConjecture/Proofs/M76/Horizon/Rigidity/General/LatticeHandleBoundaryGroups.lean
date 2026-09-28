import PoincareConjecture.Proofs.M76.Horizon.Rigidity.General.Mathlib.DiscreteProductFundamentalGroup
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.RetractionFundamentalGroup
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.HomotopyFundamentalGroup
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonLatticeHandleModel

set_option autoImplicit false

open Set Metric

namespace PoincareConjecture.M76

theorem finite_unit_rim_of_card_eq_one {ι : Type*} [Fintype ι]
    (hι : Fintype.card ι = 1) :
    ({a : closedBall (0 : ι → ℝ) 1 | ‖(a : ι → ℝ)‖ = 1} :
      Set (closedBall (0 : ι → ℝ) 1)).Finite := by
  obtain ⟨u⟩ := Fintype.card_eq_one_iff_nonempty_unique.mp hι
  let : Unique ι := u
  let E := IsometryEquiv.funUnique ι ℝ
  have hE0 : E 0 = 0 := rfl
  have hpre : E ⁻¹' sphere (0 : ℝ) 1 = sphere (0 : ι → ℝ) 1 := by
    simpa only [hE0] using E.isometry.preimage_sphere 0 1
  have hsphere : (sphere (0 : ι → ℝ) 1).Finite := by
    rw [← hpre, Real.sphere_eq_pair 0 (by norm_num : (0 : ℝ) ≤ 1)]
    exact Set.Finite.preimage E.injective.injOn ((finite_singleton _).insert _)
  have hrim : {a : closedBall (0 : ι → ℝ) 1 | ‖(a : ι → ℝ)‖ = 1} =
      (Subtype.val : closedBall (0 : ι → ℝ) 1 → (ι → ℝ)) ⁻¹' sphere 0 1 := by
    ext a
    simp only [mem_ofPred_eq, mem_preimage, mem_sphere_zero_iff_norm]
  rw [hrim]
  exact Set.Finite.preimage Subtype.val_injective.injOn hsphere

theorem latticeHandleBoundary_pi1_injective_of_card_eq_one
    {ι κ : Type*} [Fintype ι] [Fintype κ] (hι : Fintype.card ι = 1)
    (L : Submodule ℤ (κ → ℝ)) (x : latticeHandleBoundary ι κ L) :
    Function.Injective (FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ :
        C(latticeHandleBoundary ι κ L, LatticeHandle ι κ L)) x) := by
  let S : Set (closedBall (0 : ι → ℝ) 1) := {a | ‖(a : ι → ℝ)‖ = 1}
  let T := (κ → ℝ) ⧸ L.toAddSubgroup
  let : Finite S := (finite_unit_rim_of_card_eq_one hι).to_subtype
  let q : latticeHandleBoundary ι κ L ≃ₜ (S × T) :=
    (Homeomorph.Set.prod S (univ : Set T)).trans
      ((Homeomorph.refl S).prodCongr (Homeomorph.Set.univ T))
  let proj : C(latticeHandleBoundary ι κ L, T) :=
    ⟨fun y => y.val.2, continuous_snd.comp continuous_subtype_val⟩
  have hq : Function.Injective (FundamentalGroup.map ⟨q, q.continuous⟩ x) :=
    FundamentalGroup.map_injective_of_leftInverse ⟨q, q.continuous⟩ ⟨q.symm, q.symm.continuous⟩
      q.symm_apply_apply x
  have hproj : Function.Injective (FundamentalGroup.map proj x) := by
    intro a b hab
    apply hq
    apply FundamentalGroup.map_snd_injective_of_totallyDisconnected (q x)
    have hc := FundamentalGroup.map_comp_apply ⟨q, q.continuous⟩
      (⟨Prod.snd, continuous_snd⟩ : C(S × T, T)) x
    exact (hc a).symm.trans (hab.trans (hc b))
  intro a b hab
  apply hproj
  change FundamentalGroup.map
      (ContinuousMap.snd.comp (⟨Subtype.val, continuous_subtype_val⟩ :
        C(latticeHandleBoundary ι κ L, LatticeHandle ι κ L))) x a =
    FundamentalGroup.map
      (ContinuousMap.snd.comp (⟨Subtype.val, continuous_subtype_val⟩ :
        C(latticeHandleBoundary ι κ L, LatticeHandle ι κ L))) x b
  rw [FundamentalGroup.map_comp_apply, FundamentalGroup.map_comp_apply, hab]

end PoincareConjecture.M76
