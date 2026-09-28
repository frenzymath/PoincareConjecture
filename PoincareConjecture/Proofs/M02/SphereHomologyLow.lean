import PoincareConjecture.Proofs.M02.HurewiczRepresentatives
import PoincareConjecture.Proofs.M02.SphereConnectivity
import PoincareConjecture.Statement










set_option autoImplicit false

open CategoryTheory Limits

namespace PoincareConjecture.Proofs.M02

noncomputable section

open PoincareConjecture

private noncomputable abbrev threeSphereType :=
  PoincareConjecture.ThreeSphere

private noncomputable abbrev threeSphereBasepoint : TopCat :=
  TopCat.of threeSphereType

private noncomputable abbrev threeSpherePoint : threeSphereType :=
  Classical.choice (NormedSpace.sphere_nonempty.mpr zero_le_one).coe_sort


theorem isZero_integral_threeSphere_homology_one :
      IsZero ((TopCat.toSSet.obj threeSphereBasepoint).homology
      (ModuleCat.of ℤ (ULift ℤ)) 1) := by
  let : SimplyConnectedSpace threeSphereType :=
    sphere_simplyConnectedSpace_of_two_lt_finrank (E := EuclideanSpace ℝ (Fin 4)) (by simp)
  exact isZero_integral_singularHomology_of_homotopy_vanishing
    threeSphereBasepoint threeSpherePoint 0 (by
      intro k hk hk1
      have hk' : k = 1 := by omega
      subst k
      exact sphere_homotopyGroup_subsingleton_of_dim_lt
        (N := Fin 1) (E := EuclideanSpace ℝ (Fin 4)) (by simp) threeSpherePoint)


theorem isZero_integral_threeSphere_homology_two :
      IsZero ((TopCat.toSSet.obj threeSphereBasepoint).homology
      (ModuleCat.of ℤ (ULift ℤ)) 2) := by
  let : SimplyConnectedSpace threeSphereType :=
    sphere_simplyConnectedSpace_of_two_lt_finrank (E := EuclideanSpace ℝ (Fin 4)) (by simp)
  exact isZero_integral_singularHomology_of_homotopy_vanishing
    threeSphereBasepoint threeSpherePoint 1 (by
      intro k hk hk2
      rcases k with _ | k
      · omega
      · rcases k with _ | k
        · exact sphere_homotopyGroup_subsingleton_of_dim_lt
            (N := Fin 1) (E := EuclideanSpace ℝ (Fin 4)) (by simp) threeSpherePoint
        · rcases k with _ | k
          · exact sphere_homotopyGroup_subsingleton_of_dim_lt
              (N := Fin 2) (E := EuclideanSpace ℝ (Fin 4)) (by simp) threeSpherePoint
          · omega)

end

end PoincareConjecture.Proofs.M02
