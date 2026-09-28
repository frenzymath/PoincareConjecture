import PoincareConjecture.Statements.Ch04.Pinching
import PoincareConjecture.Proofs.M01.Curvature
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum














set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]

open LeviCivitaData

theorem m01_tangentSpace_finrank [IsManifold (𝓡 3) ∞ M] (x : M) :
    Module.finrank ℝ (TangentSpace (𝓡 3) x) = 3 := by
  change Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3
  simp

variable [IsManifold (𝓡 3) ∞ M] {g : RiemannianMetric 3 M}

theorem m01_curvatureTensor_self (D : LeviCivitaData g) (x : M)
    (u w z : TangentSpace (𝓡 3) x) : D.curvatureTensor x u u w z = 0 := by
  have h := D.m01_curvature_swap x u u z
  have hneg : D.curvatureTensor x u u w z = -D.curvatureTensor x u u w z := by
    unfold curvatureTensor
    conv_lhs => rw [h]
    simp
  linarith

theorem m01_orthonormalPair_exists (x : M) :
    ∃ u v : TangentSpace (𝓡 3) x, IsOrthonormalPair g x u v := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let b := g.orthonormalBasis x
  let i : Fin (Module.finrank ℝ (TangentSpace (𝓡 3) x)) :=
    ⟨0, by rw [m01_tangentSpace_finrank]; decide⟩
  let j : Fin (Module.finrank ℝ (TangentSpace (𝓡 3) x)) :=
    ⟨1, by rw [m01_tangentSpace_finrank]; decide⟩
  have hij : i ≠ j := by
    intro h
    have := congrArg Fin.val h
    norm_num [i, j] at this
  refine ⟨b i, b j, ?_, ?_, ?_⟩
  · exact b.inner_eq_ite i i |>.trans (if_pos rfl)
  · exact b.inner_eq_ite j j |>.trans (if_pos rfl)
  · exact b.inner_eq_ite i j |>.trans (if_neg hij)

theorem m01_scalarCurvature_lower_bound (D : LeviCivitaData g) (x : M) (k : ℝ)
    (hk : ∀ u v : TangentSpace (𝓡 3) x, IsOrthonormalPair g x u v →
      k ≤ D.curvatureTensor x u v u v) :
    6 * k ≤ D.scalarCurvature x := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let b := g.orthonormalBasis x
  have hterm (i j : Fin (Module.finrank ℝ (TangentSpace (𝓡 3) x))) :
      k - (if i = j then k else 0) ≤ D.curvatureTensor x (b i) (b j) (b i) (b j) := by
    by_cases hij : i = j
    · subst j
      simp [m01_curvatureTensor_self]
    · rw [if_neg hij, sub_zero]
      apply hk
      exact ⟨b.inner_eq_ite i i |>.trans (if_pos rfl),
        b.inner_eq_ite j j |>.trans (if_pos rfl),
        b.inner_eq_ite i j |>.trans (if_neg hij)⟩
  have hsum := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => Finset.sum_le_sum (s := Finset.univ) (fun j _ => hterm i j))
  have hleft :
      (∑ i : Fin (Module.finrank ℝ (TangentSpace (𝓡 3) x)),
        ∑ j : Fin (Module.finrank ℝ (TangentSpace (𝓡 3) x)),
          (k - if i = j then k else 0)) = 6 * k := by
    simp [Finset.sum_sub_distrib, m01_tangentSpace_finrank]
    ring
  rw [hleft] at hsum
  exact hsum

theorem m01HamiltonIveyPinchedAt_zero (D : LeviCivitaData g)
    (hsec : ∀ x u v, IsOrthonormalPair g x u v →
      (-1 : ℝ) ≤ D.curvatureTensor x u v u v) :
    HamiltonIveyPinchedAt D 0 := by
  have hbdd (x : M) : BddBelow {k : ℝ | ∃ u v : TangentSpace (𝓡 3) x,
      IsOrthonormalPair g x u v ∧ k = D.curvatureTensor x u v u v} := by
    refine ⟨-1, ?_⟩
    rintro k ⟨u, v, huv, rfl⟩
    exact hsec x u v huv
  have hleast (x : M) : -1 ≤ D.leastSectionalCurvature x := by
    apply le_csInf
    · obtain ⟨u, v, huv⟩ := m01_orthonormalPair_exists (g := g) x
      exact ⟨D.curvatureTensor x u v u v, u, v, huv, rfl⟩
    · rintro k ⟨u, v, huv, rfl⟩
      exact hsec x u v huv
  have hscalar (x : M) : 6 * D.leastSectionalCurvature x ≤ D.scalarCurvature x := by
    apply m01_scalarCurvature_lower_bound
    intro u v huv
    exact csInf_le (hbdd x) ⟨u, v, huv, rfl⟩
  refine ⟨le_rfl, ?_, ?_⟩
  · intro x
    have := m01_scalarCurvature_lower_bound D x (-1) (hsec x)
    norm_num at this ⊢
    exact this
  · intro x hx
    have hX : D.negativeCurvaturePart x ≤ 1 := by
      dsimp [negativeCurvaturePart]
      exact max_le (by linarith [hleast x]) zero_le_one
    have hlog : Real.log (D.negativeCurvaturePart x) ≤ 0 :=
      Real.log_nonpos hx.le hX
    have hdef : -D.negativeCurvaturePart x ≤ D.leastSectionalCurvature x := by
      have := le_max_left (-D.leastSectionalCurvature x) (0 : ℝ)
      change -D.negativeCurvaturePart x ≤ D.leastSectionalCurvature x
      dsimp [negativeCurvaturePart]
      linarith
    have hmul := mul_nonpos_of_nonneg_of_nonpos hx.le hlog
    norm_num only [add_zero, Real.log_one] at *
    nlinarith [hscalar x]

end PoincareConjecture
