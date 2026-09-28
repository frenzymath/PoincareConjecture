import PoincareConjecture.Proofs.M76.Mathlib.SimplexOppositeApices
import Mathlib.LinearAlgebra.Determinant

set_option autoImplicit false

open Set

namespace PoincareConjecture.M76.HamiltonIndexOne

variable {ι E : Type*} [Finite ι]
  [AddCommGroup E] [Module ℝ E]

private theorem det_eq_repr_of_fixed_basis_except
    (v : Module.Basis ι ℝ E) (i : ι) (a : E →ₗ[ℝ] E)
    (hfix : ∀ j, j ≠ i → a (v j) = v j) :
    LinearMap.det a = v.repr (a (v i)) i := by
  classical
  let := Fintype.ofFinite ι
  have hm : LinearMap.toMatrix v v a =
      (1 : Matrix ι ι ℝ).updateCol i (v.repr (a (v i))) := by
    ext j k
    by_cases hki : k = i
    · subst k
      simp only [LinearMap.toMatrix_apply, Matrix.updateCol_self]
    · rw [LinearMap.toMatrix_apply, hfix k hki, Matrix.updateCol_ne hki]
      simp only [v.repr_self, Finsupp.single_apply, Matrix.one_apply, eq_comm]
  rw [← LinearMap.det_toMatrix v a, hm]
  have h := Matrix.det_updateCol_sum (1 : Matrix ι ι ℝ) i (v.repr (a (v i)))
  simpa [Matrix.one_apply] using h

omit [Finite ι] in
private theorem affine_coord_eq_basis_coord (b : AffineBasis ι ℝ E)
    (i j : ι) (hij : i ≠ j) (q : E) :
    (b.basisOf j).repr (q - b j) ⟨i, hij⟩ = b.coord i q := by
  classical
  let c : E →ᵃ[ℝ] ℝ :=
    ((b.basisOf j).coord ⟨i, hij⟩).toAffineMap.comp
      (AffineMap.id ℝ E - AffineMap.const ℝ E (b j))
  have hc : c = b.coord i := by
    apply AffineMap.ext_on b.tot
    rintro _ ⟨k, rfl⟩
    by_cases hkj : k = j
    · subst k
      simp only [c, AffineMap.comp_apply, LinearMap.coe_toAffineMap,
        AffineMap.coe_sub, Pi.sub_apply, AffineMap.id_apply,
        AffineMap.const_apply, sub_self, map_zero, b.coord_apply_ne hij]
    · change (b.basisOf j).repr (b k -ᵥ b j) ⟨i, hij⟩ = b.coord i (b k)
      rw [← b.basisOf_apply j ⟨k, hkj⟩, (b.basisOf j).repr_self]
      simp only [Finsupp.single_apply, b.coord_apply, Subtype.mk.injEq, eq_comm]
  exact congrArg (fun f : E →ᵃ[ℝ] ℝ => f q) hc

theorem det_eq_coord_of_fixes_affine_facet (b : AffineBasis ι ℝ E)
    (i j : ι) (hij : i ≠ j) (a : E →ᵃ[ℝ] E)
    (hfix : ∀ k, k ≠ i → a (b k) = b k) :
    LinearMap.det a.linear = b.coord i (a (b i)) := by
  classical
  have hbase : a (b j) = b j := hfix j hij.symm
  have hfixed (k : {k : ι // k ≠ j}) (hk : k ≠ ⟨i, hij⟩) :
      a.linear (b.basisOf j k) = b.basisOf j k := by
    have hki : (k : ι) ≠ i := fun h => hk (Subtype.ext h)
    rw [b.basisOf_apply, a.linearMap_vsub, hfix k hki, hbase]
  have h := det_eq_repr_of_fixed_basis_except (b.basisOf j) ⟨i, hij⟩ a.linear hfixed
  rw [b.basisOf_apply, a.linearMap_vsub, hbase] at h
  exact h.trans (affine_coord_eq_basis_coord b i j hij (a (b i)))

theorem det_mul_coord_of_fixes_affine_facet (b : AffineBasis ι ℝ E)
    (i j : ι) (hij : i ≠ j) (a : E →ᵃ[ℝ] E)
    (hfix : ∀ k, k ≠ i → a (b k) = b k) (q : E) :
    LinearMap.det a.linear * b.coord i q = b.coord i (a q) := by
  classical
  have he : (b.coord i).comp a = b.coord i (a (b i)) • b.coord i := by
    apply AffineMap.ext_on b.tot
    rintro _ ⟨k, rfl⟩
    change b.coord i (a (b k)) = b.coord i (a (b i)) * b.coord i (b k)
    by_cases hki : k = i
    · subst k
      rw [b.coord_apply_eq, mul_one]
    · rw [hfix k hki, b.coord_apply_ne (Ne.symm hki), mul_zero]
  rw [det_eq_coord_of_fixes_affine_facet b i j hij a hfix]
  exact (congrArg (fun f : E →ᵃ[ℝ] ℝ => f q) he).symm

theorem same_det_sign_of_opposite_facet_coordinates
    (b : AffineBasis ι ℝ E) (i j : ι) (hij : i ≠ j)
    (A B : E ≃ᵃ[ℝ] E)
    (hagree : ∀ k, k ≠ i → B (b k) = A (b k))
    (q : E) (hq : b.coord i q < 0)
    (himage : b.coord i (A.symm (B q)) < 0) :
    0 < LinearMap.det (A.linear : E →ₗ[ℝ] E) *
      LinearMap.det (B.linear : E →ₗ[ℝ] E) := by
  let C := A.symm.toAffineMap.comp B.toAffineMap
  have hfix (k : ι) (hk : k ≠ i) : C (b k) = b k := by
    change A.symm (B (b k)) = b k
    rw [hagree k hk, A.symm_apply_apply]
  have hc := det_mul_coord_of_fixes_affine_facet b i j hij C hfix q
  have hcpos : 0 < LinearMap.det C.linear := by
    by_contra h
    have hn := mul_nonneg_of_nonpos_of_nonpos (le_of_not_gt h) hq.le
    rw [hc] at hn
    exact (not_lt_of_ge hn) himage
  have hdet : LinearMap.det C.linear =
      LinearMap.det (A.linear.symm : E →ₗ[ℝ] E) *
        LinearMap.det (B.linear : E →ₗ[ℝ] E) := by
    exact LinearMap.det_comp _ _
  have hmul : LinearMap.det C.linear * LinearMap.det (A.linear : E →ₗ[ℝ] E) =
      LinearMap.det (B.linear : E →ₗ[ℝ] E) := by
    rw [hdet]
    calc
      _ = (LinearMap.det (A.linear.symm : E →ₗ[ℝ] E) *
          LinearMap.det (A.linear : E →ₗ[ℝ] E)) *
          LinearMap.det (B.linear : E →ₗ[ℝ] E) := by ring
      _ = _ := by rw [A.linear.det_symm_mul_det, one_mul]
  have hAne : LinearMap.det (A.linear : E →ₗ[ℝ] E) ≠ 0 := A.linear.isUnit_det'.ne_zero
  have hpos := mul_pos hcpos (sq_pos_of_ne_zero hAne)
  rw [← hmul]
  nlinarith

end PoincareConjecture.M76.HamiltonIndexOne
