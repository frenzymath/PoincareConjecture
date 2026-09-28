import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryConformalInitialGain
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.SmoothDomain.HalfSpaceChart

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Function

namespace PoincareConjecture

theorem m64_exists_metric_tangent_frame {n : ℕ}
    (G : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ)
    (v : EuclideanSpace ℝ (Fin (n + 1))) (hv : 0 < G v v) :
    ∃ B : EuclideanSpace ℝ (Fin (n + 1)) ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 1)),
      B (EuclideanSpace.single 0 1) = v ∧
      ∀ z, G v (B z) = G v v * z 0 := by
  let E := EuclideanSpace ℝ (Fin (n + 1))
  let L : E →L[ℝ] ℝ := (G v v)⁻¹ • G v
  have hLv : L v = 1 := by
    change (G v v)⁻¹ * G v v = 1
    exact inv_mul_cancel₀ hv.ne'
  have hLs : Surjective L := by
    intro t
    refine ⟨t • v, ?_⟩
    rw [map_smul, hLv, smul_eq_mul, mul_one]
  have hdim := L.toLinearMap.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hLs, finrank_top, Module.finrank_self] at hdim
  have hdim' : 1 + Module.finrank ℝ L.ker = n + 1 := by
    simpa only [E, finrank_euclideanSpace_fin] using hdim
  have hker : Module.finrank ℝ L.ker = Module.finrank ℝ (Fin n → ℝ) := by
    rw [Module.finrank_fin_fun]
    omega
  let K : L.ker ≃L[ℝ] (Fin n → ℝ) := ContinuousLinearEquiv.ofFinrankEq hker
  let A : (ℝ × L.ker) ≃L[ℝ] E := ((ContinuousLinearEquiv.refl ℝ ℝ).prodCongr K).trans
    ((Fin.consEquivL ℝ (fun _ : Fin (n + 1) => ℝ)).trans
      (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin (n + 1))).symm)
  have hA (z : ℝ × L.ker) : A z 0 = z.1 := rfl
  have hAxis (t : ℝ) : A (t, 0) = EuclideanSpace.single 0 t := by
    ext i
    change Fin.cons (α := fun _ : Fin (n + 1) => ℝ) t (K 0) i = _
    rw [map_zero]
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simp
  let P : (ℝ × L.ker) →L[ℝ] E :=
    ((ContinuousLinearMap.id ℝ ℝ).smulRight v).coprod L.ker.subtypeL
  have hP (z : ℝ × L.ker) : P z = z.1 • v + z.2 := rfl
  have hLP (z : ℝ × L.ker) : L (P z) = z.1 := by
    rw [hP, map_add, map_smul, hLv, smul_eq_mul, mul_one]
    have hz : L (z.2 : E) = 0 := z.2.property
    rw [hz, add_zero]
  have hPb : Bijective P := by
    constructor
    · intro z w hzw
      have hfirst : z.1 = w.1 := by simpa only [hLP] using congrArg L hzw
      apply Prod.ext hfirst
      apply Subtype.ext
      have hh := hzw
      rw [hP, hP, hfirst] at hh
      exact add_left_cancel hh
    · intro z
      have hz : z - L z • v ∈ L.ker := by
        change L (z - L z • v) = 0
        rw [map_sub, map_smul, hLv, smul_eq_mul, mul_one, sub_self]
      refine ⟨(L z, ⟨z - L z • v, hz⟩), ?_⟩
      rw [hP]
      dsimp only
      abel
  let Q : (ℝ × L.ker) ≃L[ℝ] E :=
    (LinearEquiv.ofBijective P.toLinearMap hPb).toContinuousLinearEquiv
  let B := A.symm.trans Q
  have hQ (z : ℝ × L.ker) : Q z = P z := rfl
  refine ⟨B, ?_, ?_⟩
  · rw [← hAxis 1]
    change Q (A.symm (A (1, 0))) = v
    rw [A.symm_apply_apply, hQ, hP]
    simp
  · intro z
    have hh := hLP (A.symm z)
    have hfirst : (A.symm z).1 = z 0 := by
      rw [← hA, A.apply_symm_apply]
    rw [hfirst] at hh
    change (G v v)⁻¹ * G v (B z) = z 0 at hh
    have he := congrArg (fun t : ℝ => G v v * t) hh
    simpa only [← mul_assoc, mul_inv_cancel₀ hv.ne', one_mul] using he

end PoincareConjecture
