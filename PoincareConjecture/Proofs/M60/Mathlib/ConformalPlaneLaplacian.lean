import PoincareConjecture.Proofs.M60.Mathlib.SecondDerivativeChain
import PoincareConjecture.Proofs.M60.Mathlib.ConformalTrace
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false

open Filter
open scoped Topology ContDiff BigOperators

namespace PoincareConjecture.M60

local notation "E" => EuclideanSpace ℝ (Fin 2)

theorem laplacian_eq_zero_of_conformal_plane
    {φ : E → E} {z : E} (hφ : ContDiffAt ℝ 2 φ z)
    (hsurj : Function.Surjective (fderiv ℝ φ z))
    (hself : (fun q => inner ℝ
      (fderiv ℝ φ q (EuclideanSpace.basisFun (Fin 2) ℝ 0))
      (fderiv ℝ φ q (EuclideanSpace.basisFun (Fin 2) ℝ 0))) =ᶠ[𝓝 z]
      (fun q => inner ℝ (fderiv ℝ φ q (EuclideanSpace.basisFun (Fin 2) ℝ 1))
        (fderiv ℝ φ q (EuclideanSpace.basisFun (Fin 2) ℝ 1))))
    (horth : (fun q => inner ℝ
      (fderiv ℝ φ q (EuclideanSpace.basisFun (Fin 2) ℝ 0))
      (fderiv ℝ φ q (EuclideanSpace.basisFun (Fin 2) ℝ 1))) =ᶠ[𝓝 z] (fun _ => 0)) :
    fderiv ℝ (fderiv ℝ φ) z (EuclideanSpace.basisFun (Fin 2) ℝ 0)
        (EuclideanSpace.basisFun (Fin 2) ℝ 0) +
      fderiv ℝ (fderiv ℝ φ) z (EuclideanSpace.basisFun (Fin 2) ℝ 1)
        (EuclideanSpace.basisFun (Fin 2) ℝ 1) = 0 := by
  let e := EuclideanSpace.basisFun (Fin 2) ℝ
  let Y := fun q => fderiv ℝ φ q (e 0)
  let Z := fun q => fderiv ℝ φ q (e 1)
  let H := fderiv ℝ (fderiv ℝ φ) z
  have hd := hφ.fderiv_right (m := 1) (by norm_num)
  have hY : DifferentiableAt ℝ Y z := (hd.clm_apply contDiffAt_const).differentiableAt (by simp)
  have hZ : DifferentiableAt ℝ Z z := (hd.clm_apply contDiffAt_const).differentiableAt (by simp)
  have hsym : H (e 1) (e 0) = H (e 0) (e 1) :=
    (hφ.isSymmSndFDerivAt (by norm_num)).eq _ _
  have hlen (d : E) :
      2 * inner ℝ (fderiv ℝ Y z d) (Y z) =
        2 * inner ℝ (fderiv ℝ Z z d) (Z z) := by
    have h := congrArg (fun L : E →L[ℝ] ℝ => L d) hself.fderiv_eq
    rw [fderiv_inner_apply ℝ hY hY, fderiv_inner_apply ℝ hZ hZ] at h
    rw [real_inner_comm (fderiv ℝ Y z d) (Y z),
      real_inner_comm (fderiv ℝ Z z d) (Z z)] at h
    linarith
  have hort (d : E) : inner ℝ (fderiv ℝ Y z d) (Z z) +
      inner ℝ (Y z) (fderiv ℝ Z z d) = 0 := by
    have h := congrArg (fun L : E →L[ℝ] ℝ => L d) horth.fderiv_eq
    rw [fderiv_inner_apply ℝ hY hZ, fderiv_const_apply, zero_apply] at h
    linarith
  have hlen0 := hlen (e 0)
  have hlen1 := hlen (e 1)
  have hort0 := hort (e 0)
  have hort1 := hort (e 1)
  dsimp only [Y, Z] at hlen0 hlen1 hort0 hort1
  simp only [fderiv_column hφ] at hlen0 hlen1 hort0 hort1
  change 2 * inner ℝ (H (e 0) (e 0)) (Y z) =
    2 * inner ℝ (H (e 0) (e 1)) (Z z) at hlen0
  change 2 * inner ℝ (H (e 1) (e 0)) (Y z) =
    2 * inner ℝ (H (e 1) (e 1)) (Z z) at hlen1
  change inner ℝ (H (e 0) (e 0)) (Z z) + inner ℝ (Y z) (H (e 0) (e 1)) = 0 at hort0
  change inner ℝ (H (e 1) (e 0)) (Z z) + inner ℝ (Y z) (H (e 1) (e 1)) = 0 at hort1
  rw [hsym] at hlen1 hort1
  rw [real_inner_comm (H (e 0) (e 1)) (Y z)] at hort0
  rw [real_inner_comm (H (e 1) (e 1)) (Y z)] at hort1
  let L := H (e 0) (e 0) + H (e 1) (e 1)
  have hLY : inner ℝ L (Y z) = 0 := by dsimp only [L]; rw [inner_add_left]; linarith
  have hLZ : inner ℝ L (Z z) = 0 := by dsimp only [L]; rw [inner_add_left]; linarith
  obtain ⟨v, hv⟩ := hsurj L
  have hv' : v = v 0 • e 0 + v 1 • e 1 := by
    ext i
    fin_cases i <;> simp [e, EuclideanSpace.basisFun_apply]
  have hLL : inner ℝ L L = 0 := by
    calc
      _ = inner ℝ L (fderiv ℝ φ z v) := congrArg (inner ℝ L) hv.symm
      _ = 0 := by
        rw [hv', map_add, map_smul, map_smul, inner_add_right,
      real_inner_smul_right, real_inner_smul_right, hLY, hLZ]
        simp
  exact (inner_self_eq_zero.mp hLL : L = 0)

theorem covariant_laplacian_comp_eq_zero {n : ℕ}
    {u : E → EuclideanSpace ℝ (Fin n)} {φ : E → E} {z : E}
    (Γ : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ]
        EuclideanSpace ℝ (Fin n))
    (hu : ContDiffAt ℝ 2 u (φ z)) (hφ : ContDiffAt ℝ 2 φ z)
    {a : ℝ} (ha : 0 < a)
    (hgram : ∀ i j : Fin 2, inner ℝ
      (fderiv ℝ φ z (EuclideanSpace.basisFun (Fin 2) ℝ i))
      (fderiv ℝ φ z (EuclideanSpace.basisFun (Fin 2) ℝ j)) =
        a * (if i = j then 1 else 0))
    (hlap : fderiv ℝ (fderiv ℝ φ) z (EuclideanSpace.basisFun (Fin 2) ℝ 0)
        (EuclideanSpace.basisFun (Fin 2) ℝ 0) +
      fderiv ℝ (fderiv ℝ φ) z (EuclideanSpace.basisFun (Fin 2) ℝ 1)
        (EuclideanSpace.basisFun (Fin 2) ℝ 1) = 0)
    (hτ : let e := EuclideanSpace.basisFun (Fin 2) ℝ
      fderiv ℝ (fderiv ℝ u) (φ z) (e 0) (e 0) +
        fderiv ℝ (fderiv ℝ u) (φ z) (e 1) (e 1) +
        Γ (u (φ z)) (fderiv ℝ u (φ z) (e 0)) (fderiv ℝ u (φ z) (e 0)) +
        Γ (u (φ z)) (fderiv ℝ u (φ z) (e 1)) (fderiv ℝ u (φ z) (e 1)) = 0) :
    let e := EuclideanSpace.basisFun (Fin 2) ℝ
    fderiv ℝ (fderiv ℝ (u ∘ φ)) z (e 0) (e 0) +
      fderiv ℝ (fderiv ℝ (u ∘ φ)) z (e 1) (e 1) +
      Γ ((u ∘ φ) z) (fderiv ℝ (u ∘ φ) z (e 0)) (fderiv ℝ (u ∘ φ) z (e 0)) +
      Γ ((u ∘ φ) z) (fderiv ℝ (u ∘ φ) z (e 1)) (fderiv ℝ (u ∘ φ) z (e 1)) = 0 := by
  let e := EuclideanSpace.basisFun (Fin 2) ℝ
  let F := EuclideanSpace ℝ (Fin n)
  let L := fderiv ℝ u (φ z)
  let T := fderiv ℝ (fderiv ℝ u) (φ z) + (Γ (u (φ z))).bilinearComp L L
  let Q := fderiv ℝ φ z
  have hT : T (e 0) (e 0) + T (e 1) (e 1) = 0 := by
    simp only [T, add_apply, ContinuousLinearMap.bilinearComp_apply]
    convert hτ using 1
    abel
  have ht : T (Q (e 0)) (Q (e 0)) + T (Q (e 1)) (Q (e 1)) = 0 := by
    ext k
    let C := EuclideanSpace.proj (𝕜 := ℝ) k
    let B := ((ContinuousLinearMap.compL ℝ E F ℝ C).comp T).toBilinForm
    have hb := sum_bilinear_conformal_basis B e (fun i => Q (e i))
      (by simp) ha hgram
    have hz := congrArg C hT
    simp only [map_add, map_zero] at hz
    change C (T (e 0) (e 0)) + C (T (e 1) (e 1)) = 0 at hz
    change C (T (Q (e 0)) (Q (e 0)) + T (Q (e 1)) (Q (e 1))) = 0
    rw [map_add]
    simpa only [Fin.sum_univ_two, B, ContinuousLinearMap.toBilinForm_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.compL_apply, hz, mul_zero] using hb
  dsimp only
  calc
    _ = (T (Q (e 0)) (Q (e 0)) + T (Q (e 1)) (Q (e 1))) +
        L (fderiv ℝ (fderiv ℝ φ) z (e 0) (e 0) +
          fderiv ℝ (fderiv ℝ φ) z (e 1) (e 1)) := by
      rw [second_fderiv_comp hu hφ, second_fderiv_comp hu hφ,
        fderiv_comp z (hu.differentiableAt (by simp)) (hφ.differentiableAt (by simp))]
      simp only [Function.comp_apply, ContinuousLinearMap.comp_apply,
        T, L, Q, add_apply, ContinuousLinearMap.bilinearComp_apply, map_add]
      abel
    _ = 0 := by rw [ht, hlap, map_zero, add_zero]

end PoincareConjecture.M60
