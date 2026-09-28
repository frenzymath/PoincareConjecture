import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Calculus.Tensors.RicciRegularity
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Calculus.Identities.CurvatureSymmetries
import Mathlib.LinearAlgebra.BilinearForm.Properties

set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture.RicciFlowAnalysis

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem nonneg_ricci_of_nonnegativeSectionalAt (D : LeviCivitaData g) (x : M)
    (hsec : ∀ v w : TangentSpace (𝓡 n) x, 0 ≤ D.curvatureTensor x v w v w)
    (v : TangentSpace (𝓡 n) x) : 0 ≤ D.ricci x v v := by
  exact Finset.sum_nonneg fun i _ ↦ hsec v (g.orthonormalBasis x i)

theorem nonneg_scalar_of_nonnegativeSectionalAt (D : LeviCivitaData g) (x : M)
    (hsec : ∀ v w : TangentSpace (𝓡 n) x, 0 ≤ D.curvatureTensor x v w v w) :
    0 ≤ D.scalarCurvature x := by
  exact Finset.sum_nonneg fun i _ ↦
    nonneg_ricci_of_nonnegativeSectionalAt D x hsec (g.orthonormalBasis x i)

set_option maxHeartbeats 600000 in

set_option backward.isDefEq.respectTransparency false in
theorem curvatureTensor_eq_zero_of_nonnegativeSectionalAt_scalar_zero
    (D : LeviCivitaData g) (x : M)
    (hsec : ∀ v w : TangentSpace (𝓡 n) x, 0 ≤ D.curvatureTensor x v w v w)
    (hscalar : D.scalarCurvature x = 0)
    (u v w z : TangentSpace (𝓡 n) x) : D.curvatureTensor x u v w z = 0 := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let E := TangentSpace (𝓡 n) x
  let b := g.orthonormalBasis x
  have hzero (B : LinearMap.BilinForm ℝ E) (hB : B.IsSymm)
      (hp : ∀ a, 0 ≤ B a a) (ht : ∑ i, B (b i) (b i) = 0) :
      ∀ a c, B a c = 0 := by
    have hd := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ ↦ hp (b i))).mp ht
    have hk (i : Fin (Module.finrank ℝ E)) : B (b i) = 0 := by
      exact LinearMap.mem_ker.mp ((B.apply_apply_same_eq_zero_iff hp
        (LinearMap.BilinForm.isSymm_iff.mp hB)).mp
        (hd i (Finset.mem_univ i)))
    intro a c
    rw [← b.sum_repr a, map_sum]
    simp only [map_smul, hk,
      LinearMap.zero_apply, smul_zero, Finset.sum_const_zero]
  obtain ⟨A, hA⟩ := (isSmoothCovariantTensor_ricciEvaluation D).1 x
  have hRic (a c : E) : D.ricci x a c = A ![a, c] := hA ![a, c]
  have hu0 (a c d : E) : Function.update ![a, c] 0 d = ![d, c] := by
    ext i
    fin_cases i <;> simp [Function.update]
  have hu1 (a c d : E) : Function.update ![a, c] 1 d = ![a, d] := by
    ext i
    fin_cases i <;> simp [Function.update]
  have hra1 (a c d : E) : D.ricci x (a + c) d = D.ricci x a d + D.ricci x c d := by
    simp only [hRic]
    simpa only [hu0] using A.map_update_add ![a, d] 0 a c
  have hra2 (a c d : E) : D.ricci x d (a + c) = D.ricci x d a + D.ricci x d c := by
    simp only [hRic]
    simpa only [hu1] using A.map_update_add ![d, a] 1 a c
  have hrs1 (s : ℝ) (a c : E) : D.ricci x (s • a) c = s • D.ricci x a c := by
    simp only [hRic]
    simpa only [hu0] using A.map_update_smul ![a, c] 0 s a
  have hrs2 (s : ℝ) (a c : E) : D.ricci x a (s • c) = s • D.ricci x a c := by
    simp only [hRic]
    simpa only [hu1] using A.map_update_smul ![a, c] 1 s c
  let B : LinearMap.BilinForm ℝ E :=
    { toFun := fun a ↦
        { toFun := fun c ↦ D.ricci x a c
          map_add' := fun c d ↦ hra2 c d a
          map_smul' := fun s c ↦ hrs2 s a c }
      map_add' := by intro a c; ext d; exact hra1 a c d
      map_smul' := by intro s a; ext c; exact hrs1 s a c }
  have hBsymm : B.IsSymm := ⟨fun a c ↦ ricci_symm D x a c⟩
  have hBpos (a : E) : 0 ≤ B a a := nonneg_ricci_of_nonnegativeSectionalAt D x hsec a
  have hRicZero (a c : E) : D.ricci x a c = 0 := hzero B hBsymm hBpos hscalar a c
  obtain ⟨T, hT⟩ := (isSmoothCovariantTensor_riemannEvaluation D).1 x
  have hR (a c d e : E) : D.curvatureTensor x a c d e = T ![a, c, d, e] :=
    hT ![a, c, d, e]
  have hv0 (a c d e f : E) : Function.update ![a, c, d, e] 0 f = ![f, c, d, e] := by
    ext i
    fin_cases i <;> simp [Function.update]
  have hv1 (a c d e f : E) : Function.update ![a, c, d, e] 1 f = ![a, f, d, e] := by
    ext i
    fin_cases i <;> simp [Function.update]
  have hv2 (a c d e f : E) : Function.update ![a, c, d, e] 2 f = ![a, c, f, e] := by
    ext i
    fin_cases i <;> simp [Function.update]
  have hv3 (a c d e f : E) : Function.update ![a, c, d, e] 3 f = ![a, c, d, f] := by
    ext i
    fin_cases i <;> simp [Function.update]
  have hRa0 (a a' c d e : E) : D.curvatureTensor x (a + a') c d e =
      D.curvatureTensor x a c d e + D.curvatureTensor x a' c d e := by
    simp only [hR]
    simpa only [hv0] using T.map_update_add ![a, c, d, e] 0 a a'
  have hRa1 (a c c' d e : E) : D.curvatureTensor x a (c + c') d e =
      D.curvatureTensor x a c d e + D.curvatureTensor x a c' d e := by
    simp only [hR]
    simpa only [hv1] using T.map_update_add ![a, c, d, e] 1 c c'
  have hRa2 (a c d d' e : E) : D.curvatureTensor x a c (d + d') e =
      D.curvatureTensor x a c d e + D.curvatureTensor x a c d' e := by
    simp only [hR]
    simpa only [hv2] using T.map_update_add ![a, c, d, e] 2 d d'
  have hRa3 (a c d e e' : E) : D.curvatureTensor x a c d (e + e') =
      D.curvatureTensor x a c d e + D.curvatureTensor x a c d e' := by
    simp only [hR]
    simpa only [hv3] using T.map_update_add ![a, c, d, e] 3 e e'
  have hRs1 (s : ℝ) (a c d e : E) : D.curvatureTensor x a (s • c) d e =
      s • D.curvatureTensor x a c d e := by
    simp only [hR]
    simpa only [hv1] using T.map_update_smul ![a, c, d, e] 1 s c
  have hRs3 (s : ℝ) (a c d e : E) : D.curvatureTensor x a c d (s • e) =
      s • D.curvatureTensor x a c d e := by
    simp only [hR]
    simpa only [hv3] using T.map_update_smul ![a, c, d, e] 3 s e
  have hrepeat (a c e : E) : D.curvatureTensor x a c a e = 0 := by
    let C : LinearMap.BilinForm ℝ E :=
      { toFun := fun v ↦
          { toFun := fun z ↦ D.curvatureTensor x a v a z
            map_add' := fun z z' ↦ hRa3 a v a z z'
            map_smul' := fun s z ↦ hRs3 s a v a z }
        map_add' := by intro v v'; ext z; exact hRa1 a v v' a z
        map_smul' := by intro s v; ext z; exact hRs1 s a v a z }
    have hCsymm : C.IsSymm := ⟨fun v z ↦ curvatureTensor_pair_exchange D x a v a z⟩
    have hCpos (v : E) : 0 ≤ C v v := hsec a v
    exact hzero C hCsymm hCpos (hRicZero a a) c e
  have hpolar (a c d e : E) :
      D.curvatureTensor x a c d e + D.curvatureTensor x d c a e = 0 := by
    have h := hrepeat (a + d) c e
    rw [hRa0, hRa2, hRa2, hrepeat, hrepeat] at h
    simpa only [zero_add, add_zero] using h
  have hp1 := hpolar u v w z
  have hp2 := hpolar v w u z
  have hs1 := curvatureTensor_swap_first D x w v u z
  have hs2 := curvatureTensor_swap_first D x u w v z
  have hc := curvatureTensor_cyclic D x u v w z
  linarith only [hp1, hp2, hs1, hs2, hc]

theorem curvatureTensorNorm_eq_zero_of_nonnegativeSectionalAt_scalar_zero
    (D : LeviCivitaData g) (x : M)
    (hsec : ∀ v w : TangentSpace (𝓡 n) x, 0 ≤ D.curvatureTensor x v w v w)
    (hscalar : D.scalarCurvature x = 0) : D.curvatureTensorNorm x = 0 := by
  simp [LeviCivitaData.curvatureTensorNorm,
    curvatureTensor_eq_zero_of_nonnegativeSectionalAt_scalar_zero D x hsec hscalar]

end PoincareConjecture.RicciFlowAnalysis
