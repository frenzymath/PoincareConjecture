import PoincareConjecture.Proofs.M04.RiemannRegularity
import Mathlib.LinearAlgebra.Trace





set_option autoImplicit false

open scoped Manifold ContDiff Bundle
open Topology Filter

universe u

namespace PoincareConjecture.M04

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

set_option maxHeartbeats 400000 in

set_option backward.isDefEq.respectTransparency false in
theorem contMDiffOn_ricci (D : LeviCivitaData g)
    {U : Set M} (hU : IsOpen U) {X Y : (x : M) → TangentSpace (𝓡 n) x}
    (hX : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% X) U)
    (hY : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% Y) U) :
    ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun y ↦ D.ricci y (X y) (Y y)) U := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hTensor := isSmoothCovariantTensor_riemannEvaluation D
  choose T hT using hTensor.1
  let R := fun y a b ↦ D.curvatureTensor y (X y) a (Y y) b
  have hRT (y : M) (a b : TangentSpace (𝓡 n) y) :
      R y a b = T y ![X y, a, Y y, b] := hT y ![X y, a, Y y, b]
  have hUpdate1 {y : M} (a b c d z : TangentSpace (𝓡 n) y) :
      Function.update ![a, b, c, d] 1 z = ![a, z, c, d] := by
    ext i
    fin_cases i <;> simp [Function.update]
  have hUpdate3 {y : M} (a b c d z : TangentSpace (𝓡 n) y) :
      Function.update ![a, b, c, d] 3 z = ![a, b, c, z] := by
    ext i
    fin_cases i <;> simp [Function.update]
  have hRa (y : M) (a b z : TangentSpace (𝓡 n) y) :
      R y (a + b) z = R y a z + R y b z := by
    simp only [hRT]
    simpa only [hUpdate1] using (T y).map_update_add ![X y, a, Y y, z] 1 a b
  have hRb (y : M) (a b z : TangentSpace (𝓡 n) y) :
      R y z (a + b) = R y z a + R y z b := by
    simp only [hRT]
    simpa only [hUpdate3] using (T y).map_update_add ![X y, z, Y y, a] 3 a b
  have hRs1 (y : M) (c : ℝ) (a b : TangentSpace (𝓡 n) y) :
      R y (c • a) b = c • R y a b := by
    simp only [hRT]
    simpa only [hUpdate1] using (T y).map_update_smul ![X y, a, Y y, b] 1 c a
  have hRs2 (y : M) (c : ℝ) (a b : TangentSpace (𝓡 n) y) :
      R y a (c • b) = c • R y a b := by
    simp only [hRT]
    simpa only [hUpdate3] using (T y).map_update_smul ![X y, a, Y y, b] 3 c b
  intro x hx
  apply ContMDiffAt.contMDiffWithinAt
  let E := EuclideanSpace ℝ (Fin n)
  let t := trivializationAt E (TangentSpace (𝓡 n) : M → Type _) x
  let O := U ∩ t.baseSet
  have hO : IsOpen O := hU.inter t.open_baseSet
  have hxT : x ∈ t.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  have hxO : x ∈ O := ⟨hx, hxT⟩
  let S := fun y ↦ t.symmL ℝ y
  have hSext (v : E) {y : M} (hy : y ∈ t.baseSet) :
      FiberBundle.extend E (S x v) y = S y v := by
    change t.symm y (t ⟨x, t.symmL ℝ x v⟩).2 = t.symmL ℝ y v
    rw [← Bundle.Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) t hxT,
      t.continuousLinearMapAt_symmL hxT, t.symmL_apply hy]
  have hS (v : E) :
      ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, E)) ∞ (T% (fun y ↦ S y v)) t.baseSet := by
    apply (contMDiffOn_extend_baseSet (S x v)).congr
    intro y hy
    exact congrArg (Bundle.TotalSpace.mk y) (hSext v hy).symm
  let B : M → E →L[ℝ] E →L[ℝ] ℝ := fun y ↦
    (g.inner y).bilinearComp (S y) (S y)
  let C : M → E →L[ℝ] E →L[ℝ] ℝ := fun y ↦
    LinearMap.toContinuousLinearMap
      { toFun := fun v ↦ LinearMap.toContinuousLinearMap
          { toFun := fun w ↦ R y (S y v) (S y w)
            map_add' := by intro a b; rw [map_add, hRb]
            map_smul' := by intro c a; rw [map_smul, hRs2]; rfl }
        map_add' := by
          intro a b
          ext w
          change R y (S y (a + b)) (S y w) = R y (S y a) (S y w) + R y (S y b) (S y w)
          rw [map_add, hRa]
        map_smul' := by
          intro c a
          ext w
          change R y (S y (c • a)) (S y w) = c • R y (S y a) (S y w)
          rw [map_smul, hRs1] }
  have hB : ContMDiffAt (𝓡 n) 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) ∞ B x := by
    apply contMDiffAt_clm_of_apply
    intro v
    apply contMDiffAt_clm_of_apply
    intro w
    exact ((hS v).inner_bundle (hS w)).contMDiffAt (t.open_baseSet.mem_nhds hxT)
  have hC : ContMDiffAt (𝓡 n) 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) ∞ C x := by
    apply contMDiffAt_clm_of_apply
    intro v
    apply contMDiffAt_clm_of_apply
    intro w
    let V : Fin 4 → (y : M) → TangentSpace (𝓡 n) y :=
      ![X, fun y ↦ S y v, Y, fun y ↦ S y w]
    have hV (i : Fin 4) :
        ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, E)) ∞ (T% (V i)) O := by
      fin_cases i
      · exact hX.mono Set.inter_subset_left
      · exact (hS v).mono Set.inter_subset_right
      · exact hY.mono Set.inter_subset_left
      · exact (hS w).mono Set.inter_subset_right
    exact (hTensor.2 O hO V hV).contMDiffAt (hO.mem_nhds hxO)
  let Q := (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv
  let A : M → E →L[ℝ] E := fun y ↦ Q.toContinuousLinearMap.comp (B y)
  let H : M → E →L[ℝ] E := fun y ↦ Q.toContinuousLinearMap.comp (C y)
  have hA : ContMDiffAt (𝓡 n) 𝓘(ℝ, E →L[ℝ] E) ∞ A x :=
    contMDiffAt_const.clm_comp hB
  have hH : ContMDiffAt (𝓡 n) 𝓘(ℝ, E →L[ℝ] E) ∞ H x :=
    contMDiffAt_const.clm_comp hC
  have hInv {y : M} (hy : y ∈ t.baseSet) : (A y).IsInvertible := by
    have hz (v : E) (hv : A y v = 0) : v = 0 := by
      have hBv : B y v = 0 := Q.injective (by simpa [A] using hv)
      have hi : g.inner y (S y v) (S y v) = 0 := by
        simpa [B] using congrArg (fun L : E →L[ℝ] ℝ ↦ L v) hBv
      have hSv : S y v = 0 := by
        by_contra hne
        exact (ne_of_gt (g.pos y _ hne)) hi
      have hv' := congrArg (t.continuousLinearMapAt ℝ y) hSv
      simpa only [S, t.continuousLinearMapAt_symmL hy, map_zero] using hv'
    have hinj : Function.Injective (A y) := by
      intro v w h
      apply sub_eq_zero.mp
      apply hz
      rw [map_sub, h, sub_self]
    have hsurj : Function.Surjective (A y) := (LinearMap.injective_iff_surjective).mp hinj
    exact ⟨(LinearEquiv.ofBijective (A y).toLinearMap ⟨hinj, hsurj⟩).toContinuousLinearEquiv,
      by ext v; rfl⟩
  let L := fun y ↦ (A y).inverse.comp (H y)
  have hL : ContMDiffAt (𝓡 n) 𝓘(ℝ, E →L[ℝ] E) ∞ L x :=
    ((hInv hxT).contDiffAt_map_inverse.contMDiffAt.comp x hA).clm_comp hH
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let tr := fun y ↦ ∑ i, b.repr (L y (b i)) i
  have htr : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ tr x := by
    apply ContMDiffAt.sum
    intro i _
    exact (b.coord i).toContinuousLinearMap.contMDiffAt.comp x
      (hL.clm_apply contMDiffAt_const)
  have htr_eq (y : M) : LinearMap.trace ℝ E (L y).toLinearMap = tr y := by
    rw [LinearMap.trace_eq_matrix_trace ℝ b]
    simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply, tr]
    apply Finset.sum_congr rfl
    intro i _
    rfl
  have heq {y : M} (hy : y ∈ t.baseSet) : tr y = D.ricci y (X y) (Y y) := by
    let e := (t.continuousLinearEquivAt ℝ y hy).symm
    let K := e.toLinearEquiv.conj (L y).toLinearMap
    have hrec (v : E) : B y (L y v) = C y v := by
      apply Q.injective
      change A y ((A y).inverse (H y v)) = H y v
      exact (hInv hy).self_apply_inverse _
    have hK (a b : TangentSpace (𝓡 n) y) : g.inner y (K a) b = R y a b := by
      have h := congrArg (fun f : E →L[ℝ] ℝ ↦ f (e.symm b)) (hrec (e.symm a))
      have hSe (v : E) : S y v = e v :=
        (congrFun (t.symm_continuousLinearEquivAt_eq hy) v).symm
      change g.inner y (S y (L y (e.symm a))) (S y (e.symm b)) =
        R y (S y (e.symm a)) (S y (e.symm b)) at h
      simp only [hSe, e.apply_symm_apply] at h
      exact h
    calc
      tr y = LinearMap.trace ℝ E (L y).toLinearMap := (htr_eq y).symm
      _ = LinearMap.trace ℝ (TangentSpace (𝓡 n) y) K :=
        (LinearMap.trace_conj' (L y).toLinearMap e.toLinearEquiv).symm
      _ = ∑ i, inner ℝ (g.orthonormalBasis y i) (K (g.orthonormalBasis y i)) := by
        rw [LinearMap.trace_eq_matrix_trace ℝ (g.orthonormalBasis y).toBasis]
        simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply,
          OrthonormalBasis.coe_toBasis, OrthonormalBasis.coe_toBasis_repr_apply,
          OrthonormalBasis.repr_apply_apply]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        change g.inner y (g.orthonormalBasis y i) (K (g.orthonormalBasis y i)) =
          R y (g.orthonormalBasis y i) (g.orthonormalBasis y i)
        rw [g.symm, hK]
  apply htr.congr_of_eventuallyEq
  filter_upwards [hO.mem_nhds hxO] with y hy
  exact (heq hy.2).symm

set_option maxHeartbeats 400000 in

set_option backward.isDefEq.respectTransparency false in
theorem isSmoothCovariantTensor_ricciEvaluation (D : LeviCivitaData g) :
    IsSmoothCovariantTensor D.ricciEvaluation := by
  constructor
  · intro x
    obtain ⟨T, hT⟩ := (isSmoothCovariantTensor_riemannEvaluation D).1 x
    have hR (a b c d : TangentSpace (𝓡 n) x) :
        D.curvatureTensor x a b c d = T ![a, b, c, d] := hT ![a, b, c, d]
    have hUpdate0 (a b c d z : TangentSpace (𝓡 n) x) :
        Function.update ![a, b, c, d] 0 z = ![z, b, c, d] := by
      ext i
      fin_cases i <;> simp [Function.update]
    have hUpdate2 (a b c d z : TangentSpace (𝓡 n) x) :
        Function.update ![a, b, c, d] 2 z = ![a, b, z, d] := by
      ext i
      fin_cases i <;> simp [Function.update]
    have ha1 (a a' b c d : TangentSpace (𝓡 n) x) :
        D.curvatureTensor x (a + a') b c d =
          D.curvatureTensor x a b c d + D.curvatureTensor x a' b c d := by
      simp only [hR]
      simpa only [hUpdate0] using T.map_update_add ![a, b, c, d] 0 a a'
    have ha3 (a b c c' d : TangentSpace (𝓡 n) x) :
        D.curvatureTensor x a b (c + c') d =
          D.curvatureTensor x a b c d + D.curvatureTensor x a b c' d := by
      simp only [hR]
      simpa only [hUpdate2] using T.map_update_add ![a, b, c, d] 2 c c'
    have hs1 (s : ℝ) (a b c d : TangentSpace (𝓡 n) x) :
        D.curvatureTensor x (s • a) b c d = s • D.curvatureTensor x a b c d := by
      simp only [hR]
      simpa only [hUpdate0] using T.map_update_smul ![a, b, c, d] 0 s a
    have hs3 (s : ℝ) (a b c d : TangentSpace (𝓡 n) x) :
        D.curvatureTensor x a b (s • c) d = s • D.curvatureTensor x a b c d := by
      simp only [hR]
      simpa only [hUpdate2] using T.map_update_smul ![a, b, c, d] 2 s c
    refine ⟨MultilinearMap.mk' (R := ℝ) (D.ricciEvaluation x) ?_ ?_, fun _ ↦ rfl⟩
    · intro v i a b
      fin_cases i <;>
        simp [LeviCivitaData.ricciEvaluation, LeviCivitaData.ricci, Function.update,
          ha1, ha3, Finset.sum_add_distrib]
    · intro v i s a
      fin_cases i <;>
        simp [LeviCivitaData.ricciEvaluation, LeviCivitaData.ricci, Function.update,
          hs1, hs3, Finset.mul_sum]
  · intro U hU X hX
    exact contMDiffOn_ricci D hU (hX 0) (hX 1)

end PoincareConjecture.M04

