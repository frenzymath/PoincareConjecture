import PoincareConjecture.Definitions.Ch01.ScalarOperators
import PoincareConjecture.Proofs.M04.CurvatureCalculus
import PoincareConjecture.Proofs.M13
import PoincareConjecture.Definitions.Ch15.SurgeryFlow
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Topology.Algebra.Module.FiniteDimension









set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators

universe u v

namespace PoincareConjecture

theorem m48_sum_sq_bilin_basis_independent
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {ι κ : Type*} [Fintype ι] [Fintype κ]
    (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
    (b : OrthonormalBasis ι ℝ E) (c : OrthonormalBasis κ ℝ E) :
    (∑ i, ∑ j, (B (b i) (b j)) ^ 2) =
      ∑ i, ∑ j, (B (c i) (c j)) ^ 2 := by
  have right (x : E) :
      (∑ j, (B x (b j)) ^ 2) = ∑ j, (B x (c j)) ^ 2 :=
    (b.norm_dual (B x).toContinuousLinearMap).symm.trans
      (c.norm_dual (B x).toContinuousLinearMap)
  have left (y : E) :
      (∑ i, (B (b i) y) ^ 2) = ∑ i, (B (c i) y) ^ 2 :=
    (b.norm_dual (B.flip y).toContinuousLinearMap).symm.trans
      (c.norm_dual (B.flip y).toContinuousLinearMap)
  calc
    (∑ i, ∑ j, (B (b i) (b j)) ^ 2) =
        ∑ i, ∑ j, (B (b i) (c j)) ^ 2 := by simp_rw [right]
    _ = ∑ j, ∑ i, (B (b i) (c j)) ^ 2 := Finset.sum_comm
    _ = ∑ j, ∑ i, (B (c i) (c j)) ^ 2 := by simp_rw [left]
    _ = ∑ i, ∑ j, (B (c i) (c j)) ^ 2 := Finset.sum_comm

theorem m48_sum_sq_tensor_basis_independent
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {ι κ : Type*} [Fintype ι] [Fintype κ]
    (T : MultilinearMap ℝ (fun _ : Fin 2 ↦ E) ℝ)
    (b : OrthonormalBasis ι ℝ E) (c : OrthonormalBasis κ ℝ E) :
    (∑ i, ∑ j, (T ![b i, b j]) ^ 2) =
      ∑ i, ∑ j, (T ![c i, c j]) ^ 2 := by
  have update_zero (u v w : E) :
      Function.update ![u, v] 0 w = ![w, v] := by
    funext i
    fin_cases i <;> rfl
  have update_one (u v w : E) :
      Function.update ![u, v] 1 w = ![u, w] := by
    funext i
    fin_cases i <;> rfl
  let B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ :=
    { toFun := fun u =>
        { toFun := fun v => T ![u, v]
          map_add' := by
            intro v w
            simpa only [update_one] using T.map_update_add ![u, 0] 1 v w
          map_smul' := by
            intro a v
            simpa only [update_one, RingHom.id_apply] using
              T.map_update_smul ![u, 0] 1 a v }
      map_add' := by
        intro u v
        ext w
        change T ![u + v, w] = T ![u, w] + T ![v, w]
        simpa only [update_zero] using T.map_update_add ![0, w] 0 u v
      map_smul' := by
        intro a u
        ext w
        change T ![a • u, w] = a • T ![u, w]
        simpa only [update_zero] using T.map_update_smul ![0, w] 0 a u }
  simpa [B] using m48_sum_sq_bilin_basis_independent B b c



theorem LeviCivitaData.m48_ricciNormSq_eq_sum
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : RiemannianMetric n M} (D : LeviCivitaData g) (x : M)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ (TangentSpace (𝓡 n) x))
    (hb : ∀ i j, g.inner x (b i) (b j) = if i = j then 1 else 0) :
    D.ricciNormSq x = ∑ i, ∑ j, (D.ricci x (b i) (b j)) ^ 2 := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : FiniteDimensional ℝ (TangentSpace (𝓡 n) x) :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) x
  have hb' : Orthonormal ℝ b := orthonormal_iff_ite.mpr hb
  obtain ⟨T, hT⟩ := D.curvatureTensorCalculus.2.1.1 x
  have hRicci (u v : TangentSpace (𝓡 n) x) : D.ricci x u v = T ![u, v] :=
    hT ![u, v]
  simpa only [LeviCivitaData.ricciNormSq, hRicci,
    Module.Basis.coe_toOrthonormalBasis] using
      m48_sum_sq_tensor_basis_independent T (g.orthonormalBasis x)
        (b.toOrthonormalBasis hb')




theorem MetricHomothetyCalculus.m48_ricciNormSq_eq
    {n : ℕ} {M : Type u} {N : Type v}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
    [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
    [IsManifold (𝓡 n) ∞ N] [T3Space N] [MeasurableSpace N] [BorelSpace N]
    {g : RiemannianMetric n M} {h : RiemannianMetric n N}
    {f : Diffeomorph (𝓡 n) (𝓡 n) M N ∞}
    (H : MetricHomothetyCalculus g h f 1) (hf : MetricHomothety g h f 1)
    (D : LeviCivitaData g) (D' : LeviCivitaData h) (x : M) :
    D'.ricciNormSq (f x) = D.ricciNormSq x := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : FiniteDimensional ℝ (TangentSpace (𝓡 n) x) :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) x
  let b := (g.orthonormalBasis x).toBasis
  let e : TangentSpace (𝓡 n) x ≃ₗ[ℝ] TangentSpace (𝓡 n) (f x) :=
    ((f.toOpenPartialHomeomorph_mdifferentiable (by simp)).mfderiv
      (x := x) (Set.mem_univ x)).toLinearEquiv
  have he (u : TangentSpace (𝓡 n) x) :
      e u = mfderiv (𝓡 n) (𝓡 n) f x u := rfl
  have hb (i j) : g.inner x (b i) (b j) = if i = j then 1 else 0 := by
    exact (g.orthonormalBasis x).inner_eq_ite i j
  have hc (i j) : h.inner (f x) ((b.map e) i) ((b.map e) j) =
      if i = j then 1 else 0 := by
    rw [Module.Basis.map_apply, Module.Basis.map_apply, he, he, hf]
    simpa using hb i j
  rw [D'.m48_ricciNormSq_eq_sum (f x) (b.map e) hc]
  simp_rw [Module.Basis.map_apply, he, H.ricci_eq D D']
  rfl




theorem SurgeryRegularSlab.m48_ricciNormSq_eq
    {slice : ℝ → GeneralizedSliceCarrier.{u}}
    {metric : ∀ t, RiemannianMetric 3 (slice t).carrier} {a b : ℝ}
    (B : SurgeryRegularSlab slice metric a b) (t : Set.Icc a b)
    (D : LeviCivitaData (metric t.1)) (x : (slice a).carrier) :
    D.ricciNormSq (B.identify t x) = (B.flow.connection t.1).ricciNormSq x := by
  have hf : MetricHomothety (B.flow.metric t.1) (metric t.1) (B.identify t) 1 := by
    intro y v w
    simpa only [one_mul] using B.metric_pullback t y v w
  have H := (generalizedParabolicRescaling_from_M12 3).metric_homothety
    (slice a).carrier (slice t.1).carrier (B.flow.metric t.1) (metric t.1)
    (B.identify t) 1 (by norm_num) hf
  exact H.m48_ricciNormSq_eq hf (B.flow.connection t.1) D x

end PoincareConjecture
