import PoincareConjecture.Proofs.M08.TraceContractionAlgebra
import PoincareConjecture.Statements.Ch04.CurvatureTheory
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.Algebra.Structures

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Topology
open scoped Manifold ContDiff Bundle BigOperators Matrix Classical

universe u

namespace PoincareConjecture.M08

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

private theorem trace_mvfderiv_congr {f h : M → ℝ} {x : M}
    (heq : f =ᶠ[𝓝 x] h) : mvfderiv (𝓡 n) f x = mvfderiv (𝓡 n) h x := by
  ext W
  change mfderiv (𝓡 n) (𝓘(ℝ, ℝ)) f x W = mfderiv (𝓡 n) (𝓘(ℝ, ℝ)) h x W
  rw [heq.mfderiv_eq]
  rfl

private theorem trace_mvfderiv_sum {ι : Type} (s : Finset ι) (f : ι → M → ℝ)
    {x : M} (hf : ∀ i ∈ s, MDifferentiableAt (𝓡 n) (𝓘(ℝ, ℝ)) (f i) x)
    (W : TangentSpace (𝓡 n) x) :
    mvfderiv (𝓡 n) (fun y ↦ ∑ i ∈ s, f i y) x W =
      ∑ i ∈ s, mvfderiv (𝓡 n) (f i) x W := by
  induction s using Finset.induction_on with
  | empty => simp [mvfderiv_const]
  | @insert i s hi ih =>
    have hsum : MDifferentiableAt (𝓡 n) (𝓘(ℝ, ℝ)) (∑ j ∈ s, f j) x :=
      MDifferentiableAt.sum (fun j hj ↦ hf j (Finset.mem_insert_of_mem hj))
    have hsumFun : (∑ j ∈ s, f j) = (fun y ↦ ∑ j ∈ s, f j y) := by
      funext y
      simp only [Finset.sum_apply]
    rw [hsumFun] at hsum
    simp only [Finset.sum_insert hi]
    rw [mvfderiv_fun_add (hf i (Finset.mem_insert_self _ _)) hsum]
    simp only [add_apply, ih (fun j hj ↦ hf j (Finset.mem_insert_of_mem hj))]

private theorem trace_contMDiffAt_det {ι : Type} [Fintype ι] [DecidableEq ι]
    {G : M → Matrix ι ι ℝ} {x : M}
    (hG : ∀ i j, ContMDiffAt (𝓡 n) (𝓘(ℝ, ℝ)) ∞ (fun y ↦ G y i j) x) :
    ContMDiffAt (𝓡 n) (𝓘(ℝ, ℝ)) ∞ (fun y ↦ (G y).det) x := by
  simp only [Matrix.det_apply']
  apply ContMDiffAt.sum
  intro σ _
  apply ContMDiffAt.mul contMDiffAt_const
  exact ContMDiffAt.prod (fun i _ ↦ hG (σ i) i)

private theorem trace_contMDiffAt_inverse {ι : Type} [Fintype ι] [DecidableEq ι]
    {G : M → Matrix ι ι ℝ} {x : M}
    (hG : ∀ i j, ContMDiffAt (𝓡 n) (𝓘(ℝ, ℝ)) ∞ (fun y ↦ G y i j) x)
    (hdet : (G x).det ≠ 0) (i j : ι) :
    ContMDiffAt (𝓡 n) (𝓘(ℝ, ℝ)) ∞ (fun y ↦ (G y)⁻¹ i j) x := by
  simp only [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv,
    Matrix.adjugate_apply]
  refine ((trace_contMDiffAt_det hG).inv₀ hdet).mul ?_
  apply trace_contMDiffAt_det (G := fun y ↦ (G y).updateRow j (Pi.single i 1))
  intro a b
  by_cases ha : a = j
  · subst a
    simp only [Matrix.updateRow_self]
    exact contMDiffAt_const
  · simpa only [Matrix.updateRow_ne ha] using hG a b

private theorem trace_inverse_derivative_at_one {ι : Type} [Fintype ι] [DecidableEq ι]
    {G : M → Matrix ι ι ℝ} {x : M}
    (hG : ∀ i j, ContMDiffAt (𝓡 n) (𝓘(ℝ, ℝ)) ∞ (fun y ↦ G y i j) x)
    (hGx : G x = 1) (i j : ι) (W : TangentSpace (𝓡 n) x) :
    mvfderiv (𝓡 n) (fun y ↦ (G y)⁻¹ i j) x W =
      -mvfderiv (𝓡 n) (fun y ↦ G y i j) x W := by
  have hdet : (G x).det ≠ 0 := by rw [hGx, Matrix.det_one]; exact one_ne_zero
  have hGd (a b : ι) := (hG a b).mdifferentiableAt (by simp)
  have hHd (a b : ι) := (trace_contMDiffAt_inverse hG hdet a b).mdifferentiableAt (by simp)
  have hdetN : ∀ᶠ y in 𝓝 x, (G y).det ≠ 0 :=
    (trace_contMDiffAt_det hG).continuousAt.eventually_ne hdet
  have heq : (fun y ↦ ∑ k, G y i k * (G y)⁻¹ k j) =ᶠ[𝓝 x]
      (fun _ : M ↦ (1 : Matrix ι ι ℝ) i j) := by
    filter_upwards [hdetN] with y hy
    exact congrArg (fun A : Matrix ι ι ℝ ↦ A i j)
      (Matrix.mul_nonsing_inv (G y) (isUnit_iff_ne_zero.mpr hy))
  have hd := congrArg (fun L : TangentSpace (𝓡 n) x →L[ℝ] ℝ ↦ L W)
    (trace_mvfderiv_congr heq)
  rw [trace_mvfderiv_sum] at hd
  · simp only [mvfderiv_fun_mul (hGd _ _) (hHd _ _),
      add_apply, smul_apply, smul_eq_mul,
      hGx, inv_one, Matrix.one_apply, mvfderiv_const, zero_apply] at hd
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_add_distrib,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true] at hd
    linarith
  · intro k _
    exact (hGd i k).mul (hHd k j)

private theorem trace_extend_contMDiffOn {x : M} (v : TangentSpace (𝓡 n) x) :
    ContMDiffOn (𝓡 n) ((𝓡 n).prod (𝓘(ℝ, EuclideanSpace ℝ (Fin n)))) ∞
      (T% (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v))
      (trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x).baseSet := by
  let t := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x
  intro y hy
  rw [t.contMDiffWithinAt_section _ hy]
  apply (contMDiffWithinAt_const (c := (t ⟨x, v⟩).2)).congr
  · intro z hz
    have h := congrArg (fun p : M × EuclideanSpace ℝ (Fin n) ↦ p.2)
      (t.apply_mk_symm hz ((t ⟨x, v⟩).2))
    exact h
  · have h := congrArg (fun p : M × EuclideanSpace ℝ (Fin n) ↦ p.2)
      (t.apply_mk_symm hy ((t ⟨x, v⟩).2))
    exact h

private theorem trace_extendedFrame_basis {g : RiemannianMetric n M} (x y : M)
    (hy : y ∈ (trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x).baseSet) :
    ∃ e : Module.Basis (Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))) ℝ
        (TangentSpace (𝓡 n) y),
      ∀ i, e i = FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (g.orthonormalBasis x i) y := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let t := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x
  have hx : x ∈ t.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  let L := (t.linearEquivAt ℝ x hx).trans (t.linearEquivAt ℝ y hy).symm
  refine ⟨(g.orthonormalBasis x).toBasis.map L, ?_⟩
  intro i
  rfl

set_option maxHeartbeats 800000 in
private theorem trace_scalar_extendedFrame {g : RiemannianMetric n M}
    (hM04 : RicciFlowCurvatureTheory.{u}) (D : LeviCivitaData g) (x : M) :
    let b := g.orthonormalBasis x
    let E := fun i ↦ FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (b i)
    let G := fun y ↦ Matrix.of fun i j ↦ g.inner y (E i y) (E j y)
    D.scalarCurvature =ᶠ[𝓝 x] fun y ↦
      ∑ i, ∑ j, ∑ k, ∑ l, (G y)⁻¹ i j * (G y)⁻¹ k l *
        D.curvatureTensor y (E i y) (E k y) (E j y) (E l y) := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  dsimp only
  let t := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x
  filter_upwards [t.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' x)] with y hy
  obtain ⟨e, he⟩ := trace_extendedFrame_basis (g := g) x y hy
  obtain ⟨A, hA⟩ := (hM04.tensor_calculus n M g D).1.1 y
  have h := fourTensor_trace_eq_inverseGram e (g.orthonormalBasis y) A
  simp_rw [← hA] at h
  have hG : Matrix.gram ℝ e = Matrix.of fun i j ↦ g.inner y
      (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (g.orthonormalBasis x i) y)
      (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (g.orthonormalBasis x j) y) := by
    ext i j
    rw [Matrix.gram_apply, he i, he j]
    rfl
  rw [hG] at h
  have hdec : (fun a b : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) ↦
      Classical.propDecidable (a = b)) =
      instDecidableEqFin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) :=
    Subsingleton.elim _ _
  rw [hdec] at h
  simpa +instances only [LeviCivitaData.scalarCurvature, LeviCivitaData.ricci,
    LeviCivitaData.riemannEvaluation, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    he] using h

private theorem trace_curvature_extended_smooth {g : RiemannianMetric n M}
    (hM04 : RicciFlowCurvatureTheory.{u}) (D : LeviCivitaData g) (x : M)
    (v : Fin 4 → TangentSpace (𝓡 n) x) :
    ContMDiffAt (𝓡 n) (𝓘(ℝ, ℝ)) ∞
      (fun y ↦ D.riemannEvaluation y
        (fun i ↦ FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (v i) y)) x := by
  let t := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x
  apply ((hM04.tensor_calculus n M g D).1.2 t.baseSet t.open_baseSet
    (fun i ↦ FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (v i))
    (fun i ↦ trace_extend_contMDiffOn (v i))).contMDiffAt
  exact t.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' x)

private theorem trace_double_derivative {ι : Type} [Fintype ι] [DecidableEq ι]
    (H : M → Matrix ι ι ℝ) (R : ι → ι → ι → ι → M → ℝ) {x : M}
    (hH : ∀ i j, ContMDiffAt (𝓡 n) (𝓘(ℝ, ℝ)) ∞ (fun y ↦ H y i j) x)
    (hR : ∀ i k j l, ContMDiffAt (𝓡 n) (𝓘(ℝ, ℝ)) ∞ (R i k j l) x)
    (hHx : H x = 1) (W : TangentSpace (𝓡 n) x) :
    mvfderiv (𝓡 n) (fun y ↦ ∑ i, ∑ j, ∑ k, ∑ l,
        H y i j * H y k l * R i k j l y) x W =
      (∑ i, ∑ j, ∑ k, mvfderiv (𝓡 n) (fun y ↦ H y i j) x W * R i k j k x) +
      (∑ i, ∑ k, ∑ l, mvfderiv (𝓡 n) (fun y ↦ H y k l) x W * R i k i l x) +
      ∑ i, ∑ k, mvfderiv (𝓡 n) (R i k i k) x W := by
  let Q := fun i j k l y ↦ H y i j * H y k l * R i k j l y
  have hQ (i j k l : ι) : ContMDiffAt (𝓡 n) (𝓘(ℝ, ℝ)) ∞ (Q i j k l) x :=
    ((hH i j).mul (hH k l)).mul (hR i k j l)
  have hS1 (i j k : ι) : ContMDiffAt (𝓡 n) (𝓘(ℝ, ℝ)) ∞
      (fun y ↦ ∑ l, Q i j k l y) x := ContMDiffAt.sum (fun l _ ↦ hQ i j k l)
  have hS2 (i j : ι) : ContMDiffAt (𝓡 n) (𝓘(ℝ, ℝ)) ∞
      (fun y ↦ ∑ k, ∑ l, Q i j k l y) x := ContMDiffAt.sum (fun k _ ↦ hS1 i j k)
  have hS3 (i : ι) : ContMDiffAt (𝓡 n) (𝓘(ℝ, ℝ)) ∞
      (fun y ↦ ∑ j, ∑ k, ∑ l, Q i j k l y) x := ContMDiffAt.sum (fun j _ ↦ hS2 i j)
  have hsum : mvfderiv (𝓡 n) (fun y ↦ ∑ i, ∑ j, ∑ k, ∑ l, Q i j k l y) x W =
      ∑ i, ∑ j, ∑ k, ∑ l, mvfderiv (𝓡 n) (Q i j k l) x W := by
    rw [trace_mvfderiv_sum _ _ (fun i _ ↦ (hS3 i).mdifferentiableAt (by simp))]
    apply Finset.sum_congr rfl
    intro i _
    rw [trace_mvfderiv_sum _ _ (fun j _ ↦ (hS2 i j).mdifferentiableAt (by simp))]
    apply Finset.sum_congr rfl
    intro j _
    rw [trace_mvfderiv_sum _ _ (fun k _ ↦ (hS1 i j k).mdifferentiableAt (by simp))]
    apply Finset.sum_congr rfl
    intro k _
    exact trace_mvfderiv_sum _ _ (fun l _ ↦ (hQ i j k l).mdifferentiableAt (by simp)) W
  have hterm (i j k l : ι) : mvfderiv (𝓡 n) (Q i j k l) x W =
      mvfderiv (𝓡 n) (fun y ↦ H y i j) x W * H x k l * R i k j l x +
      H x i j * mvfderiv (𝓡 n) (fun y ↦ H y k l) x W * R i k j l x +
      H x i j * H x k l * mvfderiv (𝓡 n) (R i k j l) x W := by
    dsimp only [Q]
    have hmid : MDifferentiableAt (𝓡 n) (𝓘(ℝ, ℝ))
        (fun y ↦ H y i j * H y k l) x :=
      ((hH i j).mul (hH k l)).mdifferentiableAt (by simp)
    erw [mvfderiv_fun_mul hmid
      ((hR i k j l).mdifferentiableAt (by simp)),
      mvfderiv_fun_mul ((hH i j).mdifferentiableAt (by simp))
        ((hH k l).mdifferentiableAt (by simp))]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  change mvfderiv (𝓡 n) (fun y ↦ ∑ i, ∑ j, ∑ k, ∑ l, Q i j k l y) x W = _
  rw [hsum]
  simp only [hterm, hHx, Matrix.one_apply, mul_ite, ite_mul,
    zero_mul, mul_zero, one_mul, mul_one, Finset.sum_add_distrib,
    Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]

private theorem trace_slot_expand {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {ι : Type} [Fintype ι] (b : OrthonormalBasis ι ℝ V) {d : ℕ}
    (A : MultilinearMap ℝ (fun _ : Fin d ↦ V) ℝ) (v : Fin d → V) (k : Fin d) (w : V) :
    A (Function.update v k w) =
      ∑ j, inner ℝ (b j) w * A (Function.update v k (b j)) := by
  have h := congrArg (A.toLinearMap v k) (b.sum_repr w)
  simpa only [map_sum, map_smul, smul_eq_mul, MultilinearMap.toLinearMap_apply,
    OrthonormalBasis.repr_apply_apply] using h.symm

private theorem trace_connection_sum {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {ι : Type} [Fintype ι] (b : OrthonormalBasis ι ℝ V) (C : ι → V)
    (A : ι → ι → ℝ) (L R : ι → ℝ)
    (hL : ∀ j, (∑ i, inner ℝ (b i) (C j) * A i j) = L j)
    (hR : ∀ i, (∑ j, inner ℝ (b j) (C i) * A i j) = R i) :
    (∑ i, ∑ j, (inner ℝ (C i) (b j) + inner ℝ (b i) (C j)) * A i j) =
      ∑ i, (L i + R i) := by
  simp only [add_mul, Finset.sum_add_distrib]
  have hfirst : (∑ i, ∑ j, inner ℝ (C i) (b j) * A i j) = ∑ i, R i := by
    apply Finset.sum_congr rfl
    intro i _
    simpa only [real_inner_comm (C i)] using hR i
  have hsecond : (∑ i, ∑ j, inner ℝ (b i) (C j) * A i j) = ∑ j, L j := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ ↦ hL j
  rw [hfirst, hsecond]
  exact add_comm _ _

private theorem trace_update4_zero {V : Type*} (u v w z q : V) :
    Function.update ![u, v, w, z] 0 q = ![q, v, w, z] := by
  funext a
  fin_cases a <;> simp

private theorem trace_update4_one {V : Type*} (u v w z q : V) :
    Function.update ![u, v, w, z] 1 q = ![u, q, w, z] := by
  funext a
  fin_cases a <;> simp

private theorem trace_update4_two {V : Type*} (u v w z q : V) :
    Function.update ![u, v, w, z] 2 q = ![u, v, q, z] := by
  funext a
  fin_cases a <;> simp

private theorem trace_update4_three {V : Type*} (u v w z q : V) :
    Function.update ![u, v, w, z] 3 q = ![u, v, w, q] := by
  funext a
  fin_cases a <;> simp

private theorem trace_curvature_corrections {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {ι : Type} [Fintype ι] (b : OrthonormalBasis ι ℝ V) (C : ι → V)
    (A : MultilinearMap ℝ (fun _ : Fin 4 ↦ V) ℝ) :
    (∑ i, ∑ j, ∑ k, (inner ℝ (C i) (b j) + inner ℝ (b i) (C j)) *
      A ![b i, b k, b j, b k]) +
    (∑ i, ∑ k, ∑ l, (inner ℝ (C k) (b l) + inner ℝ (b k) (C l)) *
      A ![b i, b k, b i, b l]) =
      ∑ i, ∑ k, (A ![C i, b k, b i, b k] + A ![b i, C k, b i, b k] +
        A ![b i, b k, C i, b k] + A ![b i, b k, b i, C k]) := by
  have hslot (v : Fin 4 → V) (k : Fin 4) (w : V) := trace_slot_expand b A v k w
  have h02 (k : ι) : (∑ i, ∑ j,
      (inner ℝ (C i) (b j) + inner ℝ (b i) (C j)) * A ![b i, b k, b j, b k]) =
      ∑ i, (A ![C i, b k, b i, b k] + A ![b i, b k, C i, b k]) := by
    apply trace_connection_sum b C
    · intro j
      simpa only [trace_update4_zero] using
        (hslot ![b j, b k, b j, b k] 0 (C j)).symm
    · intro i
      simpa only [trace_update4_two] using
        (hslot ![b i, b k, b i, b k] 2 (C i)).symm
  have h13 (i : ι) : (∑ k, ∑ l,
      (inner ℝ (C k) (b l) + inner ℝ (b k) (C l)) * A ![b i, b k, b i, b l]) =
      ∑ k, (A ![b i, C k, b i, b k] + A ![b i, b k, b i, C k]) := by
    apply trace_connection_sum b C
    · intro l
      simpa only [trace_update4_one] using
        (hslot ![b i, b l, b i, b l] 1 (C l)).symm
    · intro k
      simpa only [trace_update4_three] using
        (hslot ![b i, b k, b i, b k] 3 (C k)).symm
  have hfirst : (∑ i, ∑ j, ∑ k,
      (inner ℝ (C i) (b j) + inner ℝ (b i) (C j)) * A ![b i, b k, b j, b k]) =
      ∑ i, ∑ k, (A ![C i, b k, b i, b k] + A ![b i, b k, C i, b k]) := by
    calc
      _ = ∑ i, ∑ k, ∑ j,
          (inner ℝ (C i) (b j) + inner ℝ (b i) (C j)) * A ![b i, b k, b j, b k] :=
        Finset.sum_congr rfl fun i _ ↦ Finset.sum_comm
      _ = ∑ k, ∑ i, ∑ j,
          (inner ℝ (C i) (b j) + inner ℝ (b i) (C j)) * A ![b i, b k, b j, b k] :=
        Finset.sum_comm
      _ = _ := by simp_rw [h02]; rw [Finset.sum_comm]
  rw [hfirst]
  simp_rw [h13]
  simp only [Finset.sum_add_distrib]
  ring

set_option maxHeartbeats 1500000 in

theorem scalarCurvature_differential_eq_trace {g : RiemannianMetric n M}
    (hM04 : RicciFlowCurvatureTheory.{u}) (D : LeviCivitaData g) (x : M)
    (W : TangentSpace (𝓡 n) x) :
    let b := g.orthonormalBasis x
    mvfderiv (𝓡 n) D.scalarCurvature x W =
      ∑ i, ∑ k, D.covariantTensorDerivative D.riemannEvaluation x
        ![W, b i, b k, b i, b k] := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let b := g.orthonormalBasis x
  let E := fun i ↦ FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (b i)
  let G := fun y ↦ Matrix.of fun i j ↦ g.inner y (E i y) (E j y)
  let H := fun y ↦ (G y)⁻¹
  let R := fun i k j l y ↦ D.curvatureTensor y (E i y) (E k y) (E j y) (E l y)
  let C := fun i ↦ D.connection (E i) x W
  have hE (i) : ContMDiffAt (𝓡 n)
      ((𝓡 n).prod (𝓘(ℝ, EuclideanSpace ℝ (Fin n)))) ∞ (T% (E i)) x :=
    FiberBundle.contMDiffAt_extend (𝓡 n) (EuclideanSpace ℝ (Fin n)) (b i)
  have hG (i j) : ContMDiffAt (𝓡 n) (𝓘(ℝ, ℝ)) ∞ (fun y ↦ G y i j) x :=
    (hE i).inner_bundle (hE j)
  have hGx : G x = 1 := by
    ext i j
    change g.inner x (E i x) (E j x) = (1 : Matrix _ _ ℝ) i j
    simp only [E, FiberBundle.extend_apply_self, Matrix.one_apply]
    exact b.inner_eq_ite i j
  have hH (i j) : ContMDiffAt (𝓡 n) (𝓘(ℝ, ℝ)) ∞ (fun y ↦ H y i j) x :=
    trace_contMDiffAt_inverse hG (by rw [hGx, Matrix.det_one]; exact one_ne_zero) i j
  have hHx : H x = 1 := by simp only [H, hGx, inv_one]
  have hR (i k j l) : ContMDiffAt (𝓡 n) (𝓘(ℝ, ℝ)) ∞ (R i k j l) x := by
    simpa only [LeviCivitaData.riemannEvaluation, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons] using
      trace_curvature_extended_smooth hM04 D x ![b i, b k, b j, b l]
  have hGd (i j) : mvfderiv (𝓡 n) (fun y ↦ G y i j) x W =
      inner ℝ (C i) (b j) + inner ℝ (b i) (C j) := by
    have hh := D.metricCompatible.mvfderiv_inner_eq
      (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) W)
      ((hE i).mdifferentiableAt (by simp)) ((hE j).mdifferentiableAt (by simp))
    change mvfderiv (𝓡 n) (fun y ↦ g.inner y (E i y) (E j y)) x
        (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) W x) =
      g.inner x (D.connection (E i) x (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) W x))
        (E j x) + g.inner x (E i x)
        (D.connection (E j) x (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) W x)) at hh
    change mvfderiv (𝓡 n) (fun y ↦ g.inner y (E i y) (E j y)) x W =
      g.inner x (C i) (b j) + g.inner x (b i) (C j)
    simpa only [E, FiberBundle.extend_apply_self] using hh
  have hHd (i j) : mvfderiv (𝓡 n) (fun y ↦ H y i j) x W =
      -(inner ℝ (C i) (b j) + inner ℝ (b i) (C j)) := by
    rw [trace_inverse_derivative_at_one hG hGx, hGd]
  obtain ⟨A, hA⟩ := (hM04.tensor_calculus n M g D).1.1 x
  have hAeval (u v w z : TangentSpace (𝓡 n) x) : D.curvatureTensor x u v w z =
      A ![u, v, w, z] := by
    simpa only [LeviCivitaData.riemannEvaluation, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons] using hA ![u, v, w, z]
  have hRx (i k j l) : R i k j l x = A ![b i, b k, b j, b l] := by
    simp only [R, E, FiberBundle.extend_apply_self, hAeval]
  have hcov (i k) : D.covariantTensorDerivative D.riemannEvaluation x
      ![W, b i, b k, b i, b k] = mvfderiv (𝓡 n) (R i k i k) x W -
      (A ![C i, b k, b i, b k] + A ![b i, C k, b i, b k] +
        A ![b i, b k, C i, b k] + A ![b i, b k, b i, C k]) := by
    simp only [LeviCivitaData.covariantTensorDerivative, hA, Fin.sum_univ_succ,
      Matrix.vecCons, Fin.cons_zero, Fin.cons_succ, ← Fin.cons_update, Fin.update_cons_zero]
    change mvfderiv (𝓡 n) (R i k i k) x W -
      (A ![C i, b k, b i, b k] +
        (A ![b i, C k, b i, b k] +
          (A ![b i, b k, C i, b k] + (A ![b i, b k, b i, C k] + 0)))) = _
    simp only [Matrix.vecCons]
    ring
  have hscalar := trace_scalar_extendedFrame hM04 D x
  have hder := trace_double_derivative H R hH hR hHx W
  have hcorr := trace_curvature_corrections b C A
  change mvfderiv (𝓡 n) D.scalarCurvature x W =
    ∑ i, ∑ k, D.covariantTensorDerivative D.riemannEvaluation x ![W, b i, b k, b i, b k]
  rw [trace_mvfderiv_congr hscalar, hder]
  simp only [hHd, hRx, hcov, neg_mul, Finset.sum_neg_distrib]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib] at hcorr ⊢
  linarith

private theorem trace_tensor_component_le (g : RiemannianMetric n M) {d : ℕ}
    (T : CovariantTensorEvaluation n M d) (x : M)
    (a : Fin d → Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))) :
    |T x (fun i ↦ g.orthonormalBasis x (a i))| ≤ g.tensorNorm T x := by
  have hs : (T x (fun i ↦ g.orthonormalBasis x (a i))) ^ 2 ≤
      ∑ q : Fin d → Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)),
        (T x (fun i ↦ g.orthonormalBasis x (q i))) ^ 2 :=
    Finset.single_le_sum
      (f := fun q : Fin d → Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) ↦
        (T x (fun i ↦ g.orthonormalBasis x (q i))) ^ 2)
      (fun _ _ ↦ sq_nonneg _) (Finset.mem_univ a)
  simpa only [Real.sqrt_sq_eq_abs, RiemannianMetric.tensorNorm] using Real.sqrt_le_sqrt hs

private theorem trace_curvature_component_le {g : RiemannianMetric n M}
    (D : LeviCivitaData g) (x : M)
    (i j k l : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))) :
    |D.curvatureTensor x (g.orthonormalBasis x i) (g.orthonormalBasis x j)
      (g.orthonormalBasis x k) (g.orthonormalBasis x l)| ≤ D.curvatureTensorNorm x := by
  let A : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) →
      Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) →
      Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) →
      Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) → ℝ :=
    fun a b c d ↦ D.curvatureTensor x (g.orthonormalBasis x a)
    (g.orthonormalBasis x b) (g.orthonormalBasis x c) (g.orthonormalBasis x d)
  have hs : A i j k l ^ 2 ≤ ∑ a, ∑ b, ∑ c, ∑ d, A a b c d ^ 2 := by
    calc
      A i j k l ^ 2 ≤ ∑ d, A i j k d ^ 2 :=
        Finset.single_le_sum (f := fun d ↦ A i j k d ^ 2)
          (fun _ _ ↦ sq_nonneg _) (Finset.mem_univ l)
      _ ≤ ∑ c, ∑ d, A i j c d ^ 2 :=
        Finset.single_le_sum (f := fun c ↦ ∑ d, A i j c d ^ 2)
          (fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)
          (Finset.mem_univ k)
      _ ≤ ∑ b, ∑ c, ∑ d, A i b c d ^ 2 :=
        Finset.single_le_sum (f := fun b ↦ ∑ c, ∑ d, A i b c d ^ 2)
          (fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)
          (Finset.mem_univ j)
      _ ≤ _ := Finset.single_le_sum (f := fun a ↦ ∑ b, ∑ c, ∑ d, A a b c d ^ 2)
        (fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦
          Finset.sum_nonneg fun _ _ ↦ sq_nonneg _) (Finset.mem_univ i)
  simpa only [Real.sqrt_sq_eq_abs, LeviCivitaData.curvatureTensorNorm, A] using
    Real.sqrt_le_sqrt hs


theorem scalarCurvature_differential_abs_le {g : RiemannianMetric n M}
    (hM04 : RicciFlowCurvatureTheory.{u}) (D : LeviCivitaData g) (x : M)
    (W : TangentSpace (𝓡 n) x) :
    |mvfderiv (𝓡 n) D.scalarCurvature x W| ≤
      (n : ℝ) ^ 3 * D.curvatureDerivativeNorm 1 x * Real.sqrt (g.inner x W W) := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let b := g.orthonormalBasis x
  let T := D.covariantTensorDerivative D.riemannEvaluation
  have hT := (hM04.tensor_calculus n M g D).2.2.1 4 D.riemannEvaluation
    (hM04.tensor_calculus n M g D).1
  obtain ⟨A, hA⟩ := hT.1 x
  have hAT (v : Fin 5 → TangentSpace (𝓡 n) x) : T x v = A v := hA v
  have hcoord (i) : |inner ℝ (b i) W| ≤ ‖W‖ := by
    simpa only [b.norm_eq_one, one_mul] using abs_real_inner_le_norm (b i) W
  have hcomponent (k i j) : |T x ![b k, b i, b j, b i, b j]| ≤
      D.curvatureDerivativeNorm 1 x := by
    have h := trace_tensor_component_le g T x ![k, i, j, i, j]
    have he : (fun a : Fin 5 ↦ b (![k, i, j, i, j] a)) = ![b k, b i, b j, b i, b j] := by
      funext a
      fin_cases a <;> rfl
    change |T x (fun a ↦ b (![k, i, j, i, j] a))| ≤ _ at h
    rw [he] at h
    exact h
  have hexp (i j) : T x ![W, b i, b j, b i, b j] =
      ∑ k, inner ℝ (b k) W * T x ![b k, b i, b j, b i, b j] := by
    simp only [hAT]
    simpa only [Matrix.vecCons, Fin.update_cons_zero] using
      trace_slot_expand b A ![W, b i, b j, b i, b j] 0 W
  rw [scalarCurvature_differential_eq_trace hM04 D x W]
  change |∑ i, ∑ j, T x ![W, b i, b j, b i, b j]| ≤ _
  simp_rw [hexp]
  calc
    |∑ i, ∑ j, ∑ k, inner ℝ (b k) W * T x ![b k, b i, b j, b i, b j]| ≤
        ∑ i, ∑ j, ∑ k, |inner ℝ (b k) W * T x ![b k, b i, b j, b i, b j]| :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun _ _ ↦
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun _ _ ↦
          Finset.abs_sum_le_sum_abs _ _))
    _ ≤ ∑ _i : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)),
        ∑ _j : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)),
          ∑ _k : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)),
            ‖W‖ * D.curvatureDerivativeNorm 1 x := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro k _
      rw [abs_mul]
      exact mul_le_mul (hcoord k) (hcomponent k i j) (abs_nonneg _) (norm_nonneg _)
    _ = _ := by
      have hdim : Module.finrank ℝ (TangentSpace (𝓡 n) x) = n := finrank_euclideanSpace_fin
      have hnorm : ‖W‖ = Real.sqrt (g.inner x W W) := norm_eq_sqrt_real_inner W
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, hdim, nsmul_eq_mul, hnorm]
      ring


theorem ricci_quadratic_abs_le {g : RiemannianMetric n M}
    (hM04 : RicciFlowCurvatureTheory.{u}) (D : LeviCivitaData g) (x : M)
    (W : TangentSpace (𝓡 n) x) :
    |D.ricci x W W| ≤ (n : ℝ) ^ 3 * D.curvatureTensorNorm x * g.inner x W W := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let b := g.orthonormalBasis x
  obtain ⟨A, hA⟩ := (hM04.tensor_calculus n M g D).1.1 x
  have hAeval (u v w z : TangentSpace (𝓡 n) x) : D.curvatureTensor x u v w z =
      A ![u, v, w, z] := by
    simpa only [LeviCivitaData.riemannEvaluation, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons] using hA ![u, v, w, z]
  have hcoord (i) : |inner ℝ (b i) W| ≤ ‖W‖ := by
    simpa only [b.norm_eq_one, one_mul] using abs_real_inner_le_norm (b i) W
  have h0 (i) : A ![W, b i, W, b i] =
      ∑ j, inner ℝ (b j) W * A ![b j, b i, W, b i] := by
    simpa only [Matrix.vecCons, Fin.update_cons_zero] using
      trace_slot_expand b A ![W, b i, W, b i] 0 W
  have h2 (i j) : A ![b j, b i, W, b i] =
      ∑ k, inner ℝ (b k) W * A ![b j, b i, b k, b i] := by
    simpa only [trace_update4_two] using
      trace_slot_expand b A ![b j, b i, W, b i] 2 W
  have hexp (i) : D.curvatureTensor x W (b i) W (b i) =
      ∑ j, ∑ k, inner ℝ (b j) W * inner ℝ (b k) W *
        D.curvatureTensor x (b j) (b i) (b k) (b i) := by
    simp_rw [hAeval]
    rw [h0]
    simp only [h2, Finset.mul_sum, mul_assoc]
  change |∑ i, D.curvatureTensor x W (b i) W (b i)| ≤ _
  simp_rw [hexp]
  calc
    |∑ i, ∑ j, ∑ k, inner ℝ (b j) W * inner ℝ (b k) W *
        D.curvatureTensor x (b j) (b i) (b k) (b i)| ≤
        ∑ i, ∑ j, ∑ k, |inner ℝ (b j) W * inner ℝ (b k) W *
          D.curvatureTensor x (b j) (b i) (b k) (b i)| :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun _ _ ↦
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun _ _ ↦
          Finset.abs_sum_le_sum_abs _ _))
    _ ≤ ∑ _i : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)),
        ∑ _j : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)),
          ∑ _k : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)),
            (‖W‖ * ‖W‖) * D.curvatureTensorNorm x := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro k _
      simp only [abs_mul]
      exact mul_le_mul
        (mul_le_mul (hcoord j) (hcoord k) (abs_nonneg _) (norm_nonneg _))
        (trace_curvature_component_le D x j i k i) (abs_nonneg _)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = _ := by
      have hdim : Module.finrank ℝ (TangentSpace (𝓡 n) x) = n := finrank_euclideanSpace_fin
      have hnorm : g.inner x W W = ‖W‖ ^ 2 := real_inner_self_eq_norm_sq W
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, hdim, nsmul_eq_mul, hnorm]
      ring

end PoincareConjecture.M08
