import PoincareConjecture.Proofs.M03.Existence.CoordinateConnectionNative
import PoincareConjecture.Proofs.M03.CurvatureTrace










set_option autoImplicit false
set_option maxHeartbeats 1600000

open scoped Manifold ContDiff Bundle BigOperators Topology

noncomputable section

universe u

namespace PoincareConjecture.DeTurckNative

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

private theorem connection_sum_at {g : RiemannianMetric n M}
    (D : LeviCivitaData g)
    (Z : Fin n → (y : M) → TangentSpace (𝓡 n) y) {x : M}
    (hZ : ∀ a, MDifferentiableAt (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% (Z a)) x)
    (v : TangentSpace (𝓡 n) x) :
    D.connection (fun y => ∑ a, Z a y) x v =
      ∑ a, D.connection (Z a) x v := by
  classical
  have hc := D.connection.isCovariantDerivativeOn (s := Set.univ)
  have hsum (s : Finset (Fin n)) :
      D.connection (fun y => ∑ a ∈ s, Z a y) x v =
        ∑ a ∈ s, D.connection (Z a) x v := by
    induction s using Finset.induction_on with
    | empty =>
        simp only [Finset.sum_empty]
        change D.connection 0 x v = 0
        rw [hc.zero, ContinuousLinearMap.zero_apply]
    | @insert a s ha ih =>
        simp only [Finset.sum_insert ha]
        change D.connection (Z a + fun y => ∑ c ∈ s, Z c y) x v = _
        rw [hc.add (hZ a) (MDifferentiableAt.sum_section fun c _ => hZ c),
          ContinuousLinearMap.add_apply, ih]
  exact hsum Finset.univ

theorem connection_frame_expansion
    {g : RiemannianMetric n M} (D : LeviCivitaData g)
    (F : Fin n → (y : M) → TangentSpace (𝓡 n) y)
    (f : Fin n → M → ℝ) (Q : (y : M) → TangentSpace (𝓡 n) y)
    {x : M}
    (hF : ∀ a, MDifferentiableAt (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% (F a)) x)
    (hf : ∀ a, MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) (f a) x)
    (hQ : MDifferentiableAt (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% Q) x)
    (hrep : ∀ᶠ y in 𝓝 x, Q y = ∑ a, f a y • F a y)
    (v : TangentSpace (𝓡 n) x) :
    D.connection Q x v =
      ∑ a, (f a x • D.connection (F a) x v +
        mvfderiv (𝓡 n) (f a) x v • F a x) := by
  have hc := D.connection.isCovariantDerivativeOn (s := Set.univ)
  have hterm (a : Fin n) : MDifferentiableAt (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (T% ((f a) • F a)) x := (hf a).smul_section (hF a)
  have heq := hc.congr_of_eventuallyEq hQ
    (MDifferentiableAt.sum_section fun a _ => hterm a) Filter.univ_mem hrep
  calc
    D.connection Q x v =
        D.connection (fun y => ∑ a, f a y • F a y) x v :=
      congrArg (fun L => L v) heq
    _ = ∑ a, D.connection ((f a) • F a) x v :=
      connection_sum_at D (fun a => (f a) • F a) hterm v
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      exact congrArg (fun L => L v) (hc.leibniz (hF a) (hf a))

def frameCurvatureCoefficient
    (F : Fin n → (y : M) → TangentSpace (𝓡 n) y)
    (Γ : Fin n → Fin n → Fin n → M → ℝ)
    (x : M) (i j k l : Fin n) : ℝ :=
  mvfderiv (𝓡 n) (Γ l j k) x (F i x) -
    mvfderiv (𝓡 n) (Γ l i k) x (F j x) +
    ∑ a, (Γ a j k x * Γ l i a x - Γ a i k x * Γ l j a x)

theorem curvature_repr_eq_frameCurvatureCoefficient
    {g : RiemannianMetric n M} (D : LeviCivitaData g)
    {U : Set M} (hU : IsOpen U)
    (F : Fin n → (y : M) → TangentSpace (𝓡 n) y)
    (hF : ∀ a, ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% (F a)) U)
    (Γ : Fin n → Fin n → Fin n → M → ℝ)
    (hcoeff : ∀ y ∈ U, ∀ a c,
      D.connection (F c) y (F a y) = ∑ l, Γ l a c y • F l y)
    {x : M} (hx : x ∈ U)
    (hΓ : ∀ l a c, MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) (Γ l a c) x)
    (b : Module.Basis (Fin n) ℝ (TangentSpace (𝓡 n) x))
    (hpoint : ∀ a, F a x = b a)
    (hbracket : ∀ a c, VectorField.mlieBracket (𝓡 n) (F a) (F c) x = 0)
    (i j k l : Fin n) :
    b.repr (D.curvature x (F i x) (F j x) (F k x)) l =
      frameCurvatureCoefficient F Γ x i j k l := by
  classical
  have hFmd (a : Fin n) :=
    ((hF a).contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)
  have hcoord (a c r : Fin n) :
      b.coord r (D.connection (F c) x (F a x)) = Γ r a c x := by
    rw [hcoeff x hx a c, map_sum]
    simp [map_smul, hpoint, Module.Basis.coord_apply,
      Module.Basis.repr_self_apply, Finsupp.single_apply, smul_eq_mul]
  have houter (a c d r : Fin n) :
      b.coord r (D.connection (fun y => D.connection (F d) y (F c y)) x
        (F a x)) =
      mvfderiv (𝓡 n) (Γ r c d) x (F a x) +
        ∑ m, Γ m c d x * Γ r a m x := by
    have hNs := D.contMDiffOn_connection_apply hU (F c) (F d) (hF c) (hF d)
    have hN := (hNs.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)
    have hrep : ∀ᶠ y in 𝓝 x,
        D.connection (F d) y (F c y) = ∑ m, Γ m c d y • F m y :=
      Filter.eventuallyEq_of_mem (hU.mem_nhds hx) (fun y hy => hcoeff y hy c d)
    have hexp := connection_frame_expansion D F (fun m => Γ m c d)
      (fun y => D.connection (F d) y (F c y)) hFmd
      (fun m => hΓ m c d) hN hrep (F a x)
    rw [hexp, map_sum]
    simp only [map_add, map_smul, smul_eq_mul, hcoord, Finset.sum_add_distrib]
    have hbasis (m : Fin n) : b.coord r (F m x) = if m = r then 1 else 0 := by
      rw [hpoint m, Module.Basis.coord_apply, Module.Basis.repr_self_apply]
    simp [hbasis, add_comm]
  change b.coord l (D.curvature x (F i x) (F j x) (F k x)) = _
  rw [Proofs.M03.curvature_eq_curvatureOnFields D hU (F i) (F j) (F k)
    (hF i) (hF j) (hF k) hx]
  unfold LeviCivitaData.curvatureOnFields
  rw [hbracket i j, map_zero, sub_zero, map_sub, houter i j k l, houter j i k l]
  simp only [frameCurvatureCoefficient, Finset.sum_sub_distrib]
  ring

theorem ricci_eq_sum_frameCurvatureCoefficient
    {g : RiemannianMetric n M} (D : LeviCivitaData g)
    {U : Set M} (hU : IsOpen U)
    (F : Fin n → (y : M) → TangentSpace (𝓡 n) y)
    (hF : ∀ a, ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% (F a)) U)
    (Γ : Fin n → Fin n → Fin n → M → ℝ)
    (hcoeff : ∀ y ∈ U, ∀ a c,
      D.connection (F c) y (F a y) = ∑ l, Γ l a c y • F l y)
    {x : M} (hx : x ∈ U)
    (hΓ : ∀ l a c, MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) (Γ l a c) x)
    (b : Module.Basis (Fin n) ℝ (TangentSpace (𝓡 n) x))
    (hpoint : ∀ a, F a x = b a)
    (hbracket : ∀ a c, VectorField.mlieBracket (𝓡 n) (F a) (F c) x = 0)
    (i j : Fin n) :
    D.ricci x (F i x) (F j x) =
      ∑ k, frameCurvatureCoefficient F Γ x k i j k := by
  rw [Proofs.M03.ricci_eq_sum_basis D x (F i x) (F j x) b]
  apply Finset.sum_congr rfl
  intro k _
  rw [← hpoint k]
  exact curvature_repr_eq_frameCurvatureCoefficient D hU F hF Γ hcoeff hx hΓ
    b hpoint hbracket k i j k

end PoincareConjecture.DeTurckNative

end
