import PoincareConjecture.Proofs.M03.CurvatureExtension
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Local.Energy.Comparison.ScalarCommutator
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Local.Curvature.Calculus.CurvatureTensoriality

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.RicciFlow.Local

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem curvatureOnFields_pair_skew {g : RiemannianMetric n M}
    (D : LeviCivitaData g) {U : Set M} (hU : IsOpen U)
    (X Y Z W : (x : M) → TangentSpace (𝓡 n) x)
    (hX : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% X) U)
    (hY : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) U)
    (hZ : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Z) U)
    (hW : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% W) U)
    {x : M} (hx : x ∈ U) :
    g.inner x (D.curvatureOnFields X Y Z x) (W x) =
      -g.inner x (Z x) (D.curvatureOnFields X Y W x) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hmd (A : (y : M) → TangentSpace (𝓡 n) y)
      (hA : ContMDiffOn (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% A) U)
      {y : M} (hy : y ∈ U) :
      MDifferentiableAt (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% A) y :=
    (hA.contMDiffAt (hU.mem_nhds hy)).mdifferentiableAt (by simp)
  have hsecond (A B : (y : M) → TangentSpace (𝓡 n) y)
      (hB : ContMDiffOn (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% B) U) :
      mvfderiv (𝓡 n)
          (fun y => mvfderiv (𝓡 n) (fun z => g.inner z (Z z) (W z)) y (B y))
          x (A x) =
        g.inner x (D.connection (fun y => D.connection Z y (B y)) x (A x)) (W x) +
        g.inner x (D.connection Z x (B x)) (D.connection W x (A x)) +
        (g.inner x (D.connection Z x (A x)) (D.connection W x (B x)) +
          g.inner x (Z x) (D.connection (fun y => D.connection W y (B y)) x (A x))) := by
    have hBZ := D.contMDiffOn_connection_apply hU B Z hB hZ
    have hBW := D.contMDiffOn_connection_apply hU B W hB hW
    have heq :
        (fun y => mvfderiv (𝓡 n) (fun z => g.inner z (Z z) (W z)) y (B y))
          =ᶠ[𝓝 x] (fun y =>
            g.inner y (D.connection Z y (B y)) (W y) +
              g.inner y (Z y) (D.connection W y (B y))) := by
      filter_upwards [hU.mem_nhds hx] with y hy
      exact D.localTheory_mvfderiv_inner B Z W (hmd Z hZ hy) (hmd W hW hy)
    have hd :
        mvfderiv (𝓡 n)
            (fun y => mvfderiv (𝓡 n) (fun z => g.inner z (Z z) (W z)) y (B y)) x =
          mvfderiv (𝓡 n) (fun y =>
            g.inner y (D.connection Z y (B y)) (W y) +
              g.inner y (Z y) (D.connection W y (B y))) x := by
      apply ContinuousLinearMap.ext
      intro v
      change mfderiv (𝓡 n) 𝓘(ℝ, ℝ)
          (fun y => mvfderiv (𝓡 n) (fun z => g.inner z (Z z) (W z)) y (B y)) x v =
        mfderiv (𝓡 n) 𝓘(ℝ, ℝ) (fun y =>
          g.inner y (D.connection Z y (B y)) (W y) +
            g.inner y (Z y) (D.connection W y (B y))) x v
      exact congrArg (fun L => L v) (heq.mfderiv_eq (I := 𝓡 n) (I' := 𝓘(ℝ, ℝ)))
    have hp₁ : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ)
        (fun y => g.inner y (D.connection Z y (B y)) (W y)) x :=
      (hmd _ hBZ hx).inner_bundle (hmd W hW hx)
    have hp₂ : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ)
        (fun y => g.inner y (Z y) (D.connection W y (B y))) x :=
      (hmd Z hZ hx).inner_bundle (hmd _ hBW hx)
    rw [hd, mvfderiv_fun_add hp₁ hp₂, add_apply,
      D.localTheory_mvfderiv_inner A _ W (hmd _ hBZ hx) (hmd W hW hx),
      D.localTheory_mvfderiv_inner A Z _ (hmd Z hZ hx) (hmd _ hBW hx)]
  have hpair : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun y => g.inner y (Z y) (W y)) U := hZ.inner_bundle hW
  have hcomm := mvfderiv_mlieBracket_eq_commutator hU hpair X Y hX hY hx
  rw [D.localTheory_mvfderiv_inner (VectorField.mlieBracket (𝓡 n) X Y) Z W
    (hmd Z hZ hx) (hmd W hW hx), hsecond X Y hY, hsecond Y X hX] at hcomm
  delta LeviCivitaData.curvatureOnFields
  simp only [map_sub, sub_apply]
  linarith only [hcomm]

theorem curvatureOnFields_pointwise_third {g : RiemannianMetric n M}
    (D : LeviCivitaData g) {U : Set M} (hU : IsOpen U)
    (X Y Z Z' : (x : M) → TangentSpace (𝓡 n) x)
    (hX : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% X) U)
    (hY : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) U)
    (hZ : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Z) U)
    (hZ' : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Z') U)
    {x : M} (hx : x ∈ U) (hZZ' : Z x = Z' x) :
    D.curvatureOnFields X Y Z x = D.curvatureOnFields X Y Z' x := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  apply ext_inner_right ℝ
  intro w
  change g.inner x (D.curvatureOnFields X Y Z x) w =
    g.inner x (D.curvatureOnFields X Y Z' x) w
  obtain ⟨V, hV, hw⟩ :=
    FiberBundle.exists_contMDiffOn_extend (k := ∞) (𝓡 n) (EuclideanSpace ℝ (Fin n)) w
  obtain ⟨S, hS, hSopen, hxS⟩ := mem_nhds_iff.mp (Filter.inter_mem (hU.mem_nhds hx) hV)
  have hXS := hX.mono fun _ hy => (hS hy).1
  have hYS := hY.mono fun _ hy => (hS hy).1
  have hwS := hw.mono fun _ hy => (hS hy).2
  have hleft := curvatureOnFields_pair_skew D hSopen X Y Z
    (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) w) hXS hYS
    (hZ.mono fun _ hy => (hS hy).1) hwS hxS
  have hright := curvatureOnFields_pair_skew D hSopen X Y Z'
    (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) w) hXS hYS
    (hZ'.mono fun _ hy => (hS hy).1) hwS hxS
  rw [FiberBundle.extend_apply_self] at hleft hright
  rw [hleft, hright, hZZ']

theorem curvature_eq_curvatureOnFields {g : RiemannianMetric n M}
    (D : LeviCivitaData g) {U : Set M} (hU : IsOpen U)
    (X Y Z : (x : M) → TangentSpace (𝓡 n) x)
    (hX : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% X) U)
    (hY : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) U)
    (hZ : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Z) U)
    {x : M} (hx : x ∈ U) :
    D.curvature x (X x) (Y x) (Z x) = D.curvatureOnFields X Y Z x := by
  obtain ⟨V, hV, hZE⟩ :=
    FiberBundle.exists_contMDiffOn_extend (k := ∞) (𝓡 n)
      (EuclideanSpace ℝ (Fin n)) (Z x)
  obtain ⟨S, hS, hSopen, hxS⟩ := mem_nhds_iff.mp (Filter.inter_mem (hU.mem_nhds hx) hV)
  have hXS := hX.mono fun _ hy => (hS hy).1
  have hYS := hY.mono fun _ hy => (hS hy).1
  have hZS := hZ.mono fun _ hy => (hS hy).1
  have hZES := hZE.mono fun _ hy => (hS hy).2
  have hXm := (hX.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)
  have hYm := (hY.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)
  have hXE := FiberBundle.mdifferentiableAt_extend (𝓡 n)
    (EuclideanSpace ℝ (Fin n)) (X x)
  have hYE := FiberBundle.mdifferentiableAt_extend (𝓡 n)
    (EuclideanSpace ℝ (Fin n)) (Y x)
  delta LeviCivitaData.curvature
  trans D.curvatureOnFields X (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (Y x))
    (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (Z x)) x
  · exact (curvatureOnFields_tensorial_first D hSopen _ _ hZES hxS).pointwise
      hXE hXm (FiberBundle.extend_apply_self _ _)
  trans D.curvatureOnFields X Y (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (Z x)) x
  · exact (curvatureOnFields_tensorial_second D hSopen _ _ hZES hxS).pointwise
      hYE hYm (FiberBundle.extend_apply_self _ _)
  exact curvatureOnFields_pointwise_third D hSopen X Y _ Z hXS hYS hZES hZS hxS
    (FiberBundle.extend_apply_self _ _)

end PoincareConjecture.RicciFlow.Local
