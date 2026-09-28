import PoincareConjecture.Proofs.M01.ConnectionExistenceKoszul
import PoincareConjecture.Proofs.M01.ConnectionRiesz
import PoincareConjecture.Proofs.M01.ConnectionExistenceRegularity
import Mathlib.Geometry.Manifold.VectorBundle.Tensoriality












set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

namespace ConnectionExistence

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

private noncomputable def koszulBilin (g : RiemannianMetric n M)
    (Y : (x : M) → TangentSpace (𝓡 n) x) (x : M)
    (hY : MDifferentiableAt (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% Y) x) :
    TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x →L[ℝ] ℝ :=
  TensorialAt.mkHom₂ (fun X Z ↦ koszulRHS g X Y Z x) x
    (fun Z hZ ↦
      { smul := fun hf hX ↦ by
          simpa [smul_eq_mul] using koszulRHS_smul_direction g hf hX hY hZ
        add := fun hX hX' ↦ by
          simpa using koszulRHS_add_direction g hX hX' hY hZ })
    (fun X hX ↦
      { smul := fun hf hZ ↦ by
          simpa [smul_eq_mul] using koszulRHS_smul_test g hf hX hY hZ
        add := fun hZ hZ' ↦ by
          simpa using koszulRHS_add_test g hX hY hZ hZ' })

noncomputable def leviCivitaCov (g : RiemannianMetric n M)
    (Y : (x : M) → TangentSpace (𝓡 n) x) (x : M) :
    TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  letI : FiniteDimensional ℝ (TangentSpace (𝓡 n) x) :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) x
  letI : CompleteSpace (TangentSpace (𝓡 n) x) :=
    FiniteDimensional.complete ℝ (TangentSpace (𝓡 n) x)
  by_cases hY : MDifferentiableAt (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% Y) x
  · exact (1 / 2 : ℝ) •
      (metricRieszCLM g x).comp (koszulBilin g Y x hY)
  · exact 0

theorem leviCivitaCov_inner (g : RiemannianMetric n M)
    (Y X Z : (x : M) → TangentSpace (𝓡 n) x) {x : M}
    (hX : MDifferentiableAt (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% X) x)
    (hY : MDifferentiableAt (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% Y) x)
    (hZ : MDifferentiableAt (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% Z) x) :
    g.inner x (leviCivitaCov g Y x (X x)) (Z x) =
      (1 / 2 : ℝ) * koszulRHS g X Y Z x := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : FiniteDimensional ℝ (TangentSpace (𝓡 n) x) :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) x
  let : CompleteSpace (TangentSpace (𝓡 n) x) :=
    FiniteDimensional.complete ℝ (TangentSpace (𝓡 n) x)
  simp only [leviCivitaCov, dif_pos hY, smul_apply,
    ContinuousLinearMap.comp_apply, map_smul, smul_eq_mul]
  rw [metricRieszCLM_inner]
  unfold koszulBilin
  rw [TensorialAt.mkHom₂_apply _ _ hX hZ]

end ConnectionExistence


theorem m01_exists_leviCivitaData {n : ℕ} {M : Type u}
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) : Nonempty (LeviCivitaData g) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let cov : CovariantDerivative (𝓡 n) (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    { toFun := fun Y x ↦ ConnectionExistence.leviCivitaCov g Y x
      isCovariantDerivativeOnUniv := by
        constructor
        · intro Y Y' x hY hY' hx
          apply ContinuousLinearMap.ext
          intro X
          apply ext_inner_right ℝ
          intro Z
          have hX : MDifferentiableAt (𝓡 n)
              ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
              (T% (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) X)) x :=
            FiberBundle.mdifferentiableAt_extend (𝓡 n)
              (EuclideanSpace ℝ (Fin n)) X
          have hZ : MDifferentiableAt (𝓡 n)
              ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
              (T% (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) Z)) x :=
            FiberBundle.mdifferentiableAt_extend (𝓡 n)
              (EuclideanSpace ℝ (Fin n)) Z
          have hsum := ConnectionExistence.leviCivitaCov_inner g (Y + Y')
            (FiberBundle.extend _ X) (FiberBundle.extend _ Z) hX
            (mdifferentiableAt_add_section hY hY') hZ
          have hleft := ConnectionExistence.leviCivitaCov_inner g Y
            (FiberBundle.extend _ X) (FiberBundle.extend _ Z) hX hY hZ
          have hright := ConnectionExistence.leviCivitaCov_inner g Y'
            (FiberBundle.extend _ X) (FiberBundle.extend _ Z) hX hY' hZ
          simp only [FiberBundle.extend_apply_self] at hsum hleft hright
          change g.inner x (ConnectionExistence.leviCivitaCov g (Y + Y') x X) Z =
            g.inner x ((ConnectionExistence.leviCivitaCov g Y x +
              ConnectionExistence.leviCivitaCov g Y' x) X) Z
          simp only [add_apply]
          simp only [map_add]
          simp only [add_apply]
          rw [hsum, hleft, hright,
            ConnectionExistence.koszulRHS_add_field g hX hY hY' hZ]
          ring
        · intro Y f x hY hf hx
          apply ContinuousLinearMap.ext
          intro X
          apply ext_inner_right ℝ
          intro Z
          have hX : MDifferentiableAt (𝓡 n)
              ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
              (T% (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) X)) x :=
            FiberBundle.mdifferentiableAt_extend (𝓡 n)
              (EuclideanSpace ℝ (Fin n)) X
          have hZ := FiberBundle.mdifferentiableAt_extend (𝓡 n)
            (EuclideanSpace ℝ (Fin n)) Z
          have hsfY : MDifferentiableAt (𝓡 n)
              ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% (f • Y)) x :=
            hf.smul_section hY
          change g.inner x (ConnectionExistence.leviCivitaCov g (f • Y) x X) Z =
            g.inner x ((f x • ConnectionExistence.leviCivitaCov g Y x +
              (mvfderiv (𝓡 n) f x).smulRight (Y x)) X) Z
          simp only [add_apply, map_add]
          have hsf := ConnectionExistence.leviCivitaCov_inner g (f • Y)
            (FiberBundle.extend _ X) (FiberBundle.extend _ Z) hX hsfY hZ
          have hYinner := ConnectionExistence.leviCivitaCov_inner g Y
            (FiberBundle.extend _ X) (FiberBundle.extend _ Z) hX hY hZ
          simp only [FiberBundle.extend_apply_self] at hsf hYinner
          rw [hsf]
          rw [ConnectionExistence.koszulRHS_smul_field g hf hX hY hZ]
          simp only [ContinuousLinearMap.smulRight_apply, smul_apply, map_smul,
            smul_eq_mul]
          rw [hYinner]
          simp only [FiberBundle.extend_apply_self]
          ring }
  refine ⟨
    { connection := cov
      smooth := by
        refine ⟨⟨?_⟩⟩
        intro Y hY
        let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
          ⟨g.toRiemannianMetric⟩
        have hY' : ContMDiffOn (𝓡 n)
            ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) Set.univ := by
          intro x hx
          exact (hY x hx).of_le (by simp)
        have hA : ∀ (X Y Z : (x : M) → TangentSpace (𝓡 n) x) {x : M},
            MDifferentiableAt (𝓡 n)
              ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% X) x →
            MDifferentiableAt (𝓡 n)
              ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% Y) x →
            MDifferentiableAt (𝓡 n)
              ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% Z) x →
            g.inner x (ConnectionExistence.leviCivitaCov g Y x (X x)) (Z x) =
              (1 / 2 : ℝ) * ConnectionExistence.koszulRHS g X Y Z x := by
          intro X Y Z x hX hY hZ
          exact ConnectionExistence.leviCivitaCov_inner g Y X Z hX hY hZ
        simpa only [Set.mem_univ, and_true] using
          (ConnectionExistence.koszul_operator_contMDiffOn g
            (fun Y x ↦ ConnectionExistence.leviCivitaCov g Y x)
            hA isOpen_univ Y hY')
      torsion_eq_zero := by
        apply (cov.torsion_eq_zero_iff).2
        intro X Y x hX hY
        apply ext_inner_right ℝ
        intro Z₀
        let Z : (x : M) → TangentSpace (𝓡 n) x := FiberBundle.extend
          (EuclideanSpace ℝ (Fin n)) Z₀
        have hZ : MDifferentiableAt (𝓡 n)
            ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% Z) x :=
          FiberBundle.mdifferentiableAt_extend (𝓡 n)
            (EuclideanSpace ℝ (Fin n)) Z₀
        change g.inner x
          (ConnectionExistence.leviCivitaCov g Y x (X x) -
            ConnectionExistence.leviCivitaCov g X x (Y x)) Z₀ =
          g.inner x (VectorField.mlieBracket (𝓡 n) X Y x) Z₀
        simp only [map_sub]
        change (g.inner x (ConnectionExistence.leviCivitaCov g Y x (X x)) Z₀ -
          g.inner x (ConnectionExistence.leviCivitaCov g X x (Y x)) Z₀) =
          g.inner x (VectorField.mlieBracket (𝓡 n) X Y x) Z₀
        have hYinner := ConnectionExistence.leviCivitaCov_inner g Y X Z hX hY hZ
        have hXinner := ConnectionExistence.leviCivitaCov_inner g X Y Z hY hX hZ
        have hZx : Z x = Z₀ := by
          simp [Z]
        rw [hZx] at hYinner hXinner
        rw [hYinner, hXinner]
        have hswap := ConnectionExistence.koszulRHS_swap_diff g hX hY hZ
        rw [hZx] at hswap
        calc
          _ = (1 / 2 : ℝ) *
              (ConnectionExistence.koszulRHS g X Y Z x -
                ConnectionExistence.koszulRHS g Y X Z x) := by ring
          _ = _ := by rw [hswap]; ring
      metricCompatible := by
        apply (CovariantDerivative.isMetricCompatible_iff cov).2
        intro x X Y Z hX hY hZ
        change mvfderiv (𝓡 n) (fun y ↦ g.inner y (Y y) (Z y)) x (X x) =
          g.inner x (ConnectionExistence.leviCivitaCov g Y x (X x)) (Z x) +
            g.inner x (Y x) (ConnectionExistence.leviCivitaCov g Z x (X x))
        rw [ConnectionExistence.leviCivitaCov_inner g Y X Z hX hY hZ]
        have hs := g.symm x (Y x)
          (ConnectionExistence.leviCivitaCov g Z x (X x))
        rw [hs, ConnectionExistence.leviCivitaCov_inner g Z X Y hX hZ hY]
        have hk := ConnectionExistence.koszulRHS_compat_sum g hX hY hZ
        linarith [hk] }⟩

end PoincareConjecture
