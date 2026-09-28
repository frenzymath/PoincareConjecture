import PoincareConjecture.Definitions.Ch01.ScalarOperators
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.VectorBundle.Tensoriality

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M48ScalarCalculus

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem scalar_directional_mdifferentiableAt {phi : M → ℝ} {x : M}
    (hphi : ContMDiffAt (𝓡 n) 𝓘(ℝ) ∞ phi x)
    (Y : (y : M) → TangentSpace (𝓡 n) y)
    (hY : MDifferentiableAt (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% Y) x) :
    MDifferentiableAt (𝓡 n) 𝓘(ℝ)
      (fun y ↦ mvfderiv (𝓡 n) phi y (Y y)) x := by
  have hd := MDifferentiableAt.clm_apply_of_inCoordinates
    (b₁ := id) (b₂ := phi)
    ((hphi.mfderiv_const (m := ∞) (n := ∞) (by simp)).mdifferentiableAt
      (by simp)) hY (hphi.mdifferentiableAt (by simp))
  have hs := (mdifferentiableAt_totalSpace 𝓘(ℝ) _ |>.mp hd).2
  convert hs using 1
  funext y
  simp only [id_eq, trivializationAt_model_space_apply]
  rfl

theorem hessian_tensorial_left (D : LeviCivitaData g) (phi : M → ℝ)
    (Y : (y : M) → TangentSpace (𝓡 n) y) (x : M) :
    TensorialAt (𝓡 n) (EuclideanSpace ℝ (Fin n))
      (fun X ↦ D.hessianOnFields phi X Y x) x where
  smul _ _ := by
    simp only [LeviCivitaData.hessianOnFields, Pi.smul_apply',
      map_smul, smul_eq_mul]
    ring
  add _ _ := by
    simp only [LeviCivitaData.hessianOnFields, Pi.add_apply, map_add]
    ring

theorem hessian_tensorial_right (D : LeviCivitaData g) (phi : M → ℝ)
    (X : (y : M) → TangentSpace (𝓡 n) y) (x : M)
    (hphi : ContMDiffAt (𝓡 n) 𝓘(ℝ) ∞ phi x) :
    TensorialAt (𝓡 n) (EuclideanSpace ℝ (Fin n))
      (fun Y ↦ D.hessianOnFields phi X Y x) x where
  smul ha hY := by
    simp only [LeviCivitaData.hessianOnFields, Pi.smul_apply', map_smul]
    rw [mvfderiv_fun_smul ha (scalar_directional_mdifferentiableAt hphi _ hY)]
    rw [D.connection.isCovariantDerivativeOn.leibniz hY ha]
    simp only [add_apply, smul_apply,
      ContinuousLinearMap.smulRight_apply, map_add, map_smul, smul_eq_mul]
    ring
  add hY hZ := by
    simp only [LeviCivitaData.hessianOnFields, Pi.add_apply, map_add]
    rw [mvfderiv_fun_add
      (scalar_directional_mdifferentiableAt hphi _ hY)
      (scalar_directional_mdifferentiableAt hphi _ hZ)]
    rw [D.connection.isCovariantDerivativeOn.add hY hZ]
    simp only [add_apply, map_add]
    ring

noncomputable def hessianBilin (D : LeviCivitaData g) (phi : M → ℝ) (x : M)
    (hphi : ContMDiffAt (𝓡 n) 𝓘(ℝ) ∞ phi x) :
    TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x →L[ℝ] ℝ :=
  TensorialAt.mkHom₂ (fun X Y ↦ D.hessianOnFields phi X Y x) x
    (fun Y _ ↦ hessian_tensorial_left D phi Y x)
    (fun X _ ↦ hessian_tensorial_right D phi X x hphi)

theorem hessianBilin_apply (D : LeviCivitaData g) (phi : M → ℝ) (x : M)
    (hphi : ContMDiffAt (𝓡 n) 𝓘(ℝ) ∞ phi x)
    (X Y : (y : M) → TangentSpace (𝓡 n) y)
    (hX : MDifferentiableAt (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% X) x)
    (hY : MDifferentiableAt (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% Y) x) :
    hessianBilin D phi x hphi (X x) (Y x) = D.hessianOnFields phi X Y x := by
  exact TensorialAt.mkHom₂_apply _ _ hX hY

theorem hessianBilin_apply_eq_hessian (D : LeviCivitaData g) (phi : M → ℝ) (x : M)
    (hphi : ContMDiffAt (𝓡 n) 𝓘(ℝ) ∞ phi x)
    (v w : TangentSpace (𝓡 n) x) :
    hessianBilin D phi x hphi v w = D.hessian phi x v w := by
  exact TensorialAt.mkHom₂_apply_eq_extend _ _ v w

theorem hessian_eq_fields (D : LeviCivitaData g) (phi : M → ℝ) (x : M)
    (hphi : ContMDiffAt (𝓡 n) 𝓘(ℝ) ∞ phi x)
    (X Y : (y : M) → TangentSpace (𝓡 n) y)
    (hX : MDifferentiableAt (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% X) x)
    (hY : MDifferentiableAt (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% Y) x) :
    D.hessian phi x (X x) (Y x) = D.hessianOnFields phi X Y x := by
  rw [← hessianBilin_apply_eq_hessian D phi x hphi]
  exact hessianBilin_apply D phi x hphi X Y hX hY

end PoincareConjecture.M48ScalarCalculus
