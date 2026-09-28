import PoincareConjecture.Proofs.Ch01.Koszul
import PoincareConjecture.Proofs.M03.ConnectionCoordinates
import Mathlib.Geometry.Manifold.VectorBundle.Tensoriality

set_option autoImplicit false
set_option maxHeartbeats 1600000

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.Proofs.M03

theorem leviCivitaData_nonempty {n : ℕ} {M : Type u}
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) : Nonempty (LeviCivitaData g) := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let K (X Y Z : (x : M) → TangentSpace (𝓡 n) x) (x : M) : ℝ :=
    mvfderiv (𝓡 n) (fun y ↦ g.inner y (Y y) (Z y)) x (X x) +
    mvfderiv (𝓡 n) (fun y ↦ g.inner y (Z y) (X y)) x (Y x) -
    mvfderiv (𝓡 n) (fun y ↦ g.inner y (X y) (Y y)) x (Z x) +
    g.inner x (VectorField.mlieBracket (𝓡 n) X Y x) (Z x) -
    g.inner x (Y x) (VectorField.mlieBracket (𝓡 n) X Z x) -
    g.inner x (X x) (VectorField.mlieBracket (𝓡 n) Y Z x)
  have hpair {Y Z : (x : M) → TangentSpace (𝓡 n) x} {x : M}
      (hY : MDifferentiableAt (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% Y) x)
      (hZ : MDifferentiableAt (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% Z) x) :
      MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) (fun y ↦ g.inner y (Y y) (Z y)) x :=
    hY.inner_bundle hZ
  have hadd_test {X Y Z Z' : (x : M) → TangentSpace (𝓡 n) x} {x : M}
      (hX : MDifferentiableAt (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% X) x)
      (hY : MDifferentiableAt (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% Y) x)
      (hZ : MDifferentiableAt (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% Z) x)
      (hZ' : MDifferentiableAt (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% Z') x) :
      K X Y (Z + Z') x = K X Y Z x + K X Y Z' x := by
    simp only [K, Pi.add_apply, map_add, add_apply,
      mvfderiv_fun_add (hpair hY hZ) (hpair hY hZ'),
      mvfderiv_fun_add (hpair hZ hX) (hpair hZ' hX),
      VectorField.mlieBracket_add_right hZ hZ']
    ring
  have hsmul_test {X Y Z : (x : M) → TangentSpace (𝓡 n) x} {x : M} {f : M → ℝ}
      (hf : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) f x)
      (hX : MDifferentiableAt (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% X) x)
      (hY : MDifferentiableAt (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% Y) x)
      (hZ : MDifferentiableAt (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% Z) x) :
      K X Y (f • Z) x = f x * K X Y Z x := by
    simp only [K, Pi.smul_apply', map_smul, smul_apply, smul_eq_mul,
      VectorField.mlieBracket_smul_right hf hZ, map_add, add_apply,
      mvfderiv_fun_mul hf (hpair hY hZ), mvfderiv_fun_mul hf (hpair hZ hX)]
    simp only [g.symm x]
    ring
  have hadd_direction {X X' Y Z : (x : M) → TangentSpace (𝓡 n) x} {x : M}
      (hX : MDifferentiableAt (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% X) x)
      (hX' : MDifferentiableAt (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% X') x)
      (hY : MDifferentiableAt (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% Y) x)
      (hZ : MDifferentiableAt (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% Z) x) :
      K (X + X') Y Z x = K X Y Z x + K X' Y Z x := by
    simp only [K, Pi.add_apply, map_add, add_apply,
      mvfderiv_fun_add (hpair hZ hX) (hpair hZ hX'),
      mvfderiv_fun_add (hpair hX hY) (hpair hX' hY),
      VectorField.mlieBracket_add_left hX hX']
    ring
  have hsmul_direction {X Y Z : (x : M) → TangentSpace (𝓡 n) x} {x : M} {f : M → ℝ}
      (hf : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) f x)
      (hX : MDifferentiableAt (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% X) x)
      (hY : MDifferentiableAt (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% Y) x)
      (hZ : MDifferentiableAt (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% Z) x) :
      K (f • X) Y Z x = f x * K X Y Z x := by
    simp only [K, Pi.smul_apply', map_smul, smul_apply, smul_eq_mul,
      VectorField.mlieBracket_smul_left hf hX, map_add, add_apply,
      mvfderiv_fun_mul hf (hpair hZ hX), mvfderiv_fun_mul hf (hpair hX hY)]
    simp only [g.symm x]
    ring
  have hadd_field {X Y Y' Z : (x : M) → TangentSpace (𝓡 n) x} {x : M}
      (hX : MDifferentiableAt (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% X) x)
      (hY : MDifferentiableAt (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% Y) x)
      (hY' : MDifferentiableAt (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% Y') x)
      (hZ : MDifferentiableAt (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% Z) x) :
      K X (Y + Y') Z x = K X Y Z x + K X Y' Z x := by
    simp only [K, Pi.add_apply, map_add, add_apply,
      mvfderiv_fun_add (hpair hY hZ) (hpair hY' hZ),
      mvfderiv_fun_add (hpair hX hY) (hpair hX hY'),
      VectorField.mlieBracket_add_right hY hY', VectorField.mlieBracket_add_left hY hY']
    ring
  have hsmul_field {X Y Z : (x : M) → TangentSpace (𝓡 n) x} {x : M} {f : M → ℝ}
      (hf : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) f x)
      (hX : MDifferentiableAt (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% X) x)
      (hY : MDifferentiableAt (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% Y) x)
      (hZ : MDifferentiableAt (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% Z) x) :
      K X (f • Y) Z x = f x * K X Y Z x +
        2 * mvfderiv (𝓡 n) f x (X x) * g.inner x (Y x) (Z x) := by
    simp only [K, Pi.smul_apply', map_smul, smul_apply, smul_eq_mul,
      VectorField.mlieBracket_smul_left hf hY, VectorField.mlieBracket_smul_right hf hY,
      map_add, add_apply, mvfderiv_fun_mul hf (hpair hY hZ),
      mvfderiv_fun_mul hf (hpair hX hY)]
    simp only [g.symm x]
    ring
  have hswap (X Y Z : (x : M) → TangentSpace (𝓡 n) x) (x : M) :
      K X Y Z x - K Y X Z x =
        2 * g.inner x (VectorField.mlieBracket (𝓡 n) X Y x) (Z x) := by
    have h₁ : (fun y ↦ g.inner y (X y) (Z y)) =
        (fun y ↦ g.inner y (Z y) (X y)) := funext fun y ↦ g.symm y _ _
    have h₂ : (fun y ↦ g.inner y (Y y) (X y)) =
        (fun y ↦ g.inner y (X y) (Y y)) := funext fun y ↦ g.symm y _ _
    have h₃ : (fun y ↦ g.inner y (Z y) (Y y)) =
        (fun y ↦ g.inner y (Y y) (Z y)) := funext fun y ↦ g.symm y _ _
    simp only [K]
    rw [h₁, h₂, h₃, VectorField.mlieBracket_swap_apply]
    simp only [map_neg, neg_apply, g.symm x]
    ring
  have hcompat (X Y Z : (x : M) → TangentSpace (𝓡 n) x) (x : M) :
      K X Y Z x + K X Z Y x =
        2 * mvfderiv (𝓡 n) (fun y ↦ g.inner y (Y y) (Z y)) x (X x) := by
    have h₁ : (fun y ↦ g.inner y (Z y) (X y)) =
        (fun y ↦ g.inner y (X y) (Z y)) := funext fun y ↦ g.symm y _ _
    have h₂ : (fun y ↦ g.inner y (X y) (Z y)) =
        (fun y ↦ g.inner y (Z y) (X y)) := funext fun y ↦ g.symm y _ _
    have h₃ : (fun y ↦ g.inner y (X y) (Y y)) =
        (fun y ↦ g.inner y (Y y) (X y)) := funext fun y ↦ g.symm y _ _
    have h₄ : (fun y ↦ g.inner y (Z y) (Y y)) =
        (fun y ↦ g.inner y (Y y) (Z y)) := funext fun y ↦ g.symm y _ _
    have hb₁ : VectorField.mlieBracket (𝓡 n) X Y x =
        -VectorField.mlieBracket (𝓡 n) Y X x := VectorField.mlieBracket_swap_apply
    have hb₂ : VectorField.mlieBracket (𝓡 n) X Z x =
        -VectorField.mlieBracket (𝓡 n) Z X x := VectorField.mlieBracket_swap_apply
    have hb₃ : VectorField.mlieBracket (𝓡 n) Z Y x =
        -VectorField.mlieBracket (𝓡 n) Y Z x := VectorField.mlieBracket_swap_apply
    simp only [K]
    rw [h₁, h₂, h₃, h₄, hb₁, hb₂, hb₃]
    simp only [map_neg, neg_apply, g.symm x]
    ring

  let B (Y : (x : M) → TangentSpace (𝓡 n) x) (x : M)
      (hY : MDifferentiableAt (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% Y) x) :
      TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x →L[ℝ] ℝ :=
    TensorialAt.mkHom₂ (fun X Z ↦ K X Y Z x) x
      (fun Z hZ ↦
        { smul := fun hf hX ↦ by simpa [smul_eq_mul] using hsmul_direction hf hX hY hZ
          add := fun hX hX' ↦ hadd_direction hX hX' hY hZ })
      (fun X hX ↦
        { smul := fun hf hZ ↦ by simpa [smul_eq_mul] using hsmul_test hf hX hY hZ
          add := fun hZ hZ' ↦ hadd_test hX hY hZ hZ' })
  have hginv (x : M) : (g.inner x).IsInvertible := by
    let : FiniteDimensional ℝ (TangentSpace (𝓡 n) x) :=
      VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n))
        (TangentSpace (𝓡 n) : M → Type _) x
    have hinj : Function.Injective (g.inner x).toLinearMap := by
      intro a b hab
      apply ext_inner_right ℝ
      intro c
      exact congrArg (fun L : TangentSpace (𝓡 n) x →L[ℝ] ℝ ↦ L c) hab
    have hdim : Module.finrank ℝ (TangentSpace (𝓡 n) x) =
        Module.finrank ℝ (TangentSpace (𝓡 n) x →L[ℝ] ℝ) := by
      calc
        _ = Module.finrank ℝ (Module.Dual ℝ (TangentSpace (𝓡 n) x)) :=
          Subspace.dual_finrank_eq.symm
        _ = _ := (LinearMap.toContinuousLinearMap :
          (TangentSpace (𝓡 n) x →ₗ[ℝ] ℝ) ≃ₗ[ℝ]
            (TangentSpace (𝓡 n) x →L[ℝ] ℝ)).finrank_eq
    exact ⟨((g.inner x).toLinearMap.linearEquivOfInjective hinj hdim).toContinuousLinearEquiv, rfl⟩
  let A (Y : (x : M) → TangentSpace (𝓡 n) x) (x : M) :
      TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x :=
    if hY : MDifferentiableAt (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% Y) x then
      (1 / 2 : ℝ) • (g.inner x).inverse.comp (B Y x hY)
    else 0
  have hA (X Y Z : (x : M) → TangentSpace (𝓡 n) x) {x : M}
      (hX : MDifferentiableAt (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% X) x)
      (hY : MDifferentiableAt (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% Y) x)
      (hZ : MDifferentiableAt (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% Z) x) :
      g.inner x (A Y x (X x)) (Z x) = (1 / 2 : ℝ) * K X Y Z x := by
    simp only [A, dif_pos hY, smul_apply, map_smul, smul_eq_mul,
      ContinuousLinearMap.comp_apply]
    rw [(hginv x).self_apply_inverse]
    congr 1
    exact TensorialAt.mkHom₂_apply _ _ hX hZ
  let cov : CovariantDerivative (𝓡 n) (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    { toFun := A
      isCovariantDerivativeOnUniv := by
        constructor
        · intro Y Y' x hY hY' hx
          apply ContinuousLinearMap.ext
          intro u
          apply ext_inner_right ℝ
          intro v
          have hX := FiberBundle.mdifferentiableAt_extend (𝓡 n)
            (EuclideanSpace ℝ (Fin n)) u
          have hZ := FiberBundle.mdifferentiableAt_extend (𝓡 n)
            (EuclideanSpace ℝ (Fin n)) v
          have hsum := hA (FiberBundle.extend _ u) (Y + Y')
            (FiberBundle.extend _ v) hX (mdifferentiableAt_add_section hY hY') hZ
          have hleft := hA (FiberBundle.extend _ u) Y (FiberBundle.extend _ v) hX hY hZ
          have hright := hA (FiberBundle.extend _ u) Y' (FiberBundle.extend _ v) hX hY' hZ
          simp only [FiberBundle.extend_apply_self] at hsum hleft hright
          change g.inner x (A (Y + Y') x u) v = g.inner x ((A Y x + A Y' x) u) v
          simp only [add_apply, map_add]
          rw [hsum, hleft, hright, hadd_field hX hY hY' hZ]
          ring
        · intro Y f x hY hf hx
          apply ContinuousLinearMap.ext
          intro u
          apply ext_inner_right ℝ
          intro v
          have hX := FiberBundle.mdifferentiableAt_extend (𝓡 n)
            (EuclideanSpace ℝ (Fin n)) u
          have hZ := FiberBundle.mdifferentiableAt_extend (𝓡 n)
            (EuclideanSpace ℝ (Fin n)) v
          have hsf := hA (FiberBundle.extend _ u) (f • Y)
            (FiberBundle.extend _ v) hX (hf.smul_section hY) hZ
          have hinner := hA (FiberBundle.extend _ u) Y (FiberBundle.extend _ v) hX hY hZ
          simp only [FiberBundle.extend_apply_self] at hsf hinner
          change g.inner x (A (f • Y) x u) v =
            g.inner x ((f x • A Y x + (mvfderiv (𝓡 n) f x).smulRight (Y x)) u) v
          simp only [add_apply, map_add]
          rw [hsf, hsmul_field hf hX hY hZ]
          simp only [ContinuousLinearMap.smulRight_apply, smul_apply, map_smul, smul_eq_mul]
          rw [hinner]
          simp only [FiberBundle.extend_apply_self]
          ring }
  refine ⟨{
    connection := cov
    smooth := ?_
    torsion_eq_zero := ?_
    metricCompatible := ?_ }⟩
  · refine ⟨⟨?_⟩⟩
    intro Y hY
    have hY' : ContMDiffOn (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) Set.univ := by
      intro x hx
      exact (hY x hx).of_le (by simp)
    exact Proofs.M03.koszul_operator_contMDiffOn g A hA isOpen_univ Y hY'
  · apply cov.torsion_eq_zero_iff.mpr
    intro X Y x hX hY
    apply ext_inner_right ℝ
    intro v
    let Z := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v
    have hZ := FiberBundle.mdifferentiableAt_extend (𝓡 n) (EuclideanSpace ℝ (Fin n)) v
    have hZx : Z x = v := FiberBundle.extend_apply_self (EuclideanSpace ℝ (Fin n)) v
    have hYinner := hA X Y Z hX hY hZ
    have hXinner := hA Y X Z hY hX hZ
    rw [hZx] at hYinner hXinner
    change g.inner x (A Y x (X x) - A X x (Y x)) v =
      g.inner x (VectorField.mlieBracket (𝓡 n) X Y x) v
    simp only [map_sub, sub_apply]
    rw [hYinner, hXinner]
    have hs := hswap X Y Z x
    rw [hZx] at hs
    linarith only [hs]
  · apply (CovariantDerivative.isMetricCompatible_iff cov).mpr
    intro x X Y Z hX hY hZ
    change mvfderiv (𝓡 n) (fun y ↦ g.inner y (Y y) (Z y)) x (X x) =
      g.inner x (A Y x (X x)) (Z x) + g.inner x (Y x) (A Z x (X x))
    rw [hA X Y Z hX hY hZ, g.symm x (Y x) (A Z x (X x)), hA X Z Y hX hZ hY]
    linarith only [hcompat X Y Z x]

end PoincareConjecture.Proofs.M03
