/- Adapted from Mapher `PoincareMT/Proofs/M03/Existence/PullbackRicciNative.lean` at
f927d9e1f0810042766d3b5f64d3f4da02ee93cc. See
`references/ricci-flow/mapher/local-theory/port.json`. -/

import PoincareLib.Geometry.Riemannian.Connection
import PoincareLib.Geometry.RicciFlow.Local.Curvature.Calculus.CurvatureTrace
import PoincareLib.Geometry.RicciFlow.Local.Gauge.Pullback.PullbackConnection

/-!
# Finite-dimensional Ricci trace transport

The pullback connection calculation is pointwise, while the native Ricci
definition is a trace in a metric orthonormal basis.  This file isolates the
finite-dimensional step: a linear isometry transports the orthonormal basis
and a four-tensor identity transports the corresponding finite sum.  The
geometric curvature identity is deliberately an explicit input, so this
adapter does not conceal the producer's connection or flow obligations.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators

noncomputable section

namespace PoincareMT

universe u

/-! The bare finite sum is useful when the curvature transport is first proved
as a four-covariant identity. -/
theorem sum_fourTensor_naturality_of_basis_map
    {V W : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) (b' : OrthonormalBasis ι ℝ W)
    (L : V ≃ₗᵢ[ℝ] W)
    (hframe : ∀ i, b' i = L (b i))
    (B : V → V → V → V → ℝ) (B' : W → W → W → W → ℝ)
    (hB : ∀ x y z w, B' (L x) (L y) (L z) (L w) = B x y z w)
    (x y : V) :
    ∑ i, B x (b i) y (b i) = ∑ i, B' (L x) (b' i) (L y) (b' i) := by
  apply Finset.sum_congr rfl
  intro i hi
  rw [hframe i]
  exact (hB x (b i) y (b i)).symm

/-! A version directly phrased for the native Ricci contraction.  The two
metric arguments may live on different tangent fibers; the caller supplies
the orthonormal bases and the linear-isometry curvature identity. -/
theorem ricci_naturality_of_basis_map
    {V W : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    {ι : Type*} [Fintype ι]
    (RV : V → V → V → V → ℝ) (RW : W → W → W → W → ℝ)
    (b : OrthonormalBasis ι ℝ V) (b' : OrthonormalBasis ι ℝ W)
    (L : V ≃ₗᵢ[ℝ] W)
    (hframe : ∀ i, b' i = L (b i))
    (hB : ∀ x y z w, RW (L x) (L y) (L z) (L w) = RV x y z w)
    (x y : V) :
    ∑ i, RV x (b i) y (b i) = ∑ i, RW (L x) (b' i) (L y) (b' i) := by
  exact sum_fourTensor_naturality_of_basis_map b b' L hframe RV RW hB x y

/-! Coordinates are the form used by the native `ricci_eq_sum_basis` theorem.
The representation identity is proved from the basis expansion itself, so no
inner-product instance needs to be installed simultaneously on two tangent
fibers. -/
theorem basis_repr_map
    {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W]
    {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℝ V) (b' : Module.Basis ι ℝ W)
    (L : V ≃ₗ[ℝ] W)
    (hframe : ∀ i, b' i = L (b i))
    (z : V) (i : ι) :
    b'.repr (L z) i = b.repr z i := by
  have hz : L z = ∑ j, b.repr z j • b' j := by
    calc
      L z = L (∑ j, b.repr z j • b j) := by rw [b.sum_repr]
      _ = ∑ j, b.repr z j • L (b j) := by
        simp only [map_sum, map_smul]
      _ = ∑ j, b.repr z j • b' j := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hframe j]
  rw [hz, b'.repr_sum_self]

theorem ricci_repr_naturality_of_basis_map
    {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W]
    {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℝ V) (b' : Module.Basis ι ℝ W)
    (L : V ≃ₗ[ℝ] W)
    (hframe : ∀ i, b' i = L (b i))
    (RV : V → V → V → V) (RW : W → W → W → W)
    (hR : ∀ a c d, RW (L a) (L c) (L d) = L (RV a c d))
    (x y : V) :
    ∑ i, b.repr (RV (b i) x y) i =
      ∑ i, b'.repr (RW (b' i) (L x) (L y)) i := by
  apply Finset.sum_congr rfl
  intro i hi
  rw [hframe i, hR, basis_repr_map b b' L hframe]

/-! Ricci naturality for the concrete native pullback.  The source basis is
the pullback metric's orthonormal basis; the target basis is its image under
the differential.  The latter need not be declared orthonormal because
`ricci_eq_sum_basis` is basis-independent. -/
theorem ricci_pullback
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M)
    (Φ : Diffeomorph (𝓡 n) (𝓡 n) M M ∞)
    (hsmooth : ContMDiff (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ]
        EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)) ∞
      (fun x : M => Bundle.TotalSpace.mk'
        (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
        x (pinner g Φ x)))
    (D : LeviCivitaData g)
    (P : LeviCivitaData (pullbackMetric g Φ hsmooth))
    (x : M) (u v : TangentSpace (𝓡 n) x) :
    P.ricci x u v = D.ricci (Φ x)
      (mfderiv (𝓡 n) (𝓡 n) Φ x u)
      (mfderiv (𝓡 n) (𝓡 n) Φ x v) := by
  let A := Φ.mfderivToContinuousLinearEquiv (by simp) x
  let L : TangentSpace (𝓡 n) x ≃ₗ[ℝ] TangentSpace (𝓡 n) (Φ x) :=
    A.toLinearEquiv
  have hAeq : ∀ z : TangentSpace (𝓡 n) x,
      L z = mfderiv (𝓡 n) (𝓡 n) Φ x z := by
    intro z
    change A z = mfderiv (𝓡 n) (𝓡 n) Φ x z
    exact congrArg (fun f => f z)
      (Diffeomorph.mfderivToContinuousLinearEquiv_coe Φ (by simp) (x := x))
  letI : FiniteDimensional ℝ (TangentSpace (𝓡 n) x) :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) x
  let b : Module.Basis (Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))) ℝ
      (TangentSpace (𝓡 n) x) :=
    Module.finBasis ℝ (TangentSpace (𝓡 n) x)
  let b' : Module.Basis (Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))) ℝ
      (TangentSpace (𝓡 n) (Φ x)) := b.map L
  have hframe : ∀ i, b' i = L (b i) := by
    intro i
    rfl
  have hR : ∀ a c d, D.curvature (Φ x) (L a) (L c) (L d) =
      L (P.curvature x a c d) := by
    intro a c d
    have h := DiffeomorphNative.curvature_pullback g Φ hsmooth D P x a c d
    rw [hAeq a, hAeq c, hAeq d, hAeq (P.curvature x a c d)]
    exact h.symm
  rw [← hAeq u, ← hAeq v,
    RicciFlow.Local.ricci_eq_sum_basis P x u v b,
    RicciFlow.Local.ricci_eq_sum_basis D (Φ x) (L u) (L v) b']
  exact ricci_repr_naturality_of_basis_map b b' L hframe
    (fun a c d => P.curvature x a c d)
    (fun a c d => D.curvature (Φ x) a c d) hR u v

end PoincareMT

end
