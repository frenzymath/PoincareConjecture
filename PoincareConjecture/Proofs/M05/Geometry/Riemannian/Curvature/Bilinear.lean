
import PoincareConjecture.Definitions.Ch01.Curvature
import PoincareConjecture.Proofs.M05.Geometry.Riemannian.Connection.Regularity
import PoincareConjecture.Proofs.M05.Geometry.Riemannian.Connection.LocalRegularity
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Tactic.Module












set_option autoImplicit false
open scoped Manifold ContDiff Bundle Topology
open Bundle VectorField Filter

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

private lemma extend_add (x : M) (v w : TangentSpace (𝓡 n) x) :
    ∀ᶠ y in 𝓝 x, FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (v + w) y =
      (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v +
        FiberBundle.extend (EuclideanSpace ℝ (Fin n)) w) y := by
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x
  have hx : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  have hlin := (e.linear ℝ hx).map_add v w
  filter_upwards [e.open_baseSet.mem_nhds hx] with y hy
  simp only [FiberBundle.extend, Pi.add_apply]
  change e.symm y ((e ⟨x, v + w⟩).2) =
    e.symm y ((e ⟨x, v⟩).2) + e.symm y ((e ⟨x, w⟩).2)
  rw [hlin]
  simpa only [e.symmL_apply hy] using (e.symmL ℝ y).map_add
    ((e ⟨x, v⟩).2) ((e ⟨x, w⟩).2)

private lemma extend_smul (x : M) (c : ℝ) (v : TangentSpace (𝓡 n) x) :
    ∀ᶠ y in 𝓝 x, FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (c • v) y =
      (c • FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v) y := by
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x
  have hx : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  have hlin := (e.linear ℝ hx).map_smul c v
  filter_upwards [e.open_baseSet.mem_nhds hx] with y hy
  simp only [FiberBundle.extend, Pi.smul_apply]
  change e.symm y ((e ⟨x, c • v⟩).2) = c • e.symm y ((e ⟨x, v⟩).2)
  rw [hlin]
  simpa only [e.symmL_apply hy] using (e.symmL ℝ y).map_smul c ((e ⟨x, v⟩).2)

private lemma curvatureOnFields_add_left (D : LeviCivitaData g)
    (X X' Y Z : (x : M) → TangentSpace (𝓡 n) x) (x : M)
    (hX : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (T% X) x)
    (hX' : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (T% X') x)
    (hDX : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (T% (fun y ↦ D.connection Z y (X y))) x)
    (hDX' : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (T% (fun y ↦ D.connection Z y (X' y))) x) :
    D.curvatureOnFields (X + X') Y Z x =
      D.curvatureOnFields X Y Z x + D.curvatureOnFields X' Y Z x := by
  have heq : (fun y ↦ D.connection Z y ((X + X') y)) =
      (fun y ↦ D.connection Z y (X y)) + (fun y ↦ D.connection Z y (X' y)) := by
    funext y
    simp
  unfold curvatureOnFields
  rw [heq, D.connection.isCovariantDerivativeOn.add hDX hDX']
  simp only [Pi.add_apply, map_add, mlieBracket_add_left hX hX', add_apply]
  module

private lemma curvatureOnFields_smul_left (D : LeviCivitaData g)
    (X Y Z : (x : M) → TangentSpace (𝓡 n) x) (x : M) (c : ℝ)
    (hX : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (T% X) x)
    (hDX : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (T% (fun y ↦ D.connection Z y (X y))) x) :
    D.curvatureOnFields (c • X) Y Z x = c • D.curvatureOnFields X Y Z x := by
  have heq : (fun y ↦ D.connection Z y ((c • X) y)) =
      c • (fun y ↦ D.connection Z y (X y)) := by
    funext y
    simp
  unfold curvatureOnFields
  rw [heq, D.connection.isCovariantDerivativeOn.smul_const c hDX]
  simp only [Pi.smul_apply, map_smul, mlieBracket_const_smul_left hX,
    smul_apply]
  module

private lemma curvatureOnFields_congr_left (D : LeviCivitaData g)
    (X X' Y Z : (x : M) → TangentSpace (𝓡 n) x) (x : M)
    (hXX' : ∀ᶠ y in 𝓝 x, X y = X' y)
    (hDX : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (T% (fun y ↦ D.connection Z y (X y))) x)
    (hDX' : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (T% (fun y ↦ D.connection Z y (X' y))) x) :
    D.curvatureOnFields X Y Z x = D.curvatureOnFields X' Y Z x := by
  have hcov := D.connection.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
    hDX hDX' Filter.univ_mem (hXX'.mono fun y hy ↦ congrArg (D.connection Z y) hy)
  have hb : mlieBracket (𝓡 n) X Y x = mlieBracket (𝓡 n) X' Y x :=
    Filter.EventuallyEq.mlieBracket_vectorField_eq hXX'
      (show Y =ᶠ[𝓝 x] Y from Filter.EventuallyEq.rfl)
  unfold curvatureOnFields
  rw [hXX'.self_of_nhds, hcov, hb]

private noncomputable def curvatureLinearFirstOfRegular
    (D : LeviCivitaData g) (x : M) (y z : TangentSpace (𝓡 n) x)
    (hZ : ContMDiffAt (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))) ∞
      (fun q ↦ Bundle.TotalSpace.mk'
        (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) q
        (D.connection (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) z) q)) x) :
    TangentSpace (𝓡 n) x →ₗ[ℝ] TangentSpace (𝓡 n) x := by
  let X := fun v : TangentSpace (𝓡 n) x ↦
    FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v
  have hX (v : TangentSpace (𝓡 n) x) := FiberBundle.contMDiffAt_extend
    (V := TangentSpace (𝓡 n)) (k := ∞) (𝓡 n)
    (EuclideanSpace ℝ (Fin n)) v
  have hDX (v) := (hZ.clm_bundle_apply (hX v)).mdifferentiableAt (by simp)
  refine { toFun := fun v ↦ D.curvature x v y z, map_add' := ?_, map_smul' := ?_ }
  · intro v w
    change D.curvatureOnFields (X (v + w)) (X y) (X z) x =
      D.curvatureOnFields (X v) (X y) (X z) x +
        D.curvatureOnFields (X w) (X y) (X z) x
    have hadd := (hZ.clm_bundle_apply ((hX v).add_section (hX w))).mdifferentiableAt
      (by simp)
    rw [curvatureOnFields_congr_left D (X (v + w)) (X v + X w) (X y) (X z) x
      (extend_add x v w) (hDX (v + w)) hadd]
    exact curvatureOnFields_add_left D _ _ _ _ x
      ((hX v).mdifferentiableAt (by simp)) ((hX w).mdifferentiableAt (by simp))
      (hDX v) (hDX w)
  · intro c v
    change D.curvatureOnFields (X (c • v)) (X y) (X z) x =
      c • D.curvatureOnFields (X v) (X y) (X z) x
    have hsmul := (hZ.clm_bundle_apply ((hX v).const_smul_section (a := c))).mdifferentiableAt
      (by simp)
    rw [curvatureOnFields_congr_left D (X (c • v)) (c • X v) (X y) (X z) x
      (extend_smul x c v) (hDX (c • v)) hsmul]
    exact curvatureOnFields_smul_left D _ _ _ x c
      ((hX v).mdifferentiableAt (by simp)) (hDX v)


noncomputable def curvatureTensor_bilinear_first_third
    (D : LeviCivitaData g) (x : M) (y z : TangentSpace (𝓡 n) x) :
    TangentSpace (𝓡 n) x →ₗ[ℝ] TangentSpace (𝓡 n) x →ₗ[ℝ] ℝ := by
  let X := fun v : TangentSpace (𝓡 n) x ↦
    FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v
  have hX (v : TangentSpace (𝓡 n) x) := FiberBundle.contMDiffAt_extend
    (V := TangentSpace (𝓡 n)) (k := ∞) (𝓡 n)
    (EuclideanSpace ℝ (Fin n)) v
  have hY := hX y
  have hZ := hX z
  have hD (u : TangentSpace (𝓡 n) x) :
      MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
        (T% (fun q => D.connection (X z) q (X u q))) x := by
    simpa only [covariantDerivativeOnFields, X] using
      (D.contMDiffAt_covariantDerivativeOnFields (hX u) hZ).mdifferentiableAt
        (by simp)
  let A : TangentSpace (𝓡 n) x →ₗ[ℝ] TangentSpace (𝓡 n) x :=
    { toFun := fun u ↦ D.curvatureOnFields (X u) (X y) (X z) x
      map_add' := by
        intro u v
        have hadd := D.contMDiffAt_covariantDerivativeOnFields
          ((hX u).add_section (hX v)) hZ
        rw [curvatureOnFields_congr_left D (X (u + v)) (X u + X v) (X y) (X z) x
          (extend_add x u v)
          (hD (u + v))
          (hadd.mdifferentiableAt (by simp))]
        exact curvatureOnFields_add_left D _ _ _ _ x
          ((hX u).mdifferentiableAt (by simp)) ((hX v).mdifferentiableAt (by simp))
          (hD u) (hD v)
      map_smul' := by
        intro c u
        have hsmul := D.contMDiffAt_covariantDerivativeOnFields
          ((hX u).const_smul_section (a := c)) hZ
        rw [curvatureOnFields_congr_left D (X (c • u)) (c • X u) (X y) (X z) x
          (extend_smul x c u)
          (hD (c • u))
          (hsmul.mdifferentiableAt (by simp))]
        exact curvatureOnFields_smul_left D _ _ _ x c
          ((hX u).mdifferentiableAt (by simp))
          (hD u) }
  refine { toFun := fun u ↦ (g.inner x (A u)).toLinearMap
           map_add' := ?_
           map_smul' := ?_ }
  · intro u v
    ext w
    simp only [LinearMap.add_apply, ContinuousLinearMap.coe_coe, map_add,
      add_apply]
  · intro c u
    ext w
    simp only [LinearMap.smul_apply, ContinuousLinearMap.coe_coe, map_smul,
      smul_apply, RingHom.id_apply]

@[simp] theorem curvatureTensor_bilinear_first_third_apply
    (D : LeviCivitaData g) (x : M) (y z u v : TangentSpace (𝓡 n) x) :
    D.curvatureTensor_bilinear_first_third x y z u v = D.curvatureTensor x u y v z := rfl

end PoincareConjecture.LeviCivitaData
