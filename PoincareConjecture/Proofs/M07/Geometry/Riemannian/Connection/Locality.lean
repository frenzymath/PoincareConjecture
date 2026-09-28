import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Connection.Uniqueness





set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology
open Bundle Filter Set

universe u

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g h : RiemannianMetric n M}



private theorem inner_connection_eq_of_inner_eq_nhds
    (D : LeviCivitaData g) (D' : LeviCivitaData h)
    {Y : (x : M) → TangentSpace (𝓡 n) x} {x : M}
    (hY : MDifferentiableAt (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% Y) x)
    (hgh : ∀ᶠ y in 𝓝 x, ∀ a b : TangentSpace (𝓡 n) y,
      g.inner y a b = h.inner y a b)
    (v w : TangentSpace (𝓡 n) x) :
    g.inner x (D.connection Y x v) w =
      g.inner x (D'.connection Y x v) w := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hX := FiberBundle.mdifferentiableAt_extend
    (𝓡 n) (EuclideanSpace ℝ (Fin n)) v
  have hZ := FiberBundle.mdifferentiableAt_extend
    (𝓡 n) (EuclideanSpace ℝ (Fin n)) w
  have h₁ := D.koszul_identity hX hY hZ
  have h₂ := D'.koszul_identity hX hY hZ
  have hinner (a b : TangentSpace (𝓡 n) x) :
      g.inner x a b = h.inner x a b := (hgh.self_of_nhds) a b
  have hscalar (A B : (y : M) → TangentSpace (𝓡 n) y) :
      (fun y ↦ g.inner y (A y) (B y)) =ᶠ[𝓝 x]
        (fun y ↦ h.inner y (A y) (B y)) := by
    filter_upwards [hgh] with y hy
    exact hy (A y) (B y)
  let V := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v
  let W := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) w
  have hd₁ := Filter.EventuallyEq.mfderiv_eq
    (𝕜 := ℝ) (I := 𝓡 n) (I' := 𝓘(ℝ, ℝ)) (hscalar Y W)
  have hd₂ := Filter.EventuallyEq.mfderiv_eq
    (𝕜 := ℝ) (I := 𝓡 n) (I' := 𝓘(ℝ, ℝ)) (hscalar W V)
  have hd₃ := Filter.EventuallyEq.mfderiv_eq
    (𝕜 := ℝ) (I := 𝓡 n) (I' := 𝓘(ℝ, ℝ)) (hscalar V Y)
  dsimp [V, W] at hd₁ hd₂ hd₃
  have hda := congrArg (fun L ↦ L v) hd₁
  have hdb := congrArg (fun L ↦ L (Y x)) hd₂
  have hdc := congrArg (fun L ↦ L w) hd₃
  change ((mvfderiv (𝓡 n) (fun y ↦ g.inner y (Y y)
      (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) w y)) x) v =
    (mvfderiv (𝓡 n) (fun y ↦ h.inner y (Y y)
      (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) w y)) x) v) at hda
  change ((mvfderiv (𝓡 n) (fun y ↦ g.inner y
      (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) w y)
      (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v y)) x) (Y x) =
    (mvfderiv (𝓡 n) (fun y ↦ h.inner y
      (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) w y)
      (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v y)) x) (Y x)) at hdb
  change ((mvfderiv (𝓡 n) (fun y ↦ g.inner y
      (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v y) (Y y)) x) w =
    (mvfderiv (𝓡 n) (fun y ↦ h.inner y
      (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v y) (Y y)) x) w) at hdc
  simp only [covariantDerivativeOnFields, FiberBundle.extend_apply_self] at h₁ h₂
  simp_rw [← hinner] at h₂
  rw [← hda, ← hdb, ← hdc] at h₂
  linarith [h₁, h₂]


theorem connection_eq_of_inner_eq_nhds
    (D : LeviCivitaData g) (D' : LeviCivitaData h)
    {Y : (x : M) → TangentSpace (𝓡 n) x} {x : M}
    (hY : MDifferentiableAt (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% Y) x)
    (hgh : ∀ᶠ y in 𝓝 x, ∀ a b : TangentSpace (𝓡 n) y,
      g.inner y a b = h.inner y a b)
    (v : TangentSpace (𝓡 n) x) :
    D.connection Y x v = D'.connection Y x v := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  apply ext_inner_right ℝ
  intro w
  exact D.inner_connection_eq_of_inner_eq_nhds D' hY hgh v w


theorem connection_covariantDerivativeOnFields_eq_of_inner_eq_nhds
    (D : LeviCivitaData g) (D' : LeviCivitaData h)
    {X Y : (x : M) → TangentSpace (𝓡 n) x} {x : M}
    (hX : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% X) x)
    (hY : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) x)
    (hgh : ∀ᶠ y in 𝓝 x, ∀ a b : TangentSpace (𝓡 n) y,
      g.inner y a b = h.inner y a b)
    (v : TangentSpace (𝓡 n) x) :
    D.connection (D.covariantDerivativeOnFields X Y) x v =
      D'.connection (D'.covariantDerivativeOnFields X Y) x v := by
  have hD := D.contMDiffAt_covariantDerivativeOnFields hX hY
  have hD' := D'.contMDiffAt_covariantDerivativeOnFields hX hY
  have heq : D.covariantDerivativeOnFields X Y =ᶠ[𝓝 x]
      D'.covariantDerivativeOnFields X Y := by
    filter_upwards [hgh.eventually_nhds, eventually_mdifferentiableAt_of_contMDiffAt hY]
      with y hgy hy
    exact D.connection_eq_of_inner_eq_nhds D' hy hgy (X y)
  have hconn := D.connection.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
    (hD.mdifferentiableAt (by simp)) (hD'.mdifferentiableAt (by simp)) (by simp) heq
  exact (congrArg (fun L ↦ L v) hconn).trans
    (D.connection_eq_of_inner_eq_nhds D' (hD'.mdifferentiableAt (by simp)) hgh v)


theorem curvatureOnFields_eq_of_inner_eq_nhds
    (D : LeviCivitaData g) (D' : LeviCivitaData h)
    {X Y Z : (x : M) → TangentSpace (𝓡 n) x} {x : M}
    (hX : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% X) x)
    (hY : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) x)
    (hZ : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Z) x)
    (hgh : ∀ᶠ y in 𝓝 x, ∀ a b : TangentSpace (𝓡 n) y,
      g.inner y a b = h.inner y a b) :
    D.curvatureOnFields X Y Z x = D'.curvatureOnFields X Y Z x := by
  change D.connection (D.covariantDerivativeOnFields Y Z) x (X x) -
      D.connection (D.covariantDerivativeOnFields X Z) x (Y x) -
      D.connection Z x (VectorField.mlieBracket (𝓡 n) X Y x) = _
  rw [D.connection_covariantDerivativeOnFields_eq_of_inner_eq_nhds D' hY hZ hgh,
    D.connection_covariantDerivativeOnFields_eq_of_inner_eq_nhds D' hX hZ hgh,
    D.connection_eq_of_inner_eq_nhds D' (hZ.mdifferentiableAt (by simp)) hgh]
  rfl


theorem curvature_eq_of_inner_eq_nhds
    (D : LeviCivitaData g) (D' : LeviCivitaData h) {x : M}
    (hgh : ∀ᶠ y in 𝓝 x, ∀ a b : TangentSpace (𝓡 n) y,
      g.inner y a b = h.inner y a b)
    (u v w : TangentSpace (𝓡 n) x) :
    D.curvature x u v w = D'.curvature x u v w :=
  D.curvatureOnFields_eq_of_inner_eq_nhds D'
    (FiberBundle.contMDiffAt_extend (𝓡 n) (EuclideanSpace ℝ (Fin n)) u)
    (FiberBundle.contMDiffAt_extend (𝓡 n) (EuclideanSpace ℝ (Fin n)) v)
    (FiberBundle.contMDiffAt_extend (𝓡 n) (EuclideanSpace ℝ (Fin n)) w) hgh


theorem curvatureTensor_eq_of_inner_eq_nhds
    (D : LeviCivitaData g) (D' : LeviCivitaData h) {x : M}
    (hgh : ∀ᶠ y in 𝓝 x, ∀ a b : TangentSpace (𝓡 n) y,
      g.inner y a b = h.inner y a b)
    (u v w z : TangentSpace (𝓡 n) x) :
    D.curvatureTensor x u v w z = D'.curvatureTensor x u v w z := by
  unfold curvatureTensor
  rw [D.curvature_eq_of_inner_eq_nhds D' hgh]
  exact hgh.self_of_nhds _ _

end PoincareConjecture.LeviCivitaData
