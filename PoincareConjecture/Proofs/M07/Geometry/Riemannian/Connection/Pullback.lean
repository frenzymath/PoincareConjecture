import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Connection.Locality

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology
open Bundle Filter Set VectorField

universe u v

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type u} {N : Type v}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold (𝓡 n) ∞ N]
  {g : RiemannianMetric n M} {h : RiemannianMetric n N}
  {f : M → N} {x : M}

private lemma mdifferentiableAt_inner_fields
    {A B : (y : N) → TangentSpace (𝓡 n) y} {z : N}
    (hA : MDifferentiableAt (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% A) z)
    (hB : MDifferentiableAt (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% B) z) :
    MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ)
      (fun y ↦ h.inner y (A y) (B y)) z := by
  have hA' := ((h.contMDiff z).mdifferentiableAt (by simp)).clm_bundle_apply hA
  have hAB := hA'.clm_bundle_apply hB
  simpa using (mdifferentiableAt_totalSpace (𝓡 n) _).mp hAB |>.2

private lemma inner_mpullback_of_metric_pullback
    (hinv : (mfderiv (𝓡 n) (𝓡 n) f x).IsInvertible)
    (hmetric : ∀ a b : TangentSpace (𝓡 n) x,
      g.inner x a b = h.inner (f x)
        (mfderiv (𝓡 n) (𝓡 n) f x a) (mfderiv (𝓡 n) (𝓡 n) f x b))
    (A B : (y : N) → TangentSpace (𝓡 n) y) :
    g.inner x (mpullback (𝓡 n) (𝓡 n) f A x) (mpullback (𝓡 n) (𝓡 n) f B x) =
      h.inner (f x) (A (f x)) (B (f x)) := by
  rw [hmetric]
  simp only [mpullback, hinv.self_apply_inverse]

private lemma mvfderiv_inner_mpullback_of_metric_pullback
    (hf : MDifferentiableAt (𝓡 n) (𝓡 n) f x)
    (hinv : ∀ᶠ y in 𝓝 x, (mfderiv (𝓡 n) (𝓡 n) f y).IsInvertible)
    (hmetric : ∀ᶠ y in 𝓝 x, ∀ a b : TangentSpace (𝓡 n) y,
      g.inner y a b = h.inner (f y)
        (mfderiv (𝓡 n) (𝓡 n) f y a) (mfderiv (𝓡 n) (𝓡 n) f y b))
    {A B : (y : N) → TangentSpace (𝓡 n) y}
    (hA : MDifferentiableAt (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% A) (f x))
    (hB : MDifferentiableAt (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% B) (f x))
    (C : (y : N) → TangentSpace (𝓡 n) y) :
    mvfderiv (𝓡 n) (fun y ↦ g.inner y
        (mpullback (𝓡 n) (𝓡 n) f A y) (mpullback (𝓡 n) (𝓡 n) f B y)) x
        (mpullback (𝓡 n) (𝓡 n) f C x) =
      mvfderiv (𝓡 n) (fun y ↦ h.inner y (A y) (B y)) (f x) (C (f x)) := by
  have heq : (fun y ↦ g.inner y (mpullback (𝓡 n) (𝓡 n) f A y)
      (mpullback (𝓡 n) (𝓡 n) f B y)) =ᶠ[𝓝 x]
      (fun y ↦ h.inner (f y) (A (f y)) (B (f y))) := by
    filter_upwards [hinv, hmetric] with y hi hm
    exact inner_mpullback_of_metric_pullback hi hm A B
  have hd := heq.mfderiv_eq (I := 𝓡 n) (I' := 𝓘(ℝ, ℝ))
  change mvfderiv (𝓡 n) (fun y ↦ g.inner y
      (mpullback (𝓡 n) (𝓡 n) f A y) (mpullback (𝓡 n) (𝓡 n) f B y)) x =
    mvfderiv (𝓡 n) ((fun y ↦ h.inner y (A y) (B y)) ∘ f) x at hd
  rw [hd, mvfderiv_comp x (mdifferentiableAt_inner_fields (h := h) hA hB) hf]
  simp only [ContinuousLinearMap.comp_apply, mpullback,
    hinv.self_of_nhds.self_apply_inverse]

theorem connection_mpullback_of_metric_pullback_of_contMDiffAt_two
    (D : LeviCivitaData g) (D' : LeviCivitaData h)
    (hf : ContMDiffAt (𝓡 n) (𝓡 n) 2 f x)
    (hinv : ∀ᶠ y in 𝓝 x, (mfderiv (𝓡 n) (𝓡 n) f y).IsInvertible)
    (hmetric : ∀ᶠ y in 𝓝 x, ∀ a b : TangentSpace (𝓡 n) y,
      g.inner y a b = h.inner (f y)
        (mfderiv (𝓡 n) (𝓡 n) f y a) (mfderiv (𝓡 n) (𝓡 n) f y b))
    {Y : (y : N) → TangentSpace (𝓡 n) y}
    (hY : MDifferentiableAt (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% Y) (f x))
    (v : TangentSpace (𝓡 n) x) :
    D.connection (mpullback (𝓡 n) (𝓡 n) f Y) x v =
      (mfderiv (𝓡 n) (𝓡 n) f x).inverse
        (D'.connection Y (f x) (mfderiv (𝓡 n) (𝓡 n) f x v)) := by
  have : IsManifold (𝓡 n) (minSmoothness ℝ 2) M := by
    simpa only [minSmoothness_of_isRCLikeNormedField] using
      (inferInstance : IsManifold (𝓡 n) 2 M)
  have : IsManifold (𝓡 n) (minSmoothness ℝ 2) N := by
    simpa only [minSmoothness_of_isRCLikeNormedField] using
      (inferInstance : IsManifold (𝓡 n) 2 N)
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  apply ext_inner_right ℝ
  intro w
  change g.inner x _ w = g.inner x _ w
  let X := FiberBundle.extend (EuclideanSpace ℝ (Fin n))
    (mfderiv (𝓡 n) (𝓡 n) f x v)
  let Z := FiberBundle.extend (EuclideanSpace ℝ (Fin n))
    (mfderiv (𝓡 n) (𝓡 n) f x w)
  have hX := FiberBundle.mdifferentiableAt_extend (𝓡 n)
    (EuclideanSpace ℝ (Fin n)) (mfderiv (𝓡 n) (𝓡 n) f x v)
  have hZ := FiberBundle.mdifferentiableAt_extend (𝓡 n)
    (EuclideanSpace ℝ (Fin n)) (mfderiv (𝓡 n) (𝓡 n) f x w)
  have hi := hinv.self_of_nhds
  have hpX := hX.mpullback_vectorField hf hi le_rfl
  have hpY := hY.mpullback_vectorField hf hi le_rfl
  have hpZ := hZ.mpullback_vectorField hf hi le_rfl
  have hk := D.koszul_identity hpX hpY hpZ
  have hk' := D'.koszul_identity hX hY hZ
  have hv : mpullback (𝓡 n) (𝓡 n) f X x = v := by
    simp only [X, mpullback, FiberBundle.extend_apply_self, hi.inverse_apply_self]
  have hw : mpullback (𝓡 n) (𝓡 n) f Z x = w := by
    simp only [Z, mpullback, FiberBundle.extend_apply_self, hi.inverse_apply_self]
  have hd (A B C : (y : N) → TangentSpace (𝓡 n) y)
      (hA : MDifferentiableAt (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% A) (f x))
      (hB : MDifferentiableAt (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% B) (f x)) :=
    mvfderiv_inner_mpullback_of_metric_pullback (g := g) (h := h)
      (hf.mdifferentiableAt (by simp)) hinv hmetric hA hB C
  have hb (A B C : (y : N) → TangentSpace (𝓡 n) y)
      (hA : MDifferentiableAt (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% A) (f x))
      (hB : MDifferentiableAt (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% B) (f x)) :
      g.inner x (mlieBracket (𝓡 n) (mpullback (𝓡 n) (𝓡 n) f A)
        (mpullback (𝓡 n) (𝓡 n) f B) x) (mpullback (𝓡 n) (𝓡 n) f C x) =
      h.inner (f x) (mlieBracket (𝓡 n) A B (f x)) (C (f x)) := by
    rw [← mpullback_mlieBracket hA hB hf (by simp only [minSmoothness_of_isRCLikeNormedField]; exact le_rfl)]
    exact inner_mpullback_of_metric_pullback hi hmetric.self_of_nhds _ _
  rw [hd Y Z X hY hZ, hd Z X Y hZ hX, hd X Y Z hX hY,
    hb X Y Z hX hY, hb Y Z X hY hZ, hb Z X Y hZ hX] at hk
  have heq : g.inner x (D.connection (mpullback (𝓡 n) (𝓡 n) f Y) x v) w =
      h.inner (f x) (D'.connection Y (f x) (mfderiv (𝓡 n) (𝓡 n) f x v))
        (mfderiv (𝓡 n) (𝓡 n) f x w) := by
    dsimp [X] at hv
    dsimp [Z] at hw
    simp only [covariantDerivativeOnFields, hv, hw, X, Z,
      FiberBundle.extend_apply_self] at hk
    simp only [covariantDerivativeOnFields, FiberBundle.extend_apply_self] at hk'
    linarith
  rw [heq, hmetric.self_of_nhds, hi.self_apply_inverse]

theorem connection_mpullback_of_metric_pullback
    (D : LeviCivitaData g) (D' : LeviCivitaData h)
    (hf : ContMDiffAt (𝓡 n) (𝓡 n) ∞ f x)
    (hinv : ∀ᶠ y in 𝓝 x, (mfderiv (𝓡 n) (𝓡 n) f y).IsInvertible)
    (hmetric : ∀ᶠ y in 𝓝 x, ∀ a b : TangentSpace (𝓡 n) y,
      g.inner y a b = h.inner (f y)
        (mfderiv (𝓡 n) (𝓡 n) f y a) (mfderiv (𝓡 n) (𝓡 n) f y b))
    {Y : (y : N) → TangentSpace (𝓡 n) y}
    (hY : MDifferentiableAt (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% Y) (f x))
    (v : TangentSpace (𝓡 n) x) :
    D.connection (mpullback (𝓡 n) (𝓡 n) f Y) x v =
      (mfderiv (𝓡 n) (𝓡 n) f x).inverse
        (D'.connection Y (f x) (mfderiv (𝓡 n) (𝓡 n) f x v)) :=
  D.connection_mpullback_of_metric_pullback_of_contMDiffAt_two D'
    (hf.of_le (by norm_cast)) hinv hmetric hY v

end PoincareConjecture.LeviCivitaData
