import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Hessian.Pullback
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Hessian.Locality
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Splitting.ParallelGradient.Basic
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Hessian.Symmetry
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Scaling
import Mathlib.Geometry.Manifold.Diffeomorph
open Set Filter
open scoped Manifold ContDiff Bundle Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace PoincareConjecture.RiemannianMetric
variable {n : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (n+1))) P] [IsManifold (𝓡 (n+1)) ∞ P]
  (g : RiemannianMetric n M) (G : RiemannianMetric (n+1) P)
  (D : LeviCivitaData G)
  (e : (M × ℝ) ≃ₘ⟮(𝓡 n).prod 𝓘(ℝ,ℝ), 𝓡 (n+1)⟯ P)
  (hmetric : ∀ (z : M × ℝ) (v w : TangentSpace ((𝓡 n).prod 𝓘(ℝ,ℝ)) z),
    G.inner (e z)
      (mfderiv ((𝓡 n).prod 𝓘(ℝ,ℝ)) (𝓡 (n+1)) e z v)
      (mfderiv ((𝓡 n).prod 𝓘(ℝ,ℝ)) (𝓡 (n+1)) e z w) =
      g.inner z.1 v.1 w.1 + v.2*w.2)
omit [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 (n+1)) ∞ P] in
private theorem product_mfderiv_inverse (z : M × ℝ)
    (v : TangentSpace ((𝓡 n).prod 𝓘(ℝ,ℝ)) z) :
    mfderiv (𝓡 (n+1)) ((𝓡 n).prod 𝓘(ℝ,ℝ)) e.symm (e z)
      (mfderiv ((𝓡 n).prod 𝓘(ℝ,ℝ)) (𝓡 (n+1)) e z v) = v := by
  have hh := mfderiv_comp z (e.symm.contMDiff.mdifferentiable (by simp) _)
    (e.contMDiff.mdifferentiable (by simp) _)
  have hid : (e.symm : P → M × ℝ) ∘ e = id := funext e.symm_apply_apply
  rw [hid, mfderiv_id] at hh
  exact (congrArg (fun L => L v) hh).symm

omit [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 (n+1)) ∞ P] in
private theorem product_mfderiv_surjective (z : M × ℝ) :
    Function.Surjective (mfderiv ((𝓡 n).prod 𝓘(ℝ,ℝ)) (𝓡 (n+1)) e z) := by
  intro w
  refine ⟨mfderiv (𝓡 (n+1)) ((𝓡 n).prod 𝓘(ℝ,ℝ)) e.symm (e z) w, ?_⟩
  have hh := mfderiv_comp (e z) (e.contMDiff.mdifferentiable (by simp) _)
    (e.symm.contMDiff.mdifferentiable (by simp) _)
  have hid : (e : M × ℝ → P) ∘ e.symm = id := funext e.apply_symm_apply
  rw [hid, mfderiv_id, e.symm_apply_apply] at hh
  exact (congrArg (fun L => L w) hh).symm

include hmetric in
private theorem product_height_gradient (z : M × ℝ) :
    D.gradient (Prod.snd ∘ e.symm) (e z) =
      mfderiv ((𝓡 n).prod 𝓘(ℝ,ℝ)) (𝓡 (n+1)) e z (0,1) := by
  apply (G.inner_isInvertible (e z)).injective
  ext w
  obtain ⟨v, rfl⟩ := product_mfderiv_surjective e z w
  rw [D.inner_gradient, hmetric]
  change mfderiv (𝓡 (n+1)) 𝓘(ℝ,ℝ) (Prod.snd ∘ e.symm) (e z)
    (mfderiv ((𝓡 n).prod 𝓘(ℝ,ℝ)) (𝓡 (n+1)) e z v) = _
  rw [mfderiv_comp_apply _ mdifferentiableAt_snd
    (e.symm.contMDiff.mdifferentiable (by simp) _), product_mfderiv_inverse e z v,
    mfderiv_snd]
  simp
  rfl

private noncomputable def productReflection (t : ℝ) (z : P) : P :=
  e ((e.symm z).1, 2*t - (e.symm z).2)

omit [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 (n+1)) ∞ P] in
private theorem productReflection_smooth (t : ℝ) :
    ContMDiff (𝓡 (n+1)) (𝓡 (n+1)) ∞ (productReflection e t) := by
  exact e.contMDiff.comp ((contMDiff_fst.comp e.symm.contMDiff).prodMk
    (contMDiff_const.sub (contMDiff_snd.comp e.symm.contMDiff)))

omit [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 (n+1)) ∞ P] in
private theorem productReflection_mfderiv (t : ℝ) (z : M × ℝ)
    (v : TangentSpace ((𝓡 n).prod 𝓘(ℝ,ℝ)) z) :
    mfderiv (𝓡 (n+1)) (𝓡 (n+1)) (productReflection e t) (e z)
      (mfderiv ((𝓡 n).prod 𝓘(ℝ,ℝ)) (𝓡 (n+1)) e z v) =
    mfderiv ((𝓡 n).prod 𝓘(ℝ,ℝ)) (𝓡 (n+1)) e (z.1, 2*t-z.2) (v.1,-v.2) := by
  let j : M × ℝ → M × ℝ := fun z => (z.1, 2*t-z.2)
  have hj : ContMDiff ((𝓡 n).prod 𝓘(ℝ,ℝ)) ((𝓡 n).prod 𝓘(ℝ,ℝ)) ∞ j :=
    contMDiff_fst.prodMk (contMDiff_const.sub contMDiff_snd)
  have heq : productReflection e t ∘ e = e ∘ j := by
    ext z
    simp [productReflection, j]
  have hd := mfderiv_comp_apply z
    ((productReflection_smooth e t).mdifferentiable (by simp) _) (e.contMDiff.mdifferentiable (by simp) _) v
  rw [heq, mfderiv_comp_apply z (e.contMDiff.mdifferentiable (by simp) _)
    (hj.mdifferentiable (by simp) _)] at hd
  rw [← hd]
  congr 1
  change mfderiv ((𝓡 n).prod 𝓘(ℝ,ℝ)) ((𝓡 n).prod 𝓘(ℝ,ℝ))
    (fun z : M × ℝ => (z.1, 2*t-z.2)) z v = _
  change EuclideanSpace ℝ (Fin n) × ℝ at v
  rw [mfderiv_prodMk (f := Prod.fst) (g := fun z : M × ℝ => 2*t-z.2) mdifferentiableAt_fst
    (mdifferentiableAt_const.sub mdifferentiableAt_snd)]
  change (mfderiv ((𝓡 n).prod 𝓘(ℝ,ℝ)) (𝓡 n) Prod.fst z v,
    mfderiv ((𝓡 n).prod 𝓘(ℝ,ℝ)) 𝓘(ℝ,ℝ) (fun z : M × ℝ => 2*t-z.2) z v) = _
  erw [mfderiv_sub (f := fun _ : M × ℝ => 2*t) (g := Prod.snd) mdifferentiableAt_const mdifferentiableAt_snd, mfderiv_const,
    mfderiv_fst, mfderiv_snd]
  change (v.1, 0-v.2) = (v.1,-v.2)
  simp

include hmetric in
private theorem productReflection_metric (t : ℝ) (x : P)
    (v w : TangentSpace (𝓡 (n+1)) x) :
    G.inner x v w = G.inner (productReflection e t x)
      (mfderiv (𝓡 (n+1)) (𝓡 (n+1)) (productReflection e t) x v)
      (mfderiv (𝓡 (n+1)) (𝓡 (n+1)) (productReflection e t) x w) := by
  obtain ⟨z,rfl⟩ := e.surjective x
  obtain ⟨a,rfl⟩ := product_mfderiv_surjective e z v
  obtain ⟨b,rfl⟩ := product_mfderiv_surjective e z w
  erw [productReflection_mfderiv e, productReflection_mfderiv e, hmetric]
  have he : productReflection e t (e z) = e (z.1,2*t-z.2) := by
    simp [productReflection]
  erw [he, hmetric]
  change g.inner z.1 a.1 b.1 + a.2*b.2 =
    g.inner z.1 a.1 b.1 + (-a.2)*(-b.2)
  ring

omit [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 (n+1)) ∞ P] in
private theorem productReflection_involutive (t : ℝ) :
    Function.Involutive (productReflection e t) := by
  intro x
  simp only [productReflection, e.symm_apply_apply]
  have he : 2*t-(2*t-(e.symm x).2) = (e.symm x).2 := by ring
  rw [he]
  exact e.apply_symm_apply x

omit [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 (n+1)) ∞ P] in
private theorem productReflection_invertible (t : ℝ) (x : P) :
    (mfderiv (𝓡 (n+1)) (𝓡 (n+1)) (productReflection e t) x).IsInvertible := by
  let J := productReflection e t
  have hj := productReflection_smooth e t
  have hinv : J ∘ J = id := funext (productReflection_involutive e t)
  have hc (y : P) := mfderiv_comp y (hj.mdifferentiable (by simp) _) (hj.mdifferentiable (by simp) _)
  have h₁ := hc x
  have h₂ := hc (J x)
  rw [show (productReflection e t ∘ productReflection e t) = id from hinv, mfderiv_id] at h₁ h₂
  rw [productReflection_involutive e t x] at h₂
  exact ContinuousLinearMap.IsInvertible.of_inverse h₂.symm h₁.symm

include hmetric in
private theorem product_height_horizontal_hessian (z : M × ℝ)
    (v w : TangentSpace (𝓡 n) z.1) :
    D.hessian (Prod.snd ∘ e.symm) (e z)
      (mfderiv ((𝓡 n).prod 𝓘(ℝ,ℝ)) (𝓡 (n+1)) e z (v,0))
      (mfderiv ((𝓡 n).prod 𝓘(ℝ,ℝ)) (𝓡 (n+1)) e z (w,0)) = 0 := by
  let h : P → ℝ := Prod.snd ∘ e.symm
  have hh : ContMDiff (𝓡 (n+1)) 𝓘(ℝ,ℝ) ∞ h := contMDiff_snd.comp e.symm.contMDiff
  have he : h ∘ productReflection e z.2 = fun y => 2*z.2 + (-1)*h y := by
    ext y
    simp only [Function.comp_apply, h, productReflection, e.symm_apply_apply]
    ring
  have hp := D.hessian_comp_of_metric_pullback D
    (productReflection_smooth e z.2 (e z))
    (Filter.Eventually.of_forall (productReflection_invertible e z.2))
    (Filter.Eventually.of_forall (productReflection_metric g G e hmetric z.2))
    (hh _) (mfderiv ((𝓡 n).prod 𝓘(ℝ,ℝ)) (𝓡 (n+1)) e z (v,0))
    (mfderiv ((𝓡 n).prod 𝓘(ℝ,ℝ)) (𝓡 (n+1)) e z (w,0))
  rw [he, D.hessian_const_add_at (by simpa using (hh (e z)).neg),
    D.hessian_const_mul, productReflection_mfderiv e, productReflection_mfderiv e] at hp
  have hz : 2*z.2-z.2 = z.2 := by ring
  have hfix : productReflection e z.2 (e z) = e z := by
    simp [productReflection, hz]
  simp only [neg_zero] at hp
  erw [hz, Prod.mk.eta, hfix] at hp
  change D.hessian h (e z) _ _ = 0
  linarith

include hmetric in
theorem product_height_hasUnitGradient_and_hasZeroHessian :
    HasUnitGradient D (Prod.snd ∘ e.symm) ∧
      HasZeroHessian D (Prod.snd ∘ e.symm) := by
  let h : P → ℝ := Prod.snd ∘ e.symm
  have hh : ContMDiff (𝓡 (n+1)) 𝓘(ℝ,ℝ) ∞ h := contMDiff_snd.comp e.symm.contMDiff
  have hu : HasUnitGradient D h := by
    intro x
    obtain ⟨z,rfl⟩ := e.surjective x
    erw [product_height_gradient g G D e hmetric, hmetric]
    simp
  refine ⟨hu, ?_⟩
  intro x v w
  obtain ⟨z,rfl⟩ := e.surjective x
  obtain ⟨a,rfl⟩ := product_mfderiv_surjective e z v
  obtain ⟨b,rfl⟩ := product_mfderiv_surjective e z w
  let A := mfderiv ((𝓡 n).prod 𝓘(ℝ,ℝ)) (𝓡 (n+1)) e z
  let N := D.gradient h (e z)
  have hN : N = A (0,1) := product_height_gradient g G D e hmetric z
  have hz (v : TangentSpace (𝓡 (n+1)) (e z)) : D.hessian h (e z) v N = 0 := by
    have hv := D.mvfderiv_gradient_normSq (hh (e z)) v
    have hfun : (fun y => G.inner y (D.gradient h y) (D.gradient h y)) = fun _ => 1 :=
      funext hu
    rw [hfun, mvfderiv_const] at hv
    change (0 : ℝ) = 2 * D.hessian h (e z) v N at hv
    linarith
  have hz' (v : TangentSpace (𝓡 (n+1)) (e z)) : D.hessian h (e z) N v = 0 :=
    (D.hessian_symm hh _ _ _).trans (hz v)
  have hsplit (a : EuclideanSpace ℝ (Fin n) × ℝ) :
      a = (a.1,0) + a.2 • ((0,1) : EuclideanSpace ℝ (Fin n) × ℝ) := by
    ext <;> simp
  have ha : A a = A (a.1,0) + a.2 • N := by
    rw [hN, ← map_smul, ← map_add]
    congr 1
    change a = (a.1,0) + a.2 • ((0,1) : EuclideanSpace ℝ (Fin n) × ℝ)
    exact hsplit a
  have hb : A b = A (b.1,0) + b.2 • N := by
    rw [hN, ← map_smul, ← map_add]
    congr 1
    change b = (b.1,0) + b.2 • ((0,1) : EuclideanSpace ℝ (Fin n) × ℝ)
    exact hsplit b
  have hbil (u v : TangentSpace (𝓡 (n+1)) (e z)) :
      D.hessian h (e z) u v =
        G.inner (e z) (D.connection (D.gradient h) (e z) u) v :=
    D.hessian_eq_inner_connection_gradient (hh (e z)) u v
  change D.hessian h (e z) (A a) (A b) = 0
  rw [ha,hb]
  simp only [hbil, map_add, map_smul, add_apply, smul_apply,
    smul_eq_mul]
  have hhoriz := product_height_horizontal_hessian g G D e hmetric z a.1 b.1
  rw [hbil] at hhoriz
  have hz₁ := hz (A (a.1,0))
  have hz₂ := hz' (A (b.1,0))
  have hz₃ := hz N
  rw [hbil] at hz₁ hz₂ hz₃
  change G.inner (e z) (D.connection (D.gradient h) (e z) (A (a.1,0)))
      (A (b.1,0)) = 0 at hhoriz
  rw [hhoriz, hz₁, hz₂, hz₃]
  ring

end PoincareConjecture.RiemannianMetric
