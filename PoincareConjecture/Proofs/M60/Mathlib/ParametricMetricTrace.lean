import PoincareConjecture.Proofs.M05.Geometry.Riemannian.Tensor.TraceRegularity
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Bundle
open scoped Manifold ContDiff Topology BigOperators

universe u v w

namespace PoincareConjecture.M60

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
  {N : Type u} [TopologicalSpace N] [ChartedSpace H N]

private theorem contMDiffAt_matrix_det {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : N → Matrix ι ι ℝ) (x : N)
    (hG : ∀ i j, ContMDiffAt J 𝓘(ℝ, ℝ) ∞ (fun y => G y i j) x) :
    ContMDiffAt J 𝓘(ℝ, ℝ) ∞ (fun y => (G y).det) x := by
  simp only [Matrix.det_apply']
  exact ContMDiffAt.sum fun σ _ =>
    contMDiffAt_const.mul (ContMDiffAt.prod fun i _ => hG (σ i) i)

private theorem contMDiffAt_matrix_inv_entry {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : N → Matrix ι ι ℝ) (x : N)
    (hG : ∀ i j, ContMDiffAt J 𝓘(ℝ, ℝ) ∞ (fun y => G y i j) x)
    (hx : (G x).det ≠ 0) (i j : ι) :
    ContMDiffAt J 𝓘(ℝ, ℝ) ∞ (fun y => (G y)⁻¹ i j) x := by
  simp only [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul,
    Matrix.adjugate_apply]
  apply ((contMDiffAt_matrix_det G x hG).inv₀ hx).mul
  apply contMDiffAt_matrix_det
  intro a b
  by_cases ha : a = j
  · subst a
    simpa using (contMDiffAt_const (I := J) (x := x) (n := ∞)
      (c := (Pi.single i (1 : ℝ) : ι → ℝ) b))
  · simpa [Matrix.updateRow_apply, ha] using hG a b

variable {n m : ℕ} {X : Type v} {Y : Type w} [TopologicalSpace X] [TopologicalSpace Y]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) Y]
  [IsManifold (𝓡 n) ∞ X] [IsManifold (𝓡 m) ∞ Y]

local notation "TX" => TangentSpace (𝓡 n) (M := X)
local notation "TY" => TangentSpace (𝓡 m) (M := Y)




theorem contMDiffAt_parametric_tangentMap [IsManifold J 1 N]
    (f : N → X → Y) (p : N → X) {x : N}
    (hf : ContMDiffAt (J.prod (𝓡 n)) (𝓡 m) ∞ (Function.uncurry f) (x, p x))
    (hp : ContMDiffAt J (𝓡 n) ∞ p x)
    (V : (y : N) → TX (p y))
    (hV : ContMDiffAt J ((𝓡 n).prod (𝓡 n)) ∞
      (fun y => (⟨p y, V y⟩ : TangentBundle (𝓡 n) X)) x) :
    ContMDiffAt J ((𝓡 m).prod (𝓡 m)) ∞
      (fun y => (⟨f y (p y), mfderiv (𝓡 n) (𝓡 m) (f y) (p y) (V y)⟩ :
        TangentBundle (𝓡 m) Y)) x := by
  have hA := hf.mfderiv f p hp (by simp)
  have hb := hf.comp x (contMDiffAt_id.prodMk hp)
  exact ContMDiffAt.clm_apply_of_inCoordinates hA hV hb

omit [IsManifold (𝓡 m) ∞ Y] in



theorem contMDiffAt_metricTrace_along (g : RiemannianMetric n X)
    (p : N → X) {x : N} (hp : ContMDiffAt J (𝓡 n) ∞ p x)
    (A : (y : N) → TX (p y) →ₗ[ℝ] TX (p y) →ₗ[ℝ] ℝ)
    (hA : ∀ (V W : (y : N) → TX (p y)),
      ContMDiffAt J ((𝓡 n).prod (𝓡 n)) ∞
        (fun y => (⟨p y, V y⟩ : TangentBundle (𝓡 n) X)) x →
      ContMDiffAt J ((𝓡 n).prod (𝓡 n)) ∞
        (fun y => (⟨p y, W y⟩ : TangentBundle (𝓡 n) X)) x →
      ContMDiffAt J 𝓘(ℝ, ℝ) ∞ (fun y => A y (V y) (W y)) x) :
    ContMDiffAt J 𝓘(ℝ, ℝ) ∞
      (fun y => ∑ i, A y (g.orthonormalBasis (p y) i) (g.orthonormalBasis (p y) i)) x := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : X → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContMDiffRiemannianBundle (𝓡 n) ∞ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : X → Type _) := ⟨g.inner, g.contMDiff, fun _ _ _ => rfl⟩
  let b := g.orthonormalBasis (p x)
  let V := fun i => FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (b i)
  let G : N → Matrix (Fin (Module.finrank ℝ (TX (p x))))
      (Fin (Module.finrank ℝ (TX (p x)))) ℝ := fun y i j =>
    g.inner (p y) (V i (p y)) (V j (p y))
  have hV (i) : ContMDiffAt J ((𝓡 n).prod (𝓡 n)) ∞
      (fun y => (⟨p y, V i (p y)⟩ : TangentBundle (𝓡 n) X)) x :=
    (FiberBundle.contMDiffAt_extend (k := ∞) (𝓡 n) _ (b i)).comp x hp
  have hG (i j) : ContMDiffAt J 𝓘(ℝ, ℝ) ∞ (fun y => G y i j) x :=
    (hV i).inner_bundle (hV j)
  have hGx : G x = 1 := by
    ext i j
    change g.inner (p x) (V i (p x)) (V j (p x)) = _
    simp only [V, FiberBundle.extend_apply_self]
    exact b.inner_eq_ite i j
  have hinv := contMDiffAt_matrix_inv_entry G x hG (by simp [hGx])
  have hsum : ContMDiffAt J 𝓘(ℝ, ℝ) ∞
      (fun y => ∑ i, ∑ j, (G y)⁻¹ i j * A y (V i (p y)) (V j (p y))) x :=
    ContMDiffAt.sum fun i _ => ContMDiffAt.sum fun j _ =>
      (hinv i j).mul (hA _ _ (hV i) (hV j))
  apply hsum.congr_of_eventuallyEq
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) TX (p x)
  have hx : p x ∈ e.baseSet := mem_baseSet_trivializationAt _ TX (p x)
  filter_upwards [hp.continuousAt.preimage_mem_nhds (e.open_baseSet.mem_nhds hx)] with y hy
  let L := (e.continuousLinearEquivAt ℝ (p x) hx).trans
    (e.continuousLinearEquivAt ℝ (p y) hy).symm
  let c := b.toBasis.map L.toLinearEquiv
  have hc (i) : c i = V i (p y) := by
    change (e.continuousLinearEquivAt ℝ (p y) hy).symm
      ((e.continuousLinearEquivAt ℝ (p x) hx) (b i)) = _
    rw [Bundle.Trivialization.symm_continuousLinearEquivAt_eq,
      Bundle.Trivialization.symmL_apply _ hy]
    rfl
  have h := bilinear_sum_basis_eq_inverse_gram (A y) c (g.orthonormalBasis (p y))
  change _ = ∑ i, ∑ j, (Matrix.of (fun i j => g.inner (p y) (c i) (c j)))⁻¹ i j *
    A y (c i) (c j) at h
  simp only [hc] at h
  have hGy : G y = Matrix.of (fun i j => g.inner (p y) (V i (p y)) (V j (p y))) := by
    ext i j
    rfl
  rw [← hGy] at h
  exact h

end PoincareConjecture.M60
