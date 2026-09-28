import PoincareConjecture.Proofs.M03.Existence.CoordinateConnectionNative
import PoincareConjecture.Proofs.M03.Existence.ChartStateSmoothness
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators Topology Matrix.Norms.Elementwise

noncomputable section

universe u

namespace PoincareConjecture.DeTurckNative

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

private def matrixEntriesEquiv :
    (Fin n → Fin n → ℝ) ≃L[ℝ] Matrix (Fin n) (Fin n) ℝ :=
  (Matrix.ofLinearEquiv ℝ).toContinuousLinearEquiv

def matrixInverseEntries (A : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  matrixEntriesEquiv.symm ((matrixEntriesEquiv A)⁻¹)

@[simp] theorem matrixInverseEntries_apply (A : Fin n → Fin n → ℝ)
    (i j : Fin n) : matrixInverseEntries A i j = (Matrix.of A)⁻¹ i j := rfl

theorem contDiffAt_matrixInverseEntries (A : Fin n → Fin n → ℝ)
    (hdet : (Matrix.of A).det ≠ 0) :
    ContDiffAt ℝ 1 matrixInverseEntries A := by
  have hinv := contDiffAt_matrix_inv_of_nonsingular (matrixEntriesEquiv A) hdet
  exact matrixEntriesEquiv.symm.contDiff.contDiffAt.comp A
    (hinv.comp A matrixEntriesEquiv.contDiff.contDiffAt)

private theorem mdifferentiableAt_finset_sum {ι : Type*}
    (f : ι → M → ℝ) {x : M}
    (hf : ∀ a, MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) (f a) x)
    (s : Finset ι) :
    MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) (fun y => ∑ a ∈ s, f a y) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using mdifferentiableAt_const (c := (0 : ℝ))
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      exact (hf a).add ih

private theorem mvfderiv_finset_sum {ι : Type*}
    (f : ι → M → ℝ) {x : M}
    (hf : ∀ a, MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) (f a) x)
    (s : Finset ι) (v : TangentSpace (𝓡 n) x) :
    mvfderiv (𝓡 n) (fun y => ∑ a ∈ s, f a y) x v =
      ∑ a ∈ s, mvfderiv (𝓡 n) (f a) x v := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [mvfderiv_const]
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      rw [mvfderiv_fun_add (hf a) (mdifferentiableAt_finset_sum f hf s),
        ContinuousLinearMap.add_apply, ih]

theorem mvfderiv_matrix_inv_entry
    (G : M → Matrix (Fin n) (Fin n) ℝ) {x : M}
    (hG : ContMDiffAt (𝓡 n) 𝓘(ℝ, Fin n → Fin n → ℝ) 1
      (fun y a b => G y a b) x)
    (hdet : (G x).det ≠ 0) (v : TangentSpace (𝓡 n) x) (i j : Fin n) :
    mvfderiv (𝓡 n) (fun y => (G y)⁻¹ i j) x v =
      -∑ a, ∑ b, (G x)⁻¹ i a *
        mvfderiv (𝓡 n) (fun y => G y a b) x v * (G x)⁻¹ b j := by
  classical
  have hI : ContMDiffAt (𝓡 n) 𝓘(ℝ, Fin n → Fin n → ℝ) 1
      (fun y => matrixInverseEntries (fun a b => G y a b)) x := by
    have hc : ContMDiffAt 𝓘(ℝ, Fin n → Fin n → ℝ) 𝓘(ℝ, Fin n → Fin n → ℝ) 1
        matrixInverseEntries (fun a b => G x a b) :=
      (contDiffAt_matrixInverseEntries (fun a b => G x a b) hdet).contMDiffAt
    exact hc.comp (f := fun y a b => G y a b) x hG
  have hGe (a b : Fin n) :
      MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) (fun y => G y a b) x :=
    (contMDiffAt_pi_space.mp (contMDiffAt_pi_space.mp hG a) b).mdifferentiableAt
      (by simp)
  have hIe (a b : Fin n) :
      MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) (fun y => (G y)⁻¹ a b) x :=
    (contMDiffAt_pi_space.mp (contMDiffAt_pi_space.mp hI a) b).mdifferentiableAt
      (by simp)
  have hdetc : ContinuousAt (fun y => (G y).det) x :=
    (continuous_id.matrix_det).continuousAt.comp hG.continuousAt
  let P : Matrix (Fin n) (Fin n) ℝ :=
    fun a b => mvfderiv (𝓡 n) (fun y => G y a b) x v
  let Q : Matrix (Fin n) (Fin n) ℝ :=
    fun a b => mvfderiv (𝓡 n) (fun y => (G y)⁻¹ a b) x v
  have hder (a b : Fin n) :
      (∑ c, ((G x)⁻¹ a c * P c b + G x c b * Q a c)) = 0 := by
    have hevent : (fun y => ∑ c, (G y)⁻¹ a c * G y c b) =ᶠ[𝓝 x]
        (fun _ => (1 : Matrix (Fin n) (Fin n) ℝ) a b) := by
      filter_upwards [hdetc.eventually_ne hdet] with y hy
      change ((G y)⁻¹ * G y) a b = _
      rw [Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hy)]
    have heq :
        mvfderiv (𝓡 n) (fun y => ∑ c, (G y)⁻¹ a c * G y c b) x =
          mvfderiv (𝓡 n) (fun _ : M =>
            (1 : Matrix (Fin n) (Fin n) ℝ) a b) x := by
      simp only [mvfderiv]
      rw [hevent.mfderiv_eq, hevent.eq_of_nhds]
    have hd := congrArg (fun L => L v) heq
    rw [mvfderiv_const, ContinuousLinearMap.zero_apply,
      mvfderiv_finset_sum (fun c y => (G y)⁻¹ a c * G y c b)
        (fun c => (hIe a c).mul (hGe c b)) Finset.univ v] at hd
    simpa only [mvfderiv_fun_mul (hIe _ _) (hGe _ _),
      ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul, P, Q] using hd
  have hprod : Q * G x + (G x)⁻¹ * P = 0 := by
    ext a b
    change (∑ c, Q a c * G x c b) +
      (∑ c, (G x)⁻¹ a c * P c b) = 0
    calc
      _ = ∑ c, ((G x)⁻¹ a c * P c b + G x c b * Q a c) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro c _
        ring
      _ = 0 := hder a b
  have hsolve : Q = -((G x)⁻¹ * P * (G x)⁻¹) := by
    have hm : Q * G x * (G x)⁻¹ + (G x)⁻¹ * P * (G x)⁻¹ = 0 := by
      simpa only [add_mul, zero_mul] using
        congrArg (fun A : Matrix (Fin n) (Fin n) ℝ => A * (G x)⁻¹) hprod
    rw [mul_assoc Q (G x) ((G x)⁻¹),
      Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet), mul_one] at hm
    exact eq_neg_of_add_eq_zero_left hm
  change Q i j = -∑ a, ∑ b, (G x)⁻¹ i a * P a b * (G x)⁻¹ b j
  rw [hsolve]
  simp only [Matrix.neg_apply, Matrix.mul_apply, Finset.sum_mul]
  congr 1
  rw [Finset.sum_comm]

theorem frameMetricJet_value_contMDiffAt
    (g : RiemannianMetric n M)
    (F : Fin n → (y : M) → TangentSpace (𝓡 n) y) {x : M}
    (hF : ∀ a, ContMDiffAt (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% (F a)) x) :
    ContMDiffAt (𝓡 n) 𝓘(ℝ, Fin n → Fin n → ℝ) ∞
      (fun y i j => (frameMetricJet g F y).value i j) x := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  apply contMDiffAt_pi_space.mpr
  intro i
  apply contMDiffAt_pi_space.mpr
  intro j
  exact (hF i).inner_bundle (hF j)

theorem frameMetricJet_first_contMDiffAt
    (g : RiemannianMetric n M)
    (F : Fin n → (y : M) → TangentSpace (𝓡 n) y) {x : M}
    (hF : ∀ a, ContMDiffAt (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% (F a)) x)
    (a i j : Fin n) :
    ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun y => (frameMetricJet g F y).first a i j) x := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsManifold (𝓡 n) (∞ + 1) M := by
    simpa using (inferInstance : IsManifold (𝓡 n) ∞ M)
  have hpair := (hF i).inner_bundle (hF j)
  have hd := ContMDiffAt.clm_apply_of_inCoordinates
    (b₁ := id) (b₂ := fun y => g.inner y (F i y) (F j y))
    (hpair.mfderiv_const (m := ∞) (n := ∞) (by simp)) (hF a) hpair
  have hs := (Bundle.contMDiffAt_totalSpace.mp hd).2
  convert hs using 1
  funext y
  simp only [trivializationAt_model_space_apply]
  rfl

theorem mvfderiv_christoffelJet_frameMetricJet
    (g : RiemannianMetric n M)
    (F : Fin n → (y : M) → TangentSpace (𝓡 n) y) {x : M}
    (hF : ∀ a, ContMDiffAt (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% (F a)) x)
    (hdet : (frameMetricJet g F x).value.det ≠ 0)
    (a k i j : Fin n) :
    mvfderiv (𝓡 n) (fun y => christoffelJet (frameMetricJet g F y) k i j)
        x (F a x) =
      christoffelSecond (frameMetricJet g F x) a k i j := by
  have hG : ContMDiffAt (𝓡 n) 𝓘(ℝ, Fin n → Fin n → ℝ) 1
      (fun y i j => (frameMetricJet g F y).value i j) x :=
    (frameMetricJet_value_contMDiffAt g F hF).of_le (by simp)
  have hI : ContMDiffAt (𝓡 n) 𝓘(ℝ, Fin n → Fin n → ℝ) 1
      (fun y => matrixInverseEntries (fun r s => (frameMetricJet g F y).value r s)) x := by
    have hc : ContMDiffAt 𝓘(ℝ, Fin n → Fin n → ℝ) 𝓘(ℝ, Fin n → Fin n → ℝ) 1
        matrixInverseEntries (fun r s => (frameMetricJet g F x).value r s) :=
      (contDiffAt_matrixInverseEntries _ hdet).contMDiffAt
    exact hc.comp (f := fun y r s => (frameMetricJet g F y).value r s) x hG
  have hIe (r s : Fin n) : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ)
      (fun y => (frameMetricJet g F y).value⁻¹ r s) x :=
    (contMDiffAt_pi_space.mp (contMDiffAt_pi_space.mp hI r) s).mdifferentiableAt
      (by simp)
  have hfirst (r s t : Fin n) : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ)
      (fun y => (frameMetricJet g F y).first r s t) x :=
    (frameMetricJet_first_contMDiffAt g F hF r s t).mdifferentiableAt (by simp)
  let B : Fin n → M → ℝ := fun l y =>
    (frameMetricJet g F y).first i l j +
      (frameMetricJet g F y).first j l i - (frameMetricJet g F y).first l i j
  have hB (l : Fin n) : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) (B l) x :=
    ((hfirst i l j).add (hfirst j l i)).sub (hfirst l i j)
  have hBderiv (l : Fin n) : mvfderiv (𝓡 n) (B l) x (F a x) =
      (frameMetricJet g F x).second a i l j +
        (frameMetricJet g F x).second a j l i -
        (frameMetricJet g F x).second a l i j := by
    change mvfderiv (𝓡 n)
      ((fun y => (frameMetricJet g F y).first i l j) +
        (fun y => (frameMetricJet g F y).first j l i) -
        (fun y => (frameMetricJet g F y).first l i j)) x (F a x) = _
    rw [mvfderiv_sub ((hfirst i l j).add (hfirst j l i)) (hfirst l i j),
      ContinuousLinearMap.sub_apply,
      mvfderiv_add (hfirst i l j) (hfirst j l i), ContinuousLinearMap.add_apply]
    rfl
  have hterm (l : Fin n) : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ)
      (fun y => (frameMetricJet g F y).value⁻¹ k l * B l y) x :=
    (hIe k l).mul (hB l)
  have hinvderiv (l : Fin n) :
      mvfderiv (𝓡 n) (fun y => (frameMetricJet g F y).value⁻¹ k l)
          x (F a x) = inverseFirst (frameMetricJet g F x) a k l := by
    exact mvfderiv_matrix_inv_entry (fun y => (frameMetricJet g F y).value)
      hG hdet (F a x) k l
  change mvfderiv (𝓡 n)
      (fun y => (1 / 2 : ℝ) *
        ∑ l, (frameMetricJet g F y).value⁻¹ k l * B l y) x (F a x) = _
  rw [mvfderiv_fun_mul mdifferentiableAt_const
    (mdifferentiableAt_finset_sum _ hterm Finset.univ)]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul, mvfderiv_const, ContinuousLinearMap.zero_apply, mul_zero, add_zero]
  rw [mvfderiv_finset_sum _ hterm Finset.univ (F a x)]
  unfold christoffelSecond
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  rw [mvfderiv_fun_mul (hIe k l) (hB l)]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul, hinvderiv, hBderiv]
  dsimp only [B]
  ring

end PoincareConjecture.DeTurckNative

end
