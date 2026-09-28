import PoincareConjecture.Proofs.M03.Existence.IntrinsicDeTurckNative

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators Topology Matrix.Norms.Elementwise

noncomputable section

universe u

namespace PoincareConjecture.DeTurckNative

variable {n : ℕ}

private theorem contDiff_det_entries_infty :
    ContDiff ℝ ∞ (fun A : Fin n → Fin n → ℝ => (Matrix.of A).det) := by
  have h : ContDiff ℝ ∞ (fun A : Fin n → Fin n → ℝ =>
      ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℝ) *
        ∏ i, A (σ i) i) := by
    fun_prop
  convert h using 1
  funext A
  exact Matrix.det_apply' (Matrix.of A)

private theorem contDiff_adjugate_entry_infty (i j : Fin n) :
    ContDiff ℝ ∞ (fun A : Fin n → Fin n → ℝ => (Matrix.of A).adjugate i j) := by
  have hrow : ContDiff ℝ ∞ (fun A : Fin n → Fin n → ℝ =>
      fun r c => (Matrix.of A).updateRow j (Pi.single i 1) r c) := by
    apply contDiff_pi.mpr
    intro r
    apply contDiff_pi.mpr
    intro c
    by_cases hr : r = j
    · subst r
      simpa [Matrix.updateRow_apply] using
        (contDiff_const : ContDiff ℝ ∞
          (fun _ : (Fin n → Fin n → ℝ) => ((Pi.single i (1 : ℝ) : Fin n → ℝ) c)))
    · simp only [Matrix.updateRow_apply, hr, if_false, Matrix.of_apply]
      fun_prop
  have h := (contDiff_det_entries_infty (n := n)).comp hrow
  convert h using 1
  funext A
  simp only [Function.comp_apply, Matrix.adjugate_apply] <;> rfl

theorem contDiffAt_matrixInverseEntries_infty (A : Fin n → Fin n → ℝ)
    (hdet : (Matrix.of A).det ≠ 0) :
    ContDiffAt ℝ ∞ matrixInverseEntries A := by
  apply contDiffAt_pi.mpr
  intro i
  apply contDiffAt_pi.mpr
  intro j
  have h := ((contDiff_det_entries_infty (n := n)).contDiffAt.inv hdet).mul
    (contDiff_adjugate_entry_infty i j).contDiffAt
  have heq : (fun Q : Fin n → Fin n → ℝ => matrixInverseEntries Q i j) =
      (fun Q => (Matrix.of Q).det⁻¹ * (Matrix.of Q).adjugate i j) := by
    funext Q
    simp only [matrixInverseEntries_apply, Matrix.inv_def, Ring.inverse_eq_inv',
      Matrix.smul_apply, smul_eq_mul]
  rw [heq]
  exact h

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin n)

private theorem contMDiffAt_scalar_finset_sum {ι : Type*}
    (f : ι → M → ℝ) {x : M}
    (hf : ∀ a, ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ (f a) x) (s : Finset ι) :
    ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun y => ∑ a ∈ s, f a y) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using contMDiffAt_const (c := (0 : ℝ))
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      exact (hf a).add ih

private theorem mvfderiv_smooth_finset_sum {ι : Type*}
    (f : ι → M → ℝ) {x : M}
    (hf : ∀ a, ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ (f a) x)
    (s : Finset ι) (v : TangentSpace (𝓡 n) x) :
    mvfderiv (𝓡 n) (fun y => ∑ a ∈ s, f a y) x v =
      ∑ a ∈ s, mvfderiv (𝓡 n) (f a) x v := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [mvfderiv_const]
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      rw [mvfderiv_fun_add ((hf a).mdifferentiableAt (by simp))
        ((contMDiffAt_scalar_finset_sum f hf s).mdifferentiableAt (by simp)),
        ContinuousLinearMap.add_apply, ih]

theorem frameMetricJet_inverse_contMDiffAt (g : RiemannianMetric n M)
    (F : Fin n → (y : M) → TangentSpace (𝓡 n) y) {x : M}
    (hF : ∀ a, ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, E)) ∞ (T% (F a)) x)
    (hdet : (frameMetricJet g F x).value.det ≠ 0) (i j : Fin n) :
    ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun y => (frameMetricJet g F y).value⁻¹ i j) x := by
  have hG := frameMetricJet_value_contMDiffAt g F hF
  have hI : ContMDiffAt (𝓡 n) 𝓘(ℝ, Fin n → Fin n → ℝ) ∞
      (fun y => matrixInverseEntries (fun a b => (frameMetricJet g F y).value a b)) x := by
    have hc : ContMDiffAt 𝓘(ℝ, Fin n → Fin n → ℝ)
        𝓘(ℝ, Fin n → Fin n → ℝ) ∞ matrixInverseEntries
        (fun a b => (frameMetricJet g F x).value a b) :=
      (contDiffAt_matrixInverseEntries_infty _ hdet).contMDiffAt
    exact hc.comp (f := fun y a b => (frameMetricJet g F y).value a b) x hG
  exact contMDiffAt_pi_space.mp (contMDiffAt_pi_space.mp hI i) j

theorem frameChristoffel_contMDiffAt (g : RiemannianMetric n M)
    (F : Fin n → (y : M) → TangentSpace (𝓡 n) y) {x : M}
    (hF : ∀ a, ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, E)) ∞ (T% (F a)) x)
    (hdet : (frameMetricJet g F x).value.det ≠ 0) (k i j : Fin n) :
    ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun y => christoffelJet (frameMetricJet g F y) k i j) x := by
  have hfirst := frameMetricJet_first_contMDiffAt g F hF
  have hterm (l : Fin n) : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun y => (frameMetricJet g F y).value⁻¹ k l *
        ((frameMetricJet g F y).first i l j +
          (frameMetricJet g F y).first j l i - (frameMetricJet g F y).first l i j)) x :=
    (frameMetricJet_inverse_contMDiffAt g F hF hdet k l).smul
      (((hfirst i l j).add (hfirst j l i)).sub (hfirst l i j))
  have hhalf : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun _ : M => (1 / 2 : ℝ)) x :=
    contMDiffAt_const
  exact hhalf.smul (contMDiffAt_scalar_finset_sum _ hterm Finset.univ)

theorem frameDeTurck_contMDiffAt (g background : RiemannianMetric n M)
    (F : Fin n → (y : M) → TangentSpace (𝓡 n) y) {x : M}
    (hF : ∀ a, ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, E)) ∞ (T% (F a)) x)
    (hdet : (frameMetricJet g F x).value.det ≠ 0)
    (hdetB : (frameMetricJet background F x).value.det ≠ 0) (k : Fin n) :
    ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun y => deTurckVector (frameMetricJet background F y) (frameMetricJet g F y) k) x := by
  apply contMDiffAt_scalar_finset_sum
  intro a
  apply contMDiffAt_scalar_finset_sum
  intro b
  exact (frameMetricJet_inverse_contMDiffAt g F hF hdet a b).smul
    ((frameChristoffel_contMDiffAt g F hF hdet k a b).sub
      (frameChristoffel_contMDiffAt background F hF hdetB k a b))

theorem mvfderiv_deTurckVector_frameMetricJet (g background : RiemannianMetric n M)
    (F : Fin n → (y : M) → TangentSpace (𝓡 n) y) {x : M}
    (hF : ∀ a, ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, E)) ∞ (T% (F a)) x)
    (hdet : (frameMetricJet g F x).value.det ≠ 0)
    (hdetB : (frameMetricJet background F x).value.det ≠ 0) (a k : Fin n) :
    mvfderiv (𝓡 n)
      (fun y => deTurckVector (frameMetricJet background F y) (frameMetricJet g F y) k)
      x (F a x) =
        deTurckVectorFirst (frameMetricJet background F x) (frameMetricJet g F x) a k := by
  let q := fun y => frameMetricJet g F y
  let r := fun y => frameMetricJet background F y
  let C := fun u v y => christoffelJet (q y) k u v - christoffelJet (r y) k u v
  have hI (u v : Fin n) : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun y => (q y).value⁻¹ u v) x :=
    frameMetricJet_inverse_contMDiffAt g F hF hdet u v
  have hC (u v : Fin n) : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ (C u v) x :=
    (frameChristoffel_contMDiffAt g F hF hdet k u v).sub
      (frameChristoffel_contMDiffAt background F hF hdetB k u v)
  have hterm (u v : Fin n) : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun y => (q y).value⁻¹ u v * C u v y) x := (hI u v).smul (hC u v)
  have hsum (u : Fin n) : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun y => ∑ v, (q y).value⁻¹ u v * C u v y) x :=
    contMDiffAt_scalar_finset_sum _ (hterm u) Finset.univ
  have hIderiv (u v : Fin n) :
      mvfderiv (𝓡 n) (fun y => (q y).value⁻¹ u v) x (F a x) =
        inverseFirst (q x) a u v :=
    mvfderiv_matrix_inv_entry (fun y => (frameMetricJet g F y).value)
      ((frameMetricJet_value_contMDiffAt g F hF).of_le (by simp)) hdet (F a x) u v
  have hCderiv (u v : Fin n) : mvfderiv (𝓡 n) (C u v) x (F a x) =
      christoffelSecond (q x) a k u v - christoffelSecond (r x) a k u v := by
    change mvfderiv (𝓡 n)
      ((fun y => christoffelJet (frameMetricJet g F y) k u v) -
        (fun y => christoffelJet (frameMetricJet background F y) k u v)) x (F a x) = _
    rw [mvfderiv_sub
      ((frameChristoffel_contMDiffAt g F hF hdet k u v).mdifferentiableAt (by simp))
      ((frameChristoffel_contMDiffAt background F hF hdetB k u v).mdifferentiableAt (by simp)),
      ContinuousLinearMap.sub_apply,
      mvfderiv_christoffelJet_frameMetricJet g F hF hdet a k u v,
      mvfderiv_christoffelJet_frameMetricJet background F hF hdetB a k u v]
  change mvfderiv (𝓡 n) (fun y => ∑ u, ∑ v, (q y).value⁻¹ u v * C u v y)
      x (F a x) = _
  rw [mvfderiv_smooth_finset_sum _ hsum Finset.univ (F a x)]
  unfold deTurckVectorFirst
  apply Finset.sum_congr rfl
  intro u _
  rw [mvfderiv_smooth_finset_sum _ (hterm u) Finset.univ (F a x)]
  apply Finset.sum_congr rfl
  intro v _
  rw [mvfderiv_fun_mul ((hI u v).mdifferentiableAt (by simp))
    ((hC u v).mdifferentiableAt (by simp))]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul, hIderiv, hCderiv]
  dsimp only [C, q, r]
  ring

theorem intrinsicDeTurckField_contMDiffAt
    {g background : RiemannianMetric n M}
    (D : LeviCivitaData g) (B : LeviCivitaData background) (x : M) :
    ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, E)) ∞ (T% (intrinsicDeTurckField D B)) x := by
  have hx : x ∈ (chartAt E x).source := mem_chart_source E x
  have hF (a : Fin n) := (chartFrame_contMDiffOn x a).contMDiffAt
    ((chartAt E x).open_source.mem_nhds hx)
  have hdet : (frameMetricJet g (chartFrame x) x).value.det ≠ 0 :=
    ne_of_gt (frameMetricJet_value_posDef g (chartFrame x) x
      (chartFrameBasis x x hx) (chartFrame_eq_basis x x hx)).det_pos
  have hdetB : (frameMetricJet background (chartFrame x) x).value.det ≠ 0 :=
    ne_of_gt (frameMetricJet_value_posDef background (chartFrame x) x
      (chartFrameBasis x x hx) (chartFrame_eq_basis x x hx)).det_pos
  have hsum : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, E)) ∞
      (T% (fun y => ∑ k, deTurckVector (frameMetricJet background (chartFrame x) y)
        (frameMetricJet g (chartFrame x) y) k • chartFrame x k y)) x :=
    ContMDiffAt.sum_section fun k _ =>
      (frameDeTurck_contMDiffAt g background (chartFrame x) hF hdet hdetB k).smul_section (hF k)
  apply hsum.congr_of_eventuallyEq
  filter_upwards [(chartAt E x).open_source.mem_nhds hx] with y hy
  exact congrArg (fun v : TangentSpace (𝓡 n) y => Bundle.TotalSpace.mk' E y v)
    (intrinsicDeTurckField_eq_chartFrame_sum D B x hy)

theorem intrinsicDeTurckField_contMDiff
    {g background : RiemannianMetric n M}
    (D : LeviCivitaData g) (B : LeviCivitaData background) :
    ContMDiff (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, E)) ∞ (T% (intrinsicDeTurckField D B)) :=
  intrinsicDeTurckField_contMDiffAt D B

end PoincareConjecture.DeTurckNative

end
