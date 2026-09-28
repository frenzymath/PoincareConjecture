import PoincareConjecture.Proofs.M03.Existence.ChartStateContinuity
import PoincareConjecture.Proofs.M03.Existence.IntrinsicRicciJetNative
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Connection.ScalarJets
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.Contraction
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.Bilinear








noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology BigOperators Matrix.Norms.Elementwise

namespace PoincareConjecture.DeepHorn

open DeTurckNative

variable {n : ℕ}

private theorem smooth_det :
    ContDiff ℝ ∞ (fun A : Matrix (Fin n) (Fin n) ℝ => A.det) := by
  have h : ContDiff ℝ ∞ (fun A : Matrix (Fin n) (Fin n) ℝ =>
      ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℝ) *
        ∏ i, A (σ i) i) := by fun_prop
  convert h using 1
  funext A
  exact Matrix.det_apply' A

private theorem smooth_adjugate :
    ContDiff ℝ ∞ (fun A : Matrix (Fin n) (Fin n) ℝ => A.adjugate) := by
  apply contDiff_pi.2
  intro i
  apply contDiff_pi.2
  intro j
  have hrow : ContDiff ℝ ∞ (fun A : Matrix (Fin n) (Fin n) ℝ =>
      A.updateRow j (Pi.single i 1)) := by
    apply contDiff_pi.2
    intro r
    apply contDiff_pi.2
    intro c
    by_cases hr : r = j
    · subst r
      simp [Matrix.updateRow_apply]
      fun_prop
    · simp [Matrix.updateRow_apply, hr]
      fun_prop
  convert (smooth_det (n := n)).comp hrow using 1
  funext A
  simp only [Function.comp_apply, Matrix.adjugate_apply]

theorem smoothAt_matrix_inverse (G : Matrix (Fin n) (Fin n) ℝ)
    (hdet : G.det ≠ 0) :
    ContDiffAt ℝ ∞ (fun A : Matrix (Fin n) (Fin n) ℝ => A⁻¹) G := by
  have hs : ContDiffAt ℝ ∞ (fun A : Matrix (Fin n) (Fin n) ℝ =>
      A.det⁻¹ • A.adjugate) G := ((smooth_det (n := n)).contDiffAt.inv hdet).smul
    (smooth_adjugate (n := n)).contDiffAt
  simpa only [Matrix.inv_def, Ring.inverse_eq_inv', Pi.smul_apply, Pi.inv_apply] using hs


def scalarChartState (p : ChartState (n := n)) : ℝ :=
  ∑ i, ∑ j, p.1⁻¹ i j * ricciJet (chartStateJet p) i j


theorem smoothAt_scalarChartState (p : ChartState (n := n))
    (hdet : p.1.det ≠ 0) : ContDiffAt ℝ ∞ scalarChartState p := by
  have hinv : ContDiffAt ℝ ∞ (fun q : ChartState (n := n) => q.1⁻¹) p :=
    (smoothAt_matrix_inverse p.1 hdet).comp p contDiffAt_fst
  have hinvEntry (k l : Fin n) : ContDiffAt ℝ ∞
      (fun q : ChartState (n := n) => q.1⁻¹ k l) p :=
    (contDiffAt_apply ℝ _ l _).comp p
      ((contDiffAt_apply ℝ _ k _).comp p hinv)
  have hfirst (a i j : Fin n) : ContDiffAt ℝ ∞
      (fun q : ChartState (n := n) => q.2.1 a i j) p := by fun_prop
  have hsecond (a b i j : Fin n) : ContDiffAt ℝ ∞
      (fun q : ChartState (n := n) => q.2.2 a b i j) p := by fun_prop
  have hchrist (k i j : Fin n) : ContDiffAt ℝ ∞
      (fun q : ChartState (n := n) => christoffelJet (chartStateJet q) k i j) p := by
    unfold christoffelJet chartStateJet
    exact contDiffAt_const.mul (ContDiffAt.sum fun l _ =>
      (hinvEntry k l).mul (((hfirst i l j).add (hfirst j l i)).sub (hfirst l i j)))
  have hinverseFirst (a k l : Fin n) : ContDiffAt ℝ ∞
      (fun q : ChartState (n := n) => inverseFirst (chartStateJet q) a k l) p := by
    unfold inverseFirst chartStateJet
    exact (ContDiffAt.sum fun u _ => ContDiffAt.sum fun v _ =>
      ((hinvEntry k u).mul (hfirst a u v)).mul (hinvEntry v l)).neg
  have hchristSecond (a k i j : Fin n) : ContDiffAt ℝ ∞
      (fun q : ChartState (n := n) =>
        christoffelSecond (chartStateJet q) a k i j) p := by
    unfold christoffelSecond chartStateJet
    exact contDiffAt_const.mul (ContDiffAt.sum fun l _ =>
      ((hinverseFirst a k l).mul (((hfirst i l j).add (hfirst j l i)).sub
        (hfirst l i j))).add ((hinvEntry k l).mul
          (((hsecond a i l j).add (hsecond a j l i)).sub (hsecond a l i j))))
  have hmixed (i j k l : Fin n) : ContDiffAt ℝ ∞
      (fun q : ChartState (n := n) => mixedCurvatureJet (chartStateJet q) i j k l) p := by
    unfold mixedCurvatureJet
    exact ((hchristSecond i l j k).sub (hchristSecond j l i k)).add
      (ContDiffAt.sum fun m _ => ((hchrist m j k).mul (hchrist l i m)).sub
        ((hchrist m i k).mul (hchrist l j m)))
  unfold scalarChartState ricciJet
  exact ContDiffAt.sum fun i _ => ContDiffAt.sum fun j _ =>
    (hinvEntry i j).mul (ContDiffAt.sum fun k _ => hmixed k i j k)


def euclideanMetricState (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
    (b : Module.Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    (x : EuclideanSpace ℝ (Fin n)) : ChartState (n := n) :=
  let q := coordinateMetricJet b (fun y i j => g.inner y (b i) (b j)) x
  (q.value, q.first, q.second)

theorem euclideanMetricState_posDef (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
    (b : Module.Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    (x : EuclideanSpace ℝ (Fin n)) : (euclideanMetricState g b x).1.PosDef := by
  exact frameMetricJet_value_posDef g (fun a _ => b a) x b (fun _ => rfl)

private theorem scalarCurvature_eq_inverse_gram
    {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))} (D : LeviCivitaData g)
    (x : EuclideanSpace ℝ (Fin n))
    (b : Module.Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) :
    D.scalarCurvature x = ∑ i, ∑ j,
      (Matrix.of (fun i j => g.inner x (b i) (b j)))⁻¹ i j *
        D.ricci x (b i) (b j) := by
  let : Bundle.RiemannianBundle
      (TangentSpace (𝓡 n) : EuclideanSpace ℝ (Fin n) → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let B := ∑ i, D.curvatureTensor_bilinear_first_third x
    (g.orthonormalBasis x i) (g.orthonormalBasis x i)
  have h := bilinear_sum_basis_eq_inverse_gram (E := TangentSpace (𝓡 n) x)
    B b (g.orthonormalBasis x)
  change (∑ i, B (g.orthonormalBasis x i) (g.orthonormalBasis x i)) =
    ∑ i, ∑ j, (Matrix.of (fun i j => g.inner x (b i) (b j)))⁻¹ i j * B (b i) (b j) at h
  simpa only [B, LinearMap.sum_apply, LeviCivitaData.curvatureTensor_bilinear_first_third_apply,
    LeviCivitaData.ricci, LeviCivitaData.scalarCurvature] using h


theorem scalarCurvature_eq_scalarChartState
    {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))} (D : LeviCivitaData g)
    (b : Module.Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    (x : EuclideanSpace ℝ (Fin n)) :
    D.scalarCurvature x = scalarChartState (euclideanMetricState g b x) := by
  let F : Fin n → (y : EuclideanSpace ℝ (Fin n)) → TangentSpace (𝓡 n) y :=
    fun a _ => b a
  have hF (a : Fin n) : ContMDiffOn (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞
      (T% (F a)) Set.univ := by
    apply ContMDiff.contMDiffOn
    intro y
    rw [Bundle.contMDiffAt_totalSpace]
    exact ⟨contMDiffAt_id, by simpa using
      (contMDiffAt_const (I := 𝓡 n) (I' := 𝓡 n) (c := b a) (x := y))⟩
  have hbracket (y : EuclideanSpace ℝ (Fin n)) (_ : y ∈ Set.univ) (a c : Fin n) :
      VectorField.mlieBracket (𝓡 n) (fun _ => b a) (fun _ => b c) y = 0 := by
    simp only [VectorField.mlieBracket, VectorField.mlieBracketWithin_eq_lieBracketWithin,
      VectorField.lieBracketWithin, fderivWithin_univ, fderiv_const_apply]
    simp +instances
  have hricci (i j : Fin n) := ricci_eq_ricciJet_frameMetricJet D isOpen_univ
    (fun a _ => b a) hF (fun _ _ => b) (fun _ _ _ => rfl) hbracket
    (Set.mem_univ x) i j
  have hstate : frameMetricJet g (fun a _ => b a) x =
      chartStateJet (euclideanMetricState g b x) := by
    unfold frameMetricJet chartStateJet euclideanMetricState coordinateMetricJet
    simp only [mvfderiv, mfderiv_eq_fderiv]
    rfl
  rw [scalarCurvature_eq_inverse_gram D x b]
  unfold scalarChartState
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hricci i j, hstate]
  rfl

end PoincareConjecture.DeepHorn
