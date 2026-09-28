import PoincareConjecture.Proofs.M03.Existence.CoordinateCurvatureNative
import PoincareConjecture.Proofs.M03.Existence.FrameJetDerivativeNative









set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators Topology Matrix.Norms.Elementwise

noncomputable section

universe u

namespace PoincareConjecture.DeTurckNative

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem mdifferentiableAt_christoffelJet_frameMetricJet
    (g : RiemannianMetric n M)
    (F : Fin n → (y : M) → TangentSpace (𝓡 n) y) {x : M}
    (hF : ∀ a, ContMDiffAt (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% (F a)) x)
    (hdet : (frameMetricJet g F x).value.det ≠ 0)
    (k i j : Fin n) :
    MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ)
      (fun y => christoffelJet (frameMetricJet g F y) k i j) x := by
  have hG : ContMDiffAt (𝓡 n) 𝓘(ℝ, Fin n → Fin n → ℝ) 1
      (fun y r s => (frameMetricJet g F y).value r s) x :=
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
  have hterm (l : Fin n) : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ)
      (fun y => (frameMetricJet g F y).value⁻¹ k l *
        ((frameMetricJet g F y).first i l j +
          (frameMetricJet g F y).first j l i -
          (frameMetricJet g F y).first l i j)) x :=
    (hIe k l).mul (((hfirst i l j).add (hfirst j l i)).sub (hfirst l i j))
  have hsum : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ)
      (fun y => ∑ l, (frameMetricJet g F y).value⁻¹ k l *
        ((frameMetricJet g F y).first i l j +
          (frameMetricJet g F y).first j l i -
          (frameMetricJet g F y).first l i j)) x := by
    convert (MDifferentiableAt.sum (t := Finset.univ)
      (fun (l : Fin n) (_ : l ∈ Finset.univ) => hterm l)) using 1
    funext y
    simp only [Finset.sum_apply]
  exact mdifferentiableAt_const.mul hsum

theorem connection_eq_frame_christoffelJet
    {g : RiemannianMetric n M} (D : LeviCivitaData g)
    (F : Fin n → (y : M) → TangentSpace (𝓡 n) y) {x : M}
    (b : Module.Basis (Fin n) ℝ (TangentSpace (𝓡 n) x))
    (hpoint : ∀ a, F a x = b a)
    (hF : ∀ a, MDifferentiableAt (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% (F a)) x)
    (hbracket : ∀ a c, VectorField.mlieBracket (𝓡 n) (F a) (F c) x = 0)
    (i j : Fin n) :
    D.connection (F j) x (F i x) =
      ∑ l, christoffelJet (frameMetricJet g F x) l i j • F l x := by
  classical
  calc
    D.connection (F j) x (F i x) =
        ∑ l, b.repr (D.connection (F j) x (F i x)) l • b l :=
      (b.sum_repr _).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro l _
      rw [connection_repr_eq_christoffelJet D F b hpoint hF hbracket l i j,
        hpoint l]

theorem curvature_repr_eq_mixedCurvatureJet_frameMetricJet
    {g : RiemannianMetric n M} (D : LeviCivitaData g)
    {U : Set M} (hU : IsOpen U)
    (F : Fin n → (y : M) → TangentSpace (𝓡 n) y)
    (hF : ∀ a, ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% (F a)) U)
    (b : (y : M) → y ∈ U → Module.Basis (Fin n) ℝ (TangentSpace (𝓡 n) y))
    (hpoint : ∀ y (hy : y ∈ U) a, F a y = b y hy a)
    (hbracket : ∀ y ∈ U, ∀ a c,
      VectorField.mlieBracket (𝓡 n) (F a) (F c) y = 0)
    {x : M} (hx : x ∈ U) (i j k l : Fin n) :
    (b x hx).repr (D.curvature x (F i x) (F j x) (F k x)) l =
      mixedCurvatureJet (frameMetricJet g F x) i j k l := by
  let Γ : Fin n → Fin n → Fin n → M → ℝ :=
    fun r a c y => christoffelJet (frameMetricJet g F y) r a c
  have hFAt (y : M) (hy : y ∈ U) (a : Fin n) :
      ContMDiffAt (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% (F a)) y :=
    (hF a).contMDiffAt (hU.mem_nhds hy)
  have hcoeff (y : M) (hy : y ∈ U) (a c : Fin n) :
      D.connection (F c) y (F a y) = ∑ r, Γ r a c y • F r y :=
    connection_eq_frame_christoffelJet D F (b y hy) (hpoint y hy)
      (fun r => (hFAt y hy r).mdifferentiableAt (by simp)) (hbracket y hy) a c
  have hdet : (frameMetricJet g F x).value.det ≠ 0 :=
    ne_of_gt (frameMetricJet_value_posDef g F x (b x hx) (hpoint x hx)).det_pos
  have hΓ (r a c : Fin n) :
      MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) (Γ r a c) x :=
    mdifferentiableAt_christoffelJet_frameMetricJet g F (hFAt x hx) hdet r a c
  calc
    _ = frameCurvatureCoefficient F Γ x i j k l :=
      curvature_repr_eq_frameCurvatureCoefficient D hU F hF Γ hcoeff hx hΓ
        (b x hx) (hpoint x hx) (hbracket x hx) i j k l
    _ = _ := by
      dsimp only [frameCurvatureCoefficient, mixedCurvatureJet, Γ]
      rw [mvfderiv_christoffelJet_frameMetricJet g F (hFAt x hx) hdet i l j k,
        mvfderiv_christoffelJet_frameMetricJet g F (hFAt x hx) hdet j l i k]

theorem ricci_eq_ricciJet_frameMetricJet
    {g : RiemannianMetric n M} (D : LeviCivitaData g)
    {U : Set M} (hU : IsOpen U)
    (F : Fin n → (y : M) → TangentSpace (𝓡 n) y)
    (hF : ∀ a, ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% (F a)) U)
    (b : (y : M) → y ∈ U → Module.Basis (Fin n) ℝ (TangentSpace (𝓡 n) y))
    (hpoint : ∀ y (hy : y ∈ U) a, F a y = b y hy a)
    (hbracket : ∀ y ∈ U, ∀ a c,
      VectorField.mlieBracket (𝓡 n) (F a) (F c) y = 0)
    {x : M} (hx : x ∈ U) (i j : Fin n) :
    D.ricci x (F i x) (F j x) = ricciJet (frameMetricJet g F x) i j := by
  rw [Proofs.M03.ricci_eq_sum_basis D x (F i x) (F j x) (b x hx)]
  unfold ricciJet
  apply Finset.sum_congr rfl
  intro k _
  rw [← hpoint x hx k]
  exact curvature_repr_eq_mixedCurvatureJet_frameMetricJet D hU F hF b
    hpoint hbracket hx k i j k

end PoincareConjecture.DeTurckNative

end
