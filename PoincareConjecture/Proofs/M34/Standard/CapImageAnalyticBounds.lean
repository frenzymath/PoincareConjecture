import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.CapPersistenceBoundaryScalar
import PoincareConjecture.Proofs.M34.Standard.ScalarGradientNorm

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u v

namespace PoincareConjecture.CapCertificate

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  {g : RiemannianMetric 3 M} (N : CapCertificate g)

theorem exists_image_scalarAnalytic_tolerance {C eta : ℝ}
    (hC : 0 < C) (heta : 0 < eta) :
    ∃ nu : ℝ, 0 < nu ∧
      ∀ {X : Type v} [TopologicalSpace X]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X] [IsManifold (𝓡 3) ∞ X]
        (h : RiemannianMetric 3 X) (D : LeviCivitaData h) (f : M → X),
        (∀ x ∈ closure N.end_neck.carrier,
          |N.end_neck.scale ^ 2 * N.connection.scalarCurvature x - 1| ≤
            min (eta / 2) (1 / 10)) →
        (∀ x ∈ N.carrier,
          ‖(D.scalarCurvature (f x), scalarGradientNorm h D (f x),
              D.laplacian D.scalarCurvature (f x) + 2 * D.ricciNormSq (f x)) -
            (N.connection.scalarCurvature x, scalarGradientNorm g N.connection x,
              N.connection.laplacian N.connection.scalarCurvature x +
                2 * N.connection.ricciNormSq x)‖ ≤ nu) →
        (∀ x ∈ N.carrier,
          |D.scalarCurvature (f x) - N.connection.scalarCurvature x| ≤ (2 * C)⁻¹) ∧
        (∀ x ∈ N.carrier,
          |scalarGradientNorm h D (f x) - scalarGradientNorm g N.connection x| ≤ 1) ∧
        (∀ x ∈ N.carrier,
          |(D.laplacian D.scalarCurvature (f x) + 2 * D.ricciNormSq (f x)) -
            (N.connection.laplacian N.connection.scalarCurvature x +
              2 * N.connection.ricciNormSq x)| ≤ 1) ∧
        (∀ x ∈ N.end_neck.carrier,
          |N.end_neck.scale ^ 2 * D.scalarCurvature (f x) - 1| ≤ eta) ∧
        |N.boundary_neck.scale ^ 2 * D.scalarCurvature (f N.boundary_neck.center) - 1| ≤ eta ∧
        (∀ x ∈ N.boundary_sphere,
          (2 * N.end_neck.scale ^ 2)⁻¹ ≤ D.scalarCurvature (f x)) := by
  let a := N.end_neck.scale ^ 2
  let b := N.boundary_neck.scale ^ 2
  have ha : 0 < a := sq_pos_of_pos N.end_neck.scale_pos
  have hb : 0 < b := sq_pos_of_pos N.boundary_neck.scale_pos
  let nu := min 1 (min (2 * C)⁻¹ (min (eta / (2 * a))
    (min (eta / (2 * b)) (10 * a)⁻¹)))
  have hnu : 0 < nu := by dsimp only [nu]; positivity
  have hn : nu ≤ 1 ∧ nu ≤ (2 * C)⁻¹ ∧ nu ≤ eta / (2 * a) ∧
      nu ≤ eta / (2 * b) ∧ nu ≤ (10 * a)⁻¹ := by
    have h1 := le_min_iff.mp (le_rfl : nu ≤
      min 1 (min (2 * C)⁻¹ (min (eta / (2 * a)) (min (eta / (2 * b)) (10 * a)⁻¹))))
    have h2 := le_min_iff.mp h1.2
    have h3 := le_min_iff.mp h2.2
    have h4 := le_min_iff.mp h3.2
    exact ⟨h1.1, h2.1, h3.1, h4.1, h4.2⟩
  have hanu : a * nu ≤ eta / 2 := by
    have h := (le_div_iff₀ (by positivity : 0 < 2 * a)).mp hn.2.2.1
    nlinarith
  have hbnu : b * nu ≤ eta / 2 := by
    have h := (le_div_iff₀ (by positivity : 0 < 2 * b)).mp hn.2.2.2.1
    nlinarith
  have hanu' : a * nu ≤ 1 / 10 := by
    have h := (le_div_iff₀ (by positivity : 0 < 10 * a)).mp
      (show nu ≤ 1 / (10 * a) by simpa only [one_div] using hn.2.2.2.2)
    nlinarith
  refine ⟨nu, hnu, ?_⟩
  intro X _ _ _ h D f hold htuple
  have herr (x : M) (hx : x ∈ N.carrier) :
      |D.scalarCurvature (f x) - N.connection.scalarCurvature x| ≤ nu ∧
      |scalarGradientNorm h D (f x) - scalarGradientNorm g N.connection x| ≤ nu ∧
      |(D.laplacian D.scalarCurvature (f x) + 2 * D.ricciNormSq (f x)) -
        (N.connection.laplacian N.connection.scalarCurvature x +
          2 * N.connection.ricciNormSq x)| ≤ nu := by
    simpa only [Prod.norm_def, Prod.fst_sub, Prod.snd_sub, Real.norm_eq_abs,
      max_le_iff] using htuple x hx
  have hweighted (x : M) (hx : x ∈ N.carrier) :
      |a * (D.scalarCurvature (f x) - N.connection.scalarCurvature x)| ≤ a * nu := by
    rw [abs_mul, abs_of_pos ha]
    exact mul_le_mul_of_nonneg_left (herr x hx).1 ha.le
  refine ⟨fun x hx => (herr x hx).1.trans hn.2.1,
    fun x hx => (herr x hx).2.1.trans hn.1,
    fun x hx => (herr x hx).2.2.trans hn.1, ?_, ?_, ?_⟩
  · intro x hx
    calc
      _ = |a * (D.scalarCurvature (f x) - N.connection.scalarCurvature x) +
          (a * N.connection.scalarCurvature x - 1)| := congrArg abs (by dsimp [a]; ring)
      _ ≤ |a * (D.scalarCurvature (f x) - N.connection.scalarCurvature x)| +
          |a * N.connection.scalarCurvature x - 1| := abs_add_le _ _
      _ ≤ a * nu + eta / 2 := add_le_add (hweighted x (N.end_neck_subset hx))
        ((hold x (subset_closure hx)).trans (min_le_left _ _))
      _ ≤ eta := by linarith
  · have hcenter : N.boundary_neck.center ∈ N.boundary_sphere := by
      rw [N.boundary_eq_neck_sphere]
      exact N.boundary_neck.center_on_central_sphere
    have hnormal := N.boundary_neck.scale_sq_mul_scalar_center
    rw [N.boundary_neck_connection] at hnormal
    calc
      _ = |b * (D.scalarCurvature (f N.boundary_neck.center) -
          N.connection.scalarCurvature N.boundary_neck.center)| := by
        congr 1
        dsimp only [b]
        nlinarith
      _ = b * |D.scalarCurvature (f N.boundary_neck.center) -
          N.connection.scalarCurvature N.boundary_neck.center| := by
        rw [abs_mul, abs_of_pos hb]
      _ ≤ b * nu := mul_le_mul_of_nonneg_left
        (herr _ (N.boundary_subset hcenter)).1 hb.le
      _ ≤ eta := hbnu.trans (by linarith)
  · intro x hx
    have hxend : x ∈ closure N.end_neck.carrier :=
      (closure_mono (fun _ hy => hy.1)) (N.boundary_subset_negative_end_closure hx)
    have hsource := (abs_le.mp ((hold x hxend).trans (min_le_right _ _))).1
    have htarget := (abs_le.mp ((hweighted x (N.boundary_subset hx)).trans hanu')).1
    have hlow : (1 / 2 : ℝ) ≤ a * D.scalarCurvature (f x) := by
      change -(1 / 10 : ℝ) ≤ a * N.connection.scalarCurvature x - 1 at hsource
      nlinarith
    rw [← one_div, div_le_iff₀ (by positivity : 0 < 2 * N.end_neck.scale ^ 2)]
    change 1 ≤ D.scalarCurvature (f x) * (2 * a)
    nlinarith

end PoincareConjecture.CapCertificate
