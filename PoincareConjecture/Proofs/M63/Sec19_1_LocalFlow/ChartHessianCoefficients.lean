import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.GaugeCoefficientRegularity
import PoincareConjecture.Proofs.M63.Sec19_4_Approximation.GeodesicConnection
import PoincareConjecture.Proofs.M09.LocalFixedChartHessian
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.Jacobi.Coefficients










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M63

open Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin n)




theorem hessian_eq_chart_christoffel {g : RiemannianMetric n M}
    (D : LeviCivitaData g) {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    (p q : M) (hq : q ∈ (chartAt E p).source) (u v : E) :
    let φ : E → ℝ := f ∘ (chartAt E p).symm
    D.hessian f q (chartVectorField p u q) (chartVectorField p v q) =
      fderiv ℝ (fderiv ℝ φ) ((chartAt E p) q) u v -
        fderiv ℝ φ ((chartAt E p) q)
          (coordinateChristoffel (g.pullbackCoefficients (chartAt E p).symm)
            ((chartAt E p) q) u v) := by
  let A := CoordinateExponential.christoffelBilinear
    (g.pullbackCoefficients (chartAt E p).symm) ((chartAt E p) q) u
  apply hessian_fixedChart_local D f p q hq univ isOpen_univ (mem_univ q)
    hf.contMDiffOn u v A
  intro w
  have h := chartVectorField_coordinateChristoffel D p ((chartAt E p) q)
    ((chartAt E p).map_source hq) u w
  rw [(chartAt E p).left_inv hq] at h
  exact h.symm




theorem flow_hessian_chart_contDiffOn {a b : ℝ} (F : RicciFlow n M (Icc a b))
    {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) (p : M) :
    ContDiffOn ℝ ∞
      (fun z : (ℝ × E) × E =>
        (F.connection z.1.1).hessian f ((chartAt E p).symm z.1.2)
          (chartVectorField p z.2 ((chartAt E p).symm z.1.2))
          (chartVectorField p z.2 ((chartAt E p).symm z.1.2)))
      ((Icc a b ×ˢ (chartAt E p).target) ×ˢ univ) := by
  let c := chartAt E p
  let φ : E → ℝ := f ∘ c.symm
  let S : Set ((ℝ × E) × E) := (Icc a b ×ˢ c.target) ×ˢ univ
  have hφ : ContDiffOn ℝ ∞ φ c.target :=
    (hf.comp_contMDiffOn (contMDiffOn_chart_symm (I := 𝓡 n) (x := p))).contDiffOn
  have hD := hφ.fderiv_of_isOpen c.open_target (m := ∞) (by simp)
  have hDD := hD.fderiv_of_isOpen c.open_target (m := ∞) (by simp)
  have hy : ContDiffOn ℝ ∞ (fun z : (ℝ × E) × E => z.1.2) S :=
    contDiff_fst.snd.contDiffOn
  have hDy : ContDiffOn ℝ ∞ (fun z : (ℝ × E) × E => fderiv ℝ φ z.1.2) S :=
    hD.comp hy (fun _ hz => hz.1.2)
  have hDDy : ContDiffOn ℝ ∞
      (fun z : (ℝ × E) × E => fderiv ℝ (fderiv ℝ φ) z.1.2) S :=
    hDD.comp hy (fun _ hz => hz.1.2)
  have hexpr := ((hDDy.clm_apply contDiffOn_snd).clm_apply contDiffOn_snd).sub
    (hDy.clm_apply (gauge_christoffel_contDiffOn F p))
  apply hexpr.congr
  intro z hz
  have h := hessian_eq_chart_christoffel (F.connection z.1.1) hf p (c.symm z.1.2)
    (c.map_target hz.1.2) z.2 z.2
  dsimp only at h
  rw [c.right_inv hz.1.2] at h
  exact h

end PoincareConjecture.M63
