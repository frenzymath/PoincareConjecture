import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.Boundary








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.RiemannianMetric

variable {S : Type*} [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]



theorem frameQuarterTurn_change
    (g : RiemannianMetric 2 S) (x : S)
    {e₁ e₂ : TangentSpace (𝓡 2) x}
    (he₁ : g.inner x e₁ e₁ = 1) (he₂ : g.inner x e₂ e₂ = 1)
    (horth : g.inner x e₁ e₂ = 0) (f₁ f₂ v : TangentSpace (𝓡 2) x) :
    -g.inner x v f₂ • f₁ + g.inner x v f₁ • f₂ =
      (g.inner x f₁ e₁ * g.inner x f₂ e₂ - g.inner x f₁ e₂ * g.inner x f₂ e₁) •
        (-g.inner x v e₂ • e₁ + g.inner x v e₁ • e₂) := by
  have hf₁ := g.eq_frameCoordinates_smul x he₁ he₂ horth f₁
  have hf₂ := g.eq_frameCoordinates_smul x he₁ he₂ horth f₂
  conv_lhs => rw [hf₁, hf₂]
  simp only [map_add, map_smul, smul_eq_mul]
  module

end PoincareConjecture.RiemannianMetric

namespace PoincareConjecture.LeviCivitaData

variable {S : Type*} [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]
  {g : RiemannianMetric 2 S}


theorem surfaceTurningForm_change_frame
    (D : LeviCivitaData g) (e₁ e₂ f₁ f₂ T V : (x : S) → TangentSpace (𝓡 2) x)
    (x : S) (he₁ : g.inner x (e₁ x) (e₁ x) = 1)
    (he₂ : g.inner x (e₂ x) (e₂ x) = 1) (ho : g.inner x (e₁ x) (e₂ x) = 0) :
    D.surfaceTurningForm f₁ f₂ T V x =
      (g.inner x (f₁ x) (e₁ x) * g.inner x (f₂ x) (e₂ x) -
        g.inner x (f₁ x) (e₂ x) * g.inner x (f₂ x) (e₁ x)) *
          D.surfaceTurningForm e₁ e₂ T V x := by
  unfold surfaceTurningForm
  rw [g.frameQuarterTurn_change x he₁ he₂ ho, map_smul, smul_eq_mul]


theorem surfaceTurningForm_eq_of_frameDet_pos
    (D : LeviCivitaData g) (e₁ e₂ f₁ f₂ T V : (x : S) → TangentSpace (𝓡 2) x)
    (x : S) (he₁ : g.inner x (e₁ x) (e₁ x) = 1)
    (he₂ : g.inner x (e₂ x) (e₂ x) = 1) (he : g.inner x (e₁ x) (e₂ x) = 0)
    (hf₁ : g.inner x (f₁ x) (f₁ x) = 1)
    (hf₂ : g.inner x (f₂ x) (f₂ x) = 1) (hf : g.inner x (f₁ x) (f₂ x) = 0)
    (hdet : 0 < g.inner x (f₁ x) (e₁ x) * g.inner x (f₂ x) (e₂ x) -
      g.inner x (f₁ x) (e₂ x) * g.inner x (f₂ x) (e₁ x)) :
    D.surfaceTurningForm f₁ f₂ T V x = D.surfaceTurningForm e₁ e₂ T V x := by
  have hs := gramDet_eq_frameDet_sq g x he₁ he₂ he (f₁ x) (f₂ x)
  rw [hf₁, hf₂, hf] at hs
  have hd : g.inner x (f₁ x) (e₁ x) * g.inner x (f₂ x) (e₂ x) -
      g.inner x (f₁ x) (e₂ x) * g.inner x (f₂ x) (e₁ x) = 1 := by nlinarith
  rw [D.surfaceTurningForm_change_frame e₁ e₂ f₁ f₂ T V x he₁ he₂ he, hd, one_mul]


theorem surfaceTurningForm_eq_neg_of_frameDet_neg
    (D : LeviCivitaData g) (e₁ e₂ f₁ f₂ T V : (x : S) → TangentSpace (𝓡 2) x)
    (x : S) (he₁ : g.inner x (e₁ x) (e₁ x) = 1)
    (he₂ : g.inner x (e₂ x) (e₂ x) = 1) (he : g.inner x (e₁ x) (e₂ x) = 0)
    (hf₁ : g.inner x (f₁ x) (f₁ x) = 1)
    (hf₂ : g.inner x (f₂ x) (f₂ x) = 1) (hf : g.inner x (f₁ x) (f₂ x) = 0)
    (hdet : g.inner x (f₁ x) (e₁ x) * g.inner x (f₂ x) (e₂ x) -
      g.inner x (f₁ x) (e₂ x) * g.inner x (f₂ x) (e₁ x) < 0) :
    D.surfaceTurningForm f₁ f₂ T V x = -D.surfaceTurningForm e₁ e₂ T V x := by
  have hs := gramDet_eq_frameDet_sq g x he₁ he₂ he (f₁ x) (f₂ x)
  rw [hf₁, hf₂, hf] at hs
  have hd : g.inner x (f₁ x) (e₁ x) * g.inner x (f₂ x) (e₂ x) -
      g.inner x (f₁ x) (e₂ x) * g.inner x (f₂ x) (e₁ x) = -1 := by nlinarith
  rw [D.surfaceTurningForm_change_frame e₁ e₂ f₁ f₂ T V x he₁ he₂ he, hd, neg_one_mul]


theorem surfaceTurningForm_neg_field
    (D : LeviCivitaData g) (e₁ e₂ T V : (x : S) → TangentSpace (𝓡 2) x)
    (x : S) (hT : MDifferentiableAt (𝓡 2) ((𝓡 2).prod (𝓡 2)) (T% T) x) :
    D.surfaceTurningForm e₁ e₂ (-T) V x = D.surfaceTurningForm e₁ e₂ T V x := by
  have hneg : D.connection (-T) x = -D.connection T x := by
    simpa only [neg_one_smul] using D.connection.isCovariantDerivativeOnUniv.smul_const (-1) hT
  simp only [surfaceTurningForm, hneg, Pi.neg_apply, neg_apply, map_neg, neg_smul,
    neg_neg, map_add, map_smul, smul_eq_mul]
  ring


theorem surfaceTurningForm_neg_direction
    (D : LeviCivitaData g) (e₁ e₂ T V : (x : S) → TangentSpace (𝓡 2) x) (x : S) :
    D.surfaceTurningForm e₁ e₂ T (-V) x = -D.surfaceTurningForm e₁ e₂ T V x := by
  simp only [surfaceTurningForm, Pi.neg_apply, map_neg, neg_apply]

end PoincareConjecture.LeviCivitaData
