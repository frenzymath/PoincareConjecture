import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Curvature.Estimates.Local
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.TimeTranslation











set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.M30




theorem exists_uniform_curvatureDerivativeNorm_bound_on_buffered_cylinders
    (hShi : LocalCurvatureDerivativeEstimates.{u}) (n m : ℕ) (B T r δ : ℝ)
    (hT : 0 < T) (hr : 0 < r) (hδ : 0 < δ) :
    ∃ D : ℝ, 0 < D ∧
      ∀ (M : Type u) [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
        [T2Space M] [SecondCountableTopology M],
      ∀ (G : RicciFlow n M (Icc (-T) 0)) (V : Set M),
        (∀ x ∈ V, IsCompact (closure ((G.metric (-T)).ball x r))) →
        (∀ s ∈ Icc (-T) 0, ∀ y : M, (G.connection s).curvatureTensorNorm y ≤ B) →
        ∀ s ∈ Icc (-T + δ) 0, ∀ x ∈ V,
          (G.connection s).curvatureDerivativeNorm m x ≤ D := by
  let K := max B 1
  have hK : 0 < K := lt_of_lt_of_le (by norm_num) (le_max_right B 1)
  obtain ⟨C, hC, hlocal⟩ := hShi n m K (T * K) r hK (mul_pos hT hK) hr
  refine ⟨C / δ ^ ((m : ℝ) / 2), by positivity, ?_⟩
  intro M _ _ _ _ _ G V hcompact hcurv s hs x hx
  have hshift : (fun t : ℝ => t + -T) '' Icc 0 T ⊆ Icc (-T) 0 := by
    rintro _ ⟨t, ht, rfl⟩
    constructor <;> linarith [ht.1, ht.2]
  have hne : (Icc (0 : ℝ) T).Nontrivial :=
    ⟨0, ⟨le_rfl, hT.le⟩, T, ⟨hT.le, le_rfl⟩, hT.ne'.symm⟩
  let Gplus := G.translate (-T) hshift ordConnected_Icc hne
  have hlength : T ≤ (T * K) / K := by
    rw [mul_div_cancel_right₀ _ hK.ne']
  have hcompact' : IsCompact (closure ((Gplus.metric 0).ball x r)) := by
    simpa only [Gplus, RicciFlow.translate, zero_add] using hcompact x hx
  have hcurv' : ∀ t ∈ Icc 0 T, ∀ y ∈ (Gplus.metric 0).ball x r,
      (Gplus.connection t).curvatureTensorNorm y ≤ K := by
    intro t ht y _
    exact (hcurv (t + -T) (by constructor <;> linarith [ht.1, ht.2]) y).trans
      (le_max_left B 1)
  have hs' : s + T ∈ Ioc 0 T := by
    constructor <;> linarith [hs.1, hs.2]
  have hx' : x ∈ (Gplus.metric 0).ball x (r / 2) := by
    change (Gplus.metric 0).edist x x < ENNReal.ofReal (r / 2)
    simp only [RiemannianMetric.edist, Manifold.riemannianEDist_self]
    exact ENNReal.ofReal_pos.mpr (by positivity)
  have h := hlocal M T hT hlength Gplus x hcompact' hcurv' (s + T) hs' x hx'
  change (G.connection (s + T + -T)).curvatureDerivativeNorm m x ≤ _ at h
  rw [add_neg_cancel_right] at h
  apply h.trans
  apply div_le_div_of_nonneg_left hC.le (Real.rpow_pos_of_pos hδ _)
  exact Real.rpow_le_rpow hδ.le (by linarith [hs.1]) (by positivity)

end PoincareConjecture.M30
