import PoincareConjecture.Definitions.Ch09.NeckCapTopology
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Homothety.Assembly
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.Regularity
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.ScalarOperators.Divergence.Pullback
import PoincareConjecture.Proofs.M14.Sec6_5_ScalarEvolutionTransportRicci

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u v w

namespace PoincareConjecture.M32

theorem preimage_value_range {X : Type u} {Y : Type v} {Z : Type w}
    (e : X ≃ Y) (U : Set Y) (a : X → Z) (b : Y → Z)
    (hab : ∀ x, a x = b (e x)) :
    Set.range (fun x : e ⁻¹' U => a x.1) = Set.range (fun y : U => b y.1) := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨⟨e x, x.property⟩, (hab x).symm⟩
  · rintro ⟨y, rfl⟩
    refine ⟨⟨e.symm y, by simp [y.property]⟩, ?_⟩
    simpa using hab (e.symm y)

variable {M : Type u} {N : Type v}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
  [IsManifold (𝓡 3) ∞ N] [T3Space N] [MeasurableSpace N] [BorelSpace N]
  {g : RiemannianMetric 3 M} {h : RiemannianMetric 3 N}
  {e : Diffeomorph (𝓡 3) (𝓡 3) M N ∞}
  (Hcal : MetricHomothetyCalculus g h e 1)

include Hcal

theorem unitHomothety_scalar_eq (D : LeviCivitaData g) (D' : LeviCivitaData h) (x : M) :
    D.scalarCurvature x = D'.scalarCurvature (e x) := by
  simpa only [div_one] using (Hcal.scalar_eq D D' x).symm

theorem unitHomothety_scalar_range (D : LeviCivitaData g) (D' : LeviCivitaData h)
    (U : Set N) (a : ℝ → ℝ) :
    Set.range (fun x : e ⁻¹' U => a (D.scalarCurvature x.1)) =
      Set.range (fun y : U => a (D'.scalarCurvature y.1)) :=
  preimage_value_range e.toEquiv U (fun x => a (D.scalarCurvature x))
    (fun y => a (D'.scalarCurvature y))
    (fun x => congrArg a (unitHomothety_scalar_eq Hcal D D' x))

theorem unitHomothety_scalarSup_eq
    (D : LeviCivitaData g) (D' : LeviCivitaData h) (U : Set N) :
    scalarCurvatureSupOn g D (e ⁻¹' U) = scalarCurvatureSupOn h D' U := by
  unfold scalarCurvatureSupOn
  exact congrArg sSup (unitHomothety_scalar_range Hcal D D' U id)

theorem unitHomothety_ball_eq (x : M) (r : ℝ) : g.ball x r = e ⁻¹' h.ball (e x) r := by
  have hi : e '' g.ball x r = h.ball (e x) r := by simpa using Hcal.ball_image x r
  rw [← hi]
  exact (Set.preimage_image_eq _ (show Function.Injective e from e.injective)).symm

theorem unitHomothety_volume_eq (U : Set N) :
    calibratedMetricVolume g (e ⁻¹' U) = calibratedMetricVolume h U := by
  have hr : Real.rpow 1 (((3 : ℕ) : ℝ) / 2) = 1 := Real.one_rpow _
  simpa only [hr, ENNReal.ofReal_one, one_mul,
    Set.image_preimage_eq _ (show Function.Surjective e from e.surjective)] using
    (Hcal.volume_image (e ⁻¹' U)).symm

theorem unitHomothety_intrinsicEDist_eq (U : Set N) (x y : M) :
    intrinsicEDist g (e ⁻¹' U) x y = intrinsicEDist h U (e x) (e y) := by
  unfold intrinsicEDist
  congr 1
  ext L
  constructor
  · rintro ⟨γ, hγ, h0, h1, hU, rfl⟩
    refine ⟨e ∘ γ, (e.contMDiff.of_le (by simp)).comp_contMDiffOn hγ,
      by simp [h0], by simp [h1], ?_, ?_⟩
    · rintro _ ⟨s, hs, rfl⟩
      exact hU ⟨s, hs, rfl⟩
    · simpa using (Hcal.path_length 0 1 (by norm_num) γ hγ).symm
  · rintro ⟨γ, hγ, h0, h1, hU, rfl⟩
    have hγ' := (e.symm.contMDiff.of_le (by simp)).comp_contMDiffOn hγ
    refine ⟨e.symm ∘ γ, hγ', by simp [h0], by simp [h1], ?_, ?_⟩
    · rintro _ ⟨s, hs, rfl⟩
      simpa using hU ⟨s, hs, rfl⟩
    · simpa [Function.comp_def] using Hcal.path_length 0 1 (by norm_num) (e.symm ∘ γ) hγ'

theorem unitHomothety_intrinsicDiameter_eq (U : Set N) :
    intrinsicDiameter g (e ⁻¹' U) = intrinsicDiameter h U := by
  unfold intrinsicDiameter
  congr 1
  ext L
  constructor
  · rintro ⟨⟨x, y⟩, rfl⟩
    exact ⟨(⟨e x, x.property⟩, ⟨e y, y.property⟩),
      (unitHomothety_intrinsicEDist_eq Hcal U x y).symm⟩
  · rintro ⟨⟨x, y⟩, rfl⟩
    refine ⟨(⟨e.symm x, by simp [x.property]⟩,
      ⟨e.symm y, by simp [y.property]⟩), ?_⟩
    simpa using unitHomothety_intrinsicEDist_eq Hcal U (e.symm x) (e.symm y)

theorem unitHomothety_scalarGradient_eq (he : MetricHomothety g h e 1)
    (D : LeviCivitaData g) (D' : LeviCivitaData h) (x : M) :
    scalarGradientNorm g D x = scalarGradientNorm h D' (e x) := by
  let L := e.mfderivToContinuousLinearEquiv (by simp) x
  have hL (v : TangentSpace (𝓡 3) x) : L v = mfderiv (𝓡 3) (𝓡 3) e x v := rfl
  have hscalar : D'.scalarCurvature ∘ e = D.scalarCurvature := by
    funext y
    exact (unitHomothety_scalar_eq Hcal D D' y).symm
  have hd (v : TangentSpace (𝓡 3) x) :
      mvfderiv (𝓡 3) D'.scalarCurvature (e x) (L v) =
        mvfderiv (𝓡 3) D.scalarCurvature x v := by
    rw [hL, ← mvfderiv_comp_apply x
      (D'.contMDiff_scalarCurvature.mdifferentiable (by simp) _)
      (e.contMDiff.mdifferentiable (by simp) _), hscalar]
  unfold scalarGradientNorm
  congr 1
  ext z
  constructor
  · rintro ⟨v, rfl⟩
    refine ⟨⟨L v, ?_⟩, congrArg abs (hd v)⟩
    rw [hL, he, one_mul]
    exact v.property
  · rintro ⟨v, rfl⟩
    have hv : g.inner x (L.symm v.1) (L.symm v.1) = 1 := by
      have hi := he x (L.symm v.1) (L.symm v.1)
      change h.inner (e x) (L (L.symm v.1)) (L (L.symm v.1)) = _ at hi
      simpa only [L.apply_symm_apply, one_mul, v.property] using hi.symm
    refine ⟨⟨L.symm v.1, hv⟩, ?_⟩
    simpa only [L.apply_symm_apply] using congrArg abs (hd (L.symm v.1)).symm

theorem unitHomothety_scalarEvolution_eq (he : MetricHomothety g h e 1)
    (D : LeviCivitaData g) (D' : LeviCivitaData h) (x : M) :
    D.laplacian D.scalarCurvature x + 2 * D.ricciNormSq x =
      D'.laplacian D'.scalarCurvature (e x) + 2 * D'.ricciNormSq (e x) := by
  have hs : D'.scalarCurvature ∘ e = D.scalarCurvature := by
    funext y
    exact (unitHomothety_scalar_eq Hcal D D' y).symm
  have hinv (y : M) : (mfderiv (𝓡 3) (𝓡 3) e y).IsInvertible :=
    ⟨(e.toOpenPartialHomeomorph_mdifferentiable (by simp)).mfderiv
      (x := y) (mem_univ y), rfl⟩
  have hm (y : M) (v w : TangentSpace (𝓡 3) y) :
      g.inner y v w = h.inner (e y)
        (mfderiv (𝓡 3) (𝓡 3) e y v) (mfderiv (𝓡 3) (𝓡 3) e y w) := by
    simpa only [one_mul] using (he y v w).symm
  have hlap := D.laplacian_comp_of_metric_pullback D' (e.contMDiff x)
    (Eventually.of_forall hinv) (Eventually.of_forall hm)
    (D'.contMDiff_scalarCurvature (e x))
  rw [hs] at hlap
  have hric := M14.ricciNormSq_eq_of_local_isometry D D' isOpen_univ
    e.contMDiff.contMDiffOn (fun y _ => hm y) (mem_univ x)
  rw [hlap, hric]

end PoincareConjecture.M32
