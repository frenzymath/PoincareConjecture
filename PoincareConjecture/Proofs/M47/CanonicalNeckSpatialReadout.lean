import PoincareConjecture.Proofs.M47.CanonicalNeckUniformTimeJets
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.StrongNeckCylinderReadout










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology BigOperators

universe u

namespace PoincareConjecture.Proofs.M47

open M34

local notation "E₂" => EuclideanSpace ℝ (Fin 2)
local notation "E₃" => EuclideanSpace ℝ (Fin 3)
local notation "V" => RoundCylinderCoordinates



theorem metric_chart_pullback_apply
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (a : M)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {phi : E → M} {x : E}
    (hphi : MDifferentiableAt 𝓘(ℝ, E) (𝓡 n) phi x)
    (ha : phi x ∈ (extChartAt (𝓡 n) a).source) (v w : E) :
    ((g.pullbackCoefficients (extChartAt (𝓡 n) a).symm
      ((extChartAt (𝓡 n) a) (phi x))).bilinearComp
        (fderiv ℝ ((extChartAt (𝓡 n) a) ∘ phi) x)
        (fderiv ℝ ((extChartAt (𝓡 n) a) ∘ phi) x)) v w =
      g.inner (phi x) (mfderiv 𝓘(ℝ, E) (𝓡 n) phi x v)
        (mfderiv 𝓘(ℝ, E) (𝓡 n) phi x w) := by
  have hd := mfderiv_inverse_chart_comp_fderiv_coordinates a hphi ha
  change g.inner _
    (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) a).symm
      ((extChartAt (𝓡 n) a) (phi x))
      (fderiv ℝ ((extChartAt (𝓡 n) a) ∘ phi) x v))
    (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) a).symm
      ((extChartAt (𝓡 n) a) (phi x))
      (fderiv ℝ ((extChartAt (𝓡 n) a) ∘ phi) x w)) = _
  have hv := congrArg (fun A => A v) hd
  have hw := congrArg (fun A => A w) hd
  exact (congrArg₂ (fun v1 w1 : EuclideanSpace ℝ (Fin n) =>
    g.inner ((extChartAt (𝓡 n) a).symm ((extChartAt (𝓡 n) a) (phi x))) v1 w1)
      hv hw).trans (congrArg (fun y : M =>
        g.inner y (mfderiv 𝓘(ℝ, E) (𝓡 n) phi x v)
          (mfderiv 𝓘(ℝ, E) (𝓡 n) phi x w))
            ((extChartAt (𝓡 n) a).left_inv ha))



theorem neck_metric_coefficient_fixed_native_chart
    {M : Type u} [TopologicalSpace M] [ChartedSpace E₃ M]
    [IsManifold (𝓡 3) ∞ M] (g : RiemannianMetric 3 M)
    (coordinate : RoundCylinderSpace → M) (q : UnitTwoSphere) (a : M)
    (p : V)
    (hf : MDifferentiableAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) coordinate
      ((chartAt E₂ q).symm p.1, p.2))
    (ha : coordinate ((chartAt E₂ q).symm p.1, p.2) ∈
      (extChartAt (𝓡 3) a).source) (i l : Fin 3) :
    let phi := fun y : V => coordinate ((chartAt E₂ q).symm y.1, y.2)
    let f := (extChartAt (𝓡 3) a) ∘ phi
    roundCylinderTensorCoefficient (roundCylinderPullback g coordinate)
        (chartAt E₂ q) p i l =
      ((g.pullbackCoefficients (extChartAt (𝓡 3) a).symm (f p)).bilinearComp
        (fderiv ℝ f p) (fderiv ℝ f p))
          (roundCylinderCoordinateBasis i) (roundCylinderCoordinateBasis l) := by
  dsimp only
  have hphi := hf.comp p ((cylinderChart_symm_smooth q p).mdifferentiableAt (by simp))
  have h := metric_chart_pullback_apply g a hphi ha
    (roundCylinderCoordinateBasis i) (roundCylinderCoordinateBasis l)
  have hv := mfderiv_comp_chosen_cylinder_chart q coordinate p hf
    (roundCylinderCoordinateBasis i)
  have hw := mfderiv_comp_chosen_cylinder_chart q coordinate p hf
    (roundCylinderCoordinateBasis l)
  apply Eq.symm
  refine h.trans ?_
  simp only [roundCylinderTensorCoefficient, roundCylinderPullback]
  exact congrArg₂ (fun v1 w1 : E₃ =>
    g.inner (coordinate ((chartAt E₂ q).symm p.1, p.2)) v1 w1) hv hw



theorem metric_jets_bounded_on_compact_time_space
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {a b : ℝ} (hab : a < b) (F : RicciFlow n M (Icc a b))
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {e : EuclideanSpace ℝ (Fin n) → M} (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e U)
    {H : Set (EuclideanSpace ℝ (Fin n))} (hH : IsCompact H) (hHU : H ⊆ U)
    (m : ℕ) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ t ∈ Icc a b, ∀ x ∈ H, ∀ j ≤ m,
      ‖iteratedFDeriv ℝ j (fun y => (F.metric t).pullbackCoefficients e y) x‖ ≤ B := by
  classical
  have hc (j : Fin (m + 1)) : ContinuousOn
      (fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
        iteratedFDeriv ℝ j.val (fun y => (F.metric z.1).pullbackCoefficients e y) z.2)
      (Icc a b ×ˢ H) :=
    (M44.continuousOn_pullback_spatialJet hab F hU he j.val).mono
      (fun _ hz => ⟨hz.1, hHU hz.2⟩)
  choose C hC using fun j : Fin (m + 1) =>
    (isCompact_Icc.prod hH).exists_bound_of_continuousOn (hc j)
  let B := 1 + ∑ j : Fin (m + 1), max 0 (C j)
  have hsum : 0 ≤ ∑ j : Fin (m + 1), max 0 (C j) :=
    Finset.sum_nonneg fun _ _ => le_max_left _ _
  refine ⟨B, by dsimp only [B]; linarith, ?_⟩
  intro t ht x hx j hj
  let i : Fin (m + 1) := ⟨j, Nat.lt_succ_of_le hj⟩
  calc
    _ ≤ C i := hC i (t, x) ⟨ht, hx⟩
    _ ≤ max 0 (C i) := le_max_right _ _
    _ ≤ ∑ k : Fin (m + 1), max 0 (C k) :=
      Finset.single_le_sum (fun _ _ => le_max_left _ _) (Finset.mem_univ i)
    _ ≤ B := by dsimp only [B]; linarith

end PoincareConjecture.Proofs.M47
