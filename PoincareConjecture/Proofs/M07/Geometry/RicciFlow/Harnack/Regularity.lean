import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Curvature.Theory
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.VectorBundle.Hom














set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace Poincare.Geometry.RicciFlow.Harnack

open PoincareConjecture


def restrictFlow
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M] {J K : Set ℝ}
    (F : RicciFlow n M J) (hKJ : K ⊆ J)
    (hK : K.OrdConnected) (hne : K.Nontrivial) : RicciFlow n M K where
  metric := F.metric
  connection := F.connection
  interval := hK
  nontrivial := hne
  smooth := F.smooth.mono (Set.prod_mono hKJ (Subset.refl _))
  equation t ht x v w := (F.equation t (hKJ ht) x v w).mono hKJ

theorem scalarCurvature_contDiffOn_time
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M]
    (hM04 : RicciFlowCurvatureTheory.{u})
    (J : Set ℝ) (F : RicciFlow n M J) (x : M) :
    ContDiffOn ℝ ∞ (fun t ↦ (F.connection t).scalarCurvature x) J := by
  exact ((hM04.scalar_regular n M J F).comp
    (contMDiffOn_id.prodMk contMDiffOn_const)
    (fun t ht ↦ ⟨ht, mem_univ x⟩)).contDiffOn


theorem scalarEvolution_continuousOn_ancient
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M]
    (hM04 : RicciFlowCurvatureTheory.{u})
    (F : RicciFlow n M (Iic 0)) (x : M) :
    ContinuousOn (fun t ↦
      (F.connection t).laplacian (F.connection t).scalarCurvature x +
        2 * (F.connection t).ricciNormSq x) (Iic 0) := by
  have h := (scalarCurvature_contDiffOn_time hM04 (Iic 0) F x).continuousOn_derivWithin
    (uniqueDiffOn_Iic 0) (by simp)
  apply h.congr
  intro t ht
  exact ((hM04.scalar_evolution n M (Iic 0) F t ht x).derivWithin
    (uniqueDiffOn_Iic 0 t ht)).symm

theorem metric_inner_contDiffOn_time
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M] {J : Set ℝ}
    (F : RicciFlow n M J) (x : M) (v w : TangentSpace (𝓡 n) x) :
    ContDiffOn ℝ ∞ (fun t ↦ (F.metric t).inner x v w) J := by
  have h := F.smooth.comp
    (contMDiffOn_id.prodMk (contMDiffOn_const (c := x)))
    (fun t ht ↦ ⟨ht, mem_univ x⟩)
  have heval := h.clm_bundle_apply₂ (F₃ := ℝ) (E₃ := Bundle.Trivial M ℝ)
    (contMDiffOn_const (c := Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) x v))
    (contMDiffOn_const (c := Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) x w))
  intro t ht
  have hpoint := heval t ht
  simp only [Bundle.contMDiffWithinAt_totalSpace] at hpoint
  exact hpoint.2.contDiffWithinAt

set_option backward.isDefEq.respectTransparency false in
theorem scalarCurvature_mvfderiv_continuousOn_time
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M]
    (hM04 : RicciFlowCurvatureTheory.{u})
    (J : Set ℝ) (F : RicciFlow n M J) (x : M)
    (v : TangentSpace (𝓡 n) x) :
    ContinuousOn (fun t ↦ mvfderiv (𝓡 n)
      (fun y ↦ (F.connection t).scalarCurvature y) x v) J := by
  intro t ht
  have hjoint := hM04.scalar_regular n M J F (t, x) ⟨ht, mem_univ x⟩
  have hd := ContMDiffWithinAt.mfderivWithin (m := 0)
    (f := fun t y ↦ (F.connection t).scalarCurvature y) (g := fun _ ↦ x)
    hjoint contMDiffWithinAt_const ht (fun _ _ ↦ mem_univ x)
    (by simp) uniqueMDiffOn_univ
  let v' : EuclideanSpace ℝ (Fin n) := v
  have hv : ContMDiffWithinAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) 0
      (fun _ : ℝ ↦ v') J t := contMDiffWithinAt_const
  have heval := hd.clm_apply hv
  have heq : ∀ s : ℝ, mvfderiv (𝓡 n)
      (fun y ↦ (F.connection s).scalarCurvature y) x v =
      inTangentCoordinates (𝓡 n) (𝓘(ℝ, ℝ)) (fun _ : ℝ ↦ x)
        (fun s ↦ (F.connection s).scalarCurvature x)
        (fun s ↦ mfderivWithin (𝓡 n) (𝓘(ℝ, ℝ))
          (fun y ↦ (F.connection s).scalarCurvature y) univ x) t s v := by
    intro s
    rw [inTangentCoordinates_eq (x₀ := t) (x := s) _ _ _
      (mem_chart_source _ _) (show (F.connection s).scalarCurvature x ∈
        (chartAt ℝ ((F.connection t).scalarCurvature x)).source from mem_univ _)]
    simp only [tangentBundleCore_coordChange_model_space, ContinuousLinearMap.id_comp,
      ContinuousLinearMap.comp_apply]
    rw [(tangentBundleCore (𝓡 n) M).coordChange_self _ _ (mem_achart_source _ _)]
    rw [mfderivWithin_univ]
    rfl
  exact heval.continuousWithinAt.congr (fun s _ ↦ heq s) (heq t)


theorem ricci_continuousOn_ancient
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M]
    (F : RicciFlow n M (Iic 0)) (x : M) (v w : TangentSpace (𝓡 n) x) :
    ContinuousOn (fun t ↦ (F.connection t).ricci x v w) (Iic 0) := by
  have h := (metric_inner_contDiffOn_time F x v w).continuousOn_derivWithin
    (uniqueDiffOn_Iic 0) (by simp)
  apply (h.div_const (-2)).congr
  intro t ht
  dsimp only
  rw [(F.equation t ht x v w).derivWithin (uniqueDiffOn_Iic 0 t ht)]
  ring

theorem scalarCurvature_continuousOn_time
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M]
    (hM04 : RicciFlowCurvatureTheory.{u})
    (J : Set ℝ) (F : RicciFlow n M J) (x : M) :
    ContinuousOn (fun t ↦ (F.connection t).scalarCurvature x) J := by
  have hjoint : ContinuousOn
      (fun p : ℝ × M ↦ (F.connection p.1).scalarCurvature p.2)
      (J ×ˢ (Set.univ : Set M)) :=
    (hM04.scalar_regular n M J F).continuousOn
  have hpath : ContinuousOn (fun t : ℝ ↦ (t, x)) J :=
    continuousOn_id.prodMk continuousOn_const
  have hmap : MapsTo (fun t : ℝ ↦ (t, x)) J (J ×ˢ (Set.univ : Set M)) := by
    intro t ht
    exact ⟨ht, mem_univ x⟩
  change ContinuousOn
    ((fun p : ℝ × M ↦ (F.connection p.1).scalarCurvature p.2) ∘
      (fun t : ℝ ↦ (t, x))) J
  exact hjoint.comp hpath hmap

theorem scalarCurvature_continuousOn_path
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M]
    (hM04 : RicciFlowCurvatureTheory.{u})
    (J : Set ℝ) (F : RicciFlow n M J) (γ : ℝ → M)
    {a b : ℝ} (hab : Set.Icc a b ⊆ J)
    (hγ : ContinuousOn γ (Set.Icc a b)) :
    ContinuousOn
      (fun t ↦ (F.connection t).scalarCurvature (γ t)) (Set.Icc a b) := by
  have hjoint : ContinuousOn
      (fun p : ℝ × M ↦ (F.connection p.1).scalarCurvature p.2)
      (J ×ˢ (Set.univ : Set M)) :=
    (hM04.scalar_regular n M J F).continuousOn
  have hpath : ContinuousOn (fun t : ℝ ↦ (t, γ t)) (Set.Icc a b) :=
    continuousOn_id.prodMk hγ
  have hmap : MapsTo (fun t : ℝ ↦ (t, γ t)) (Set.Icc a b)
      (J ×ˢ (Set.univ : Set M)) := by
    intro t ht
    exact ⟨hab ht, mem_univ (γ t)⟩
  change ContinuousOn
    ((fun p : ℝ × M ↦ (F.connection p.1).scalarCurvature p.2) ∘
      (fun t : ℝ ↦ (t, γ t))) (Set.Icc a b)
  exact hjoint.comp hpath hmap

end Poincare.Geometry.RicciFlow.Harnack
