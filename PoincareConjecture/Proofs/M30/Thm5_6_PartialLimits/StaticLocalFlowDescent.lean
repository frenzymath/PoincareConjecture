import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Metric.Gluing.Descent
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Connection.Construction
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.MetricFamily.Descent
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Limit.Descent
import PoincareConjecture.Proofs.M12.Geometry.Riemannian.Curvature.LocalIsometryInvariants

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe uI uU uM

namespace PoincareConjecture.M30

theorem exists_flow_of_common_metric_chart_limits
    {n : ℕ} {ι : Type uI} [Nonempty ι] {U : ι → Type uU} {M : Type uM}
    [∀ i, TopologicalSpace (U i)] [TopologicalSpace M]
    [∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (U i)]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [∀ i, IsManifold (𝓡 n) ∞ (U i)] [IsManifold (𝓡 n) ∞ M]
    {J : Set ℝ} (t₀ : ℝ) (ht₀ : t₀ ∈ J)
    (g₀ : RiemannianMetric n M) (h : ℕ → ℝ → RiemannianMetric n M)
    (Fchart : ∀ i, RicciFlow n (U i) J)
    (q : ∀ i, U i → M)
    (hq : ∀ i, IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ (q i))
    (hcover : ∀ y, ∃ i x, q i x = y)
    (hlimit : ∀ t ∈ J, ∀ i (x : U i) (v w : TangentSpace (𝓡 n) x),
      Tendsto (fun k => (h k t).inner (q i x)
        (mfderiv (𝓡 n) (𝓡 n) (q i) x v)
        (mfderiv (𝓡 n) (𝓡 n) (q i) x w)) atTop
          (𝓝 (((Fchart i).metric t).inner x v w)))
    (hterminal : ∀ i (x : U i) (v w : TangentSpace (𝓡 n) x),
      ((Fchart i).metric t₀).inner x v w = g₀.inner (q i x)
        (mfderiv (𝓡 n) (𝓡 n) (q i) x v)
        (mfderiv (𝓡 n) (𝓡 n) (q i) x w))
    (hoperator : ∀ i t, t ∈ J → ∀ x : U i,
      ((Fchart i).connection t).NonnegativeCurvatureOperator x) :
    ∃ F : RicciFlow n M J, F.metric t₀ = g₀ ∧
      (∀ t ∈ J, ∀ i (x : U i) (v w : TangentSpace (𝓡 n) x),
        ((Fchart i).metric t).inner x v w = (F.metric t).inner (q i x)
          (mfderiv (𝓡 n) (𝓡 n) (q i) x v)
          (mfderiv (𝓡 n) (𝓡 n) (q i) x w)) ∧
      ∀ t ∈ J, ∀ x : M, (F.connection t).NonnegativeCurvatureOperator x := by
  classical
  have hinv (t : ℝ) (ht : t ∈ J) (i j : ι) (x : U i) (y : U j)
      (hxy : q i x = q j y)
      (v w : TangentSpace (𝓡 n) x) (v' w' : TangentSpace (𝓡 n) y)
      (hv : mfderiv (𝓡 n) (𝓡 n) (q i) x v = mfderiv (𝓡 n) (𝓡 n) (q j) y v')
      (hw : mfderiv (𝓡 n) (𝓡 n) (q i) x w = mfderiv (𝓡 n) (𝓡 n) (q j) y w') :
      ((Fchart i).metric t).inner x v w = ((Fchart j).metric t).inner y v' w' := by
    have hseq : (fun k => (h k t).inner (q i x)
          (mfderiv (𝓡 n) (𝓡 n) (q i) x v)
          (mfderiv (𝓡 n) (𝓡 n) (q i) x w)) =
        (fun k => (h k t).inner (q j y)
          (mfderiv (𝓡 n) (𝓡 n) (q j) y v')
          (mfderiv (𝓡 n) (𝓡 n) (q j) y w')) := by
      funext k
      let B : M → EuclideanSpace ℝ (Fin n) →L[ℝ]
          EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ := fun z => (h k t).inner z
      change B (q i x) _ _ = B (q j y) _ _
      rw [hv, hw, hxy]
    have hi := hlimit t ht i x v w
    rw [hseq] at hi
    exact tendsto_nhds_unique hi (hlimit t ht j y v' w')
  let selectedTime (t : ℝ) := if t ∈ J then t else t₀
  have hselected (t : ℝ) : selectedTime t ∈ J := by
    dsimp [selectedTime]
    split_ifs with ht
    · exact ht
    · exact ht₀
  have hselected_eq (t : ℝ) (ht : t ∈ J) : selectedTime t = t :=
    if_pos ht
  have hex (t : ℝ) := Poincare.Gluing.exists_unique_metric_of_covering_local_diffeomorphisms
    (fun i => (Fchart i).metric (selectedTime t)) q hq hcover
    (hinv (selectedTime t) (hselected t))
  let g (t : ℝ) := Classical.choose (hex t)
  have hpres (t : ℝ) (ht : t ∈ J) (i : ι) (x : U i)
      (v w : TangentSpace (𝓡 n) x) :
      ((Fchart i).metric t).inner x v w = (g t).inner (q i x)
        (mfderiv (𝓡 n) (𝓡 n) (q i) x v)
        (mfderiv (𝓡 n) (𝓡 n) (q i) x w) := by
    have hp := (Classical.choose_spec (hex t)).1 i x v w
    change ((Fchart i).metric (selectedTime t)).inner x v w = (g t).inner (q i x)
      (mfderiv (𝓡 n) (𝓡 n) (q i) x v)
      (mfderiv (𝓡 n) (𝓡 n) (q i) x w) at hp
    rwa [hselected_eq t ht] at hp
  have hzero : g t₀ = g₀ := by
    symm
    apply (Classical.choose_spec (hex t₀)).2 g₀
    intro i x v w
    simpa only [hselected_eq t₀ ht₀] using hterminal i x v w
  have hsmooth : RiemannianMetric.IsSmoothFamilyOn g J :=
    Poincare.Gluing.isSmoothFamilyOn_of_local_diffeomorphisms
      (fun i => (Fchart i).metric) g (fun i => (Fchart i).smooth) q hq hcover hpres
  obtain ⟨F, hF⟩ := RicciFlow.exists_of_covering_local_diffeomorphisms
    Fchart g hsmooth t₀ (g t₀).leviCivitaData q hq hcover hpres
  have hpresF : ∀ t ∈ J, ∀ i (x : U i) (v w : TangentSpace (𝓡 n) x),
      ((Fchart i).metric t).inner x v w = (F.metric t).inner (q i x)
        (mfderiv (𝓡 n) (𝓡 n) (q i) x v)
        (mfderiv (𝓡 n) (𝓡 n) (q i) x w) := by
    simpa only [hF] using hpres
  refine ⟨F, by simpa only [hF] using hzero, hpresF, ?_⟩
  intro t ht z
  obtain ⟨i, x, rfl⟩ := hcover z
  exact (((Fchart i).connection t).nonnegativeCurvatureOperator_iff_of_local_isometry
    (F.connection t) isOpen_univ (hq i).contMDiff.contMDiffOn
    (fun y _ v w => hpresF t ht i y v w) (mem_univ x)).mp (hoperator i t ht x)

end PoincareConjecture.M30
