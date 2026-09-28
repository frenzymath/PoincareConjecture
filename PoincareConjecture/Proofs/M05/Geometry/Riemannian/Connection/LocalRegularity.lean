import PoincareConjecture.Proofs.M05.Geometry.Riemannian.Connection.MetricDuality
import PoincareConjecture.Proofs.M05.Geometry.Riemannian.Curvature.SecondBianchi

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology
open Bundle Filter Set

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

lemma exists_open_contMDiffOn_extend (x : M) :
    ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ ∀ v : TangentSpace (𝓡 n) x,
      ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
        (T% (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v)) U := by
  let E := EuclideanSpace ℝ (Fin n)
  let V := TangentSpace (𝓡 n) (M := M)
  let e := trivializationAt E V x
  refine ⟨e.baseSet, e.open_baseSet,
    FiberBundle.mem_baseSet_trivializationAt E V x, ?_⟩
  intro v
  suffices h : ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞
      (fun y => (e ⟨y, FiberBundle.extend E v y⟩).2) e.baseSet by
    intro y hy
    rw [e.contMDiffWithinAt_section _ hy]
    exact h y hy
  let w : E := (e ⟨x, v⟩).2
  have h : ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ (fun _ : M => w) e.baseSet :=
    contMDiffOn_const
  exact h.congr fun y hy => by
    change (e ⟨y, e.symm y w⟩).2 = w
    simpa using congrArg Prod.snd (e.apply_mk_symm hy w)

namespace LeviCivitaData

lemma contMDiffAt_covariantDerivativeOnFields (D : LeviCivitaData g)
    {X Y : (x : M) → TangentSpace (𝓡 n) x} {x : M}
    (hX : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% X) x)
    (hY : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) x) :
    ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (T% (D.covariantDerivativeOnFields X Y)) x := by
  apply g.contMDiffAt_of_metricDual
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, ?_⟩
  apply contMDiffAt_clm_of_apply
  intro v
  let E := EuclideanSpace ℝ (Fin n)
  let V := TangentSpace (𝓡 n) (M := M)
  let e := trivializationAt E V x
  have hv : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, E)) ∞
      (fun y => TotalSpace.mk' E y v) x := by
    rw [contMDiffAt_totalSpace]
    exact ⟨contMDiffAt_id, by simpa using contMDiffAt_const (c := v)⟩
  have hZ := (e.contMDiffAt_symmL (IB := 𝓡 n) (n := ∞)
    (FiberBundle.mem_baseSet_trivializationAt E V x)).clm_bundle_apply hv
  have h := D.contMDiffAt_inner_covariantDerivativeOnFields hX hY hZ
  change ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞
    (fun y => (ContinuousLinearMap.inCoordinates E V ℝ (fun _ : M => ℝ)
      x y x y (g.inner y (D.covariantDerivativeOnFields X Y y))) v) x
  have he : trivializationAt ℝ (fun _ : M => ℝ) x = Bundle.Trivial.trivialization M ℝ := rfl
  simpa only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply,
    he, Bundle.Trivial.continuousLinearMapAt_trivialization,
    ContinuousLinearMap.id_apply] using h

end PoincareConjecture.LeviCivitaData
