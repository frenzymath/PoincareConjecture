import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Curvature.LocalIsometry
import PoincareConjecture.Definitions.Ch04.Pinching

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.Proofs.M46

variable {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
  [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ N]
  {g : RiemannianMetric 3 M} {h : RiemannianMetric 3 N}

theorem sectional_positive_iff_of_local_isometry
    (D : LeviCivitaData g) (D' : LeviCivitaData h)
    {f : M → N} {U : Set M} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U)
    (hmetric : ∀ y ∈ U, ∀ u v : TangentSpace (𝓡 3) y,
      g.inner y u v = h.inner (f y) (mfderiv (𝓡 3) (𝓡 3) f y u)
        (mfderiv (𝓡 3) (𝓡 3) f y v))
    {x : M} (hx : x ∈ U) :
    (∀ u v : TangentSpace (𝓡 3) x,
      LeviCivitaData.IsOrthonormalPair g x u v →
        0 < D.sectionalCurvature x u v) ↔
    (∀ u v : TangentSpace (𝓡 3) (f x),
      LeviCivitaData.IsOrthonormalPair h (f x) u v →
        0 < D'.sectionalCurvature (f x) u v) := by
  have hcurv (u v : TangentSpace (𝓡 3) x) :
      D.sectionalCurvature x u v = D'.sectionalCurvature (f x)
        (mfderiv (𝓡 3) (𝓡 3) f x u) (mfderiv (𝓡 3) (𝓡 3) f x v) := by
    unfold LeviCivitaData.sectionalCurvature
    rw [D.curvatureTensor_eq_of_local_isometry D' hU hf hmetric hx,
      hmetric x hx u u, hmetric x hx v v, hmetric x hx u v]
  have hpair (u v : TangentSpace (𝓡 3) x) :
      LeviCivitaData.IsOrthonormalPair g x u v ↔
      LeviCivitaData.IsOrthonormalPair h (f x)
        (mfderiv (𝓡 3) (𝓡 3) f x u) (mfderiv (𝓡 3) (𝓡 3) f x v) := by
    unfold LeviCivitaData.IsOrthonormalPair
    rw [hmetric x hx u u, hmetric x hx v v, hmetric x hx u v]
  constructor
  · intro hpos u v huv
    have hsurj := (g.mfderiv_bijective_of_pullback_eq h x
      (fun a b => (hmetric x hx a b).symm)).2
    obtain ⟨a, rfl⟩ := hsurj u
    obtain ⟨b, rfl⟩ := hsurj v
    rw [← hcurv]
    exact hpos a b ((hpair a b).mpr huv)
  · intro hpos u v huv
    rw [hcurv]
    exact hpos _ _ ((hpair u v).mp huv)

theorem sectional_positive_iff_connection
    (D D' : LeviCivitaData g) (x : M) :
    (∀ u v : TangentSpace (𝓡 3) x,
      LeviCivitaData.IsOrthonormalPair g x u v →
        0 < D.sectionalCurvature x u v) ↔
    (∀ u v : TangentSpace (𝓡 3) x,
      LeviCivitaData.IsOrthonormalPair g x u v →
        0 < D'.sectionalCurvature x u v) := by
  simpa only [id_eq] using sectional_positive_iff_of_local_isometry D D'
    (f := id) isOpen_univ contMDiff_id.contMDiffOn
    (fun y _ u v => by rw [mfderiv_id]; rfl)
    (mem_univ x)

theorem component_positive_iff_of_diffeomorph
    (D : LeviCivitaData g) (D' : LeviCivitaData h)
    (e : Diffeomorph (𝓡 3) (𝓡 3) M N ∞)
    (hmetric : ∀ y, ∀ u v : TangentSpace (𝓡 3) y,
      g.inner y u v = h.inner (e y) (mfderiv (𝓡 3) (𝓡 3) e y u)
        (mfderiv (𝓡 3) (𝓡 3) e y v)) (x : M) :
    (∀ y ∈ connectedComponent x, ∀ u v : TangentSpace (𝓡 3) y,
      LeviCivitaData.IsOrthonormalPair g y u v →
        0 < D.sectionalCurvature y u v) ↔
    (∀ y ∈ connectedComponent (e x), ∀ u v : TangentSpace (𝓡 3) y,
      LeviCivitaData.IsOrthonormalPair h y u v →
        0 < D'.sectionalCurvature y u v) := by
  have hpoint (y : M) := sectional_positive_iff_of_local_isometry D D'
    isOpen_univ e.contMDiff.contMDiffOn (fun z _ => hmetric z) (mem_univ y)
  constructor
  · intro hpos y hy
    have hpre : e.symm y ∈ connectedComponent x := by
      simpa only [e.symm_apply_apply] using
        e.symm.continuous.image_connectedComponent_subset (e x) (mem_image_of_mem e.symm hy)
    have h := (hpoint (e.symm y)).mp (hpos _ hpre)
    exact e.apply_symm_apply y ▸ h
  · intro hpos y hy
    exact (hpoint y).mpr (hpos _
      (e.continuous.image_connectedComponent_subset x (mem_image_of_mem e hy)))

end PoincareConjecture.Proofs.M46
