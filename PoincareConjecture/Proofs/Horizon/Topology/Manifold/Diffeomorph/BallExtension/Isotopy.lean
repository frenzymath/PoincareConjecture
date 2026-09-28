import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Models
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.BallExtension.ParametricInverse
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.SphereIsotopy.Normalization
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.SphereIsotopy.CompactSupport
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.SphereIsotopy.Plane












set_option autoImplicit false
open scoped Manifold ContDiff

namespace Poincare.Manifold

open Set



theorem exists_sphere_diffeomorph_isotopy
    (d : Diffeomorph (𝓡 2) (𝓡 2)
      PoincareConjecture.UnitTwoSphere PoincareConjecture.UnitTwoSphere ∞) :
    ∃ A : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3),
      ∃ f : ℝ → Diffeomorph (𝓡 2) (𝓡 2)
        PoincareConjecture.UnitTwoSphere PoincareConjecture.UnitTwoSphere ∞,
        ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 2) ∞
          (fun z : ℝ × PoincareConjecture.UnitTwoSphere => f z.1 z.2) ∧
        ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 2) ∞
          (fun z : ℝ × PoincareConjecture.UnitTwoSphere => (f z.1).symm z.2) ∧
        (∀ p : PoincareConjecture.UnitTwoSphere,
          (f 0 p : EuclideanSpace ℝ (Fin 3)) = A p) ∧
        (∀ p : PoincareConjecture.UnitTwoSphere, f 1 p = d p) := by
  classical
  let p : PoincareConjecture.UnitTwoSphere :=
    ⟨EuclideanSpace.single 0 1, by simp [Metric.mem_sphere, dist_zero_right]⟩
  obtain ⟨A, a, ha, Φ, hΦ0, hΦs, U, hU, hpU, hΦ1⟩ :=
    SphereIsotopy.exists_orthogonal_germ d p
  let b := (d.trans (Φ 1)).trans a.symm
  have hbU : EqOn b id U := by
    intro q hq
    change a.symm (Φ 1 (d q)) = q
    rw [hΦ1 q hq, a.symm_apply_apply]
  have hbp : b p = p := hbU hpU
  obtain ⟨g, hg, K, hK, hgfix⟩ := SphereIsotopy.exists_plane_diffeomorph b p hU hpU hbU
  obtain ⟨F, hFs, hF0, hF1, S, hS, hFfix⟩ :=
    SphereIsotopy.exists_compactly_supported_plane_isotopy g hK hgfix
  obtain ⟨H, hHs, _, hH0, hH1, _⟩ :=
    SphereIsotopy.exists_sphere_isotopy_of_plane_isotopy b p hbp F hF0 hFs hS hFfix
      (fun x => (hF1 x).trans (hg x))
  let f : ℝ → Diffeomorph (𝓡 2) (𝓡 2)
      PoincareConjecture.UnitTwoSphere PoincareConjecture.UnitTwoSphere ∞ :=
    fun t => ((H t).trans a).trans (Φ t).symm
  have hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 2) ∞
      (fun z : ℝ × PoincareConjecture.UnitTwoSphere => f z.1 z.2) :=
    (contMDiff_diffeomorph_family_symm Φ hΦs).comp
      (contMDiff_fst.prodMk (a.contMDiff.comp hHs))
  refine ⟨A, f, hf, contMDiff_diffeomorph_family_symm f hf, ?_, ?_⟩
  · intro q
    have hz : (Φ 0).symm (a (H 0 q)) = a q := by
      rw [hH0]
      apply (Φ 0).injective
      change Φ 0 ((Φ 0).symm (a q)) = Φ 0 (a q)
      rw [(Φ 0).apply_symm_apply, hΦ0]
    exact (congrArg Subtype.val hz).trans (ha q)
  · intro q
    change (Φ 1).symm (a (H 1 q)) = d q
    rw [hH1]
    change (Φ 1).symm (a (a.symm (Φ 1 (d q)))) = d q
    rw [a.apply_symm_apply, (Φ 1).symm_apply_apply]

end Poincare.Manifold
