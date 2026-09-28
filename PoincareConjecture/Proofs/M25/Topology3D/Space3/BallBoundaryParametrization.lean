import PoincareConjecture.Proofs.M25.Topology3D.Space3.CollarCoordinates
import PoincareConjecture.Proofs.M25.Topology3D.Space3.SharedBoundaryTangency
import PoincareConjecture.Proofs.M25.Topology3D.Space3.SphereSmoothRestriction











set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold

namespace PoincareConjecture.M25.Topology3D



theorem exists_ball_boundary_parametrization (ψ : UnitTwoSphere × ℝ → E3)
    (hψ : IsCollarEmbedding ψ) (B : BallNeighborhoodChart E3 E3)
    (hboundary : B.boundary = ψ '' (univ ×ˢ {0})) :
    ∃ g : Diffeomorph (𝓡 2) (𝓡 2) UnitTwoSphere UnitTwoSphere ∞,
      ∀ q, B.chart (g q : E3) = ψ (q, 0) := by
  let : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp [E3]⟩
  obtain ⟨e, he, hsource, _, hi⟩ := exists_collar_chart ψ hψ
  have hcentral (q : UnitTwoSphere) : (q, (0 : ℝ)) ∈ e.source := by
    rw [hsource]
    exact ⟨mem_univ _, by norm_num⟩
  have hqB (q : UnitTwoSphere) : ψ (q, 0) ∈ B.boundary := by
    rw [hboundary]
    exact ⟨(q, 0), ⟨mem_univ _, rfl⟩, rfl⟩
  have hqtarget (q : UnitTwoSphere) : ψ (q, 0) ∈ B.chart.target := by
    obtain ⟨x, hx, hxq⟩ := hqB q
    rw [← hxq]
    exact B.chart.map_source (B.closedBall_subset_source (sphere_subset_closedBall hx))
  let g : UnitTwoSphere → UnitTwoSphere := fun q =>
    ⟨B.chart.symm (ψ (q, 0)),
      mem_sphere_zero_iff_norm.mpr (B.norm_symm_of_mem_boundary (hqB q))⟩
  let f : UnitTwoSphere → UnitTwoSphere := fun x => (e.symm (B.chart (x : E3))).1
  have hgmap (q : UnitTwoSphere) : B.chart (g q : E3) = ψ (q, 0) :=
    B.chart.right_inv (hqtarget q)
  have hBcentral (x : UnitTwoSphere) :
      e.symm (B.chart (x : E3)) = (f x, 0) := by
    have hxb : B.chart (x : E3) ∈ B.boundary := ⟨x, x.2, rfl⟩
    rw [hboundary] at hxb
    obtain ⟨⟨q, s⟩, ⟨_, hs⟩, hxq⟩ := hxb
    have hs0 : s = 0 := hs
    subst s
    have hinv : e.symm (B.chart (x : E3)) = (q, 0) := by
      rw [← hxq, ← he]
      exact e.left_inv (hcentral q)
    have hzero : (e.symm (B.chart (x : E3))).2 = 0 := by rw [hinv]
    exact Prod.ext rfl hzero
  have hBtarget (x : UnitTwoSphere) : B.chart (x : E3) ∈ e.target := by
    have hxb : B.chart (x : E3) ∈ B.boundary := ⟨x, x.2, rfl⟩
    rw [hboundary] at hxb
    obtain ⟨⟨q, s⟩, ⟨_, hs⟩, hxq⟩ := hxb
    have hs0 : s = 0 := hs
    subst s
    rw [← hxq, ← he]
    exact e.map_source (hcentral q)
  have hfg (q : UnitTwoSphere) : f (g q) = q := by
    change (e.symm (B.chart (g q : E3))).1 = q
    rw [hgmap q, ← he, e.left_inv (hcentral q)]
  have hgf (x : UnitTwoSphere) : g (f x) = x := by
    apply Subtype.ext
    change B.chart.symm (ψ (f x, 0)) = (x : E3)
    rw [← he, ← hBcentral x, e.right_inv (hBtarget x)]
    exact B.chart.left_inv (B.closedBall_subset_source (sphere_subset_closedBall x.2))
  have hψzero : ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞ (fun q => ψ (q, 0)) := by
    apply contMDiffOn_univ.mp
    exact hψ.1.comp (contMDiff_id.prodMk contMDiff_const).contMDiffOn
      (fun _ _ => ⟨mem_univ _, by norm_num⟩)
  have hgcoe : ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞ (fun q => (g q : E3)) := by
    apply contMDiffOn_univ.mp
    exact B.smooth_symm.contMDiffOn.comp hψzero.contMDiffOn (fun q _ => hqtarget q)
  have hgsmooth : ContMDiff (𝓡 2) (𝓡 2) ∞ g :=
    hgcoe.codRestrict_sphere (fun q => (g q).2)
  have hBsmooth : ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞ (fun x : UnitTwoSphere => B.chart (x : E3)) := by
    apply contMDiffOn_univ.mp
    exact B.smooth.contMDiffOn.comp contMDiff_coe_sphere.contMDiffOn
      (fun x _ => B.closedBall_subset_source (sphere_subset_closedBall x.2))
  have hfsmooth : ContMDiff (𝓡 2) (𝓡 2) ∞ f := by
    apply contMDiffOn_univ.mp
    exact contMDiff_fst.comp_contMDiffOn
      (hi.comp hBsmooth.contMDiffOn (fun x _ => hBtarget x))
  exact ⟨{ toEquiv := { toFun := g, invFun := f, left_inv := hfg, right_inv := hgf }
           contMDiff_toFun := hgsmooth
           contMDiff_invFun := hfsmooth }, hgmap⟩

end PoincareConjecture.M25.Topology3D
