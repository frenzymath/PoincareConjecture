import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.SphereCircle.CollarMatching.Radial

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.CircleCollar

private abbrev S2 := sphere (0 : EuclideanSpace Real (Fin 3)) 1
local notation "Iprod" => ModelWithCorners.prod (𝓡 1) 𝓘(Real, Real)
private instance : Fact (Module.finrank Real Plane = 1 + 1) := ⟨by simp⟩
private instance : Fact (Module.finrank Real (EuclideanSpace Real (Fin 3)) = 2 + 1) := ⟨by simp⟩

theorem exists_boundary_reparametrization
    (e : OpenPartialHomeomorph Plane S2)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target)
    (hsource : closedBall 0 1 ⊆ e.source)
    {ε : Real} (hε : 0 < ε) (T : OpenPartialHomeomorph (Circle × Real) S2)
    (hT : ContMDiffOn Iprod (𝓡 2) ∞ T T.source)
    (hTi : ContMDiffOn (𝓡 2) Iprod ∞ T.symm T.target)
    (hTsource : T.source = univ ×ˢ Ioo (-ε) ε)
    (hcenter : range (fun p : Circle => T (p, 0)) = e '' sphere (0 : Plane) 1) :
    ∃ q : Diffeomorph (𝓡 1) (𝓡 1) Circle Circle ∞,
      ∀ p : Circle, T (q p, 0) = e p := by
  have hpS (p : Circle) : (p : Plane) ∈ e.source := hsource (sphere_subset_closedBall p.property)
  have hT0 (p : Circle) : (p, (0 : Real)) ∈ T.source := by
    rw [hTsource]
    exact ⟨mem_univ _, by constructor <;> linarith⟩
  have hepT (p : Circle) : e p ∈ T.target := by
    obtain ⟨q, hq⟩ := hcenter.symm ▸ (mem_image_of_mem e p.property)
    rw [← hq]
    exact T.map_source (hT0 q)
  have hTep (p : Circle) : (T.symm (e p)).2 = 0 := by
    obtain ⟨q, hq⟩ := hcenter.symm ▸ (mem_image_of_mem e p.property)
    rw [← hq, T.left_inv (hT0 q)]
  have hT0e (p : Circle) : T (p, 0) ∈ e.target := by
    obtain ⟨x, hx, hxe⟩ := hcenter ▸ mem_range_self p
    rw [← hxe]
    exact e.map_source (hsource (sphere_subset_closedBall hx))
  have hInvSphere (p : Circle) : e.symm (T (p, 0)) ∈ sphere (0 : Plane) 1 := by
    obtain ⟨x, hx, hxe⟩ := hcenter ▸ mem_range_self p
    rw [← hxe, e.left_inv (hsource (sphere_subset_closedBall hx))]
    exact hx
  let Q : Circle -> Circle := fun p => (T.symm (e p)).1
  let P : Circle -> Circle := fun p => ⟨e.symm (T (p, 0)), hInvSphere p⟩
  have hQ (p : Circle) : T (Q p, 0) = e p := by
    have hpair : (Q p, (0 : Real)) = T.symm (e p) := Prod.ext rfl (hTep p).symm
    rw [hpair, T.right_inv (hepT p)]
  have hP (p : Circle) : e (P p) = T (p, 0) := e.right_inv (hT0e p)
  have hPQ (p : Circle) : P (Q p) = p := by
    apply Subtype.ext
    change e.symm (T (Q p, 0)) = (p : Plane)
    rw [hQ, e.left_inv (hpS p)]
  have hQP (p : Circle) : Q (P p) = p := by
    change (T.symm (e (P p))).1 = p
    rw [hP, T.left_inv (hT0 p)]
  have hQs : ContMDiff (𝓡 1) (𝓡 1) ∞ Q := by
    intro p
    exact contMDiff_fst.contMDiffAt.comp p
      ((hTi.contMDiffAt (T.open_target.mem_nhds (hepT p))).comp p
        ((he.contMDiffAt (e.open_source.mem_nhds (hpS p))).comp p (contMDiff_coe_sphere p)))
  have hPs : ContMDiff (𝓡 1) (𝓡 1) ∞ P := by
    have hs : ContMDiff (𝓡 1) (𝓡 2) ∞ (fun p : Circle => e.symm (T (p, 0))) := by
      intro p
      exact (hei.contMDiffAt (e.open_target.mem_nhds (hT0e p))).comp p
        ((hT.contMDiffAt (T.open_source.mem_nhds (hT0 p))).comp p
          ((contMDiff_id.prodMk contMDiff_const) p))
    exact hs.codRestrict_sphere hInvSphere
  exact ⟨{ toFun := Q
           invFun := P
           left_inv := hPQ
           right_inv := hQP
           contMDiff_toFun := hQs
           contMDiff_invFun := hPs }, hQ⟩

end Poincare.Manifold.Schoenflies.CircleCollar
