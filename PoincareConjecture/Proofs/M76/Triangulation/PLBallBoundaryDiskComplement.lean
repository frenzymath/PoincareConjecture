import PoincareConjecture.Proofs.M76.Triangulation.ConvexSphereDiskComplement
import PoincareConjecture.Proofs.M76.Mathlib.ConvexFrontierSubcomplex

set_option autoImplicit false

open Set Geometry

namespace Set

variable {V X : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]

theorem IsFinitePLBallPair.boundary_disk_complement
    {B S d q : Set X} (hB : IsFinitePLBallPair V B S)
    (hdim : Module.finrank ℝ V = 3) (hd : IsFinitePLBallPair (ℝ × ℝ) d q)
    (hdS : d ⊆ S) (hout : (S \ d).Nonempty) :
    IsFinitePLBallPair (ℝ × ℝ) (S \ (d \ q)) q := by
  obtain ⟨hSB, C, hC, hcv, hne, e, he, heb⟩ := hB
  have hecopy := he
  obtain ⟨f, hf, heval⟩ := hecopy
  obtain ⟨g, hg, hgval⟩ := he.symm
  have hgf : LeftInvOn g f B := by
    intro x hx
    rw [← heval ⟨x, hx⟩, ← hgval, e.symm_apply_apply]
  have hfg : LeftInvOn f g C := by
    intro y hy
    rw [← hgval ⟨y, hy⟩, ← heval, e.apply_symm_apply]
  have hfmap : MapsTo f B C := by
    intro x hx
    rw [← heval ⟨x, hx⟩]
    exact (e ⟨x, hx⟩).property
  have hfS : f '' S = frontier C := by
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      rw [← heval ⟨x, hSB hx⟩]
      exact (heb ⟨x, hSB hx⟩).mp hx
    · intro y hy
      let x := e.symm ⟨y, hC.isClosed.frontier_subset hy⟩
      have hex : (e x : V) = y := congrArg Subtype.val (e.apply_symm_apply _)
      have hxS : (x : X) ∈ S := (heb x).mpr (hex.symm ▸ hy)
      exact ⟨x, hxS, (heval x).symm.trans hex⟩
  have hback (U : Set X) (hU : U ⊆ B) : g '' (f '' U) = U := by
    apply Subset.antisymm
    · rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      rwa [hgf (hU hx)]
    · intro x hx
      exact ⟨f x, mem_image_of_mem f hx, hgf (hU hx)⟩
  have hgS : g '' frontier C = S := by rw [← hfS, hback S hSB]
  have hdB : d ⊆ B := hdS.trans hSB
  have hqB : q ⊆ B := hd.1.trans hdB
  have hd' := hd.image_of_subset hf hdB hgf.injOn
  have hdf : f '' d ⊆ frontier C := (image_mono hdS).trans hfS.subset
  obtain ⟨p, hpS, hpd⟩ := hout
  have hout' : (frontier C \ f '' d).Nonempty := by
    refine ⟨f p, hfS.subset (mem_image_of_mem f hpS), ?_⟩
    rintro ⟨x, hx, hxp⟩
    exact hpd (hgf.injOn (hdB hx) (hSB hpS) hxp ▸ hx)
  have hgcopy := hg
  obtain ⟨K, hK, hKC, _⟩ := hgcopy
  have hcomp := (K.frontierSubcomplex C).isFinitePLBallPair_convex_sphere_disk_complement
    (K.frontierSubcomplex_finite C hK) hC hcv hne
    (K.frontierSubcomplex_space hC.isClosed hcv hne hKC) hdim hd' hdf hout'
  have hcompC : frontier C \ (f '' d \ f '' q) ⊆ C :=
    sdiff_subset.trans hC.isClosed.frontier_subset
  have hresult := hcomp.image_of_subset hg hcompC hfg.injOn
  have hremove : g '' (f '' d \ f '' q) = d \ q := by
    rw [(hfg.injOn.mono (hdf.trans hC.isClosed.frontier_subset)).image_sdiff_subset
      (image_mono hd.1), hback d hdB, hback q hqB]
  have hcarrier : g '' (frontier C \ (f '' d \ f '' q)) = S \ (d \ q) := by
    rw [(hfg.injOn.mono hC.isClosed.frontier_subset).image_sdiff_subset
      (sdiff_subset.trans hdf), hgS, hremove]
  rwa [hcarrier, hback q hqB] at hresult

end Set
