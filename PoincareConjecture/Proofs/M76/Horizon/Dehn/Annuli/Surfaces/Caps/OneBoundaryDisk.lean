import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surfaces.Caps.OneBoundarySphere
import PoincareConjecture.Proofs.M76.Triangulation.PLBallBoundaryDiskComplement
import PoincareConjecture.Proofs.M76.PrimeReduction.BallModelCoordinates
import PoincareConjecture.Proofs.M76.Horizon.Polyhedral.Simplicial.RefinementEdgeStars









set_option autoImplicit false
open Set Metric Geometry TriangularRoofModel

namespace PoincareConjecture.M76.Dehn.Annuli

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem finitePL_sphere_disk_complement {S D Q : Set E}
    (H : S ≃ₜ frontier (halfBall 1)) (hH : H.IsFinitePL)
    (hD : IsFinitePLBallPair (ℝ × ℝ) D Q) (hDS : D ⊆ S)
    (hout : (S \ D).Nonempty) :
    IsFinitePLBallPair (ℝ × ℝ) (S \ (D \ Q)) Q := by
  obtain ⟨f, hf, hfH⟩ := hH
  obtain ⟨g, hg, hgH⟩ := (show H.IsFinitePL from ⟨f, hf, hfH⟩).symm
  have hgf (x : E) (hx : x ∈ S) : g (f x) = x := by
    rw [← hfH ⟨x, hx⟩, ← hgH, H.symm_apply_apply]
  have hfg (y) (hy : y ∈ frontier (halfBall 1)) : f (g y) = y := by
    rw [← hgH ⟨y, hy⟩, ← hfH, H.apply_symm_apply]
  have hfi : InjOn f S := by
    intro x hx y hy hxy
    exact (hgf x hx).symm.trans ((congrArg g hxy).trans (hgf y hy))
  have hgi : InjOn g (frontier (halfBall 1)) := by
    intro x hx y hy hxy
    exact (hfg x hx).symm.trans ((congrArg f hxy).trans (hfg y hy))
  have hfs : f '' S = frontier (halfBall 1) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [← hfH ⟨x, hx⟩]
      exact (H ⟨x, hx⟩).property
    · intro hy
      refine ⟨H.symm ⟨y, hy⟩, (H.symm ⟨y, hy⟩).property, ?_⟩
      rw [← hfH, H.apply_symm_apply]
  have hgS (y) (hy : y ∈ frontier (halfBall 1)) : g y ∈ S := by
    rw [← hgH ⟨y, hy⟩]
    exact (H.symm ⟨y, hy⟩).property
  have hqS := hD.1.trans hDS
  have hD' := hD.image_of_subset hf hDS hfi
  have hdB : f '' D ⊆ frontier (halfBall 1) := by
    rw [← hfs]
    exact image_mono hDS
  have hout' : (frontier (halfBall 1) \ f '' D).Nonempty := by
    obtain ⟨x, hx, hxd⟩ := hout
    refine ⟨f x, hfs.subset (mem_image_of_mem f hx), ?_⟩
    rintro ⟨y, hy, hyx⟩
    exact hxd ((hfi (hDS hy) hx hyx) ▸ hy)
  have hball := isFinitePLBallPair_halfBall (h := 1) (Or.inl rfl)
  rw [← frontier_halfBall (Or.inl rfl)] at hball
  have hcomp := hball.boundary_disk_complement
    (by simp [Module.finrank_prod]) hD' hdB hout'
  have hback := hcomp.image_of_subset hg sdiff_subset hgi
  have hqback : g '' (f '' Q) = Q := by
    ext x
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      rwa [hgf y (hqS hy)]
    · intro hx
      exact ⟨f x, mem_image_of_mem f hx, hgf x (hqS hx)⟩
  have hmember (T : Set E) (hTS : T ⊆ S) (y) (hy : y ∈ frontier (halfBall 1)) :
      g y ∈ T ↔ y ∈ f '' T := by
    constructor
    · intro ht
      exact ⟨g y, ht, hfg y hy⟩
    · rintro ⟨x, hx, rfl⟩
      rwa [hgf x (hTS hx)]
  have hbackset : g '' (frontier (halfBall 1) \ (f '' D \ f '' Q)) = S \ (D \ Q) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨hgS y hy.1, ?_⟩
      rintro ⟨hd, hnq⟩
      exact hy.2 ⟨(hmember D hDS y hy.1).mp hd,
        fun hq ↦ hnq ((hmember Q hqS y hy.1).mpr hq)⟩
    · rintro ⟨hx, hnot⟩
      have hfB := hfs.subset (mem_image_of_mem f hx)
      refine ⟨f x, ⟨hfB, ?_⟩, hgf x hx⟩
      rintro ⟨hd, hnq⟩
      have hxd := (hmember D hDS (f x) hfB).mpr hd
      rw [hgf x hx] at hxd
      exact hnot ⟨hxd, fun hq ↦ hnq (mem_image_of_mem f hq)⟩
  rwa [hqback, hbackset] at hback

open Classical in
theorem isFinitePLBallPair_of_one_boundary_count_one
    (K L : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (hlinks : ∀ v ∈ K.vertices, IsConnected (K.link v).space)
    (hconn : IsConnected K.space) (hcount : K.surfaceEulerCount = 1) (hLK : L ≤ K)
    (gamma : sphere (0 : Fin 2 → ℝ) 1 ≃ₜ L.space) (hgamma : gamma.IsFinitePL)
    (hboundary : ∀ s ∈ K.faces, s.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard =
        if s ∈ L.faces then 1 else 2) :
    IsFinitePLBallPair (ℝ × ℝ) K.space L.space := by
  classical
  obtain ⟨J, hJ, hJs, H, hH⟩ := exists_one_boundary_capped_sphere
    K L hK hpure hlinks hconn hcount hLK gamma hgamma hboundary
  let z : E → E × ℝ := fun x ↦ (x, 0)
  have hcap := (isFinitePLBallPair_boundaryCircleCap true gamma hgamma).model_equiv
    (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)
  have hcapJ : boundaryCircleCap true L.space ⊆ J.space := by
    rw [hJs]
    exact subset_union_right
  have hnot : (K.space \ L.space).Nonempty := by
    by_contra hn
    have hsub : K.space ⊆ L.space := by
      intro x hx
      by_contra hxl
      exact hn ⟨x, hx, hxl⟩
    have hKL := K.le_of_common_subcomplex_space_subset K L le_rfl hLK hsub
    obtain ⟨x, hx⟩ := hconn.nonempty
    obtain ⟨s, hs, _⟩ := SimplicialComplex.mem_space_iff.mp hx
    obtain ⟨t, ht, hc, _⟩ := hpure s hs
    have hdim := (circle_incidence L (hK.subset hLK) gamma hgamma).1 t (hKL ht)
    omega
  have hout : (J.space \ boundaryCircleCap true L.space).Nonempty := by
    obtain ⟨x, hx, hxl⟩ := hnot
    refine ⟨z x, hJs.symm.subset (Or.inl (mem_image_of_mem z hx)), ?_⟩
    intro hcapx
    exact hxl ((boundaryCircleCap_plane true L.space).subset
      ⟨hcapx, mem_univ _, rfl⟩).1
  have hdisk := finitePL_sphere_disk_complement H hH hcap hcapJ hout
  have hcarrier : J.space \ (boundaryCircleCap true L.space \ L.space ×ˢ {0}) =
      z '' K.space := by
    ext x
    rw [hJs]
    constructor
    · rintro ⟨hx | hx, hnot⟩
      · exact hx
      · have hq : x ∈ L.space ×ˢ ({0} : Set ℝ) := by
          by_contra hnq
          exact hnot ⟨hx, hnq⟩
        exact ⟨x.1, SimplicialComplex.space_subset_of_le hLK hq.1,
          Prod.ext rfl hq.2.symm⟩
    · rintro ⟨y, hy, rfl⟩
      refine ⟨Or.inl (mem_image_of_mem z hy), ?_⟩
      rintro ⟨hcapy, hnq⟩
      exact hnq ((boundaryCircleCap_plane true L.space).subset ⟨hcapy, mem_univ _, rfl⟩)
  rw [hcarrier] at hdisk
  let fst : (E × ℝ) →ᴬ[ℝ] E := (ContinuousLinearMap.fst ℝ E ℝ).toContinuousAffineMap
  have hi : InjOn fst (z '' K.space) := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ he
    exact congrArg z he
  have hpair := hdisk.affine_image fst hi
  have hbase : fst '' (z '' K.space) = K.space := by
    rw [image_image]
    exact image_id _
  have hrim : fst '' (L.space ×ˢ ({0} : Set ℝ)) = L.space := by
    ext x
    exact ⟨fun ⟨y, hy, he⟩ ↦ he ▸ hy.1, fun hx ↦ ⟨(x, 0), ⟨hx, rfl⟩, rfl⟩⟩
  rwa [hbase, hrim] at hpair

end PoincareConjecture.M76.Dehn.Annuli
