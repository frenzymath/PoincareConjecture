import PoincareConjecture.Proofs.M76.Mathlib.InteriorConnectedLinks
import PoincareConjecture.Proofs.M76.Mathlib.FaceLinkCofaceCount
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallPairs










set_option autoImplicit false

open Set Filter
open scoped Topology

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]



theorem isConnected_link_of_punctured_neighborhood
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {p : E} {B : Set E} (hB : IsConnected B)
    (hBstar : B ⊆ (K.closedFaceStar {p}).space \ {p})
    (hnear : insert p B ∈ 𝓝[K.space] p) : IsConnected (K.link p).space := by
  obtain ⟨R, hRcont, hRmap, hRline⟩ := K.exists_continuous_faceLink_retraction hK {p}
  have hBdomain : B ⊆ (K.closedFaceStar {p}).space \
      (affineSpan ℝ (({p} : Finset E) : Set E) : Set E) := by
    simpa using hBstar
  obtain ⟨U, hU, hpU, hUB⟩ := mem_nhdsWithin.mp hnear
  have himage : R '' B = (K.faceLink {p}).space := by
    apply subset_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact hRmap (hBdomain hx)
    · intro y hy
      have hlocal : ∀ᶠ r : ℝ in 𝓝[>] 0, AffineMap.lineMap p y r ∈ U :=
        AffineMap.lineMap_continuous.continuousWithinAt.eventually_mem
          (by simpa using hU.mem_nhds hpU)
      obtain ⟨r, hrU, hr⟩ := (hlocal.and (Ioo_mem_nhdsGT zero_lt_one)).exists
      obtain ⟨hrD, hrR⟩ := hRline p (by simp) y hy r ⟨hr.1, hr.2.le⟩
      have hrK : AffineMap.lineMap p y r ∈ K.space := by
        obtain ⟨a, ha, hxa⟩ := mem_space_iff.mp hrD.1
        exact K.convexHull_subset_space ha.1 hxa
      have hrne : AffineMap.lineMap p y r ≠ p := by simpa using hrD.2
      exact ⟨AffineMap.lineMap p y r, (hUB ⟨hrU, hrK⟩).resolve_left hrne, hrR⟩
  rw [← K.faceLink_singleton_eq_link p, ← himage]
  exact hB.image R (hRcont.mono hBdomain)




theorem isConnected_link_of_local_finitePLBallPair
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] (hdim : 1 < Module.finrank ℝ F)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {p : E} (hp : p ∈ K.vertices) {d rim : Set E}
    (hd : IsFinitePLBallPair F d rim) (hdK : d ⊆ K.space)
    (hpd : p ∈ d \ rim)
    (hopen : IsOpen (Subtype.val ⁻¹' (d \ rim) : Set K.space)) :
    IsConnected (K.link p).space := by
  classical
  obtain ⟨_, C, hC, _, _, e, he, hboundary⟩ := hd
  obtain ⟨g, hg, heg⟩ := he.symm
  obtain ⟨f, hf, hef⟩ := he
  let z : F := e ⟨p, hpd.1⟩
  have hzC : z ∈ C := (e ⟨p, hpd.1⟩).property
  have hzint : z ∈ interior C := by
    by_contra hz
    exact hpd.2 ((hboundary ⟨p, hpd.1⟩).mpr ⟨subset_closure hzC, hz⟩)
  have hfmem (x : E) (hx : x ∈ d) : f x ∈ C := by
    rw [← hef ⟨x, hx⟩]
    exact (e ⟨x, hx⟩).property
  have hgmem (y : F) (hy : y ∈ C) : g y ∈ d := by
    rw [← heg ⟨y, hy⟩]
    exact (e.symm ⟨y, hy⟩).property
  have hgf (x : E) (hx : x ∈ d) : g (f x) = x := by
    rw [← hef ⟨x, hx⟩, ← heg, e.symm_apply_apply]
  have hfg (y : F) (hy : y ∈ C) : f (g y) = y := by
    rw [← heg ⟨y, hy⟩, ← hef, e.apply_symm_apply]
  have hfp : f p = z := (hef ⟨p, hpd.1⟩).symm
  have hgz : g z = p := by rw [← hfp]; exact hgf p hpd.1
  have hpK : p ∈ K.space := K.vertices_subset_space hp
  have hdnear : d ∈ 𝓝[K.space] p := by
    rw [← map_nhds_subtype_val (⟨p, hpK⟩ : K.space)]
    exact mem_of_superset (hopen.mem_nhds hpd) (fun _ hx => hx.1)
  have hnhdseq : 𝓝[d] p = 𝓝[K.space] p := by
    simpa only [inter_eq_left.mpr hdK] using nhdsWithin_inter_of_mem hdnear
  have hstar : (K.closedFaceStar {p}).space ∈ 𝓝[K.space] p := by
    rw [← map_nhds_subtype_val (⟨p, hpK⟩ : K.space)]
    apply K.closedFaceStar_mem_nhds_of_intrinsicInterior hK hp
    simp
  obtain ⟨U, hU, hpU, hUstar⟩ := mem_nhdsWithin.mp hstar
  have hgcont : ContinuousAt g z :=
    (hg.continuousOn z hzC).continuousAt (mem_interior_iff_mem_nhds.mp hzint)
  have hgzU : g ⁻¹' U ∈ 𝓝 z :=
    hgcont.preimage_mem_nhds (by simpa only [hgz] using hU.mem_nhds hpU)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp
    (inter_mem (mem_interior_iff_mem_nhds.mp hzint) hgzU)
  let B : Set E := g '' (Metric.ball z ε \ {z})
  have hconn : IsConnected (Metric.ball z ε \ {z}) := by
    simpa using (AffineSubspace.isPathConnected_sdiff_iUnion
      (fun _ : Unit => affineSpan ℝ ({z} : Set F))
      (fun _ => by
        rw [direction_affineSpan, vectorSpan_singleton, finrank_bot]
        exact hdim)
      Metric.isOpen_ball (convex_ball z ε)
      ⟨z, Metric.mem_ball_self hε⟩).isConnected
  have hBconn : IsConnected B :=
    hconn.image g (hg.continuousOn.mono (fun _ hy => (hball hy.1).1))
  have hBstar : B ⊆ (K.closedFaceStar {p}).space \ {p} := by
    rintro x ⟨y, hy, rfl⟩
    have hyC := (hball hy.1).1
    refine ⟨hUstar ⟨(hball hy.1).2, hdK (hgmem y hyC)⟩, ?_⟩
    intro heq
    have heq' : g y = p := heq
    apply hy.2
    change y = z
    rw [← hfg y hyC, heq', hfp]
  have hBnear : insert p B ∈ 𝓝[K.space] p := by
    rw [← hnhdseq]
    have hpre : f ⁻¹' Metric.ball z ε ∈ 𝓝[d] p :=
      (hf.continuousOn p hpd.1)
        (by simpa only [hfp] using Metric.ball_mem_nhds z hε)
    filter_upwards [hpre, self_mem_nhdsWithin] with x hxball hxd
    by_cases hxp : x = p
    · exact Or.inl hxp
    · right
      refine ⟨f x, ⟨hxball, ?_⟩, hgf x hxd⟩
      intro hxz
      apply hxp
      rw [← hgf x hxd, show f x = z from hxz, hgz]
  exact K.isConnected_link_of_punctured_neighborhood hK hBconn hBstar hBnear

end Geometry.SimplicialComplex
