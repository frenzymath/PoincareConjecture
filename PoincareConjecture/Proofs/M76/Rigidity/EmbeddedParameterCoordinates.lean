import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLInverse
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonPLDomainMaps











set_option autoImplicit false

open Set Geometry
open scoped Topology

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

variable {E X Y ι κ : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace X] [TopologicalSpace Y] {R : Set X} {T : Set Y}




theorem chartwisePLMap_of_embedded_polyhedral_parameters
    (e : ι → OpenPartialHomeomorph X V3)
    (d : κ → OpenPartialHomeomorph Y V3)
    (he : PLDomain e R) (hd : PLDomain d T) (f : C(R, T))
    (hparameters : ∀ x : R,
      ∃ (K : SimplicialComplex ℝ E) (q : E → R) (z : K.space),
        K.faces.Finite ∧ ContinuousOn q K.space ∧
        Topology.IsEmbedding (fun u : K.space => q u) ∧ q z = x ∧
        range (fun u : K.space => q u) ∈ 𝓝 x ∧
        PolyhedralPLInCharts e (fun u => (q u : X)) K.space ∧
        PolyhedralPLInCharts d (fun u => (f (q u) : Y)) K.space) :
    ChartwisePLMap e d f := by
  classical
  refine ⟨he, hd, isOpen_univ, ?_⟩
  intro x _
  obtain ⟨K, q, z, hK, _, hQ, hqz, hrange, hqPL, hfqPL⟩ := hparameters x
  rcases hqz with rfl
  obtain ⟨i, J, V, _, hJK, hV, hzV, hVJ, hqJ, hsource⟩ := hqPL.coordinates z
  obtain ⟨j, L, U, _, hLK, hU, hzU, hUL, hfqL, htarget⟩ := hfqPL.coordinates z
  obtain ⟨N, Z, hN, hNK, hZ, hzZ, hZN, hNZ⟩ :=
    K.exists_relative_polyhedral_neighborhood hK z (hV.inter hU) ⟨hzV, hzU⟩
  have hNJ : N.space ⊆ J.space := by
    intro u hu
    exact hVJ ⟨⟨u, hNK hu⟩,
      (hNZ (show (⟨u, hNK hu⟩ : K.space) ∈ Subtype.val ⁻¹' N.space from hu)).1, rfl⟩
  have hNL : N.space ⊆ L.space := by
    intro u hu
    exact hUL ⟨⟨u, hNK hu⟩,
      (hNZ (show (⟨u, hNK hu⟩ : K.space) ∈ Subtype.val ⁻¹' N.space from hu)).2, rfl⟩
  have hqi (u : E) (hu : u ∈ N.space) : (q u : X) ∈ (e i).source := hqJ (hNJ hu)
  have hfqj (u : E) (hu : u ∈ N.space) : (f (q u) : Y) ∈ (d j).source :=
    hfqL (hNL hu)
  let A : E → V3 := fun u => e i (q u)
  let Cmap : E → V3 := fun u => d j (f (q u))
  have hA : FinitePiecewiseAffineOn A N.space := hsource.restrict N hN hNJ
  have hC : FinitePiecewiseAffineOn Cmap N.space := htarget.restrict N hN hNL
  have hAi : InjOn A N.space := by
    intro u hu v hv huv
    have hqu : q u = q v := Subtype.ext ((e i).injOn (hqi u hu) (hqi v hv) huv)
    have heq : (⟨u, hNK hu⟩ : K.space) = ⟨v, hNK hv⟩ := hQ.injective hqu
    exact congrArg Subtype.val heq
  obtain ⟨b, hb, hbval⟩ := hA.exists_homeomorph_image hAi
  obtain ⟨G, hG, hGval⟩ := hb.symm
  have hGA (u : E) (hu : u ∈ N.space) : G (A u) = u := by
    have h := hGval (b ⟨u, hu⟩)
    rw [b.symm_apply_apply] at h
    simpa only [hbval] using h.symm
  obtain ⟨P, hP, hPimage, hGfaces⟩ := hG
  have hGP : MapsTo G P.space N.space := by
    intro y hy
    obtain ⟨u, hu, rfl⟩ := hPimage.subset hy
    rwa [hGA u hu]
  have hformula : FinitePiecewiseAffineOn (Cmap ∘ G) P.space :=
    hC.comp (hGfaces.finitePiecewiseAffineOn hP) hGP
  obtain ⟨O, hO, hQZO⟩ := hQ.isInducing.image_eq_isOpen_inter_range hZ
  let W : Set R := O ∩ interior (range (fun u : K.space => q u))
  have hW : IsOpen W := hO.inter isOpen_interior
  have hxW : q z ∈ W :=
    ⟨(hQZO.subset ⟨z, hzZ, rfl⟩).1, mem_interior_iff_mem_nhds.mpr hrange⟩
  have hWqN (y : R) (hy : y ∈ W) : ∃ u : E, u ∈ N.space ∧ q u = y := by
    obtain ⟨u, hu, hqu⟩ := hQZO.symm.subset ⟨hy.1, interior_subset hy.2⟩
    exact ⟨u, hZN ⟨u, hu, rfl⟩, hqu⟩
  refine ⟨i, j, P, W, Cmap ∘ G, hP, hW, hxW, subset_univ _, ?_, ?_, ?_, ?_,
    hformula, ?_⟩
  · intro y hy
    obtain ⟨u, hu, rfl⟩ := hWqN y hy
    exact hqi u hu
  · rintro _ ⟨y, hy, rfl⟩
    obtain ⟨u, hu, rfl⟩ := hWqN y hy
    exact hPimage.symm.subset ⟨u, hu, rfl⟩
  · intro y hy
    obtain ⟨u, hu, rfl⟩ := hPimage.subset hy
    exact (e i).map_source (hqi u hu)
  · intro y hy
    obtain ⟨u, hu, rfl⟩ := hPimage.subset hy
    exact ⟨q u, mem_univ _, ((e i).left_inv (hqi u hu)).symm⟩
  · intro y hyi hyP
    obtain ⟨u, hu, hue⟩ := hPimage.subset hyP
    have hqu : q u = y := Subtype.ext ((e i).injOn (hqi u hu) hyi hue)
    refine ⟨hqu ▸ hfqj u hu, ?_⟩
    change Cmap (G (e i y)) = d j (f y)
    rw [← hue, hGA u hu]
    change d j (f (q u)) = d j (f y)
    rw [hqu]

end PoincareConjecture.M76
