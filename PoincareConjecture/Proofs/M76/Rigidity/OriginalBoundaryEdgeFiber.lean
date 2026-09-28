import PoincareConjecture.Proofs.M76.Rigidity.OriginalTriangleFiber
import PoincareConjecture.Proofs.M76.Rigidity.OriginalFrontierEdgeCofaces









set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.OriginalProperDiskTriangulation

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "I" => Icc (-1 : ℝ) 1

variable {X ι : Type*} [TopologicalSpace X] [T2Space X]
  {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}
  (T : OriginalProperDiskTriangulation e R j)




theorem exists_boundary_edge_fiber
    {s : Finset (T.index → ℝ × V3)} (hs : s ∈ (T.marked 2).faces)
    (hcard : s.card = 2) (hsB : s ∈ (T.marked 1).faces) :
    ∃ F : ℝ → (T.index → ℝ × V3), FinitePiecewiseAffineOn F I ∧ InjOn F I ∧
      F '' I = T.dualRegion s ∩ (T.marked 1).space ∧ F 0 = s.centroid ℝ id ∧
      (∀ p : (T.marked 2).vertices, (p : T.index → ℝ × V3) ∈ s → ∀ r ∈ I,
        0 ≤ T.height p (F r) ↔ 0 ≤ r) ∧
      ∀ p : (T.marked 2).vertices, (p : T.index → ℝ × V3) ∈ s → ∀ r ∈ I,
        T.height p (F r) ≤ 0 ↔ r ≤ 0 := by
  classical
  let : Fintype (T.marked 1).faces := (T.marked_finite 1).fintype
  obtain ⟨p0, hp0⟩ := (T.marked 2).nonempty_of_mem_faces hs
  let p : (T.marked 2).vertices := ⟨p0, (T.marked 2).face_subset_vertices hs hp0⟩
  have hps : (p : T.index → ℝ × V3) ∈ s := hp0
  have hpfront : (T.inverse p : X) ∈ frontier R :=
    (T.inverse_mem_boundary_iff (T.ambient.subset_space (T.marked_le 1 hsB) hps)).mpr
      ((T.marked 1).subset_space hsB hps)
  obtain ⟨f, hf, hfi, _, hfval⟩ := T.exists_frontier_star_plane_chart p hpfront
  obtain ⟨t, ht, u, hu, hst, hsu, htc, huc, htu, hpair, _⟩ :=
    T.exists_frontier_edge_dual_interval hs hsB hcard
  have hNF : T.dualRegion s ∩ (T.marked 1).space =
      ((T.marked 1).barycentricDualBlock s).space := T.dualRegion_inter_boundary s
  have hzero : (T.dualRegion s ∩ (T.marked 1).space) ∩
      {x | T.height p x = 0} = {s.centroid ℝ id} := by
    rw [← T.boundary_edge_base_contact hs hcard hsB]
    ext x
    constructor
    · intro hx
      exact ⟨⟨hx.1.1, (T.height_eq_zero_iff_on_dualRegion p hps hx.1.1).mp hx.2⟩,
        hx.1.2⟩
    · intro hx
      exact ⟨⟨hx.1.1, hx.2⟩,
        (T.height_eq_zero_iff_on_dualRegion p hps hx.1.1).mpr hx.1.2⟩
  let ell : P2 →ₗ[ℝ] ℝ := T.weight (T.chart_index p) • LinearMap.snd ℝ ℝ ℝ
  have hell : ell.toAffineMap.linear ≠ 0 := by
    intro he
    have hz := congrArg (fun m : P2 →ₗ[ℝ] ℝ => m (0, 1)) he
    apply T.weight_nonzero (T.chart_index p)
    change T.weight (T.chart_index p) * 1 = 0 at hz
    simpa only [mul_one] using hz
  have heval (x : T.index → ℝ × V3) : ell (f x) = T.height p x := by
    rw [hfval]
    rfl
  have hstar {v : Finset (T.index → ℝ × V3)} (hv : v ∈ (T.marked 1).faces)
      (hsv : s ⊆ v) : v ∈ ((T.marked 1).closedStar p).faces :=
    ⟨hv, by simpa only [Finset.insert_eq_of_mem (hsv hps)] using hv⟩
  have hvertexzero : ∀ x ∈ s, ell (f x) = 0 := by
    intro x hx
    rw [heval]
    have hsstar : s ∈ (T.ambient.closedStar p).faces :=
      ⟨T.marked_le 2 hs,
        by simpa only [Finset.insert_eq_of_mem hps] using T.marked_le 2 hs⟩
    have hxD := (T.marked 2).subset_space hs hx
    exact (T.height_eq_zero_iff p ((T.ambient.closedStar p).subset_space hsstar hx)
      (T.disk_space_subset_region hxD)).mpr hxD
  have hsign := hf.opposite_centroid_signs hfi (hstar hsB Subset.rfl)
    (hstar ht hst) (hstar hu hsu)
    (by simpa only [Module.finrank_prod, Module.finrank_self] using hcard)
    (by simpa only [Module.finrank_prod, Module.finrank_self] using htc)
    (by simpa only [Module.finrank_prod, Module.finrank_self] using huc)
    hst hsu htu ell.toAffineMap hell hvertexzero
  change (ell (f (t.centroid ℝ id)) < 0 ∧ 0 < ell (f (u.centroid ℝ id))) ∨
    (0 < ell (f (t.centroid ℝ id)) ∧ ell (f (u.centroid ℝ id)) < 0) at hsign
  simp only [heval] at hsign
  obtain ⟨F, hF, hi, him, h0, _, hpos, hneg⟩ :=
    exists_finitePL_fiber_of_paired_ends (hNF.symm ▸ hpair) (T.height p)
      ((T.continuousOn_height_dualRegion p hps).mono inter_subset_left) hzero hsign
  refine ⟨F, hF, hi, him, h0, ?_, ?_⟩
  · intro q hqs r hr
    have hx : F r ∈ T.dualRegion s := (him.subset (mem_image_of_mem F hr)).1
    have heq := (T.dualRegion_halves_eq p q hs hps hqs).1
    have he : 0 ≤ T.height q (F r) ↔ 0 ≤ T.height p (F r) :=
      ⟨fun h => (heq.symm.subset ⟨hx, h⟩).2, fun h => (heq.subset ⟨hx, h⟩).2⟩
    exact he.trans (hpos r hr)
  · intro q hqs r hr
    have hx : F r ∈ T.dualRegion s := (him.subset (mem_image_of_mem F hr)).1
    have heq := (T.dualRegion_halves_eq p q hs hps hqs).2
    have he : T.height q (F r) ≤ 0 ↔ T.height p (F r) ≤ 0 :=
      ⟨fun h => (heq.symm.subset ⟨hx, h⟩).2, fun h => (heq.subset ⟨hx, h⟩).2⟩
    exact he.trans (hneg r hr)

end PoincareConjecture.M76.OriginalProperDiskTriangulation
