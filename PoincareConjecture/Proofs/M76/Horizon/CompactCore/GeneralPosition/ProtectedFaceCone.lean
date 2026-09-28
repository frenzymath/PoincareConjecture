import PoincareConjecture.Proofs.M76.Horizon.Polyhedral.Maps.TranslatedBoundaryCone
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.GeneralPosition.ProtectedVertexMotion
import PoincareConjecture.Proofs.M76.PrimeReduction.CompatibleNormalCoordinates

set_option autoImplicit false

open Set Geometry Geometry.SimplicialComplex unitInterval

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

theorem PLDomain.exists_protected_face_cone
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [DecidableEq E] [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {N Y F : Set X}
    (hN : PLDomain e N) (hY : IsOpen Y) (hcut : Y ∩ frontier N = F)
    (B : OpenPartialHomeomorph X V3)
    (hcompat : ∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid V3)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {S : Set E} (hS : IsCompact S) (hScv : Convex ℝ S)
    (c : E) (hc : c ∈ interior S) (hKS : K.space = frontier S)
    (f b : E → X) (A : E →ᴬ[ℝ] V3)
    (hfsource : MapsTo f S B.source) (hfcoord : EqOn (B ∘ f) A S)
    (hb : K.AffineOnFaces (B ∘ b))
    {W : Set V3} (hWopen : IsOpen W) (hWcv : Convex ℝ W)
    (hWtarget : W ⊆ B.target) (hWY : MapsTo B.symm W Y)
    (hfW : MapsTo A S W)
    (D : C(I × frontier S, X))
    (hDsource : ∀ z, D z ∈ B.source) (hDW : ∀ z, B (D z) ∈ W)
    (hD0 : ∀ u : frontier S, D (0, u) = f u)
    (hD1 : ∀ u : frontier S, D (1, u) = b u) :
    ∃ (L : SimplicialComplex ℝ E) (g : E → X) (H : C(I × S, X)),
      L.faces.Finite ∧ L.space = S ∧ K ≤ L ∧ L.vertices = insert c K.vertices ∧
      (∀ s ∈ K.faces, insert c s ∈ L.faces) ∧
      (∀ s, s ∈ L.faces ↔ s.Nonempty ∧ (s.erase c = ∅ ∨ s.erase c ∈ K.faces)) ∧
      L.AffineOnFaces (B ∘ g) ∧ PolyhedralPLInCharts e g S ∧
      g c ∉ F ∧ EqOn g b (frontier S) ∧
      (∀ x ∈ S, g x ∈ B.source ∧ B (g x) ∈ W ∧ g x ∈ Y) ∧
      (∀ z, H z ∈ B.source ∧ B (H z) ∈ W ∧ H z ∈ Y) ∧
      (∀ u ∈ frontier S, ∀ r ∈ Icc (0 : ℝ) 1,
        B (g ((1 - r) • c + r • u)) =
          (1 - r) • B (g c) + r • B (b u)) ∧
      (∀ x : S, H (0, x) = f x) ∧ (∀ x : S, H (1, x) = g x) ∧
      ∀ (t : I) (u : frontier S),
        H (t, ⟨u, hS.isClosed.frontier_subset u.property⟩) = D (t, u) := by
  classical
  have hcS : c ∈ S := interior_subset hc
  have hfc : B (f c) ∈ W := by
    change (B ∘ f) c ∈ W
    rw [hfcoord hcS]
    exact hfW hcS
  have hfcY : f c ∈ Y := by
    simpa only [B.left_inv (hfsource hcS)] using hWY hfc
  have hO : IsOpen (B.source ∩ B ⁻¹' W) :=
    B.continuousOn.isOpen_inter_preimage B.open_source hWopen
  obtain ⟨p, hp0, hpO, hpfix, hpoff⟩ :=
    hN.exists_protected_vertex_motion hY hcut hO hfcY ⟨hfsource hcS, hfc⟩
  have hpa : B (p 1) ∈ W := (hpO 1).1.2
  let C : C(I × frontier S, W) :=
    ⟨fun z => ⟨B (D z), hDW z⟩,
      (B.continuousOn.comp_continuous D.continuous hDsource).subtype_mk _⟩
  have hC0 (u : frontier S) : (C (0, u) : V3) = A u := by
    change B (D (0, u)) = A u
    rw [hD0]
    exact hfcoord (hS.isClosed.frontier_subset u.property)
  have hC1 (u : frontier S) : (C (1, u) : V3) = (B ∘ b) u := by
    change B (D (1, u)) = B (b u)
    rw [hD1]
  obtain ⟨L, q, Hq, hL, hLS, hKL, hLv, hcone, hfaces, hq, hqPL, hqc, hqb,
    hqW, hqray, hH0, hH1, hHB⟩ :=
    hb.exists_boundary_cone_at_homotopy_with_faces hK hS hScv c hc hKS
      hWcv A hfW C hC0 hC1 (B (p 1)) hpa
  let g : E → X := B.symm ∘ q
  have hgcoord : EqOn (B ∘ g) q S := fun x hx => B.right_inv (hWtarget (hqW hx))
  let H : C(I × S, X) :=
    ⟨fun z => B.symm (Hq z),
      B.symm.continuousOn.comp_continuous
        (continuous_subtype_val.comp Hq.continuous) (fun z => hWtarget (Hq z).property)⟩
  have hgc : g c = p 1 := by
    change B.symm (q c) = p 1
    rw [hqc, B.left_inv (hpO 1).1.1]
  have hgPL : PolyhedralPLInCharts e g S := by
    have h := polyhedralPLInCharts_of_compatible_inverse e B
      (fun x _ => hN.cover x) hcompat L hL (hLS.symm ▸ hqPL)
      (fun x hx => hWtarget (hqW (hLS.subset hx)))
    simpa only [hLS] using h
  refine ⟨L, g, H, hL, hLS, hKL, hLv, hcone, hfaces, ?_, hgPL, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hq.congr (hLS.symm ▸ hgcoord.symm)
  · rw [hgc]
    exact hpoff 1 zero_lt_one
  · intro u hu
    change B.symm (q u) = b u
    rw [hqb hu]
    exact B.left_inv (hD1 ⟨u, hu⟩ ▸ hDsource (1, ⟨u, hu⟩))
  · intro x hx
    refine ⟨B.map_target (hWtarget (hqW hx)), ?_, hWY (hqW hx)⟩
    change (B ∘ g) x ∈ W
    rw [hgcoord hx]
    exact hqW hx
  · intro z
    refine ⟨B.map_target (hWtarget (Hq z).property), ?_, hWY (Hq z).property⟩
    change B (B.symm (Hq z)) ∈ W
    rw [B.right_inv (hWtarget (Hq z).property)]
    exact (Hq z).property
  · intro u hu r hr
    have hxu : (1 - r) • c + r • u ∈ S :=
      hScv hcS (hS.isClosed.frontier_subset hu) (sub_nonneg.mpr hr.2) hr.1 (sub_add_cancel 1 r)
    change (B ∘ g) ((1 - r) • c + r • u) = (1 - r) • (B ∘ g) c + r • B (b u)
    rw [hgcoord hxu, hgcoord hcS, hqray u hu r hr, hqc]
    rfl
  · intro x
    change B.symm (Hq (0, x)) = f x
    rw [hH0, ← hfcoord x.property]
    exact B.left_inv (hfsource x.property)
  · intro x
    change B.symm (Hq (1, x)) = B.symm (q x)
    rw [hH1]
  · intro t u
    change B.symm (Hq (t, ⟨u, hS.isClosed.frontier_subset u.property⟩)) = D (t, u)
    rw [hHB]
    exact B.left_inv (hDsource (t, u))

end PoincareConjecture.M76
