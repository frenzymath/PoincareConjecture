import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Tubes.CoordinateModelAxis

set_option autoImplicit false
open Set Metric Geometry Topology Geometry.SimplicialComplex

namespace PoincareConjecture.M76.Dehn

local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)

open Classical in

theorem original_vertex_coordinate_faces
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X] {C : Set X}
    (K : SimplicialComplex ℝ E) [Fintype K.faces]
    (H : C ≃ₜ K.space) (g : E → C)
    (hg : ∀ z : K.space, (g z : X) = (H.symm z : X))
    (v : E) (hvK : v ∈ K.vertices) (hvC : (g v : X) ∈ interior C)
    (B : OpenPartialHomeomorph X V3)
    (hsource : MapsTo (fun z => (g z : X)) (K.closedStar v).space B.source)
    (hface : (K.closedStar v).AffineOnFaces (fun z => B (g z)))
    (hvzero : ∀ i : Fin 2, B (g v) i.castSucc = 0) :
    let V := K.barycentricDualBlock {v}
    let Z := {z | z ∈ V.space ∧ B (g z) 0 = 0 ∧ B (g z) 1 = 0}
    let bZ := Z ∩ (V.link v).space
    IsFinitePLBallPair ℝ Z bZ ∧
      ∀ (i : Fin 2) (b : Bool),
        let F := {z | z ∈ V.space ∧ B (g z) i.castSucc = 0 ∧
          if b then 0 ≤ B (g z) i.rev.castSucc else B (g z) i.rev.castSucc ≤ 0}
        let O := F ∩ (V.link v).space
        IsFinitePLBallPair P2 F (Z ∪ O) ∧ IsFinitePLBallPair ℝ O bZ := by
  classical
  let V := K.barycentricDualBlock {v}
  let Z := {z | z ∈ V.space ∧ B (g z) 0 = 0 ∧ B (g z) 1 = 0}
  let bZ := Z ∩ (V.link v).space
  let f : E → V3 := fun z => B (g z) - B (g v)
  obtain ⟨C0, L, theta, hC, hcv, hC0, _, hrep, htheta, _, hlink, hmarks⟩ :=
    exists_original_vertex_coordinate_model K H g hg v hvK hvC B hsource hface
  have hc (z : E) (i : Fin 2) : f z i.castSucc = B (g z) i.castSucc := by
    simp only [f, Pi.sub_apply, hvzero i, sub_zero]
  have hc0 (z : E) : f z 0 = B (g z) 0 := hc z 0
  have hc1 (z : E) : f z 1 = B (g z) 1 := hc z 1
  have haxis := finitePL_coordinate_model_axis V.space (V.link v).space f
    C0 hC hcv hC0 L hrep theta htheta hlink hmarks
  have hZ : IsFinitePLBallPair ℝ Z bZ := by
    convert haxis using 1
    · ext z
      simp only [Z, mem_ofPred_eq, hc0, hc1]
    · ext z
      simp only [bZ, Z, mem_ofPred_eq, mem_inter_iff, hc0, hc1]
      tauto
  refine ⟨hZ, ?_⟩
  intro i b
  let F := {z | z ∈ V.space ∧ B (g z) i.castSucc = 0 ∧
    if b then 0 ≤ B (g z) i.rev.castSucc else B (g z) i.rev.castSucc ≤ 0}
  let O := F ∩ (V.link v).space
  have hplane := finitePL_coordinate_model_planes V.space (V.link v).space f
    C0 hC hcv hC0 L hrep theta htheta hlink hmarks i.castSucc ![true, false] ![b, true]
  have hFraw : IsFinitePLBallPair P2 F
      {z | z ∈ F ∧ (z ∈ (V.link v).space ∨ B (g z) i.rev.castSucc = 0)} := by
    convert hplane using 1
    · ext z
      fin_cases i <;>
        simp [F, coordinatePlaneIndex, Fin.forall_fin_two, hc0, hc1]
    · ext z
      fin_cases i <;>
        simp [F, coordinatePlaneIndex, Fin.forall_fin_two, Fin.exists_fin_two, hc0, hc1,
          and_assoc]
  have hZF : Z ⊆ F := by
    rintro z ⟨hz, hz0, hz1⟩
    fin_cases i <;> cases b <;> simp [F, hz, hz0, hz1]
  have hrim : {z | z ∈ F ∧ (z ∈ (V.link v).space ∨ B (g z) i.rev.castSucc = 0)} =
      Z ∪ O := by
    ext z
    constructor
    · rintro ⟨hz, hl | ho⟩
      · exact Or.inr ⟨hz, hl⟩
      · apply Or.inl
        fin_cases i
        · exact ⟨hz.1, hz.2.1, ho⟩
        · exact ⟨hz.1, ho, hz.2.1⟩
    · rintro (hz | hz)
      · refine ⟨hZF hz, Or.inr ?_⟩
        fin_cases i
        · exact hz.2.2
        · exact hz.2.1
      · exact ⟨hz.1, Or.inl hz.2⟩
  have hF : IsFinitePLBallPair P2 F (Z ∪ O) := hrim ▸ hFraw
  have hZO : Z ∩ O = bZ := by
    ext z
    exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hZF h.1, h.2⟩⟩
  obtain ⟨x, y, hxy, hbpair⟩ := hZ.exists_boundary_eq_pair
  obtain ⟨O', hO', hwhole, hinter⟩ := hF.exists_boundary_arc_complement
    (hbpair ▸ hZ) subset_union_left hxy
  have hOeq : O' = O := by
    apply Subset.antisymm
    · intro z hz
      by_cases hzZ : z ∈ Z
      · exact (hZO.symm.subset (hbpair.symm.subset (hinter.subset ⟨hzZ, hz⟩))).2
      · exact (hwhole.subset (Or.inr hz)).resolve_left hzZ
    · intro z hz
      by_cases hzZ : z ∈ Z
      · exact hO'.1 (hbpair.subset (hZO.subset ⟨hzZ, hz⟩))
      · exact (hwhole.symm.subset (Or.inr hz)).resolve_left hzZ
  exact ⟨hF, by simpa only [hOeq, ← hbpair] using hO'⟩

end PoincareConjecture.M76.Dehn
