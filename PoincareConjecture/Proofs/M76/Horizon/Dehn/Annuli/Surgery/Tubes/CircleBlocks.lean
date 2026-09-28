import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Tubes.CircleBlockData
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Tubes.CircleModel
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Tubes.Joints.DiamondMaps
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Tubes.Blocks.VertexBlockMap



set_option autoImplicit false
open Set Metric Geometry Topology Geometry.SimplicialComplex

namespace PoincareConjecture.M76.Dehn.Annuli
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)

variable {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace X]
  {S : Set E} {e : ι → OpenPartialHomeomorph X V3} {f : E → X} {R : Set X}
  {old : SourceCircleDecomposition f S} {i : old.Index}

open Classical in


theorem ComponentBranchModel.exists_component_circle_blocks
    (D : ComponentBranchModel (e := e) (R := R) old i) (hcore : D.core ⊆ interior R)
    {n : ℕ} (p : Fin (n + 3) → D.sample → ℝ × V3)
    (hpi : Function.Injective p) (hpv : range p = D.axis.vertices)
    (hpf : ∀ s : Finset (D.sample → ℝ × V3), s ∈ D.axis.faces ↔
      s.Nonempty ∧ ∃ j : Fin (n + 3), s ⊆ {p j, p (finRotate (n + 3) j)}) :
    letI : Fintype D.complex.faces := D.complex_finite.fintype
    Nonempty (ComponentCircleBlockData D p) := by
  classical
  let : Fintype D.complex.faces := D.complex_finite.fintype
  obtain ⟨x, y, C, hC, hface, haxis, hsheet, hJoint⟩ := D.exists_incident_diamond_maps hcore
  let Edge := {s : Finset (D.sample → ℝ × V3) // s ∈ D.axis.faces ∧ s.card = 2}
  have hJoint' (s : Edge) := hJoint s s.property.1 s.property.2
  choose G hG hcenter hcorners hincidentFrame using hJoint'
  have hnext (j : Fin (n + 3)) : j ≠ finRotate (n + 3) j := by
    intro h
    have h' : (1 : Fin (n + 3)) = 0 := add_left_cancel
      (show j + 1 = j + 0 by simpa only [finRotate_apply, add_zero] using h.symm)
    have := congrArg Fin.val h'
    norm_num at this
  let vertex (j : Fin (n + 3)) : D.axis.vertices := ⟨p j, hpv ▸ mem_range_self j⟩
  let edge (j : Fin (n + 3)) : Edge :=
    ⟨{p j, p (finRotate (n + 3) j)},
      (hpf _).mpr ⟨Finset.insert_nonempty _ _, j, subset_rfl⟩,
      Finset.card_pair (hpi.ne (hnext j))⟩
  let incident (j : Fin (n + 3)) (b : Bool) :=
    if b then j else (finRotate (n + 3)).symm j
  have hincident (j : Fin (n + 3)) (b : Bool) :
      (vertex j : D.sample → ℝ × V3) ∈ (edge (incident j b) : Finset _) := by
    cases b <;> simp [vertex, edge, incident]
  have hframe (j : Fin (n + 3)) (b : Bool) :=
    hincidentFrame (edge (incident j b)) (vertex j) (hincident j b)
  choose a ha hside using hframe
  have hjointDisj := (D.complex.full_cyclic_dual_contacts D.axis D.axis_le
    D.axis_full p hpi hpv hpf).2.2.2.1
  have hblock (j : Fin (n + 3)) :
      ∃ map : ↥(signedTubeDiamond ×ˢ Icc (0 : ℝ) 1) ≃ₜ
        (D.complex.barycentricDualBlock {p j}).space,
        map.IsFinitePL ∧
        (∀ b (z : signedTubeDiamond),
          (map ⟨(z, if b then 1 else 0), z.property, by cases b <;> simp⟩ : D.sample → ℝ × V3) =
            G (edge (incident j b)) ((a j b).symm.diamond z)) ∧
        (∀ k (z : ↥(signedTubeDiamond ×ˢ Icc (0 : ℝ) 1)),
          (z : P2 × ℝ).1 ∈ signedTubeSheet k ↔ (C (vertex j)).chart (D.inverse (map z)) k.castSucc = 0) ∧
        ∀ z : ↥(signedTubeDiamond ×ˢ Icc (0 : ℝ) 1),
          (z : P2 × ℝ).1 = (0, 0) ↔ (map z : D.sample → ℝ × V3) ∈ D.axis.space := by
    have hne : (finRotate (n + 3)).symm j ≠ j := by
      intro h
      exact hnext j (by simpa only [Equiv.apply_symm_apply] using congrArg (finRotate (n + 3)) h)
    have hdisj := hjointDisj ((finRotate (n + 3)).symm j) j hne
    let s : Bool → Finset (D.sample → ℝ × V3) := fun b => edge (incident j b)
    let Gj : ∀ b, signedTubeDiamond ≃ₜ (D.complex.barycentricDualBlock (s b)).space :=
      fun b => (a j b).symm.diamond.trans (G (edge (incident j b)))
    have hGj (b : Bool) : (Gj b).IsFinitePL := ha j b
    have hGq (b : Bool) := signed_diamond_quarters_of_coordinate_sides (Gj b)
      (fun k z => (C (vertex j)).chart (D.inverse z) k.castSucc) (hside j b)
    have hGc (b : Bool) : (Gj b ⟨(0, 0),
        signedTubeRadius_subset_diamond 0 false (left_mem_segment ℝ _ _)⟩ : D.sample → ℝ × V3) =
          (s b).centroid ℝ id := by
      change (G (edge (incident j b)) ((a j b).symm.diamond _) : D.sample → ℝ × V3) = _
      have hz : (a j b).symm.diamond ⟨(0, 0),
          signedTubeRadius_subset_diamond 0 false (left_mem_segment ℝ _ _)⟩ =
          ⟨(0, 0), mem_iUnion.mpr ⟨false, mem_iUnion.mpr ⟨false, signedTube_center_mem⟩⟩⟩ :=
        Subtype.ext (a j b).symm.linear_zero
      rw [hz]
      exact hcenter (edge (incident j b))
    obtain ⟨_, map, _, hm, hend, _, _, hms, hma, _⟩ :=
      D.exists_local_vertex_block_map hcore (vertex j) (vertex j).property (C (vertex j))
        (hC (vertex j)) (hface (vertex j)) (haxis (vertex j)) (hsheet (vertex j)) s
        (fun b => (edge (incident j b)).property.1)
        (fun b => (edge (incident j b)).property.2) (hincident j)
        (by simpa only [s, edge, incident, Bool.false_eq_true, ↓reduceIte] using hdisj)
        Gj hGj hGq hGc
    exact ⟨map, hm, hend, hms, hma⟩
  choose map hmap hend hmaps hmapa using hblock
  exact ⟨{
    x := fun j => x (vertex j)
    y := fun j => y (vertex j)
    chart := fun j => C (vertex j)
    source := fun j => hC (vertex j)
    affine := fun j => hface (vertex j)
    axisChart := fun j => haxis (vertex j)
    sheetChart := fun j => hsheet (vertex j)
    joint := fun j => G (edge j)
    jointPL := fun j => hG (edge j)
    left := fun j => (a j false).symm
    right := fun j => (a j true).symm
    map := map
    mapPL := hmap
    lower := fun j z => hend j false z
    upper := fun j z => hend j true z
    sheets := hmaps
    axis := hmapa }⟩




theorem ComponentBranchModel.exists_circle_blocks
    (D : ComponentBranchModel (e := e) (R := R) old i) (hcore : D.core ⊆ interior R) :
    letI : Fintype D.complex.faces := D.complex_finite.fintype
    ∃ (n : ℕ) (p : Polygon (D.sample → ℝ × V3) (n + 3)),
      Function.Injective p ∧ p.HasSimplicialEdges ∧ range p = D.axis.vertices ∧
      p.boundary ℝ = D.axis.space ∧
      (∀ s : Finset (D.sample → ℝ × V3), s ∈ D.axis.faces ↔ s.Nonempty ∧
        ∃ j : Fin (n + 3), s ⊆ {p j, p (finRotate (n + 3) j)}) ∧
      Nonempty (ComponentCircleBlockData D p) := by
  obtain ⟨n, p, hpi, hP, hpv, hpbd, hpf, _⟩ := D.exists_axis_order
  exact ⟨n, p, hpi, hP, hpv, hpbd, hpf,
    D.exists_component_circle_blocks hcore p hpi hpv hpf⟩

end PoincareConjecture.M76.Dehn.Annuli

