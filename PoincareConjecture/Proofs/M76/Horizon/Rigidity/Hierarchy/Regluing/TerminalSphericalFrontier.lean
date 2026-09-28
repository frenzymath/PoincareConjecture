import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Regluing.BoxBoundarySphere
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Regluing.RectangleFaces
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Regluing.TerminalCoordinatePL
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Mathlib.FiniteClosedPartition

set_option autoImplicit false
open Set Metric Geometry Topology

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "E3" => ((ℝ × ℝ) × ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "p" => (4 * (16 : ℝ))
local notation "C0" => AddCircle p
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates

theorem exists_hamiltonZero_terminal_spherical_frontier
    {ι κ : Type*} {e : ι → OpenPartialHomeomorph X0 V3}
    {d : κ → OpenPartialHomeomorph X0 V3}
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    {phi : C(H0, H0)}
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    {N : Set X0} (he : PLDomain e N) (hN : IsCompact N) (hne : N.Nonempty)
    {u v a b alpha beta : ℝ} (huv : u < v) (hab : a < b) (halpha : alpha < beta)
    (hthird : v < u + p) (hsecond : b < a + p) (hfirst : beta < alpha + p)
    (boundaryMap : C(frontier N, frontier ((Icc u v ×ˢ Icc a b) ×ˢ Icc alpha beta)))
    (hvalue : ∀ x : frontier N, Q0 (hamiltonZeroAmbientMap phi x) =
      (((((boundaryMap x : E3).1.1) : C0), (((boundaryMap x : E3).1.2) : C0)),
        (((boundaryMap x : E3).2) : C0)))
    (hc : IsCoveringMap boundaryMap) :
    ∃ (n : ℕ) (S : Fin n → Set X0),
      Pairwise (fun i j => Disjoint (S i) (S j)) ∧ (⋃ i, S i) = frontier N ∧
      ∀ i, IsCompact (S i) ∧ (S i).Nonempty ∧
        Nonempty (ChartwisePLSphere e (S i)) ∧
        ∀ x ∈ S i, connectedComponentIn (frontier N) x = S i := by
  classical
  let : T2Space X0 := (Q0).isEmbedding.t2Space
  let : CompactSpace (frontier N) := isCompact_iff_compactSpace.mp
    (hN.of_isClosed_subset isClosed_frontier he.closed.frontier_subset)
  let Sphere := sphere (0 : V3) 1
  let : CompactSpace Sphere := isCompact_iff_compactSpace.mp (isCompact_sphere _ _)
  let : SimplyConnectedSpace Sphere := unitThreeSphere_lifting_properties.1
  let : LocallyPathConnectedSpace Sphere := unitThreeSphere_lifting_properties.2
  obtain ⟨B, hB⟩ := exists_finitePL_terminalBox_boundary_sphere huv hab halpha
  let base : C(Sphere, frontier ((Icc u v ×ˢ Icc a b) ×ˢ Icc alpha beta)) := B
  let z0 : Sphere := ⟨fun _ => 1, by simp [Sphere]⟩
  obtain ⟨n, face, hface, hdis, hwhole, hcoord⟩ :=
    hc.exists_finite_lifted_compact_family base B.injective z0
  have hwhole' : (⋃ i, range (face i)) = univ := by
    rw [hwhole]
    have hb : range base = univ := B.surjective.range_eq
    rw [hb, preimage_univ]
  let f (i : Fin n) : Sphere → X0 := fun z => face i z
  let S (i : Fin n) : Set X0 := range (f i)
  have hfc (i : Fin n) : Continuous (f i) := continuous_subtype_val.comp (face i).continuous
  have hfi (i : Fin n) : IsEmbedding (f i) := IsEmbedding.subtypeVal.comp (hface i)
  have hSS (i : Fin n) : S i ⊆ frontier N := by
    rintro _ ⟨z, rfl⟩
    exact (face i z).property
  have hScompact (i : Fin n) : IsCompact (S i) := isCompact_range (hfc i)
  have hSdis : Pairwise (fun i j => Disjoint (S i) (S j)) := by
    intro i j hij
    apply disjoint_left.mpr
    rintro _ ⟨z, rfl⟩ ⟨w, hw⟩
    exact disjoint_left.mp (hdis hij) ⟨z, rfl⟩ ⟨w, Subtype.ext hw⟩
  have hSwhole : (⋃ i, S i) = frontier N := by
    apply le_antisymm (iUnion_subset hSS)
    intro x hx
    have hmem : (⟨x, hx⟩ : frontier N) ∈ ⋃ i, range (face i) := hwhole'.symm ▸ mem_univ _
    obtain ⟨i, z, hz⟩ := mem_iUnion.mp hmem
    exact mem_iUnion.mpr ⟨i, z, congrArg Subtype.val hz⟩
  obtain ⟨s, A, HB, j, lift, hA, hj, hjval, hlift, hliftval⟩ :=
    exists_hamiltonZero_finitePL_boundary_coordinates hd hphi he hN hne
      huv hab halpha hthird hsecond hfirst boundaryMap hvalue
  have hliftPL := polyhedralPL_terminalBoxAtlas_of_finitePiecewiseAffineOn hlift
  have hlocalinj : IsLocallyInjective (fun z : A.space => lift z) := by
    intro z
    obtain ⟨U, hU, hzU, hinjU⟩ :=
      (hc.isLocalHomeomorph.comp HB.isLocalHomeomorph).isLocallyInjective z
    refine ⟨U, hU, hzU, ?_⟩
    intro y hy w hw heq
    apply hinjU hy hw
    apply Subtype.ext
    exact (hliftval y).symm.trans (heq.trans (hliftval w))
  obtain ⟨J, hJ, hJS⟩ := exists_finite_unitCubeSphere (ι := Fin 3)
  obtain ⟨bmap, hbmap, hbval⟩ := hB
  have hsphere (i : Fin n) : Nonempty (ChartwisePLSphere e (S i)) := by
    let q (z : V3) : (s → ℝ × V3) :=
      if hz : z ∈ Sphere then HB.symm (face i ⟨z, hz⟩) else 0
    have hq (z : Sphere) : q z = (HB.symm (face i z) : s → ℝ × V3) := by
      simp only [q, dif_pos z.property]
    have hqcont : ContinuousOn q Sphere := by
      rw [continuousOn_iff_continuous_domRestrict]
      exact (continuous_subtype_val.comp (HB.symm.continuous.comp (face i).continuous)).congr
        (fun z => (hq z).symm)
    have hqA : MapsTo q Sphere A.space := by
      intro z hz
      rw [hq ⟨z, hz⟩]
      exact (HB.symm (face i ⟨z, hz⟩)).property
    have hcompose : PolyhedralPLInCharts terminalBoxAtlas (lift ∘ q) Sphere := by
      apply (polyhedralPL_terminalBoxAtlas_of_finitePiecewiseAffineOn hbmap).congr
      intro z hz
      change bmap z = lift (q z)
      rw [hq ⟨z, hz⟩, hliftval, HB.apply_symm_apply]
      exact (hbval ⟨z, hz⟩).symm.trans (congrArg Subtype.val (hcoord i ⟨z, hz⟩)).symm
    have hqPL : FinitePiecewiseAffineOn q Sphere := by
      have h := hliftPL.finitePiecewiseAffineOn_lift_of_locallyInjective
        (plDomain_terminalBox huv hab halpha).compatible A hA hlocalinj J hJ
        (by simpa only [hJS] using hqcont) (by simpa only [hJS] using hqA)
        (by simpa only [hJS] using hcompose)
      simpa only [hJS] using h
    have hjq := hj.comp_finitePiecewiseAffineOn J hJ
      (by simpa only [hJS] using hqPL) (by simpa only [hJS] using hqA)
    refine ⟨⟨(hfi i).toHomeomorph, j ∘ q, ?_, ?_⟩⟩
    · intro z
      change j (q z) = f i z
      rw [hq z, hjval, HB.apply_symm_apply]
    · simpa only [hJS] using hjq
  refine ⟨n, S, hSdis, hSwhole, fun i =>
    ⟨hScompact i, ⟨f i z0, z0, rfl⟩, hsphere i, ?_⟩⟩
  intro x hx
  have hclopen : IsClopen ((Subtype.val : frontier N → X0) ⁻¹' S i) := by
    have h := Poincare.Topology.isClopen_part_of_finite_closed_partition
      S (fun i => (hScompact i).isClosed) hSdis i
    exact h.preimage (Homeomorph.setCongr hSwhole.symm).continuous
  apply le_antisymm
  · rw [connectedComponentIn_eq_image (hSS i hx)]
    rintro _ ⟨y, hy, rfl⟩
    exact hclopen.connectedComponent_subset hx hy
  · exact (isPreconnected_range (hfc i)).subset_connectedComponentIn hx (hSS i)

end PoincareConjecture.M76
