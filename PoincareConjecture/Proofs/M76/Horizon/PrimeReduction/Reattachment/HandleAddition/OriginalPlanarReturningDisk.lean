import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.OriginalPlanarDiskComplement
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.PlanarReturningDiskSelection
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.PairedContactIntervals







set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76
local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)
noncomputable local instance originalPlanarReturningDiskDecidableEq : DecidableEq P2 :=
  fun _ _ => Classical.propDecidable _

open Classical in
theorem ChartwisePLSphere.exists_original_outermost_returning_disk
    {X α : Type*} [MetricSpace X]
    {e : α → OpenPartialHomeomorph X V3} {S E : Set X}
    (s : ChartwisePLSphere e S) (he : PLDomain e E)
    (K : SimplicialComplex ℝ P2) (hK : K.faces.Finite)
    {B J : Set P2}
    (p : P2 → X) (hp : PolyhedralPLInCharts e p K.space) (hpi : InjOn p K.space)
    (hps : p '' K.space = S ∩ E)
    (hproper : ∀ z ∈ K.space, p z ∈ frontier E ↔ z ∈ B)
    (hcross : ∀ x ∈ S ∩ frontier E, ∃ H : OpenPartialHomeomorph X V3,
      x ∈ H.source ∧ H x = 0 ∧
      (∀ i, (e i).symm.trans H ∈ piecewiseAffineGroupoid V3) ∧
      (∀ y ∈ H.source, y ∈ S ↔ H y 1 = 0) ∧
      ∀ y ∈ H.source, y ∈ frontier E ↔ H y 0 = 0)
    {f : P2 → X} (C : SurfaceIntersectionComponents J K.space f p B)
    (harcs : ∀ i, IsFinitePLBallPair ℝ (C.pieces i) (C.pieces i ∩ B))
    (i : C.right.vertexAbstractComplex.edgeGraph.ConnectedComponent)
    {D U : Set P2} (hD : IsFinitePLBallPair P2 D (U ∪ C.pieces i))
    (hU : IsFinitePLBallPair ℝ U (U ∩ C.pieces i))
    (hDK : D ⊆ K.space) (hDB : D ∩ B = U) :
    ∃ j, ∃ A V T : Set P2,
      IsFinitePLBallPair P2 A (V ∪ C.pieces j) ∧
      IsFinitePLBallPair ℝ V (V ∩ C.pieces j) ∧
      A ⊆ K.space ∧ A ∩ B = V ∧
      A ∩ (⋃ k, C.pieces k) = C.pieces j ∧
      IsCompact T ∧ A ∪ T = K.space ∧ A ∩ T = C.pieces j := by
  let := C.components_finite
  have hsub : ∀ j, C.pieces j ⊆ K.space := fun j x hx =>
    (C.right_space.subset (C.cover.symm.subset (mem_iUnion.mpr ⟨j,hx⟩))).1
  choose a b hab hends using fun j => (harcs j).exists_boundary_eq_pair
  have hball : ∀ j, IsFinitePLBallPair ℝ (C.pieces j) {a j,b j} :=
    fun j => hends j ▸ harcs j
  have haB : ∀ j, a j ∈ B := fun j =>
    ((hends j).symm.subset (Or.inl rfl)).2
  have hbB : ∀ j, b j ∈ B := fun j =>
    ((hends j).symm.subset (Or.inr rfl)).2
  have hproperArc : ∀ j, C.pieces j \ {a j,b j} ⊆ K.space \ B :=
    fun j x hx => ⟨hsub j hx.1,fun hxB => hx.2 ((hends j).subset ⟨hx.1,hxB⟩)⟩
  have hseedEnds : U ∩ C.pieces i = {a i,b i} := by
    rw [←hends i]
    ext x
    constructor
    · exact fun hx => ⟨hx.2,(hDB.symm.subset hx.1).2⟩
    · exact fun hx => ⟨hDB.subset ⟨hD.1 (Or.inr hx.1),hx.2⟩,hx.1⟩
  obtain ⟨T,hT,hcover,hDT⟩ := s.exists_planar_disk_complement he K hK p hp hpi
    hps hproper hcross hD hDK (fun x hx => (hDB.symm.subset hx).2)
    (C.topology i).1.isClosed
  obtain ⟨j,A,V,hA,hV,hAD,hAB,hVW,hcontact,_⟩ :=
    exists_outermost_planar_returning_disk C.pieces a b hball hab C.disjoint hsub
      haB hbB hproperArc i hD (hseedEnds ▸ hU) hDB hT.isClosed
      hcover.symm.subset hDT
  have hAK := hAD.trans hDK
  obtain ⟨T',hT',hcover',hAT'⟩ := s.exists_planar_disk_complement he K hK p hp hpi
    hps hproper hcross hA hAK (fun x hx => (hAB.symm.subset hx).2)
    (C.topology j).1.isClosed
  exact ⟨j,A,V,T',hA,hVW.symm ▸ hV,hAK,hAB,hcontact,hT',hcover',hAT'⟩

end PoincareConjecture.M76
