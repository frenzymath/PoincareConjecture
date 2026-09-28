import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.OriginalRegularRectangleFamily
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.OriginalFaceArcModels









set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76.PrismBelt

structure OriginalFaceRectangles
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
    (K : SimplicialComplex ℝ E) (g : E → X) (S : Set X) (s : Finset E) where
  Arc : Type
  finiteArc : Finite Arc
  arc : Arc → Set E
  rim : Arc → Set E
  arcBall : ∀ i, IsFinitePLBallPair ℝ (arc i) (rim i)
  arcDisjoint : Pairwise fun i j => Disjoint (arc i) (arc j)
  arcSubset : (⋃ i, arc i) ⊆ convexHull ℝ (s : Set E)
  arcPhysical : g '' (⋃ i, arc i) = S ∩ (g '' convexHull ℝ (s : Set E))
  arcRim : ∀ i, rim i = arc i ∩ intrinsicFrontier ℝ (convexHull ℝ (s : Set E))
  arcNonreturning : ∀ i a, a ⊆ s → a.card = 2 → ¬ rim i ⊆ convexHull ℝ (a : Set E)
  Region : Type
  finiteRegion : Finite Region
  carrier : Region → Set E
  cap : Region → Bool → Arc
  edge : Region → Bool → ℝ →ᴬ[ℝ] E
  lo : Region → Bool → ℝ
  hi : Region → Bool → ℝ
  exceptional : Set (ConnectedComponents (convexHull ℝ (s : Set E) \ ⋃ i, arc i : Set E))
  carrierInjective : Function.Injective carrier
  exceptionalFinite : exceptional.Finite
  exceptionalBound : exceptional.ncard ≤ 4
  regionLabels : ∀ x : (convexHull ℝ (s : Set E) \ ⋃ i, arc i : Set E),
    ConnectedComponents.mk x ∉ exceptional ↔ ∃! k, (x : E) ∈ carrier k \ ⋃ i, arc i
  capDistinct : ∀ k, cap k false ≠ cap k true
  regionBall : ∀ k, IsFinitePLBallPair (ℝ × ℝ) (carrier k)
    ((arc (cap k false) ∪ arc (cap k true)) ∪
      ((edge k false '' Icc (lo k false) (hi k false)) ∪
        (edge k true '' Icc (lo k true) (hi k true))))
  boundaryContact : ∀ k, carrier k ∩ intrinsicFrontier ℝ (convexHull ℝ (s : Set E)) =
    (edge k false '' Icc (lo k false) (hi k false)) ∪
      (edge k true '' Icc (lo k true) (hi k true))
  cutContact : ∀ k, carrier k ∩ (⋃ i, arc i) = arc (cap k false) ∪ arc (cap k true)
  componentClosure : ∀ k, ∀ x ∈ carrier k \ ⋃ i, arc i,
    x ∈ convexHull ℝ (s : Set E) \ ⋃ i, arc i ∧
    closure (connectedComponentIn (convexHull ℝ (s : Set E) \ ⋃ i, arc i) x) = carrier k
  edgeData : ∀ k side, Function.Injective (edge k side) ∧
    ({edge k side 0,edge k side 1} : Finset E) ∈ K.faces ∧
    ({edge k side 0,edge k side 1} : Finset E) ⊆ s ∧
    ({edge k side 0,edge k side 1} : Finset E).card = 2 ∧
    lo k side ∈ Ioo (0 : ℝ) 1 ∧ hi k side ∈ Ioo (0 : ℝ) 1 ∧ lo k side < hi k side ∧
    Disjoint (edge k side '' Ioo (lo k side) (hi k side)) (⋃ i, arc i) ∧
    edge k side (lo k side) ∈ ⋃ i, arc i ∧ edge k side (hi k side) ∈ ⋃ i, arc i
  rectangle : ∀ k, ∃ G : (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 : Set (ℝ × ℝ)) ≃ₜ carrier k,
    G.IsFinitePL ∧
    (∀ x, (G x : E) ∈ arc (cap k false) ↔ (x : ℝ × ℝ).2 = 0) ∧
    (∀ x, (G x : E) ∈ arc (cap k true) ↔ (x : ℝ × ℝ).2 = 1) ∧
    (∀ x, (G x : E) ∈ edge k false '' Icc (lo k false) (hi k false) ↔ (x : ℝ × ℝ).1 = 0) ∧
    (∀ x, (G x : E) ∈ edge k true '' Icc (lo k true) (hi k true) ↔ (x : ℝ × ℝ).1 = 1)

attribute [instance] OriginalFaceRectangles.finiteArc OriginalFaceRectangles.finiteRegion

theorem exists_original_face_rectangles
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X]
    (K : SimplicialComplex ℝ E) (g : E → X) (hgi : InjOn g K.space)
    {s : Finset E} (hs : s ∈ K.faces) (hs3 : s.card = 3)
    (Q : OpenPartialHomeomorph X (Fin 3 → ℝ)) (A : E →ᴬ[ℝ] (Fin 3 → ℝ))
    (hmap : MapsTo g (convexHull ℝ (s : Set E)) Q.source)
    (hA : EqOn (Q ∘ g) A (convexHull ℝ (s : Set E)))
    {S : Set X} (havoid : Disjoint S (g '' K.vertices))
    (hposition : InCircleFreeNonreturningTriangleGraphPosition Q S g s A) :
    Nonempty (OriginalFaceRectangles K g S s) := by
  classical
  obtain ⟨γ,hγ,d,r,hdis,hphysical,hsub,harcs⟩ :=
    hposition.exists_normal_arc_family_on_original_face K g hgi hs Q A hmap hA
  let : Finite γ := hγ
  have hvertex (i : γ) : Disjoint (d i) (s : Set E) := by
    refine disjoint_left.mpr ?_
    intro x hxd hxs
    have hxS := (hphysical.subset (mem_image_of_mem g (mem_iUnion.mpr ⟨i,hxd⟩))).1
    exact disjoint_left.mp havoid hxS (mem_image_of_mem g (K.face_subset_vertices hs hxs))
  obtain ⟨κ,hκ,M,caps,edge,lo,hi,exceptional,hMi,hexFin,hexCard,hlabels,hdata⟩ :=
    exists_original_regular_rectangle_family K hs hs3 d r (fun i => (harcs i).1)
      (fun i _ hx => hsub (mem_iUnion.mpr ⟨i,hx⟩)) (fun i => (harcs i).2.1)
      hdis hvertex (fun i => (harcs i).2.2)
  exact ⟨{
    Arc := γ, finiteArc := hγ, arc := d, rim := r,
    arcBall := fun i => (harcs i).1, arcDisjoint := hdis, arcSubset := hsub,
    arcPhysical := hphysical, arcRim := fun i => (harcs i).2.1,
    arcNonreturning := fun i => (harcs i).2.2,
    Region := κ, finiteRegion := hκ, carrier := M, cap := caps, edge := edge,
    lo := lo, hi := hi, exceptional := exceptional, carrierInjective := hMi,
    exceptionalFinite := hexFin, exceptionalBound := hexCard, regionLabels := hlabels,
    capDistinct := fun k => (hdata k).1,
    regionBall := fun k => (hdata k).2.1,
    boundaryContact := fun k => (hdata k).2.2.1,
    cutContact := fun k => (hdata k).2.2.2.1,
    componentClosure := fun k => (hdata k).2.2.2.2.1,
    edgeData := fun k => (hdata k).2.2.2.2.2.1,
    rectangle := fun k => (hdata k).2.2.2.2.2.2 }⟩

end PoincareConjecture.M76.PrismBelt
