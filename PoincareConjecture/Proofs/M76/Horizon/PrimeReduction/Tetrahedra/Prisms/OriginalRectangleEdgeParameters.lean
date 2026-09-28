import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.RectangleEdgeGaps
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.SimplicialEdgeGapMatching
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Faces.Counting.CornerVertexComponents

set_option autoImplicit false
open Set Geometry TriangularRoofModel
namespace PoincareConjecture.M76.PrismBelt
open TriangleCorner

def rectangleEdgeCoordinate (b : Bool) : ℝ →ᴬ[ℝ] (ℝ × ℝ) :=
  if b then (ContinuousAffineMap.id ℝ ℝ).prod (ContinuousAffineMap.const ℝ ℝ 0)
  else (ContinuousAffineMap.const ℝ ℝ 0).prod (ContinuousAffineMap.id ℝ ℝ)

def originalRectangleEdge {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : (ℝ × ℝ) →ᴬ[ℝ] E) (c : Fin 3) (b : Bool) : ℝ →ᴬ[ℝ] E :=
  F.comp ((cornerMap c).comp (rectangleEdgeCoordinate b))

theorem rectangleEdgeCoordinate_injective (b : Bool) :
    Function.Injective (rectangleEdgeCoordinate b) := by
  intro s t h
  cases b
  · exact congrArg Prod.snd h
  · exact congrArg Prod.fst h

theorem rectangleEdgeCoordinate_image (b : Bool) (J : Set ℝ) :
    rectangleEdgeCoordinate b '' J = if b then J ×ˢ {0} else {0} ×ˢ J := by
  cases b
  · change (fun t : ℝ => (0,t)) '' J = {0} ×ˢ J
    ext p
    constructor
    · rintro ⟨t,ht,rfl⟩
      exact ⟨by simp,ht⟩
    · rintro ⟨hp0,hpJ⟩
      exact ⟨p.2,hpJ,Prod.ext (mem_singleton_iff.mp hp0).symm rfl⟩
  · change (fun t : ℝ => (t,0)) '' J = J ×ˢ {0}
    ext p
    constructor
    · rintro ⟨t,ht,rfl⟩
      exact ⟨ht,by simp⟩
    · rintro ⟨hpJ,hp0⟩
      exact ⟨p.1,hpJ,Prod.ext rfl (mem_singleton_iff.mp hp0).symm⟩

theorem originalRectangleEdge_injective
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : (ℝ × ℝ) →ᴬ[ℝ] E) (hF : Function.Injective F) (c : Fin 3) (b : Bool) :
    Function.Injective (originalRectangleEdge F c b) :=
  hF.comp ((cornerMap_involutive c).injective.comp (rectangleEdgeCoordinate_injective b))

theorem originalRectangleEdge_image
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : (ℝ × ℝ) →ᴬ[ℝ] E) (c : Fin 3) (b : Bool) (J : Set ℝ) :
    originalRectangleEdge F c b '' J =
      F '' (cornerMap c '' (if b then J ×ˢ {0} else {0} ×ˢ J)) := by
  rw [←rectangleEdgeCoordinate_image b J,image_image,image_image]
  rfl

theorem originalRectangleEdge_sides_disjoint
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : (ℝ × ℝ) →ᴬ[ℝ] E) (hF : Function.Injective F) (c : Fin 3)
    {a b p q : ℝ} (ha : 0 < a) :
    Disjoint (originalRectangleEdge F c false '' Icc b q)
      (originalRectangleEdge F c true '' Icc a p) := by
  apply disjoint_left.mpr
  rintro x ⟨t,ht,htx⟩ ⟨s,hs,hsx⟩
  have he : ((0,t) : ℝ × ℝ) = (s,0) :=
    (cornerMap_involutive c).injective (hF (htx.trans hsx.symm))
  have hs0 : s = 0 := (congrArg Prod.fst he).symm
  exact ha.not_ge (hs0 ▸ hs.1)

theorem originalRectangleEdge_original_face
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
    (K : SimplicialComplex ℝ E) {s : Finset E} (hs : s ∈ K.faces)
    (F : (ℝ × ℝ) →ᴬ[ℝ] E) (hF : Function.Injective F)
    (hverts : F '' vertices = (s : Set E)) (c : Fin 3) (b : Bool) :
    ({originalRectangleEdge F c b 0,originalRectangleEdge F c b 1} : Finset E) ∈ K.faces ∧
      ({originalRectangleEdge F c b 0,originalRectangleEdge F c b 1} : Finset E) ⊆ s ∧
      ({originalRectangleEdge F c b 0,originalRectangleEdge F c b 1} : Finset E).card = 2 := by
  have hv (t : ℝ) (ht : t = 0 ∨ t = 1) : originalRectangleEdge F c b t ∈ (s : Set E) := by
    apply hverts.subset
    apply mem_image_of_mem F
    apply (cornerMap_image_vertices c).subset
    apply mem_image_of_mem (cornerMap c)
    rcases ht with rfl | rfl <;> cases b <;> norm_num [rectangleEdgeCoordinate,vertices]
  have hsub : ({originalRectangleEdge F c b 0,originalRectangleEdge F c b 1} : Finset E) ⊆ s := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hv 0 (Or.inl rfl)
    · exact Finset.mem_singleton.mp hx ▸ hv 1 (Or.inr rfl)
  have hne : originalRectangleEdge F c b 0 ≠ originalRectangleEdge F c b 1 :=
    fun he => zero_ne_one (originalRectangleEdge_injective F hF c b he)
  exact ⟨K.down_closed hs hsub ⟨_,Finset.mem_insert_self _ _⟩,hsub,by simp [hne]⟩

theorem original_rectangle_edge_gaps
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : (ℝ × ℝ) →ᴬ[ℝ] E) (hF : Function.Injective F) (c : Fin 3)
    {M Q T D Z : Set E} {a b u v : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hu : 0 < u) (hv : 0 < v)
    (hDZ : Disjoint D Z)
    (hMQ : M ∩ Q = F '' (cornerMap c '' edgeIntervals a b u v))
    (hMT : M ∩ T = D ∪ Z)
    (hDQ : D ∩ Q = F '' (cornerMap c '' ({(0,b),(a,0)} : Set (ℝ × ℝ))))
    (hZQ : Z ∩ Q = F '' (cornerMap c '' ({(0,v),(u,0)} : Set (ℝ × ℝ)))) :
    a < u ∧ b < v ∧
      Disjoint (originalRectangleEdge F c false '' Ioo b v) T ∧
      Disjoint (originalRectangleEdge F c true '' Ioo a u) T ∧
      originalRectangleEdge F c false b ∈ T ∧ originalRectangleEdge F c true a ∈ T ∧
      originalRectangleEdge F c false v ∈ T ∧ originalRectangleEdge F c true u ∈ T := by
  have h := rectangle_edge_gaps (F ∘ cornerMap c) (hF.comp (cornerMap_involutive c).injective)
    ha hb hu hv hDZ (by simpa only [image_image,Function.comp_def] using hMQ) hMT
    (by simpa only [image_image,Function.comp_def] using hDQ)
    (by simpa only [image_image,Function.comp_def] using hZQ)
  rw [originalRectangleEdge_image,originalRectangleEdge_image]
  simp only [Bool.false_eq_true,if_false,if_true,image_image]
  exact h

end PoincareConjecture.M76.PrismBelt
