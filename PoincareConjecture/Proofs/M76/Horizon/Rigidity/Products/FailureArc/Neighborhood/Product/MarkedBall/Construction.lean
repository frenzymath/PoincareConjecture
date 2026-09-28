import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Product.MarkedBall.Coordinates
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Product.MarkedBall.FiniteProduct
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLComposition
import PoincareConjecture.Proofs.M76.Mathlib.HamiltonHandleCubeBall



set_option autoImplicit false
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli.MarkedBall

local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Cube" => closedBall (0 : V3) 1
local notation "Rim" => sphere (0 : V3) 1
local notation "I" => Icc (0 : ℝ) 1

theorem exists_original_product
    {E₀ E₁ X ι : Type*}
    [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [FiniteDimensional ℝ E₀]
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁]
    [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3}
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    {c₀ q₀ : Set E₀} {c₁ q₁ : Set E₁}
    (hc₀ : IsFinitePLBallPair P2 c₀ q₀) (hc₁ : IsFinitePLBallPair P2 c₁ q₁)
    (K : SimplicialComplex ℝ (E₀ × ℝ)) (hK : K.faces.Finite) (hKs : K.space = q₀ ×ˢ I)
    {a : E₀ × ℝ → X} (ha : PolyhedralPLInCharts e a (q₀ ×ˢ I)) (hai : InjOn a (q₀ ×ˢ I))
    {g₀ : E₀ → X} {g₁ : E₁ → X}
    (hg₀ : PolyhedralPLInCharts e g₀ c₀) (hg₁ : PolyhedralPLInCharts e g₁ c₁)
    (hi₀ : InjOn g₀ c₀) (hi₁ : InjOn g₁ c₁)
    (hbottom : ∀ z ∈ q₀, a (z,0) = g₀ z)
    {B : Set X} (ball : ChartwisePLBall e B
      ((a '' (q₀ ×ˢ I)) ∪ ((g₀ '' c₀) ∪ (g₁ '' c₁))))
    (htoprim : g₁ '' q₁ = a '' (q₀ ×ˢ {(1 : ℝ)}))
    (hcontact : (g₁ '' c₁) ∩ (a '' (q₀ ×ˢ I)) = g₁ '' q₁)
    (hbasecontact : (g₀ '' c₀) ∩ (a '' (q₀ ×ˢ I)) = a '' (q₀ ×ˢ {(0 : ℝ)}))
    (hdis : Disjoint (g₁ '' c₁) (g₀ '' c₀)) :
    ∃ (H : (c₀ ×ˢ I : Set (E₀ × ℝ)) ≃ₜ B) (k : E₀ × ℝ → X),
      PolyhedralPLInCharts e k (c₀ ×ˢ I) ∧
      (∀ p : (c₀ ×ˢ I : Set (E₀ × ℝ)), k p = (H p : X)) ∧
      IsEmbedding (fun p : (c₀ ×ˢ I : Set (E₀ × ℝ)) ↦ k p) ∧ k '' (c₀ ×ˢ I) = B ∧
      (∀ z ∈ c₀, k (z,0) = g₀ z) ∧ EqOn k a (q₀ ×ˢ I) ∧
      (∀ p ∈ c₀ ×ˢ I, k p ∈ g₁ '' c₁ ↔ p.2 = 1) ∧
      (∀ p ∈ c₀ ×ˢ I, k p ∈ g₀ '' c₀ ↔ p.2 = 0) ∧
      ∀ p ∈ c₀ ×ˢ I, k p ∈ a '' (q₀ ×ˢ I) ↔ p.1 ∈ q₀ := by
  have hbi : InjOn ball.map Cube := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (ball.isEmbedding.injective (a₁ := ⟨x,hx⟩) (a₂ := ⟨y,hy⟩) hxy)
  have hc₀copy := hc₀
  have hc₁copy := hc₁
  obtain ⟨_,_,_,_,_,_,⟨_,⟨K₀,hK₀,hK₀s,_⟩,_⟩,_⟩ := hc₀copy
  obtain ⟨_,_,_,_,_,_,⟨_,⟨K₁,hK₁,hK₁s,_⟩,_⟩,_⟩ := hc₁copy
  have haB : MapsTo a K.space B := by
    intro p hp
    exact ball.boundary_subset (Or.inl ⟨p,hKs.subset hp,rfl⟩)
  have hg₀B : MapsTo g₀ K₀.space B := by
    intro p hp
    exact ball.boundary_subset (Or.inr (Or.inl ⟨p,hK₀s.subset hp,rfl⟩))
  have hg₁B : MapsTo g₁ K₁.space B := by
    intro p hp
    exact ball.boundary_subset (Or.inr (Or.inr ⟨p,hK₁s.subset hp,rfl⟩))
  obtain ⟨v,hv,hvmap,hvval⟩ := ball.exists_finite_coordinates hcompat K hK (hKs.symm ▸ ha) haB
  obtain ⟨u₀,hu₀,hu₀map,hu₀val⟩ := ball.exists_finite_coordinates hcompat K₀ hK₀
    (hK₀s.symm ▸ hg₀) hg₀B
  obtain ⟨u₁,hu₁,hu₁map,hu₁val⟩ := ball.exists_finite_coordinates hcompat K₁ hK₁
    (hK₁s.symm ▸ hg₁) hg₁B
  rw [hKs] at hv hvmap hvval
  rw [hK₀s] at hu₀ hu₀map hu₀val
  rw [hK₁s] at hu₁ hu₁map hu₁val
  have hvi : InjOn v (q₀ ×ˢ I) := fun x hx y hy hxy ↦
    hai hx hy ((hvval hx).symm.trans ((congrArg ball.map hxy).trans (hvval hy)))
  have hu₀i : InjOn u₀ c₀ := fun x hx y hy hxy ↦
    hi₀ hx hy ((hu₀val hx).symm.trans ((congrArg ball.map hxy).trans (hu₀val hy)))
  have hu₁i : InjOn u₁ c₁ := fun x hx y hy hxy ↦
    hi₁ hx hy ((hu₁val hx).symm.trans ((congrArg ball.map hxy).trans (hu₁val hy)))
  have hav : ball.map '' (v '' (q₀ ×ˢ I)) = a '' (q₀ ×ˢ I) := by
    rw [← image_comp]; exact image_congr hvval
  have hgv₀ : ball.map '' (u₀ '' c₀) = g₀ '' c₀ := by
    rw [← image_comp]; exact image_congr hu₀val
  have hgv₁ : ball.map '' (u₁ '' c₁) = g₁ '' c₁ := by
    rw [← image_comp]; exact image_congr hu₁val
  have hgvq₁ : ball.map '' (u₁ '' q₁) = g₁ '' q₁ := by
    rw [← image_comp]; exact image_congr (hu₁val.mono hc₁.1)
  have hlevel (t : ℝ) (ht : t ∈ I) :
      ball.map '' (v '' (q₀ ×ˢ {t})) = a '' (q₀ ×ˢ {t}) := by
    rw [← image_comp]
    apply image_congr (hvval.mono _)
    exact prod_mono Subset.rfl (singleton_subset_iff.mpr ht)
  have hset {A C : Set V3} (hA : A ⊆ Cube) (hC : C ⊆ Cube)
      (heq : ball.map '' A = ball.map '' C) : A=C := by
    ext x
    constructor
    · intro hx
      obtain ⟨y,hy,hyx⟩ := heq.subset (mem_image_of_mem ball.map hx)
      exact (hbi (hC hy) (hA hx) hyx) ▸ hy
    · intro hx
      obtain ⟨y,hy,hyx⟩ := heq.symm.subset (mem_image_of_mem ball.map hx)
      exact (hbi (hA hy) (hC hx) hyx) ▸ hy
  have hbottom' (z : E₀) (hz : z ∈ q₀) : v (z,0) = u₀ z := by
    have hzI : (z,(0 : ℝ)) ∈ q₀ ×ˢ I := ⟨hz,by norm_num⟩
    exact hbi (hvmap hzI) (hu₀map (hc₀.1 hz))
      ((hvval hzI).trans ((hbottom z hz).trans (hu₀val (hc₀.1 hz)).symm))
  have hboundary : Rim = (v '' (q₀ ×ˢ I)) ∪ ((u₀ '' c₀) ∪ (u₁ '' c₁)) := by
    apply hset sphere_subset_closedBall
      (union_subset (image_subset_iff.mpr hvmap)
        (union_subset (image_subset_iff.mpr hu₀map) (image_subset_iff.mpr hu₁map)))
    rw [ball.image_sphere,image_union,image_union,hav,hgv₀,hgv₁]
  have hcube := isFinitePLBallPair_unit_cube (ι := Fin 3)
  rw [hboundary] at hcube
  have htop := hc₁.image hu₁ hu₁i
  have htoprim' : u₁ '' q₁ = v '' (q₀ ×ˢ {(1 : ℝ)}) := by
    apply hset (image_subset_iff.mpr (hu₁map.mono_left hc₁.1))
      (image_subset_iff.mpr (hvmap.mono_left (prod_mono Subset.rfl (by norm_num))))
    rw [hgvq₁,hlevel 1 (by norm_num),htoprim]
  have hcontact' : (u₁ '' c₁) ∩ (v '' (q₀ ×ˢ I)) = u₁ '' q₁ := by
    apply hset (inter_subset_left.trans (image_subset_iff.mpr hu₁map))
      (image_subset_iff.mpr (hu₁map.mono_left hc₁.1))
    rw [hbi.image_inter (image_subset_iff.mpr hu₁map) (image_subset_iff.mpr hvmap),
      hgv₁,hav,hgvq₁,hcontact]
  have hbasecontact' : (u₀ '' c₀) ∩ (v '' (q₀ ×ˢ I)) = v '' (q₀ ×ˢ {(0 : ℝ)}) := by
    apply hset (inter_subset_left.trans (image_subset_iff.mpr hu₀map))
      (image_subset_iff.mpr (hvmap.mono_left (prod_mono Subset.rfl (by norm_num))))
    rw [hbi.image_inter (image_subset_iff.mpr hu₀map) (image_subset_iff.mpr hvmap),
      hgv₀,hav,hlevel 0 (by norm_num),hbasecontact]
  have hdis' : Disjoint (u₁ '' c₁) (u₀ '' c₀) := by
    apply disjoint_left.mpr
    intro x hx hy
    exact disjoint_left.mp hdis (hgv₁.subset (mem_image_of_mem ball.map hx))
      (hgv₀.subset (mem_image_of_mem ball.map hy))
  obtain ⟨H,hH,hH₀,hHa,hHt,hHb,hHann⟩ := exists_finite_product hc₀ hv hvi hu₀ hu₀i
    hbottom' hcube htop htoprim' hcontact' hbasecontact' hdis'
  obtain ⟨m,hm,hmval⟩ := hH
  have hmmap : MapsTo m (c₀ ×ˢ I) Cube := by
    intro p hp
    rw [← hmval ⟨p,hp⟩]
    exact (H ⟨p,hp⟩).property
  let k : E₀ × ℝ → X := ball.map ∘ m
  let G := H.trans ball.parametrization
  have hk : PolyhedralPLInCharts e k (c₀ ×ˢ I) := by
    obtain ⟨L,hL,hLs,hfaces⟩ := hm
    rw [← hLs]
    exact ball.piecewiseAffine.comp_finitePiecewiseAffineOn L hL ⟨L,hL,rfl,hfaces⟩
      (fun p hp ↦ hmmap (hLs.subset hp))
  have hkval (p : (c₀ ×ˢ I : Set (E₀ × ℝ))) : k p = (G p : X) := by
    change ball.map (m p) = (ball.parametrization (H p) : X)
    rw [← hmval p,ball.map_eq]
  have hkembed : IsEmbedding (fun p : (c₀ ×ˢ I : Set (E₀ × ℝ)) ↦ k p) := by
    have heq : (fun p : (c₀ ×ˢ I : Set (E₀ × ℝ)) ↦ k p) = Subtype.val ∘ G := funext hkval
    rw [heq]
    exact IsEmbedding.subtypeVal.comp G.isEmbedding
  have hkimage : k '' (c₀ ×ˢ I) = B := by
    ext y
    constructor
    · rintro ⟨p,hp,rfl⟩; rw [hkval ⟨p,hp⟩]; exact (G ⟨p,hp⟩).property
    · intro hy
      exact ⟨G.symm ⟨y,hy⟩,(G.symm ⟨y,hy⟩).property,
        (hkval _).trans (congrArg Subtype.val (G.apply_symm_apply ⟨y,hy⟩))⟩
  have hrecognize {A : Set V3} (hA : A ⊆ Cube) (p : (c₀ ×ˢ I : Set (E₀ × ℝ))) :
      k p ∈ ball.map '' A ↔ (H p : V3) ∈ A := by
    change ball.map (m p) ∈ ball.map '' A ↔ _
    rw [← hmval p]
    constructor
    · rintro ⟨x,hx,hxval⟩; exact (hbi (hA hx) (H p).property hxval) ▸ hx
    · exact fun hx ↦ ⟨H p,hx,rfl⟩
  refine ⟨G,k,hk,hkval,hkembed,hkimage,?_,?_,?_,?_,?_⟩
  · intro z hz
    change ball.map (m (z,0)) = g₀ z
    rw [← hmval ⟨(z,0),⟨hz,by norm_num⟩⟩,hH₀ z hz]
    exact hu₀val hz
  · intro p hp
    change ball.map (m p) = a p
    rw [← hmval ⟨p,⟨hc₀.1 hp.1,hp.2⟩⟩,hHa p hp]
    exact hvval hp
  · intro p hp
    rw [← hgv₁,hrecognize (image_subset_iff.mpr hu₁map) ⟨p,hp⟩]
    exact hHt ⟨p,hp⟩
  · intro p hp
    rw [← hgv₀,hrecognize (image_subset_iff.mpr hu₀map) ⟨p,hp⟩]
    exact hHb ⟨p,hp⟩
  · intro p hp
    rw [← hav,hrecognize (image_subset_iff.mpr hvmap) ⟨p,hp⟩]
    exact hHann ⟨p,hp⟩

end PoincareConjecture.M76.Dehn.Annuli.MarkedBall
