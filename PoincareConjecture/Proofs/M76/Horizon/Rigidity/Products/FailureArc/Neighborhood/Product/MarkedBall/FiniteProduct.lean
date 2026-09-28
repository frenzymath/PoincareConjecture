import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Product.MarkedBall.RelativeExtension
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderBaseProductBall
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallImages
import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionSphericalBall

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn.Annuli.MarkedBall

local notation "P2" => (ℝ × ℝ)
local notation "I" => Icc (0 : ℝ) 1

theorem exists_finite_product
    {E F V : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {c q : Set E} (hc : IsFinitePLBallPair P2 c q)
    {a : E × ℝ → F} (ha : FinitePiecewiseAffineOn a (q ×ˢ I)) (hai : InjOn a (q ×ˢ I))
    {g : E → F} (hg : FinitePiecewiseAffineOn g c) (hgi : InjOn g c)
    (hbottom : ∀ z ∈ q, a (z,0) = g z)
    {B Top Qtop : Set F}
    (hB : IsFinitePLBallPair V B ((a '' (q ×ˢ I)) ∪ ((g '' c) ∪ Top)))
    (hTop : IsFinitePLBallPair P2 Top Qtop)
    (htoprim : Qtop = a '' (q ×ˢ {(1 : ℝ)}))
    (hcontact : Top ∩ (a '' (q ×ˢ I)) = Qtop)
    (hbasecontact : (g '' c) ∩ (a '' (q ×ˢ I)) = a '' (q ×ˢ {(0 : ℝ)}))
    (hdis : Disjoint Top (g '' c)) :
    ∃ H : (c ×ˢ I : Set (E × ℝ)) ≃ₜ B, H.IsFinitePL ∧
      (∀ z (hz : z ∈ c), (H ⟨(z,0),⟨hz,by norm_num⟩⟩ : F) = g z) ∧
      (∀ p (hp : p ∈ q ×ˢ I), (H ⟨p,⟨hc.1 hp.1,hp.2⟩⟩ : F) = a p) ∧
      (∀ p : (c ×ˢ I : Set (E × ℝ)), (H p : F) ∈ Top ↔ (p : E × ℝ).2 = 1) ∧
      (∀ p : (c ×ˢ I : Set (E × ℝ)), (H p : F) ∈ g '' c ↔ (p : E × ℝ).2 = 0) ∧
      ∀ p : (c ×ˢ I : Set (E × ℝ)), (H p : F) ∈ a '' (q ×ˢ I) ↔ (p : E × ℝ).1 ∈ q := by
  have hcap₀ := hc.prod_singleton (0 : ℝ)
  have hcap₁ := hc.prod_singleton (1 : ℝ)
  have hcap₀copy := hcap₀
  obtain ⟨_,_,_,_,_,_,⟨_,⟨K,hK,hKs,_⟩,_⟩,_⟩ := hcap₀copy
  let bmap : E × ℝ → F := fun p ↦ g p.1
  have hbmap : FinitePiecewiseAffineOn bmap (c ×ˢ {(0 : ℝ)}) :=
    hg.comp ⟨K,hK,hKs,K.affineOnFaces_affine (ContinuousLinearMap.fst ℝ E ℝ).toContinuousAffineMap⟩
      (fun _ hp ↦ hp.1)
  have hbmi : InjOn bmap (c ×ˢ {(0 : ℝ)}) := by
    intro p hp s hs heq
    exact Prod.ext (hgi hp.1 hs.1 heq) (hp.2.trans hs.2.symm)
  have hbimage : bmap '' (c ×ˢ {(0 : ℝ)}) = g '' c := by
    ext y
    constructor
    · rintro ⟨p,hp,rfl⟩; exact ⟨p.1,hp.1,rfl⟩
    · rintro ⟨z,hz,rfl⟩; exact ⟨(z,0),⟨hz,rfl⟩,rfl⟩
  have hbex := hbmap.exists_homeomorph_image hbmi
  rw [hbimage] at hbex
  obtain ⟨b,hb,hbval⟩ := hbex
  obtain ⟨A,hA,hAval⟩ := ha.exists_homeomorph_image hai
  have hprod := hc.prod (isFinitePLBallPair_Icc (show (0 : ℝ) < 1 from zero_lt_one))
  have hbd : (q ×ˢ I) ∪ (c ×ˢ ({0,1} : Set ℝ)) =
      (q ×ˢ I) ∪ ((c ×ˢ {(0 : ℝ)}) ∪ (c ×ˢ {(1 : ℝ)})) := by
    ext p
    simp only [mem_union,mem_prod,mem_insert_iff,mem_singleton_iff]
    tauto
  rw [hbd] at hprod
  have htopmeet : (c ×ˢ {(1 : ℝ)}) ∩ (q ×ˢ I) = q ×ˢ {(1 : ℝ)} := by
    ext p
    constructor
    · exact fun h ↦ ⟨h.2.1,h.1.2⟩
    · intro h; exact ⟨⟨hc.1 h.1,h.2⟩,h.1,by rw [show p.2=1 from h.2]; norm_num⟩
  have hsrcdis : Disjoint (c ×ˢ {(1 : ℝ)}) (c ×ˢ {(0 : ℝ)}) := by
    apply disjoint_left.mpr
    intro p hp hs
    have h1 : p.2=1 := hp.2
    have h0 : p.2=0 := hs.2
    linarith
  have hoverlap (x : (c ×ˢ {(0 : ℝ)} : Set (E × ℝ))) :
      (x : E × ℝ) ∈ q ×ˢ I ↔ (b x : F) ∈ a '' (q ×ˢ I) := by
    rw [hbval]
    constructor
    · intro hx
      refine ⟨(x.1.1,0),⟨hx.1,by norm_num⟩,?_⟩
      exact hbottom _ hx.1
    · intro hx
      have hm : bmap x ∈ (g '' c) ∩ (a '' (q ×ˢ I)) := ⟨⟨x.1.1,x.property.1,rfl⟩,hx⟩
      obtain ⟨p,hp,hpval⟩ := hbasecontact.subset hm
      have hg : g p.1 = g x.1.1 := (hbottom p.1 hp.1).symm.trans
        ((congrArg a (show (p.1,0)=p from Prod.ext rfl hp.2.symm)).trans hpval)
      have heq := hgi (hc.1 hp.1) x.property.1 hg
      exact ⟨heq ▸ hp.1,by rw [show x.1.2=0 from x.property.2]; norm_num⟩
  have hagree (x : E × ℝ) (hx : x ∈ c ×ˢ {(0 : ℝ)}) (hy : x ∈ q ×ˢ I) :
      (b ⟨x,hx⟩ : F) = A ⟨x,hy⟩ := by
    rw [hbval,hAval]
    change g x.1 = a x
    rw [show x = (x.1,0) from Prod.ext rfl hx.2]
    exact (hbottom _ hy.1).symm
  have hrim (x : (q ×ˢ I : Set (E × ℝ))) :
      (x : E × ℝ) ∈ q ×ˢ {(1 : ℝ)} ↔ (A x : F) ∈ Qtop := by
    rw [hAval,htoprim]
    constructor
    · exact fun hx ↦ ⟨x,hx,rfl⟩
    · rintro ⟨p,hp,hpv⟩
      have hpi : p ∈ q ×ˢ I := ⟨hp.1,by rw [show p.2=1 from hp.2]; norm_num⟩
      exact (hai hpi x.property hpv) ▸ hp
  obtain ⟨H,hH,hHb,hHA,htop,hbase,hann⟩ := exists_relative_ball_extension hprod hB
    hcap₁ hTop htopmeet hcontact hsrcdis hdis b hb A hA hoverlap hagree hrim
  refine ⟨H,hH,?_,?_,?_,?_,?_⟩
  · intro z hz
    exact (hHb ⟨(z,0),⟨hz,rfl⟩⟩).trans (hbval _)
  · intro p hp
    exact (hHA ⟨p,hp⟩).trans (hAval _)
  · intro p
    simpa only [mem_prod,p.property.1,true_and,mem_singleton_iff] using (htop p).symm
  · intro p
    simpa only [mem_prod,p.property.1,true_and,mem_singleton_iff] using (hbase p).symm
  · intro p
    simpa only [mem_prod,p.property.2,and_true] using (hann p).symm

end PoincareConjecture.M76.Dehn.Annuli.MarkedBall
