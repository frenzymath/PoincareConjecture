import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.AnnularBallProduct
import PoincareConjecture.Proofs.M76.Triangulation.PLBallBoundaryDiskComplement
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallTopology









set_option autoImplicit false
open Set Geometry

namespace Set

local notation "P2" => (ℝ × ℝ)
local notation "P3" => ((ℝ × ℝ) × ℝ)
local notation "I" => Icc (0 : ℝ) 1

theorem IsFinitePLBallPair.product_with_annular_top
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {A a D d band : Set E}
    (hA : IsFinitePLBallPair P2 A a) (hD : IsFinitePLBallPair P2 D d)
    (hcover : D ∪ band = A) (hmeet : D ∩ band = d)
    (ha : a ⊆ band) (hdis : Disjoint a D) :
    ∃ C : Set (E × ℝ),
      C = ((a ×ˢ I) ∪ (A ×ˢ ({0, 1} : Set ℝ))) \
        ((A ×ˢ {(1 : ℝ)}) \ (a ×ˢ {(1 : ℝ)})) ∧
      IsFinitePLBallPair P2 C (a ×ˢ {(1 : ℝ)}) ∧
      IsFinitePLBallPair P2 (D ×ˢ {(1 : ℝ)}) (d ×ˢ {(1 : ℝ)}) ∧
      IsFinitePLBallPair P3 (A ×ˢ I)
        ((band ×ˢ {(1 : ℝ)}) ∪ (C ∪ (D ×ˢ {(1 : ℝ)}))) ∧
      C ∩ (band ×ˢ {(1 : ℝ)}) = a ×ˢ {(1 : ℝ)} ∧
      (D ×ˢ {(1 : ℝ)}) ∩ (band ×ˢ {(1 : ℝ)}) = d ×ˢ {(1 : ℝ)} ∧
      Disjoint (D ×ˢ {(1 : ℝ)}) C := by
  let S := (a ×ˢ I) ∪ (A ×ˢ ({0, 1} : Set ℝ))
  let C := S \ ((A ×ˢ {(1 : ℝ)}) \ (a ×ˢ {(1 : ℝ)}))
  have hprod : IsFinitePLBallPair P3 (A ×ˢ I) S :=
    hA.prod (isFinitePLBallPair_Icc (by norm_num : (0 : ℝ) < 1))
  have htop : A ×ˢ {(1 : ℝ)} ⊆ S := by
    rintro z ⟨hzA,hz1⟩
    exact Or.inr ⟨hzA,Or.inr hz1⟩
  obtain ⟨x,hx,_⟩ := hA.sdiff_nonempty
  have hout : (S \ (A ×ˢ {(1 : ℝ)})).Nonempty := by
    refine ⟨(x,0),Or.inr ⟨hx,Or.inl rfl⟩,?_⟩
    norm_num
  have hC : IsFinitePLBallPair P2 C (a ×ˢ {(1 : ℝ)}) :=
    hprod.boundary_disk_complement (by simp [Module.finrank_prod])
      (hA.prod_singleton 1) htop hout
  have hDA : D ⊆ A := subset_union_left.trans hcover.subset
  have hbandA : band ⊆ A := subset_union_right.trans hcover.subset
  have hCtop (z : E × ℝ) (hz1 : z.2 = 1) (hzA : z.1 ∈ A) :
      z ∈ C ↔ z.1 ∈ a := by
    constructor
    · intro hz
      by_contra hza
      exact hz.2 ⟨⟨hzA,hz1⟩,fun h => hza h.1⟩
    · intro hza
      exact ⟨htop ⟨hzA,hz1⟩,fun h => h.2 ⟨hza,hz1⟩⟩
  have hbound : (band ×ˢ {(1 : ℝ)}) ∪ (C ∪ (D ×ˢ {(1 : ℝ)})) = S := by
    apply Subset.antisymm
    · rintro z (hz | hz | hz)
      · exact htop ⟨hbandA hz.1,hz.2⟩
      · exact hz.1
      · exact htop ⟨hDA hz.1,hz.2⟩
    · intro z hz
      by_cases hzC : z ∈ C
      · exact Or.inr (Or.inl hzC)
      have hztop : z ∈ A ×ˢ {(1 : ℝ)} := by
        by_contra hn
        exact hzC ⟨hz,fun h => hn h.1⟩
      rcases hcover.symm.subset hztop.1 with hD | hband
      · exact Or.inr (Or.inr ⟨hD,hztop.2⟩)
      · exact Or.inl ⟨hband,hztop.2⟩
  refine ⟨C,rfl,hC,hD.prod_singleton 1,hbound.symm ▸ hprod,?_,?_,?_⟩
  · ext z
    constructor
    · intro hz
      exact ⟨(hCtop z hz.2.2 (hbandA hz.2.1)).mp hz.1,hz.2.2⟩
    · intro hz
      exact ⟨(hCtop z hz.2 (hA.1 hz.1)).mpr hz.1,ha hz.1,hz.2⟩
  · ext z
    constructor
    · exact fun hz => ⟨hmeet.subset ⟨hz.1.1,hz.2.1⟩,hz.1.2⟩
    · exact fun hz => ⟨⟨(hmeet.symm.subset hz.1).1,hz.2⟩,
        (hmeet.symm.subset hz.1).2,hz.2⟩
  · apply disjoint_left.mpr
    intro z hzD hzC
    exact disjoint_left.mp hdis ((hCtop z hzD.2 (hDA hzD.1)).mp hzC) hzD.1

end Set
