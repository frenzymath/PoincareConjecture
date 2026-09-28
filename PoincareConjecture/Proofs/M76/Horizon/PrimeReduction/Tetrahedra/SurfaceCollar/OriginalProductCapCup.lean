import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.AnnularDiskProductBall
import PoincareConjecture.Proofs.M76.Rigidity.OriginalDiskProduct
import PoincareConjecture.Proofs.M76.Mathlib.HamiltonHandleCubeBall
import PoincareConjecture.Proofs.M76.PrimeReduction.BallModelCoordinates
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Regions.PunctureBallTriangulation









set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1

theorem finitePLBallPair_product_cup
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {D q : Set E} (hD : IsFinitePLBallPair (ℝ × ℝ) D q)
    {a b : ℝ} (hab : a < b) (side : Bool) :
    IsFinitePLBallPair (ℝ × ℝ)
      ((D ×ˢ {if side then a else b}) ∪ (q ×ˢ Icc a b))
      (q ×ˢ {if side then b else a}) := by
  let s : Set (E × ℝ) := (q ×ˢ Icc a b) ∪ (D ×ˢ ({a,b} : Set ℝ))
  let t := if side then b else a
  let u := if side then a else b
  have htu : t ≠ u := by
    cases side
    · exact hab.ne
    · exact hab.ne'
  have htop : D ×ˢ {t} ⊆ s := by
    rintro z ⟨hz,ht⟩
    refine Or.inr ⟨hz,?_⟩
    rw [show z.2 = t from ht]
    cases side <;> simp [t]
  obtain ⟨x,hx,_⟩ := hD.sdiff_nonempty
  have hout : (s \ (D ×ˢ {t})).Nonempty := by
    refine ⟨(x,u),Or.inr ⟨hx,?_⟩,?_⟩
    · cases side <;> simp [u]
    · exact fun h => htu h.2.symm
  have hprod : IsFinitePLBallPair ((ℝ × ℝ) × ℝ) (D ×ˢ Icc a b) s :=
    hD.prod (isFinitePLBallPair_Icc hab)
  have hcup := hprod.boundary_disk_complement (by simp [Module.finrank_prod])
    (hD.prod_singleton t) htop hout
  have heq : s \ ((D ×ˢ {t}) \ (q ×ˢ {t})) = (D ×ˢ {u}) ∪ (q ×ˢ Icc a b) := by
    ext ⟨x,z⟩
    have hq := @hD.1 x
    cases side <;> simp only [s,t,u,Bool.false_eq_true,if_false,if_true,
      mem_sdiff,mem_union,mem_prod,mem_Icc,mem_insert_iff,mem_singleton_iff] <;>
      constructor
    · rintro ⟨h,hn⟩
      rcases h with h | ⟨hx,hz | hz⟩
      · exact Or.inr h
      · subst z
        have hxq : x ∈ q := by tauto
        exact Or.inr ⟨hxq,le_rfl,hab.le⟩
      · exact Or.inl ⟨hx,hz⟩
    · rintro (⟨hx,hz⟩ | ⟨hx,haz,hzb⟩)
      · subst z
        exact ⟨Or.inr ⟨hx,Or.inr rfl⟩,by tauto⟩
      · exact ⟨Or.inl ⟨hx,haz,hzb⟩,by tauto⟩
    · rintro ⟨h,hn⟩
      rcases h with h | ⟨hx,hz | hz⟩
      · exact Or.inr h
      · exact Or.inl ⟨hx,hz⟩
      · subst z
        have hxq : x ∈ q := by tauto
        exact Or.inr ⟨hxq,hab.le,le_rfl⟩
    · rintro (⟨hx,hz⟩ | ⟨hx,haz,hzb⟩)
      · subst z
        exact ⟨Or.inr ⟨hx,Or.inl rfl⟩,by tauto⟩
      · exact ⟨Or.inl ⟨hx,haz,hzb⟩,by tauto⟩
  exact heq ▸ hcup

namespace OriginalDiskProduct

theorem exists_original_product_cap_replacement
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e R j) (b : Bool) :
    let I := if b then Icc (0 : ℝ) (1/2) else Icc (-(1/2 : ℝ)) 0
    let t := if b then (1/2 : ℝ) else -(1/2)
    let C := (Disk ×ˢ {(0 : ℝ)}) ∪ (Rim ×ˢ I)
    IsFinitePLBallPair V2 C (Rim ×ˢ {t}) ∧
      PolyhedralPLInCharts e P.map C ∧ InjOn P.map C ∧
      P.map '' C = (j '' Disk) ∪ (P.map '' (Rim ×ˢ I)) ∧
      ∃ H : C ≃ₜ (Disk ×ˢ {t} : Set (V2 × ℝ)), H.IsFinitePL ∧
        (∀ x : C, (x : V2 × ℝ) ∈ Rim ×ˢ {t} → (H x : V2 × ℝ) = x) ∧
        ∀ x : C, (H x : V2 × ℝ) ∈ Rim ×ˢ {t} ↔ (x : V2 × ℝ) ∈ Rim ×ˢ {t} := by
  classical
  dsimp only
  let I := if b then Icc (0 : ℝ) (1/2) else Icc (-(1/2 : ℝ)) 0
  let t := if b then (1/2 : ℝ) else -(1/2)
  let C := (Disk ×ˢ {(0 : ℝ)}) ∪ (Rim ×ˢ I)
  have hD2 : IsFinitePLBallPair (ℝ × ℝ) Disk Rim := by
    exact isFinitePLBallPair_unit_cube.model_equiv (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)
  have hC2 : IsFinitePLBallPair (ℝ × ℝ) C (Rim ×ˢ {t}) := by
    cases b
    · exact finitePLBallPair_product_cup hD2 (by norm_num : -(1/2 : ℝ) < 0) false
    · exact finitePLBallPair_product_cup hD2 (by norm_num : (0 : ℝ) < 1/2) true
  have hC : IsFinitePLBallPair V2 C (Rim ×ˢ {t}) :=
    hC2.model_equiv (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm
  have hsub : C ⊆ Disk ×ˢ Icc (-1 : ℝ) 1 := by
    rintro ⟨x,u⟩ (⟨hx,hu⟩ | ⟨hx,hu⟩)
    · exact ⟨hx,by rw [show u = 0 from hu]; norm_num⟩
    · refine ⟨sphere_subset_closedBall hx,?_⟩
      cases b <;> dsimp [I] at hu <;> constructor <;> linarith [hu.1,hu.2]
  have hPL : PolyhedralPLInCharts e P.map C := by
    obtain ⟨K,_,hK,hKs,_,_⟩ := hC.exists_finite_carrier_and_rim_complexes
    rw [←hKs]
    exact P.polyhedral.restrict_finite K hK (hKs.subset.trans hsub)
  have him : P.map '' C = (j '' Disk) ∪ (P.map '' (Rim ×ˢ I)) := by
    rw [image_union]
    congr 1
    ext y
    constructor
    · rintro ⟨⟨x,u⟩,⟨hx,hu⟩,rfl⟩
      have hu0 : u = 0 := hu
      subst u
      rw [P.central x hx]
      exact mem_image_of_mem j hx
    · rintro ⟨x,hx,rfl⟩
      exact ⟨(x,0),⟨hx,rfl⟩,P.central x hx⟩
  have hend : IsFinitePLBallPair V2 (Disk ×ˢ {t}) (Rim ×ˢ {t}) :=
    isFinitePLBallPair_unit_cube.prod_singleton t
  have hrefl : (Homeomorph.refl (Rim ×ˢ {t} : Set (V2 × ℝ))).IsFinitePL := by
    obtain ⟨_,K,_,_,hK,hKs⟩ := hC.exists_finite_carrier_and_rim_complexes
    exact ⟨id,⟨K,hK,hKs,K.affineOnFaces_affine (ContinuousAffineMap.id ℝ (V2 × ℝ))⟩,
      fun _ => rfl⟩
  obtain ⟨H,hH,hHr,hHmem⟩ := hC.exists_extension hend (Homeomorph.refl _) hrefl
  refine ⟨hC,hPL,P.injective.mono hsub,him,H,hH,?_,fun x => (hHmem x).symm⟩
  intro x hx
  exact congrArg Subtype.val (hHr ⟨x,hx⟩)

end OriginalDiskProduct
end PoincareConjecture.M76
