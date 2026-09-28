import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.SpanningMarkedInsideBlock








set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76
local notation "P2" => (ℝ × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "I" => Icc (-1 : ℝ) 1
local notation "Rect" => Set.prod (Icc (0 : ℝ) 1) (Icc (-1 : ℝ) 1)

theorem exists_original_marked_base_rectangle
    {X α F : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {e : α → OpenPartialHomeomorph X V3}
    {d U C : Set F} {a b : F} {S : Set X}
    (hU : IsFinitePLBallPair ℝ U {a,b}) (hab : a ≠ b)
    (hUd : U ⊆ d) (hUC : U ∩ C = {a,b}) {k : F × ℝ → X}
    (hk : PolyhedralPLInCharts e k (d ×ˢ I)) (hki : InjOn k (d ×ˢ I))
    (hkS : ∀ z ∈ d ×ˢ I, k z ∈ S ↔ z.1 ∈ C) :
    ∃ r : P2 → X, PolyhedralPLInCharts e r Rect ∧ InjOn r Rect ∧
      r '' Rect = k '' (U ×ˢ I) ∧
      r '' (Icc (0 : ℝ) 1 ×ˢ ({-1,1} : Set ℝ)) = k '' (U ×ˢ ({-1,1} : Set ℝ)) ∧
      (∀ t ∈ I,r (0,t) = k (a,t)) ∧ (∀ t ∈ I,r (1,t) = k (b,t)) ∧
      (∀ z ∈ Rect,r z ∈ S ↔ z.1 = 0 ∨ z.1 = 1) ∧
      ∃ j : V2 → X,
        PolyhedralPLInCharts e j (closedBall 0 1) ∧ InjOn j (closedBall 0 1) ∧
        j '' closedBall 0 1 = k '' (U ×ˢ I) ∧
        j '' sphere 0 1 = k '' (({a,b} ×ˢ I) ∪ (U ×ˢ ({-1,1} : Set ℝ))) := by
  obtain ⟨r,hr,hri,hrimage,hrSides,hr0,hr1,hbase⟩ :=
    exists_original_inside_block_base_rectangle hU hab hUd hk hki
  have haU : a ∈ U := hU.1 (by simp)
  have hbU : b ∈ U := hU.1 (by simp)
  have haC : a ∈ C := (hUC.symm.subset (by simp)).2
  have hbC : b ∈ C := (hUC.symm.subset (by simp)).2
  refine ⟨r,hr,hri,hrimage,hrSides,hr0,hr1,?_,hbase⟩
  intro z hz
  constructor
  · intro hS
    obtain ⟨w,hw,hwz⟩ := hrimage.subset ⟨z,hz,rfl⟩
    have hwC := (hkS w ⟨hUd hw.1,hw.2⟩).mp (hwz.symm ▸ hS)
    have hab' : w.1 = a ∨ w.1 = b := hUC.subset ⟨hw.1,hwC⟩
    rcases hab' with ha | hb
    · left
      have heq : r (0,w.2) = r z := by rw [hr0 w.2 hw.2,←ha]; exact hwz
      exact (congrArg Prod.fst (hri ⟨by norm_num,hw.2⟩ hz heq)).symm
    · right
      have heq : r (1,w.2) = r z := by rw [hr1 w.2 hw.2,←hb]; exact hwz
      exact (congrArg Prod.fst (hri ⟨by norm_num,hw.2⟩ hz heq)).symm
  · rintro (h0 | h1)
    · have heq : z = (0,z.2) := Prod.ext h0 rfl
      rw [heq,hr0 z.2 hz.2]
      exact (hkS (a,z.2) ⟨hUd haU,hz.2⟩).mpr haC
    · have heq : z = (1,z.2) := Prod.ext h1 rfl
      rw [heq,hr1 z.2 hz.2]
      exact (hkS (b,z.2) ⟨hUd hbU,hz.2⟩).mpr hbC

theorem mapsTo_interior_of_frontier_contact
    {X F : Type*} [TopologicalSpace X]
    {R E : Set X} (hER : E ⊆ R) {d U : Set F} {f : F → X}
    (hfE : MapsTo f d E) (hfront : f '' d ∩ frontier E = f '' U)
    (hU : f '' U ⊆ interior R) : MapsTo f d (interior R) := by
  intro z hz
  by_cases hzf : f z ∈ frontier E
  · exact hU (hfront.subset ⟨⟨z,hz,rfl⟩,hzf⟩)
  · exact interior_mono hER ((mem_interior_iff_notMem_frontier (hfE hz)).mpr hzf)

end PoincareConjecture.M76
