import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.SpanningInsideQuarterBox








set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1
local notation "Rect" => Set.prod (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1)
local notation "Minus" => Set.prod (Set.prod (Icc (-1 : ℝ) 0) I) (Icc (0 : ℝ) 1)
local notation "Corners" => Set.prod ({0,1} : Set ℝ) ({-1,1} : Set ℝ)

theorem OriginalDiskProduct.exists_original_spanning_corner_sector
    {X ι V : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {e : ι → OpenPartialHomeomorph X V3} {E W S R : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e (E ∩ W) j)
    (hNfront : frontier (E ∩ W) = (E ∩ W) ∩ (frontier E ∪ S))
    (hPO : MapsTo P.map (Disk ×ˢ I) (interior R))
    {d U C : Set V} {a₀ a₁ : V}
    (hd : IsFinitePLBallPair P2 d (U ∪ C))
    (hU : IsFinitePLBallPair ℝ U {a₀,a₁})
    (hC : IsFinitePLBallPair ℝ C {a₀,a₁})
    (hab : a₀ ≠ a₁) (hUC : U ∩ C = {a₀,a₁})
    (H : Disk ≃ₜ d) (hH : H.IsFinitePL)
    (hHrim : ∀ z : Disk,(z : V2) ∈ Rim ↔ (H z : V) ∈ U ∪ C)
    {f : V → X} (hj : ∀ z : Disk,j z = f (H z))
    (hjU : ∀ z : Disk,j z ∈ frontier E ↔ (H z : V) ∈ U)
    (hjC : ∀ z : Disk,j z ∈ S ↔ (H z : V) ∈ C)
    (hmark : ∀ z ∈ Rim,∀ t ∈ I,
      (P.map (z,t) ∈ frontier E ↔ j z ∈ frontier E) ∧
      (P.map (z,t) ∈ S ↔ j z ∈ S))
    {k : V × ℝ → X}
    (hk : ∀ z (hz : z ∈ d ×ˢ I),k z = P.map (H.symm ⟨z.1,hz.1⟩,z.2 / 2))
    {r : P2 → X}
    (hr₀ : ∀ t ∈ I,r (0,t) = k (a₀,t))
    (hr₁ : ∀ t ∈ I,r (1,t) = k (a₁,t))
    {x : X} (hx : x ∈ r '' Corners) :
    ∃ a ∈ ({a₀,a₁} : Set V), ∃ (positive : Bool)
      (kWide : V × ℝ → X) (q : P2 → V) (u : C3 → X),
      (∀ z (hz : z ∈ d ×ˢ I),kWide z = P.map (H.symm ⟨z.1,hz.1⟩,z.2)) ∧
      FinitePiecewiseAffineOn q Rect ∧ InjOn q Rect ∧ MapsTo q Rect d ∧ q 0 = a ∧
      PolyhedralPLInCharts e u Minus ∧ InjOn u Minus ∧
      (∀ z,u z = kWide (q (z.2,-z.1.1),
        if positive then 1/2+z.1.2/4 else -(1/2+z.1.2/4))) ∧
      u 0 = x ∧ u '' Minus ⊆ (E ∩ W) ∩ interior R ∧
      (∀ z ∈ Minus,u z ∈ frontier E ↔ z.1.1 = 0) ∧
      (∀ z ∈ Minus,u z ∈ S ↔ z.2 = 0) ∧
      ∀ z ∈ Minus,u z ∈ P.map '' (Disk ×ˢ Icc (-1/2 : ℝ) (1/2)) ↔ z.1.2 ≤ 0 := by
  have hcorner (a b : V) (ha : a ∈ ({a₀,a₁} : Set V))
      (hU' : IsFinitePLBallPair ℝ U {a,b})
      (hC' : IsFinitePLBallPair ℝ C {a,b})
      (hab' : a ≠ b) (hUC' : U ∩ C = {a,b})
      (t : ℝ) (ht : t ∈ ({-1,1} : Set ℝ)) :
      ∃ endpoint ∈ ({a₀,a₁} : Set V), ∃ (positive : Bool)
        (kWide : V × ℝ → X) (q : P2 → V) (u : C3 → X),
        (∀ z (hz : z ∈ d ×ˢ I),kWide z = P.map (H.symm ⟨z.1,hz.1⟩,z.2)) ∧
        FinitePiecewiseAffineOn q Rect ∧ InjOn q Rect ∧ MapsTo q Rect d ∧ q 0 = endpoint ∧
        PolyhedralPLInCharts e u Minus ∧ InjOn u Minus ∧
        (∀ z,u z = kWide (q (z.2,-z.1.1),
          if positive then 1/2+z.1.2/4 else -(1/2+z.1.2/4))) ∧
        u 0 = k (a,t) ∧ u '' Minus ⊆ (E ∩ W) ∩ interior R ∧
        (∀ z ∈ Minus,u z ∈ frontier E ↔ z.1.1 = 0) ∧
        (∀ z ∈ Minus,u z ∈ S ↔ z.2 = 0) ∧
        ∀ z ∈ Minus,u z ∈ P.map '' (Disk ×ˢ Icc (-1/2 : ℝ) (1/2)) ↔ z.1.2 ≤ 0 := by
    obtain ⟨positive,htval⟩ : ∃ positive : Bool,t = if positive then (1 : ℝ) else -1 := by
      rcases ht with ht | ht
      · exact ⟨false,ht⟩
      · exact ⟨true,ht⟩
    obtain ⟨kWide,q,u,hw,hq,hqi,hqd,hq0,hu,hui,huval,hu0,huN,huF,huS,huB⟩ :=
      P.exists_marked_inside_quarter_box hNfront hd hU' hC' hab' hUC'
        H hH hHrim hj hjU hjC hmark positive
    have haD : a ∈ d := hq0 ▸ hqd (by
      change ((0 : ℝ) ∈ Icc 0 1) ∧ ((0 : ℝ) ∈ Icc 0 1)
      norm_num)
    have htI : t ∈ I := by rw [htval]; cases positive <;> norm_num
    have hsI : (if positive then (1/2 : ℝ) else -1/2) ∈ I := by
      cases positive <;> norm_num
    have hzero : u 0 = k (a,t) := by
      rw [hu0,hw _ ⟨haD,hsI⟩,hk _ ⟨haD,htI⟩]
      change P.map (H.symm ⟨a,haD⟩,if positive then (1/2 : ℝ) else -1/2) =
        P.map (H.symm ⟨a,haD⟩,t/2)
      rw [htval]
      cases positive <;> norm_num
    have huR : u '' Minus ⊆ interior R := by
      rintro _ ⟨z,hz,rfl⟩
      have hzq : (z.2,-z.1.1) ∈ Rect :=
        ⟨hz.2,⟨by linarith [hz.1.1.2],by linarith [hz.1.1.1]⟩⟩
      have hzt : (if positive then (1/2 : ℝ)+z.1.2/4 else -(1/2+z.1.2/4)) ∈ I := by
        change (-1 ≤ (if positive then (1/2 : ℝ)+z.1.2/4 else -(1/2+z.1.2/4))) ∧
          (if positive then (1/2 : ℝ)+z.1.2/4 else -(1/2+z.1.2/4)) ≤ 1
        split <;> constructor <;> linarith [hz.1.2.1,hz.1.2.2]
      rw [huval,hw _ ⟨hqd hzq,hzt⟩]
      exact hPO ⟨(H.symm ⟨q (z.2,-z.1.1),hqd hzq⟩).property,hzt⟩
    exact ⟨a,ha,positive,kWide,q,u,hw,hq,hqi,hqd,hq0,hu,hui,huval,hzero,
      fun y hy => ⟨huN hy,huR hy⟩,huF,huS,huB⟩
  obtain ⟨⟨s,t⟩,⟨hs,ht⟩,rfl⟩ := hx
  have htI : t ∈ I := by
    have ht' : t = -1 ∨ t = 1 := by simpa only [mem_insert_iff,mem_singleton_iff] using ht
    rcases ht' with rfl | rfl <;> norm_num
  rcases hs with hs | hs
  · change s = 0 at hs
    subst s
    rw [hr₀ t htI]
    exact hcorner a₀ a₁ (by simp) hU hC hab hUC t ht
  · change s = 1 at hs
    subst s
    rw [hr₁ t htI]
    exact hcorner a₁ a₀ (by simp) (by simpa only [pair_comm] using hU)
      (by simpa only [pair_comm] using hC) hab.symm
      (hUC.trans (Set.pair_comm _ _)) t ht

end PoincareConjecture.M76
