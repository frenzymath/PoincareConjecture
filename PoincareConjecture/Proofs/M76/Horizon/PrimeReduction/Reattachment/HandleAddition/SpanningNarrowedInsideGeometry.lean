import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.SpanningInsideGeometry
import PoincareConjecture.Proofs.M76.Rigidity.OriginalProductRescaling









set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76
local notation "P2" => (ℝ × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1
local notation "Rect" => Set.prod (Icc (0 : ℝ) 1) (Icc (-1 : ℝ) 1)

theorem OriginalDiskProduct.exists_narrowed_spanning_inside_geometry
    {X α F : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {e : α → OpenPartialHomeomorph X V3} {R E W S : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e (E ∩ W) j)
    (hNfront : frontier (E ∩ W) = (E ∩ W) ∩ (frontier E ∪ S))
    (hPO : MapsTo P.map (Disk ×ˢ I) (interior R))
    {d U C : Set F} {a b : F} (hd : IsFinitePLBallPair P2 d (U ∪ C))
    (hU : IsFinitePLBallPair ℝ U {a,b}) (hab : a ≠ b) (hUC : U ∩ C = {a,b})
    (H : Disk ≃ₜ d) (hH : H.IsFinitePL)
    (hHrim : ∀ z : Disk, (z : V2) ∈ Rim ↔ (H z : F) ∈ U ∪ C)
    {f : F → X} (hj : ∀ z : Disk, j z = f (H z))
    (hjU : ∀ z : Disk, j z ∈ frontier E ↔ (H z : F) ∈ U)
    (hjC : ∀ z : Disk, j z ∈ S ↔ (H z : F) ∈ C)
    (hmark : ∀ z ∈ Rim, ∀ t ∈ I,
      (P.map (z,t) ∈ frontier E ↔ j z ∈ frontier E) ∧
      (P.map (z,t) ∈ S ↔ j z ∈ S)) :
    ∃ (k : F × ℝ → X) (B T : Set X) (r : P2 → X),
      PolyhedralPLInCharts e k (d ×ˢ I) ∧ InjOn k (d ×ˢ I) ∧
      (∀ x ∈ d,k (x,0) = f x) ∧
      B = k '' (d ×ˢ I) ∧ T = k '' (((U ∪ C) ×ˢ I) ∪ (d ×ˢ ({-1,1} : Set ℝ))) ∧
      Nonempty (ChartwisePLBall e B T) ∧ B ⊆ E ∩ W ∧ B ⊆ interior R ∧
      (∀ z ∈ d ×ˢ I,k z ∈ frontier E ↔ z.1 ∈ U) ∧
      (∀ z ∈ d ×ˢ I,k z ∈ S ↔ z.1 ∈ C) ∧
      B ∩ S = k '' (C ×ˢ I) ∧
      PolyhedralPLInCharts e r Rect ∧ InjOn r Rect ∧ r '' Rect = k '' (U ×ˢ I) ∧
      r '' (Icc (0 : ℝ) 1 ×ˢ ({-1,1} : Set ℝ)) = k '' (U ×ˢ ({-1,1} : Set ℝ)) ∧
      B ∩ frontier E = r '' Rect ∧ T ∩ frontier E = r '' Rect ∧
      (T \ r '' Rect).Nonempty ∧ MapsTo r Rect ((frontier E ∩ W) ∩ interior R) ∧
      (∀ t ∈ I,r (0,t) = k (a,t)) ∧ (∀ t ∈ I,r (1,t) = k (b,t)) ∧
      (∀ z ∈ Rect,r z ∈ S ↔ z.1 = 0 ∨ z.1 = 1) ∧
      (∀ z (hz : z ∈ d ×ˢ I),k z = P.map (H.symm ⟨z.1,hz.1⟩,z.2 / 2)) := by
  obtain ⟨Q,hQ⟩ := P.exists_rescaled_product
    (show (0 : ℝ) < 1/2 by norm_num) (by norm_num)
  have hhalf {t : ℝ} (ht : t ∈ I) : (1/2 : ℝ)*t ∈ I := by
    constructor <;> linarith [ht.1,ht.2]
  have hQO : MapsTo Q.map (Disk ×ˢ I) (interior R) := by
    intro z hz
    rw [hQ]
    exact hPO ⟨hz.1,hhalf hz.2⟩
  have hQmark : ∀ z ∈ Rim,∀ t ∈ I,
      (Q.map (z,t) ∈ frontier E ↔ j z ∈ frontier E) ∧
      (Q.map (z,t) ∈ S ↔ j z ∈ S) := by
    intro z hz t ht
    rw [hQ]
    exact hmark z hz _ (hhalf ht)
  obtain ⟨k,B,T,r,hk,hki,hk0,hB,hT,hball,hBE,hBR,hkE,hkS,hBS,
    hr,hri,hrB,hrSides,hBF,hTF,hTout,hrMap,hr0,hr1,hrS,hkQ⟩ :=
    Q.exists_spanning_inside_geometry hNfront hQO hd hU hab hUC H hH hHrim hj hjU hjC hQmark
  refine ⟨k,B,T,r,hk,hki,hk0,hB,hT,hball,hBE,hBR,hkE,hkS,hBS,
    hr,hri,hrB,hrSides,hBF,hTF,hTout,hrMap,hr0,hr1,hrS,?_⟩
  intro z hz
  rw [hkQ z hz,hQ]
  congr 1
  ext <;> simp [div_eq_mul_inv,mul_comm]

end PoincareConjecture.M76
