import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.SpanningMarkedDiskQuadrant
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.SpanningMarkedInsideBlock
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLProduct

set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1
local notation "Band" => Icc (-1 : ℝ) 1
local notation "Rect" => Set.prod (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1)
local notation "Quarter" => Set.prod (Set.prod (Icc (-1 : ℝ) 0) Band) (Icc (0 : ℝ) 1)

theorem exists_original_inside_quarter_box
    {X ι V : Type*} [TopologicalSpace X]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {e : ι → OpenPartialHomeomorph X V3} {N F S : Set X}
    {d U C : Set V} {a b : V}
    (hd : IsFinitePLBallPair P2 d (U ∪ C))
    (hU : IsFinitePLBallPair ℝ U {a,b}) (hC : IsFinitePLBallPair ℝ C {a,b})
    (hab : a ≠ b) (hUC : U ∩ C = {a,b})
    {k : V × ℝ → X} (hk : PolyhedralPLInCharts e k (d ×ˢ Band)) (hki : InjOn k (d ×ˢ Band))
    (hkN : MapsTo k (d ×ˢ Band) N)
    (hkF : ∀ z ∈ d ×ˢ Band,k z ∈ F ↔ z.1 ∈ U)
    (hkS : ∀ z ∈ d ×ˢ Band,k z ∈ S ↔ z.1 ∈ C)
    (positive : Bool) :
    ∃ (q : P2 → V) (u : C3 → X),
      FinitePiecewiseAffineOn q Rect ∧ InjOn q Rect ∧ MapsTo q Rect d ∧ q 0 = a ∧
      PolyhedralPLInCharts e u Quarter ∧ InjOn u Quarter ∧
      (∀ z,u z = k (q (z.2,-z.1.1),if positive then 1/2+z.1.2/4 else -(1/2+z.1.2/4))) ∧
      u 0 = k (a,if positive then (1/2 : ℝ) else -1/2) ∧
      u '' Quarter ⊆ N ∧
      (∀ z ∈ Quarter,u z ∈ F ↔ z.1.1 = 0) ∧
      (∀ z ∈ Quarter,u z ∈ S ↔ z.2 = 0) ∧
      ∀ z ∈ Quarter,u z ∈ k '' (d ×ˢ Icc (-1/2 : ℝ) (1/2)) ↔ z.1.2 ≤ 0 := by
  obtain ⟨q,hq,hqi,hqd,hq0,hqU,hqC⟩ := exists_marked_disk_endpoint_quadrant hd hU hC hab hUC
  let t : C3 →ᴬ[ℝ] ℝ := ContinuousAffineMap.const ℝ C3 (1/2 : ℝ) +
    (1/4 : ℝ) • ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ P2 ℝ)).toContinuousAffineMap
  let A : C3 →ᴬ[ℝ] (P2 × ℝ) :=
    ((ContinuousLinearMap.snd ℝ P2 ℝ).toContinuousAffineMap.prod
      (-((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ P2 ℝ)).toContinuousAffineMap)).prod
      (if positive then t else -t)
  have hAvalue (z : C3) : A z = ((z.2,-z.1.1),
      if positive then 1/2+z.1.2/4 else -(1/2+z.1.2/4)) := by
    apply Prod.ext
    · rfl
    · cases positive
      · change -((1/2 : ℝ)+(1/4)*z.1.2) = -(1/2+z.1.2/4)
        ring
      · change (1/2 : ℝ)+(1/4)*z.1.2 = 1/2+z.1.2/4
        ring
  have hAmap (z : C3) (hz : z ∈ Quarter) : A z ∈ Rect ×ˢ Band := by
    rw [hAvalue]
    refine ⟨⟨hz.2,⟨by linarith [hz.1.1.2],by linarith [hz.1.1.1]⟩⟩,?_⟩
    change -1 ≤ (if positive then 1/2+z.1.2/4 else -(1/2+z.1.2/4)) ∧
      (if positive then 1/2+z.1.2/4 else -(1/2+z.1.2/4)) ≤ 1
    split <;> constructor <;> linarith [hz.1.2.1,hz.1.2.2]
  have hAf : FinitePiecewiseAffineOn A Quarter := by
    obtain ⟨_,_,_,_,_,_,⟨_,⟨K,hK,hKs,_⟩,_⟩,_⟩ :=
      ((isFinitePLBallPair_Icc (by norm_num : (-1 : ℝ) < 0)).prod
        (isFinitePLBallPair_Icc (by norm_num : (-1 : ℝ) < 1))).prod
        (isFinitePLBallPair_Icc (by norm_num : (0 : ℝ) < 1))
    exact ⟨K,hK,hKs,K.affineOnFaces_affine A⟩
  have hid : FinitePiecewiseAffineOn (id : ℝ → ℝ) Band := by
    obtain ⟨_,_,_,_,_,_,⟨_,⟨K,hK,hKs,_⟩,_⟩,_⟩ := isFinitePLBallPair_Icc (by norm_num : (-1 : ℝ) < 1)
    exact ⟨K,hK,hKs,K.affineOnFaces_affine (ContinuousAffineMap.id ℝ ℝ)⟩
  let g := Prod.map q (id : ℝ → ℝ) ∘ A
  have hg : FinitePiecewiseAffineOn g Quarter := (hq.prodMap hid).comp hAf hAmap
  have hgval (z : C3) : g z = (q (z.2,-z.1.1),
      if positive then 1/2+z.1.2/4 else -(1/2+z.1.2/4)) := by
    change Prod.map q id (A z) = _
    rw [hAvalue]
    rfl
  have hgd (z : C3) (hz : z ∈ Quarter) : g z ∈ d ×ˢ Band :=
    ⟨hqd (hAmap z hz).1,(hAmap z hz).2⟩
  have hgi : InjOn g Quarter := by
    intro z hz w hw heq
    have heq' := heq
    rw [hgval,hgval] at heq'
    have hh := hqi (hAmap z hz).1 (hAmap w hw).1 (congrArg Prod.fst heq')
    have ht := congrArg Prod.snd heq'
    have h0 : z.1.1 = w.1.1 := by have h := congrArg Prod.snd hh; change -z.1.1 = -w.1.1 at h; linarith
    have h1 : z.1.2 = w.1.2 := by dsimp at ht; split at ht <;> linarith
    exact Prod.ext (Prod.ext h0 h1) (congrArg Prod.fst hh)
  let u := k ∘ g
  have hu : PolyhedralPLInCharts e u Quarter := by
    obtain ⟨K,hK,hKs,hKf⟩ := hg
    rw [←hKs]
    exact hk.comp_finitePiecewiseAffineOn K hK ⟨K,hK,rfl,hKf⟩ (fun z hz => hgd z (hKs.subset hz))
  have hui : InjOn u Quarter := fun z hz w hw heq => hgi hz hw (hki (hgd z hz) (hgd w hw) heq)
  refine ⟨q,u,hq,hqi,hqd,hq0,hu,hui,fun z => congrArg k (hgval z),?_,?_,?_,?_,?_⟩
  · change k (g 0) = _
    rw [hgval]
    have h00 : ((0 : C3).2,-(0 : C3).1.1) = (0 : P2) := by ext <;> simp
    rw [h00,hq0]
    congr 1
    apply Prod.ext
    · rfl
    · split <;> norm_num
  · rintro _ ⟨z,hz,rfl⟩
    exact hkN (hgd z hz)
  · intro z hz
    change k (g z) ∈ F ↔ _
    rw [hkF _ (hgd z hz),hgval]
    exact (hqU (z.2,-z.1.1) (hAmap z hz).1).trans neg_eq_zero
  · intro z hz
    change k (g z) ∈ S ↔ _
    rw [hkS _ (hgd z hz),hgval]
    exact hqC (z.2,-z.1.1) (hAmap z hz).1
  · intro z hz
    have hm : u z ∈ k '' (d ×ˢ Icc (-1/2 : ℝ) (1/2)) ↔ (g z).2 ∈ Icc (-1/2 : ℝ) (1/2) := by
      constructor
      · rintro ⟨w,hw,heq⟩
        have hwI : w ∈ d ×ˢ Band := ⟨hw.1,by constructor <;> linarith [hw.2.1,hw.2.2]⟩
        have hh := hki hwI (hgd z hz) heq
        exact hh ▸ hw.2
      · exact fun h => ⟨g z,⟨(hgd z hz).1,h⟩,rfl⟩
    rw [hm,hgval]
    change ((-1/2 : ℝ) ≤ (if positive then 1/2+z.1.2/4 else -(1/2+z.1.2/4)) ∧
      (if positive then 1/2+z.1.2/4 else -(1/2+z.1.2/4)) ≤ 1/2) ↔ z.1.2 ≤ 0
    split <;> constructor <;> intro h
    · linarith [h.2]
    · constructor <;> linarith [hz.1.2.1]
    · linarith [h.1]
    · constructor <;> linarith [hz.1.2.1]

theorem OriginalDiskProduct.exists_marked_inside_quarter_box
    {X ι V : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {e : ι → OpenPartialHomeomorph X V3} {N E S : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e N j)
    (hNfront : frontier N = N ∩ (frontier E ∪ S))
    {d U C : Set V} {a b : V}
    (hd : IsFinitePLBallPair P2 d (U ∪ C))
    (hU : IsFinitePLBallPair ℝ U {a,b}) (hC : IsFinitePLBallPair ℝ C {a,b})
    (hab : a ≠ b) (hUC : U ∩ C = {a,b})
    (H : Disk ≃ₜ d) (hH : H.IsFinitePL)
    (hHrim : ∀ z : Disk,(z : V2) ∈ Rim ↔ (H z : V) ∈ U ∪ C)
    {f : V → X} (hj : ∀ z : Disk,j z = f (H z))
    (hjU : ∀ z : Disk,j z ∈ frontier E ↔ (H z : V) ∈ U)
    (hjC : ∀ z : Disk,j z ∈ S ↔ (H z : V) ∈ C)
    (hmark : ∀ z ∈ Rim,∀ t ∈ Band,
      (P.map (z,t) ∈ frontier E ↔ j z ∈ frontier E) ∧
      (P.map (z,t) ∈ S ↔ j z ∈ S)) (positive : Bool) :
    ∃ (k : V × ℝ → X) (q : P2 → V) (u : C3 → X),
      (∀ z (hz : z ∈ d ×ˢ Band),k z = P.map (H.symm ⟨z.1,hz.1⟩,z.2)) ∧
      FinitePiecewiseAffineOn q Rect ∧ InjOn q Rect ∧ MapsTo q Rect d ∧ q 0 = a ∧
      PolyhedralPLInCharts e u Quarter ∧ InjOn u Quarter ∧
      (∀ z,u z = k (q (z.2,-z.1.1),if positive then 1/2+z.1.2/4 else -(1/2+z.1.2/4))) ∧
      u 0 = k (a,if positive then (1/2 : ℝ) else -1/2) ∧
      u '' Quarter ⊆ N ∧
      (∀ z ∈ Quarter,u z ∈ frontier E ↔ z.1.1 = 0) ∧
      (∀ z ∈ Quarter,u z ∈ S ↔ z.2 = 0) ∧
      ∀ z ∈ Quarter,u z ∈ P.map '' (Disk ×ˢ Icc (-1/2 : ℝ) (1/2)) ↔ z.1.2 ≤ 0 := by
  obtain ⟨k,hk,hki,hkP,_,hkN,_,hkF,hkS,_⟩ :=
    P.exists_marked_bigon_inside_block hNfront (O := univ) (fun _ _ => mem_univ _)
      hd H hH hHrim hj hjU hjC hmark
  obtain ⟨q,u,hq,hqi,hqd,hq0,hu,hui,huval,hu0,huN,huF,huS,huQ⟩ :=
    exists_original_inside_quarter_box hd hU hC hab hUC hk hki
      (fun _ hz => (hkN hz).1) hkF hkS positive
  have himage : k '' (d ×ˢ Icc (-1/2 : ℝ) (1/2)) =
      P.map '' (Disk ×ˢ Icc (-1/2 : ℝ) (1/2)) := by
    apply Subset.antisymm
    · rintro _ ⟨z,hz,rfl⟩
      have hzB : z ∈ d ×ˢ Band := ⟨hz.1,by constructor <;> linarith [hz.2.1,hz.2.2]⟩
      exact ⟨(H.symm ⟨z.1,hz.1⟩,z.2),⟨(H.symm ⟨z.1,hz.1⟩).property,hz.2⟩,
        (hkP z hzB).symm⟩
    · rintro _ ⟨z,hz,rfl⟩
      have ht : z.2 ∈ Band := by constructor <;> linarith [hz.2.1,hz.2.2]
      refine ⟨((H ⟨z.1,hz.1⟩ : V),z.2),⟨(H ⟨z.1,hz.1⟩).property,hz.2⟩,?_⟩
      rw [hkP _ ⟨(H ⟨z.1,hz.1⟩).property,ht⟩]
      simp only [H.symm_apply_apply]
  refine ⟨k,q,u,hkP,hq,hqi,hqd,hq0,hu,hui,huval,hu0,huN,huF,huS,?_⟩
  simpa only [himage] using huQ

end PoincareConjecture.M76
