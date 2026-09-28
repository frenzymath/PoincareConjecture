import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.SpanningRelativeCap
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.SpanningMarkedInsideBlock

set_option autoImplicit false
set_option quotPrecheck false
open Set Metric Geometry
namespace PoincareConjecture.M76
local notation "P2" => (ℝ × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1
local notation "J" => Icc (0 : ℝ) 1
local notation "I" => Icc (-1 : ℝ) 1
local notation "Rect" => (J ×ˢ I)
local notation "RectRim" => ((({0,1} : Set ℝ) ×ˢ I) ∪ (J ×ˢ ({-1,1} : Set ℝ)))

theorem exists_relative_rectangle_cap_reparametrization
    {X α : Type*} [TopologicalSpace X] [T2Space X]
    {e : α → OpenPartialHomeomorph X V3} {D W O R E S : Set X}
    (H : Disk ≃ₜ Rect) (hH : H.IsFinitePL)
    (v : V2 → P2) (hvval : ∀ z : Disk,(H z : P2) = v z)
    (r : P2 → X) (c : V2 × ℝ → X)
    (hc : PolyhedralPLInCharts e c (Disk ×ˢ J)) (hci : InjOn c (Disk ×ˢ J))
    (hcDW : MapsTo c (Disk ×ˢ J) (D ∩ W))
    (hcO : MapsTo c (Disk ×ˢ J) (O ∩ interior R))
    (hc0 : ∀ z ∈ Disk,c (z,0) = r (v z))
    (hcE : ∀ z ∈ Disk ×ˢ J,c z ∈ E ↔ z.2 = 0)
    (hcS : ∀ z ∈ Disk ×ˢ J,c z ∈ S ↔ r (v z.1) ∈ S) :
    ∃ (u : P2 → V2) (k : P2 × ℝ → X),
      FinitePiecewiseAffineOn u Rect ∧ (∀ z : Rect,(H.symm z : V2) = u z) ∧
      (∀ z,k z = c (u z.1,z.2)) ∧ k '' (Rect ×ˢ J) = c '' (Disk ×ˢ J) ∧
      PolyhedralPLInCharts e k (Rect ×ˢ J) ∧ InjOn k (Rect ×ˢ J) ∧
      MapsTo k (Rect ×ˢ J) (D ∩ W) ∧ MapsTo k (Rect ×ˢ J) (O ∩ interior R) ∧
      (∀ z ∈ Rect,k (z,0) = r z) ∧
      (∀ z ∈ Rect ×ˢ J,k z ∈ E ↔ z.2 = 0) ∧
      (∀ z ∈ Rect ×ˢ J,k z ∈ S ↔ r z.1 ∈ S) ∧
      k '' (Rect ×ˢ J) ∩ E = r '' Rect ∧
      Nonempty (ChartwisePLBall e (k '' (Rect ×ˢ J))
        (k '' ((RectRim ×ˢ J) ∪ (Rect ×ˢ ({0,1} : Set ℝ))))) := by
  obtain ⟨u,hu,huval⟩ := hH.symm
  have humap : MapsTo u Rect Disk := by
    intro z hz
    rw [←huval ⟨z,hz⟩]
    exact (H.symm ⟨z,hz⟩).property
  have hvmap : MapsTo v Disk Rect := by
    intro z hz
    rw [←hvval ⟨z,hz⟩]
    exact (H ⟨z,hz⟩).property
  have hvu : LeftInvOn v u Rect := by
    intro z hz
    rw [←huval ⟨z,hz⟩,←hvval,H.apply_symm_apply]
  have huv : LeftInvOn u v Disk := by
    intro z hz
    rw [←hvval ⟨z,hz⟩,←huval,H.symm_apply_apply]
  obtain ⟨K,_,hK,hKs,_,_⟩ :=
    (isFinitePLBallPair_Icc (by norm_num : (0 : ℝ) < 1)).exists_finite_carrier_and_rim_complexes
  have hid : FinitePiecewiseAffineOn (id : ℝ → ℝ) J :=
    ⟨K,hK,hKs,K.affineOnFaces_affine (ContinuousAffineMap.id ℝ ℝ)⟩
  let g := Prod.map u (id : ℝ → ℝ)
  have hg : FinitePiecewiseAffineOn g (Rect ×ˢ J) := hu.prodMap hid
  have hgmap : MapsTo g (Rect ×ˢ J) (Disk ×ˢ J) := fun z hz => ⟨humap hz.1,hz.2⟩
  have hgi : InjOn g (Rect ×ˢ J) := by
    intro z hz w hw heq
    exact Prod.ext (hvu.injOn hz.1 hw.1 (congrArg Prod.fst heq))
      (show z.2 = w.2 from congrArg (fun z : V2 × ℝ => z.2) heq)
  let k := c ∘ g
  have hk : PolyhedralPLInCharts e k (Rect ×ˢ J) := by
    obtain ⟨K,hK,hKs,hKf⟩ := hg
    rw [←hKs]
    exact hc.comp_finitePiecewiseAffineOn K hK ⟨K,hK,rfl,hKf⟩
      (fun z hz => hgmap (hKs.subset hz))
  have hki : InjOn k (Rect ×ˢ J) := hci.comp hgi hgmap
  have hk0 (z : P2) (hz : z ∈ Rect) : k (z,0) = r z := by
    change c (u z,0) = r z
    rw [hc0 (u z) (humap hz),hvu hz]
  have hkE (z : P2 × ℝ) (hz : z ∈ Rect ×ˢ J) : k z ∈ E ↔ z.2 = 0 :=
    hcE (g z) (hgmap hz)
  refine ⟨u,k,hu,huval,fun _ => rfl,?_,hk,hki,
    fun z hz => hcDW (hgmap hz),fun z hz => hcO (hgmap hz),hk0,hkE,?_,?_,?_⟩
  · apply Subset.antisymm
    · rintro x ⟨z,hz,rfl⟩
      exact ⟨g z,hgmap hz,rfl⟩
    · rintro x ⟨z,hz,rfl⟩
      refine ⟨(v z.1,z.2),⟨hvmap hz.1,hz.2⟩,?_⟩
      change c (u (v z.1),z.2) = c z
      rw [huv hz.1]
  · intro z hz
    have h := hcS (g z) (hgmap hz)
    change k z ∈ S ↔ r (v (u z.1)) ∈ S at h
    simpa only [hvu hz.1] using h
  · ext x
    constructor
    · rintro ⟨⟨z,hz,rfl⟩,hx⟩
      have ht := (hkE z hz).mp hx
      rw [show z = (z.1,0) from Prod.ext rfl ht,hk0 z.1 hz.1]
      exact ⟨z.1,hz.1,rfl⟩
    · rintro ⟨z,hz,rfl⟩
      have hzero : (z,0) ∈ Rect ×ˢ J := ⟨hz,by norm_num⟩
      exact ⟨⟨(z,0),hzero,hk0 z hz⟩,(hk0 z hz) ▸ (hkE (z,0) hzero).mpr rfl⟩
  · have hRect : IsFinitePLBallPair P2 Rect RectRim :=
      (isFinitePLBallPair_Icc (by norm_num : (0 : ℝ) < 1)).prod
        (isFinitePLBallPair_Icc (by norm_num : (-1 : ℝ) < 1))
    exact exists_chartwisePLBall_image
      (hRect.prod (isFinitePLBallPair_Icc (by norm_num : (0 : ℝ) < 1)))
      (ContinuousLinearEquiv.ofFinrankEq (by simp)) hk subset_rfl hki

theorem HamiltonMarkedProtectedBall.exists_original_relative_rectangle_cap
    {ι κ α : Type*} [Fintype ι] [Fintype κ]
    {L : Submodule ℤ (κ → ℝ)} [DiscreteTopology L] [IsZLattice ℝ L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    {D S W : Set (LatticeHandleAmbient ι κ L)}
    (b : HamiltonMarkedProtectedBall ι κ L e D)
    (he : PLDomain e (latticeHandleDomain ι κ L))
    (hdim : Fintype.card ι + Fintype.card κ = 3) (hi : Fintype.card ι = 1)
    (hW : PLDomain e W) (hWS : frontier W = S)
    (hSR : S ⊆ interior (latticeHandleDomain ι κ L)) :
    let X := LatticeHandleAmbient ι κ L
    let R := latticeHandleDomain ι κ L
    let E := closure (R \ D)
    ∀ (_hcross : ∀ x ∈ S ∩ frontier E,∃ H : OpenPartialHomeomorph X V3,
      x ∈ H.source ∧ H x = 0 ∧
      (∀ i,(e i).symm.trans H ∈ piecewiseAffineGroupoid V3) ∧
      (∀ y ∈ H.source,y ∈ S ↔ H y 1 = 0) ∧
      ∀ y ∈ H.source,y ∈ frontier E ↔ H y 0 = 0)
      {r : P2 → X} (_hr : PolyhedralPLInCharts e r Rect)
      (_hri : InjOn r Rect) (_hrF : MapsTo r Rect (frontier E))
      (_hrW : MapsTo r Rect W) (_hrR : MapsTo r Rect (interior R))
      {O : Set X} (_hO : IsOpen O) (_hrO : r '' Rect ⊆ O),
    ∃ k : P2 × ℝ → X,
      PolyhedralPLInCharts e k (Rect ×ˢ J) ∧ InjOn k (Rect ×ˢ J) ∧
      MapsTo k (Rect ×ˢ J) (D ∩ W) ∧ MapsTo k (Rect ×ˢ J) (O ∩ interior R) ∧
      (∀ z ∈ Rect,k (z,0) = r z) ∧
      (∀ z ∈ Rect ×ˢ J,k z ∈ E ↔ z.2 = 0) ∧
      (∀ z ∈ Rect ×ˢ J,k z ∈ S ↔ r z.1 ∈ S) ∧
      k '' (Rect ×ˢ J) ∩ E = r '' Rect ∧
      Nonempty (ChartwisePLBall e (k '' (Rect ×ˢ J))
        (k '' ((RectRim ×ˢ J) ∪ (Rect ×ˢ ({0,1} : Set ℝ))))) ∧
      ∃ (H : Disk ≃ₜ Rect) (v : V2 → P2) (c : V2 × ℝ → X) (u : P2 → V2),
        H.IsFinitePL ∧ FinitePiecewiseAffineOn v Disk ∧
        (∀ z : Disk,(H z : P2) = v z) ∧
        PolyhedralPLInCharts e c (Disk ×ˢ J) ∧ InjOn c (Disk ×ˢ J) ∧
        FinitePiecewiseAffineOn u Rect ∧ (∀ z : Rect,(H.symm z : V2) = u z) ∧
        (∀ z,k z = c (u z.1,z.2)) ∧ k '' (Rect ×ˢ J) = c '' (Disk ×ˢ J) ∧
        ∃ (K : Set X) (s : Finset (D ∪ K : Set X))
          (P : RelativeFrontierDiskProduct e D W (O ∩ interior R) (r ∘ v) K s),
          P.map = c ∧ ∀ z ∈ Rect ×ˢ J,
            P.productInverse (P.graph (k z)) = (P.graph (r z.1),P.delta * z.2) := by
  intro X R E hcross r hr hri hrF hrW hrR O hO hrO
  have hRect : IsFinitePLBallPair P2 Rect RectRim :=
    (isFinitePLBallPair_Icc (by norm_num : (0 : ℝ) < 1)).prod
      (isFinitePLBallPair_Icc (by norm_num : (-1 : ℝ) < 1))
  have hDisk : IsFinitePLBallPair P2 Disk Rim :=
    (isFinitePLBallPair_unit_cube (ι := Fin 2)).model_equiv
      (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)
  obtain ⟨H,hH,_hHrim⟩ := hDisk.exists_homeomorph hRect
  have hHcopy := hH
  obtain ⟨v,hv,hvval⟩ := hHcopy
  have hvmap : MapsTo v Disk Rect := by
    intro z hz
    rw [←hvval ⟨z,hz⟩]
    exact (H ⟨z,hz⟩).property
  have hvi : InjOn v Disk := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (H.injective (Subtype.ext
      ((hvval ⟨x,hx⟩).trans (hxy.trans (hvval ⟨y,hy⟩).symm))))
  let j := r ∘ v
  have hj : PolyhedralPLInCharts e j Disk := by
    obtain ⟨K,hK,hKs,hKf⟩ := hv
    rw [←hKs]
    exact hr.comp_finitePiecewiseAffineOn K hK ⟨K,hK,rfl,hKf⟩
      (fun z hz => hvmap (hKs.subset hz))
  have hji : InjOn j Disk := hri.comp hvi hvmap
  have hjF : MapsTo j Disk (frontier E) := fun z hz => hrF (hvmap hz)
  have hjW : MapsTo j Disk W := fun z hz => hrW (hvmap hz)
  have hjR : MapsTo j Disk (interior R) := fun z hz => hrR (hvmap hz)
  have hjO : j '' Disk ⊆ O := by
    rintro x ⟨z,hz,rfl⟩
    exact hrO ⟨v z,hvmap hz,rfl⟩
  obtain ⟨c,hc,hci,hcDW,hcO,hc0,hcE,hcS,_hcbase,_hcball,hretained⟩ :=
    b.exists_original_relative_protected_cap he hdim hi hW hWS hSR hcross
      hj hji hjF hjW hjR hO hjO
  obtain ⟨u,k,hu,huval,hkeq,himage,hk,hki,hkDW,hkO,hk0,hkE,hkS,hbase,hball⟩ :=
    exists_relative_rectangle_cap_reparametrization H hH v hvval r c hc hci hcDW hcO hc0 hcE hcS
  obtain ⟨K,s,P,hPc⟩ := hretained
  refine ⟨k,hk,hki,hkDW,hkO,hk0,hkE,hkS,hbase,hball,
    H,v,c,u,hH,hv,hvval,hc,hci,hu,huval,hkeq,himage,K,s,P,hPc,?_⟩
  intro z hz
  have huDisk : u z.1 ∈ Disk := by
    rw [←huval ⟨z.1,hz.1⟩]
    exact (H.symm ⟨z.1,hz.1⟩).property
  have hbase : v (u z.1) = z.1 := by
    rw [←huval ⟨z.1,hz.1⟩,←hvval,H.apply_symm_apply]
  have h := P.map_productInverse (u z.1,z.2) ⟨huDisk,hz.2⟩
  rw [hPc] at h
  rw [hkeq]
  simpa only [j,Function.comp_apply,hbase] using h

end PoincareConjecture.M76
