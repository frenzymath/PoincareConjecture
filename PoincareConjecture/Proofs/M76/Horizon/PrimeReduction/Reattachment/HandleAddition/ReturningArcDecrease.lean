import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.ReturningArcJoinedDisk
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.ReturningIntervalTube
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.ReturningArcPreparedDecrease
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Intervals.Construction
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Boundary.Resolution.RetainedCharts

set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli
open PolygonalCrossingResolution
local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)

theorem exists_essential_returning_arc_decrease
    {X ι κ : Type*} [MetricSpace X] [Finite κ]
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X}
    (hR : IsCompact R) (he : PLDomain e R)
    (J K : SimplicialComplex ℝ P2) (hJ : J.faces.Finite) (hK : K.faces.Finite)
    {q rim W D V Z E : Set P2} {a b c d : P2}
    (hJball : IsFinitePLBallPair P2 J.space q) (hrim : rim ⊆ K.space)
    (hW : IsFinitePLBallPair ℝ W {a,b}) (haq : a ∈ q) (hbq : b ∈ q) (hab : a ≠ b)
    (hproperW : W \ {a,b} ⊆ J.space \ q)
    (hD : IsFinitePLBallPair P2 D (V ∪ Z))
    (hV : IsFinitePLBallPair ℝ V {c,d}) (hZ : IsFinitePLBallPair ℝ Z {c,d})
    (hVZ : V ∩ Z = {c,d}) (hcd : c ≠ d)
    (hDK : D ⊆ K.space) (hDrim : D ∩ rim = V)
    (hE : IsCompact E) (hcover : K.space ⊆ D ∪ E) (hcommon : D ∩ E = Z)
    {f g : P2 → X}
    (hf : PolyhedralPLInCharts e f J.space) (hg : PolyhedralPLInCharts e g K.space)
    (hfi : InjOn f J.space) (hgi : InjOn g K.space)
    (hfR : MapsTo f J.space R) (hgR : MapsTo g K.space R)
    (hfproper : ∀ x ∈ J.space,f x ∈ frontier R ↔ x ∈ q)
    (hgproper : ∀ x ∈ K.space,g x ∈ frontier R ↔ x ∈ rim)
    (himage : f '' W = g '' Z) (ha : f a = g c) (hb : f b = g d)
    (htrace : D ∩ g ⁻¹' (f '' J.space) = Z)
    (hne : ¬∃ F : C(J.space,frontier R),
      ∀ x : q,(F ⟨x,hJball.1 x.property⟩ : X) = f x)
    (hrest : IsClosed ((J.space ∩ f ⁻¹' (g '' K.space)) \ W))
    (hboundary : ∀ x ∈ J.space,f x ∈ g '' K.space → f x ∈ frontier R →
      ∃ B : OriginalSurfacePairChart e (f '' J.space) (g '' K.space) (f x) true,
        (∀ z ∈ B.coordinates.source,B.chart.symm z ∈ R ↔ 0 ≤ (B.coordinates z).1.2) ∧
        ∀ z ∈ B.coordinates.source,B.chart.symm z ∈ frontier R ↔ (B.coordinates z).1.2 = 0)
    (hinterior : ∀ x ∈ J.space,f x ∈ g '' K.space → f x ∈ interior R →
      Nonempty (OriginalSurfacePairChart e (f '' J.space) (g '' K.space) (f x) false))
    (pieces : κ → Set P2) (hclosed : ∀ i,IsClosed (pieces i))
    (hdis : Pairwise (fun i j => Disjoint (pieces i) (pieces j)))
    (hpieces : ⋃ i,pieces i = J.space ∩ f ⁻¹' (g '' K.space))
    (hconn : ∀ i,IsConnected (pieces i)) :
    ∃ k : P2 → X,PolyhedralPLInCharts e k J.space ∧
      IsEmbedding (fun x : J.space => k x) ∧ MapsTo k J.space R ∧
      (∀ x ∈ J.space,k x ∈ frontier R ↔ x ∈ q) ∧
      J.space ∩ k ⁻¹' (g '' K.space) ⊆ J.space ∩ f ⁻¹' (g '' K.space) ∧
      EqOn k f (J.space ∩ k ⁻¹' (g '' K.space)) ∧
      Nat.card (ConnectedComponents (J.space ∩ k ⁻¹' (g '' K.space) : Set P2)) <
        Nat.card (ConnectedComponents (J.space ∩ f ⁻¹' (g '' K.space) : Set P2)) ∧
      (¬∃ F : C(J.space,frontier R),
        ∀ x : q,(F ⟨x,hJball.1 x.property⟩ : X) = k x) ∧
      (∀ x ∈ J.space,k x ∈ g '' K.space → k x ∈ frontier R →
        ∃ B : OriginalSurfacePairChart e (k '' J.space) (g '' K.space) (k x) true,
          (∀ z ∈ B.coordinates.source,B.chart.symm z ∈ R ↔ 0 ≤ (B.coordinates z).1.2) ∧
          ∀ z ∈ B.coordinates.source,B.chart.symm z ∈ frontier R ↔ (B.coordinates z).1.2 = 0) ∧
      (∀ x ∈ J.space,k x ∈ g '' K.space → k x ∈ interior R →
        Nonempty (OriginalSurfacePairChart e (k '' J.space) (g '' K.space) (k x) false)) ∧
      ∃ O : Set X,IsOpen O ∧ (g '' K.space) ∩ (k '' J.space) ⊆ O ∧
        ∀ z ∈ O,z ∈ k '' J.space ↔ z ∈ f '' J.space := by
  obtain ⟨KD,_,hKD,hKDs,_,_⟩ := hD.exists_finite_carrier_and_rim_complexes
  have hgD : PolyhedralPLInCharts e g D :=
    hKDs ▸ hg.restrict_finite KD hKD (hKDs.subset.trans hDK)
  have hgDproper (x : P2) (hx : x ∈ D) : g x ∈ frontier R ↔ x ∈ V :=
    (hgproper x (hDK hx)).trans
      ⟨fun h => hDrim.subset ⟨hx,h⟩,fun h => (hDrim.superset h).2⟩
  obtain ⟨A,B,U,T,u,hA,hB,hU,hT,hAB,hAi,hUT,hUi,hAq,hBq,
    hu,hui,hue,huR,hukeep,huB,huT,huimage,huproper,hune⟩ :=
    exists_essential_original_returning_disk_branch he.compatible hJball hW haq hbq hab
      hproperW hD hV hZ hVZ hcd hf hgD hfi (hgi.mono hDK) hfR
      (fun x hx => hgR (hDK hx)) hfproper hgDproper himage ha hb htrace hne
  have hAS : A ⊆ J.space := subset_union_left.trans hAB.subset
  have hBS : B ⊆ J.space := subset_union_right.trans hAB.subset
  have hWS : W ⊆ J.space := (subset_union_right.trans hA.1).trans hAS
  have hZS : Z ⊆ K.space := (subset_union_right.trans hD.1).trans hDK
  have hWq : W ∩ q = {a,b} := by
    apply Subset.antisymm
    · intro x hx
      by_contra hn
      exact (hproperW ⟨hx.1,hn⟩).2 hx.2
    · intro x hx
      refine ⟨hW.1 hx,?_⟩
      rcases hx with hx | hx
      · simpa only [mem_singleton_iff.mp hx] using haq
      · simpa only [mem_singleton_iff.mp hx] using hbq
  obtain ⟨I⟩ := nonempty_originalIntervalTube he J K hJ hK f g hf hg hfi hgi
    hfR hgR q rim hJball.1 hrim hfproper hgproper hboundary hinterior
    W Z hWS hZS (hWq.symm ▸ hW) himage hrest isOpen_univ (subset_univ _)
  obtain ⟨c₀,c₁,τ,hc₀,hc₁,hci₀,hci₁,hc₀S,hc₁S,_,_,hcenter₀,hcenter₁,
    _,hhalf₀,hhalf₁,_,hτ,hτe,hτR,hτO,_,hsheet₀,hsheet₁,htrace₀,htrace₁,hτfront⟩ :=
    exists_disk_region_oriented_original_interval_tube I hB
      (by simpa only [union_comm] using hA) hD hE.isClosed
      (by rw [union_comm B A]; exact hAB.symm.subset) hcover
      ((inter_comm B A).trans hAi) hcommon
  have hc₀Q (p : P2) (hp : p ∈ source) : c₀ p ∈ q ↔ p.1 = 0 ∨ p.1 = 1 := by
    have hh := hfproper (c₀ p) (hc₀S hp)
    rw [hsheet₀ p hp,hτfront ((p.2,-p.2),p.1) (originalStripSheet_mem_tube true hp)] at hh
    exact hh.symm
  have hc₁Q (p : P2) (hp : p ∈ source) : c₁ p ∈ rim ↔ p.1 = 0 ∨ p.1 = 1 := by
    have hh := hgproper (c₁ p) (hc₁S hp)
    rw [hsheet₁ p hp,hτfront ((p.2,p.2),p.1) (originalStripSheet_mem_tube false hp)] at hh
    exact hh.symm
  have hTends : T ∩ W = {a,b} := by
    apply Subset.antisymm
    · intro x hx
      exact hWq.subset ⟨hx.2,(hBq.superset hx.1).2⟩
    · exact fun x hx => ⟨hT.1 hx,hW.1 hx⟩
  have hends : ({a,b} : Set P2) = {c₀ (0,0),c₀ (1,0)} := by
    rw [←hTends,←hBq,inter_assoc,
      inter_eq_right.mpr (inter_subset_right.trans (subset_union_right.trans hB.1)),←hcenter₀]
    exact proper_strip_arm_rim_contact (by norm_num) hc₀Q
  have hA' : IsFinitePLBallPair P2 A ((A ∩ q) ∪ c₀ '' arm 0) := by
    rw [hAq,hcenter₀]
    exact hA
  have hEi : E ∩ D = c₁ '' arm 0 := by rw [inter_comm,hcommon,hcenter₁]
  have hfi' (c' : P2 → P2) (hc' : IsEmbedding (fun p : source => c' p)) : InjOn c' source :=
    fun x hx y hy hxy => congrArg Subtype.val (hc'.injective (a₁ := ⟨x,hx⟩) (a₂ := ⟨y,hy⟩) hxy)
  have hτi : InjOn τ tube := fun x hx y hy hxy =>
    congrArg Subtype.val (hτe.injective (a₁ := ⟨x,hx⟩) (a₂ := ⟨y,hy⟩) hxy)
  obtain ⟨k,hk,hke,hkR,hkproper,hksub,hkkeep,hkcount,hkne,O,hO,hinside,hagree⟩ :=
    exists_essential_prepared_returning_arc_decrease hR he isOpen_univ J hJ hJball rfl rfl rfl
      (hcenter₀.symm ▸ hB) hA' (hends ▸ hT) hBq ((union_comm B A).trans hAB)
      (((inter_comm B A).trans hAi).trans hcenter₀.symm) (hcenter₁.symm ▸ hD) hDrim
      (hcover.trans (union_comm D E).subset) hEi hc₀ (hfi' c₀ hci₀) hc₁ (hfi' c₁ hci₁)
      hc₀S hc₁S hc₀Q hc₁Q hhalf₀ hhalf₁ (J.isCompact_space_of_finite hJ)
      (K.isCompact_space_of_finite hK) hE Subset.rfl hBS hDK
      (disjoint_empty _) (disjoint_empty _) (disjoint_empty _) hf hg hfi hgi hfR hgR
      (mapsTo_univ _ _) (mapsTo_univ _ _)
      (fun x hx => by simpa only [union_empty] using hfproper x hx)
      (fun x hx => by simpa only [union_empty] using hgproper x hx)
      (fun x hx ht => hcenter₁.superset (htrace.subset ⟨hx,ht⟩))
      hτ hτi hτR hτO hτfront htrace₀ htrace₁ hsheet₀ hsheet₁ hu.continuousOn
      (fun x hx => (huproper x (hJball.1 hx)).mpr hx) huimage hune
      pieces hclosed hdis hpieces hconn
  obtain ⟨hb',hi'⟩ := original_pair_charts_after_local_replacement hO hinside hagree hkkeep
    hboundary hinterior
  exact ⟨k,hk,hke,hkR,hkproper,hksub,hkkeep,hkcount,hkne,hb',hi',O,hO,hinside,hagree⟩

end PoincareConjecture.M76.Dehn.Annuli
