import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Boundary.Source.Enlarge
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.ReturningCupLocalPush
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.ReturningCupPasting
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.ReturningCupBend



set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli
open PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "C3" => (P2 × ℝ)
local notation "V3" => (Fin 3 → ℝ)

theorem exists_essential_prepared_returning_arc_decrease
    {X ι κ : Type*} [MetricSpace X] [Finite κ]
    {e : ι → OpenPartialHomeomorph X V3} {R O : Set X}
    (hR : IsCompact R) (he : PLDomain e R) (hO : IsOpen O)
    (J : SimplicialComplex ℝ P2) (hJ : J.faces.Finite)
    {T₀ Q₀ D₀ E₀ U₀ S₀ H₀ D₁ E₁ U₁ S₁ Q₁ H₁ : Set P2}
    {c₀ c₁ : P2 → P2} {f₀ f₁ : P2 → X} {τ : C3 → X}
    (hT₀ : IsFinitePLBallPair P2 T₀ Q₀)
    (hT₀eq : T₀ = J.space) (hS₀eq : S₀ = J.space) (hH₀eq : H₀ = ∅)
    (hD₀ : IsFinitePLBallPair P2 D₀ (U₀ ∪ c₀ '' arm 0))
    (hE₀ : IsFinitePLBallPair P2 E₀ ((E₀ ∩ Q₀) ∪ c₀ '' arm 0))
    (hU₀ : IsFinitePLBallPair ℝ U₀ {c₀ (0, 0), c₀ (1, 0)})
    (hDU₀ : D₀ ∩ Q₀ = U₀) (hcover₀ : D₀ ∪ E₀ = T₀)
    (hcommon₀ : D₀ ∩ E₀ = c₀ '' arm 0)
    (hD₁ : IsFinitePLBallPair P2 D₁ (U₁ ∪ c₁ '' arm 0))
    (hDU₁ : D₁ ∩ Q₁ = U₁)
    (hcover₁ : S₁ ⊆ E₁ ∪ D₁) (hcommon₁ : E₁ ∩ D₁ = c₁ '' arm 0)
    (hc₀ : FinitePiecewiseAffineOn c₀ source) (hi₀ : InjOn c₀ source)
    (hc₁ : FinitePiecewiseAffineOn c₁ source) (hi₁ : InjOn c₁ source)
    (hc₀S : MapsTo c₀ source S₀) (hc₁S : MapsTo c₁ source S₁)
    (hc₀Q : ∀ p ∈ source, c₀ p ∈ Q₀ ↔ p.1 = 0 ∨ p.1 = 1)
    (hc₁Q : ∀ p ∈ source, c₁ p ∈ Q₁ ↔ p.1 = 0 ∨ p.1 = 1)
    (hhalf₀ : c₀ '' halfSource false ⊆ E₀) (hhalf₁ : c₁ '' halfSource true ⊆ D₁)
    (hS₀ : IsCompact S₀) (hS₁ : IsCompact S₁) (hE₁ : IsCompact E₁)
    (hS₀T : S₀ ⊆ T₀) (hD₀S : D₀ ⊆ S₀) (hD₁S : D₁ ⊆ S₁)
    (hD₀H : Disjoint D₀ H₀) (hc₀H : Disjoint (c₀ '' source) H₀)
    (hD₁H : Disjoint D₁ H₁)
    (hf₀ : PolyhedralPLInCharts e f₀ S₀) (hf₁ : PolyhedralPLInCharts e f₁ S₁)
    (hfi₀ : InjOn f₀ S₀) (hfi₁ : InjOn f₁ S₁)
    (hf₀R : MapsTo f₀ S₀ R) (hf₁R : MapsTo f₁ S₁ R)
    (hf₀O : MapsTo f₀ D₀ O) (hf₁O : MapsTo f₁ D₁ O)
    (hp₀ : ∀ x ∈ S₀, f₀ x ∈ frontier R ↔ x ∈ Q₀ ∪ H₀)
    (hp₁ : ∀ x ∈ S₁, f₁ x ∈ frontier R ↔ x ∈ Q₁ ∪ H₁)
    (honly : ∀ x ∈ D₁, f₁ x ∈ f₀ '' S₀ → x ∈ c₁ '' arm 0)
    (hτ : PolyhedralPLInCharts e τ tube) (hτi : InjOn τ tube)
    (hτR : MapsTo τ tube R) (hτO : MapsTo τ tube O)
    (hτfront : ∀ z ∈ tube, τ z ∈ frontier R ↔ z.2 = 0 ∨ z.2 = 1)
    (htrace₀ : ∀ z ∈ tube, τ z ∈ f₀ '' S₀ ↔ z.1.2 = -z.1.1)
    (htrace₁ : ∀ z ∈ tube, τ z ∈ f₁ '' S₁ ↔ z.1.2 = z.1.1)
    (hsheet₀ : ∀ p ∈ source, f₀ (c₀ p) = τ ((p.2, -p.2), p.1))
    (hsheet₁ : ∀ p ∈ source, f₁ (c₁ p) = τ ((p.2, p.2), p.1) )
    {u : P2 → X} (hu : ContinuousOn u T₀)
    (huq : ∀ x ∈ Q₀,u x ∈ frontier R)
    (huimage : u '' T₀ = f₀ '' E₀ ∪ f₁ '' D₁)
    (hne : ¬∃ F : C(T₀,frontier R),∀ x : Q₀,(F ⟨x,hT₀.1 x.property⟩:X) = u x)
    (pieces : κ → Set P2) (hclosed : ∀ i,IsClosed (pieces i))
    (hdis : Pairwise (fun i j => Disjoint (pieces i) (pieces j)))
    (hpieces : ⋃ i,pieces i = J.space ∩ f₀ ⁻¹' (f₁ '' S₁))
    (hconn : ∀ i,IsConnected (pieces i)) :
    ∃ k : P2 → X,PolyhedralPLInCharts e k J.space ∧
      IsEmbedding (fun x : J.space => k x) ∧ MapsTo k J.space R ∧
      (∀ x ∈ J.space,k x ∈ frontier R ↔ x ∈ Q₀) ∧
      J.space ∩ k ⁻¹' (f₁ '' S₁) ⊆ J.space ∩ f₀ ⁻¹' (f₁ '' S₁) ∧
      EqOn k f₀ (J.space ∩ k ⁻¹' (f₁ '' S₁)) ∧
      Nat.card (ConnectedComponents (J.space ∩ k ⁻¹' (f₁ '' S₁) : Set P2)) <
        Nat.card (ConnectedComponents (J.space ∩ f₀ ⁻¹' (f₁ '' S₁) : Set P2)) ∧
      (¬∃ F : C(J.space,frontier R),
        ∀ x : Q₀,(F ⟨x,hT₀eq ▸ hT₀.1 x.property⟩:X) = k x) ∧
      ∃ W : Set X,IsOpen W ∧ (f₁ '' S₁) ∩ (k '' J.space) ⊆ W ∧
        ∀ z ∈ W,z ∈ k '' J.space ↔ z ∈ f₀ '' J.space := by
  subst S₀
  subst T₀
  subst H₀
  let S₀ := J.space
  let T₀ := J.space
  let H₀ : Set P2 := ∅
  obtain ⟨N, C, U, V, hN, hC, hU, hUZ, hNC, hNZ, hNQ, hNeq, hCeq,
    hNS, hNH, hcenter, _⟩ := exists_enlarged_returning_disk hT₀ hc₀ hi₀ hc₀S hS₀T
      hD₀S hc₀Q hE₀ hcover₀ hcommon₀ hhalf₀ hD₀H hc₀H
  obtain ⟨B, V₁, _, hB, hV₁, hVZ, hBQ, hBD, htrimCover, htrim, hBcenter⟩ :=
    exists_trimmed_returning_disk hD₁ hDU₁ hc₁ hi₁ hc₁Q hhalf₁
  have hUW : U₀ ∩ (c₀ '' arm 0) = {c₀ (0, 0), c₀ (1, 0)} := by
    rw [← hDU₀, inter_assoc,
      inter_eq_right.mpr (inter_subset_right.trans (subset_union_right.trans hD₀.1))]
    exact proper_strip_arm_rim_contact (by norm_num) hc₀Q
  have hNproper (x : P2) (hx : x ∈ N) : f₀ x ∈ frontier R ↔ x ∈ U := by
    rw [hp₀ x (hNS hx)]
    constructor
    · rintro (hQ | hH)
      · exact hNQ.subset ⟨hx, hQ⟩
      · exact (disjoint_left.mp hNH hx hH).elim
    · exact fun h ↦ Or.inl (hNQ.superset h).2
  have hBproper (x : P2) (hx : x ∈ B) : f₁ x ∈ frontier R ↔ x ∈ V₁ := by
    rw [hp₁ x (hD₁S (hBD hx))]
    constructor
    · rintro (hQ | hH)
      · exact hBQ.subset ⟨hx, hQ⟩
      · exact (disjoint_left.mp hD₁H (hBD hx) hH).elim
    · exact fun h ↦ Or.inl (hBQ.superset h).2
  have hNO : MapsTo f₀ N O := by
    intro x hx
    rcases hNeq.subset hx with hx | ⟨p, hp, rfl⟩
    · exact hf₀O hx
    · rw [hsheet₀ p (halfSource_subset_source false hp)]
      exact hτO (originalStripSheet_mem_tube true (halfSource_subset_source false hp))
  have hBT : Disjoint (f₁ '' B) (f₀ '' S₀) := by
    refine disjoint_left.mpr ?_
    rintro _ ⟨x, hx, rfl⟩ ht
    exact disjoint_left.mp hBcenter hx (honly x (hBD hx) ht)
  have hfar (t : Icc (0 : ℝ) 1) :
      f₀ (c₀ ((t : ℝ), -1)) = τ ((-1, 1), (t : ℝ)) := by
    simpa using hsheet₀ ((t : ℝ), -1) ⟨t.property, by norm_num⟩

  obtain ⟨v,g,hv,hvi,hvfix,hvcapA,hvcapT,hvimage,hvR,hvproper,
    hg,hgi,hgR,hgO,hgfix,hgavoid,hgtrace,hgproper,H,hH0,hH1,hHR,hHfront,hHfix⟩ :=
    exists_original_local_returning_arc_removal_with_cup_homotopy hR he hO hc₀ hi₀ hc₁ hi₁
      hD₀ hB hU₀ hV₁ hUW hVZ (returning_disk_negative_half_contact hcommon₀ hhalf₀)
      hDU₀ hNQ hc₀Q hNeq hN hU hUZ hS₀ hS₁ hE₁ hNS (hBD.trans hD₁S) hc₁S
      hcover₁ hcommon₁ htrim htrimCover hf₀ hf₁ hfi₀ hfi₁ hf₀R hf₁R hNO
      (fun _ hx => hf₁O (hBD hx)) hNproper hBproper hτ hτi hτR hτO hτfront
      htrace₁ htrace₀ hBT hfar hsheet₁
  have hCS : C ⊆ J.space := fun x hx => hNC.subset (Or.inr hx)
  have hE₀S : E₀ ⊆ J.space := fun x hx => hcover₀.subset (Or.inr hx)
  have hWN : c₀ '' arm (-1) ⊆ N := subset_union_right.trans hN.1
  have hvtrace (x : P2) (hx : x ∈ N) :
      v x ∈ f₀ '' J.space ↔ x ∈ c₀ '' arm (-1) := by
    constructor
    · intro ht
      obtain ⟨y,hy,hyx⟩ := hvcapT.subset ⟨⟨x,hx,rfl⟩,ht⟩
      exact (hvi (hWN hy) hx ((hvfix hy).trans hyx)) ▸ hy
    · intro hxW
      exact ⟨x,hNS hx,(hvfix hxW).symm⟩
  have hvproperQ (x : P2) (hx : x ∈ N) : v x ∈ frontier R ↔ x ∈ Q₀ :=
    (hvproper x hx).trans
      ⟨fun h => (hNQ.superset h).2,fun h => hNQ.subset ⟨hx,h⟩⟩
  obtain ⟨F,hF1,hFR,hFfront,hFfix,hFi,hFimage⟩ :=
    BoundaryCup.exists_original_returning_cup_branch_homotopy hc₀S hi₀ hc₁S hi₁
      hE₀S (hBD.trans hD₁S) hCeq hhalf₀ htrim htrimCover hC.isCompact hB.isCompact
      (hf₀.continuousOn.mono hCS) (hf₁.continuousOn.mono (hBD.trans hD₁S))
      hfi₀ hfi₁ (fun x hx => hf₀R (hCS hx)) (fun x hx => hf₁R (hD₁S (hBD hx)))
      hτ.continuousOn hτi hτR hτfront htrace₁ htrace₀ hBT hsheet₀ hsheet₁
  let Y := v '' N ∪ f₀ '' (J.space ∩ C)
  let Z := (f₁ '' B ∪ f₀ '' C) ∪ τ '' (BoundaryCup.bridgeCoordinates '' halfSource false)
  have hYZ : Y = Z := by
    dsimp only [Y,Z]
    rw [hvimage,inter_eq_right.mpr hCS]
    ext x
    simp only [mem_union]
    tauto
  let L : Y ≃ₜ Z := Homeomorph.setCongr hYZ
  let G : C(↥(Icc (0:ℝ) 1) × ↥Y,X) := F.comp ⟨fun z => (z.1,L z.2),by fun_prop⟩
  have hG1 (z : Y) : G (⟨1,by norm_num⟩,z) = z := hF1 (L z)
  have hGfront (z) : G z ∈ frontier R ↔ (z.2:X) ∈ frontier R := hFfront (z.1,L z.2)
  have hGi : Function.Injective (fun z : Y => G (⟨0,by norm_num⟩,z)) := by
    intro z w hzw
    exact L.injective (hFi hzw)
  have hGimage : u '' J.space ⊆ Set.range (fun z : Y => G (⟨0,by norm_num⟩,z)) := by
    change u '' J.space ⊆ Set.range ((fun z : Z => F (⟨0,by norm_num⟩,z)) ∘ L)
    rw [range_comp,L.surjective.range_eq,image_univ,hFimage,huimage]
  have h00 : ((0,0):P2) ∈ source := by norm_num [source]
  have hcenter0 : c₀ (0,0) ∈ c₀ '' arm 0 := ⟨(0,0),by norm_num [arm],rfl⟩
  have hvalue : f₁ (c₁ (0,0)) = f₀ (c₀ (0,0)) := by
    rw [hsheet₀ _ h00,hsheet₁ _ h00]
    simp
  have hdeleted : ((J.space ∩ f₀ ⁻¹' (f₁ '' S₁)) \ C).Nonempty :=
    ⟨c₀ (0,0),⟨hc₀S h00,⟨c₁ (0,0),hc₁S h00,hvalue⟩⟩,(hcenter hcenter0).2⟩
  obtain ⟨k,hk,hke,hkR,hkC,hkproper,hkcontact,hkcount,hkne,hgerm⟩ :=
    exists_essential_pasted_cup_contact_decrease he.compatible J hJ hT₀ hN hC hNS
      (hNC.symm.subset) hNZ hf₀ hfi₀ hf₀R
      (fun x hx => by simpa only [union_empty] using hp₀ x hx)
      hv hvi hvfix hvtrace hvR hvproperQ hg hgi hgfix hgtrace hgavoid H hH0 hH1 hHR hHfront hHfix
      hu huq hne G hG1 hGfront hGi hGimage pieces hclosed hdis hpieces hconn hdeleted
  refine ⟨k,hk,hke,hkR,hkproper,hkcontact.subset.trans inter_subset_left,?_,hkcount,hkne,hgerm⟩
  intro x hx
  have hxc := hkcontact.subset hx
  exact hkC ⟨hxc.1.1,hxc.2⟩

end PoincareConjecture.M76.Dehn.Annuli
