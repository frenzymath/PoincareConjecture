import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.SpanningCornerCharts
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.SpanningBigonCornerDomain
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Boundary.UnionDisk.Product








set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1

theorem HamiltonMarkedProtectedBall.exists_original_marked_bigon_product
    {ι κ α F : Type*} [Fintype ι] [Fintype κ]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {L : Submodule ℤ (κ → ℝ)} [DiscreteTopology L] [IsZLattice ℝ L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    {D S : Set (LatticeHandleAmbient ι κ L)}
    (b : HamiltonMarkedProtectedBall ι κ L e D)
    (he : PLDomain e (latticeHandleDomain ι κ L))
    (hdim : Fintype.card ι + Fintype.card κ = 3) (hi : Fintype.card ι = 1)
    (s : ChartwisePLSphere e S)
    (hSR : S ⊆ interior (latticeHandleDomain ι κ L)) :
    let X := LatticeHandleAmbient ι κ L
    let E := closure (latticeHandleDomain ι κ L \ D)
    ∀ (_hcross : ∀ x ∈ S ∩ frontier E,
      ∃ H : OpenPartialHomeomorph X V3,
        x ∈ H.source ∧ H x = 0 ∧
        (∀ i, (e i).symm.trans H ∈ piecewiseAffineGroupoid V3) ∧
        (∀ y ∈ H.source, y ∈ S ↔ H y 1 = 0) ∧
        ∀ y ∈ H.source, y ∈ frontier E ↔ H y 0 = 0)
      {d U C : Set F} (_hd : IsFinitePLBallPair (ℝ × ℝ) d (U ∪ C))
      {a c : F} (_hac : a ≠ c) (_hUC : U ∩ C = {a,c})
      {f : F → X} (_hf : PolyhedralPLInCharts e f d) (_hfi : InjOn f d)
      (_hfE : MapsTo f d E)
      (_hfront : f '' d ∩ frontier E = f '' U)
      (_hsphere : f '' d ∩ S = f '' C)
      {M : Set X} (_hfM : f '' d ⊆ M)
      (_hboundary : ∀ x ∈ S ∩ frontier E, x ∈ M →
        ∃ B : OriginalSurfacePairChart e M (S ∩ E) x true,
          (∀ z ∈ B.coordinates.source, B.chart.symm z ∈ E ↔ 0 ≤ (B.coordinates z).1.2) ∧
          ∀ z ∈ B.coordinates.source, B.chart.symm z ∈ frontier E ↔ (B.coordinates z).1.2 = 0)
      {O : Set X} (_hO : IsOpen O) (_hfO : f '' d ⊆ O),
    ∃ (W : Set X) (H : Disk ≃ₜ d) (j : V2 → X)
      (P : OriginalDiskProduct e (E ∩ W) j),
      PLDomain e W ∧ frontier W = S ∧
      IsCompact (E ∩ W) ∧ PLDomain e (E ∩ W) ∧
      frontier (E ∩ W) = (E ∩ W) ∩ (frontier E ∪ S) ∧
      IsCompact (D ∩ W) ∧ PLDomain e (D ∩ W) ∧
      frontier (D ∩ W) = (D ∩ W) ∩ (frontier D ∪ S) ∧
      H.IsFinitePL ∧ (∀ z : Disk, j z = f (H z)) ∧
      (∀ z : Disk, (z : V2) ∈ Rim ↔ (H z : F) ∈ U ∪ C) ∧
      MapsTo P.map (Disk ×ˢ I) O ∧
      P.map '' (Disk ×ˢ {(0 : ℝ)}) = f '' d ∧
      (∀ z : Disk, j z ∈ frontier E ↔ (H z : F) ∈ U) ∧
      (∀ z : Disk, j z ∈ S ↔ (H z : F) ∈ C) ∧
      (∀ z ∈ Rim, ∀ t ∈ I,
        (P.map (z,t) ∈ frontier E ↔ j z ∈ frontier E) ∧
        (P.map (z,t) ∈ S ↔ j z ∈ S)) ∧
      ∀ v : ℝ, 0 < v → v ≤ 1 →
        IsOpen ((Subtype.val : ↥(E ∩ W) → X) ⁻¹' (P.map '' (Disk ×ˢ Ioo (-v) v))) := by
  intro X E hcross d U C hd a c hac hUC f hf hfi hfE hfront hsphere M hfM hboundary O hO hfO
  obtain ⟨W,hW,hWS,hN,heN,hfN,hproper,hNfront,hDW,heDW,hDWfront⟩ :=
    b.exists_original_bigon_paired_corners he hdim hi s hSR hcross hd hf hfi hfE hfront hsphere
  obtain ⟨H,j,P,hH,hj,hHrim,hPO,_,hcenter,hopen⟩ :=
    Dehn.Annuli.exists_original_finite_proper_disk_product hN heN hd hf hfi hfN hproper hO hfO
  have hmark {T : Set X} {A : Set F} (hAd : A ⊆ d)
      (hcontact : f '' d ∩ T = f '' A) (z : Disk) :
      j z ∈ T ↔ (H z : F) ∈ A := by
    rw [hj z]
    constructor
    · intro hz
      obtain ⟨w,hw,heq⟩ := hcontact.subset ⟨⟨H z,(H z).property,rfl⟩,hz⟩
      exact hfi (hAd hw) (H z).property heq ▸ hw
    · intro hz
      exact (hcontact.symm.subset ⟨H z,hz,rfl⟩).2
  have hjF := hmark (subset_union_left.trans hd.1) hfront
  have hjS := hmark (subset_union_right.trans hd.1) hsphere
  have hjW (z : Disk) : j z ∈ frontier W ↔ (H z : F) ∈ C := hWS.symm ▸ hjS z
  have hjM : j '' Disk ⊆ M := by
    rintro x ⟨z,hz,rfl⟩
    rw [hj ⟨z,hz⟩]
    exact hfM ⟨H ⟨z,hz⟩,(H ⟨z,hz⟩).property,rfl⟩
  have hboundaryW : ∀ x ∈ frontier W ∩ frontier E, x ∈ M →
      ∃ B : OriginalSurfacePairChart e M (frontier W ∩ E) x true,
        (∀ z ∈ B.coordinates.source, B.chart.symm z ∈ E ↔ 0 ≤ (B.coordinates z).1.2) ∧
        ∀ z ∈ B.coordinates.source, B.chart.symm z ∈ frontier E ↔ (B.coordinates z).1.2 = 0 := by
    rw [hWS]
    exact hboundary
  obtain ⟨P',hsub,hmarks,hopen'⟩ := P.exists_original_bigon_marked_correction
    heN isClosed_closure hW hopen hd hac hUC H hHrim hjF hjW hjM hboundaryW
  have hP'O : MapsTo P'.map (Disk ×ˢ I) O := by
    intro z hz
    obtain ⟨w,hw,heq⟩ := hsub ⟨z,hz,rfl⟩
    exact heq ▸ hPO hw
  have hPcenter : P'.map '' (Disk ×ˢ {(0 : ℝ)}) = f '' d := by
    rw [←hcenter]
    apply image_congr
    rintro ⟨z,t⟩ ⟨hz,ht⟩
    have ht0 : t = 0 := ht
    subst t
    exact (P'.central z hz).trans (P.central z hz).symm
  refine ⟨W,H,j,P',hW,hWS,hN,heN,hNfront,hDW,heDW,hDWfront,
    hH,hj,hHrim,hP'O,hPcenter,hjF,hjS,?_,hopen'⟩
  intro z hz t ht
  simpa only [hWS] using hmarks z hz t ht

end PoincareConjecture.M76
