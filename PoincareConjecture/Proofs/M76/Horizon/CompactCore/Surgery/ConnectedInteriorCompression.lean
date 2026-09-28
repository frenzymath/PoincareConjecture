import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Surgery.ProtectedInteriorCompression
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Surgery.ConnectedProtectedCompressionComponent
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Surgery.ProtectedCompressionLoops










set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1

theorem PLDomain.exists_connected_protected_interior_compression
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R K C F : Set X} {j : V2 → X}
    (he : PLDomain e K) (hK : IsCompact K) (hR : IsClosed R) (hKR : K ⊆ R)
    (hRconn : IsConnected R) (hend : HasOneSimplyConnectedEnd R)
    (hC : IsClosed C) (hCconn : IsConnected C) (hCR : C ⊆ R)
    (hBC : frontier R ⊆ C) (hF : IsCompact F) (hFR : F ⊆ R)
    (hprotect : (Subtype.val : R → X) ⁻¹' C ⊆
      interior ((Subtype.val : R → X) ⁻¹' K))
    (hrel : frontier ((Subtype.val : R → X) ⁻¹' K) = (Subtype.val : R → X) ⁻¹' F)
    (hfront : frontier K = frontier R ∪ F)
    (hloops : ∀ (x : R) (p : Path x x),
      (∀ t, p t ∈ (Subtype.val : R → X) ⁻¹' F) →
      ∃ H : p.Homotopy (Path.refl x),
        ∀ z, H z ∉ (Subtype.val : R → X) ⁻¹' C)
    (hj : PolyhedralPLInCharts e j D)
    (hemb : Topology.IsEmbedding (fun z : D => j z))
    (hjK : MapsTo j D K) (hjC : Disjoint (j '' D) C)
    (hproper : ∀ z : D, j z ∈ F ↔ (z : V2) ∈ Q) :
    ∃ (P : OriginalDiskProduct e K j) (Fnew : Set X) (x : X) (M : Set X),
      MapsTo P.map (D ×ˢ Icc (-1 : ℝ) 1) (R \ C) ∧
      PLDomain e P.cutCarrier ∧ IsCompact P.cutCarrier ∧ P.cutCarrier ⊆ K ∧
      Fnew = (F \ P.openStrip) ∪ P.endDisks ∧ IsCompact Fnew ∧
      frontier P.cutCarrier = frontier R ∪ Fnew ∧
      x ∈ C ∧ M = _root_.connectedComponentIn P.cutCarrier x ∧
      IsCompact M ∧ IsConnected M ∧ PLDomain e M ∧
      C ⊆ M ∧ M ⊆ P.cutCarrier ∧ M ⊆ R ∧
      (Fnew ∩ M).Nonempty ∧ IsCompact (Fnew ∩ M) ∧ Fnew ∩ M ⊆ interior R ∧
      Disjoint (frontier R) (Fnew ∩ M) ∧
      frontier M = frontier R ∪ (Fnew ∩ M) ∧
      frontier ((Subtype.val : R → X) ⁻¹' M) =
        (Subtype.val : R → X) ⁻¹' (Fnew ∩ M) ∧
      ((Subtype.val : R → X) ⁻¹' C ⊆ interior ((Subtype.val : R → X) ⁻¹' M)) ∧
      ((Subtype.val : R → X) ⁻¹' frontier R ⊆
        interior ((Subtype.val : R → X) ⁻¹' M)) ∧
      (∀ (y : R) (p : Path y y),
        (∀ t, p t ∈ (Subtype.val : R → X) ⁻¹' (Fnew ∩ M)) →
        ∃ H : p.Homotopy (Path.refl y),
          ∀ z, H z ∉ (Subtype.val : R → X) ⁻¹' C) ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
        IsOpen ((Subtype.val : K → X) ⁻¹' (P.map '' (D ×ˢ Ioo (-ε) ε))) ∧
        IsOpen ((Subtype.val : frontier K → X) ⁻¹'
          (P.map '' (Q ×ˢ Ioo (-ε) ε))) := by
  obtain ⟨P, Fnew, hsmall, _, hPL, hcompact, hsub, heq, hFnew,
    hnewU, _, hnewfront, hnewrel, hnewprotect, _, _, _, _, _, _, _, hcollars⟩ :=
    he.exists_protected_interior_compression_with_collars
      hK hR hKR hC hBC hFR hprotect hrel hfront hj hemb hjK hjC hproper
  obtain ⟨_, _, hcut⟩ :=
    Set.protected_open_cut_region hC hBC hFR hprotect hrel hfront
  have hrawloops := P.protected_compression_frontier_loops hF hcut subset_rfl hsmall
    (hcollars (3 / 4) (by norm_num) (by norm_num)).2 hloops
  have hnewint : Fnew ⊆ interior R := by
    intro y hy
    exact (mem_interior_iff_notMem_frontier (hnewU hy).1).mpr
      (fun h => (hnewU hy).2 (hBC h))
  obtain ⟨x, M, hx, hM, hMc, hMconn, hMPL, hCM, hMsub, hMR,
    hne, hMFc, hMFi, hdisj, hMfront, hMrel, hMprotect, hMBprotect⟩ :=
    hPL.exists_connected_protected_compression_component hcompact (hsub.trans hKR)
      hRconn hend hCconn hCR hBC hFnew hnewint hnewfront hnewrel hnewprotect
  refine ⟨P, Fnew, x, M, hsmall, hPL, hcompact, hsub, heq, hFnew,
    hnewfront, hx, hM, hMc, hMconn, hMPL, hCM, hMsub, hMR,
    hne, hMFc, hMFi, hdisj, hMfront, hMrel, hMprotect, hMBprotect, ?_, hcollars⟩
  intro y p hp
  apply hrawloops y p
  intro t
  exact heq.subset (hp t).1

end PoincareConjecture.M76
